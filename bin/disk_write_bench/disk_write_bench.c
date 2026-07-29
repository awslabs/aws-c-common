/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * Disk write throughput benchmark: O_DIRECT + plain write, no io_uring.
 *
 * The Rust sibling in this repo gets its concurrency from io_uring queue depth.
 * Here every write is an ordinary blocking `pwrite`, so concurrency comes from
 * running several threads, each writing its own interleaved set of blocks. That
 * is deliberately the shape aws-c-s3 uses for parallel download-to-file: a pool
 * of threads issuing blocking positioned writes at part-aligned offsets. The
 * thread count is therefore the analogue of queue depth, and comparing the two
 * programs at matching concurrency isolates io_uring's contribution from
 * O_DIRECT's.
 *
 * Uses aws-c-common for CLI parsing, timing, threads, atomics, and — the part
 * that actually matters for O_DIRECT — the explicitly aligned allocator.
 */

#include <aws/common/allocator.h>
#include <aws/common/atomics.h>
#include <aws/common/clock.h>
#include <aws/common/command_line_parser.h>
#include <aws/common/common.h>
#include <aws/common/thread.h>

#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/*
 * O_DIRECT requires the file offset, the length, and the buffer address to be
 * aligned to the device's logical block size. 4096 covers 512e and 4Kn devices
 * and matches the page size on the platforms of interest.
 */
#define DIRECT_IO_ALIGN 4096

struct bench_config {
    const char *path;
    size_t block_size;
    size_t num_threads;
    uint64_t duration_secs;
    uint64_t max_bytes;
    bool no_prealloc;
    bool do_fsync;
    bool keep;
};

struct worker {
    struct aws_thread thread;
    struct bench_config *config;
    /* Shared: set once the deadline passes, polled by every worker. */
    struct aws_atomic_var *stop;
    /* Shared: total bytes written across all workers. */
    struct aws_atomic_var *bytes_written;
    struct aws_allocator *aligned_alloc;
    /* Worker index; determines which interleaved blocks this thread owns. */
    size_t index;
    int fd;
    uint64_t writes;
    int error_code;
};

static void s_print_usage(void) {
    fprintf(
        stderr,
        "\n"
        "Disk write throughput benchmark (O_DIRECT + pwrite, threads for concurrency)\n"
        "\n"
        "USAGE:\n"
        "    disk-write-bench-c --path <FILE> [OPTIONS]\n"
        "\n"
        "OPTIONS:\n"
        "    --path <FILE>          Output file, on the filesystem under test.\n"
        "                           O_DIRECT is unsupported on tmpfs.\n"
        "    --block-size <BYTES>   Bytes per write, multiple of %d. Default 8388608.\n"
        "    --threads <N>          Concurrent writers. The analogue of queue\n"
        "                           depth in the io_uring version. Default 1.\n"
        "    --duration <SECS>      How long to write. Default 30.\n"
        "    --max-bytes <BYTES>    Stop after this many bytes; also bounds the\n"
        "                           fallocate reservation.\n"
        "    --no-prealloc          Skip fallocate, so writes extend the file.\n"
        "                           Extending O_DIRECT writes take the inode lock\n"
        "                           exclusively and serialize regardless of how\n"
        "                           many threads are running.\n"
        "    --fsync                fsync() at the end, inside the measured window.\n"
        "    --keep                 Do not delete the output file on exit.\n"
        "\n",
        DIRECT_IO_ALIGN);
}

/*
 * Each worker owns the blocks whose index is congruent to its own index modulo
 * the worker count, so the threads write disjoint, interleaved regions and never
 * contend for the same bytes.
 */
static void s_worker_fn(void *arg) {
    struct worker *worker = arg;
    struct bench_config *config = worker->config;

    void *buffer = aws_mem_acquire(worker->aligned_alloc, config->block_size);
    if (buffer == NULL) {
        worker->error_code = ENOMEM;
        return;
    }
    /*
     * Fill with a non-trivial pattern: an all-zero buffer can be short-circuited
     * by a filesystem or device that detects sparse writes.
     */
    for (size_t i = 0; i < config->block_size; ++i) {
        ((uint8_t *)buffer)[i] = (uint8_t)(i % 251);
    }

    uint64_t block_index = worker->index;
    while (!aws_atomic_load_int(worker->stop)) {
        uint64_t offset = block_index * (uint64_t)config->block_size;

        if (config->max_bytes != 0 && offset >= config->max_bytes) {
            break;
        }

        ssize_t written = pwrite(worker->fd, buffer, config->block_size, (off_t)offset);
        if (written < 0) {
            worker->error_code = errno;
            break;
        }
        if ((size_t)written != config->block_size) {
            /* Short direct write indicates device trouble; do not paper over it. */
            worker->error_code = EIO;
            break;
        }

        aws_atomic_fetch_add(worker->bytes_written, (size_t)written);
        ++worker->writes;
        block_index += config->num_threads;
    }

    aws_mem_release(worker->aligned_alloc, buffer);
}

/* Best-effort filesystem type for the path's directory, for the tmpfs warning. */
static void s_report_filesystem(const char *path) {
    char dir[4096];
    snprintf(dir, sizeof(dir), "%s", path);
    char *slash = strrchr(dir, '/');
    if (slash != NULL && slash != dir) {
        *slash = '\0';
    }

    FILE *mounts = fopen("/proc/mounts", "r");
    if (mounts == NULL) {
        printf("  filesystem   : unknown\n");
        return;
    }
    char best_type[64] = "unknown";
    char best_dev[256] = "";
    size_t best_len = 0;
    char dev[256], mount[4096], type[64];
    while (fscanf(mounts, "%255s %4095s %63s %*[^\n]", dev, mount, type) == 3) {
        size_t len = strlen(mount);
        if (strncmp(dir, mount, len) == 0 && len > best_len) {
            best_len = len;
            snprintf(best_type, sizeof(best_type), "%s", type);
            snprintf(best_dev, sizeof(best_dev), "%s", dev);
        }
    }
    fclose(mounts);
    printf("  filesystem   : %s on %s", best_type, best_dev);
    if (strcmp(best_type, "tmpfs") == 0) {
        printf("   <-- tmpfs does not support O_DIRECT");
    }
    printf("\n");
}

int main(int argc, char *argv[]) {
    struct aws_allocator *allocator = aws_default_allocator();
    aws_common_library_init(allocator);

    struct bench_config config = {
        .path = NULL,
        .block_size = 8 * 1024 * 1024,
        .num_threads = 1,
        .duration_secs = 30,
        .max_bytes = 0,
        .no_prealloc = false,
        .do_fsync = false,
        .keep = false,
    };

    enum {
        OPT_PATH = 'p',
        OPT_BLOCK_SIZE = 'b',
        OPT_THREADS = 't',
        OPT_DURATION = 'd',
        OPT_MAX_BYTES = 'm',
        OPT_NO_PREALLOC = 'n',
        OPT_FSYNC = 'f',
        OPT_KEEP = 'k',
        OPT_HELP = 'h',
    };
    const struct aws_cli_option options[] = {
        {.name = "path", .has_arg = AWS_CLI_OPTIONS_REQUIRED_ARGUMENT, .val = OPT_PATH},
        {.name = "block-size", .has_arg = AWS_CLI_OPTIONS_REQUIRED_ARGUMENT, .val = OPT_BLOCK_SIZE},
        {.name = "threads", .has_arg = AWS_CLI_OPTIONS_REQUIRED_ARGUMENT, .val = OPT_THREADS},
        {.name = "duration", .has_arg = AWS_CLI_OPTIONS_REQUIRED_ARGUMENT, .val = OPT_DURATION},
        {.name = "max-bytes", .has_arg = AWS_CLI_OPTIONS_REQUIRED_ARGUMENT, .val = OPT_MAX_BYTES},
        {.name = "no-prealloc", .has_arg = AWS_CLI_OPTIONS_NO_ARGUMENT, .val = OPT_NO_PREALLOC},
        {.name = "fsync", .has_arg = AWS_CLI_OPTIONS_NO_ARGUMENT, .val = OPT_FSYNC},
        {.name = "keep", .has_arg = AWS_CLI_OPTIONS_NO_ARGUMENT, .val = OPT_KEEP},
        {.name = "help", .has_arg = AWS_CLI_OPTIONS_NO_ARGUMENT, .val = OPT_HELP},
        {NULL, 0, NULL, 0},
    };

    int opt = 0;
    while ((opt = aws_cli_getopt_long(argc, argv, "p:b:t:d:m:nfkh", options, NULL)) != -1) {
        switch (opt) {
            case OPT_PATH:
                config.path = aws_cli_optarg;
                break;
            case OPT_BLOCK_SIZE:
                config.block_size = (size_t)strtoull(aws_cli_optarg, NULL, 10);
                break;
            case OPT_THREADS:
                config.num_threads = (size_t)strtoull(aws_cli_optarg, NULL, 10);
                break;
            case OPT_DURATION:
                config.duration_secs = strtoull(aws_cli_optarg, NULL, 10);
                break;
            case OPT_MAX_BYTES:
                config.max_bytes = strtoull(aws_cli_optarg, NULL, 10);
                break;
            case OPT_NO_PREALLOC:
                config.no_prealloc = true;
                break;
            case OPT_FSYNC:
                config.do_fsync = true;
                break;
            case OPT_KEEP:
                config.keep = true;
                break;
            case OPT_HELP:
                s_print_usage();
                return 0;
            default:
                break;
        }
    }

    if (config.path == NULL) {
        fprintf(stderr, "error: --path is required\n");
        s_print_usage();
        return 2;
    }
    if (config.block_size == 0 || config.block_size % DIRECT_IO_ALIGN != 0) {
        fprintf(stderr, "error: --block-size must be a non-zero multiple of %d\n", DIRECT_IO_ALIGN);
        return 2;
    }
    if (config.num_threads == 0) {
        fprintf(stderr, "error: --threads must be at least 1\n");
        return 2;
    }

    /* Create/truncate with a plain descriptor first, so an O_DIRECT failure is
     * distinguishable from a failure to create the file at all. */
    int setup_fd = open(config.path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (setup_fd < 0) {
        fprintf(stderr, "error: cannot create %s: %s\n", config.path, strerror(errno));
        return 1;
    }

    printf("disk write benchmark (C, O_DIRECT + pwrite)\n");
    printf("  path         : %s\n", config.path);
    s_report_filesystem(config.path);
    printf("  block size   : %zu bytes (%.2f MiB)\n", config.block_size, config.block_size / 1048576.0);
    printf("  threads      : %zu\n", config.num_threads);
    printf("  duration     : %" PRIu64 "s\n", config.duration_secs);

    /*
     * Preallocate unless disabled. Without this every write extends the file,
     * which takes the inode lock exclusively and serializes the writers no
     * matter how many threads are running.
     */
    if (config.no_prealloc) {
        printf("  preallocate  : disabled  <-- appends serialize on the inode lock\n");
    } else {
        uint64_t target = config.max_bytes;
        if (target == 0) {
            /* No cap given: reserve enough for the duration at an optimistic rate. */
            uint64_t optimistic = 20ULL * 1024 * 1024 * 1024;
            target = (config.duration_secs > 0 ? config.duration_secs : 1) * optimistic;
        }
        if (fallocate(setup_fd, 0, 0, (off_t)target) == 0) {
            printf("  preallocate  : %.2f GiB (fallocate)\n", target / 1073741824.0);
        } else {
            printf("  preallocate  : FAILED (%s) -- appends will serialize\n", strerror(errno));
        }
    }
    printf("\n");

    int direct_fd = open(config.path, O_WRONLY | O_DIRECT);
    if (direct_fd < 0) {
        fprintf(
            stderr,
            "error: cannot open %s with O_DIRECT: %s\n"
            "The filesystem may not support it (tmpfs does not).\n",
            config.path,
            strerror(errno));
        close(setup_fd);
        return 1;
    }

    /*
     * Explicitly aligned allocator: O_DIRECT rejects unaligned buffer addresses,
     * and the default allocator makes no alignment guarantee beyond the type's.
     */
    struct aws_allocator *aligned_alloc = aws_explicit_aligned_allocator_new(DIRECT_IO_ALIGN);
    if (aligned_alloc == NULL) {
        fprintf(stderr, "error: cannot create aligned allocator\n");
        close(direct_fd);
        close(setup_fd);
        return 1;
    }

    struct aws_atomic_var stop;
    struct aws_atomic_var bytes_written;
    aws_atomic_init_int(&stop, 0);
    aws_atomic_init_int(&bytes_written, 0);

    struct worker *workers = aws_mem_calloc(allocator, config.num_threads, sizeof(struct worker));

    uint64_t start_ns = 0;
    aws_high_res_clock_get_ticks(&start_ns);

    for (size_t i = 0; i < config.num_threads; ++i) {
        workers[i].config = &config;
        workers[i].stop = &stop;
        workers[i].bytes_written = &bytes_written;
        workers[i].aligned_alloc = aligned_alloc;
        workers[i].index = i;
        workers[i].fd = direct_fd;
        aws_thread_init(&workers[i].thread, allocator);
        if (aws_thread_launch(&workers[i].thread, s_worker_fn, &workers[i], NULL) != AWS_OP_SUCCESS) {
            fprintf(stderr, "error: cannot launch worker %zu\n", i);
            aws_atomic_store_int(&stop, 1);
        }
    }

    /* Wall-clock deadline, then signal every worker to stop. */
    sleep((unsigned)config.duration_secs);
    aws_atomic_store_int(&stop, 1);

    uint64_t total_writes = 0;
    int first_error = 0;
    for (size_t i = 0; i < config.num_threads; ++i) {
        aws_thread_join(&workers[i].thread);
        aws_thread_clean_up(&workers[i].thread);
        total_writes += workers[i].writes;
        if (first_error == 0 && workers[i].error_code != 0) {
            first_error = workers[i].error_code;
        }
    }

    uint64_t fsync_ns = 0;
    if (config.do_fsync) {
        uint64_t fsync_start = 0;
        aws_high_res_clock_get_ticks(&fsync_start);
        fsync(direct_fd);
        uint64_t fsync_end = 0;
        aws_high_res_clock_get_ticks(&fsync_end);
        fsync_ns = fsync_end - fsync_start;
    }

    uint64_t end_ns = 0;
    aws_high_res_clock_get_ticks(&end_ns);

    double secs = (double)(end_ns - start_ns) / 1e9;
    uint64_t total_bytes = (uint64_t)aws_atomic_load_int(&bytes_written);
    double gib_s = (double)total_bytes / secs / 1073741824.0;
    double gb_s = (double)total_bytes / secs / 1e9;
    double gbit_s = (double)total_bytes * 8.0 / secs / 1e9;

    printf("results\n");
    printf("  elapsed      : %.3f s\n", secs);
    printf("  written      : %.2f GiB (%" PRIu64 " bytes)\n", total_bytes / 1073741824.0, total_bytes);
    printf("  writes       : %" PRIu64 "\n", total_writes);
    printf("  throughput   : %.2f GiB/s  (%.2f GB/s, %.2f Gb/s)\n", gib_s, gb_s, gbit_s);
    printf("  IOPS         : %.0f\n", (double)total_writes / secs);
    printf(
        "  avg latency  : %.3f ms/write (%zu threads)\n",
        total_writes > 0 ? secs * 1000.0 * (double)config.num_threads / (double)total_writes : 0.0,
        config.num_threads);
    if (config.do_fsync) {
        printf("  fsync        : %.3f s (included above)\n", (double)fsync_ns / 1e9);
    }
    if (first_error != 0) {
        printf("  WARNING      : a worker failed: %s\n", strerror(first_error));
    }

    close(direct_fd);
    close(setup_fd);
    aws_mem_release(allocator, workers);
    aws_explicit_aligned_allocator_destroy(aligned_alloc);

    if (!config.keep) {
        unlink(config.path);
    } else {
        printf("\noutput file kept at %s\n", config.path);
    }

    aws_common_library_clean_up();
    return first_error == 0 ? 0 : 1;
}
