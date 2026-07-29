#!/bin/bash
# Full-picture sweep for the C disk-write-bench (O_DIRECT + pwrite).
#
# Usage: ./sweep.sh <BINARY> [PATH] [DURATION_SECS]
#   ./sweep.sh ../../build/bin/disk_write_bench/disk-write-bench /mnt/raid0/bench.dat 15
#
# This version has no io_uring: every write is a blocking pwrite, so concurrency
# comes from threads. `--threads N` is the analogue of queue depth, which makes
# section A directly comparable against the Rust sibling's queue-depth sweep --
# matching concurrency there isolates io_uring's contribution from O_DIRECT's.
#
# Sections:
#   A. threads x preallocation   <-- the headline: does concurrency do anything?
#   B. block size
#   C. fsync cost
#
# Section A at threads=1 is also the single-threaded first-touch case: the shape
# of a plain C write loop against a fresh file.

set -u

BENCH="${1:-}"
PATH_ARG="${2:-/mnt/raid0/bench.dat}"
DUR="${3:-15}"
CAP="300g"   # bounds the fallocate reservation; raise if the device is faster

if [ -z "$BENCH" ] || [ ! -x "$BENCH" ]; then
    echo "usage: $0 <path-to-disk-write-bench> [PATH] [DURATION]" >&2
    echo "build it with: cmake -DBUILD_TESTING=ON .. && make disk-write-bench" >&2
    exit 1
fi

run() {
    # run <label> <extra args...>
    local label="$1"; shift
    local out thr warn
    out=$("$BENCH" --path "$PATH_ARG" --duration "$DUR" --max-bytes "$CAP" "$@" 2>&1)
    thr=$(echo "$out"  | awk -F': ' '/throughput/{print $2}')
    warn=$(echo "$out" | awk -F': ' '/WARNING/{print $2}')
    if [ -z "$thr" ]; then
        printf '  %-30s ERROR\n' "$label"
        echo "$out" | grep -iE "error|cannot" | sed 's/^/      /' | head -3
        return
    fi
    printf '  %-30s %s' "$label" "$thr"
    [ -n "$warn" ] && printf '  [%s]' "$warn"
    printf '\n'
    rm -f "$PATH_ARG"
}

echo "=============================================================="
echo " disk-write-bench (C, O_DIRECT + pwrite) sweep"
echo " binary=$BENCH"
echo " path=$PATH_ARG  duration=${DUR}s  cap=$CAP"
echo " $(date -u '+%Y-%m-%dT%H:%M:%SZ')"
echo "=============================================================="
echo
echo "--- A. threads x preallocation (bs=8m) -----------------------"
echo "    threads here == queue depth in the io_uring version"
for t in 1 2 4 8 16 32 64; do
    run "prealloc    threads=$t" --threads "$t"
done
echo
for t in 1 2 4 8 16 32 64; do
    run "no-prealloc threads=$t" --threads "$t" --no-prealloc
done
echo
echo "--- B. block size (preallocated, threads=32) -----------------"
for bs in 1m 2m 4m 8m 16m 64m; do
    run "bs=$bs" --threads 32 --block-size "$bs"
done
echo
echo "--- C. fsync cost (preallocated, bs=8m) ----------------------"
echo "    O_DIRECT already bypasses the page cache; fsync here flushes"
echo "    remaining filesystem metadata, so expect a small delta"
run "threads=32, no fsync" --threads 32
run "threads=32, fsync"    --threads 32 --fsync
echo
echo "--- D. single thread, block size ladder, aws helper ----------"
echo "    1 thread via aws_file_path_write_to_offset_direct_io(), so the only"
echo "    source of parallelism is however much the device overlaps a single"
echo "    large write. Tests whether one very large write can substitute for"
echo "    many concurrent smaller ones."
echo "    The helper writes in one write(2) up to ~2 GiB (AWS_FILE_MAX_READ_CHUNK"
echo "    = 0x7ffff000), so nothing here is split internally."
echo "    Note it reopens and closes the file per call, so larger blocks also"
echo "    amortize that per-call overhead over more bytes."
for bs in 1m 4m 8m 16m 32m 64m 128m 256m 512m 1g; do
    run "aws-helper t=1 bs=$bs" --threads 1 --block-size "$bs" --use-aws-helper
done
echo
echo "    same ladder with pwrite on a long-lived fd, to separate the"
echo "    block-size effect from the helper's per-call open/close"
for bs in 1m 4m 8m 16m 32m 64m 128m 256m 512m 1g; do
    run "pwrite     t=1 bs=$bs" --threads 1 --block-size "$bs"
done
echo
echo "=============================================================="
echo " done"
echo "=============================================================="
