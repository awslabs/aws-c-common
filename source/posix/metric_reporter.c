/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/metric_reporter.h>

#if defined(__linux__) || defined(__unix__)
#    include <sys/sysinfo.h>
#    include <sys/types.h>
#endif

/** Static variables to store the last CPU usage call. */
static uint64_t s_cpuLastTotalUser = 0;
static uint64_t s_cpuLastTotalUserLow = 0;
static uint64_t s_cpuLastTotalSystem = 0;
static uint64_t s_cpuLastTotalIdle = 0;

static void s_getCurrentCpuUsage(
    uint64_t *totalUser,
    uint64_t *totalUserLow,
    uint64_t *totalSystem,
    uint64_t *totalIdle) {
    *totalUser = 0;    // prevent warnings over unused parameter on Mac
    *totalUserLow = 0; // prevent warnings over unused parameter on Mac
    *totalSystem = 0;  // prevent warnings over unused parameter on Mac
    *totalIdle = 0;    // prevent warnings over unused parameter on Mac

// Get the CPU usage from Linux
#if defined(__linux__) || defined(__unix__)
    FILE *file;
    int matchedResults;
    file = fopen("/proc/stat", "r");
    matchedResults = fscanf(
        file,
        "cpu %llu %llu %llu %llu",
        (long long unsigned int *)totalUser,
        (long long unsigned int *)totalUserLow,
        (long long unsigned int *)totalSystem,
        (long long unsigned int *)totalIdle);
    fclose(file);
    if (matchedResults == EOF || matchedResults != 4) {
        aws_raise_error(AWS_ERROR_INVALID_STATE);
    }
#endif
}

int aws_get_custom_metric_cpu_usage(double *output) {
// Get the CPU usage from Linux
#if defined(__linux__) || defined(__unix__)
    int return_result = AWS_OP_ERR;
    uint64_t totalUser, totalUserLow, totalSystem, totalIdle, total;
    s_getCurrentCpuUsage(&totalUser, &totalUserLow, &totalSystem, &totalIdle);
    double percent;

    // Overflow detection
    if (totalUser < s_cpuLastTotalUser || totalUserLow < s_cpuLastTotalUserLow || totalSystem < s_cpuLastTotalSystem ||
    totalIdle < s_cpuLastTotalIdle) {
        *output = 0;
    } else {
        total = (totalUser - s_cpuLastTotalUser) + (totalUserLow - s_cpuLastTotalUserLow) +
                (totalSystem - s_cpuLastTotalSystem);
        percent = total;
        total += totalIdle - s_cpuLastTotalIdle;
        percent = (percent / total) * 100;

        // If percent is negative, then there was an error (overflow?)
        if (percent < 0) {
            *output = 0;
            return_result = AWS_OP_ERR;
        } else {
            *output = percent;
            return_result = AWS_OP_SUCCESS;
        }
    }

    s_cpuLastTotalUser = totalUser;
    s_cpuLastTotalUserLow = totalUserLow;
    s_cpuLastTotalSystem = totalSystem;
    s_cpuLastTotalIdle = totalIdle;

    return return_result;
#endif

    // prevent warnings over unused parameter on Mac
    s_getCurrentCpuUsage(
        s_cpuLastTotalUser,
        s_cpuLastTotalUserLow,
        s_cpuLastTotalSystem,
        s_cpuLastTotalIdle);

    // OS not supported? Just return an error and set the output to 0
    *output = 0;
    aws_raise_error(AWS_ERROR_PLATFORM_NOT_SUPPORTED);
    return AWS_OP_ERR;
}

int aws_get_custom_metric_memory_usage(double *output) {
// Get the Memory usage from Linux
#if defined(__linux__) || defined(__unix__)
    struct sysinfo memoryInfo;
    sysinfo(&memoryInfo);
    uint64_t physicalMemoryUsed = memoryInfo.totalram - memoryInfo.freeram;
    physicalMemoryUsed *= memoryInfo.mem_unit;
    // Return data in Kilobytes
    physicalMemoryUsed = physicalMemoryUsed / (1024);
    *output = (double)physicalMemoryUsed;
    return AWS_OP_SUCCESS;
#endif

    // OS not supported? Just return an error and set the output to 0
    *output = 0;
    aws_raise_error(AWS_ERROR_PLATFORM_NOT_SUPPORTED);
    return AWS_OP_ERR;
}

int aws_get_custom_metric_process_count(double *output) {
// Get the process count from Linux
#if defined(__linux__) || defined(__unix__)
    struct sysinfo systemInfo;
    sysinfo(&systemInfo);
    *output = (double)systemInfo.procs;
    return AWS_OP_SUCCESS;
#endif
    // OS not supported? Just return an error and set the output to 0
    *output = 0;
    aws_raise_error(AWS_ERROR_PLATFORM_NOT_SUPPORTED);
    return AWS_OP_ERR;
}
