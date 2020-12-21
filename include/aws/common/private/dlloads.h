#ifndef AWS_COMMON_PRIVATE_DLLOADS_H
#define AWS_COMMON_PRIVATE_DLLOADS_H
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

/*
 * definition is here: https://linux.die.net/man/2/set_mempolicy
 */
#define AWS_MPOL_PREFERRED_ALIAS 1

struct bitmask;

extern long (*g_set_mempolicy_ptr)(int, const unsigned long *, unsigned long);
extern int (*g_numa_available_ptr)(void);
extern int (*g_numa_num_configured_nodes_ptr)(void);
extern int (*g_numa_num_possible_cpus_ptr)(void);
extern int (*g_numa_node_to_cpus_ptr)(int node, struct bitmask *mask);
extern unsigned int (*g_numa_bitmask_weight)(const struct bitmask *bmp);
extern int (*g_numa_bitmask_isbitset)(const struct bitmask *bmp, unsigned int n);
extern struct bitmask *(*g_numa_allocate_cpumask_ptr)(void);
extern void (*g_numa_free_cpumask_ptr)(struct bitmask *mask);
extern void *g_libnuma_handle;

#endif /* AWS_COMMON_PRIVATE_DLLOADS_H */
