#ifndef AWS_COMMON_FILE_H
#define AWS_COMMON_FILE_H
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/byte_buf.h>
#include <aws/common/common.h>
#include <aws/common/linked_list.h>
#include <aws/common/ref_count.h>

#ifdef _WIN32
static const char AWS_PATH_DELIM = '\\';
#else
static const char AWS_PATH_DELIM = '/';
#endif

enum aws_file_type {
    AWS_FILE_TYPE_NONE,
    AWS_FILE_TYPE_FILE,
    AWS_FILE_TYPE_SYM_LINK,
    AWS_FILE_TYPE_DIRECTORY,
};

struct aws_directory_entry {
    struct aws_allocator *allocator;
    struct aws_string *path;
    struct aws_string *relative_path;
    enum aws_file_type file_type;
    int64_t file_size;
    struct aws_linked_list children;
    struct aws_linked_list_node node;
    struct aws_directory_entry *parent;
    struct aws_ref_count ref_count;
    void *impl;
};

/**
 * Platform implementation of opening a file and loading its immediate children (not recursive).
 * return AWS_OP_SUCCESS if successful.
 */
int aws_directory_entry_open_internal(struct aws_directory_entry *entry);

/**
 * Destroy any resources allocated in aws_directory_entry_open_internal.
 */
void aws_directory_entry_destroy_internal(struct aws_directory_entry *entry);

/**
 * General function for allocating and setting up a directory entry. Use for allocating and setting up the
 * platform agnostic portions of aws_directory_entry.
 *
 * returns an instance of aws_directory_entry on success and NULL on failure.
 */
struct aws_directory_entry *aws_directory_entry_open_base(
    struct aws_allocator *allocator,
    struct aws_byte_cursor path,
    struct aws_byte_cursor relative_path);

AWS_EXTERN_C_BEGIN

/**
 * To support non-ascii file path across platform.
 * For windows, _wfopen will be invoked under the hood. For other platforms, same as calling fopen
 * Functionality is the same as fopen.
 * On error, errno will be set, and NULL will be returned. Same as fopen.
 */
AWS_COMMON_API
FILE *aws_fopen(const char *file_path, const char *mode);

/**
 * Opens a directory at path. It's ref-count will be initialized to 1 on successful return.
 * You must call aws_directory_entry_release() when finished or the resource will leak.
 *
 * This function allocates resources for children in the directory, but only with a depth of one. To get to the
 * next level, you call aws_directory_entry_descend() which will repeat this process.
 */
AWS_COMMON_API struct aws_directory_entry *aws_directory_entry_open(
    struct aws_allocator *allocator,
    struct aws_byte_cursor path,
    struct aws_byte_cursor relative_path);

/**
 * Holds a reference to the entry. Call this before seating an instance of aws_directory_entry().
 */
AWS_COMMON_API void aws_directory_entry_acquire(struct aws_directory_entry *entry);

/**
 * Releases reference to entry. When the last reference is dropped, the resource will be freed.
 */
AWS_COMMON_API void aws_directory_entry_release(struct aws_directory_entry *entry);

/**
 * Get's the next directory entry at the current directory depth level as entry. Returns NULL when there are no more
 * sibling entries.
 */
AWS_COMMON_API struct aws_directory_entry *aws_directory_entry_get_next_sibling(struct aws_directory_entry *entry);

/**
 * Get's the previous directory entry at the current directory depth level as entry. Returns NULL when there are no more
 * sibling entries.
 */
AWS_COMMON_API struct aws_directory_entry *aws_directory_entry_get_prev_sibling(struct aws_directory_entry *entry);

/**
 * Descends into the next depth level for entry. Returns the first child in entry. Returns NULL if entry is not a
 * directory or it's empty. The return value's reference count is owned by entry. You do not need to acquire unless
 * you'll be seating the return value beyond the scope of the root entry.
 */
AWS_COMMON_API struct aws_directory_entry *aws_directory_entry_descend(struct aws_directory_entry *entry);

/**
 * Returns the parent for the current entry unless the entry is the initial root directory from
 * aws_directory_entry_open(). In that case it returns NULL. Also note, you do not need to acquire or release a
 * reference to the returned value unless you plan on seating it beyond the scope of the root entry.
 */
AWS_COMMON_API struct aws_directory_entry *aws_directory_entry_parent(struct aws_directory_entry *entry);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_FILE_H */
