/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/file.h>
#include <aws/common/string.h>

static void s_ref_dropped_callback(void *dir_ent) {
    struct aws_directory_entry *entry = dir_ent;
    aws_directory_entry_destroy_internal(entry);

    while (!aws_linked_list_empty(&entry->children)) {
        struct aws_linked_list_node *child = aws_linked_list_pop_front(&entry->children);
        struct aws_directory_entry *child_entry = AWS_CONTAINER_OF(child, struct aws_directory_entry, node);
        aws_directory_entry_release(child_entry);
    }

    aws_string_destroy(entry->path);
    aws_string_destroy(entry->relative_path);
    aws_mem_release(entry->allocator, entry);
}

struct aws_directory_entry *aws_directory_entry_open_base(
    struct aws_allocator *allocator,
    struct aws_byte_cursor path,
    struct aws_byte_cursor relative_path) {
    struct aws_directory_entry *entry = aws_mem_calloc(allocator, 1, sizeof(struct aws_directory_entry));

    struct aws_byte_cursor trimmed_path = aws_byte_cursor_trim_pred(&path, aws_isspace);
    struct aws_byte_cursor trimmed_relative_path = aws_byte_cursor_trim_pred(&relative_path, aws_isspace);

    if (trimmed_path.len && trimmed_path.ptr[trimmed_path.len - 1] == AWS_PATH_DELIM) {
        trimmed_path.len -= 1;
    }

    entry->path = aws_string_new_from_cursor(allocator, &trimmed_path);

    if (trimmed_relative_path.len && trimmed_relative_path.ptr[trimmed_relative_path.len - 1] == AWS_PATH_DELIM) {
        trimmed_relative_path.len -= 1;
    }

    entry->relative_path = aws_string_new_from_cursor(allocator, &trimmed_relative_path);

    entry->allocator = allocator;
    aws_ref_count_init(&entry->ref_count, entry, s_ref_dropped_callback);
    aws_linked_list_init(&entry->children);

    return entry;
}

struct aws_directory_entry *aws_directory_entry_open(
    struct aws_allocator *allocator,
    struct aws_byte_cursor path,
    struct aws_byte_cursor relative_path) {
    struct aws_directory_entry *entry = aws_directory_entry_open_base(allocator, path, relative_path);

    if (aws_directory_entry_open_internal(entry)) {
        aws_string_destroy(entry->path);
        aws_string_destroy(entry->relative_path);
        aws_mem_release(entry->allocator, entry);
        return NULL;
    }

    return entry;
}

void aws_directory_entry_acquire(struct aws_directory_entry *entry) {
    aws_ref_count_acquire(&entry->ref_count);
}

void aws_directory_entry_release(struct aws_directory_entry *entry) {
    aws_ref_count_release(&entry->ref_count);
}

struct aws_directory_entry *aws_directory_entry_get_next_sibling(struct aws_directory_entry *entry) {
    if (aws_linked_list_node_next_is_valid(&entry->node)) {
        struct aws_linked_list_node *sibling = aws_linked_list_next(&entry->node);
        return AWS_CONTAINER_OF(sibling, struct aws_directory_entry, node);
    }

    return NULL;
}

struct aws_directory_entry *aws_directory_entry_get_prev_sibling(struct aws_directory_entry *entry) {
    if (aws_linked_list_node_prev_is_valid(&entry->node)) {
        struct aws_linked_list_node *sibling = aws_linked_list_prev(&entry->node);
        return AWS_CONTAINER_OF(sibling, struct aws_directory_entry, node);
    }

    return NULL;
}

struct aws_directory_entry *aws_directory_entry_parent(struct aws_directory_entry *entry) {
    return entry->parent;
}

struct aws_directory_entry *aws_directory_entry_descend(struct aws_directory_entry *entry) {
    if (entry->file_type != AWS_FILE_TYPE_DIRECTORY && entry->file_type != AWS_FILE_TYPE_SYM_LINK) {
        aws_raise_error(AWS_ERROR_FILE_INVALID_PATH);
        return NULL;
    }

    if (aws_linked_list_empty(&entry->children)) {
        if (aws_directory_entry_open_internal(entry)) {
            return NULL;
        }
    }

    if (!aws_linked_list_empty(&entry->children)) {
        struct aws_linked_list_node *first_child = aws_linked_list_front(&entry->children);
        return AWS_CONTAINER_OF(first_child, struct aws_directory_entry, node);
    }

    aws_raise_error(AWS_ERROR_FILE_INVALID_PATH);
    return NULL;
}
