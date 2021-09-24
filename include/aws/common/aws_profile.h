/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#ifndef AWS_COMMON_PROFILE_H
#define AWS_COMMON_PROFILE_H

#include <aws/common/common.h>
#include <aws/common/hash_table.h>

struct aws_allocator;
struct aws_string;
struct aws_byte_buf;
struct aws_byte_cursor;

/*
 * A set of data types that model the aws profile specification
 *
 * A profile collection is a collection of zero or more named profiles
 * Each profile is a set of properties (named key-value pairs)
 * Empty-valued properties may have sub properties (named key-value pairs)
 *
 * Resolution rules exist to determine what profile to use, what files to
 * read profile collections from, and what types of credentials have priority.
 *
 * The profile specification is informally defined as "what the aws cli does" and
 * formally defined in internal aws documents.
 */
struct aws_profile_property {
    struct aws_allocator *allocator;
    struct aws_string *name;
    struct aws_string *value;
    struct aws_hash_table sub_properties;
    bool is_empty_valued;
};

struct aws_profile {
    struct aws_allocator *allocator;
    struct aws_string *name;
    struct aws_hash_table properties;
    bool has_profile_prefix;
};

/**
 * The profile specification has rule exceptions based on what file
 * the profile collection comes from.
 */
enum aws_profile_source_type { AWS_PST_NONE, AWS_PST_CONFIG, AWS_PST_CREDENTIALS };

struct aws_profile_collection {
    struct aws_allocator *allocator;
    enum aws_profile_source_type profile_source;
    struct aws_hash_table profiles;
};

AWS_EXTERN_C_BEGIN

/*************************
 * Profile collection APIs
 *************************/

/**
 * Clean up everything associated with a profile collection
 */
AWS_COMMON_API
void aws_profile_collection_destroy(struct aws_profile_collection *profile_collection);

/**
 * Create a new profile collection by parsing a file with the specified path
 */
AWS_COMMON_API
struct aws_profile_collection *aws_profile_collection_new_from_file(
    struct aws_allocator *allocator,
    const struct aws_string *file_path,
    enum aws_profile_source_type source);

/**
 * Create a new profile collection by merging a config-file-based profile
 * collection and a credentials-file-based profile collection
 */
AWS_COMMON_API
struct aws_profile_collection *aws_profile_collection_new_from_merge(
    struct aws_allocator *allocator,
    const struct aws_profile_collection *config_profiles,
    const struct aws_profile_collection *credentials_profiles);

/**
 * Create a new profile collection by parsing text in a buffer.  Primarily
 * for testing.
 */
AWS_COMMON_API
struct aws_profile_collection *aws_profile_collection_new_from_buffer(
    struct aws_allocator *allocator,
    const struct aws_byte_buf *buffer,
    enum aws_profile_source_type source);

/**
 * Retrieves a profile with the specified name, if it exists, from the profile collection
 */
AWS_COMMON_API
struct aws_profile *aws_profile_collection_get_profile(
    const struct aws_profile_collection *profile_collection,
    const struct aws_string *profile_name);

/**
 * Returns how many profiles a collection holds
 */
AWS_COMMON_API
size_t aws_profile_collection_get_profile_count(const struct aws_profile_collection *profile_collection);

/**************
 * profile APIs
 **************/

/**
 * Retrieves a property with the specified name, if it exists, from a profile
 */
AWS_COMMON_API
struct aws_profile_property *aws_profile_get_property(
    const struct aws_profile *profile,
    const struct aws_string *property_name);

/**
 * Returns how many properties a profile holds
 */
AWS_COMMON_API
size_t aws_profile_get_property_count(const struct aws_profile *profile);

/***********************
 * profile property APIs
 ***********************/

/**
 * Returns the value of a sub property with the given name, if it exists, in the property
 */
AWS_COMMON_API
const struct aws_string *aws_profile_property_get_sub_property(
    const struct aws_profile_property *property,
    const struct aws_string *sub_property_name);

/**
 * Returns how many sub properties the property holds
 */
AWS_COMMON_API
size_t aws_profile_property_get_sub_property_count(const struct aws_profile_property *property);

/***********
 * Misc APIs
 ***********/

/**
 * Computes the final platform-specific path for the profile credentials file.  Does limited home directory
 * expansion/resolution.
 */
AWS_COMMON_API
struct aws_string *aws_get_credentials_file_path(
    struct aws_allocator *allocator,
    const struct aws_byte_cursor *override_path);

/**
 * Computes the final platform-specific path for the profile config file.  Does limited home directory
 * expansion/resolution.
 */
AWS_COMMON_API
struct aws_string *aws_get_config_file_path(
    struct aws_allocator *allocator,
    const struct aws_byte_cursor *override_path);

/**
 * Computes the profile to use for credentials lookups based on profile resolution rules
 */
AWS_COMMON_API
struct aws_string *aws_get_profile_name(struct aws_allocator *allocator, const struct aws_byte_cursor *override_name);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_PROFILE_H */
