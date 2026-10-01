#ifndef AWS_COMMON_TRIBOOL_H
#define AWS_COMMON_TRIBOOL_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/macros.h>

AWS_PUSH_SANE_WARNING_LEVEL

/**
 * A boolean option that can also be left unspecified, for config structs where "the caller passed
 * false" and "the caller passed nothing" have to lead to different behavior. Replaces carrying a
 * `bool value` alongside a `bool value_is_set`, where nothing stops the two from disagreeing.
 *
 * AWS_TRIBOOL_UNSET is 0, so a zero-initialized options struct reads as unspecified.
 *
 * Do not test one of these for truth directly: `if (options->foo)` is also true for
 * AWS_TRIBOOL_FALSE, which is non-zero. Compare against the enumerator you mean, e.g.
 * `options->foo != AWS_TRIBOOL_FALSE` for an option that defaults to on.
 */
enum aws_tribool {
    AWS_TRIBOOL_UNSET = 0,
    AWS_TRIBOOL_FALSE = 1,
    AWS_TRIBOOL_TRUE = 2,
};

AWS_POP_SANE_WARNING_LEVEL

#endif /* AWS_COMMON_TRIBOOL_H */
