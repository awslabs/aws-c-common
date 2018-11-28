#ifndef AWS_COMMON_TIME_H
#define AWS_COMMON_TIME_H
/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */
#include <aws/common/common.h>

#include <time.h>

AWS_EXTERN_C_BEGIN

AWS_COMMON_API time_t aws_mk_gm_time(struct tm *const t);
AWS_COMMON_API void aws_local_time(time_t time, struct tm *t);
AWS_COMMON_API void aws_gm_time(time_t time, struct tm *t);

AWS_EXTERN_C_END

#endif /*AWS_COMMON_TIME_H */
