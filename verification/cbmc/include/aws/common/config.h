/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

// Disable all compiler, and go to bare C
#undef AWS_CRYPTOSDK_P_USE_X86_64_ASM
#undef AWS_CRYPTOSDK_P_SPECTRE_MITIGATIONS
#undef AWS_CRYPTOSDK_P_HAVE_BUILTIN_EXPECT
