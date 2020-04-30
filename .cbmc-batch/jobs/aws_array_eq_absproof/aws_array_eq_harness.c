/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>


struct ainfo {
    size_t l_c;
    size_t l_len;
    size_t r_c;
    size_t r_len;
};

// Abstraction related. compute_abs_len(len, l_cncrt, r_cncrt)

size_t compute_abs_length(size_t len, const struct ainfo abs_info) {
    size_t l_cncrt = abs_info.l_c;
    size_t r_cncrt = abs_info.r_c;
    if (len > l_cncrt && len > r_cncrt) return 5;
    else assert(false);
}

size_t two_abs(size_t index, size_t a1, size_t a2) {
    if (index < a1) return 0;
    else if (index == a1) return 1;
    else if (index > a1 && index < a2) return 2;
    else if (index == a2) return 3;
    else return 4;
}

size_t three_abs(size_t index, size_t a1, size_t a2, size_t a3) {
    if (index < a1) return 0;
    else if (index == a1) return 1;
    else if (index > a1 && index < a2) return 2;
    else if (index == a2) return 3;
    else if (index > a2 && index < a3) return 4;
    else if (index == a3) return 5;
    else return 6;
}

size_t four_abs(size_t index, size_t a1, size_t a2, size_t a3, size_t a4) {
    if (index < a1) return 0;
    else if (index == a1) return 1;
    else if (index > a1 && index < a2) return 2;
    else if (index == a2) return 3;
    else if (index > a2 && index < a3) return 4;
    else if (index == a3) return 5;
    else if (index > a3 && index < a4) return 6;
    else if (index == a4) return 7;
    else return 8;
}

// Function to abstract a given index wrt to concrete indices c1, c2. 
size_t get_abs_index(size_t index, const struct ainfo abs_info) {
    size_t l_c = abs_info.l_c;
    size_t r_c = abs_info.r_c;
    size_t l_len = abs_info.l_len;
    size_t r_len = abs_info.r_len;

    // these hold the above numbers in sorted order.  
    size_t a1, a2, a3, a4;

    if( r_len <=  l_c) {
        a1 = r_c;
        a2 = r_len;
        a3 = l_c;
        a4 = l_len;
    } else if (l_len <= r_c) {
        a1 = l_c;
        a2 = l_len;
        a3 = r_c;
        a4 = r_len;
    } else if (r_c <= l_c) {
        a1 = r_c;
        a2 = l_c;
        if (l_len <= r_len) {
            a3 = l_len; 
            a4 = r_len;
        } else {
            a3 = r_len; 
            a4 = l_len;
        }
    } else {
        a1 = l_c;
        a2 = r_c;
        if (l_len <= r_len) {
            a3 = l_len; 
            a4 = r_len;
        } else {
            a3 = r_len; 
            a4 = l_len;
        }
    }

    if (a1 == a2 && a3 == a4) return two_abs(index, a1, a3);
    else if (a1 == a2) return three_abs(index, a1, a3, a4);
    else if (a3 == a4) return three_abs(index, a1, a2, a3);
    else return four_abs(index, a1, a2, a3, a4);    
}

bool is_abstract(size_t index, const struct ainfo abs_info) {
    size_t abs1 = get_abs_index(abs_info.r_c, abs_info);
    size_t abs2 = get_abs_index(abs_info.l_c, abs_info);
    return !(index == abs1 || index == abs2);
}

void save_byte_from_array_abs(const uint8_t *const array, const size_t size, struct store_byte_from_buffer *const storage, const struct ainfo abs_info) {
    size_t abs_index;
    if (size > 0 && array && storage) {
        storage->index = nondet_size_t();
        __CPROVER_assume(storage->index < size);

        abs_index = get_abs_index(storage->index, abs_info);
        if (is_abstract(abs_index, abs_info)) storage->byte = nondet_uint8_t();
        else storage->byte = array[abs_index];
    }
}

void assert_bytes_match_abs(const uint8_t *const a, const uint8_t *const b, const size_t len, const struct ainfo abs_info) {
    assert(!a == !b);
    if (len > 0 && a != NULL && b != NULL) {
        size_t i;
        size_t abs_i;
        __CPROVER_assume(i < len && len < MAX_MALLOC); /* prevent spurious pointer overflows */

        abs_i = get_abs_index(i, abs_info);
        if (is_abstract(abs_i, abs_info)) assert(true);
        else assert(a[abs_i] == b[abs_i]);
    }
}
void assert_byte_from_buffer_matches_abs(const uint8_t *const buffer, const struct store_byte_from_buffer *const b, const struct ainfo abs_info) {
    size_t abs_index;
    if (buffer && b) {
        abs_index = get_abs_index(b->index, abs_info);
        if (is_abstract(abs_index, abs_info)) assert(true);
        else assert(*(buffer + abs_index) == b->byte);
    }
}
/*
size_t minus_one(const size_t abs_index) {
   if (abs_index == 1 || abs_index == 3) return (abs_index - 1);
   else if (nondet_bool()) return (abs_index);
   else return (abs_index - 1);
}
*/

int memcmp_abs(const void *s1, const void *s2, size_t n, const struct ainfo abs_info) {
    int res = 0;
    int nondet_res = 0;
    __CPROVER_precondition(__CPROVER_r_ok(s1, n), "memcmp region 1 readable");
    __CPROVER_precondition(__CPROVER_r_ok(s2, n), "memcpy region 2 readable");

#if 1
    const unsigned char *sc1 = s1, *sc2 = s2;
    
    // s1,s2 indices are from 0..(n-1).
    while( n > 0){
        if (!is_abstract(n-1, abs_info)) {
            res = *(sc1 + n-1) - *(sc2 + n-1);
            if (res !=0 )
                return res;
            else n--;
                
        }
        else {
         nondet_res = nondet_bool();
         if (nondet_res != 0)
            return nondet_res;
         else n--;
        }
    }
 /*   for (; n != 0; n--) {
        res = (*sc1++) - (*sc2++);
        if (res != 0)
            return res;
    }
    return res;*/
#else
    return nondet_int();
#endif
}

// Abstracted version of aws_array_eq
bool aws_array_eq_abs(const void *const array_a, const size_t len_a, const void *const array_b, const size_t len_b, const struct ainfo abs_info) {
    AWS_PRECONDITION(
        (len_a == 0) || AWS_MEM_IS_READABLE(array_a, len_a), "Input array [array_a] must be readable up to [len_a].");
    AWS_PRECONDITION(
        (len_b == 0) || AWS_MEM_IS_READABLE(array_b, len_b), "Input array [array_b] must be readable up to [len_b].");

    if (len_a != len_b) {
        return false;
    }

    if (len_a == 0) {
        return true;
    }

    return !memcmp_abs(array_a, array_b, len_a, abs_info);
}


void aws_array_eq_harness() {
    /* assumptions */
    size_t lhs_len;
    size_t rhs_len;
    size_t abs_lhs_len;
    size_t abs_rhs_len;

   __CPROVER_assume(lhs_len <= MAX_BUFFER_SIZE);
    __CPROVER_assume(rhs_len <= MAX_BUFFER_SIZE);
  
   //Abstraction related
    size_t lhs_cncrt = nondet_size_t();
    __CPROVER_assume(lhs_cncrt < lhs_len);
    size_t rhs_cncrt = nondet_size_t();
    __CPROVER_assume(rhs_cncrt < rhs_len);
   // __CPROVER_assume(rhs_cncrt == lhs_cncrt);

   struct ainfo abs_info;
    abs_info.l_c = lhs_cncrt;
    abs_info.l_len = lhs_len;
    abs_info.r_c = rhs_cncrt;
    abs_info.r_len = rhs_len;


 
   abs_lhs_len = get_abs_index(lhs_len, abs_info);
 
    void *abs_lhs = can_fail_malloc(abs_lhs_len);
    void *abs_rhs; 
    if (nondet_bool()) { /* rhs could be equal to lhs */
        rhs_len = lhs_len;
        abs_rhs_len = abs_lhs_len;
        abs_rhs = abs_lhs;
    } else {
      
        abs_rhs_len = get_abs_index(rhs_len, abs_info);    
        abs_rhs = can_fail_malloc(abs_rhs_len);
    }

    /* save current state of the parameters */
    struct store_byte_from_buffer old_byte_from_lhs;
    save_byte_from_array_abs((uint8_t *)abs_lhs, lhs_len, &old_byte_from_lhs, abs_info);
    struct store_byte_from_buffer old_byte_from_rhs;
    save_byte_from_array_abs((uint8_t *)abs_rhs, rhs_len, &old_byte_from_rhs, abs_info);

    /* pre-conditions */
    __CPROVER_assume((abs_lhs_len == 0) || AWS_MEM_IS_READABLE(abs_lhs, abs_lhs_len));
    __CPROVER_assume((abs_rhs_len == 0) || AWS_MEM_IS_READABLE(abs_rhs, abs_rhs_len));

    /* operation under verification */
    if (aws_array_eq_abs(abs_lhs, abs_lhs_len, abs_rhs, abs_rhs_len, abs_info)) {
        /* asserts equivalence */
        assert(abs_lhs_len == abs_rhs_len);
        if (abs_lhs_len > 0 && abs_lhs) {
            assert_bytes_match_abs((uint8_t *)abs_lhs, (uint8_t *)abs_rhs, lhs_len, abs_info);
        }
    }

    /* asserts both parameters remain unchanged */
    if (abs_lhs_len > 0 && abs_lhs) {
        assert_byte_from_buffer_matches_abs((uint8_t *)abs_lhs, &old_byte_from_lhs, abs_info);
    }
    if (abs_rhs_len > 0 && abs_rhs) {
        assert_byte_from_buffer_matches_abs((uint8_t *)abs_rhs, &old_byte_from_rhs, abs_info);
    }
}
