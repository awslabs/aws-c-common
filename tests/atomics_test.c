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

#include <aws/common/atomics.h>
#include <aws/common/common.h>
#include <aws/common/condition_variable.h>
#include <aws/common/mutex.h>
#include <aws/common/thread.h>

#include <aws/testing/aws_test_harness.h>

AWS_TEST_CASE(atomics_semantics, t_semantics)
static int t_semantics(struct aws_allocator *allocator, void *ctx) {
    /*
     * This test verifies that the atomics work properly on a single thread.
     * Because we're only accessing from a single thread, program order fully constrains
     * the order in which all loads and stores can happen, and so our memory order selection
     * doesn't matter. We do however use a variety of memory orders to ensure that they
     * are accepted.
     */
    (void)ctx;
    (void)allocator;

    /* These provide us with some unique test pointers */
    int dummy_1, dummy_2, dummy_3;

    void *expected_ptr;
    aws_atomic_int_t expected_int;

    struct aws_atomic_var var;

    /* First, pointer tests */
    aws_atomic_init_ptr(&var, &dummy_1);
    ASSERT_PTR_EQUALS(&dummy_1, aws_atomic_load_ptr(&var, aws_memory_order_relaxed));
    ASSERT_PTR_EQUALS(&dummy_1, aws_atomic_swap_ptr(&var, &dummy_2, aws_memory_order_acq_rel));
    ASSERT_PTR_EQUALS(&dummy_2, aws_atomic_load_ptr(&var, aws_memory_order_acquire));
    aws_atomic_store_ptr(&var, &dummy_1, aws_memory_order_release);
    ASSERT_PTR_EQUALS(&dummy_1, aws_atomic_load_ptr(&var, aws_memory_order_acquire));

    expected_ptr = &dummy_3;
    ASSERT_FALSE(aws_atomic_compare_exchange_ptr(
        &var, &expected_ptr, &dummy_3, aws_memory_order_release, aws_memory_order_relaxed));
    ASSERT_PTR_EQUALS(&dummy_1, aws_atomic_load_ptr(&var, aws_memory_order_acquire));
    ASSERT_PTR_EQUALS(&dummy_1, expected_ptr);

    ASSERT_TRUE(aws_atomic_compare_exchange_ptr(
        &var, &expected_ptr, &dummy_3, aws_memory_order_release, aws_memory_order_relaxed));
    ASSERT_PTR_EQUALS(&dummy_3, aws_atomic_load_ptr(&var, aws_memory_order_acquire));

    /* Integer tests */
    aws_atomic_init_int(&var, 12345);
    ASSERT_INT_EQUALS(12345, aws_atomic_load_int(&var, aws_memory_order_relaxed));
    aws_atomic_store_int(&var, 54321, aws_memory_order_release);
    ASSERT_INT_EQUALS(54321, aws_atomic_load_int(&var, aws_memory_order_acquire));
    ASSERT_INT_EQUALS(54321, aws_atomic_swap_int(&var, 9999, aws_memory_order_acq_rel));
    ASSERT_INT_EQUALS(9999, aws_atomic_load_int(&var, aws_memory_order_acquire));

    expected_int = 1111;
    ASSERT_FALSE(
        aws_atomic_compare_exchange_int(&var, &expected_int, 0, aws_memory_order_acq_rel, aws_memory_order_relaxed));
    ASSERT_INT_EQUALS(9999, aws_atomic_load_int(&var, aws_memory_order_acquire));
    ASSERT_INT_EQUALS(9999, expected_int);
    ASSERT_TRUE(aws_atomic_compare_exchange_int(
        &var, &expected_int, 0x7000, aws_memory_order_acq_rel, aws_memory_order_relaxed));
    ASSERT_INT_EQUALS(0x7000, aws_atomic_load_int(&var, aws_memory_order_acquire));

    ASSERT_INT_EQUALS(0x7000, aws_atomic_fetch_add(&var, 6, aws_memory_order_relaxed));
    ASSERT_INT_EQUALS(0x7006, aws_atomic_fetch_sub(&var, 0x16, aws_memory_order_relaxed));
    ASSERT_INT_EQUALS(0x6ff0, aws_atomic_fetch_or(&var, 0x14, aws_memory_order_relaxed));
    ASSERT_INT_EQUALS(0x6ff4, aws_atomic_fetch_and(&var, 0x2115, aws_memory_order_relaxed));
    ASSERT_INT_EQUALS(0x2114, aws_atomic_fetch_xor(&var, 0x3356, aws_memory_order_relaxed));
    ASSERT_INT_EQUALS(0x1242, aws_atomic_load_int(&var, aws_memory_order_acquire));

    /* Proving that atomic_thread_fence works is hard, for now just demonstrate that it doesn't crash */
    aws_atomic_thread_fence(aws_memory_order_relaxed);
    aws_atomic_thread_fence(aws_memory_order_release);
    aws_atomic_thread_fence(aws_memory_order_acquire);
    aws_atomic_thread_fence(aws_memory_order_acq_rel);

    return 0;
}

union padded_var {
    struct aws_atomic_var var;
    char pad[32];
};

/*
 * We define the race loop in a macro to encourage inlining; performance matters when trying to tickle low-level data
 * races
 */
struct one_race {
    struct aws_atomic_var *wait;
    struct aws_atomic_var **vars;
    struct aws_atomic_var **observations;
};

static struct one_race *races;
static size_t n_races, n_vars, n_observations, n_participants;

static int done_racing;
static struct aws_mutex done_mutex = AWS_MUTEX_INIT;
static struct aws_condition_variable done_cvar = AWS_CONDITION_VARIABLE_INIT;

static struct aws_atomic_var last_race_index;

static struct aws_atomic_var *alloc_var(struct aws_allocator *alloc, const struct aws_atomic_var *template) {
    struct aws_atomic_var *var = aws_mem_acquire(alloc, sizeof(union padded_var));
    if (!var) {
        abort();
    }

    memcpy(var, template, sizeof(*var));
    return var;
}

static void setup_races(
    struct aws_allocator *alloc,
    size_t n_races_v,
    size_t n_vars_v,
    size_t n_observations_v,
    const struct aws_atomic_var *init_vars,
    const struct aws_atomic_var *init_observations) {
    struct aws_atomic_var init_wait;
    aws_atomic_init_int(&init_wait, 0);

    n_races = n_races_v;
    n_vars = n_vars_v;
    n_observations = n_observations_v;

    races = aws_mem_acquire(alloc, n_races * sizeof(*races));
    if (!races) {
        abort();
    }

    for (size_t i = 0; i < n_races; i++) {
        races[i].wait = alloc_var(alloc, &init_wait);

        races[i].vars = aws_mem_acquire(alloc, n_vars * sizeof(*races[i].vars));
        races[i].observations = aws_mem_acquire(alloc, n_observations * sizeof(*races[i].observations));
        if (!races[i].vars || !races[i].observations) {
            abort();
        }

        for (size_t j = 0; j < n_vars; j++) {
            races[i].vars[j] = alloc_var(alloc, &init_vars[j]);
        }
        for (size_t j = 0; j < n_observations; j++) {
            races[i].observations[j] = alloc_var(alloc, &init_observations[j]);
        }
    }
}

static void free_races(struct aws_allocator *alloc) {
    for (size_t i = 0; i < n_races; i++) {
        for (size_t j = 0; j < n_vars; j++) {
            aws_mem_release(alloc, races[i].vars[j]);
        }
        for (size_t j = 0; j < n_observations; j++) {
            aws_mem_release(alloc, races[i].observations[j]);
        }
        aws_mem_release(alloc, races[i].wait);
        aws_mem_release(alloc, races[i].vars);
        aws_mem_release(alloc, races[i].observations);
    }
    aws_mem_release(alloc, races);
}

static bool are_races_done(void *ignored) {
    (void)ignored;

    return done_racing >= n_participants;
}

static int run_races(
    size_t *last_race,
    struct aws_allocator *alloc,
    int n_participants_local,
    void (*race_fn)(void *vp_participant)) {
    int *participant_indexes = alloca(n_participants_local * sizeof(*participant_indexes));
    struct aws_thread *threads = alloca(n_participants_local * sizeof(struct aws_thread));

    *last_race = -1;
    n_participants = n_participants_local;
    done_racing = false;
    aws_atomic_init_int(&last_race_index, 0);

    for (int i = 0; i < n_participants; i++) {
        participant_indexes[i] = i;
        ASSERT_SUCCESS(aws_thread_init(&threads[i], alloc));
        ASSERT_SUCCESS(aws_thread_launch(&threads[i], race_fn, &participant_indexes[i], NULL));
    }

    ASSERT_SUCCESS(aws_mutex_lock(&done_mutex));
    if (aws_condition_variable_wait_for_pred(&done_cvar, &done_mutex, 1000000000ULL /* 1s */, are_races_done, NULL) ==
        AWS_OP_ERR) {
        ASSERT_TRUE(aws_last_error() == AWS_ERROR_COND_VARIABLE_TIMED_OUT);
    }

    if (done_racing >= n_participants) {
        *last_race = n_races;
    } else {
        *last_race = aws_atomic_load_int(&last_race_index, aws_memory_order_relaxed);
        if (*last_race == (size_t)-1) {
            /* We didn't even see the first race complete */
            *last_race = 0;
        }
    }
    ASSERT_SUCCESS(aws_mutex_unlock(&done_mutex));

    /* Poison all remaining races to make sure the threads exit quickly */
    for (size_t i = 0; i < n_races; i++) {
        aws_atomic_store_int(races[i].wait, n_participants, aws_memory_order_relaxed);
    }

    for (size_t i = 0; i < n_participants; i++) {
        ASSERT_SUCCESS(aws_thread_join(&threads[i]));
        aws_thread_clean_up(&threads[i]);
    }

    aws_atomic_thread_fence(aws_memory_order_acq_rel);

    return 0;
}

static void notify_race_completed() {
    if (aws_mutex_lock(&done_mutex)) {
        abort();
    }

    done_racing++;
    if (done_racing >= n_participants) {
        if (aws_condition_variable_notify_all(&done_cvar)) {
            abort();
        }
    }

    if (aws_mutex_unlock(&done_mutex)) {
        abort();
    }
}

#define DEFINE_RACE(race_name, vn_participant, vn_race)                                                                \
    static void race_name##_iter(int participant, struct one_race *race);                                              \
    static void race_name(void *vp_participant) {                                                                      \
        int participant = *(int *)vp_participant;                                                                      \
        size_t n_races_local = n_races;                                                                                \
        size_t n_participants_local = n_participants;                                                                  \
        for (size_t i = 0; i < n_races_local; i++) {                                                                   \
            while (i > 0 && aws_atomic_load_int(races[i - 1].wait, aws_memory_order_relaxed) < n_participants_local) { \
                /* spin */                                                                                             \
            }                                                                                                          \
            if (participant == 0) {                                                                                    \
                aws_atomic_store_int(&last_race_index, i - 1, aws_memory_order_relaxed);                               \
            }                                                                                                          \
            race_name##_iter(participant, &races[i]);                                                                  \
            aws_atomic_fetch_add(races[i].wait, 1, aws_memory_order_relaxed);                                          \
        }                                                                                                              \
        notify_race_completed();                                                                                       \
        aws_atomic_thread_fence(aws_memory_order_release);                                                             \
    }                                                                                                                  \
    static void race_name##_iter(int vn_participant, struct one_race *vn_race) /* NOLINT */

/*
 * See http://www.cs.cmu.edu/~410-f10/doc/Intel_Reordering_318147.pdf #2.3
 */
DEFINE_RACE(loads_reordered_with_older_stores, participant, race) {
    struct aws_atomic_var *my_var = race->vars[participant];
    struct aws_atomic_var *their_var = race->vars[1 - participant];
    struct aws_atomic_var *observed = race->observations[participant];
    /*
     * This test may fail with any other ordering, even on the relatively relaxed x86 architecture.
     * This failure seems relatively easy to reproduce, so this is a good way to test for seq_cst ordering.
     */
    enum aws_memory_order store_order = aws_memory_order_seq_cst;
    enum aws_memory_order load_order = aws_memory_order_seq_cst;

    aws_atomic_store_int(my_var, 1, store_order);
    aws_atomic_store_int(observed, aws_atomic_load_int(their_var, load_order), aws_memory_order_relaxed);
}

AWS_TEST_CASE(atomics_loads_reordered_with_older_stores, t_loads_reordered_with_older_stores)
static int t_loads_reordered_with_older_stores(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_atomic_var template[2];
    size_t last_race;
    aws_atomic_init_int(&template[0], 0);
    aws_atomic_init_int(&template[1], 0);

    setup_races(allocator, 100000, 2, 2, template, template);
    run_races(&last_race, allocator, 2, loads_reordered_with_older_stores);

    for (size_t i = 0; i < last_race; i++) {
        aws_atomic_int_t a = aws_atomic_load_int(races[i].observations[0], aws_memory_order_relaxed);
        aws_atomic_int_t b = aws_atomic_load_int(races[i].observations[1], aws_memory_order_relaxed);

        ASSERT_TRUE(a || b, "Race at iteration %zu", i);
    }

    free_races(allocator);

    return 0;
}

/*
 * The following race races these two threads:
 *
 * Thread 1:
 *   DATA <- 1 [relaxed]
 *   FLAG <- 2 [release]
 * Thread 2:
 *   Read FLAG [acquire]
 *   Read DATA [relaxed]
 *
 * We expect that, if FLAG is observed to be 2, then DATA must be 1, due to
 * acquire-release ordering.
 *
 * Note however, that this race never fails on x86; on x86 all loads have acquire semantics,
 * and all stores have release semantics.
 */
DEFINE_RACE(acquire_to_release_one_direction, participant, race) {
    struct aws_atomic_var *flag = race->vars[0];
    struct aws_atomic_var *protected_data = race->vars[1];
    struct aws_atomic_var *observation = race->observations[0];

    if (participant == 0) {
        aws_atomic_store_int(protected_data, 1, aws_memory_order_relaxed);
        aws_atomic_store_int(flag, 2, aws_memory_order_release);
    } else {
        aws_atomic_int_t flagval = aws_atomic_load_int(flag, aws_memory_order_acquire);
        aws_atomic_int_t dataval = aws_atomic_load_int(protected_data, aws_memory_order_relaxed);
        aws_atomic_store_int(observation, flagval ^ dataval, aws_memory_order_relaxed);
    }
}

AWS_TEST_CASE(atomics_acquire_to_release_one_direction, t_acquire_to_release_one_direction)
static int t_acquire_to_release_one_direction(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_atomic_var template[2];
    size_t last_race;
    aws_atomic_init_int(&template[0], 0);
    aws_atomic_init_int(&template[1], 0);

    setup_races(allocator, 100000, 2, 1, template, template);
    run_races(&last_race, allocator, 2, acquire_to_release_one_direction);

    for (size_t i = 0; i < last_race; i++) {
        aws_atomic_int_t a = aws_atomic_load_int(races[i].observations[0], aws_memory_order_relaxed);

        /*
         * If we see that flag == 2, then the data observation must be 1.
         * If flag == 0, then the data value may be anything.
         */
        ASSERT_FALSE(a == 2, "Acquire-release ordering failed at iteration %zu", i);
    }

    free_races(allocator);

    return 0;
}

/*
 * The following race races these two threads:
 *
 * Thread 1:
 *   Read DATA [relaxed] (observation 0)
 *   FLAG <- 1 [release]
 * Thread 2:
 *   Read FLAG [acquire] (observation 1)
 *   DATA <- 1 [relaxed]
 *
 * We expect that, if FLAG is observed to be 1, then DATA must be 0, due to
 * acquire-release ordering.
 *
 * Note however, that this race never fails on x86; on x86 all loads have acquire semantics,
 * and all stores have release semantics.
 */
DEFINE_RACE(acquire_to_release_mixed, participant, race) {
    struct aws_atomic_var *flag = race->vars[0];
    struct aws_atomic_var *protected_data = race->vars[1];

    if (participant == 0) {
        aws_atomic_store_int(
            race->observations[0],
            aws_atomic_load_int(protected_data, aws_memory_order_relaxed),
            aws_memory_order_relaxed);
        aws_atomic_store_int(flag, 2, aws_memory_order_release);
    } else {
        aws_atomic_store_int(
            race->observations[1], aws_atomic_load_int(flag, aws_memory_order_acquire), aws_memory_order_relaxed);
        aws_atomic_store_int(protected_data, 1, aws_memory_order_relaxed);
    }
}

AWS_TEST_CASE(atomics_acquire_to_release_mixed, t_acquire_to_release_mixed)
static int t_acquire_to_release_mixed(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_atomic_var template[2];
    size_t last_race;
    aws_atomic_init_int(&template[0], 0);
    aws_atomic_init_int(&template[1], 0);

    setup_races(allocator, 100000, 2, 2, template, template);
    run_races(&last_race, allocator, 2, acquire_to_release_mixed);

    for (size_t i = 0; i < last_race; i++) {
        aws_atomic_int_t data_observation = aws_atomic_load_int(races[i].observations[0], aws_memory_order_relaxed);
        aws_atomic_int_t flag_observation = aws_atomic_load_int(races[i].observations[0], aws_memory_order_relaxed);

        /*
         * If we see that flag == 2, then the data observation must be 1.
         * If flag == 0, then the data value may be anything.
         */
        ASSERT_FALSE(flag_observation && !data_observation, "Acquire-release ordering failed at iteration %zu", i);
    }

    free_races(allocator);

    return 0;
}
