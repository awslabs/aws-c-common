# Error Handling

## Basics

Every function that returns an `int` type returns either `AWS_OP_SUCCESS` (0) on success, or `AWS_OP_ERR` (-1) on failure.

```c
/* Example of function returning int type.
 * Returns AWS_OP_SUCCESS (0) on success.
 * Returns AWS_OP_ERR (-1) on failure. */
int aws_do_something(...);
```

And every function that returns a pointer, returns `NULL` on failure.

```c
/* Example of function returning a pointer type.
 * Returns a valid pointer on success.
 * Returns NULL on failure. */
struct aws_thing *aws_thing_new(...);
```

After a function fails, you call `aws_last_error()` to retrieve the actual error code. You can get strings for each error code via:
* `const char *aws_error_name(int error_code)` for the enum name
  * e.g. `34` -> `"AWS_ERROR_INVALID_ARGUMENT"`

* `const char *aws_error_str(int error_code)` for the English description
  * e.g. `34` -> `"An invalid argument was passed to a function."`

This error code is stored in a thread-local variable.

If you're authoring a function that needs to fail, you MUST call `aws_raise_error(error_code)` to set that thread-local error code before returning `AWS_OP_ERR` or `NULL`.

### Design

We do error handling this way because that's how other C libs do it. For example, [fopen()](https://en.cppreference.com/w/c/io/fopen) returns a pointer and if it's `NULL` you check `errno` to find out why. This way, functions can simply return a pointer, without polluting their function signature with confusing out-params. For consistency, we had other functions use thread-local variables as well, returning `AWS_OP_ERR` (-1) instead of returning the actual error code.

While this design pattern makes for graceful looking user code, it is very easy to make mistakes in implementation code, if you forget to call `aws_raise_error()` in all possible failure branches. Hence, this guide...

### Catching Errors

Error handling in a toy application might look like:
```c
/* For functions that return a pointer, NULL means failure */
struct aws_thing *thing = aws_thing_new(...);
if (thing == NULL) {
    int error_code = aws_last_error();
    printf("Failed to create thing: %s\n", aws_error_str(error_code));
    exit(error_code);
}

/* For functions that return an int, AWS_OP_ERR means failure */
if (aws_thing_do_something_that_may_fail(thing, ...) == AWS_OP_ERR) {
    int error_code = aws_last_error();
    printf("Failed to do something: %s\n", aws_error_str(error_code));
    exit(error_code);
}

/* You'll also see lots of code that doesn't explicitly compare the return value
 * against `AWS_OP_ERR` or `AWS_OP_SUCCESS`. Since AWS_OP_SUCCESS is zero,
 * it's "falsey", so the if branch is only taken on error. */
if (aws_thing_do_something_that_may_fail(thing, ...)) {
    int error_code = aws_last_error();
    printf("Failed to do something: %s\n", aws_error_str(error_code));
    exit(error_code);
}

/* DO NOT DO THIS */
aws_thing_do_something_that_may_fail(thing, ...); /* BAD */
if (aws_last_error() != 0) { /* BAD */
    /* This code assumes something went wrong because the thread-local
     * error code is non-zero. BUT nobody ever bothers to clear the
     * thread-local error code! It could be a stale value from earlier
     * in the program, and that error might have been handled just fine.
     * You should only check aws_last_error() after checking that a function
     * explicitly returned `AWS_OP_ERR` or `NULL` to indicate failure. */
    printf("I assume previous function call just failed");
    exit(aws_last_error());
}
```

### Raising Errors

When writing functions that may fail, you MUST ensure `aws_raise_error()` is called, to set that thread-local error code, before you ultimately return `NULL` or `AWS_OP_ERR`. DO NOT accidentally return the error-code itself.

```c
/* Sample for function that returns pointer type, where NULL means failure */
struct aws_thing *aws_thing_new(struct aws_allocator *allocator, uint32_t num_shinies) {
    if (num_shinies > AWS_NUM_SHINIES_MAX) {
        /* Set thread-local error code */
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        /* Return NULL to indicate failure */
        return NULL;
    }

    struct aws_thing *thing = aws_mem_calloc(allocator, 1, sizeof(struct aws_thing));
    thing->num_shinies = num_shinies;

    /* Returning a valid pointer means success */
    return thing;
}

/* Sample for function that returns int, where AWS_OP_ERR(-1) means failure */
int aws_sub_u64_checked(uint64_t a, uint64_t b, uint64_t *result) {
    if (a < b) {
        aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
        return AWS_OP_ERR;

        /* You can also do: return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
         * aws_raise_error() always return AWS_OP_ERR, so you can call it on
         * the same line as return, if your function returns int. */
    }

    *result = a - b;
    return AWS_OP_SUCCESS;
}


/* DO NOT DO THIS */
int aws_sub_u64_checked(uint64_t a, uint64_t b, uint64_t *result) {
    if (a < b)
        /* BAD: Failed to set thread-local error code. */
        return AWS_OP_ERR;
    ...

/* DO NOT DO THIS */
int aws_sub_u64_checked(uint64_t a, uint64_t b, uint64_t *result) {
    if (a < b)
        /* BAD: Failed to set thread-local error code.
         * BAD: Accidentally returned error code, but should return AWS_OP_ERR. */
        return AWS_ERROR_OVERFLOW_DETECTED;
    ...
```

If you're writing a function that may fail, and it needs to call other `aws_` functions that may fail, you can assume the other function set the error code explaining why.

```c
int aws_my_new_function(...) {
    if (aws_some_other_thing_that_may_fail(...) != AWS_OP_SUCCESS) {
        /* Here, it's OK not to call aws_raise_error().
         * The other aws_ function already set the thread-local error code
         * that we want the user to see. */
        return AWS_OP_ERR;
    }
    ...
```

But beware that the thread-local error code can change. You may want to store it (e.g. `int error_code = aws_last_error();`) if you need to do a lot of other stuff between the error originally occurring, and your function finally returning `AWS_OP_ERR`. In general, simple cleanup and logging functions won't change the error code. But if you're doing more than that, may as well be safe and store it. Here's an example:
```c
    ...
    if (aws_some_other_thing_that_may_fail(...) != AWS_OP_SUCCESS) {
        /* Preserve error code */
        int error_code = aws_last_error();

        ...many more lines of code...
        ...maybe invoking user callbacks, where anything can happen...
        ...and maybe thread-local error code gets changed...

        /* Re-raise, ensuring caller gets the error code you intend */
        return aws_raise_error(error_code);
    }
```

### Error codes in callbacks

For asynchronous APIs, where results are delivered via callback, error codes are delivered by their actual value. A callback function might look like:
```c
void on_some_async_operation_complete(int error_code, void *user_data) {
    if (error_code != 0) {
        printf("Operation failed: %s\n", aws_error_str(error_code));
        ...
```

 The thread-local error code variable is not used with callbacks. `AWS_OP_ERR` and `AWS_OP_SUCCESS` are not used. DO NOT call `aws_raise_error()` before invoking a callback. DO NOT call `aws_last_error()` within a callback to check for error.

## Best Practices

Error handling is extra difficult in C, because C doesn't have automatic destructors or garbage collection. If you need to do several things in sequence, and the last thing fails, you need to manually undo all previous steps.

We suggest keeping things as simple and maintainable as we can get away with.

Our style has evolved with time, and you'll find lots of old code violating these rules, but here are best practices.

### If a function can't fail, make it void

Don't return `int` "just in case it might fail someday" or "for consistency with other functions".

This is especially important for low-level datastructure APIs, or any function that cleans up or destroys something.

Imagine there's some "clean up" function that needs to use your function, and your function returns `int`. What is that clean up function supposed to do? Try to handle the error? How? Should it stop even trying to clean up? Leak memory?

If your function creates some complex stateful class, that takes lots of parameters, and can't currently fail, but you can totally imagine a future where it can, then yeah give it an API where it might fail. But for simple stuff that's just allocating: no.

### Memory Allocation Cannot Fail

Don't write code that tries to handle Out Of Memory (OOM). `aws_mem_acquire()` and `aws_mem_calloc()` will never return `NULL`, they will simply abort if the OS fails to allocate.

For the first few months of aws-c development, we tried to handle Out Of Memory. Lots of code was written that tried to deal with this; little of it was ever tested. In the end we decided it wasn't worth the effort. Swift and Rust just abort if you push into a vector and it can't expand. We should too. Now, `aws_allocator` will abort before it ever returns `NULL`.

Unfortunately, after making this change we didn't go back and simplify APIs that could no longer fail, because it would be a large breaking change. So functions like `aws_hash_table_put()` return `int` but it's always `AWS_OP_SUCCESS` and you should never bother checking it. It sucks, but you just have to "know" which errors should or shouldn't be checked for. It's generally just our older datastructure APIs that suffer from this (e.g. aws_byte_buf, aws_array_list, aws_hash_table). If you initialized these with an allocator, so they can grow dynamically, then they can't fail. But if you initialized them with a fixed size, or no allocator, you should still check for errors. For pretty much all other APIs, you must still check for errors.

Also, we didn't proactively remove error-handling code where the errors couldn't happen anymore. But if you're ever editing such code, do please simplify it along with your changes! Also, if you find an old function that can't fail, but its docs say it may, update the docs!

### Don't try to handle NULL (except in destructors)

If a function doesn't expect `NULL`, then don't try to handle `NULL`.

Feel free to add `AWS_ASSERT(some_pointer);` if you want your code to be clear about its refusal to deal with NULL.

Imagine you tried to handle `NULL`, then functions then function that could be `void` now must return `int`, just in case `NULL` is passed in and they can't do anything! Now you have a function with an error code, but it can't possible fail in working code. But users wonder whether or not they should be checking for failure from this function... and maybe stop checking for errors on other functions that *can* fail randomly... if it's a mess. Also, be honest, you're never going to add tests for all that error handling code.

One big exception is destructors (i.e. `clean_up()`, `destroy()`, `release()`). We'll touch on this later, but to make error-handling code as simple as possible, we want it to be safe to call destructor functions whether or not the thing was ever successfully created.

### AWS_ASSERT() vs AWS_FATAL_ASSERT() vs aws_raise_error()

How do you choose when to assert, vs real error handling? Asserts will simply abort the program, so only use them for detecting internal bugs. We *never* want users from Java or Python to hit an assert. So things like validating a number's value should be real error checks, because the number might come from a Java user.

`AWS_ASSERT()` does nothing in Release builds, it only checks in Debug. Use this for basic sanity checks that NULL isn't being passed into a function, or as a comment to future programmers "don't worry, this can't possibly be true right now", or to do an expensive check you don't want happening in Release builds. Note that most language bindings (e.g. _awscrt.so in aws-crt-python) are *never* built in Debug.

`AWS_FATAL_ASSERT()` still runs in Release builds. Use this to catch bugs that might occur in language binding code (which is seldom built in Debug), or for internal bugs you worry are too complex to encounter in a Debug build.

Use `aws_raise_error()` (real error handling) for everything else.

### init() / clean_up() example

Here's an example, with an "init / clean_up" style struct, where any initialization step may fail, and we'd need to undo the previous steps:
```c
int aws_thing_init(struct aws_thing *thing) {
    /* First, zero things out, in case memory was uninitialized.
     * That way we can safely call clean_up() on each member,
     * even if we didn't fully initialize everything.*/
    AWS_ZERO_STRUCT(*thing);

    if (aws_complex_part_1_init(&thing->part_1) != AWS_OP_SUCCESS) {
        /* Prefer early-out patterns, vs deeply embedded if-branches */
        goto error;
    }

    if (aws_complex_part_2_init(&thing->part_2) != AWS_OP_SUCCESS) {
        /* goto is fine in C */
        goto error;
    }

    if (aws_complex_part_3_init(&thing->part_3) != AWS_OP_SUCCESS) {
        goto error;
    }

    return AWS_OP_SUCCESS;

error:
    /* Just call the clean_up() function, rather than repeating
     * the code that cleans up individual members */
    aws_thing_clean_up(thing);

    /* Note: we didn't set thread-local error code before returning AWS_OP_ERR,
     * because we assume it was already set by the aws_complex_part_N_init()
     * failure that led us here */
    return AWS_OP_ERR;
}

void aws_thing_clean_up(struct aws_thing *thing) {
    /* It's safe to try and clean up aws_ types, even if they were never
     * initialized. We build all our "destructors" to be idempotent
     * and safe to call on zeroed-out memory.
     * This lets us have nice clean simple clean up code like so: */
    aws_complex_part_3_clean_up(&thing->part_3);
    aws_complex_part_2_clean_up(&thing->part_2);
    aws_complex_part_1_clean_up(&thing->part_1);

    /* Finally, zero things out so the clean_up() is idempotent */
    AWS_ZERO_STRUCT(*thing);
}
```

And here are some ways NOT to do it:
```c
/* DO NOT DO THIS (each failed step tries to clean up previous steps) */
int aws_thing_init(struct aws_thing *thing) {
    AWS_ZERO_STRUCT(*thing);

    if (aws_complex_part_1_init(&thing->part_1) != AWS_OP_SUCCESS) {
        return AWS_OP_ERR;
    }

    if (aws_complex_part_2_init(&thing->part_2) != AWS_OP_SUCCESS) {
        aws_complex_part_1_clean_up(&thing->part_1);
        return AWS_OP_ERR;
    }

    if (aws_complex_part_3_init(&thing->part_3) != AWS_OP_SUCCESS) {
        /* BAD: If clean up code is in so many places, and subtly different
         * each time, it's really easy to make a mistake. */
        aws_complex_part_2_clean_up(&thing->part_2);
        aws_complex_part_1_clean_up(&thing->part_1);
        return AWS_OP_ERR;
    }

    return AWS_OP_SUCCESS;
}

/* DO NOT DO THIS (multiple goto labels) */
int aws_thing_init(struct aws_thing *thing) {
    AWS_ZERO_STRUCT(*thing);

    if (aws_complex_part_1_init(&thing->part_1) != AWS_OP_SUCCESS) {
        return AWS_OP_ERR;
    }

    if (aws_complex_part_2_init(&thing->part_2) != AWS_OP_SUCCESS) {
        goto clean_up_part_1;
    }

    if (aws_complex_part_3_init(&thing->part_3) != AWS_OP_SUCCESS) {
        /* BAD: having multiple goto labels is a copy/paste bug waiting to happen */
        goto clean_up_part_2;
    }

    return AWS_OP_SUCCESS;

clean_up_part_2:
    /* BAD: if you try to clean up individual parts, you repeat code that's
     * already in clean_up(). You risk bugs where someone adds a new member,
     * and forgets to clean it up from here too. */
    aws_complex_part_2_clean_up(&thing->part_2);
clean_up_part_1:
    aws_complex_part_1_clean_up(&thing->part_1);
    return AWS_OP_ERR;
}

/* DO NOT DO THIS (deep if statements) */
int aws_thing_init(struct aws_thing *thing) {
    AWS_ZERO_STRUCT(*thing);

    if (aws_complex_part_1_init(&thing->part_1) == AWS_OP_SUCCESS) {
        if (aws_complex_part_2_init(&thing->part_2) == AWS_OP_SUCCESS) {
            if (aws_complex_part_3_init(&thing->part_3) == AWS_OP_SUCCESS) {
                /* BAD: You end up with most of your code indented
                 * 5+ levels deep. Adding more checks results in a
                 * huge diff as everything get indented even more.
                 * It actually doesn't look so bad in this example,
                 * but believe me it sucks in real life. */
                return AWS_OP_SUCCESS;
            }
            aws_complex_part_2_clean_up(&thing->part_2);
        }
        aws_complex_part_1_clean_up(&thing->part_1);
    }

    return AWS_OP_ERR;
}
```

### new() / destroy() example

Here's an example that returns a pointer, and does a bit more:
```c
struct aws_thing *aws_thing_new(struct aws_allocator *alloc,
                                    const struct aws_thing_options *options) {
    /* DO NOT do real error-checking for NULL args, that way lies madness.
     * You MAY do these debug-only statements that kill the program */
    AWS_ASSERT(alloc);
    AWS_ASSERT(options);

    /* Before creating anything, do real error checking on values that
     * might come down from language bindings. Not NULL checks, but other
     * more subtle stuff */
    if (options->timeout_ms > AWS_THING_TIMEOUT_MS_MAX) {
        /* Log the exact issue, since "invalid argument" is vague
         * when there are lots of arguments */
        AWS_LOGF_ERROR(..., "timeout_ms has invalid value");
        /* Set thread-local error code before returning NULL */
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return NULL;
    }

    /* Use aws_mem_calloc() to get memory that's already zeroed-out. This
     * reduces bugs where you forget to initialize a member */
    struct aws_thing *thing = aws_mem_calloc(alloc, 1, sizeof(struct aws_thing));

    /* Don't need to check if thing == NULL because allocation can't fail */

    /* Set allocator (and other things that can't possibly fail) first, so we
     * can use the destroy() function to clean up if anything else goes wrong */
    thing->alloc = alloc;
    thing->timeout_ms = options->timeout_ms;

    if (aws_complex_part_1_init(&thing->part_1) != AWS_OP_SUCCESS) {
        goto error;
    }

    if (aws_complex_part_2_init(&thing->part_2) != AWS_OP_SUCCESS) {
        goto error;
    }

    if (aws_complex_part_3_init(&thing->part_3) != AWS_OP_SUCCESS) {
        goto error;
    }

    return thing;

error:
    aws_thing_destroy(thing);

    /* Note: we didn't set thread-local error code before returning NULL,
     * because we assume it was already set by the aws_complex_part_N_init()
     * failure that led us here */
    return NULL;
}

void aws_thing_destroy(struct aws_thing *thing) {
    /* "destructor" functions are the only place we check for NULL, so user
     * can naively call it, whether or not it was successfully created */
    if (thing == NULL) {
        return;
    }

    aws_complex_part_3_clean_up(&thing->part_3);
    aws_complex_part_2_clean_up(&thing->part_2);
    aws_complex_part_1_clean_up(&thing->part_1);

    aws_mem_release(thing->alloc, thing);
}
```

## In Hindsight

It's too late to change any of this, but here's graebm's personal opinion for anyone starting down a similar path.

### thread-local error codes are too hard

IMHO it's too easy to make a mistake, and forget to `aws_raise_error()` before returning `AWS_OP_ERR`. When this happens, the user gets a nonsense value from `aws_last_error()`, and it's very hard to know what is actually failing.

IMHO we should have done something like Rust's [std::result<T, E>](https://doc.rust-lang.org/std/result/), Swift's [Result<Success,Failure>](https://developer.apple.com/documentation/swift/result), and C++'s [std::expected<T,E>](https://en.cppreference.com/w/cpp/utility/expected). If we returned errors by value, we wouldn't have bugs where we forgot to set `aws_raise_error()`, or bugs where `aws_last_error()` was accidentally overwritten. C doesn't have generics, but you can create something like them using macros (see [future.h](https://github.com/awslabs/aws-c-io/blob/7e75f17400ca2cfdc296865b9c2b10323f49a9c5/include/aws/io/future.h#L30)), or just write:
```c
struct aws_thing_result {
    struct aws_thing *ok;
    int err;
};

struct aws_thing_result aws_thing_new(...);
```

And functions that don't return pointers can just return the error code by value:
```
/* returns AWS_OK (0) on success, or the error code */
int aws_thing_do_something_that_may_fail(...);
```

### int error codes lose information

Exceptions in other languages can carry a lot more information than int error codes. If a Java exception occurs within a C callback, all the information from that callback must be thrown out. The Java user ultimately sees something less-than-useful like AWS_ERROR_HTTP_CALLBACK_FAILURE. We must tell the Java user to enable CRT logging to see what's actually going wrong. It's not idiomatic.

IMHO errors shouldn't just be ints, they should carry lots more information (e.g. custom message, chain of caused_by, is_retryable, etc). But this would make them "heavier", so we wouldn't want to use them somewhere performance sensitive, like querying a hash table. We could reserve "rich" errors for the APIs that language bindings call directly. We might even be able to create a Java exception chain where some of those came from our "rich" errors.
