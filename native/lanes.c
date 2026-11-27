/*
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

What Lean cannot express or check, bound from C: libsodium for cryptography whose time must not
depend on secrets, fsync for durability, and a timed wait for a thread. Each function is
declared in `Lanes/Lib/Crypto/Sodium.lean`, `Lanes/Durable/IO/Journal.lean` or `Lanes/Runtime/IO/Park.lean`;
arguments are borrowed.
*/
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <sodium.h>
#include <lean/lean.h>

static lean_obj_res lanes_bytes(size_t size) {
    return lean_alloc_sarray(1, size, size);
}

LEAN_EXPORT lean_obj_res lanes_sha256(b_lean_obj_arg msg) {
    lean_object *out = lanes_bytes(crypto_hash_sha256_BYTES);
    crypto_hash_sha256(lean_sarray_cptr(out), lean_sarray_cptr(msg), lean_sarray_size(msg));
    return out;
}

LEAN_EXPORT lean_obj_res lanes_hmac_sha256(b_lean_obj_arg key, b_lean_obj_arg msg) {
    crypto_auth_hmacsha256_state state;
    lean_object *out = lanes_bytes(crypto_auth_hmacsha256_BYTES);
    crypto_auth_hmacsha256_init(&state, lean_sarray_cptr(key), lean_sarray_size(key));
    crypto_auth_hmacsha256_update(&state, lean_sarray_cptr(msg), lean_sarray_size(msg));
    crypto_auth_hmacsha256_final(&state, lean_sarray_cptr(out));
    sodium_memzero(&state, sizeof state);
    return out;
}

LEAN_EXPORT uint8_t lanes_same(b_lean_obj_arg a, b_lean_obj_arg b) {
    size_t size = lean_sarray_size(a);
    return size == lean_sarray_size(b)
        && sodium_memcmp(lean_sarray_cptr(a), lean_sarray_cptr(b), size) == 0;
}

LEAN_EXPORT lean_obj_res lanes_argon2id(b_lean_obj_arg password, b_lean_obj_arg salt,
                                        uint32_t ops, uint32_t mem_kib) {
    if (sodium_init() < 0 || lean_sarray_size(salt) != crypto_pwhash_SALTBYTES)
        lean_internal_panic("lanes: Argon2id cannot run");
    lean_object *out = lanes_bytes(32);
    if (crypto_pwhash(lean_sarray_cptr(out), 32, (const char *)lean_sarray_cptr(password),
                      lean_sarray_size(password), lean_sarray_cptr(salt), ops,
                      (size_t)mem_kib * 1024, crypto_pwhash_ALG_ARGON2ID13) != 0)
        lean_internal_panic_out_of_memory();
    return out;
}

LEAN_EXPORT lean_obj_res lanes_random_bytes(size_t size) {
    if (sodium_init() < 0)
        return lean_io_result_mk_error(lean_mk_io_user_error(
            lean_mk_string("lanes: libsodium has no source of randomness")));
    lean_object *out = lanes_bytes(size);
    randombytes_buf(lean_sarray_cptr(out), size);
    return lean_io_result_mk_ok(out);
}

LEAN_EXPORT lean_obj_res lanes_fsync(b_lean_obj_arg path) {
    int fd = open(lean_string_cstr(path), O_RDONLY | O_CLOEXEC);
    if (fd < 0) return lean_io_result_mk_error(lean_decode_io_error(errno, path));
    int failed = fsync(fd) == 0 ? 0 : errno;
    close(fd);
    if (failed) return lean_io_result_mk_error(lean_decode_io_error(failed, path));
    return lean_io_result_mk_ok(lean_box(0));
}

/* A thread waiting here sleeps in the operating system. One waiting on a task sleeps in Lean's
   task manager, which wakes every such thread whenever any task finishes. */
typedef struct {
    pthread_mutex_t mutex;
    pthread_cond_t cond;
    int permit;
} lanes_parker;

static lean_external_class *lanes_parker_class;
static pthread_once_t lanes_parker_once = PTHREAD_ONCE_INIT;

static void lanes_parker_free(void *data) {
    lanes_parker *p = data;
    pthread_cond_destroy(&p->cond);
    pthread_mutex_destroy(&p->mutex);
    free(p);
}

static void lanes_parker_each(void *data, b_lean_obj_arg f) { (void)data; (void)f; }

static void lanes_parker_register(void) {
    lanes_parker_class = lean_register_external_class(lanes_parker_free, lanes_parker_each);
}

LEAN_EXPORT lean_obj_res lanes_parker_new(void) {
    pthread_once(&lanes_parker_once, lanes_parker_register);
    lanes_parker *p = malloc(sizeof *p);
    if (!p) lean_internal_panic_out_of_memory();
    pthread_mutex_init(&p->mutex, NULL);
    pthread_condattr_t attr;
    pthread_condattr_init(&attr);
#ifndef __APPLE__
    pthread_condattr_setclock(&attr, CLOCK_MONOTONIC);
#endif
    pthread_cond_init(&p->cond, &attr);
    pthread_condattr_destroy(&attr);
    p->permit = 0;
    return lean_alloc_external(lanes_parker_class, p);
}

LEAN_EXPORT lean_obj_res lanes_park(b_lean_obj_arg parker, uint8_t timed, uint32_t ms) {
    lanes_parker *p = lean_get_external_data(parker);
    pthread_mutex_lock(&p->mutex);
    if (!p->permit) {
        if (!timed) {
            pthread_cond_wait(&p->cond, &p->mutex);
        } else {
#ifdef __APPLE__
            struct timespec t = { ms / 1000, (long)(ms % 1000) * 1000000 };
            pthread_cond_timedwait_relative_np(&p->cond, &p->mutex, &t);
#else
            struct timespec t;
            clock_gettime(CLOCK_MONOTONIC, &t);
            t.tv_sec += ms / 1000;
            t.tv_nsec += (long)(ms % 1000) * 1000000;
            if (t.tv_nsec >= 1000000000) { t.tv_sec += 1; t.tv_nsec -= 1000000000; }
            pthread_cond_timedwait(&p->cond, &p->mutex, &t);
#endif
        }
    }
    p->permit = 0;
    pthread_mutex_unlock(&p->mutex);
    return lean_box(0);
}

LEAN_EXPORT lean_obj_res lanes_unpark(b_lean_obj_arg parker) {
    lanes_parker *p = lean_get_external_data(parker);
    pthread_mutex_lock(&p->mutex);
    p->permit = 1;
    pthread_cond_signal(&p->cond);
    pthread_mutex_unlock(&p->mutex);
    return lean_box(0);
}
