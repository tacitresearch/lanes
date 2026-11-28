/*
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

What Lean cannot express or check, bound from C: OpenSSL's libcrypto for cryptography whose time
must not depend on secrets and for random bytes, fsync for durability, and a timed wait for a
thread. Each function
is declared in `Lanes/Lib/Crypto/Native.lean`, `Lanes/Durable/IO/Journal.lean` or
`Lanes/Runtime/IO/Park.lean`; arguments are borrowed.

The OpenSSL is the one Lean's toolchain ships, as for `native/tls.c`: the functions below are
declared as OpenSSL 3 and 4 declare them (`scripts/tls-declarations.py` checks it). Argon2id
needs OpenSSL 3.2 or later.
*/
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <pthread.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <lean/lean.h>

typedef struct evp_md_st EVP_MD;
typedef struct evp_kdf_st EVP_KDF;
typedef struct evp_kdf_ctx_st EVP_KDF_CTX;
typedef struct ossl_lib_ctx_st OSSL_LIB_CTX;
typedef struct ossl_param_st OSSL_PARAM;
typedef struct ossl_param_bld_st OSSL_PARAM_BLD;
unsigned char *SHA256(const unsigned char *d, size_t n, unsigned char *md);
const EVP_MD *EVP_sha256(void);
unsigned char *HMAC(const EVP_MD *evp_md, const void *key, int key_len,
                    const unsigned char *data, size_t data_len,
                    unsigned char *md, unsigned int *md_len);
int CRYPTO_memcmp(const void *in_a, const void *in_b, size_t len);
int RAND_bytes(unsigned char *buf, int num);
OSSL_PARAM_BLD *OSSL_PARAM_BLD_new(void);
void OSSL_PARAM_BLD_free(OSSL_PARAM_BLD *bld);
int OSSL_PARAM_BLD_push_uint32(OSSL_PARAM_BLD *bld, const char *key, uint32_t val);
int OSSL_PARAM_BLD_push_octet_string(OSSL_PARAM_BLD *bld, const char *key, const void *buf,
                                     size_t bsize);
OSSL_PARAM *OSSL_PARAM_BLD_to_param(OSSL_PARAM_BLD *bld);
void OSSL_PARAM_clear_free(OSSL_PARAM *params);
EVP_KDF *EVP_KDF_fetch(OSSL_LIB_CTX *libctx, const char *algorithm, const char *properties);
void EVP_KDF_free(EVP_KDF *kdf);
EVP_KDF_CTX *EVP_KDF_CTX_new(EVP_KDF *kdf);
void EVP_KDF_CTX_free(EVP_KDF_CTX *ctx);
int EVP_KDF_derive(EVP_KDF_CTX *ctx, unsigned char *key, size_t keylen,
                   const OSSL_PARAM *params);

static lean_obj_res lanes_bytes(size_t size) {
    return lean_alloc_sarray(1, size, size);
}

LEAN_EXPORT lean_obj_res lanes_sha256(b_lean_obj_arg msg) {
    lean_object *out = lanes_bytes(32);
    if (!SHA256(lean_sarray_cptr(msg), lean_sarray_size(msg), lean_sarray_cptr(out)))
        lean_internal_panic("lanes: SHA-256 failed");
    return out;
}

/* OpenSSL clears its own state when it frees it. */
LEAN_EXPORT lean_obj_res lanes_hmac_sha256(b_lean_obj_arg key, b_lean_obj_arg msg) {
    lean_object *out = lanes_bytes(32);
    size_t size = lean_sarray_size(key);
    if (size > INT_MAX || !HMAC(EVP_sha256(), lean_sarray_cptr(key), (int)size,
                                lean_sarray_cptr(msg), lean_sarray_size(msg),
                                lean_sarray_cptr(out), NULL))
        lean_internal_panic("lanes: HMAC-SHA-256 failed");
    return out;
}

LEAN_EXPORT uint8_t lanes_same(b_lean_obj_arg a, b_lean_obj_arg b) {
    size_t size = lean_sarray_size(a);
    return size == lean_sarray_size(b)
        && CRYPTO_memcmp(lean_sarray_cptr(a), lean_sarray_cptr(b), size) == 0;
}

/* OpenSSL's CSPRNG, which seeds itself from the operating system. */
LEAN_EXPORT lean_obj_res lanes_random_bytes(size_t size) {
    if (size > INT_MAX)
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("lanes: too many random bytes")));
    lean_object *out = lanes_bytes(size);
    if (RAND_bytes(lean_sarray_cptr(out), (int)size) != 1) {
        lean_dec(out);
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("lanes: RAND_bytes failed")));
    }
    return lean_io_result_mk_ok(out);
}

static int lanes_push(OSSL_PARAM_BLD *bld, const char *key, b_lean_obj_arg bytes) {
    return OSSL_PARAM_BLD_push_octet_string(bld, key, lean_sarray_cptr(bytes),
                                            lean_sarray_size(bytes));
}

/* A 32-byte Argon2id tag, version 19, in one thread. */
LEAN_EXPORT lean_obj_res lanes_argon2id(b_lean_obj_arg password, b_lean_obj_arg salt,
                                        b_lean_obj_arg secret, b_lean_obj_arg ad,
                                        uint32_t ops, uint32_t mem_kib, uint32_t lanes) {
    lean_object *out = lanes_bytes(32);
    OSSL_PARAM_BLD *bld = OSSL_PARAM_BLD_new();
    OSSL_PARAM *params = NULL;
    if (bld && lanes_push(bld, "pass", password) && lanes_push(bld, "salt", salt)
        && lanes_push(bld, "secret", secret) && lanes_push(bld, "ad", ad)
        && OSSL_PARAM_BLD_push_uint32(bld, "iter", ops)
        && OSSL_PARAM_BLD_push_uint32(bld, "memcost", mem_kib)
        && OSSL_PARAM_BLD_push_uint32(bld, "lanes", lanes))
        params = OSSL_PARAM_BLD_to_param(bld);
    OSSL_PARAM_BLD_free(bld);
    EVP_KDF *kdf = EVP_KDF_fetch(NULL, "ARGON2ID", NULL);
    EVP_KDF_CTX *ctx = kdf ? EVP_KDF_CTX_new(kdf) : NULL;
    EVP_KDF_free(kdf);
    int ok = params && ctx && EVP_KDF_derive(ctx, lean_sarray_cptr(out), 32, params) == 1;
    EVP_KDF_CTX_free(ctx);
    OSSL_PARAM_clear_free(params);
    if (!ok) lean_internal_panic("lanes: Argon2id cannot run");
    return out;
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
