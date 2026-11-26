/*
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

What Lean cannot express or check, bound from C: libsodium for cryptography whose time must not
depend on secrets, and fsync for durability. Each function is declared in
`Lanes/Data/Sodium.lean` or `Lanes/Env/Journal.lean`; arguments are borrowed.
*/
#include <errno.h>
#include <fcntl.h>
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
