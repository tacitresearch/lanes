/*
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

A private key and the signatures it makes, from OpenSSL's libcrypto, declared in
`Lanes/Lib/Crypto/Sign.lean`. The key is read from PEM once and kept as OpenSSL's `EVP_PKEY` in
a Lean object, freed when Lean drops it. Lean decides which keys are taken, from the public key
this gives, and what is signed: here nothing is chosen. Signing is a function: RSA signs with
PKCS #1 v1.5, which is deterministic, and ECDSA is told to take its nonce as RFC 6979 says
(OpenSSL 3.2 and later), which Lean asks for under a P-256 key. Arguments are borrowed. Nothing
about the key leaves here but the public key: a failure is `none`, with no reason.

The OpenSSL is the one Lean's toolchain ships, as for `native/verify.c`: the functions below are
declared as OpenSSL 3 and 4 declare them (`scripts/tls-declarations.py` checks it).
*/
#include <limits.h>
#include <pthread.h>
#include <stddef.h>
#include <lean/lean.h>

typedef struct bio_st BIO;
typedef struct evp_pkey_st EVP_PKEY;
typedef struct evp_pkey_ctx_st EVP_PKEY_CTX;
typedef struct evp_md_st EVP_MD;
typedef struct evp_md_ctx_st EVP_MD_CTX;
typedef struct engine_st ENGINE;
typedef int pem_password_cb(char *buf, int size, int rwflag, void *userdata);
BIO *BIO_new_mem_buf(const void *buf, int len);
int BIO_free(BIO *a);
EVP_PKEY *PEM_read_bio_PrivateKey(BIO *bp, EVP_PKEY **x, pem_password_cb *cb, void *u);
void EVP_PKEY_free(EVP_PKEY *pkey);
int i2d_PUBKEY(const EVP_PKEY *a, unsigned char **pp);
EVP_MD_CTX *EVP_MD_CTX_new(void);
void EVP_MD_CTX_free(EVP_MD_CTX *ctx);
const EVP_MD *EVP_sha1(void);
const EVP_MD *EVP_sha256(void);
int EVP_DigestSignInit(EVP_MD_CTX *ctx, EVP_PKEY_CTX **pctx, const EVP_MD *type, ENGINE *e,
                       EVP_PKEY *pkey);
int EVP_DigestSign(EVP_MD_CTX *ctx, unsigned char *sigret, size_t *siglen,
                   const unsigned char *tbs, size_t tbslen);
int EVP_PKEY_CTX_ctrl_str(EVP_PKEY_CTX *ctx, const char *type, const char *value);
void ERR_clear_error(void);

static lean_external_class *lanes_key_class;
static pthread_once_t lanes_key_once = PTHREAD_ONCE_INIT;

static void lanes_key_free(void *key) { EVP_PKEY_free(key); }

static void lanes_key_each(void *key, b_lean_obj_arg f) { (void)key; (void)f; }

static void lanes_key_register(void) {
    lanes_key_class = lean_register_external_class(lanes_key_free, lanes_key_each);
}

static lean_obj_res lanes_some(lean_obj_arg x) {
    lean_object *r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, x);
    return r;
}

/* An encrypted key is refused rather than asked a password for on the terminal. */
static int lanes_no_password(char *buf, int size, int rwflag, void *u) {
    (void)buf; (void)size; (void)rwflag; (void)u;
    return -1;
}

/* The first private key of `pem`, PKCS #8 or the traditional forms, if it is not encrypted. */
LEAN_EXPORT lean_obj_res lanes_private_key_read(b_lean_obj_arg pem) {
    size_t size = lean_sarray_size(pem);
    BIO *bio = size <= INT_MAX ? BIO_new_mem_buf(lean_sarray_cptr(pem), (int)size) : NULL;
    EVP_PKEY *key = bio ? PEM_read_bio_PrivateKey(bio, NULL, lanes_no_password, NULL) : NULL;
    BIO_free(bio);
    ERR_clear_error();
    if (!key) return lean_box(0);
    pthread_once(&lanes_key_once, lanes_key_register);
    return lanes_some(lean_alloc_external(lanes_key_class, key));
}

/* The DER SubjectPublicKeyInfo of the key's public half. */
LEAN_EXPORT lean_obj_res lanes_private_key_spki(b_lean_obj_arg key) {
    EVP_PKEY *pkey = lean_get_external_data(key);
    int size = i2d_PUBKEY(pkey, NULL);
    lean_object *der = lean_alloc_sarray(1, 0, size > 0 ? (size_t)size : 0);
    unsigned char *at = lean_sarray_cptr(der);
    if (size > 0 && i2d_PUBKEY(pkey, &at) == size) lean_sarray_set_size(der, (size_t)size);
    ERR_clear_error();
    return der;
}

/* The signature of `msg` with SHA-256, or SHA-1 if `sha256` is false; an ECDSA signature is DER
   and, if `rfc6979`, takes its nonce from the key and the message. */
LEAN_EXPORT lean_obj_res lanes_private_key_sign(b_lean_obj_arg key, uint8_t sha256,
                                                uint8_t rfc6979, b_lean_obj_arg msg) {
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    EVP_PKEY_CTX *pctx = NULL;
    size_t size = 0;
    lean_object *sig = NULL;
    if (ctx && EVP_DigestSignInit(ctx, &pctx, sha256 ? EVP_sha256() : EVP_sha1(), NULL,
                                  lean_get_external_data(key)) == 1
        && (!rfc6979 || EVP_PKEY_CTX_ctrl_str(pctx, "nonce-type", "1") > 0)
        && EVP_DigestSign(ctx, NULL, &size, lean_sarray_cptr(msg), lean_sarray_size(msg)) == 1) {
        sig = lean_alloc_sarray(1, 0, size);
        if (EVP_DigestSign(ctx, lean_sarray_cptr(sig), &size, lean_sarray_cptr(msg),
                           lean_sarray_size(msg)) == 1) {
            lean_sarray_set_size(sig, size);
        } else {
            lean_dec(sig);
            sig = NULL;
        }
    }
    EVP_MD_CTX_free(ctx);
    ERR_clear_error();
    return sig ? lanes_some(sig) : lean_box(0);
}
