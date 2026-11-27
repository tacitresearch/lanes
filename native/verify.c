/*
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

A signature checked with SHA-256 under a public key, from OpenSSL's libcrypto, declared in
`Lanes/Lib/Crypto/Verify.lean`. The key is a DER SubjectPublicKeyInfo and an ECDSA signature
is DER, both written in Lean (`Lanes/Lib/Crypto/PublicKey.lean`), which also decides which key
may check which signature: here nothing is chosen. Arguments are borrowed; nothing is kept.

The OpenSSL is the one Lean's toolchain ships, as for `native/tls.c`: the functions below are
declared as OpenSSL 3 and 4 declare them (`scripts/tls-declarations.py` checks it).
*/
#include <limits.h>
#include <stddef.h>
#include <lean/lean.h>

typedef struct evp_pkey_st EVP_PKEY;
typedef struct evp_pkey_ctx_st EVP_PKEY_CTX;
typedef struct evp_md_st EVP_MD;
typedef struct evp_md_ctx_st EVP_MD_CTX;
typedef struct engine_st ENGINE;
EVP_PKEY *d2i_PUBKEY(EVP_PKEY **a, const unsigned char **pp, long length);
void EVP_PKEY_free(EVP_PKEY *pkey);
EVP_MD_CTX *EVP_MD_CTX_new(void);
void EVP_MD_CTX_free(EVP_MD_CTX *ctx);
const EVP_MD *EVP_sha256(void);
int EVP_DigestVerifyInit(EVP_MD_CTX *ctx, EVP_PKEY_CTX **pctx, const EVP_MD *type, ENGINE *e,
                         EVP_PKEY *pkey);
int EVP_DigestVerify(EVP_MD_CTX *ctx, const unsigned char *sigret, size_t siglen,
                     const unsigned char *tbs, size_t tbslen);
void ERR_clear_error(void);

/* Whether `sig` signs `msg` under the key `spki`, which must be read whole. RSA verifies with
   PKCS #1 v1.5 padding, OpenSSL's default for it. */
LEAN_EXPORT uint8_t lanes_verify_sha256(b_lean_obj_arg spki, b_lean_obj_arg msg,
                                        b_lean_obj_arg sig) {
    const unsigned char *start = lean_sarray_cptr(spki), *end = start;
    size_t size = lean_sarray_size(spki);
    EVP_PKEY *key = size <= LONG_MAX ? d2i_PUBKEY(NULL, &end, (long)size) : NULL;
    int ok = 0;
    if (key && end == start + size) {
        EVP_MD_CTX *ctx = EVP_MD_CTX_new();
        ok = ctx && EVP_DigestVerifyInit(ctx, NULL, EVP_sha256(), NULL, key) == 1
             && EVP_DigestVerify(ctx, lean_sarray_cptr(sig), lean_sarray_size(sig),
                                 lean_sarray_cptr(msg), lean_sarray_size(msg)) == 1;
        EVP_MD_CTX_free(ctx);
    }
    EVP_PKEY_free(key);
    ERR_clear_error();
    return ok;
}
