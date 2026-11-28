/*
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

A TLS client from OpenSSL, declared in `Lanes/Lib/Net/IO/Tls.lean`. It does no IO: the caller hands
it the bytes that arrived and sends the bytes it gives back, so it sits on any socket. The
server's certificate is always verified, against the certificates of a file the caller names,
and so is the name or address it is for unless the caller asks for the chain only. It gives the
server's certificate, for channel binding, and offers and reports ALPN protocols. Arguments are
borrowed.

The OpenSSL is the one Lean's toolchain ships and links into every executable, which comes
without headers; the functions below are declared as OpenSSL 3 and 4 declare them
(`scripts/tls-declarations.py` checks it), from the part of its API LibreSSL and AWS-LC share.
*/
#include <limits.h>
#include <pthread.h>
#include <stdio.h>
#include <string.h>
#include <lean/lean.h>

typedef struct ssl_st SSL;
typedef struct ssl_ctx_st SSL_CTX;
typedef struct ssl_method_st SSL_METHOD;
typedef struct bio_st BIO;
typedef struct bio_method_st BIO_METHOD;
typedef struct X509_VERIFY_PARAM_st X509_VERIFY_PARAM;
typedef struct x509_store_ctx_st X509_STORE_CTX;
typedef struct x509_st X509;
const SSL_METHOD *TLS_client_method(void);
SSL_CTX *SSL_CTX_new(const SSL_METHOD *method);
void SSL_CTX_free(SSL_CTX *ctx);
long SSL_CTX_ctrl(SSL_CTX *ctx, int cmd, long larg, void *parg);
int SSL_CTX_load_verify_locations(SSL_CTX *ctx, const char *file, const char *dir);
SSL *SSL_new(SSL_CTX *ctx);
void SSL_free(SSL *ssl);
long SSL_ctrl(SSL *ssl, int cmd, long larg, void *parg);
void SSL_set_verify(SSL *ssl, int mode, int (*callback)(int, X509_STORE_CTX *));
int SSL_set1_host(SSL *ssl, const char *name);
X509_VERIFY_PARAM *SSL_get0_param(SSL *ssl);
void X509_VERIFY_PARAM_set_hostflags(X509_VERIFY_PARAM *param, unsigned int flags);
int X509_VERIFY_PARAM_set1_ip_asc(X509_VERIFY_PARAM *param, const char *ip);
const BIO_METHOD *BIO_s_mem(void);
BIO *BIO_new(const BIO_METHOD *method);
int BIO_free(BIO *bio);
int BIO_write(BIO *bio, const void *data, int size);
int BIO_read(BIO *bio, void *data, int size);
size_t BIO_ctrl_pending(BIO *bio);
void SSL_set_bio(SSL *ssl, BIO *in, BIO *out);
BIO *SSL_get_rbio(const SSL *ssl);
BIO *SSL_get_wbio(const SSL *ssl);
void SSL_set_connect_state(SSL *ssl);
int SSL_do_handshake(SSL *ssl);
int SSL_write(SSL *ssl, const void *data, int size);
int SSL_read(SSL *ssl, void *data, int size);
int SSL_get_error(const SSL *ssl, int ret);
int SSL_get_shutdown(const SSL *ssl);
int SSL_shutdown(SSL *ssl);
long SSL_get_verify_result(const SSL *ssl);
const char *X509_verify_cert_error_string(long code);
int SSL_set_alpn_protos(SSL *ssl, const unsigned char *protos, unsigned int size);
void SSL_get0_alpn_selected(const SSL *ssl, const unsigned char **data, unsigned int *size);
X509 *SSL_get1_peer_certificate(const SSL *ssl);
int i2d_X509(const X509 *cert, unsigned char **out);
void X509_free(X509 *cert);
unsigned long ERR_get_error(void);
const char *ERR_reason_error_string(unsigned long code);
void ERR_clear_error(void);
enum {
    SSL_VERIFY_PEER = 1, SSL_ERROR_WANT_READ = 2, SSL_ERROR_ZERO_RETURN = 6,
    SSL_RECEIVED_SHUTDOWN = 2, SSL_CTRL_SET_TLSEXT_HOSTNAME = 55, TLSEXT_NAMETYPE_host_name = 0,
    SSL_CTRL_SET_MIN_PROTO_VERSION = 123, TLS1_2_VERSION = 0x0303, X509_V_OK = 0,
    X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS = 0x4
};

static lean_external_class *lanes_tls_class;
static pthread_once_t lanes_tls_once = PTHREAD_ONCE_INIT;

static void lanes_tls_free(void *ssl) { SSL_free(ssl); }

static void lanes_tls_each(void *ssl, b_lean_obj_arg f) { (void)ssl; (void)f; }

static void lanes_tls_register(void) {
    lanes_tls_class = lean_register_external_class(lanes_tls_free, lanes_tls_each);
}

/* OpenSSL's reason, and why the certificate was refused if it was. */
static lean_obj_res lanes_tls_error(SSL *ssl, const char *what) {
    char text[512];
    const char *reason = ERR_reason_error_string(ERR_get_error());
    long verified = ssl ? SSL_get_verify_result(ssl) : X509_V_OK;
    snprintf(text, sizeof text, "tls: %s: %s%s%s", what, reason ? reason : "failed",
             verified == X509_V_OK ? "" : ": ",
             verified == X509_V_OK ? "" : X509_verify_cert_error_string(verified));
    ERR_clear_error();
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(text)));
}

static lean_obj_res lanes_tls_unit(void) { return lean_io_result_mk_ok(lean_box(0)); }

/* A session with the server `host`, an IP address when `ip`, whose certificate must chain to
   one in the PEM file `trust`, and be for `host` when `check`; offering the ALPN protocols
   `alpn`, in the form TLS sends them, if there are any. */
LEAN_EXPORT lean_obj_res lanes_tls_new(b_lean_obj_arg trust, b_lean_obj_arg host, uint8_t ip,
                                       uint8_t check, b_lean_obj_arg alpn) {
    pthread_once(&lanes_tls_once, lanes_tls_register);
    ERR_clear_error();
    const char *name = lean_string_cstr(host);
    SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
    SSL *ssl = NULL;
    if (ctx && SSL_CTX_ctrl(ctx, SSL_CTRL_SET_MIN_PROTO_VERSION, TLS1_2_VERSION, NULL)
        && SSL_CTX_load_verify_locations(ctx, lean_string_cstr(trust), NULL) == 1)
        ssl = SSL_new(ctx);
    if (ctx) SSL_CTX_free(ctx);
    if (!ssl) return lanes_tls_error(NULL, "trust store");
    SSL_set_verify(ssl, SSL_VERIFY_PEER, NULL);
    X509_VERIFY_PARAM *param = SSL_get0_param(ssl);
    X509_VERIFY_PARAM_set_hostflags(param, X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS);
    int named = ip ? !check || X509_VERIFY_PARAM_set1_ip_asc(param, name)
                   : (!check || SSL_set1_host(ssl, name))
                     && SSL_ctrl(ssl, SSL_CTRL_SET_TLSEXT_HOSTNAME, TLSEXT_NAMETYPE_host_name,
                                 (void *)name);
    size_t protos = lean_sarray_size(alpn);
    if (named && protos != 0)
        named = protos <= UINT_MAX
            && SSL_set_alpn_protos(ssl, lean_sarray_cptr(alpn), (unsigned int)protos) == 0;
    BIO *in = BIO_new(BIO_s_mem()), *out = BIO_new(BIO_s_mem());
    if (!named || !in || !out) {
        if (in) BIO_free(in);
        if (out) BIO_free(out);
        lean_obj_res error = lanes_tls_error(ssl, "server name");
        SSL_free(ssl);
        return error;
    }
    SSL_set_bio(ssl, in, out);
    SSL_set_connect_state(ssl);
    return lean_io_result_mk_ok(lean_alloc_external(lanes_tls_class, ssl));
}

/* Bytes that arrived from the server. */
LEAN_EXPORT lean_obj_res lanes_tls_feed(b_lean_obj_arg tls, b_lean_obj_arg bytes) {
    SSL *ssl = lean_get_external_data(tls);
    size_t size = lean_sarray_size(bytes);
    if (size > INT_MAX || (size != 0
            && BIO_write(SSL_get_rbio(ssl), lean_sarray_cptr(bytes), (int)size) != (int)size))
        return lanes_tls_error(ssl, "feed");
    return lanes_tls_unit();
}

/* Every byte to send to the server, once. */
LEAN_EXPORT lean_obj_res lanes_tls_take(b_lean_obj_arg tls) {
    BIO *out = SSL_get_wbio(lean_get_external_data(tls));
    size_t size = BIO_ctrl_pending(out);
    if (size > INT_MAX) size = INT_MAX;
    lean_object *bytes = lean_alloc_sarray(1, 0, size);
    int got = size == 0 ? 0 : BIO_read(out, lean_sarray_cptr(bytes), (int)size);
    lean_to_sarray(bytes)->m_size = got > 0 ? (size_t)got : 0;
    return lean_io_result_mk_ok(bytes);
}

/* Whether the handshake is done; it is not while it waits for bytes from the server. */
LEAN_EXPORT lean_obj_res lanes_tls_handshake(b_lean_obj_arg tls) {
    SSL *ssl = lean_get_external_data(tls);
    ERR_clear_error();
    int done = SSL_do_handshake(ssl);
    if (done == 1 || SSL_get_error(ssl, done) == SSL_ERROR_WANT_READ)
        return lean_io_result_mk_ok(lean_box(done == 1));
    return lanes_tls_error(ssl, "handshake");
}

/* Bytes to send, encrypted into what `take` gives next. Only after the handshake. */
LEAN_EXPORT lean_obj_res lanes_tls_write(b_lean_obj_arg tls, b_lean_obj_arg bytes) {
    SSL *ssl = lean_get_external_data(tls);
    size_t size = lean_sarray_size(bytes);
    ERR_clear_error();
    if (size > INT_MAX
        || (size != 0 && SSL_write(ssl, lean_sarray_cptr(bytes), (int)size) != (int)size))
        return lanes_tls_error(ssl, "write");
    return lanes_tls_unit();
}

/* At most `max` bytes of what the server sent, decrypted: none while it waits for more bytes
   and once the server has closed. */
LEAN_EXPORT lean_obj_res lanes_tls_read(b_lean_obj_arg tls, uint32_t max) {
    SSL *ssl = lean_get_external_data(tls);
    int room = max > INT_MAX ? INT_MAX : (int)max;
    lean_object *bytes = lean_alloc_sarray(1, 0, (size_t)room);
    ERR_clear_error();
    int got = SSL_read(ssl, lean_sarray_cptr(bytes), room);
    if (got <= 0) {
        int why = SSL_get_error(ssl, got);
        if (why != SSL_ERROR_WANT_READ && why != SSL_ERROR_ZERO_RETURN) {
            lean_dec(bytes);
            return lanes_tls_error(ssl, "read");
        }
    }
    lean_to_sarray(bytes)->m_size = got > 0 ? (size_t)got : 0;
    return lean_io_result_mk_ok(bytes);
}

/* Whether the server has said it closes (`close_notify`): what it sent before is all of it. */
LEAN_EXPORT lean_obj_res lanes_tls_closed(b_lean_obj_arg tls) {
    SSL *ssl = lean_get_external_data(tls);
    return lean_io_result_mk_ok(lean_box((SSL_get_shutdown(ssl) & SSL_RECEIVED_SHUTDOWN) != 0));
}

/* Says this side closes, in what `take` gives next. */
LEAN_EXPORT lean_obj_res lanes_tls_shutdown(b_lean_obj_arg tls) {
    ERR_clear_error();
    SSL_shutdown(lean_get_external_data(tls));
    ERR_clear_error();
    return lanes_tls_unit();
}

/* The server's certificate, as DER: none before the handshake. */
LEAN_EXPORT lean_obj_res lanes_tls_peer(b_lean_obj_arg tls) {
    X509 *cert = SSL_get1_peer_certificate(lean_get_external_data(tls));
    int size = cert ? i2d_X509(cert, NULL) : 0;
    lean_object *bytes = lean_alloc_sarray(1, 0, size > 0 ? (size_t)size : 0);
    unsigned char *out = lean_sarray_cptr(bytes);
    if (size > 0 && i2d_X509(cert, &out) == size) lean_to_sarray(bytes)->m_size = (size_t)size;
    if (cert) X509_free(cert);
    return lean_io_result_mk_ok(bytes);
}

/* The ALPN protocol the server chose: none if it chose none. */
LEAN_EXPORT lean_obj_res lanes_tls_alpn(b_lean_obj_arg tls) {
    const unsigned char *data = NULL;
    unsigned int size = 0;
    SSL_get0_alpn_selected(lean_get_external_data(tls), &data, &size);
    lean_object *bytes = lean_alloc_sarray(1, data ? size : 0, data ? size : 0);
    if (data && size) memcpy(lean_sarray_cptr(bytes), data, size);
    return lean_io_result_mk_ok(bytes);
}
