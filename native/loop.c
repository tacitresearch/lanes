/*
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The server's connections on threads of C, each with its own epoll and its own listening socket
on one port (SO_REUSEPORT), declared in `Lanes/Web/IO/CLoop.lean`. It moves bytes and keeps
time and decides nothing about HTTP: what happens to a connection is handed to Lean's `turn`,
and the loop does what the `Turn` it returns says. Linux only; elsewhere `new` refuses.

Lean's objects: a thread owns the `Line` of each of its connections and its own `Handler`, both
used only by it; the handlers are marked thread-shared before the threads start, since what they
hold is shared. Answers come back through the handler's mailbox, a Lean mutex, and an eventfd.
*/
#define _GNU_SOURCE
#include <errno.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <lean/lean.h>

static lean_obj_res lanes_cloop_error(const char *what) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(what)));
}

#ifdef __linux__
#include <arpa/inet.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <pthread.h>
#include <sys/epoll.h>
#include <sys/eventfd.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);
extern lean_object *lanes_cloop_open(lean_object *h, uint32_t peer, uint64_t now);
extern lean_object *lanes_cloop_turn(lean_object *h, uint64_t token, lean_object *line,
                                     uint8_t kind, lean_object *bytes, uint64_t now);
extern lean_object *lanes_cloop_answer(lean_object *h, lean_object *line, lean_object *mail,
                                       uint64_t now);
extern lean_object *lanes_cloop_take(lean_object *h);

enum { RECEIVED, ENDED, BROKEN, TICK, STOP, SENT };
#define READ_MAX 65536
#define EVENTS_MAX 128
#define ACCEPTS_MAX 64
#define THREADS_MAX 1024
#define CONNS_MAX (1u << 20)
#define TOKEN_LISTEN UINT64_MAX
#define TOKEN_WAKE (UINT64_MAX - 1)

typedef struct {
    int fd;              /* -1: the slot is free */
    uint32_t gen;        /* changed when the slot is freed, so that a stale token finds nothing */
    lean_object *line;   /* NULL once Lean has closed the connection */
    lean_object *out;    /* bytes not yet written, from `sent` on, or NULL */
    size_t sent;
    uint64_t out_ms;     /* when `out` was given */
    uint64_t want;       /* bytes to read at most; 0: do not read */
    uint64_t deadline_ms; /* 0: none; once closed, when to close the socket */
    int readable, shut;
    int notify;          /* tell Lean `sent` once nothing is unwritten */
} conn_t;

typedef struct loop loop_t;

typedef struct {
    loop_t *loop;
    pthread_t thread;
    int started, epoll, listen, wake, paused;
    lean_object *handler;
    conn_t *conns;       /* conns_max of them */
    uint32_t *free_slots, free_count;
    uint8_t buf[READ_MAX];
} worker_t;

struct loop {
    uint32_t threads, conns_max;
    uint64_t write_ms, linger_ms, tick_ms;
    uint16_t port;
    int stopping;        /* read and written atomically */
    int running, joined;
    pthread_mutex_t join_lock;
    worker_t *workers;
};

static uint64_t now_ms(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)t.tv_sec * 1000 + (uint64_t)t.tv_nsec / 1000000;
}

static uint64_t token_of(worker_t *w, conn_t *c) {
    return ((uint64_t)c->gen << 32) | (uint64_t)(c - w->conns);
}

static conn_t *find(worker_t *w, uint64_t token) {
    uint64_t i = token & 0xffffffffu;
    if (i >= w->loop->conns_max) return NULL;
    conn_t *c = &w->conns[i];
    return c->fd >= 0 && c->gen == (uint32_t)(token >> 32) ? c : NULL;
}

static void release(worker_t *w, conn_t *c) {
    close(c->fd);
    if (c->line) lean_dec_ref(c->line);
    if (c->out) lean_dec_ref(c->out);
    c->fd = -1;
    c->line = c->out = NULL;
    c->gen++;
    w->free_slots[w->free_count++] = (uint32_t)(c - w->conns);
}

/* Do what a turn says: keep its line, queue its bytes after those not yet written, keep what
   to read and when to look again; once closed, drop the line and keep only the socket. */
static void apply(worker_t *w, conn_t *c, lean_object *t, uint64_t now) {
    lean_object *line = lean_ctor_get(t, 0), *out = lean_ctor_get(t, 1);
    c->want = lean_ctor_get_uint64(t, sizeof(void *) * 2);
    c->deadline_ms = lean_ctor_get_uint64(t, sizeof(void *) * 2 + 8);
    uint64_t closed = lean_ctor_get_uint64(t, sizeof(void *) * 2 + 16);
    c->notify = lean_ctor_get_uint64(t, sizeof(void *) * 2 + 24) != 0;
    lean_inc(line);
    lean_inc(out);
    lean_dec_ref(t);
    c->line = line;
    size_t n = lean_sarray_size(out);
    if (n == 0) {
        lean_dec_ref(out);
    } else if (!c->out) {
        c->out = out;
        c->sent = 0;
        c->out_ms = now;
    } else {
        size_t left = lean_sarray_size(c->out) - c->sent;
        lean_object *both = lean_alloc_sarray(1, left + n, left + n);
        memcpy(lean_sarray_cptr(both), lean_sarray_cptr(c->out) + c->sent, left);
        memcpy(lean_sarray_cptr(both) + left, lean_sarray_cptr(out), n);
        lean_dec_ref(c->out);
        lean_dec_ref(out);
        c->out = both;
        c->sent = 0;
    }
    if (closed) {
        lean_dec_ref(c->line);
        c->line = NULL;
        c->want = 0;
        c->deadline_ms = now + w->loop->write_ms;
    }
}

/* Tell Lean what happened to an open connection, which `c->line` is. */
static void event(worker_t *w, conn_t *c, uint8_t kind, lean_object *bytes, uint64_t now) {
    lean_object *line = c->line;
    c->line = NULL;
    lean_inc(w->handler);
    apply(w, c, lanes_cloop_turn(w->handler, token_of(w, c), line, kind, bytes, now), now);
}

/* Write what is queued: 0 when all of it is, 1 when the socket has no room, -1 on an error. */
static int flush(conn_t *c) {
    while (c->out) {
        size_t size = lean_sarray_size(c->out);
        ssize_t n = send(c->fd, lean_sarray_cptr(c->out) + c->sent, size - c->sent, MSG_NOSIGNAL);
        if (n < 0) {
            if (errno == EINTR) continue;
            return errno == EAGAIN || errno == EWOULDBLOCK ? 1 : -1;
        }
        c->sent += (size_t)n;
        if (c->sent == size) {
            lean_dec_ref(c->out);
            c->out = NULL;
        }
    }
    return 0;
}

/* Write, read while Lean wants bytes and nothing is left to write, and once Lean has closed the
   connection, shut it down and read and drop what still comes until the end or the deadline. */
static void drive(worker_t *w, conn_t *c, uint64_t now) {
    for (;;) {
        int f = flush(c);
        if (f < 0) {
            if (!c->line) { release(w, c); return; }
            event(w, c, BROKEN, lean_alloc_sarray(1, 0, 0), now);
            continue;
        }
        if (!c->line) {
            if (f) return;
            if (!c->shut) {
                shutdown(c->fd, SHUT_WR);
                c->shut = 1;
                c->deadline_ms = now + w->loop->linger_ms;
            }
            while (c->readable) {
                ssize_t n = recv(c->fd, w->buf, READ_MAX, 0);
                if (n > 0 || (n < 0 && errno == EINTR)) continue;
                if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) { c->readable = 0; return; }
                release(w, c);
                return;
            }
            return;
        }
        if (!f && c->notify) {
            c->notify = 0;
            event(w, c, SENT, lean_alloc_sarray(1, 0, 0), now);
            continue;
        }
        if (f || !c->readable || c->want == 0) return;
        size_t size = c->want < READ_MAX ? (size_t)c->want : READ_MAX;
        ssize_t n = recv(c->fd, w->buf, size, 0);
        if (n > 0) {
            lean_object *bytes = lean_alloc_sarray(1, (size_t)n, (size_t)n);
            memcpy(lean_sarray_cptr(bytes), w->buf, (size_t)n);
            /* A short read took all there was; more makes a new edge. */
            if ((size_t)n < size) c->readable = 0;
            event(w, c, RECEIVED, bytes, now);
        } else if (n == 0) {
            event(w, c, ENDED, lean_alloc_sarray(1, 0, 0), now);
        } else if (errno == EAGAIN || errno == EWOULDBLOCK) {
            c->readable = 0;
        } else if (errno != EINTR) {
            event(w, c, BROKEN, lean_alloc_sarray(1, 0, 0), now);
        }
    }
}

static void accept_some(worker_t *w, uint64_t now) {
    for (int k = 0; k < ACCEPTS_MAX; k++) {
        struct sockaddr_in a;
        socklen_t len = sizeof a;
        int fd = accept4(w->listen, (struct sockaddr *)&a, &len, SOCK_NONBLOCK | SOCK_CLOEXEC);
        if (fd < 0) {
            /* Out of descriptors or memory: stop listening until the next sweep, not spin. */
            if (errno == EMFILE || errno == ENFILE || errno == ENOBUFS || errno == ENOMEM) {
                epoll_ctl(w->epoll, EPOLL_CTL_DEL, w->listen, NULL);
                w->paused = 1;
            }
            return;
        }
        int one = 1;
        setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
        if (w->free_count == 0) { close(fd); continue; }
        lean_inc(w->handler);
        lean_object *r = lanes_cloop_open(w->handler, ntohl(a.sin_addr.s_addr), now);
        if (lean_is_scalar(r)) { close(fd); continue; }
        lean_object *t = lean_ctor_get(r, 0);
        lean_inc(t);
        lean_dec_ref(r);
        conn_t *c = &w->conns[w->free_slots[--w->free_count]];
        c->fd = fd;
        c->readable = 1;
        c->shut = 0;
        apply(w, c, t, now);
        struct epoll_event e = { .events = EPOLLIN | EPOLLOUT | EPOLLRDHUP | EPOLLET,
                                 .data.u64 = token_of(w, c) };
        if (epoll_ctl(w->epoll, EPOLL_CTL_ADD, fd, &e) < 0 && c->line)
            event(w, c, BROKEN, lean_alloc_sarray(1, 0, 0), now);
        drive(w, c, now);
    }
}

/* The answers in the mailbox, each to its connection if it is still open. The eventfd is read
   before the mailbox is taken, so a letter posted after the take writes it again. */
static void take_mail(worker_t *w, uint64_t now) {
    uint64_t n;
    if (read(w->wake, &n, sizeof n) < 0 && errno != EAGAIN) lean_internal_panic("lanes: eventfd");
    lean_inc(w->handler);
    lean_object *box = lanes_cloop_take(w->handler);
    size_t size = lean_array_size(box);
    for (size_t i = 0; i < size; i++) {
        lean_object *m = lean_array_get_core(box, i);
        conn_t *c = find(w, lean_ctor_get_uint64(m, sizeof(void *)));
        if (!c || !c->line) continue;
        lean_object *line = c->line;
        c->line = NULL;
        lean_inc(m);
        lean_inc(w->handler);
        apply(w, c, lanes_cloop_answer(w->handler, line, m, now), now);
        drive(w, c, now);
    }
    lean_dec_ref(box);
}

/* Deadlines, every tick_ms: a write not done in write_ms is a broken socket, a deadline of
   Lean's that has passed a tick, and a closed connection past its own is closed. */
static void sweep(worker_t *w, uint64_t now) {
    loop_t *l = w->loop;
    if (w->paused && w->listen >= 0) {
        struct epoll_event e = { .events = EPOLLIN, .data.u64 = TOKEN_LISTEN };
        if (epoll_ctl(w->epoll, EPOLL_CTL_ADD, w->listen, &e) == 0) w->paused = 0;
    }
    for (uint32_t i = 0; i < l->conns_max; i++) {
        conn_t *c = &w->conns[i];
        if (c->fd < 0) continue;
        if (!c->line) {
            if (c->deadline_ms <= now) release(w, c);
            continue;
        }
        if (c->out && c->out_ms + l->write_ms <= now)
            event(w, c, BROKEN, lean_alloc_sarray(1, 0, 0), now);
        else if (c->deadline_ms && c->deadline_ms <= now)
            event(w, c, TICK, lean_alloc_sarray(1, 0, 0), now);
        else
            continue;
        drive(w, c, now);
    }
}

static void stop_all(worker_t *w, uint64_t now) {
    if (w->listen >= 0) close(w->listen);
    w->listen = -1;
    for (uint32_t i = 0; i < w->loop->conns_max; i++) {
        conn_t *c = &w->conns[i];
        if (c->fd < 0 || !c->line) continue;
        event(w, c, STOP, lean_alloc_sarray(1, 0, 0), now);
        drive(w, c, now);
    }
}

static void *work(void *arg) {
    worker_t *w = arg;
    loop_t *l = w->loop;
    lean_initialize_thread();
    struct epoll_event events[EVENTS_MAX];
    uint64_t swept = now_ms();
    int stopped = 0;
    for (;;) {
        int n = epoll_wait(w->epoll, events, EVENTS_MAX, (int)l->tick_ms);
        if (n < 0 && errno != EINTR) lean_internal_panic("lanes: epoll_wait");
        uint64_t now = now_ms();
        for (int k = 0; k < n; k++) {
            uint64_t token = events[k].data.u64;
            if (token == TOKEN_LISTEN) { if (w->listen >= 0) accept_some(w, now); continue; }
            if (token == TOKEN_WAKE) { take_mail(w, now); continue; }
            conn_t *c = find(w, token);
            if (!c) continue;
            if (events[k].events & (EPOLLIN | EPOLLRDHUP | EPOLLHUP | EPOLLERR)) c->readable = 1;
            drive(w, c, now);
        }
        if (!stopped && __atomic_load_n(&l->stopping, __ATOMIC_ACQUIRE)) {
            stop_all(w, now);
            stopped = 1;
        }
        if (now - swept >= l->tick_ms) {
            sweep(w, now);
            swept = now;
        }
        if (stopped && w->free_count == l->conns_max) break;
    }
    lean_finalize_thread();
    return NULL;
}

static void destroy(loop_t *l) {
    for (uint32_t i = 0; i < l->threads; i++) {
        worker_t *w = &l->workers[i];
        for (uint32_t j = 0; w->conns && j < l->conns_max; j++)
            if (w->conns[j].fd >= 0) release(w, &w->conns[j]);
        if (w->listen >= 0) close(w->listen);
        if (w->epoll >= 0) close(w->epoll);
        if (w->wake >= 0) close(w->wake);
        free(w->conns);
        free(w->free_slots);
    }
    pthread_mutex_destroy(&l->join_lock);
    free(l->workers);
    free(l);
}

static void loop_free(void *p) { destroy(p); }
static void loop_each(void *p, b_lean_obj_arg f) { (void)p; (void)f; }
static lean_external_class *loop_class;
static pthread_once_t loop_once = PTHREAD_ONCE_INIT;
static void loop_register(void) { loop_class = lean_register_external_class(loop_free, loop_each); }

static int open_worker(loop_t *l, worker_t *w, struct sockaddr_in *a) {
    int one = 1;
    w->listen = socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0);
    if (w->listen < 0
        || setsockopt(w->listen, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one) < 0
        || setsockopt(w->listen, SOL_SOCKET, SO_REUSEPORT, &one, sizeof one) < 0
        || bind(w->listen, (struct sockaddr *)a, sizeof *a) < 0)
        return errno;
    socklen_t len = sizeof *a;
    if (a->sin_port == 0 && getsockname(w->listen, (struct sockaddr *)a, &len) < 0) return errno;
    if (listen(w->listen, 1024) < 0) return errno;
    w->epoll = epoll_create1(EPOLL_CLOEXEC);
    w->wake = eventfd(0, EFD_NONBLOCK | EFD_CLOEXEC);
    if (w->epoll < 0 || w->wake < 0) return errno;
    struct epoll_event e = { .events = EPOLLIN, .data.u64 = TOKEN_LISTEN };
    if (epoll_ctl(w->epoll, EPOLL_CTL_ADD, w->listen, &e) < 0) return errno;
    e.data.u64 = TOKEN_WAKE;
    if (epoll_ctl(w->epoll, EPOLL_CTL_ADD, w->wake, &e) < 0) return errno;
    w->conns = calloc(l->conns_max, sizeof *w->conns);
    w->free_slots = calloc(l->conns_max, sizeof *w->free_slots);
    if (!w->conns || !w->free_slots) return ENOMEM;
    for (uint32_t j = 0; j < l->conns_max; j++) {
        w->conns[j].fd = -1;
        w->free_slots[j] = l->conns_max - 1 - j;
    }
    w->free_count = l->conns_max;
    return 0;
}

LEAN_EXPORT lean_obj_res lanes_cloop_new(b_lean_obj_arg host, uint16_t port, uint32_t threads,
                                         uint32_t conns_max, uint64_t write_ms,
                                         uint64_t linger_ms, uint64_t tick_ms) {
    if (threads == 0 || threads > THREADS_MAX || conns_max == 0 || conns_max > CONNS_MAX
        || tick_ms == 0 || tick_ms > 60000)
        return lanes_cloop_error("lanes: the C loop takes 1 to 1024 threads, 1 to 2^20 "
                                 "connections and a tick of 1 to 60000 ms");
    struct sockaddr_in a = { .sin_family = AF_INET, .sin_port = htons(port) };
    if (inet_pton(AF_INET, lean_string_cstr(host), &a.sin_addr) != 1)
        return lanes_cloop_error("lanes: the C loop binds an IPv4 address only");
    pthread_once(&loop_once, loop_register);
    loop_t *l = calloc(1, sizeof *l);
    worker_t *ws = l ? calloc(threads, sizeof *ws) : NULL;
    if (!ws) { free(l); lean_internal_panic_out_of_memory(); }
    *l = (loop_t){ .threads = threads, .conns_max = conns_max, .write_ms = write_ms,
                   .linger_ms = linger_ms, .tick_ms = tick_ms, .workers = ws };
    pthread_mutex_init(&l->join_lock, NULL);
    for (uint32_t i = 0; i < threads; i++)
        ws[i] = (worker_t){ .loop = l, .epoll = -1, .listen = -1, .wake = -1 };
    for (uint32_t i = 0; i < threads; i++) {
        int err = open_worker(l, &ws[i], &a);
        if (err) {
            destroy(l);
            return lean_io_result_mk_error(lean_decode_io_error(err, NULL));
        }
    }
    l->port = ntohs(a.sin_port);
    return lean_io_result_mk_ok(lean_alloc_external(loop_class, l));
}

LEAN_EXPORT uint16_t lanes_cloop_port(b_lean_obj_arg h) {
    return ((loop_t *)lean_get_external_data(h))->port;
}

LEAN_EXPORT lean_obj_res lanes_cloop_wake(b_lean_obj_arg h, uint32_t thread) {
    loop_t *l = lean_get_external_data(h);
    uint64_t one = 1;
    /* It fails only when the count is full, and then the thread is woken already. */
    if (thread < l->threads && write(l->workers[thread].wake, &one, sizeof one) < 0) {}
    return lean_box(0);
}

LEAN_EXPORT lean_obj_res lanes_cloop_stop(b_lean_obj_arg h) {
    loop_t *l = lean_get_external_data(h);
    __atomic_store_n(&l->stopping, 1, __ATOMIC_RELEASE);
    for (uint32_t i = 0; i < l->threads; i++) lanes_cloop_wake(h, i);
    return lean_box(0);
}

LEAN_EXPORT lean_obj_res lanes_cloop_join(b_lean_obj_arg h) {
    loop_t *l = lean_get_external_data(h);
    pthread_mutex_lock(&l->join_lock);
    for (uint32_t i = 0; !l->joined && i < l->threads; i++) {
        worker_t *w = &l->workers[i];
        if (w->started) pthread_join(w->thread, NULL);
        if (w->handler) lean_dec_ref(w->handler);
        w->handler = NULL;
    }
    l->joined = 1;
    pthread_mutex_unlock(&l->join_lock);
    return lean_box(0);
}

LEAN_EXPORT lean_obj_res lanes_cloop_run(b_lean_obj_arg h, lean_obj_arg handlers) {
    loop_t *l = lean_get_external_data(h);
    if (l->running || lean_array_size(handlers) != l->threads) {
        lean_dec_ref(handlers);
        return lanes_cloop_error("lanes: the C loop is started once, with a handler a thread");
    }
    l->running = 1;
    lean_mark_mt(handlers);
    for (uint32_t i = 0; i < l->threads; i++) {
        l->workers[i].handler = lean_array_get_core(handlers, i);
        lean_inc(l->workers[i].handler);
    }
    lean_dec_ref(handlers);
    for (uint32_t i = 0; i < l->threads; i++) {
        worker_t *w = &l->workers[i];
        if (pthread_create(&w->thread, NULL, work, w) != 0) {
            lanes_cloop_stop(h);
            lanes_cloop_join(h);
            return lanes_cloop_error("lanes: the C loop cannot start its threads");
        }
        w->started = 1;
    }
    return lean_io_result_mk_ok(lean_box(0));
}

#else

LEAN_EXPORT lean_obj_res lanes_cloop_new(b_lean_obj_arg host, uint16_t port, uint32_t threads,
                                         uint32_t conns_max, uint64_t write_ms,
                                         uint64_t linger_ms, uint64_t tick_ms) {
    return lanes_cloop_error("lanes: the C loop (ServerConfig.loop := .c) runs on Linux only");
}

LEAN_EXPORT uint16_t lanes_cloop_port(b_lean_obj_arg h) { return 0; }
LEAN_EXPORT lean_obj_res lanes_cloop_wake(b_lean_obj_arg h, uint32_t t) { return lean_box(0); }
LEAN_EXPORT lean_obj_res lanes_cloop_stop(b_lean_obj_arg h) { return lean_box(0); }
LEAN_EXPORT lean_obj_res lanes_cloop_join(b_lean_obj_arg h) { return lean_box(0); }

LEAN_EXPORT lean_obj_res lanes_cloop_run(b_lean_obj_arg h, lean_obj_arg handlers) {
    lean_dec_ref(handlers);
    return lanes_cloop_error("lanes: the C loop runs on Linux only");
}

#endif
