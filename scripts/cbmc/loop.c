/* A thread of `native/loop.c` under CBMC (`scripts/cbmc.sh`), on a table of two connections.
   Lean's side, the sockets, epoll and the clock are stubs that may do anything their contracts
   allow: events with any token, reads and writes of any length or failing, turns that close or
   not and ask for any number of bytes, answers for any token. CBMC checks every path of a few
   turns of the loop for: reads and copies within the buffer and within what Lean asked for; no
   system call on a socket that is not open, none closed twice, no empty write; no turn of Lean
   without a line, nor on a closed connection; no Lean object dropped more often than it is
   held, nor used once freed; no panic; and once the thread ends, every object it held dropped
   and every socket closed. */
#define READ_MAX 16 /* the buffer, 64 KiB in the loop, small enough to check */
#include "../../native/loop.c"

size_t model_live;

#define FDS 12
#define OPEN_WANT 5
static int fd_open[FDS];
static int next_fd = 5;
static uint64_t clock_ms = 1000;
static loop_t the_loop;
static worker_t the_worker;
static lean_object *the_handler;

int nondet_int(void);
unsigned nondet_unsigned(void);
uint64_t nondet_u64(void);
uint8_t nondet_u8(void);
size_t nondet_size(void);

static void check_open(int fd) { assert(fd >= 0 && fd < FDS && fd_open[fd]); }

static lean_object *turn_for(lean_object *line, int fixed_want) {
    lean_object *t = model_new(0, 2);
    size_t n = nondet_size();
    __CPROVER_assume(n <= 3);
    t->fields[0] = line;
    t->fields[1] = model_new(1, n);
    uint64_t want = fixed_want ? OPEN_WANT : nondet_u64();
    t->scalars[0] = want;
    t->scalars[1] = nondet_u64();
    __CPROVER_assume(t->scalars[1] < 100000);
    t->scalars[2] = nondet_u8() & 1;
    t->scalars[3] = nondet_u8() & 1;
    return t;
}

lean_object *lanes_cloop_open(lean_object *h, uint32_t peer, uint64_t now) {
    (void)peer; (void)now;
    assert(h == the_handler);
    lean_dec_ref(h);
    if (nondet_u8() & 1) return lean_box(0);
    lean_object *some = model_new(0, 1);
    some->fields[0] = turn_for(model_new(3, 0), 1);
    return some;
}

lean_object *lanes_cloop_turn(lean_object *h, uint64_t token, lean_object *line, uint8_t kind,
                              lean_object *bytes, uint64_t now) {
    (void)now;
    assert(h == the_handler && line != NULL && kind <= 5);
    assert((token & 0xffffffffu) < 2);
    size_t read = lean_sarray_size(bytes);
    assert(kind != 0 || (read > 0 && read <= the_worker.conns[token & 1].want));
    lean_dec_ref(h);
    lean_dec_ref(bytes);
    return turn_for(line, 0);
}

lean_object *lanes_cloop_answer(lean_object *h, lean_object *line, lean_object *m, uint64_t now) {
    (void)now;
    assert(h == the_handler && line != NULL);
    lean_dec_ref(h);
    lean_dec_ref(m);
    return turn_for(line, 0);
}

lean_object *lanes_cloop_take(lean_object *h) {
    assert(h == the_handler);
    lean_dec_ref(h);
    size_t n = nondet_size();
    __CPROVER_assume(n <= 2);
    lean_object *box = model_new(2, n);
    for (size_t i = 0; i < n; i++) {
        box->fields[i] = model_new(0, 1);
        box->fields[i]->fields[0] = lean_box(0);
        box->fields[i]->scalars[0] = nondet_u64();
    }
    return box;
}

void lean_initialize_thread(void) {}
void lean_finalize_thread(void) {}

int clock_gettime(clockid_t id, struct timespec *t) {
    (void)id;
    unsigned step = nondet_unsigned();
    __CPROVER_assume(step <= 50000);
    clock_ms += step;
    t->tv_sec = (time_t)(clock_ms / 1000);
    t->tv_nsec = (long)(clock_ms % 1000) * 1000000;
    return 0;
}

int epoll_wait(int epfd, struct epoll_event *events, int max, int timeout) {
    (void)timeout;
    check_open(epfd);
    if (nondet_u8() & 1) __atomic_store_n(&the_loop.stopping, 1, __ATOMIC_RELEASE);
    int n = nondet_int();
    __CPROVER_assume(n >= 0 && n <= 2 && n <= max);
    for (int k = 0; k < n; k++) {
        uint8_t which = nondet_u8();
        events[k].events = nondet_unsigned();
        events[k].data.u64 = which == 0 ? TOKEN_LISTEN : which == 1 ? TOKEN_WAKE : nondet_u64();
    }
    return n;
}

int epoll_ctl(int epfd, int op, int fd, struct epoll_event *e) {
    (void)e;
    check_open(epfd);
    check_open(fd);
    (void)op;
    return nondet_u8() & 1 ? 0 : -1;
}

int accept4(int fd, struct sockaddr *a, socklen_t *len, int flags) {
    (void)flags;
    check_open(fd);
    assert(*len >= sizeof(struct sockaddr_in));
    if (next_fd >= FDS || (nondet_u8() & 1)) {
        int e = nondet_int();
        __CPROVER_assume(e == EAGAIN || e == EMFILE || e == ECONNABORTED);
        errno = e;
        return -1;
    }
    ((struct sockaddr_in *)a)->sin_addr.s_addr = nondet_unsigned();
    fd_open[next_fd] = 1;
    return next_fd++;
}

int setsockopt(int fd, int level, int name, const void *v, socklen_t len) {
    (void)level; (void)name; (void)v; (void)len;
    check_open(fd);
    return 0;
}

int shutdown(int fd, int how) {
    (void)how;
    check_open(fd);
    return 0;
}

int close(int fd) {
    assert(fd >= 0 && fd < FDS && fd_open[fd] && "a socket closed twice or never opened");
    fd_open[fd] = 0;
    return 0;
}

static ssize_t some_bytes(size_t len) {
    ssize_t n = (ssize_t)nondet_size();
    __CPROVER_assume(n >= -1 && n <= (ssize_t)len);
    if (n < 0) {
        int e = nondet_int();
        __CPROVER_assume(e == EAGAIN || e == EINTR || e == ECONNRESET || e == EPIPE);
        errno = e;
    }
    return n;
}

ssize_t send(int fd, const void *buf, size_t len, int flags) {
    (void)buf; (void)flags;
    check_open(fd);
    assert(len > 0);
    return some_bytes(len);
}

ssize_t recv(int fd, void *buf, size_t len, int flags) {
    (void)flags;
    check_open(fd);
    assert(len > 0 && len <= READ_MAX);
    ssize_t n = some_bytes(len);
    if (n > 0) __CPROVER_havoc_slice(buf, (size_t)n);
    return n;
}

ssize_t read(int fd, void *buf, size_t len) {
    check_open(fd);
    assert(len == 8);
    if (nondet_u8() & 1) { errno = EAGAIN; return -1; }
    *(uint64_t *)buf = 1;
    return 8;
}

int main(void) {
    static conn_t conns[2];
    static uint32_t free_slots[2] = { 1, 0 };
    the_handler = model_new(3, 0);
    the_loop = (loop_t){ .threads = 1, .conns_max = 2, .write_ms = 30000, .linger_ms = 2000,
                         .tick_ms = 25, .workers = &the_worker };
    the_worker.loop = &the_loop;
    the_worker.epoll = 2;
    the_worker.listen = 3;
    the_worker.wake = 4;
    the_worker.handler = the_handler;
    the_worker.conns = conns;
    the_worker.free_slots = free_slots;
    the_worker.free_count = 2;
    conns[0].fd = conns[1].fd = -1;
    fd_open[2] = fd_open[3] = fd_open[4] = 1;
    work(&the_worker);
    assert(model_live == 1 && the_handler->rc == 1);
    for (int fd = 5; fd < FDS; fd++) assert(!fd_open[fd]);
    assert(!fd_open[3]);
    return 0;
}
