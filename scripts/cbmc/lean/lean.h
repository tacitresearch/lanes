/* What `native/loop.c` uses of Lean's runtime, as a model for CBMC (`scripts/cbmc.sh`): every
   object counts its references, and one dropped more often than it is held, or used after it is
   freed, fails an assertion or CBMC's pointer check. */
#pragma once
#include <assert.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

#define LEAN_EXPORT

typedef struct lean_object {
    int rc;
    int kind; /* 0 a constructor, 1 a byte array, 2 an array, 3 anything else */
    size_t size; /* the bytes of a byte array, the fields of a constructor or an array */
    struct lean_object **fields;
    uint64_t scalars[4];
    uint8_t *data;
} lean_object;

typedef lean_object *lean_obj_res;
typedef lean_object *lean_obj_arg;
typedef lean_object *b_lean_obj_arg;
typedef struct { int unused; } lean_external_class;

extern size_t model_live;

static inline lean_object *lean_box(size_t n) { return (lean_object *)((n << 1) | 1); }
static inline int lean_is_scalar(lean_object *o) { return ((size_t)o & 1) == 1; }

static inline lean_object *model_new(int kind, size_t size) {
    lean_object *o = malloc(sizeof *o);
    __CPROVER_assume(o != NULL);
    o->rc = 1;
    o->kind = kind;
    o->size = size;
    o->fields = (kind == 0 || kind == 2) ? calloc(size ? size : 1, sizeof(lean_object *)) : NULL;
    o->data = kind == 1 ? malloc(size ? size : 1) : NULL;
    __CPROVER_assume((kind != 0 && kind != 2) || o->fields != NULL);
    __CPROVER_assume(kind != 1 || o->data != NULL);
    model_live++;
    return o;
}

static inline void lean_inc(lean_object *o) {
    if (lean_is_scalar(o)) return;
    assert(o->rc > 0);
    o->rc++;
}

static inline int model_drop(lean_object *o) {
    assert(o->rc > 0 && "an object is dropped more often than it is held");
    return --o->rc == 0;
}

static inline void model_free(lean_object *o) {
    free(o->fields);
    free(o->data);
    free(o);
    model_live--;
}

/* Two levels deep, which is as deep as the objects of the model go: a turn and its line and
   bytes, an answer box and its letters. */
static inline void model_drop_field(lean_object *o, size_t i) {
    if (!o->fields || i >= o->size) return;
    lean_object *f = o->fields[i];
    if (!f || lean_is_scalar(f) || !model_drop(f)) return;
    assert(!f->fields || f->size == 0 || lean_is_scalar(f->fields[0]));
    model_free(f);
}

static inline void lean_dec_ref(lean_object *o) {
    if (!model_drop(o)) return;
    assert(!o->fields || o->size <= 2);
    model_drop_field(o, 0);
    model_drop_field(o, 1);
    model_free(o);
}

static inline lean_object *lean_ctor_get(lean_object *o, unsigned i) {
    assert(o->kind == 0 && i < o->size);
    return o->fields[i];
}

static inline uint64_t lean_ctor_get_uint64(lean_object *o, unsigned offset) {
    size_t base = sizeof(void *) * o->size;
    assert(o->kind == 0 && offset >= base && (offset - base) % 8 == 0 && (offset - base) / 8 < 4);
    return o->scalars[(offset - base) / 8];
}

static inline size_t lean_sarray_size(lean_object *o) { assert(o->kind == 1); return o->size; }
static inline uint8_t *lean_sarray_cptr(lean_object *o) { assert(o->kind == 1); return o->data; }
static inline lean_object *lean_alloc_sarray(unsigned elem, size_t size, size_t capacity) {
    assert(elem == 1 && size == capacity);
    return model_new(1, size);
}
static inline size_t lean_array_size(lean_object *o) { assert(o->kind == 2); return o->size; }
static inline lean_object *lean_array_get_core(lean_object *o, size_t i) {
    assert(o->kind == 2 && i < o->size);
    return o->fields[i];
}

static inline void lean_internal_panic(const char *msg) { (void)msg; assert(0 && "panic"); }
static inline void lean_internal_panic_out_of_memory(void) { __CPROVER_assume(0); }
static inline void lean_mark_mt(lean_object *o) { (void)o; }
static inline lean_object *lean_mk_string(const char *s) { (void)s; return model_new(3, 0); }
static inline lean_object *lean_mk_io_user_error(lean_object *s) { return s; }
static inline lean_object *lean_decode_io_error(int e, lean_object *f) {
    (void)e; (void)f; return model_new(3, 0);
}
static inline lean_object *lean_io_result_mk_ok(lean_object *o) { return o; }
static inline lean_object *lean_io_result_mk_error(lean_object *o) { return o; }
static inline const char *lean_string_cstr(lean_object *o) { (void)o; return "127.0.0.1"; }
static inline lean_external_class *lean_register_external_class(void (*f)(void *),
                                                                void (*g)(void *, lean_object *)) {
    (void)f; (void)g; return NULL;
}
static inline lean_object *lean_alloc_external(lean_external_class *c, void *p) {
    (void)c; (void)p; return model_new(3, 0);
}
static inline void *lean_get_external_data(lean_object *o) { (void)o; return NULL; }
