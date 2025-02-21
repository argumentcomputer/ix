#include "lean/lean.h"

/*
This file provides a framework for asserting the use of mutating objects as linear ones.
The main goal is to enable the use of Rust objects that don't implement Clone an work on
the basis of mutation by Lean.

The key idea is to keep track of a `linear_idx` and a `mut_counter`, which, when equal,
signal that the object at hand is the most updated one in the chain of linear operations.

Here's an illustration of a valid snapshot for some linear object:

            ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────────┐
            │linear_object│ │linear_object│ │linear_object│ │linear_object│
            │linear_idx=0 │ │linear_idx=1 │ │linear_idx=2 │ │linear_idx=3 │
            └──────┬──────┘ └──────┬──────┘ └──────┬──────┘ └──────┬──────┘
                   │               │               │               │
┌─────────────┐<───┘               │               │               │
│ mut_object  │<───────────────────┘               │               │
│mut_counter=3│<───────────────────────────────────┘               │
└──────┬──────┘<───────────────────────────────────────────────────┘
       │
       v
 ┌───────────┐
 │  Mutable  │
 │Rust object│
 └───────────┘

`mut_counter` must be bumped everytime the underlying Rust object mutates.
A bump on `linear_idx` must follow everytime an updated reference to `mut_object` is needed.

So a "linear bump" increments the `mut_counter` of the `mut_object` and copies the
`linear_object` with an incremented `linear_idx`.

Every `linear_object` needs to be kept in memory and served to Lean as a valid reference.
Though, upon usage, we can "assert linearity" to make sure that `liner_idx == mut_counter`
and assure that only the most updated linear object can be used.

Lastly, to free a linear object, we cannot free the `mut_object` unless `liner_idx == mut_counter`
otherwise that would potentially result on double-free attempts.
*/

typedef struct {
    size_t mut_counter;
    void   *object_ref;
    void   (*finalizer)(void *);
} mut_object;

typedef struct {
    size_t     linear_idx;
    mut_object *mut_object_ref;
} linear_object;

static linear_object *linear_object_init(void *object_ref, void (*finalizer)(void *)) {
    mut_object *mut_object_ref = malloc(sizeof(mut_object));
    mut_object_ref->mut_counter = 0;
    mut_object_ref->object_ref = object_ref;
    mut_object_ref->finalizer = finalizer;

    linear_object *linear = malloc(sizeof(linear_object));
    linear->linear_idx = 0;
    linear->mut_object_ref = mut_object_ref;
    return linear;
}

static inline linear_object *to_linear_object(void *ptr) {
    return (linear_object*)ptr;
}

static inline void *get_object_ref(linear_object *linear) {
    return linear->mut_object_ref->object_ref;
}

static inline void assert_non_zero(size_t val, char const *msg) {
    if (LEAN_UNLIKELY(val == 0)) {
        lean_internal_panic(msg);
    }
}

static inline void mutation_bump(linear_object *linear) {
    linear->mut_object_ref->mut_counter++;
    assert_non_zero(
        linear->mut_object_ref->mut_counter,
        "Linear object mutation counter overflow"
    );
}

static linear_object *linear_bump(linear_object *linear) {
    mutation_bump(linear);

    linear_object *new_linear = malloc(sizeof(linear_object));
    new_linear->linear_idx = linear->linear_idx + 1;
    assert_non_zero(
        new_linear->linear_idx,
        "Linear object index overflow"
    );
    new_linear->mut_object_ref = linear->mut_object_ref;
    return new_linear;
}

static inline void assert_linearity(linear_object *linear) {
    if (LEAN_UNLIKELY(linear->linear_idx != linear->mut_object_ref->mut_counter)) {
        lean_internal_panic("Non-linear usage of linear object");
    }
}

static inline void free_linear_object(linear_object *linear) {
    // Only free `mut_object_ref` if `linear` is the latest linear object reference
    if (LEAN_UNLIKELY(linear->linear_idx == linear->mut_object_ref->mut_counter)) {
        linear->mut_object_ref->finalizer(linear->mut_object_ref->object_ref);
        free(linear->mut_object_ref);
    }

    free(linear);
}

/* --- API to implement Lean objects --- */

static void noop_foreach(void *mod, b_lean_obj_arg fn) {}
static void linear_object_finalizer(void *ptr) {
    free_linear_object(to_linear_object(ptr));
}

static lean_external_class *g_linear_object_class = NULL;

static lean_external_class *get_linear_object_class() {
    if (g_linear_object_class == NULL) {
        g_linear_object_class = lean_register_external_class(
            &linear_object_finalizer,
            &noop_foreach
        );
    }
    return g_linear_object_class;
}

static inline lean_object *alloc_lean_linear_object(linear_object *linear) {
    return lean_alloc_external(get_linear_object_class(), linear);
}
