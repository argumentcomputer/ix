#pragma once
#include "lean/lean.h"
#include "common.h"

/*
This file provides a framework for enforcing linear usage of mutating objects by
Lean's runtime. It's particularly useful when making use of Rust objects that
don't implement `Clone` and work on the basis of mutation.
*/

typedef struct {
    /* A reference to the underlying mutable object */
    void *object_ref;
    /* A pointer to a function that can free `object_ref` */
    void (*finalizer)(void *);
    /* If set to `true`, the resource pointed by `object_ref` cannot be used */
    bool outdated;
    /* If set to `true`, allow the finalizer to be called on outdated objects */
    bool finalize_even_if_outdated;
} linear_object;

static inline linear_object *linear_object_init(void *object_ref, void (*finalizer)(void *)) {
    linear_object *linear = malloc(sizeof(linear_object));
    linear->object_ref = object_ref;
    linear->finalizer = finalizer;
    linear->outdated = false;
    linear->finalize_even_if_outdated = false;
    return linear;
}

static inline linear_object *to_linear_object(void *ptr) {
    return (linear_object*)ptr;
}

static inline void *get_object_ref(linear_object *linear) {
    return linear->object_ref;
}

static inline linear_object *linear_bump(linear_object *linear) {
    linear_object *copy = malloc(sizeof(linear_object));
    *copy = *linear;
    linear->outdated = true;
    return copy;
}

static inline void ditch_linear(linear_object *linear) {
    linear->outdated = true;
    linear->finalize_even_if_outdated = true;
}

static inline void assert_linearity(linear_object *linear) {
    if (LEAN_UNLIKELY(linear->outdated)) {
        lean_internal_panic("Non-linear usage of linear object");
    }
}

static inline void free_linear_object(linear_object *linear) {
    // Only finalize `object_ref` if `linear` is the latest linear object reference
    // or if the finalizer was forcibly set as allowed. By doing this, we avoid
    // double-free attempts.
    if (LEAN_UNLIKELY(!linear->outdated || linear->finalize_even_if_outdated)) {
        linear->finalizer(linear->object_ref);
    }
    free(linear);
}

/* --- API to implement Lean objects --- */

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

static inline linear_object *validated_linear(lean_object *obj) {
    linear_object *linear = to_linear_object(lean_get_external_data(obj));
    assert_linearity(linear);
    return linear;
}
