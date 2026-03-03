/*

NOTE: This file and the linear API in general are currently unused, as we have decided to not pass mutable objects to and from Rust in order to keep the FFI boundary simple.

However, we may revisit the `linear.h` API in the future, at which point this file would be ported to Rust in the `lean_sys` crate.

For now, the `linear.h` documenation is provided below as a docstring.

*/

/*

## Dealing with mutable objects

As a functional language, Lean primarily uses purely functional data structures,
whereas Rust functions often mutate objects. This fundamental difference in
computational paradigms requires special care; otherwise, we risk introducing
Lean code with unintended or incorrect behavior.

Let's consider a type `T` and a Rust function `f(&mut T)`. In Lean, we would
like to have the corresponding `f : T → T`, which returns a modified `T` but
leaves the input `T` intact. How can we use Rust's `f` as the implementation of
Lean's `f`?

One approach is to use a Rust function `g(&T) -> T`, implemented as follows:

```rust
fn g<T: Clone>(t: &T) -> T {
    let mut clone = t.clone();
    f(&mut clone);
    clone
}
```

Already we can see two problems. First, `g` requires `T` to implement `Clone`.
Second, even when `T: Clone`, cloning might be expensive. The fact is that the
implementation provided, Rust's `f`, was designed to mutate `T` and we shouldn't
be fighting against that.

So Ix goes with the flow and mutates `T` with Rust's `f`. Consequently, Lean's
`f : T → T` will, in fact, mutate the input, which will be returned as the
output. A direct sin against the purity of the functional world.

At this point, the best we can do is to create guardrails to protect us against
ourselves and force us to use terms of `T` linearly when `f` is involved. That
is, after applying `f (t : T)`, reusing `t` should be prohibitive.

### The birth of `linear.h`

We've explored the motivation for the API provided by `linear.h`, in which a
`linear_object` wraps the reference to the raw Rust object and has a
`bool outdated` attribute telling whether the linear object can be used or not.
Then, instead of `lean_external_object` pointing directly to the Rust object, it
points to a `linear_object`. When we ought to use the Rust object, we must
always "assert linearity", which panics if `outdated` is `true`.

To illustrate it, let's use "E" for `lean_external_object`, "L" for
`linear_object` and "R" for potentially mutating Rust objects. Right after
initialization, we have:

```
E0 ──> L0 (outdated = false) ──> R
```

Now suppose we need to mutate `R`. We do it and then we perform a "linear bump",
which copies `L` and sets it as outdated. Then we wrap it as another external
object:

```
E1 ──> L1 (outdated = false) ─┐
E0 ──> L0 (outdated = true) ──┴> R
```

And after `N` linear bumps:

```
EN ──> LN (outdated = false) ─┐
...                           ┆
E2 ──> L2 (outdated = true) ──┤
E1 ──> L1 (outdated = true) ──┤
E0 ──> L0 (outdated = true) ──┴> R
```

Great. Now imagine Lean wants to free these external objects. The function that
frees a linear object should only free the Rust object when `outdated == false`.
Following up with the image above, let's free `E1`.

```
EN ──> LN (outdated = false) ─┐
...                           ┆
E2 ──> L2 (outdated = true) ──┤
                              │
E0 ──> L0 (outdated = true) ──┴> R
```

When freeing `EN`, the Rust object will be deallocated:

```
...                           ┆
E2 ──> L2 (outdated = true) ──┤
                              │
E0 ──> L0 (outdated = true) ──┴> X
```

All remaining external objects are outdated so their respective linear objects
won't try to free the (already dropped) Rust object.

## What if a Rust function takes ownership of the object?

When ownership is required, we mutate the Rust object by "taking" or "replacing"
it with a dummy object. Concretely, `std::mem::take` or `std::mem::replace` are
used, returning the actual `T` from a `&mut T`. And with `T` at hand, the target
function can be called.

The latest linear object is marked as outdated and the chain of linear objects
is broken. But then, how will the residual Rust object be dropped once Lean
wants to drop all external objects?

It turns out we also need a `bool finalize_even_if_outdated` attribute on the
`linear_object` struct, which becomes `true` in these scenarios. By doing this,
we're "ditching" the linear object. And the logic to free linear objects needs
one small adjustment: the Rust object must be dropped when either the linear
object is not outdated or when `finalize_even_if_outdated` is set to `true`.

The invariant that needs to be maintained is that *only one* linear object can
free the shared Rust object.

## Preventing unintentional Lean optimizations

We've done our lower level homework and now we have an `f : T → T` in Lean that
should panic at runtime when its input is reused. So we do:

```lean4
  ...
  let a := f t
  let b := f t -- reuses `t`!
  ...
```

We run the code and it executes smoothly. Why!?

The Lean compilation process detects that both `a` and `b` are equal to `f t` so
instead of calling `f` a second time it just sets `b` with the value of `a`. It
appears to be harmless but in fact we want discourage this kind of source code
at all costs.

Lean provides the tag `never_extract` precisely for this. It's used internally
when some function performs side-effects and should never be optimized away.

And to conclude, there are cases in which this optimization is truly harmful.
Consider an initialization function `T.init : Unit → T` in the following code:

```lean4
  ...
  let t1 := T.init ()
  let t2 := T.init ()
  let a := f t1
  let b := f t2
  ...
```

If `T.init` is not tagged with `never_extract`, `t2` and `t1` will point to the
same object, the first call to `f` will mark it as outdated and thus the second
call will panic!

So the `never_extract` tag must be applied to functions that:

* Mutate their input or
* Return objects that work on the basis of mutation

*/

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
