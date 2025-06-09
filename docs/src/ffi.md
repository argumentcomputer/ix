# Ix FFI framework

Ix extensively utilizes Lean's FFI capabilities to interface with Rust
implementations while minimizing overhead. This document consolidates the
principles for doing so responsibly.

We follow a strict dependency order:

* Lean can interface with C
* C can interface with Rust
* Lean can interface with Rust

Hence we use the following naming conventions:

* Names of external C functions start with "c_"
* Names of external Rust functions start with "rs_"
* Names of external C functions that depend on Rust functions start with "c_rs_"

Interfacing with C is a well-established and well-supported case in Lean. After
all, Lean's runtime is implemented in C and the API for reading, allocating and 
populating Lean objects is rich enough to support this interaction. Interfacing
with Rust, however, introduces a new set of challenges.

## Reading data from Lean

Making sense of data that's produced by Lean already poses an initial challenge.
One possible approach is as follows:

1. Serialize the data in Lean as a `ByteArray` and provide it to a C function
2. Get the reference to the slice of bytes and pass it to the Rust function
3. Deserialize the data and use it as needed

While that's possible (and plausible!) it adds a recurring serde cost overhead.
So the approach taken in Ix is different.

The Ix's Rust static lib mimics the memory layout of Lean runtime objects and
uses `unsafe` code to turn `*const c_void` pointers into appropriate `&T`
references. Though, when possible, raw data extraction of Lean objects is
preferably done in C with the API provided by the Lean toolchain (via `lean.h`).

For example, when targeting a Rust function that consumes a string, we don't
need to pass a reference to the whole `lean_string_object`. Instead, we make use
of the fact that Lean strings are `\0`-terminated and only pass a `char const *`
from C to Rust, which receives it as a `*const c_char` and then (unsafely) turns
it into a `&str`.

Extra care must be taken when dealing with
[inductive types](https://github.com/leanprover/lean4/blob/master/doc/dev/ffi.md#inductive-types),
as the order of arguments in the Lean objects may not match the same order from
the higher level type definition in Lean.

## Producing data for Lean

Since we can mimic the memory layout of Lean objects in Rust, we should allocate
and populate them in Rust, right? Well, the answer is "no".

Lean employs different allocation methods depending on compilation flags, making
it impractical to track them in Rust. Instead, we allocate the inner data on the
heap and return a raw pointer to C, which then wraps it using the appropriate
API.

A key concept in this design is that ownership of the data is transferred to
Lean, making it responsible for deallocation. If the data type is intended to be
used as a black box by Lean, `lean_external_object` is an useful abstraction. It
requires a function pointer for deallocation, meaning the Rust code must provide
a function that properly frees the object's memory by dropping it.

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
