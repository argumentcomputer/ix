# Ix FFI framework

Ix extensively utilizes Lean's FFI capabilities to interface with Rust
implementations for performance benefits while minimizing overhead. This document
describes the approach used in Ix and best practices for writing Lean->Rust FFI.

Interfacing with C is a well-established and well-supported case in Lean. After
all, Lean's runtime is implemented in C and the API for reading, allocating and 
populating Lean objects is rich enough to support this interaction. Interfacing
with Rust, however, is not trivial because of Rust's distinct
ownership-based memory management system.

## Bindgen Rust bindings to `lean.h`

In order to avoid this complexity and keep Lean in control of memory
management for objects created via FFI to Rust, we use
the [`lean-ffi`](https://github.com/argumentcomputer/lean-ffi) crate.
This allows us to create and manage Lean objects in Rust without taking
control of the underlying memory, needing to implement `Drop`, or having to
know about the state of Lean's reference counting mechanism.

By convention, names of external Rust functions start with `rs_`.

## Elaboration-time FFI

Most Ix FFI is linked statically into final Lean executables. Proofs using
`native_decide`, however, execute compiled Lean code while modules are still
being elaborated, before any executable is linked. The native evaluator needs
two symbol layers for each opaque `@[extern]` it reaches: the raw Rust symbol
(e.g. `rs_blake3_init`, `c_u64_to_le_bytes`) and the boxed entry point Lean
calls into it (e.g. `lp_Blake3_Blake3_Rust_hasherInit___boxed`).

The `ix_native_decide_dynlib` Lake target assembles both layers from artifacts
that already exist, so no ABI is mirrored by hand:

- The boxed entry points are Lean's own generated objects for the declaring
  modules (`Blake3`, `Blake3.Rust`, `Ix.Unsigned`) — the same code linked into
  normal executables — fetched via each module's `oExport` facet.
- The raw symbols come from `cdylib` outputs recorded as load-time
  dependencies by absolute path (so no `LD_LIBRARY_PATH` is needed): Blake3's
  `blake3_rs`, and the minimal `ix-ffi-dyn` crate for Ix's own externs. That
  crate shares its source with `ix-ffi` but is kept separate so a
  proof only loads the handful of symbols it needs, not `ix-ffi`'s whole
  dependency graph.

When an opaque external operation becomes reachable from a new
elaboration-time computation, add its declaring module's object to the target
(the raw symbol is already present if it lives in a linked cdylib).

## Linear API

There is a deprecated API for passing mutable objects between Lean and Rust in `c/linear.h`.
This code path is unused for now as the Rust FFI is designed to clone if mutation is needed.
However, the `linear.h` file is well-documented in case we want to revisit it later for
performance-critical applications.
