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

## Linear API

There is a deprecated API for passing mutable objects between Lean and Rust in `c/linear.h`.
This code path is unused for now as the Rust FFI is designed to clone if mutation is needed.
However, the `linear.h` file is well-documented in case we want to revisit it later for
performance-critical applications.

