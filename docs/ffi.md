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

## Certified execution boundary

Ix's runtime FFI is linked into host executables. The retired checker proof
loader and its separate dynamic-library crate have been removed. Certified
kernel and codec operations use pure Lean implementations; their runtime
audits reject project FFI and native-evaluation replacements. The Blake3
package supplies both the separately audited pure hash and host accelerators.
See [the kernel contract](kernel.md) for the precise boundaries.

## Linear API

There is a deprecated API for passing mutable objects between Lean and Rust in `c/linear.h`.
This code path is unused for now as the Rust FFI is designed to clone if mutation is needed.
However, the `linear.h` file is well-documented in case we want to revisit it later for
performance-critical applications.

## Rust to gnark

`ix-proof-compression::pipeline::gnark` wraps a Go C archive inside the
compression worker. The worker enables `plonk` and/or `groth16`; both
are excluded from the Lean-facing `ix-ffi` build. Rust owns setup admission,
artifact policy and publication; Go owns gnark objects and the verifier circuit.

The private C interface exchanges byte views, owned output buffers and integer
`runtime/cgo.Handle` values. `Prover` is neither `Send` nor `Sync`; its mutable
proof method excludes concurrent use, and drop releases the handle. Returned
C allocations are copied and freed through the adapter. Go panics on the exported
call's goroutine become errors; fatal runtime and device failures remain isolated
by the worker process. There is no ABI version or compatibility dispatcher.

The [backend guide](../tools/plonk-wrapper/README.md) describes builds and tests.
