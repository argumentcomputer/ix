/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
module
public import Ix.Address.Core
public import Blake3.Pure

public section

/-! # Pure BLAKE3 addresses

`Address.blake3Pure` computes an address with `Blake3.Pure.hash`, the total
pure Lean BLAKE3 implementation of the Blake3 package. It imports neither the
C nor the Rust backend, so certified paths that must hash (address
reconstruction, authentication, subject roots) can use it without any foreign
code in their execution closure. `Address.blake3` (`Ix.Address`) remains the
host accelerator over the Rust backend; the two are compared on fixture
corpora by `Tests.Ix.Kernel.AddressPure`. -/

/-- Compute the Blake3 hash of a `ByteArray` in pure Lean, returning an `Address`. -/
def Address.blake3Pure (x : ByteArray) : Address := ⟨(Blake3.Pure.hash x).val⟩

end
