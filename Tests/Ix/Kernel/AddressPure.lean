import Ix.Address
import Ix.Address.Pure
import Ix.Address.Admission
import Lean.Compiler.ImplementedByAttr

/-! # Pure and Rust BLAKE3 agreement on `Address`

`Address.blake3Pure` (the pure Lean implementation) and `Address.blake3` (the
Rust backend) must agree. The Blake3 package tests the two implementations
against each other at block and tree boundaries; these checks cover the
`Address` wrappers on the empty input, a short string, and lengths around the
64-byte block and 1024-byte chunk boundaries. They run at elaboration time,
which needs the Blake3 package's precompiled backend.

The admission hash `Address.admissionHash` is `Address.blake3Pure` for every
theorem and executes as `Address.blake3`; the owner-approved assumption that
licenses that substitution is this agreement, so it is checked here on the
admission hash as executed too. -/

private def pattern (n : Nat) : ByteArray :=
  ⟨Array.ofFn (n := n) fun i => (i.val % 251).toUInt8⟩

private def agree (n : Nat) : Bool :=
  Address.blake3Pure (pattern n) == Address.blake3 (pattern n) &&
    Address.admissionHash (pattern n) == Address.blake3Pure (pattern n)

#guard Address.blake3Pure ⟨#[]⟩ == Address.blake3 ⟨#[]⟩
#guard Address.blake3Pure "Hello".toUTF8 == Address.blake3 "Hello".toUTF8
#guard toString (Address.blake3Pure ⟨#[]⟩) ==
  "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
#guard toString (Address.admissionHash ⟨#[]⟩) ==
  "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
#guard [0, 1, 63, 64, 65, 1023, 1024, 1025, 2048, 2049, 3072].all agree
-- the executed admission hash is the Rust backend's
run_cmd do
  unless Lean.Compiler.getImplementedBy? (← Lean.getEnv) ``Address.admissionHash == some ``Address.blake3 do
    throwError "Address.admissionHash does not execute as Address.blake3"
