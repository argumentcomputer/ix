/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Ix.Ixon
import Ix.Ixon.Bounded.Universe

/-! Host-only production codec regressions, including generated values and
Rust serialization comparisons. This runner is outside the certified closure. -/

open LSpec SlimCheck Ixon

def boundedUnivMatchesRust (value : Univ) : Bool :=
  let bytes := serUniv value
  match Bounded.deUniv bytes.size value.nodeCount bytes with
  | .error _ => false
  | .ok decoded =>
    decoded == value && Tests.FFI.Ixon.rsEqUnivSerialization decoded bytes &&
      !(Bounded.deUniv bytes.size (value.nodeCount - 1) bytes).isOk &&
      !(Bounded.deUniv (bytes.size - 1) value.nodeCount bytes).isOk

def main : IO UInt32 :=
  LSpec.lspecIO (.ofList [
    ("certified-codec-production", Tests.Ixon.suite),
    ("bounded-universe", [checkIO "exact limits and Rust serialization"
      (∀ value : Univ, boundedUnivMatchesRust value)])]) []
