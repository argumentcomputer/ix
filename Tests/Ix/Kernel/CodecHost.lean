/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Ix.Ixon

/-! Host-only production codec regressions, including generated values and
Rust serialization comparisons. This runner is outside the certified closure. -/

def main : IO UInt32 :=
  LSpec.lspecIO (.ofList [("certified-codec-production", Tests.Ixon.suite)]) []
