/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import LSpec
import Ix.Kernel.Verify.Consistency.Resolution
import Tests.Ix.Kernel.IxonFixtures

/-!
Regressions for the canonical reference map `Ixon.Env.resolve` on hand-built
fixture environments. This file is not a `module` because the proof library
it exercises is not one.
-/

namespace Tests.Kernel.Resolution

open LSpec Ix.Kernel Tests.Kernel.Fixtures

/-- Standalones are one-member blocks at their own address, projections resolve
by block position and member kind, and Muts blocks, absent projections, and
mismatched records resolve to nothing. -/
private def cases : TestSeq :=
  let (standaloneEnv, axiomAddr, definitionAddr) := envIdA
  let (mutualEnv, mutualBlock) := envMutualDefs
  let (inductiveEnv, inductiveBlock) := envInductive
  let (_, carrier) := envA
  let (mismatched, wrongKind) :=
    storeConst mutualEnv ⟨.rPrj ⟨0, mutualBlock⟩, #[], #[], #[]⟩
  test "resolution: standalone keys resolve to their own one-member block"
    (standaloneEnv.resolve axiomAddr == some (.member axiomAddr 0) &&
      standaloneEnv.resolve definitionAddr == some (.member definitionAddr 0) &&
      standaloneEnv.consts.keys.all fun addr =>
        standaloneEnv.resolve addr == some (.member addr 0))
  ++ test "resolution: mutual definitions resolve to their block positions"
    (mutualEnv.resolve (defnProjAddr mutualBlock 0) == some (.member mutualBlock 0) &&
      mutualEnv.resolve (defnProjAddr mutualBlock 1) == some (.member mutualBlock 1) &&
      mutualEnv.resolve carrier == some (.member carrier 0))
  ++ test "resolution: a Muts block, an absent projection, and a mismatched record resolve to nothing"
    (mutualEnv.resolve mutualBlock == none &&
      mutualEnv.resolve (defnProjAddr mutualBlock 2) == none &&
      mismatched.resolve wrongKind == none)
  ++ test "resolution: inductive and constructor projections resolve to their coordinates"
    (inductiveEnv.resolve (indcProjAddr inductiveBlock 0) == some (.member inductiveBlock 0) &&
      inductiveEnv.resolve (ctorProjAddr inductiveBlock 0 0) == some (.ctor inductiveBlock 0 0) &&
      inductiveEnv.resolve (ctorProjAddr inductiveBlock 0 1) == none)
  ++ test "resolution: the finite materialization check accepts the fixtures"
    (Ix.Kernel.Consistency.sourceMaterializesCheck standaloneEnv &&
      Ix.Kernel.Consistency.sourceMaterializesCheck mutualEnv &&
      Ix.Kernel.Consistency.sourceMaterializesCheck inductiveEnv)

def suite : List TestSeq := [cases]

end Tests.Kernel.Resolution
