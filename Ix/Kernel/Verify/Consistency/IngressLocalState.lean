/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.LocalState
import Ix.Kernel.Verify.IngressState
import Ix.Kernel.Driver

/-!
# Production loader establishes the structural local invariant

The actual anonymous loader preserves every checker-owned environment field
on both outcomes. In particular, it cannot rewind the fresh-variable counter.
The lazy driver's initial state therefore establishes the structural local
invariant without a separate callback-effect assumption. Declaration meaning,
intern coherence and semantic cache preservation remain separate obligations.
-/

namespace Ix.Kernel.Consistency

theorem LoaderCounterMonotone.ingressAnonAddrShallow (env : Ixon.Env) (verify : Bool) :
    LoaderCounterMonotone (some fun addr => ingressAnonAddrShallow env addr verify) := by
  intro fault installed addr before
  cases installed
  dsimp only
  have frame := IngressM.FramesState.ingressAnonAddrShallow env addr verify before
  cases run : _root_.Ix.Kernel.ingressAnonAddrShallow env addr verify before <;> rw [run] at frame <;>
    exact Nat.le_of_eq (congrArg UInt64.toNat frame.counter.symm)

/-- The structural local invariant is established by the actual lazy driver,
including its concrete loader. It needs no loader-effect premise. -/
theorem LocalStateInvariant.newLazyAnon (env : Ixon.Env) (verify : Bool) :
    LocalStateInvariant (TcState.newLazyAnon env verify) :=
  ⟨LocalContext.WF.empty, LocalContext.IdsBelow.empty _,
    LoaderCounterMonotone.ingressAnonAddrShallow env verify⟩

end Ix.Kernel.Consistency
