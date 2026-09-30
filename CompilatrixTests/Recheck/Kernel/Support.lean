import Compilatrix.Recheck.Run

/-! What the kernel modules state about `Recheck.run` on the recheck
artifacts (M1.K1, M2.8): decidable equality of `Except` results, so a
claim reads `(Recheck.run cfg P c).map Artifact.bytes = .ok bytes`. -/

namespace CompilatrixTests.Recheck.Kernel

/-- `Except` compared constructor by constructor (the kernel evaluates it
through the derived instance; core provides none). -/
instance instDecidableEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α) := fun
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (by cases e; rfl)
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (by cases e; rfl)
  | .ok _, .error _ => isFalse fun e => by cases e
  | .error _, .ok _ => isFalse fun e => by cases e

end CompilatrixTests.Recheck.Kernel
