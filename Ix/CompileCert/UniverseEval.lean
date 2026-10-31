import Ix.IxonUniv

/-! # The meaning of a stored universe

`univEval ρ u` is the value of a positional Ixon universe `u` when its
variable `i` has the value `ρ i`. It is the semantics against which the
canonicalizer is proved (`Ix.CompileCert.CanonUnivEmit.canonUniv_eval`), and
the wire side of the universe bridge between the compiler and the certified
reader (`Ix.CompileCert.CanonUnivScope.convUniv_eval`). It evaluates in
unbounded naturals, independently of how the canonicalizer represents its
successor offsets. -/

namespace Ix.CompileCert

/-- The value of a wire universe under a valuation of its variables. -/
def univEval (ρ : UInt64 → Nat) : Ixon.Univ → Nat
  | .zero => 0
  | .succ u => univEval ρ u + 1
  | .max u v => max (univEval ρ u) (univEval ρ v)
  | .imax u v => if univEval ρ v = 0 then 0 else max (univEval ρ u) (univEval ρ v)
  | .var i => ρ i

/-- The derived equality of wire universes is structural. -/
theorem univ_beq_iff (left right : Ixon.Univ) : (left == right) = true ↔ left = right := by
  induction left generalizing right <;> cases right <;>
    simp_all [BEq.beq, Ixon.instBEqUniv.beq]

/-- So maps and sets keyed by wire universes (the canonicalizer's call memo,
the compiler's canonical memo and universe tables) have lawful keys. -/
instance lawfulUnivBEq : LawfulBEq Ixon.Univ where
  eq_of_beq := (univ_beq_iff _ _).mp
  rfl := (univ_beq_iff _ _).mpr rfl

end Ix.CompileCert
