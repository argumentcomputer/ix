import Ix.LeanIngress.Expr
import Ix.CompileCert.CanonUnivEmit
import IxC.Kernel.Verify.Level

/-! # Canonical levels keep their value

The ingress puts every level of a lowered declaration in the compiler's
canonical form (`Ix.LeanIngress.canonLevelIn`: `Ixon.canonUniv` over the
constant's level parameters by their index in its list, read back as
positions). That changes no level's value at any assignment
(`canonLevelIn_eval`), by `canonUniv_eval` and the round trip of a position
through its index (`ofIdxIn_idxIn`), for positions whose index fits the
wire's variables (64 bits). -/

namespace Ix.LeanIngress

open Ix.Kernel (LevelParam)

/-- Every parameter of a level satisfies `P`. -/
def ParamsAll (P : LevelParam → Prop) : KLevel → Prop
  | .zero => True
  | .succ u => ParamsAll P u
  | .max u v => ParamsAll P u ∧ ParamsAll P v
  | .imax u v => ParamsAll P u ∧ ParamsAll P v
  | .param p => P p

theorem univEval_univOfLevel (ρ : UInt64 → Nat) (ι : LevelParam → Nat) (l : KLevel) :
    Ix.CompileCert.univEval ρ (univOfLevel ι l) = l.eval (fun p => ρ (ι p).toUInt64) := by
  induction l <;> simp_all [univOfLevel, Ix.CompileCert.univEval, Ix.Kernel.Level.eval]

theorem eval_levelOfUniv (φ : LevelParam → Nat) (π : Nat → LevelParam) (u : Ixon.Univ) :
    (levelOfUniv π u).eval φ = Ix.CompileCert.univEval (fun i => φ (π i.toNat)) u := by
  induction u <;> simp_all [levelOfUniv, Ix.CompileCert.univEval, Ix.Kernel.Level.eval]

/-- A level's value depends on its parameters' values only. -/
theorem eval_congr {φ ψ : LevelParam → Nat} {P : LevelParam → Prop} (l : KLevel)
    (h : ParamsAll P l) (agree : ∀ p, P p → φ p = ψ p) : l.eval φ = l.eval ψ := by
  induction l <;> simp_all [ParamsAll, Ix.Kernel.Level.eval]

/-- **Canonicalizing a level keeps its value** at every assignment, when
its positions' indices fit the wire's 64-bit variables. -/
theorem canonLevelIn_eval (lps : List LevelParam) (φ : LevelParam → Nat) (l : KLevel)
    (bound : ParamsAll (fun p => idxIn lps p < UInt64.size) l) :
    (canonLevelIn lps l).eval φ = l.eval φ := by
  rw [canonLevelIn, eval_levelOfUniv, Ix.CompileCert.CanonUnivEmit.canonUniv_eval, univEval_univOfLevel]
  apply eval_congr l bound
  intro p hp
  have round : (idxIn lps p).toUInt64.toNat = idxIn lps p := UInt64.toNat_ofNat_of_lt' hp
  simp only [round, ofIdxIn_idxIn]

end Ix.LeanIngress

/-- info: 'Ix.LeanIngress.canonLevelIn_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.canonLevelIn_eval
