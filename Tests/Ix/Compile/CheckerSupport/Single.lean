-- Exact S_T_0_0_dir corpus case: its pattern-match helpers reach Nat.land,
-- whose pin certificate additionally needs Nat.mul outside the raw closure.
namespace AX.S_T_0_0_dir
inductive T : Type where
  | base : T
  | succ : T → T
noncomputable def auxRec := @T.rec
noncomputable def auxCases := @T.casesOn
noncomputable def auxRecOn := @T.recOn
noncomputable def auxBelow := @T.below
noncomputable def auxBrecOn := @T.brecOn
theorem casesEx (t : T) : True := by
  cases t <;> trivial
noncomputable def auxCtorIdx := @T.ctorIdx
theorem indEx (t : T) : True := by
  induction t <;> trivial
def isBase : T → Bool
  | .base => true
  | _ => false
noncomputable def auxNoConf := @T.noConfusion
noncomputable def auxNoConfType := @T.noConfusionType
def go : T → Nat
  | .base => 0
  | .succ t => go t + 1
termination_by structural t => t
noncomputable def goEq1 := @go.eq_1
noncomputable def goEqDef := @go.eq_def
noncomputable def goInduct := @go.induct
end AX.S_T_0_0_dir
