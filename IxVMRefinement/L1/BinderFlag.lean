import IxVMRefinement.L1.BinderData

/-! # The structural binder flag used by conversion

The flag follows sharing entries only below the active bound, exactly as the converter does.
It determines whether conversion must consume serialized binder data.
-/

namespace IxVM.Refinement.L1

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

/-- Whether an expression's expanded syntax contains a lambda or forall binder. -/
def needsBinderAt (sharing : List Ixon.Expr) (bound : Nat) (expr : Ixon.Expr) : Bool :=
  match expr with
  | .lam _ _ | .all _ _ => true
  | .app func arg => needsBinderAt sharing bound func || needsBinderAt sharing bound arg
  | .prj _ _ inner => needsBinderAt sharing bound inner
  | .letE _ _ ty value body =>
    (needsBinderAt sharing bound ty || needsBinderAt sharing bound value) || needsBinderAt sharing bound body
  | .share index =>
    if index.toNat < bound then
      match sharing[index.toNat]? with
      | some entry => needsBinderAt sharing index.toNat entry
      | none => false
    else false
  | _ => false
termination_by (bound, sizeOf expr)
decreasing_by
  all_goals simp_wf
  all_goals omega

def binderFlag (needed : Bool) : Nat := if needed then 1 else 0

theorem binderFlag_or_zero {left right : Bool} {a b : Nat}
    (leftCode : a = binderFlag left) (rightCode : b = binderFlag right)
    (leftZero : a = 0) (rightZero : b = 0) : 0 = binderFlag (left || right) := by
  cases left <;> cases right <;> simp_all [binderFlag]

theorem binderFlag_or_nonzero {left right : Bool} {a b : Nat} {value : SourceValue F}
    (leftCode : a = binderFlag left) (rightCode : b = binderFlag right)
    (added : evalBinOp .add (.field (a : F)) (.field (b : F)) = .ok value)
    (nonzero : value ≠ .field 0) : 1 = binderFlag (left || right) := by
  cases left <;> cases right <;> simp_all [binderFlag, evalBinOp]

theorem binderFlag_three_zero {first second third : Bool} {a b c : Nat}
    (firstCode : a = binderFlag first) (secondCode : b = binderFlag second)
    (thirdCode : c = binderFlag third) (firstZero : a = 0) (secondZero : b = 0)
    (thirdZero : c = 0) : 0 = binderFlag ((first || second) || third) := by
  cases first <;> cases second <;> cases third <;> simp_all [binderFlag]

theorem binderFlag_three_nonzero {first second third : Bool} {a b c : Nat}
    {middle value : SourceValue F}
    (firstCode : a = binderFlag first) (secondCode : b = binderFlag second)
    (thirdCode : c = binderFlag third)
    (added₁ : evalBinOp .add (.field (a : F)) (.field (b : F)) = .ok middle)
    (added₂ : evalBinOp .add middle (.field (c : F)) = .ok value)
    (nonzero : value ≠ .field 0) : 1 = binderFlag ((first || second) || third) := by
  subst a b c
  cases first <;> cases second <;> cases third
  all_goals first
    | rfl
    | (simp only [binderFlag, Nat.cast_zero, evalBinOp, zero_add, Except.ok.injEq] at added₁
       subst middle
       simp only [binderFlag, Nat.cast_zero, evalBinOp, zero_add, Except.ok.injEq] at added₂
       exact False.elim (nonzero added₂.symm))

theorem binderFlag_nonzero {needed : Bool} {bit : Nat}
    (code : bit = binderFlag needed) (nonzero : (.field (bit : F) : SourceValue F) ≠ .field 0) :
    1 = binderFlag needed := by
  cases needed <;> simp_all [binderFlag]

end IxVM.Refinement.L1
