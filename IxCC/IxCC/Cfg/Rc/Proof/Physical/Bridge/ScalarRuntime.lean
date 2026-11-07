import IxCC.Cfg.Rc.Proof.Native.RawSource
import IxCC.Cfg.Rc.Proof.Native.Indices

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC IxCC.Cfg.Rc IxCC.Cfg.Rc.Native
open IxCC.Cfg.Rc.Native.Spec

private theorem suffix_at {α : Type} (before after : List α) (i : Nat) :
    (before ++ after)[before.length + i]? = after[i]? := by
  rw [List.getElem?_append_right (by omega)]
  simp

/-- The procedure slots used by primitive lowering are the actual pow/gcd
functions in the source stage, independent of the source-function map. -/
theorem source_stage_scalar_runtime (P : Program) (pairs : List (Nat × Cfg.Fun))
    (functions : Nat → Lir.Func) (main : Nat) :
    (Public.Spec.sourceStage P functions main).funcs[(tablesOf P pairs).natPow]? = some Rt.Procs.natPow ∧
    (Public.Spec.sourceStage P functions main).funcs[(tablesOf P pairs).natGcd]? = some Rt.Procs.natGcd := by
  have powRange : ¬ (tablesOf P pairs).natPow < P.base.size := by
    change ¬ P.base.size + 2 + (layoutOf P).ctors.length + 2 + (layoutOf P).ctors.length + 1 < P.base.size
    omega
  have gcdRange : ¬ (tablesOf P pairs).natGcd < P.base.size := by
    change ¬ P.base.size + 2 + (layoutOf P).ctors.length + 2 + (layoutOf P).ctors.length + 2 < P.base.size
    omega
  have powIndex : (tablesOf P pairs).natPow - P.base.size =
      (wrappers (layoutOf P)).length + ((procedures (layoutOf P)).length + 1) := by
    rw [wrappers_length, procedures_length]
    change (P.base.size + 2 + (layoutOf P).ctors.length + 2 + (layoutOf P).ctors.length + 1) - P.base.size =
      (2 + (layoutOf P).ctors.length) + ((2 + (layoutOf P).ctors.length) + 1)
    omega
  have gcdIndex : (tablesOf P pairs).natGcd - P.base.size =
      (wrappers (layoutOf P)).length + ((procedures (layoutOf P)).length + 2) := by
    rw [wrappers_length, procedures_length]
    change (P.base.size + 2 + (layoutOf P).ctors.length + 2 + (layoutOf P).ctors.length + 2) - P.base.size =
      (2 + (layoutOf P).ctors.length) + ((2 + (layoutOf P).ctors.length) + 2)
    omega
  constructor
  · rw [Public.Spec.sourceStage_get, if_neg powRange, powIndex]
    simp only [Public.Spec.runtimeFunctions, List.append_assoc]
    rw [suffix_at, suffix_at]
    rfl
  · rw [Public.Spec.sourceStage_get, if_neg gcdRange, gcdIndex]
    simp only [Public.Spec.runtimeFunctions, List.append_assoc]
    rw [suffix_at, suffix_at]
    rfl


end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
