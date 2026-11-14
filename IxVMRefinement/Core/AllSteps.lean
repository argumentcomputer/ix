import IxVMRefinement.Subst.Steps
import IxVMRefinement.Nat.Steps
import IxVMRefinement.Levels.Spec
import IxVMRefinement.Whnf.Steps
import IxVMRefinement.DefEq.Steps
import IxVMRefinement.Infer.Steps
import IxVMRefinement.Roles.Steps
import IxVMRefinement.Callees.Steps

/-! # Registry step closure and `L4` at `S₀`

`all_steps` combines the step theorems of all nine registry families (`Fn`) into `Steps c`, closing
the strong induction (`Registry.induction`). From that single induction on call-list length,
`core_S₀` discharges `IxVM.Consistency.Core S₀` (`whnf`, `k_is_def_eq`, `k_infer` up to
`View.HashedCollision`), giving `l4_S₀ : IxVM.Consistency.L4 S₀`. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

/-- **One step per function of the `LevelOps` family.** -/
theorem levelOps_step (c : Ctx) :
    ∀ (f : Specs.LevelOps.Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W (Fn.levelOps f).name args h r h' cs → IH c cs →
      (Fn.levelOps f).spec c args h r h' cs
  | .level_leq, _, _, _, _, _, ev, _ => IxVM.Refinement.Levels.levelLeq_step ev
  | .level_equal, _, _, _, _, _, ev, _ => IxVM.Refinement.Levels.levelEqual_step ev
  | .level_is_not_zero, _, _, _, _, _, ev, _ => IxVM.Refinement.Levels.levelIsNotZero_step ev
  | .level_struct_eq, _, _, _, _, _, ev, _ => IxVM.Refinement.Levels.levelStructEq_step ev
  | .level_max, _, _, _, _, _, ev, _ => IxVM.Refinement.Levels.levelMax_step ev
  | .level_imax, _, _, _, _, _, ev, _ => IxVM.Refinement.Levels.levelIMax_step ev
  | .level_reduce, _, _, _, _, _, ev, _ => IxVM.Refinement.Levels.levelReduce_step ev
  | .level_inst_params, _, _, _, _, _, ev, _ => IxVM.Refinement.Levels.levelInstParams_step ev
  | .level_list_inst, _, _, _, _, _, ev, _ => IxVM.Refinement.Levels.levelListInst_step ev

/-- **Every registered function satisfies its step**, from `CoreFacts c`. -/
theorem all_steps (c : Ctx) (hc : CoreFacts c) : Steps c
  | .subst f, _, _, _, _, _, ev, ih => subst_step c f _ _ _ _ _ ev ih
  | .levels f, _, _, _, _, _, ev, ih => levels_step c f _ _ _ _ _ ev ih
  | .levelOps f, _, _, _, _, _, ev, ih => levelOps_step c f _ _ _ _ _ ev ih
  | .whnf f, _, _, _, _, _, ev, ih => whnf_family_step c hc f _ _ _ _ _ ev ih
  | .defEq f, _, _, _, _, _, ev, ih => defEq_step c hc f _ _ _ _ _ ev ih
  | .infer f, _, _, _, _, _, ev, ih => infer_step c hc f _ _ _ _ _ ev ih
  | .nat f, _, _, _, _, _, ev, ih => nat_step c hc f _ _ _ _ _ ev ih
  | .roles f, _, _, _, _, _, ev, ih => roles_step c hc f _ _ _ _ _ ev ih
  | .callees f, _, _, _, _, _, ev, ih => callees_step c hc f _ _ _ _ _ ev ih

/-- **Obligation L4's content at `S₀`**: weak head normalization, definitional equality, and
full-grade type inference refine `Ix.Kernel.Rules.{Red,DefEq,Infer}` up to hashed collision. -/
theorem core_S₀ : IxVM.Consistency.Core S₀ := by
  rintro E env ⟨κ, Γ⟩ d rc types heap after cs ⟨t, lim, hκ, hrc, hty, hs, henv, hloads⟩ hbd
  dsimp only [Ghost.κ, Ghost.Γ] at hκ hty hs
  subst hκ
  let c : Ctx := ⟨E, env, t, lim⟩
  have hc : CoreFacts c := ⟨henv, hloads⟩
  have htypes : c.types Γ heap d types := ⟨hty, hs⟩
  by_cases hcol : View.HashedCollision { env := E } [] cs
  · exact ⟨fun _ _ _ _ _ => .inl hcol, fun _ _ _ _ _ _ _ => .inl hcol, fun _ _ _ _ _ => .inl hcol⟩
  · have hgood : Good c cs := ⟨hcol, hbd⟩
    refine ⟨?_, ?_, ?_⟩
    · intro e r te ev hte
      exact .inr (Registry.induction c (all_steps c hc) (.whnf .whnf)
        [rc, e, types] heap r after cs ev rc e types rfl hgood hrc d Γ htypes te hte)
    · intro a b ta tb ev hta htb
      exact .inr (Registry.induction c (all_steps c hc) (.defEq .k_is_def_eq)
        [rc, a, b, types] heap (.field 1) after cs ev rc a b types rfl hgood hrc d Γ htypes ta tb
        hta htb NatAux.field_one_ne_zero)
    · intro e r te ev hte
      exact .inr (Registry.induction c (all_steps c hc) (.infer .k_infer)
        [rc, e, types] heap r after cs ev rc e types rfl hgood hrc d Γ htypes te hte)

/-- **Obligation L4 at `S₀`.** -/
theorem l4_S₀ : IxVM.Consistency.L4 S₀ := fun _ _ _ => core_S₀

end IxVM.Refinement.Core
