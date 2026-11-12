import IxVMRefinement.Subst.Spine

/-! # The substitution family: its induction closed, its registry steps, and `Terms S₀`

`gall κ`: every observed derivation of a function of the family meets its spec at the keying
`κ` (`Subst/Spec.lean`), by the family's own induction over the step lemmas of
`Subst/{Lbr,Occ,Glb,Lift,Inst,Ctx,Spine}.lean`.

**Registry steps.** At `κ = c.κ` and with `Good c calls` weakened to its bound, `gall` is each
registry spec of the family (`Core/Specs/Subst.lean`): `<f>_step` for each of the 39 functions,
and `subst_step`, the family's part of the registry harness's `Steps`.

**`Terms S₀`** (`IxVM.Consistency.Terms`, obligation L3): `expr_inst1(e, arg, 0)` is the
kernel's `instantiate1`, and `expr_lift(e, 1, 0)` reads the same image under one more opened
variable; at the keying of any ghost, with the derivation's ROM bound alone. -/

namespace IxVM.Refinement.Core.SubstAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

set_option linter.unusedVariables false

/-- **One step per function of the family.** -/
theorem gstep (κ : _root_.Address → KKey) :
    ∀ (f : Specs.Subst.Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W f.name args h r h' cs → GIH κ cs →
      gspec κ f args h r h' cs
  | .expr_lbr, _, _, _, _, _, ev, ih => g_expr_lbr κ ev ih
  | .expr_lbr_let, _, _, _, _, _, ev, ih => g_expr_lbr_let κ ev ih
  | .lbr_max, _, _, _, _, _, ev, _ => g_lbr_max ev
  | .lbr_dec, _, _, _, _, _, ev, _ => g_lbr_dec ev
  | .lbr_min, _, _, _, _, _, ev, _ => g_lbr_min ev
  | .has_bvar_in_range, _, _, _, _, _, ev, ih => g_has_bvar_in_range κ ev ih
  | .has_bvar_in_range_bvar, _, _, _, _, _, ev, _ => g_has_bvar_in_range_bvar ev
  | .has_bvar_in_range_binder, _, _, _, _, _, ev, ih => g_has_bvar_in_range_binder κ ev ih
  | .has_bvar_in_range_let, _, _, _, _, _, ev, ih => g_has_bvar_in_range_let κ ev ih
  | .expr_has_bvar_at, _, _, _, _, _, ev, ih => g_expr_has_bvar_at κ ev ih
  | .expr_has_bvar_at_binder, _, _, _, _, _, ev, ih => g_expr_has_bvar_at_binder κ ev ih
  | .expr_has_bvar_at_let, _, _, _, _, _, ev, ih => g_expr_has_bvar_at_let κ ev ih
  | .expr_glb, _, _, _, _, _, ev, ih => g_expr_glb κ ev ih
  | .expr_glb_walk, _, _, _, _, _, ev, ih => g_expr_glb_walk κ ev ih
  | .expr_glb_binder, _, _, _, _, _, ev, ih => g_expr_glb_binder κ ev ih
  | .expr_glb_let, _, _, _, _, _, ev, ih => g_expr_glb_let κ ev ih
  | .expr_lift, _, _, _, _, _, ev, ih => g_expr_lift κ ev ih
  | .expr_lift_walk, _, _, _, _, _, ev, ih => g_expr_lift_walk κ ev ih
  | .expr_lift_bvar, _, _, _, _, _, ev, _ => g_expr_lift_bvar κ ev
  | .expr_lift_let, _, _, _, _, _, ev, ih => g_expr_lift_let κ ev ih
  | .expr_lower, _, _, _, _, _, ev, ih => g_expr_lower κ ev ih
  | .expr_lower_walk, _, _, _, _, _, ev, ih => g_expr_lower_walk κ ev ih
  | .expr_lower_let, _, _, _, _, _, ev, ih => g_expr_lower_let κ ev ih
  | .expr_inst1, _, _, _, _, _, ev, ih => g_expr_inst1 κ ev ih
  | .expr_inst1_walk, _, _, _, _, _, ev, ih => g_expr_inst1_walk κ ev ih
  | .expr_inst1_bvar, _, _, _, _, _, ev, ih => g_expr_inst1_bvar κ ev ih
  | .expr_inst1_let, _, _, _, _, _, ev, ih => g_expr_inst1_let κ ev ih
  | .expr_inst_many, _, _, _, _, _, ev, ih => g_expr_inst_many κ ev ih
  | .expr_inst_many_bvar, _, _, _, _, _, ev, ih => g_expr_inst_many_bvar κ ev ih
  | .expr_inst_many_walk, _, _, _, _, _, ev, ih => g_expr_inst_many_walk κ ev ih
  | .expr_inst_many_let, _, _, _, _, _, ev, ih => g_expr_inst_many_let κ ev ih
  | .ctx_trim, _, _, _, _, _, ev, ih => g_ctx_trim κ ev ih
  | .ctx_reachable, _, _, _, _, _, ev, ih => g_ctx_reachable (κ := κ) ev ih
  | .ctx_seek_cut, _, _, _, _, _, ev, ih => g_ctx_seek_cut (κ := κ) ev ih
  | .ctx_next_cut, _, _, _, _, _, ev, _ => g_ctx_next_cut ev
  | .ctx_close_cut, _, _, _, _, _, ev, ih => g_ctx_close_cut (κ := κ) ev ih
  | .collect_spine, _, _, _, _, _, ev, ih => g_collect_spine κ ev ih
  | .expr_inst_levels, _, _, _, _, _, ev, ih => g_expr_inst_levels κ ev ih
  | .expr_inst_levels_walk, _, _, _, _, _, ev, ih => g_expr_inst_levels_walk κ ev ih

/-- **Every function of the family meets its spec at every keying.** -/
theorem gall (κ : _root_.Address → KKey) :
    ∀ (f : Specs.Subst.Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W f.name args h r h' cs →
      gspec κ f args h r h' cs :=
  ginduction κ (gstep κ)

end IxVM.Refinement.Core.SubstAux

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

set_option linter.unusedVariables false

section Steps
variable (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
  {calls : List (Call F)}

theorem expr_lbr_step (ev : ObsFn W "KernelSubst::expr_lbr" args h r h' calls) (ih : IH c calls) :
    Specs.Subst.expr_lbr c args h r h' calls :=
  fun a hargs good => SubstAux.gall c.κ .expr_lbr _ _ _ _ _ ev a hargs good.2

theorem expr_lbr_let_step (ev : ObsFn W "KernelSubst::expr_lbr_let" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_lbr_let c args h r h' calls :=
  fun a b d hargs good => SubstAux.gall c.κ .expr_lbr_let _ _ _ _ _ ev a b d hargs good.2

theorem lbr_max_step (ev : ObsFn W "KernelSubst::lbr_max" args h r h' calls) (ih : IH c calls) :
    Specs.Subst.lbr_max c args h r h' calls :=
  fun a b hargs good => SubstAux.gall c.κ .lbr_max _ _ _ _ _ ev a b hargs good.2

theorem lbr_dec_step (ev : ObsFn W "KernelSubst::lbr_dec" args h r h' calls) (ih : IH c calls) :
    Specs.Subst.lbr_dec c args h r h' calls :=
  fun a hargs good => SubstAux.gall c.κ .lbr_dec _ _ _ _ _ ev a hargs good.2

theorem lbr_min_step (ev : ObsFn W "KernelSubst::lbr_min" args h r h' calls) (ih : IH c calls) :
    Specs.Subst.lbr_min c args h r h' calls :=
  fun a b hargs good => SubstAux.gall c.κ .lbr_min _ _ _ _ _ ev a b hargs good.2

theorem has_bvar_in_range_step (ev : ObsFn W "KernelSubst::has_bvar_in_range" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.has_bvar_in_range c args h r h' calls :=
  fun a b d hargs good => SubstAux.gall c.κ .has_bvar_in_range _ _ _ _ _ ev a b d hargs good.2

theorem has_bvar_in_range_bvar_step
    (ev : ObsFn W "KernelSubst::has_bvar_in_range_bvar" args h r h' calls) (ih : IH c calls) :
    Specs.Subst.has_bvar_in_range_bvar c args h r h' calls :=
  fun a b d hargs good =>
    SubstAux.gall c.κ .has_bvar_in_range_bvar _ _ _ _ _ ev a b d hargs good.2

theorem has_bvar_in_range_binder_step
    (ev : ObsFn W "KernelSubst::has_bvar_in_range_binder" args h r h' calls) (ih : IH c calls) :
    Specs.Subst.has_bvar_in_range_binder c args h r h' calls :=
  fun a b d e hargs good =>
    SubstAux.gall c.κ .has_bvar_in_range_binder _ _ _ _ _ ev a b d e hargs good.2

theorem has_bvar_in_range_let_step
    (ev : ObsFn W "KernelSubst::has_bvar_in_range_let" args h r h' calls) (ih : IH c calls) :
    Specs.Subst.has_bvar_in_range_let c args h r h' calls :=
  fun a b d e f hargs good =>
    SubstAux.gall c.κ .has_bvar_in_range_let _ _ _ _ _ ev a b d e f hargs good.2

theorem expr_has_bvar_at_step (ev : ObsFn W "KernelSubst::expr_has_bvar_at" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_has_bvar_at c args h r h' calls :=
  fun a b hargs good => SubstAux.gall c.κ .expr_has_bvar_at _ _ _ _ _ ev a b hargs good.2

theorem expr_has_bvar_at_binder_step
    (ev : ObsFn W "KernelSubst::expr_has_bvar_at_binder" args h r h' calls) (ih : IH c calls) :
    Specs.Subst.expr_has_bvar_at_binder c args h r h' calls :=
  fun a b d hargs good =>
    SubstAux.gall c.κ .expr_has_bvar_at_binder _ _ _ _ _ ev a b d hargs good.2

theorem expr_has_bvar_at_let_step
    (ev : ObsFn W "KernelSubst::expr_has_bvar_at_let" args h r h' calls) (ih : IH c calls) :
    Specs.Subst.expr_has_bvar_at_let c args h r h' calls :=
  fun a b d e hargs good =>
    SubstAux.gall c.κ .expr_has_bvar_at_let _ _ _ _ _ ev a b d e hargs good.2

theorem expr_glb_step (ev : ObsFn W "KernelSubst::expr_glb" args h r h' calls) (ih : IH c calls) :
    Specs.Subst.expr_glb c args h r h' calls :=
  fun a b hargs good => SubstAux.gall c.κ .expr_glb _ _ _ _ _ ev a b hargs good.2

theorem expr_glb_walk_step (ev : ObsFn W "KernelSubst::expr_glb_walk" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_glb_walk c args h r h' calls :=
  fun a b hargs good => SubstAux.gall c.κ .expr_glb_walk _ _ _ _ _ ev a b hargs good.2

theorem expr_glb_binder_step (ev : ObsFn W "KernelSubst::expr_glb_binder" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_glb_binder c args h r h' calls :=
  fun a b d hargs good => SubstAux.gall c.κ .expr_glb_binder _ _ _ _ _ ev a b d hargs good.2

theorem expr_glb_let_step (ev : ObsFn W "KernelSubst::expr_glb_let" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_glb_let c args h r h' calls :=
  fun a b d e hargs good => SubstAux.gall c.κ .expr_glb_let _ _ _ _ _ ev a b d e hargs good.2

theorem expr_lift_step (ev : ObsFn W "KernelSubst::expr_lift" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_lift c args h r h' calls :=
  fun a b d hargs good => SubstAux.gall c.κ .expr_lift _ _ _ _ _ ev a b d hargs good.2

theorem expr_lift_walk_step (ev : ObsFn W "KernelSubst::expr_lift_walk" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_lift_walk c args h r h' calls :=
  fun a b d hargs good => SubstAux.gall c.κ .expr_lift_walk _ _ _ _ _ ev a b d hargs good.2

theorem expr_lift_bvar_step (ev : ObsFn W "KernelSubst::expr_lift_bvar" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_lift_bvar c args h r h' calls :=
  fun a b d hargs good => SubstAux.gall c.κ .expr_lift_bvar _ _ _ _ _ ev a b d hargs good.2

theorem expr_lift_let_step (ev : ObsFn W "KernelSubst::expr_lift_let" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_lift_let c args h r h' calls :=
  fun a b d e f hargs good => SubstAux.gall c.κ .expr_lift_let _ _ _ _ _ ev a b d e f hargs good.2

theorem expr_lower_step (ev : ObsFn W "KernelSubst::expr_lower" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_lower c args h r h' calls :=
  fun a b d hargs good => SubstAux.gall c.κ .expr_lower _ _ _ _ _ ev a b d hargs good.2

theorem expr_lower_walk_step (ev : ObsFn W "KernelSubst::expr_lower_walk" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_lower_walk c args h r h' calls :=
  fun a b d hargs good => SubstAux.gall c.κ .expr_lower_walk _ _ _ _ _ ev a b d hargs good.2

theorem expr_lower_let_step (ev : ObsFn W "KernelSubst::expr_lower_let" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_lower_let c args h r h' calls :=
  fun a b d e f hargs good =>
    SubstAux.gall c.κ .expr_lower_let _ _ _ _ _ ev a b d e f hargs good.2

theorem expr_inst1_step (ev : ObsFn W "KernelSubst::expr_inst1" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_inst1 c args h r h' calls :=
  fun a b d hargs good => SubstAux.gall c.κ .expr_inst1 _ _ _ _ _ ev a b d hargs good.2

theorem expr_inst1_walk_step (ev : ObsFn W "KernelSubst::expr_inst1_walk" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_inst1_walk c args h r h' calls :=
  fun a b d hargs good => SubstAux.gall c.κ .expr_inst1_walk _ _ _ _ _ ev a b d hargs good.2

theorem expr_inst1_bvar_step (ev : ObsFn W "KernelSubst::expr_inst1_bvar" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_inst1_bvar c args h r h' calls :=
  fun a b d hargs good => SubstAux.gall c.κ .expr_inst1_bvar _ _ _ _ _ ev a b d hargs good.2

theorem expr_inst1_let_step (ev : ObsFn W "KernelSubst::expr_inst1_let" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_inst1_let c args h r h' calls :=
  fun a b d e f hargs good =>
    SubstAux.gall c.κ .expr_inst1_let _ _ _ _ _ ev a b d e f hargs good.2

theorem expr_inst_many_step (ev : ObsFn W "KernelSubst::expr_inst_many" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_inst_many c args h r h' calls :=
  fun a b d hargs good => SubstAux.gall c.κ .expr_inst_many _ _ _ _ _ ev a b d hargs good.2

theorem expr_inst_many_bvar_step
    (ev : ObsFn W "KernelSubst::expr_inst_many_bvar" args h r h' calls) (ih : IH c calls) :
    Specs.Subst.expr_inst_many_bvar c args h r h' calls :=
  fun a b d hargs good => SubstAux.gall c.κ .expr_inst_many_bvar _ _ _ _ _ ev a b d hargs good.2

theorem expr_inst_many_walk_step
    (ev : ObsFn W "KernelSubst::expr_inst_many_walk" args h r h' calls) (ih : IH c calls) :
    Specs.Subst.expr_inst_many_walk c args h r h' calls :=
  fun a b d hargs good => SubstAux.gall c.κ .expr_inst_many_walk _ _ _ _ _ ev a b d hargs good.2

theorem expr_inst_many_let_step
    (ev : ObsFn W "KernelSubst::expr_inst_many_let" args h r h' calls) (ih : IH c calls) :
    Specs.Subst.expr_inst_many_let c args h r h' calls :=
  fun a b d e f hargs good =>
    SubstAux.gall c.κ .expr_inst_many_let _ _ _ _ _ ev a b d e f hargs good.2

theorem ctx_trim_step (ev : ObsFn W "KernelSubst::ctx_trim" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.ctx_trim c args h r h' calls :=
  fun a b hargs good => SubstAux.gall c.κ .ctx_trim _ _ _ _ _ ev a b hargs good.2

theorem ctx_reachable_step (ev : ObsFn W "KernelSubst::ctx_reachable" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.ctx_reachable c args h r h' calls :=
  fun a b hargs good => SubstAux.gall c.κ .ctx_reachable _ _ _ _ _ ev a b hargs good.2

theorem ctx_seek_cut_step (ev : ObsFn W "KernelSubst::ctx_seek_cut" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.ctx_seek_cut c args h r h' calls :=
  fun a b hargs good => SubstAux.gall c.κ .ctx_seek_cut _ _ _ _ _ ev a b hargs good.2

theorem ctx_next_cut_step (ev : ObsFn W "KernelSubst::ctx_next_cut" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.ctx_next_cut c args h r h' calls :=
  fun a hargs good => SubstAux.gall c.κ .ctx_next_cut _ _ _ _ _ ev a hargs good.2

theorem ctx_close_cut_step (ev : ObsFn W "KernelSubst::ctx_close_cut" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.ctx_close_cut c args h r h' calls :=
  fun a b hargs good => SubstAux.gall c.κ .ctx_close_cut _ _ _ _ _ ev a b hargs good.2

theorem collect_spine_step (ev : ObsFn W "KernelTypes::collect_spine" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.collect_spine c args h r h' calls :=
  fun a hargs good => SubstAux.gall c.κ .collect_spine _ _ _ _ _ ev a hargs good.2

theorem expr_inst_levels_step (ev : ObsFn W "KernelLevels::expr_inst_levels" args h r h' calls)
    (ih : IH c calls) : Specs.Subst.expr_inst_levels c args h r h' calls :=
  fun a b hargs good => SubstAux.gall c.κ .expr_inst_levels _ _ _ _ _ ev a b hargs good.2

theorem expr_inst_levels_walk_step
    (ev : ObsFn W "KernelLevels::expr_inst_levels_walk" args h r h' calls) (ih : IH c calls) :
    Specs.Subst.expr_inst_levels_walk c args h r h' calls :=
  fun a b hargs good => SubstAux.gall c.κ .expr_inst_levels_walk _ _ _ _ _ ev a b hargs good.2

end Steps

/-- **The substitution family's part of the registry harness** (`Steps c` at `.subst f`). -/
theorem subst_step (c : Ctx) :
    ∀ (f : Specs.Subst.Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W (Fn.subst f).name args h r h' cs → IH c cs →
      (Fn.subst f).spec c args h r h' cs
  | .expr_lbr, _, _, _, _, _, ev, ih => expr_lbr_step c ev ih
  | .expr_lbr_let, _, _, _, _, _, ev, ih => expr_lbr_let_step c ev ih
  | .lbr_max, _, _, _, _, _, ev, ih => lbr_max_step c ev ih
  | .lbr_dec, _, _, _, _, _, ev, ih => lbr_dec_step c ev ih
  | .lbr_min, _, _, _, _, _, ev, ih => lbr_min_step c ev ih
  | .has_bvar_in_range, _, _, _, _, _, ev, ih => has_bvar_in_range_step c ev ih
  | .has_bvar_in_range_bvar, _, _, _, _, _, ev, ih => has_bvar_in_range_bvar_step c ev ih
  | .has_bvar_in_range_binder, _, _, _, _, _, ev, ih => has_bvar_in_range_binder_step c ev ih
  | .has_bvar_in_range_let, _, _, _, _, _, ev, ih => has_bvar_in_range_let_step c ev ih
  | .expr_has_bvar_at, _, _, _, _, _, ev, ih => expr_has_bvar_at_step c ev ih
  | .expr_has_bvar_at_binder, _, _, _, _, _, ev, ih => expr_has_bvar_at_binder_step c ev ih
  | .expr_has_bvar_at_let, _, _, _, _, _, ev, ih => expr_has_bvar_at_let_step c ev ih
  | .expr_glb, _, _, _, _, _, ev, ih => expr_glb_step c ev ih
  | .expr_glb_walk, _, _, _, _, _, ev, ih => expr_glb_walk_step c ev ih
  | .expr_glb_binder, _, _, _, _, _, ev, ih => expr_glb_binder_step c ev ih
  | .expr_glb_let, _, _, _, _, _, ev, ih => expr_glb_let_step c ev ih
  | .expr_lift, _, _, _, _, _, ev, ih => expr_lift_step c ev ih
  | .expr_lift_walk, _, _, _, _, _, ev, ih => expr_lift_walk_step c ev ih
  | .expr_lift_bvar, _, _, _, _, _, ev, ih => expr_lift_bvar_step c ev ih
  | .expr_lift_let, _, _, _, _, _, ev, ih => expr_lift_let_step c ev ih
  | .expr_lower, _, _, _, _, _, ev, ih => expr_lower_step c ev ih
  | .expr_lower_walk, _, _, _, _, _, ev, ih => expr_lower_walk_step c ev ih
  | .expr_lower_let, _, _, _, _, _, ev, ih => expr_lower_let_step c ev ih
  | .expr_inst1, _, _, _, _, _, ev, ih => expr_inst1_step c ev ih
  | .expr_inst1_walk, _, _, _, _, _, ev, ih => expr_inst1_walk_step c ev ih
  | .expr_inst1_bvar, _, _, _, _, _, ev, ih => expr_inst1_bvar_step c ev ih
  | .expr_inst1_let, _, _, _, _, _, ev, ih => expr_inst1_let_step c ev ih
  | .expr_inst_many, _, _, _, _, _, ev, ih => expr_inst_many_step c ev ih
  | .expr_inst_many_bvar, _, _, _, _, _, ev, ih => expr_inst_many_bvar_step c ev ih
  | .expr_inst_many_walk, _, _, _, _, _, ev, ih => expr_inst_many_walk_step c ev ih
  | .expr_inst_many_let, _, _, _, _, _, ev, ih => expr_inst_many_let_step c ev ih
  | .ctx_trim, _, _, _, _, _, ev, ih => ctx_trim_step c ev ih
  | .ctx_reachable, _, _, _, _, _, ev, ih => ctx_reachable_step c ev ih
  | .ctx_seek_cut, _, _, _, _, _, ev, ih => ctx_seek_cut_step c ev ih
  | .ctx_next_cut, _, _, _, _, _, ev, ih => ctx_next_cut_step c ev ih
  | .ctx_close_cut, _, _, _, _, _, ev, ih => ctx_close_cut_step c ev ih
  | .collect_spine, _, _, _, _, _, ev, ih => collect_spine_step c ev ih
  | .expr_inst_levels, _, _, _, _, _, ev, ih => expr_inst_levels_step c ev ih
  | .expr_inst_levels_walk, _, _, _, _, _, ev, ih => expr_inst_levels_walk_step c ev ih

/-! ## `Terms S₀` -/

/-- **Obligation L3's content at `S₀`**: instantiating a binder body at depth `0`, and lifting
a top-level term by one opened variable, are the kernel's operations on the images, for every
ghost, with the derivation's ROM bound. -/
theorem terms_S₀ : IxVM.Consistency.Terms S₀ := by
  refine ⟨?_, ?_⟩
  · intro E env g n e arg r heap after cs tb ta ev bd he ha
    have := SubstAux.gall (Ghost.κ g) .expr_inst1 _ _ _ _ _ ev e arg 0 rfl bd n (Ghost.Γ g) tb ta
      (by rw [ZMod.val_zero]; exact he) ha
    rw [ZMod.val_zero] at this
    exact this
  · intro E env g n e r heap after cs t ev bd he
    have := SubstAux.gall (Ghost.κ g) .expr_lift _ _ _ _ _ ev e 1 0 rfl bd
      (by rw [SubstAux.val_one]; decide) 0 1 (by simp [SubstAux.val_one]) n (Ghost.Γ g) t
      (by rw [ZMod.val_zero]; exact he)
    rw [ZMod.val_zero] at this
    exact this

/-- **Obligation L3 at `S₀`.** -/
theorem l3_S₀ : IxVM.Consistency.L3 S₀ := fun _ => terms_S₀

end IxVM.Refinement.Core
