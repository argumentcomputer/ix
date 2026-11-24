import IxVMRefinement.Binding.FamilyReconZeta
import IxVMRefinement.Lib.Words
import IxVMRefinement.Core.RomBound
import IxVM.Obs.KernelCheck

/-! # The reconstruction's bound-variable builders and parameter substitutions on `TmOExact`

The functions of the reconstruction (`KernelCheck::build_rec_type`, `populate_rules`) that apply a
head to a run of bound variables, lift or peel lists of terms, count leading `Forall` binders, and
instantiate a type's parameters, each read as the model's function (`FamilyReconModel`) on open
exact terms (`TmOExact`) without any no-let premise:

* Field arithmetic on small naturals; `tmOExact_app_bvar`, `bvar_loop`;
* `build_apply_bvars_decreasing_spec`, `build_motive_apps_spec`, `build_minor_apps_spec`
  (`appBVarsDec`), `build_major_indices_spec`, `build_apply_xs_spec` (`appBVarsDown`),
  `build_major_params_spec` (`majorParams`), `apply_indices_in_conclusion_spec`
  (`conclIndices`), `build_apply_field_bvars_spec` (`fieldBVars`);
* `list_lift_indices_spec` (`liftIndices`), `apply_spec_params_lifted_spec`
  (`specParamsLifted`), `peel_leading_foralls_acc_spec`, `peel_leading_foralls_spec` (`peelAll`),
  `count_foralls_body_spec`;
* `subst_param_for_spec` (`substParamFor`), `ctor_subst_param_for_spec` (`ctorSubstParamFor`),
  `peel_motive_params_subst_spec` (`peelMotiveParams`). -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core (KExpr KLevel KKey kexprEnum kexprListEnum)
open IxVM.Refinement.Decl (TmExact)
open IxVM (F)

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Field arithmetic on small naturals -/

theorem fval_natCast {n : Nat} (hn : n < 18446744069414584321) : ZMod.val (n : F) = n :=
  ZMod.val_natCast_of_lt hn

theorem natCast_inj_small {a b : Nat} (ha : a < 18446744069414584321)
    (hb : b < 18446744069414584321) (h : (a : F) = (b : F)) : a = b := by
  have := congrArg ZMod.val h
  rwa [fval_natCast ha, fval_natCast hb] at this

theorem binop_sub_eq_zero_nat {a b : Nat} (ha : a < 18446744069414584321)
    (hb : b < 18446744069414584321)
    (op : evalBinOp .sub (.field (a : F) : SourceValue F) (.field (b : F)) = .ok (.field 0)) :
    a = b := by
  simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op
  exact natCast_inj_small ha hb (sub_eq_zero.mp op)

theorem binop_sub_ne_nat {a b : Nat} {v : SourceValue F}
    (op : evalBinOp .sub (.field (a : F) : SourceValue F) (.field (b : F)) = .ok v)
    (hne : v ≠ .field 0) : a ≠ b := by
  rintro rfl
  apply hne
  simp only [evalBinOp, Except.ok.injEq] at op
  rw [← op, sub_self]

theorem binop_sub_nat {a b : Nat} (hle : b ≤ a) {v : SourceValue F}
    (op : evalBinOp .sub (.field (a : F) : SourceValue F) (.field (b : F)) = .ok v) :
    v = .field (((a - b : Nat) : F)) := by
  simp only [evalBinOp] at op
  injection op with hv
  rw [← hv]
  simp [Nat.cast_sub hle]

theorem binop_sub_one_nat {a : Nat} (ha : 1 ≤ a) {v : SourceValue F}
    (op : evalBinOp .sub (.field (a : F) : SourceValue F) (.field 1) = .ok v) :
    v = .field (((a - 1 : Nat) : F)) := by
  simp only [evalBinOp] at op
  injection op with hv
  rw [← hv]
  simp [Nat.cast_sub ha]

theorem binop_add_nat {a b : Nat} {v : SourceValue F}
    (op : evalBinOp .add (.field (a : F) : SourceValue F) (.field (b : F)) = .ok v) :
    v = .field (((a + b : Nat) : F)) := by
  simp only [evalBinOp] at op
  injection op with hv
  rw [← hv]
  simp [Nat.cast_add]

theorem binop_add_one_nat {a : Nat} {v : SourceValue F}
    (op : evalBinOp .add (.field (a : F) : SourceValue F) (.field 1) = .ok v) :
    v = .field (((a + 1 : Nat) : F)) := by
  simp only [evalBinOp] at op
  injection op with hv
  rw [← hv]
  simp [Nat.cast_add]

theorem field_natCast_ne_zero {a : Nat} (ha : a < 18446744069414584321)
    (h : (.field (a : F) : SourceValue F) ≠ .field 0) : a ≠ 0 := by
  rintro rfl
  exact h (by simp)

theorem field_natCast_eq_zero {a : Nat} (ha : a < 18446744069414584321)
    (h : (.field (a : F) : SourceValue F) = .field 0) : a = 0 := by
  have h' : (a : F) = ((0 : Nat) : F) := by
    simpa using Value.field.inj h
  exact natCast_inj_small ha (by decide) h'

/-! ## The Boolean flag of a flat entry -/

/-- **A flag `is_aux`** as the circuit holds it: `1` for an auxiliary, `0` for a type of the
block. -/
abbrev auxVal (aux : Bool) : SourceValue F := .field (if aux then 1 else 0)

theorem auxVal_eq_zero {aux : Bool} : auxVal aux = .field 0 ↔ aux = false := by
  cases aux <;> simp [auxVal]

theorem auxVal_eq_one {aux : Bool} : auxVal aux = .field 1 ↔ aux = true := by
  cases aux <;> simp [auxVal]

/-! ## Lists of terms -/

theorem kexpr_length {R : Heap F → KExpr → SourceValue F → Prop} {xs : List KExpr}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) : r = .field (xs.length : F) ∧ h' = h :=
  Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := R)
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)

theorem kexpr_lookup {R : Heap F → KExpr → SourceValue F → Prop} {xs : List KExpr}
    {l r : SourceValue F} {i : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [l, .field i] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) : (∃ x, xs[i.val]? = some x ∧ R h x r) ∧ h' = h :=
  Lib.Lists.lookup_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := R)
    (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)

/-! ## A counter loop applying bound variables -/

/-- **One step of a bound-variable builder**: a `BVar b` cell, then an `App` cell applying the
head to it. -/
theorem tmOExact_app_bvar {κ : _root_.Address → KKey} {h : Heap F} {H : KExpr} {xh : SourceValue F}
    {b : Nat} (hb : b < 9223372036854775808) (hH : TmOExact κ h H xh) :
    TmOExact κ ((h ++ [.construct kexprEnum "BVar" [.field (b : F)]]) ++
        [.construct kexprEnum "App" [xh, .ptr (.enum kexprEnum) h.length]])
      (.app H (.bvar b))
      (.ptr (.enum kexprEnum)
        (h ++ [(.construct kexprEnum "BVar" [.field (b : F)] : SourceValue F)]).length) := by
  obtain ⟨k, rH⟩ := hH
  have hval : ZMod.val (b : F) = b := fval_natCast (Nat.lt_trans hb (by decide))
  have ext : Heap.Extends h ((h ++ [.construct kexprEnum "BVar" [.field (b : F)]]) ++
      [.construct kexprEnum "App" [xh, .ptr (.enum kexprEnum) h.length]]) :=
    Heap.Extends.trans (Heap.Extends.snoc _ _) (Heap.Extends.snoc _ _)
  have rb : TmExact κ 0 ghost0 ((h ++ [.construct kexprEnum "BVar" [.field (b : F)]]) ++
      [.construct kexprEnum "App" [xh, .ptr (.enum kexprEnum) h.length]]) (max k (b + 1))
      (.bvar (ZMod.val (b : F))) (.ptr (.enum kexprEnum) h.length) :=
    .bvarLocal (by simp) (by rw [hval]; exact hb) (by rw [hval]; omega)
  rw [hval] at rb
  exact ⟨max k (b + 1), .app (by simp)
    (tmExact_depth_le (rH.mono ext) _ (Nat.le_max_left _ _)) rb⟩

/-- **A bound-variable builder's loop** on `TmOExact`. -/
theorem bvar_loop {κ : _root_.Address → KKey} {n : Nat} {g : Nat → Nat}
    (hg : ∀ j, j < n → g j < 9223372036854775808)
    {P : Nat → SourceValue F → Heap F → SourceValue F → Heap F → Prop}
    (run : ∀ {i : Nat} {xh : SourceValue F} {h : Heap F} {r : SourceValue F} {h' : Heap F},
      i ≤ n → P i xh h r h' →
      (i = n ∧ r = xh ∧ h' = h) ∨
      (i < n ∧ P (i + 1)
        (.ptr (.enum kexprEnum)
          (h ++ [(.construct kexprEnum "BVar" [.field (g i : F)] : SourceValue F)]).length)
        ((h ++ [.construct kexprEnum "BVar" [.field (g i : F)]]) ++
          [.construct kexprEnum "App" [xh, .ptr (.enum kexprEnum) h.length]]) r h')) :
    ∀ c i, n - i = c → i ≤ n → ∀ {xh : SourceValue F} {h : Heap F} {r : SourceValue F}
      {h' : Heap F} {H : KExpr}, P i xh h r h' → TmOExact κ h H xh →
      TmOExact κ h' (appSpine H ((List.range' i (n - i)).map fun j => .bvar (g j))) r := by
  intro c
  induction c with
  | zero =>
    intro i hc hi xh h r h' H hP hH
    rcases run hi hP with ⟨rfl, rfl, rfl⟩ | ⟨hlt, -⟩
    · simpa [appSpine] using hH
    · omega
  | succ c ih =>
    intro i hc hi xh h r h' H hP hH
    rcases run hi hP with ⟨rfl, -, -⟩ | ⟨hlt, hP'⟩
    · omega
    · have hstep := ih (i + 1) (by omega) (by omega) hP' (tmOExact_app_bvar (hg i hlt) hH)
      have hr : List.range' i (n - i) = i :: List.range' (i + 1) (n - (i + 1)) := by
        rw [show n - i = (n - (i + 1)) + 1 by omega, List.range'_succ]
      rw [hr]
      exact hstep

/-- The loop's conclusion from counter `0`, over `List.range n`. -/
theorem bvar_loop_zero {κ : _root_.Address → KKey} {n : Nat} {g : Nat → Nat}
    (hg : ∀ j, j < n → g j < 9223372036854775808)
    {P : Nat → SourceValue F → Heap F → SourceValue F → Heap F → Prop}
    (run : ∀ {i : Nat} {xh : SourceValue F} {h : Heap F} {r : SourceValue F} {h' : Heap F},
      i ≤ n → P i xh h r h' →
      (i = n ∧ r = xh ∧ h' = h) ∨
      (i < n ∧ P (i + 1)
        (.ptr (.enum kexprEnum)
          (h ++ [(.construct kexprEnum "BVar" [.field (g i : F)] : SourceValue F)]).length)
        ((h ++ [.construct kexprEnum "BVar" [.field (g i : F)]]) ++
          [.construct kexprEnum "App" [xh, .ptr (.enum kexprEnum) h.length]]) r h'))
    {xh : SourceValue F} {h : Heap F} {r : SourceValue F} {h' : Heap F} {H : KExpr}
    (hP : P 0 xh h r h') (hH : TmOExact κ h H xh) :
    TmOExact κ h' (appSpine H ((List.range n).map fun j => .bvar (g j))) r := by
  have := bvar_loop (κ := κ) hg run (n - 0) 0 rfl (Nat.zero_le _) hP hH
  rwa [Nat.sub_zero, ← List.range_eq_range'] at this

/-! ## The builders -/

section Builders

variable {κ : _root_.Address → KKey}

/-- **`KernelCheck::build_apply_bvars_decreasing(head, n, start, 0)`** is `appBVarsDec`. -/
theorem build_apply_bvars_decreasing_spec {n start : Nat} (hn : n < 9223372036854775808)
    (hs : start < 9223372036854775808) (hns : n ≤ start + 1) {xh r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} {H : KExpr}
    (ev : ObsFn Obs.W "KernelCheck::build_apply_bvars_decreasing"
      [xh, .field (n : F), .field (start : F), .field 0] h r h' cs)
    (hH : TmOExact κ h H xh) : TmOExact κ h' (appBVarsDec H n start) r := by
  refine bvar_loop_zero (κ := κ) (n := n) (g := fun j => start - j)
    (P := fun i xh h r h' => ∃ cs, ObsFn Obs.W "KernelCheck::build_apply_bvars_decreasing"
      [xh, .field (n : F), .field (start : F), .field (i : F)] h r h' cs)
    (fun j hj => by omega) ?_ ⟨cs, by rw [Nat.cast_zero]; exact ev⟩ hH
  intro i xh h r h' hi ⟨cs, ev⟩
  rcases Obs.«KernelCheck::build_apply_bvars_decreasing».obs ev with
    ⟨op17, rfl, rfl, -⟩ |
    ⟨v1, m33, v47, cs67, v73, m75, op17, hne28, hm43, op61, hm83, op130, ev69, -⟩
  · exact .inl ⟨(binop_sub_eq_zero_nat (by omega) (by omega) op17).symm, rfl, rfl⟩
  · have hlt : i < n := by have := binop_sub_ne_nat op17 hne28; omega
    obtain rfl := binop_sub_nat (by omega) op61
    obtain rfl := binop_add_one_nat op130
    subst hm43 hm83
    exact .inr ⟨hlt, cs67, ev69⟩

/-- **`KernelCheck::build_motive_apps(head, n, start, 0)`** is `appBVarsDec`. -/
theorem build_motive_apps_spec {n start : Nat} (hn : n < 9223372036854775808)
    (hs : start < 9223372036854775808) (hns : n ≤ start + 1) {xh r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} {H : KExpr}
    (ev : ObsFn Obs.W "KernelCheck::build_motive_apps"
      [xh, .field (n : F), .field (start : F), .field 0] h r h' cs)
    (hH : TmOExact κ h H xh) : TmOExact κ h' (appBVarsDec H n start) r := by
  refine bvar_loop_zero (κ := κ) (n := n) (g := fun j => start - j)
    (P := fun i xh h r h' => ∃ cs, ObsFn Obs.W "KernelCheck::build_motive_apps"
      [xh, .field (n : F), .field (start : F), .field (i : F)] h r h' cs)
    (fun j hj => by omega) ?_ ⟨cs, by rw [Nat.cast_zero]; exact ev⟩ hH
  intro i xh h r h' hi ⟨cs, ev⟩
  rcases Obs.«KernelCheck::build_motive_apps».obs ev with
    ⟨op17, rfl, rfl, -⟩ |
    ⟨v1, m33, v47, cs67, v73, m75, op17, hne28, hm43, op61, hm83, op130, ev69, -⟩
  · exact .inl ⟨(binop_sub_eq_zero_nat (by omega) (by omega) op17).symm, rfl, rfl⟩
  · have hlt : i < n := by have := binop_sub_ne_nat op17 hne28; omega
    obtain rfl := binop_sub_nat (by omega) op61
    obtain rfl := binop_add_one_nat op130
    subst hm43 hm83
    exact .inr ⟨hlt, cs67, ev69⟩

/-- **`KernelCheck::build_minor_apps(head, n, start, 0)`** is `appBVarsDec`. -/
theorem build_minor_apps_spec {n start : Nat} (hn : n < 9223372036854775808)
    (hs : start < 9223372036854775808) (hns : n ≤ start + 1) {xh r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} {H : KExpr}
    (ev : ObsFn Obs.W "KernelCheck::build_minor_apps"
      [xh, .field (n : F), .field (start : F), .field 0] h r h' cs)
    (hH : TmOExact κ h H xh) : TmOExact κ h' (appBVarsDec H n start) r := by
  refine bvar_loop_zero (κ := κ) (n := n) (g := fun j => start - j)
    (P := fun i xh h r h' => ∃ cs, ObsFn Obs.W "KernelCheck::build_minor_apps"
      [xh, .field (n : F), .field (start : F), .field (i : F)] h r h' cs)
    (fun j hj => by omega) ?_ ⟨cs, by rw [Nat.cast_zero]; exact ev⟩ hH
  intro i xh h r h' hi ⟨cs, ev⟩
  rcases Obs.«KernelCheck::build_minor_apps».obs ev with
    ⟨op17, rfl, rfl, -⟩ |
    ⟨v1, m33, v47, cs67, v73, m75, op17, hne28, hm43, op61, hm83, op130, ev69, -⟩
  · exact .inl ⟨(binop_sub_eq_zero_nat (by omega) (by omega) op17).symm, rfl, rfl⟩
  · have hlt : i < n := by have := binop_sub_ne_nat op17 hne28; omega
    obtain rfl := binop_sub_nat (by omega) op61
    obtain rfl := binop_add_one_nat op130
    subst hm43 hm83
    exact .inr ⟨hlt, cs67, ev69⟩

/-- **`KernelCheck::build_major_indices(head, n, 0)`** is `appBVarsDown`. -/
theorem build_major_indices_spec {n : Nat} (hn : n < 9223372036854775808) {xh r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} {H : KExpr}
    (ev : ObsFn Obs.W "KernelCheck::build_major_indices" [xh, .field (n : F), .field 0] h r h' cs)
    (hH : TmOExact κ h H xh) : TmOExact κ h' (appBVarsDown H n) r := by
  refine bvar_loop_zero (κ := κ) (n := n) (g := fun j => n - 1 - j)
    (P := fun i xh h r h' => ∃ cs, ObsFn Obs.W "KernelCheck::build_major_indices"
      [xh, .field (n : F), .field (i : F)] h r h' cs)
    (fun j hj => by omega) ?_ ⟨cs, by rw [Nat.cast_zero]; exact ev⟩ hH
  intro i xh h r h' hi ⟨cs, ev⟩
  rcases Obs.«KernelCheck::build_major_indices».obs ev with
    ⟨op17, rfl, rfl, -⟩ |
    ⟨v1, m33, v47, x54, cs75, v80, m82, op17, hne28, hm43, op69, op61, hm90, op130, ev77, -⟩
  · exact .inl ⟨(binop_sub_eq_zero_nat (by omega) (by omega) op17).symm, rfl, rfl⟩
  · have hlt : i < n := by have := binop_sub_ne_nat op17 hne28; omega
    obtain rfl := binop_sub_one_nat (by omega) op69
    obtain rfl := binop_sub_nat (by omega) op61
    obtain rfl := binop_add_one_nat op130
    subst hm43 hm90
    exact .inr ⟨hlt, cs75, ev77⟩

/-- **`KernelCheck::build_apply_xs(head, n, 0)`** is `appBVarsDown`. -/
theorem build_apply_xs_spec {n : Nat} (hn : n < 9223372036854775808) {xh r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} {H : KExpr}
    (ev : ObsFn Obs.W "KernelCheck::build_apply_xs" [xh, .field (n : F), .field 0] h r h' cs)
    (hH : TmOExact κ h H xh) : TmOExact κ h' (appBVarsDown H n) r := by
  refine bvar_loop_zero (κ := κ) (n := n) (g := fun j => n - 1 - j)
    (P := fun i xh h r h' => ∃ cs, ObsFn Obs.W "KernelCheck::build_apply_xs"
      [xh, .field (n : F), .field (i : F)] h r h' cs)
    (fun j hj => by omega) ?_ ⟨cs, by rw [Nat.cast_zero]; exact ev⟩ hH
  intro i xh h r h' hi ⟨cs, ev⟩
  rcases Obs.«KernelCheck::build_apply_xs».obs ev with
    ⟨op17, rfl, rfl, -⟩ |
    ⟨v1, m33, v47, x54, cs75, v80, m82, op17, hne28, hm43, op69, op61, hm90, op130, ev77, -⟩
  · exact .inl ⟨(binop_sub_eq_zero_nat (by omega) (by omega) op17).symm, rfl, rfl⟩
  · have hlt : i < n := by have := binop_sub_ne_nat op17 hne28; omega
    obtain rfl := binop_sub_one_nat (by omega) op69
    obtain rfl := binop_sub_nat (by omega) op61
    obtain rfl := binop_add_one_nat op130
    subst hm43 hm90
    exact .inr ⟨hlt, cs75, ev77⟩

/-- **`KernelCheck::build_major_params(head, n, depth, 0)`** is `majorParams`. -/
theorem build_major_params_spec {n depth : Nat} (hnd : n + depth < 9223372036854775808)
    {xh r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {H : KExpr}
    (ev : ObsFn Obs.W "KernelCheck::build_major_params"
      [xh, .field (n : F), .field (depth : F), .field 0] h r h' cs)
    (hH : TmOExact κ h H xh) : TmOExact κ h' (majorParams H n depth) r := by
  refine bvar_loop_zero (κ := κ) (n := n) (g := fun j => n - 1 - j + depth)
    (P := fun i xh h r h' => ∃ cs, ObsFn Obs.W "KernelCheck::build_major_params"
      [xh, .field (n : F), .field (depth : F), .field (i : F)] h r h' cs)
    (fun j hj => by omega) ?_ ⟨cs, by rw [Nat.cast_zero]; exact ev⟩ hH
  intro i xh h r h' hi ⟨cs, ev⟩
  rcases Obs.«KernelCheck::build_major_params».obs ev with
    ⟨op17, rfl, rfl, -⟩ |
    ⟨v1, m33, v47, x54, x62, cs84, v90, m92, op17, hne28, hm43, op77, op69, op61, hm100, op147,
      ev86, -⟩
  · exact .inl ⟨(binop_sub_eq_zero_nat (by omega) (by omega) op17).symm, rfl, rfl⟩
  · have hlt : i < n := by have := binop_sub_ne_nat op17 hne28; omega
    obtain rfl := binop_sub_one_nat (by omega) op77
    obtain rfl := binop_sub_nat (by omega) op69
    obtain rfl := binop_add_nat op61
    obtain rfl := binop_add_one_nat op147
    subst hm43 hm100
    exact .inr ⟨hlt, cs84, ev86⟩

/-- **`KernelCheck::apply_indices_in_conclusion(head, n, 0)`** is `conclIndices`. -/
theorem apply_indices_in_conclusion_spec {n : Nat} (hn : n < 9223372036854775808)
    {xh r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {H : KExpr}
    (ev : ObsFn Obs.W "KernelCheck::apply_indices_in_conclusion"
      [xh, .field (n : F), .field 0] h r h' cs)
    (hH : TmOExact κ h H xh) : TmOExact κ h' (conclIndices H n) r := by
  refine bvar_loop_zero (κ := κ) (n := n) (g := fun j => n - j)
    (P := fun i xh h r h' => ∃ cs, ObsFn Obs.W "KernelCheck::apply_indices_in_conclusion"
      [xh, .field (n : F), .field (i : F)] h r h' cs)
    (fun j hj => by omega) ?_ ⟨cs, by rw [Nat.cast_zero]; exact ev⟩ hH
  intro i xh h r h' hi ⟨cs, ev⟩
  rcases Obs.«KernelCheck::apply_indices_in_conclusion».obs ev with
    ⟨op17, rfl, rfl, -⟩ |
    ⟨v1, m33, v47, cs67, v72, m74, op17, hne28, hm43, op61, hm82, op122, ev69, -⟩
  · exact .inl ⟨(binop_sub_eq_zero_nat (by omega) (by omega) op17).symm, rfl, rfl⟩
  · have hlt : i < n := by have := binop_sub_ne_nat op17 hne28; omega
    obtain rfl := binop_sub_nat (by omega) op61
    obtain rfl := binop_add_one_nat op122
    subst hm43 hm82
    exact .inr ⟨hlt, cs67, ev69⟩

/-- **`KernelCheck::build_apply_field_bvars(head, nf, nb, 0)`** is `fieldBVars`. -/
theorem build_apply_field_bvars_spec {nf nb : Nat} (hnb : nb < 9223372036854775808)
    (hfb : nf ≤ nb) {xh r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {H : KExpr}
    (ev : ObsFn Obs.W "KernelCheck::build_apply_field_bvars"
      [xh, .field (nf : F), .field (nb : F), .field 0] h r h' cs)
    (hH : TmOExact κ h H xh) : TmOExact κ h' (fieldBVars H nf nb) r := by
  refine bvar_loop_zero (κ := κ) (n := nf) (g := fun j => nb - 1 - j)
    (P := fun i xh h r h' => ∃ cs, ObsFn Obs.W "KernelCheck::build_apply_field_bvars"
      [xh, .field (nf : F), .field (nb : F), .field (i : F)] h r h' cs)
    (fun j hj => by omega) ?_ ⟨cs, by rw [Nat.cast_zero]; exact ev⟩ hH
  intro i xh h r h' hi ⟨cs, ev⟩
  rcases Obs.«KernelCheck::build_apply_field_bvars».obs ev with
    ⟨op17, rfl, rfl, -⟩ |
    ⟨v1, m33, v47, x54, cs75, v81, m83, op17, hne28, hm43, op69, op61, hm91, op138, ev77, -⟩
  · exact .inl ⟨(binop_sub_eq_zero_nat (by omega) (by omega) op17).symm, rfl, rfl⟩
  · have hlt : i < nf := by have := binop_sub_ne_nat op17 hne28; omega
    obtain rfl := binop_sub_one_nat (by omega) op69
    obtain rfl := binop_sub_nat (by omega) op61
    obtain rfl := binop_add_one_nat op138
    subst hm43 hm91
    exact .inr ⟨hlt, cs75, ev77⟩

end Builders

/-! ## Lifting and peeling lists -/

section Lists

variable {κ : _root_.Address → KKey}

/-- **`KernelCheck::list_lift_indices(doms, shift, i)`** lifts the `j`-th term by `shift` at the
cutoff `i + j`; from `i = 0` it is `liftIndices`. -/
theorem list_lift_indices_spec {shift : Nat} (hs : shift < 4611686018427387904) :
    ∀ (Ds : List KExpr) (i : Nat), i + Ds.length < 4611686018427387904 →
      ∀ {xds r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn Obs.W "KernelCheck::list_lift_indices" [xds, .field (shift : F), .field (i : F)] h r h'
        cs → IxVM.Consistency.Bounded cs → RepList kexprListEnum (TmOExact κ) h Ds xds →
      RepList kexprListEnum (TmOExact κ) h'
        ((Ds.zipIdx i).map fun p => p.1.liftLooseBVars shift p.2) r := by
  intro Ds
  induction Ds with
  | nil =>
    intro i hi xds r h h' cs ev hbnd hD
    rcases Obs.«KernelCheck::list_lift_indices».obs ev with
      ⟨ld12, rfl, rfl, -⟩ | ⟨x_d, x_rest, v54, v55, m57, cs65, m93, cs101, v106, ld12, -⟩
    · exact Lib.rep_store_nil h
    · obtain ⟨z, zs, hzs, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hD ld12
      cases hzs
  | cons D Ds ih =>
    intro i hi xds r h h' cs ev hbnd hD
    rcases Obs.«KernelCheck::list_lift_indices».obs ev with
      ⟨ld12, -, -, -⟩ |
      ⟨x_d, x_rest, v54, v55, m57, cs65, m93, cs101, v106, ld12, rfl, rfl, ev67, op134, ev103,
        hc136⟩
    · cases IxVM.Refinement.Core.RepList.nil_of_load hD ld12
    · obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hD ld12
      injection hzs with hz1 hz2
      subst hz1 hz2
      obtain rfl := binop_add_one_nat op134
      simp only [List.length_cons] at hi
      have b1 : IxVM.Consistency.Bounded cs65 :=
        RomBound.bounded_mono hbnd (fun c hc => by rw [hc136]; simp [hc])
      have b2 : IxVM.Consistency.Bounded cs101 :=
        RomBound.bounded_mono hbnd (fun c hc => by rw [hc136]; simp [hc])
      have hd := expr_lift_tmOExact hs (by omega) b1 hz ev67
      have ext1 : Heap.Extends h m57 := ObsFn.heap_extends ev67
      have hrest := ih (i + 1) (by omega) ev103 b2 (tmOExactList_mono ext1 hzs')
      have ext2 : Heap.Extends m57 m93 := ObsFn.heap_extends ev103
      have := Lib.rep_store_cons tmOExact_heapMono₂ (TmOExact.mono ext2 hd) hrest
      simpa [List.zipIdx_cons] using this

/-- **`KernelCheck::apply_spec_params_lifted(head, ps, depth)`** is `specParamsLifted`. -/
theorem apply_spec_params_lifted_spec {depth : Nat} (hd : depth < 4611686018427387904) :
    ∀ (Ps : List KExpr) {xh xps r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
      {H : KExpr},
      ObsFn Obs.W "KernelCheck::apply_spec_params_lifted" [xh, xps, .field (depth : F)] h r h'
        cs → IxVM.Consistency.Bounded cs → TmOExact κ h H xh →
      RepList kexprListEnum (TmOExact κ) h Ps xps →
      TmOExact κ h' (specParamsLifted H Ps depth) r := by
  intro Ps
  induction Ps with
  | nil =>
    intro xh xps r h h' cs H ev hbnd hH hP
    rcases Obs.«KernelCheck::apply_spec_params_lifted».obs ev with
      ⟨ld12, rfl, rfl, -⟩ | ⟨x_sp, x_rest, v41, m42, cs52, cs81, m88, ld12, -⟩
    · exact hH
    · obtain ⟨z, zs, hzs, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hP ld12
      cases hzs
  | cons P Ps ih =>
    intro xh xps r h h' cs H ev hbnd hH hP
    rcases Obs.«KernelCheck::apply_spec_params_lifted».obs ev with
      ⟨ld12, -, -, -⟩ | ⟨x_sp, x_rest, v41, m42, cs52, cs81, m88, ld12, ev54, hm96, ev83, hc130⟩
    · cases IxVM.Refinement.Core.RepList.nil_of_load hP ld12
    · obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hP ld12
      injection hzs with hz1 hz2
      rw [← hz1] at hz
      rw [← hz2] at hzs'
      subst hm96
      have b1 : IxVM.Consistency.Bounded cs52 :=
        RomBound.bounded_mono hbnd (fun c hc => by rw [hc130]; simp [hc])
      have b2 : IxVM.Consistency.Bounded cs81 :=
        RomBound.bounded_mono hbnd (fun c hc => by rw [hc130]; simp [hc])
      have ev54' : ObsFn Obs.W "KernelSubst::expr_lift"
          [x_sp, .field (depth : F), .field ((0 : Nat) : F)] h v41 m42 cs52 := by
        simpa using ev54
      have hl := expr_lift_tmOExact hd (by decide) b1 hz ev54'
      have ext1 : Heap.Extends h m42 := ObsFn.heap_extends ev54
      have ext2 : Heap.Extends m42
          (m42 ++ [.construct "KernelTypes::KExprNode" "App" [xh, v41]]) :=
        Heap.Extends.snoc _ _
      obtain ⟨k₁, r₁⟩ := TmOExact.mono (ext1.trans ext2) hH
      obtain ⟨k₂, r₂⟩ := TmOExact.mono ext2 hl
      have happ : TmOExact κ (m42 ++ [.construct "KernelTypes::KExprNode" "App" [xh, v41]])
          (.app H (P.liftLooseBVars depth 0))
          (.ptr (.enum "KernelTypes::KExprNode") m42.length) :=
        ⟨max k₁ k₂, .app (by simp) (tmExact_depth_le r₁ _ (Nat.le_max_left _ _))
          (tmExact_depth_le r₂ _ (Nat.le_max_right _ _))⟩
      exact ih ev83 b2 happ (tmOExactList_mono (ext1.trans ext2) hzs')

/-- A `NotLet` cell that is not a `Forall` node cannot represent `.forallE _ _ _`, so `peelAll E =
([], E)`. -/
theorem peelAll_of_not_forall_not_let {h : Heap F} {E : KExpr} {p v : SourceValue F}
    (hp : TmOExact κ h E p) (ld : loadValue h p = .ok v)
    (hf : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Forall" vs)
    (hlet : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Let" vs) :
    peelAll E = ([], E) := by
  obtain ⟨k, ht⟩ := hp
  cases ht with
  | forallE cell _ _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
    exact (hf _ rfl hv).elim
  | letE cell _ _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
    exact (hlet _ rfl hv).elim
  | bvarFree _ _ _ hd => omega
  | _ => rfl

/-- **`KernelCheck::peel_leading_foralls_acc(ty, acc)`** on any `TmOExact` term (stepping through
any `Let` nodes, with zero no-let premise): the leading binders' domains, reversed, before `acc`,
and the body. -/
theorem peel_leading_foralls_acc_spec {E : KExpr} {xty xacc r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} {acc : List KExpr}
    (ev : ObsFn Obs.W "KernelCheck::peel_leading_foralls_acc" [xty, xacc] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hE : TmOExact κ h E xty) (hacc : RepList kexprListEnum (TmOExact κ) h acc xacc) :
    ∃ xl xb, r = .tuple [xl, xb] ∧ Heap.Extends h h' ∧
      RepList kexprListEnum (TmOExact κ) h' ((peelAll E).1.reverse ++ acc) xl ∧
      TmOExact κ h' (peelAll E).2 xb := by
  match Obs.«KernelCheck::peel_leading_foralls_acc».obs ev with
  | .Forall (x_dom := xdom) (x_body := xbody) (cs39 := cs1) (m52 := m1)
      (ld12 := ld) (hm60 := hm1) (ev41 := e1) (hc80 := hc) .. =>
    subst hm1
    obtain ⟨D, B, ℓ, rfl, hD, hB, -⟩ := TmOExact.forallE_of_load hE ld
    have ext : Heap.Extends h (h ++ [.construct kexprListEnum "Cons" [xdom, xacc]]) :=
      Heap.Extends.snoc _ _
    have hacc' := Lib.rep_store_cons tmOExact_heapMono₂ hD hacc
    have hlt : cs1.length < cs.length := by rw [hc]; simp
    have b1 : IxVM.Consistency.Bounded cs1 :=
      RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
    obtain ⟨xl, xb, rfl, ext', hl, hb⟩ := peel_leading_foralls_acc_spec e1 b1 (hB.mono ext) hacc'
    refine ⟨xl, xb, rfl, ext.trans ext', ?_, hb⟩
    simpa [peelAll] using hl
  | .Let (x_v := xv) (x_b := xb) (v_rolzgepu := v') (m_fhppzpwh := m')
      (cs_yqrxeseo := cs1) (cs_zgkirzbb := cs2) (ld12 := ld) (ev_gemvpjgn := e1)
      (ev_vtpduequ := e2) (hc_qubwlzze := hc) .. =>
    obtain ⟨T, V, B, rfl, -, hv, hb⟩ := TmOExact.letE_of_load hE ld
    have b1 : IxVM.Consistency.Bounded cs1 :=
      RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
    have b2 : IxVM.Consistency.Bounded cs2 :=
      RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
    have hv' := expr_inst1_tmOExact b1 hb hv e1
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨xl, xb', rfl, ext2, hl, hxb⟩ := peel_leading_foralls_acc_spec e2 b2 hv'
      (tmOExactList_mono e1.heap_extends hacc)
    exact ⟨xl, xb', rfl, e1.heap_extends.trans ext2, hl, hxb⟩
  | .other (v1 := v) (ld12 := ld) (hne81 := hnf) (hne_ttotnwna := hnl)
      (he89 := hr) (he104 := hh) .. =>
    subst hr hh
    have hp := peelAll_of_not_forall_not_let hE ld hnf hnl
    rw [hp]
    exact ⟨xacc, xty, rfl, Heap.Extends.refl _, hacc, hE⟩
termination_by cs.length

/-- **`KernelCheck::peel_leading_foralls(ty)`** on any `TmOExact` term is `peelAll`. -/
theorem peel_leading_foralls_spec {E : KExpr} {xty r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (ev : ObsFn Obs.W "KernelCheck::peel_leading_foralls" [xty] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hE : TmOExact κ h E xty) :
    ∃ xl xb, r = .tuple [xl, xb] ∧ Heap.Extends h h' ∧
      RepList kexprListEnum (TmOExact κ) h' (peelAll E).1 xl ∧ TmOExact κ h' (peelAll E).2 xb := by
  obtain ⟨m2, cs12, m25, x_rev_acc, x_body, v65, m69, cs77, hm33, ev14, rfl, ev79, rfl, hc⟩ :=
    Obs.«KernelCheck::peel_leading_foralls».obs ev
  subst hm33
  have b1 : IxVM.Consistency.Bounded cs12 :=
    RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
  have ext0 : Heap.Extends h (h ++ [.construct kexprListEnum "Nil" []]) := Heap.Extends.snoc _ _
  obtain ⟨xl, xb, he, ext1, hl, hb⟩ :=
    peel_leading_foralls_acc_spec ev14 b1 (hE.mono ext0) (Lib.rep_store_nil h)
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
  obtain ⟨he1, he2⟩ := he
  rw [← he1] at hl
  rw [← he2] at hb
  have ext2 : Heap.Extends m2 h' := ObsFn.heap_extends ev79
  have hrev := Lib.Lists.reverse_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
    tmOExact_heapMono₂
    (by rw [Obs.Names.«Lists::reverse<&KernelTypes::KExprNode>».symbol]; exact ev79)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hrev
  refine ⟨v65, x_body, rfl, ext0.trans (ext1.trans ext2), ?_, TmOExact.mono ext2 hb⟩
  simpa using hrev

/-- **`KernelCheck::count_foralls_body(ty, acc)`** counts the leading `Forall` binders of `E`
(through any `Let` nodes), returning `acc + (peelAll E).1.length`. -/
theorem count_foralls_body_spec {E : KExpr} {acc : Nat} {xty r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "KernelCheck::count_foralls_body" [xty, .field (acc : F)] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hE : TmOExact κ h E xty) :
    r = .field (((acc + (peelAll E).1.length : Nat) : F)) := by
  match Obs.«KernelCheck::count_foralls_body».obs ev with
  | .Forall (x_body := xbody) (cs40 := cs1) (v44 := v1) (ld12 := ld) (op65 := op)
      (ev42 := e1) (hc67 := hc) .. =>
    obtain ⟨D, B, ℓ, rfl, -, hB, -⟩ := TmOExact.forallE_of_load hE ld
    obtain rfl := binop_add_one_nat op
    have hlt : cs1.length < cs.length := by rw [hc]; simp
    have b1 : IxVM.Consistency.Bounded cs1 :=
      RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
    have hr := count_foralls_body_spec e1 b1 hB
    rw [hr]
    simp only [peelAll, List.length_cons]
    congr 1; congr 1; omega
  | .Let (x_v := xv) (x_b := xb) (v_qjjhbakm := v') (m_fhppzpwh := m')
      (cs_yqrxeseo := cs1) (cs_fsonrmiw := cs2) (ld12 := ld) (ev_gemvpjgn := e1)
      (ev_krdhokor := e2) (hc_qubwlzze := hc) .. =>
    obtain ⟨T, V, B, rfl, -, hv, hb⟩ := TmOExact.letE_of_load hE ld
    have b1 : IxVM.Consistency.Bounded cs1 :=
      RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
    have b2 : IxVM.Consistency.Bounded cs2 :=
      RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
    have hv' := expr_inst1_tmOExact b1 hb hv e1
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    exact count_foralls_body_spec e2 b2 hv'
  | .other (v1 := v) (ld12 := ld) (hne68 := hnf) (hne_ttotnwna := hnl) (he73 := hr) .. =>
    subst hr
    have hp := peelAll_of_not_forall_not_let hE ld hnf hnl
    rw [hp]
    simp
termination_by cs.length

end Lists

/-! ## Instantiating a type's parameters -/

section Params

variable {κ : _root_.Address → KKey}

/-- **A `BVar b` cell** represents `bvar b` on `TmOExact`. -/
theorem tmOExact_bvar_cell {h : Heap F} {b : Nat} (hb : b < 9223372036854775808) :
    TmOExact κ (h ++ [.construct kexprEnum "BVar" [.field (b : F)]]) (.bvar b)
      (.ptr (.enum kexprEnum) h.length) := by
  have hval : ZMod.val (b : F) = b := fval_natCast (Nat.lt_trans hb (by decide))
  have rb : TmExact κ 0 ghost0 (h ++ [.construct kexprEnum "BVar" [.field (b : F)]]) (b + 1)
      (.bvar (ZMod.val (b : F))) (.ptr (.enum kexprEnum) h.length) :=
    .bvarLocal (by simp) (by rw [hval]; exact hb) (by rw [hval]; omega)
  rw [hval] at rb
  exact ⟨b + 1, rb⟩

/-- The comparison `UInt32::less_than_fields(j, len)` of two small naturals. -/
theorem ltf_nat {a b : Nat} (ha : a < 18446744069414584321) (hb : b < 18446744069414584321)
    {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "UInt32::less_than_fields" [.field (a : F), .field (b : F)] h r h' cs) :
    (r = .field 1 ↔ a < b) ∧ h' = h := by
  obtain ⟨-, -, hiff, -, hh⟩ := Lib.less_than_fields_field ev
  rw [fval_natCast ha, fval_natCast hb] at hiff
  exact ⟨hiff, hh⟩

/-- **`KernelCheck::subst_param_for(j, nrp, is_aux, ps)`** is `substParamFor`. -/
theorem subst_param_for_spec {j nrp : Nat} {aux : Bool} {Ps : List KExpr}
    (hnrp : nrp < 9223372036854775808) (hjb : j < 9223372036854775808)
    (hPs : Ps.length < 9223372036854775808) (hj : ¬ (aux = true ∧ j < Ps.length) → j < nrp)
    {xps r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "KernelCheck::subst_param_for"
      [.field (j : F), .field (nrp : F), auxVal aux, xps] h r h' cs)
    (hP : RepList kexprListEnum (TmOExact κ) h Ps xps) :
    Heap.Extends h h' ∧ TmOExact κ h' (substParamFor j nrp aux Ps) r := by
  rcases Obs.«KernelCheck::subst_param_for».obs ev with
    ⟨v23, x30, hv14, rfl, rfl, op45, op37, -⟩ |
    ⟨v53, m54, cs64, m76, cs87, cs113, hne49, ev66, ev89, ev115, -⟩ |
    ⟨v53, m54, cs64, v75, m76, cs87, v145, x152, hne49, ev66, ev89, hne133, rfl, rfl, op167,
      op159, -⟩
  · have haux : aux = false := auxVal_eq_zero.mp hv14
    subst haux
    have hj' : j < nrp := hj (by simp)
    obtain rfl := binop_sub_one_nat (by omega) op45
    obtain rfl := binop_sub_nat (by omega) op37
    exact ⟨Heap.Extends.snoc _ _, by
      simpa [substParamFor] using
        tmOExact_bvar_cell (κ := κ) (h := h) (b := nrp - 1 - j) (by omega)⟩
  · have haux : aux = true := by
      cases aux
      · exact (hne49 rfl).elim
      · rfl
    subst haux
    obtain ⟨rfl, hm54⟩ := kexpr_length ev66 hP
    subst m54
    obtain ⟨hlt, hm76⟩ := ltf_nat (by omega) (by omega) ev89
    subst m76
    have hlt' : j < Ps.length := hlt.mp rfl
    obtain ⟨⟨x, hx, hxr⟩, hh⟩ := kexpr_lookup ev115 hP
    subst h'
    rw [fval_natCast (by omega)] at hx
    refine ⟨Heap.Extends.refl _, ?_⟩
    simp only [substParamFor, hx]
    exact hxr
  · have haux : aux = true := by
      cases aux
      · exact (hne49 rfl).elim
      · rfl
    subst haux
    obtain ⟨rfl, hm54⟩ := kexpr_length ev66 hP
    subst m54
    obtain ⟨hlt, hm76⟩ := ltf_nat (by omega) (by omega) ev89
    subst m76
    have hge : ¬ j < Ps.length := fun h => hne133 (hlt.mpr h)
    have hj' : j < nrp := hj (by simp [hge])
    obtain rfl := binop_sub_one_nat (by omega) op167
    obtain rfl := binop_sub_nat (by omega) op159
    refine ⟨Heap.Extends.snoc _ _, ?_⟩
    have hnone : Ps[j]? = none := List.getElem?_eq_none (by omega)
    simpa [substParamFor, hnone] using
      tmOExact_bvar_cell (κ := κ) (h := h) (b := nrp - 1 - j) (by omega)

/-- **`KernelCheck::ctor_subst_param_for(j, depth, lift, is_aux, ps)`** is `ctorSubstParamFor`. -/
theorem ctor_subst_param_for_spec {j depth lift : Nat} {aux : Bool} {Ps : List KExpr}
    (hdepth : depth < 9223372036854775808) (hjb : j < 9223372036854775808)
    (hlift : lift < 4611686018427387904)
    (hPs : Ps.length < 9223372036854775808) (hj : ¬ (aux = true ∧ j < Ps.length) → j < depth)
    {xps r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "KernelCheck::ctor_subst_param_for"
      [.field (j : F), .field (depth : F), .field (lift : F), auxVal aux, xps] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hP : RepList kexprListEnum (TmOExact κ) h Ps xps) :
    Heap.Extends h h' ∧ TmOExact κ h' (ctorSubstParamFor j depth lift aux Ps) r := by
  rcases Obs.«KernelCheck::ctor_subst_param_for».obs ev with
    ⟨v23, x30, hv14, rfl, rfl, op45, op37, -⟩ |
    ⟨v53, m54, cs64, m76, cs87, cs113, v116, m120, cs128, hne49, ev66, ev89, ev130, ev115, hc⟩ |
    ⟨v53, m54, cs64, v75, m76, cs87, v173, x180, hne49, ev66, ev89, hne161, rfl, rfl, op195,
      op187, -⟩
  · have haux : aux = false := auxVal_eq_zero.mp hv14
    subst haux
    have hj' : j < depth := hj (by simp)
    obtain rfl := binop_sub_one_nat (by omega) op45
    obtain rfl := binop_sub_nat (by omega) op37
    exact ⟨Heap.Extends.snoc _ _, by
      simpa [ctorSubstParamFor] using
        tmOExact_bvar_cell (κ := κ) (h := h) (b := depth - 1 - j) (by omega)⟩
  · have haux : aux = true := by
      cases aux
      · exact (hne49 rfl).elim
      · rfl
    subst haux
    obtain ⟨rfl, hm54⟩ := kexpr_length ev66 hP
    subst m54
    obtain ⟨hlt, hm76⟩ := ltf_nat (by omega) (by omega) ev89
    subst m76
    have hlt' : j < Ps.length := hlt.mp rfl
    obtain ⟨⟨x, hx, hxr⟩, hm120⟩ := kexpr_lookup ev130 hP
    subst m120
    rw [fval_natCast (by omega)] at hx
    have b1 : IxVM.Consistency.Bounded cs113 :=
      RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
    have ev115' : ObsFn Obs.W "KernelSubst::expr_lift"
        [v116, .field (lift : F), .field ((0 : Nat) : F)] h r h' cs113 := by
      simpa using ev115
    have hl := expr_lift_tmOExact hlift (by decide) b1 hxr ev115'
    refine ⟨ObsFn.heap_extends ev115, ?_⟩
    simp only [ctorSubstParamFor, hx]
    exact hl
  · have haux : aux = true := by
      cases aux
      · exact (hne49 rfl).elim
      · rfl
    subst haux
    obtain ⟨rfl, hm54⟩ := kexpr_length ev66 hP
    subst m54
    obtain ⟨hlt, hm76⟩ := ltf_nat (by omega) (by omega) ev89
    subst m76
    have hge : ¬ j < Ps.length := fun h => hne161 (hlt.mpr h)
    have hj' : j < depth := hj (by simp [hge])
    obtain rfl := binop_sub_one_nat (by omega) op195
    obtain rfl := binop_sub_nat (by omega) op187
    refine ⟨Heap.Extends.snoc _ _, ?_⟩
    have hnone : Ps[j]? = none := List.getElem?_eq_none (by omega)
    simpa [ctorSubstParamFor, hnone] using
      tmOExact_bvar_cell (κ := κ) (h := h) (b := depth - 1 - j) (by omega)

/-- **`KernelCheck::peel_motive_params_subst(ty, n, nrp, is_aux, ps, j)`** is `peelMotiveParams`
(stepping through any intervening `Let` nodes, with zero no-let premise). -/
theorem peel_motive_params_subst_spec {nrp : Nat} {aux : Bool} {Ps : List KExpr}
    (hnrp : nrp < 9223372036854775808) (hPs : Ps.length < 9223372036854775808) :
    ∀ (n j : Nat), n + j < 9223372036854775808 →
      (∀ i, j ≤ i → i < j + n → ¬ (aux = true ∧ i < Ps.length) → i < nrp) →
      ∀ {E : KExpr} {xty xps r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn Obs.W "KernelCheck::peel_motive_params_subst"
        [xty, .field (n : F), .field (nrp : F), auxVal aux, xps, .field (j : F)] h r h' cs →
      IxVM.Consistency.Bounded cs → TmOExact κ h E xty →
      RepList kexprListEnum (TmOExact κ) h Ps xps →
      ∃ E', peelMotiveParams nrp aux Ps n j E = some E' ∧ TmOExact κ h' E' r := by
  intro n j hb hj E xty xps r h h' cs ev hbnd hE hP
  cases n with
  | zero =>
    match Obs.«KernelCheck::peel_motive_params_subst».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      exact ⟨E, rfl, hE⟩
    | .other_Forall (hne19 := hne) .. | .other_Let (hne19 := hne) .. =>
      exact (hne (by simp)).elim
  | succ n =>
    match Obs.«KernelCheck::peel_motive_params_subst».obs ev with
    | .n0 (hv14 := hv) .. =>
      exact absurd (field_natCast_eq_zero (by omega) hv) (by omega)
    | .other_Forall (x_body := xbody) (v_iysyudfr := vp) (m_dkqmqvli := m1)
        (cs_bhlupqyr := cs1) (v_tjmouerm := v2) (m_rjuwnrqp := m2) (cs_jeizituo := cs2)
        (cs_kaoaiaez := cs3) (v_epppphoo := vn) (v_kxgtyqjk := vj) (ld_hdultwxn := ld)
        (ev_yoygdtsd := e1) (ev_qxpraawz := e2) (op_czjgbwao := op1) (op_kecwtfli := op2)
        (ev_oikogjza := e3) (hc_ydqmxojp := hc) .. =>
      obtain ⟨T, B, ℓ, rfl, -, hB, -⟩ := TmOExact.forallE_of_load hE ld
      obtain ⟨ext1, hp⟩ := subst_param_for_spec (κ := κ) hnrp (by omega) hPs
        (hj j le_rfl (by omega)) e1 hP
      have b2 : IxVM.Consistency.Bounded cs2 :=
        RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
      have b3 : IxVM.Consistency.Bounded cs3 :=
        RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
      have hinst := expr_inst1_tmOExact b2 (hB.mono ext1) hp e2
      have ext2 : Heap.Extends m1 m2 := ObsFn.heap_extends e2
      obtain rfl := binop_sub_one_nat (by omega) op1
      obtain rfl := binop_add_one_nat op2
      have hlt : cs3.length < cs.length := by
        rw [hc]; simp only [List.length_cons, List.length_append]; omega
      obtain ⟨E', hE', hr⟩ := peel_motive_params_subst_spec hnrp hPs n (j + 1) (by omega)
        (fun i hi1 hi2 hni => hj i (by omega) (by omega) hni)
        (by simpa using e3) b3 hinst (tmOExactList_mono (ext1.trans ext2) hP)
      exact ⟨E', by simpa [peelMotiveParams, isForall] using hE', hr⟩
    | .other_Let (x_v := xv) (x_b := xb) (v_vylehxeo := v') (m_vopdadin := m')
        (cs_cuwzkjio := cs1) (cs_gayphuxm := cs2) (ld_hdultwxn := ld)
        (ev_mtsqvowg := e1) (ev_onsxuhrh := e2) (hc_thparjte := hc) .. =>
      obtain ⟨T, V, B, rfl, -, hv, hbB⟩ := TmOExact.letE_of_load hE ld
      have b1 : IxVM.Consistency.Bounded cs1 :=
        RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
      have b2 : IxVM.Consistency.Bounded cs2 :=
        RomBound.bounded_mono hbnd (fun c hc' => by rw [hc]; simp [hc'])
      have hv' := expr_inst1_tmOExact b1 hbB hv e1
      have hlt : cs2.length < cs.length := by
        rw [hc]; simp only [List.length_cons, List.length_append]; omega
      exact peel_motive_params_subst_spec hnrp hPs (n + 1) j hb hj e2 b2 hv'
        (tmOExactList_mono e1.heap_extends hP)
termination_by _ _ _ _ _ _ _ _ _ _ cs => cs.length

end Params

end IxVM.Refinement.Binding.FamilyRecon
