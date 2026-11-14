import IxVMRefinement.Subst.Lbr

/-! # Occurrence tests: `has_bvar_in_range*`, `expr_has_bvar_at*`

Each answers `0` or `1`, reads only, and claims on `0` that no heap index lies in its window
(shifted by one under each binder). `has_bvar_in_range` shifts its window at a binder with
the field's `+ 1`, which may wrap: its claim is `NoIdxF` (nothing where the window's end has
passed the field's size); where the start wraps alone, the start has passed every index, so
the claim holds anyway (`noIdxF_succ`). `expr_has_bvar_at` compares for equality, so its claim
is exact: a wrapped depth `0` is again past every index (`noIdx_succ`). -/

namespace IxVM.Refinement.Core.SubstAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency (Bounded)
open Specs.Subst (IdxAll IdxLt NoIdx NoIdxF BVarIm idxBound)

set_option linter.unusedVariables false

local macro "lt_calls" : term => `(by simp <;> omega)
local macro "sub_calls" : term => `(fun _ hx => by simp [hx])

/-! ## Windows one binder deeper -/

theorem noIdxF_succ {h : Heap F} {l u : F} {p : SourceValue F}
    (hn : NoIdxF h (ZMod.val (l + 1)) (ZMod.val (u + 1)) p) :
    NoIdxF h (ZMod.val l + 1) (ZMod.val u + 1) p :=
  idxAll_mono hn (fun n i hi hlt => by
    have hiv := ZMod.val_lt i
    rcases val_add_one_cases u with ⟨_, hu⟩ | ⟨hu1, _⟩
    · rcases val_add_one_cases l with ⟨_, hl⟩ | ⟨hl1, _⟩
      · rw [hu, hl] at hi; exact hi (by omega)
      · left; omega
    · exfalso; omega)

theorem noIdx_succ {h : Heap F} {j : F} {p : SourceValue F}
    (hn : NoIdx h (ZMod.val (j + 1)) (ZMod.val (j + 1) + 1) p) :
    NoIdx h (ZMod.val j + 1) (ZMod.val j + 2) p :=
  idxAll_mono hn (fun n i hi => by
    have hiv := ZMod.val_lt i
    rcases val_add_one_cases j with ⟨_, hj⟩ | ⟨hj1, _⟩
    · rw [hj] at hi; omega
    · left; omega)

/-- A window's fact on a binder body, at offset `1`. -/
theorem noIdxF_body {h : Heap F} {lo hi : Nat} {p : SourceValue F}
    (hn : NoIdxF h (lo + 1) (hi + 1) p) :
    IdxAll h (fun m i => hi + m < Aiur.Library.U32.Goldilocks.modulus →
      (ZMod.val i < lo + m ∨ hi + m ≤ ZMod.val i)) 1 p :=
  idxAll_imp hn (fun n i h1 h2 => by have := h1 (by omega); omega)

theorem noIdx_body {h : Heap F} {lo hi : Nat} {p : SourceValue F}
    (hn : NoIdx h (lo + 1) (hi + 1) p) :
    IdxAll h (fun m i => ZMod.val i < lo + m ∨ hi + m ≤ ZMod.val i) 1 p :=
  idxAll_imp hn (fun n i h1 => by omega)

/-- A represented node none of whose index-carrying constructors it is: a leaf. -/
theorem idxAll_of_other {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {e v : SourceValue F} {P : Nat → F → Prop} {m : Nat}
    (hE : Tm κ d Γ h k E e) (ld : loadValue h e = .ok v)
    (n1 : ∀ vs : List (SourceValue F), vs.length = 1 → v ≠ .construct kexprEnum "BVar" vs)
    (n2 : ∀ vs : List (SourceValue F), vs.length = 2 → v ≠ .construct kexprEnum "App" vs)
    (n3 : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Lam" vs)
    (n4 : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Forall" vs)
    (n5 : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Let" vs)
    (n6 : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Proj" vs) :
    IdxAll h P m e := by
  cases hE with
  | bvarLocal cell _ _ =>
    rw [loadValue_enum_cell cell] at ld; injection ld with ld; exact absurd ld.symm (n1 _ rfl)
  | bvarFree cell _ _ _ =>
    rw [loadValue_enum_cell cell] at ld; injection ld with ld; exact absurd ld.symm (n1 _ rfl)
  | sort cell _ _ => exact .sort cell
  | const cell _ _ _ => exact .const cell
  | app cell _ _ =>
    rw [loadValue_enum_cell cell] at ld; injection ld with ld; exact absurd ld.symm (n2 _ rfl)
  | lam cell _ _ _ =>
    rw [loadValue_enum_cell cell] at ld; injection ld with ld; exact absurd ld.symm (n3 _ rfl)
  | forallE cell _ _ _ =>
    rw [loadValue_enum_cell cell] at ld; injection ld with ld; exact absurd ld.symm (n4 _ rfl)
  | letE cell _ _ _ =>
    rw [loadValue_enum_cell cell] at ld; injection ld with ld; exact absurd ld.symm (n5 _ rfl)
  | litNat cell _ _ => exact .lit cell
  | litStr cell _ _ => exact .lit cell
  | proj cell _ _ =>
    rw [loadValue_enum_cell cell] at ld; injection ld with ld; exact absurd ld.symm (n6 _ rfl)

theorem field_one_ne_zero : (Value.field (1 : F) : SourceValue F) ≠ .field 0 := by
  intro h; injection h with h; exact absurd h (by decide)

/-- An answer `0` or `1` other than `1` is `0`. -/
theorem zero_of_ne_one {r : SourceValue F} (h01 : r = .field 0 ∨ r = .field 1)
    (hne : r ≠ .field 1) : r = .field 0 := h01.resolve_right hne

/-! ## `has_bvar_in_range` -/

theorem hbir_bvar_obs {a r : SourceValue F} {l u : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelSubst::has_bvar_in_range_bvar" [a, .field l, .field u] h r h' cs) :
    ∃ i : F, a = .field i ∧ h' = h ∧ (r = .field 0 ∨ r = .field 1) ∧
      (r = .field 0 → ZMod.val i < ZMod.val l ∨ ZMod.val u ≤ ZMod.val i) := by
  cases Obs.«KernelSubst::has_bvar_in_range_bvar».obs ev with
  | n1 m2 cs13 ev15 he36 he37 hc38 =>
    obtain ⟨i, l', rfl, hl, -, -, hr, rfl⟩ := ltf ev15
    injection hl with hl; subst hl
    subst he36 he37
    exact ⟨i, rfl, rfl, .inl rfl, fun _ => .inl (ltf_one hr.symm)⟩
  | n0 m2 cs13 cs47 ev15 ev49 hc66 =>
    obtain ⟨i, l', rfl, hl, -, -, hr, rfl⟩ := ltf ev15
    injection hl with hl; subst hl
    obtain ⟨i', u', hi', hu, -, -, hr', rfl⟩ := ltf ev49
    injection hi' with hi'; injection hu with hu; subst hi' hu
    refine ⟨i, rfl, rfl, ?_, fun h0 => .inr ?_⟩
    · rw [hr']; split <;> simp
    · rw [hr'] at h0; exact Nat.le_of_not_lt (ltf_zero h0)

theorem g_has_bvar_in_range_bvar {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::has_bvar_in_range_bvar" args h r h' calls) :
    G.has_bvar_in_range_bvar args h r h' calls := by
  intro i l u hargs _
  subst hargs
  obtain ⟨i', hi, hh, h01, h0⟩ := hbir_bvar_obs ev
  injection hi with hi; subst hi
  exact ⟨hh, h01, h0⟩

theorem g_has_bvar_in_range (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::has_bvar_in_range" args h r h' calls) (ih : GIH κ calls) :
    G.has_bvar_in_range κ args h r h' calls := by
  intro e l u hargs bd
  subst hargs
  match Obs.«KernelSubst::has_bvar_in_range».obs ev with
  | .BVar (ld12 := ld) (ev30 := e1) .. =>
    obtain ⟨i, rfl, rfl, h01, h0⟩ := hbir_bvar_obs e1
    exact ⟨rfl, h01, fun hr d Γ k E hE => idxAll_bvar_of_load ld (fun _ => by simpa using h0 hr)⟩
  | .Srt (ld12 := ld) (he69 := hr) (he70 := he) .. =>
    subst hr he; exact ⟨rfl, .inl rfl, fun _ d Γ k E hE => idxAll_sort_of_load ld⟩
  | .Const (ld12 := ld) (he91 := hr) (he92 := he) .. =>
    subst hr he; exact ⟨rfl, .inl rfl, fun _ d Γ k E hE => idxAll_const_of_load ld⟩
  | .Lit (ld12 := ld) (he107 := hr) (he108 := he) .. =>
    subst hr he; exact ⟨rfl, .inl rfl, fun _ d Γ k E hE => idxAll_lit_of_load ld⟩
  | .App_n1 (ev141 := e1) (he170 := hr) (he171 := he) (hc172 := hc) .. =>
    subst hc hr he
    obtain ⟨rfl, -⟩ := ih.get .has_bvar_in_range lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd)
    exact ⟨rfl, .inr rfl, fun h0 => absurd h0 field_one_ne_zero⟩
  | .App_n0 (ld12 := ld) (ev141 := e1) (ev183 := e2) (hc208 := hc) .. =>
    subst hc
    obtain ⟨rfl, -, sf⟩ := ih.get .has_bvar_in_range lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd)
    obtain ⟨rfl, h01, sa⟩ := ih.get .has_bvar_in_range lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd)
    refine ⟨rfl, h01, fun hr d Γ k E hE => ?_⟩
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hE ld
    exact idxAll_app_of_load ld (sf rfl d Γ k Ef hf) (sa hr d Γ k Ea ha)
  | .Lam (ld12 := ld) (ev238 := e1) (hc271 := hc) .. =>
    subst hc
    obtain ⟨rfl, h01, sb⟩ :=
      ih.get .has_bvar_in_range_binder lt_calls e1 _ _ _ _ rfl (bounded_sub sub_calls bd)
    refine ⟨rfl, h01, fun hr d Γ k E hE => ?_⟩
    obtain ⟨T, B, ℓ, rfl, ht, hb, -⟩ := Tm.lam_of_load hE ld
    obtain ⟨n1, n2⟩ := sb hr d Γ k T B ht hb
    exact idxAll_lam_of_load ld n1 (noIdxF_body n2)
  | .Forall (ld12 := ld) (ev300 := e1) (hc333 := hc) .. =>
    subst hc
    obtain ⟨rfl, h01, sb⟩ :=
      ih.get .has_bvar_in_range_binder lt_calls e1 _ _ _ _ rfl (bounded_sub sub_calls bd)
    refine ⟨rfl, h01, fun hr d Γ k E hE => ?_⟩
    obtain ⟨T, B, ℓ, rfl, ht, hb, -⟩ := Tm.forallE_of_load hE ld
    obtain ⟨n1, n2⟩ := sb hr d Γ k T B ht hb
    exact idxAll_forallE_of_load ld n1 (noIdxF_body n2)
  | .Let (ld12 := ld) (ev361 := e1) (hc402 := hc) .. =>
    subst hc
    obtain ⟨rfl, h01, sl⟩ :=
      ih.get .has_bvar_in_range_let lt_calls e1 _ _ _ _ _ rfl (bounded_sub sub_calls bd)
    refine ⟨rfl, h01, fun hr d Γ k E hE => ?_⟩
    obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := Tm.letE_of_load hE ld
    obtain ⟨n1, n2, n3⟩ := sl hr d Γ k T V B ht hv hb
    exact idxAll_letE_of_load ld n1 n2 (noIdxF_body n3)
  | .Proj (ld12 := ld) (ev432 := e1) (hc457 := hc) .. =>
    subst hc
    obtain ⟨rfl, h01, s1⟩ := ih.get .has_bvar_in_range lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd)
    refine ⟨rfl, h01, fun hr d Γ k E hE => ?_⟩
    obtain ⟨a, i, Es, -, rfl, -, hes⟩ := Tm.proj_of_load hE ld
    exact idxAll_proj_of_load ld (s1 hr d Γ k Es hes)

theorem g_has_bvar_in_range_binder (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::has_bvar_in_range_binder" args h r h' calls) (ih : GIH κ calls) :
    G.has_bvar_in_range_binder κ args h r h' calls := by
  intro ty body l u hargs bd
  subst hargs
  match Obs.«KernelSubst::has_bvar_in_range_binder».obs ev with
  | .n1 (ev15 := e1) (he44 := hr) (he45 := he) (hc46 := hc) .. =>
    subst hc hr he
    obtain ⟨rfl, -⟩ := ih.get .has_bvar_in_range lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd)
    exact ⟨rfl, .inr rfl, fun h0 => absurd h0 field_one_ne_zero⟩
  | .n0 (ev15 := e1) (op81 := o1) (op96 := o2) (ev57 := e2) (hc98 := hc) .. =>
    subst hc
    rw [add_ok o1] at e2; rw [add_ok o2] at e2
    obtain ⟨rfl, -, st⟩ := ih.get .has_bvar_in_range lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd)
    obtain ⟨rfl, h01, sb⟩ := ih.get .has_bvar_in_range lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd)
    refine ⟨rfl, h01, fun hr d Γ k T B ht hb => ⟨st rfl d Γ k T ht, ?_⟩⟩
    exact noIdxF_succ (sb hr d Γ (k + 1) B hb)

theorem g_has_bvar_in_range_let (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::has_bvar_in_range_let" args h r h' calls) (ih : GIH κ calls) :
    G.has_bvar_in_range_let κ args h r h' calls := by
  intro ty val body l u hargs bd
  subst hargs
  match Obs.«KernelSubst::has_bvar_in_range_let».obs ev with
  | .n1 (ev15 := e1) (he44 := hr) (he45 := he) (hc46 := hc) .. =>
    subst hc hr he
    obtain ⟨rfl, -⟩ := ih.get .has_bvar_in_range lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd)
    exact ⟨rfl, .inr rfl, fun h0 => absurd h0 field_one_ne_zero⟩
  | .n0_n1 (ev15 := e1) (ev66 := e2) (he95 := hr) (he96 := he) (hc97 := hc) .. =>
    subst hc hr he
    obtain ⟨rfl, -⟩ := ih.get .has_bvar_in_range lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd)
    obtain ⟨rfl, -⟩ := ih.get .has_bvar_in_range lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd)
    exact ⟨rfl, .inr rfl, fun h0 => absurd h0 field_one_ne_zero⟩
  | .n0_n0 (ev15 := e1) (ev66 := e2) (op132 := o1) (op147 := o2) (ev108 := e3) (hc149 := hc) .. =>
    subst hc
    rw [add_ok o1] at e3; rw [add_ok o2] at e3
    obtain ⟨rfl, -, st⟩ := ih.get .has_bvar_in_range lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd)
    obtain ⟨rfl, -, sv⟩ := ih.get .has_bvar_in_range lt_calls e2 _ _ _ rfl (bounded_sub sub_calls bd)
    obtain ⟨rfl, h01, sb⟩ := ih.get .has_bvar_in_range lt_calls e3 _ _ _ rfl (bounded_sub sub_calls bd)
    refine ⟨rfl, h01, fun hr d Γ k T V B ht hv hb =>
      ⟨st rfl d Γ k T ht, sv rfl d Γ k V hv, ?_⟩⟩
    exact noIdxF_succ (sb hr d Γ (k + 1) B hb)

/-! ## `expr_has_bvar_at` -/

theorem g_expr_has_bvar_at (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_has_bvar_at" args h r h' calls) (ih : GIH κ calls) :
    G.expr_has_bvar_at κ args h r h' calls := by
  intro e j hargs bd
  subst hargs
  match Obs.«KernelSubst::expr_has_bvar_at».obs ev with
  | .BVar_n0 (he48 := hr) (he49 := he) .. =>
    subst hr he
    exact ⟨rfl, .inr rfl, fun h0 => absurd h0 field_one_ne_zero⟩
  | .BVar_other (ld12 := ld) (op41 := op) (hne51 := hne) (he55 := hr) (he56 := he) .. =>
    subst hr he
    refine ⟨rfl, .inl rfl, fun _ d Γ k E hE => ?_⟩
    obtain ⟨i, rfl, -, -⟩ := Tm.bvar_of_load hE ld
    have hij : i ≠ j := fun hij => hne (by rw [sub_ok op, hij, sub_self])
    have hv : ZMod.val i ≠ ZMod.val j := fun hv => hij (ZMod.val_injective _ hv)
    exact idxAll_bvar_of_load ld (by show ZMod.val i < ZMod.val j + 0 ∨ ZMod.val j + 1 + 0 ≤ ZMod.val i; omega)
  | .App_n1 (ev89 := e1) (he110 := hr) (he111 := he) (hc112 := hc) .. =>
    subst hc hr he
    obtain ⟨rfl, -⟩ := ih.get .expr_has_bvar_at lt_calls e1 _ _ rfl (bounded_sub sub_calls bd)
    exact ⟨rfl, .inr rfl, fun h0 => absurd h0 field_one_ne_zero⟩
  | .App_other (ld12 := ld) (ev89 := e1) (hne113 := hne) (ev122 := e2) (hc139 := hc) .. =>
    subst hc
    obtain ⟨rfl, f01, sf⟩ := ih.get .expr_has_bvar_at lt_calls e1 _ _ rfl (bounded_sub sub_calls bd)
    obtain ⟨rfl, h01, sa⟩ := ih.get .expr_has_bvar_at lt_calls e2 _ _ rfl (bounded_sub sub_calls bd)
    refine ⟨rfl, h01, fun hr d Γ k E hE => ?_⟩
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hE ld
    exact idxAll_app_of_load ld (sf (zero_of_ne_one f01 hne) d Γ k Ef hf) (sa hr d Γ k Ea ha)
  | .Lam (ld12 := ld) (ev168 := e1) (hc193 := hc) .. =>
    subst hc
    obtain ⟨rfl, h01, sb⟩ :=
      ih.get .expr_has_bvar_at_binder lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd)
    refine ⟨rfl, h01, fun hr d Γ k E hE => ?_⟩
    obtain ⟨T, B, ℓ, rfl, ht, hb, -⟩ := Tm.lam_of_load hE ld
    obtain ⟨n1, n2⟩ := sb hr d Γ k T B ht hb
    exact idxAll_lam_of_load ld n1 (noIdx_body n2)
  | .Forall (ld12 := ld) (ev222 := e1) (hc247 := hc) .. =>
    subst hc
    obtain ⟨rfl, h01, sb⟩ :=
      ih.get .expr_has_bvar_at_binder lt_calls e1 _ _ _ rfl (bounded_sub sub_calls bd)
    refine ⟨rfl, h01, fun hr d Γ k E hE => ?_⟩
    obtain ⟨T, B, ℓ, rfl, ht, hb, -⟩ := Tm.forallE_of_load hE ld
    obtain ⟨n1, n2⟩ := sb hr d Γ k T B ht hb
    exact idxAll_forallE_of_load ld n1 (noIdx_body n2)
  | .Let (ld12 := ld) (ev275 := e1) (hc308 := hc) .. =>
    subst hc
    obtain ⟨rfl, h01, sl⟩ :=
      ih.get .expr_has_bvar_at_let lt_calls e1 _ _ _ _ rfl (bounded_sub sub_calls bd)
    refine ⟨rfl, h01, fun hr d Γ k E hE => ?_⟩
    obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := Tm.letE_of_load hE ld
    obtain ⟨n1, n2, n3⟩ := sl hr d Γ k T V B ht hv hb
    exact idxAll_letE_of_load ld n1 n2 (noIdx_body n3)
  | .Proj (ld12 := ld) (ev338 := e1) (hc355 := hc) .. =>
    subst hc
    obtain ⟨rfl, h01, s1⟩ := ih.get .expr_has_bvar_at lt_calls e1 _ _ rfl (bounded_sub sub_calls bd)
    refine ⟨rfl, h01, fun hr d Γ k E hE => ?_⟩
    obtain ⟨a, i, Es, -, rfl, -, hes⟩ := Tm.proj_of_load hE ld
    exact idxAll_proj_of_load ld (s1 hr d Γ k Es hes)
  | .other (ld12 := ld) (hne58 := n1) (hne140 := n2) (hne194 := n3) (hne248 := n4)
      (hne309 := n5) (hne356 := n6) (he360 := hr) (he361 := he) .. =>
    subst hr he
    exact ⟨rfl, .inl rfl, fun _ d Γ k E hE => idxAll_of_other hE ld n1 n2 n3 n4 n5 n6⟩

theorem g_expr_has_bvar_at_binder (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_has_bvar_at_binder" args h r h' calls) (ih : GIH κ calls) :
    G.expr_has_bvar_at_binder κ args h r h' calls := by
  intro ty body j hargs bd
  subst hargs
  match Obs.«KernelSubst::expr_has_bvar_at_binder».obs ev with
  | .n1 (ev15 := e1) (he36 := hr) (he37 := he) (hc38 := hc) .. =>
    subst hc hr he
    obtain ⟨rfl, -⟩ := ih.get .expr_has_bvar_at lt_calls e1 _ _ rfl (bounded_sub sub_calls bd)
    exact ⟨rfl, .inr rfl, fun h0 => absurd h0 field_one_ne_zero⟩
  | .other (ev15 := e1) (hne39 := hne) (op71 := o1) (ev48 := e2) (hc73 := hc) .. =>
    subst hc
    rw [add_ok o1] at e2
    obtain ⟨rfl, t01, st⟩ := ih.get .expr_has_bvar_at lt_calls e1 _ _ rfl (bounded_sub sub_calls bd)
    obtain ⟨rfl, h01, sb⟩ := ih.get .expr_has_bvar_at lt_calls e2 _ _ rfl (bounded_sub sub_calls bd)
    refine ⟨rfl, h01, fun hr d Γ k T B ht hb => ⟨st (zero_of_ne_one t01 hne) d Γ k T ht, ?_⟩⟩
    exact noIdx_succ (sb hr d Γ (k + 1) B hb)

theorem g_expr_has_bvar_at_let (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelSubst::expr_has_bvar_at_let" args h r h' calls) (ih : GIH κ calls) :
    G.expr_has_bvar_at_let κ args h r h' calls := by
  intro ty val body j hargs bd
  subst hargs
  match Obs.«KernelSubst::expr_has_bvar_at_let».obs ev with
  | .n1 (ev15 := e1) (he36 := hr) (he37 := he) (hc38 := hc) .. =>
    subst hc hr he
    obtain ⟨rfl, -⟩ := ih.get .expr_has_bvar_at lt_calls e1 _ _ rfl (bounded_sub sub_calls bd)
    exact ⟨rfl, .inr rfl, fun h0 => absurd h0 field_one_ne_zero⟩
  | .other_n1 (ev15 := e1) (ev57 := e2) (he78 := hr) (he79 := he) (hc80 := hc) .. =>
    subst hc hr he
    obtain ⟨rfl, -⟩ := ih.get .expr_has_bvar_at lt_calls e1 _ _ rfl (bounded_sub sub_calls bd)
    obtain ⟨rfl, -⟩ := ih.get .expr_has_bvar_at lt_calls e2 _ _ rfl (bounded_sub sub_calls bd)
    exact ⟨rfl, .inr rfl, fun h0 => absurd h0 field_one_ne_zero⟩
  | .other_other (ev15 := e1) (hne39 := hne1) (ev57 := e2) (hne81 := hne2) (op113 := o1)
      (ev90 := e3) (hc115 := hc) .. =>
    subst hc
    rw [add_ok o1] at e3
    obtain ⟨rfl, t01, st⟩ := ih.get .expr_has_bvar_at lt_calls e1 _ _ rfl (bounded_sub sub_calls bd)
    obtain ⟨rfl, v01, sv⟩ := ih.get .expr_has_bvar_at lt_calls e2 _ _ rfl (bounded_sub sub_calls bd)
    obtain ⟨rfl, h01, sb⟩ := ih.get .expr_has_bvar_at lt_calls e3 _ _ rfl (bounded_sub sub_calls bd)
    refine ⟨rfl, h01, fun hr d Γ k T V B ht hv hb =>
      ⟨st (zero_of_ne_one t01 hne1) d Γ k T ht, sv (zero_of_ne_one v01 hne2) d Γ k V hv, ?_⟩⟩
    exact noIdx_succ (sb hr d Γ (k + 1) B hb)

end IxVM.Refinement.Core.SubstAux
