import IxVMRefinement.Core.Specs
import IxVMRefinement.Obs.KernelCheck
import IxVMRefinement.Obs.KernelLevels
import Ix.IxVM.Refinement.Mirrors.Deserialize

/-! # Structural identity: `kexpr_struct_eq`

`KernelDefEq::k_is_def_eq` answers `1` without further work when
`KernelCheck::kexpr_struct_eq` finds its two sides structurally identical. This
module proves that answer sound: when `kexpr_struct_eq(a, b)` returns `1` and
`a`, `b` represent kernel terms at the same local depth, the terms are equal, so
`DefEq.refl` closes the definitional-equality obligation.

The proof is an induction on the size of the observed derivation, separate from
the slice's induction (`IH`): `kexpr_struct_eq` and its helpers
(`level_struct_eq`, `literal_eq`, `klimbs_eq`) call nothing outside this
group but `Bytes::address_eq` (the slice's `Assumed.addressEq`) and the leaf
`UInt64::eq` (read off its generated mirror). Terms with no image under `Tr`
(lets, projections, string literals) close by the translation's inversion;
`Const` level lists close because the slice is level-free (`Tr.const_inv`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.IxVMRep Aiur.Library.List

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! ## Arithmetic -/

theorem evalBinOp_sub_inv {x y r : SourceValue F} (h : evalBinOp .sub x y = .ok r) :
    ∃ a b, x = .field a ∧ y = .field b ∧ r = .field (a - b) := by
  cases x <;> cases y <;> simp [evalBinOp] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

theorem evalBinOp_mul_inv {x y r : SourceValue F} (h : evalBinOp .mul x y = .ok r) :
    ∃ a b, x = .field a ∧ y = .field b ∧ r = .field (a * b) := by
  cases x <;> cases y <;> simp [evalBinOp] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

theorem field_sub_eq_zero {a b : F} (h : (Value.field (a - b) : SourceValue F) = .field 0) :
    a = b := by
  injection h with h
  exact sub_eq_zero.mp h

theorem field_one_ne_zero : (Value.field 1 : SourceValue F) ≠ .field 0 := by
  intro h; injection h with h; exact one_ne_zero h

/-! ## Inversion of the representations at a load -/

theorem RepK.bvar_of_load {h : Heap F} {t : IxVMKExpr F} {p x : SourceValue F}
    (rep : RepK h t p) (hl : loadValue h p = .ok (.construct kexprEnum "BVar" [x])) :
    ∃ i, t = .bvar i ∧ x = .field i := by
  cases rep with
  | bvar cell =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ _ hargs; injection hargs with hx _
    exact ⟨_, rfl, hx.symm⟩
  | sort cell _ | const cell _ _ | app cell _ _ | lam cell _ _ | forallE cell _ _
  | letE cell _ _ _ | litNat cell _ | litStr cell _ | proj cell _ _ =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc _
    exact absurd hc (by decide)

theorem RepK.sort_of_load {h : Heap F} {t : IxVMKExpr F} {p x : SourceValue F}
    (rep : RepK h t p) (hl : loadValue h p = .ok (.construct kexprEnum "Srt" [x])) :
    ∃ l, t = .sort l ∧ RepIxVMKUniv h l x := by
  cases rep with
  | sort cell rl =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ _ hargs; injection hargs with hx _
    subst hx
    exact ⟨_, rfl, rl⟩
  | bvar cell | const cell _ _ | app cell _ _ | lam cell _ _ | forallE cell _ _
  | letE cell _ _ _ | litNat cell _ | litStr cell _ | proj cell _ _ =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc _
    exact absurd hc (by decide)

theorem RepK.forallE_of_load {h : Heap F} {t : IxVMKExpr F} {p x y : SourceValue F}
    (rep : RepK h t p) (hl : loadValue h p = .ok (.construct kexprEnum "Forall" [x, y])) :
    ∃ ty b, t = .forallE ty b ∧ RepK h ty x ∧ RepK h b y := by
  cases rep with
  | forallE cell rt rb =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ _ hargs
    injection hargs with hx hrest; injection hrest with hy _
    subst hx hy
    exact ⟨_, _, rfl, rt, rb⟩
  | bvar cell | sort cell _ | const cell _ _ | app cell _ _ | lam cell _ _
  | letE cell _ _ _ | litNat cell _ | litStr cell _ | proj cell _ _ =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc _
    exact absurd hc (by decide)

/-- A `Lit` node is a `Nat` literal over its limb list, or a string literal. -/
theorem RepK.lit_of_load {h : Heap F} {t : IxVMKExpr F} {p x : SourceValue F}
    (rep : RepK h t p) (hl : loadValue h p = .ok (.construct kexprEnum "Lit" [x])) :
    (∃ limbs lp, t = .litNat limbs ∧ x = .construct "KernelTypes::KLiteral" "Nat" [lp] ∧
      RepList limbListEnum RepU64 h limbs lp) ∨ (∃ bytes, t = .litStr bytes) := by
  cases rep with
  | litNat cell rl =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ _ hargs; injection hargs with hx _
    exact .inl ⟨_, _, rfl, hx.symm, rl⟩
  | litStr cell _ => exact .inr ⟨_, rfl⟩
  | bvar cell | sort cell _ | const cell _ _ | app cell _ _ | lam cell _ _
  | forallE cell _ _ | letE cell _ _ _ | proj cell _ _ =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc _
    exact absurd hc (by decide)

/-- The level at a pointer whose loaded value is a `KLevelNode`, by constructor. -/
theorem RepUniv.of_load {h : Heap F} {u : IxVMKUniv F} {p : SourceValue F}
    {c : String} {xs : List (SourceValue F)} (rep : RepIxVMKUniv h u p)
    (hl : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" c xs)) :
    (c = "Zero" ∧ xs = [] ∧ u = .zero) ∨
    (∃ x v, c = "Succ" ∧ xs = [x] ∧ u = .succ v ∧ RepIxVMKUniv h v x) ∨
    (∃ x y v w, c = "Max" ∧ xs = [x, y] ∧ u = .max v w ∧ RepIxVMKUniv h v x ∧
      RepIxVMKUniv h w y) ∨
    (∃ x y v w, c = "IMax" ∧ xs = [x, y] ∧ u = .imax v w ∧ RepIxVMKUniv h v x ∧
      RepIxVMKUniv h w y) ∨
    (∃ i, c = "Param" ∧ xs = [.field i] ∧ u = .param i) := by
  cases rep with
  | zero cell =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc hargs
    exact .inl ⟨hc.symm, hargs.symm, rfl⟩
  | succ cell r =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc hargs
    exact .inr (.inl ⟨_, _, hc.symm, hargs.symm, rfl, r⟩)
  | max cell r₁ r₂ =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc hargs
    exact .inr (.inr (.inl ⟨_, _, _, _, hc.symm, hargs.symm, rfl, r₁, r₂⟩))
  | imax cell r₁ r₂ =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc hargs
    exact .inr (.inr (.inr (.inl ⟨_, _, _, _, hc.symm, hargs.symm, rfl, r₁, r₂⟩)))
  | param cell =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc hargs
    exact .inr (.inr (.inr (.inr ⟨_, hc.symm, hargs.symm, rfl⟩)))

/-! ## The translation is a function -/

theorem Tr.det {κ : Bytes.Address → Ix.Kernel.Key .anon} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {t : IxVMKExpr F} {E₁ E₂ : KExpr}
    (h₁ : Tr κ d Γ k t E₁) (h₂ : Tr κ d Γ k t E₂) : E₁ = E₂ := by
  induction h₁ generalizing E₂ with
  | bvarLocal hi => cases h₂ <;> first | rfl | omega
  | bvarFree hk hd => cases h₂ <;> first | rfl | omega
  | sort => cases h₂; rfl
  | const => cases h₂; rfl
  | app _ _ ihf iha => cases h₂ with | app hf ha => rw [ihf hf, iha ha]
  | lam _ _ iht ihb => cases h₂ with | lam ht hb => rw [iht ht, ihb hb]
  | forallE _ _ iht ihb => cases h₂ with | forallE ht hb => rw [iht ht, ihb hb]
  | litNat => cases h₂; rfl

/-! ## `UInt64::eq` -/

/-- **`UInt64::eq` answers `1` only on equal words**, read off its generated
mirror (`Mirrors.«UInt64::eq».of_eval`). -/
theorem u64Eq_one {x y : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt64::eq" [x, y] h (.field 1) h' cs)
    {w₁ w₂ : UInt64} (r₁ : RepU64 h w₁ x) (r₂ : RepU64 h w₂ y) : w₁ = w₂ := by
  obtain ⟨k0, hk⟩ := Mirrors.«UInt64::eq».of_eval ev.erase
  have run := hk (k0 + 2) (by omega)
  subst r₁ r₂
  simp only [List.range, List.range.loop, List.map, Mirrors.«UInt64::eq»,
    Mirrors.«UInt8::to_field», evalBinOp, bind, Option.bind] at run
  split at run
  · rename_i heq
    simp only [Value.tuple.injEq, List.cons.injEq, Value.field.injEq, sub_eq_zero,
      and_true] at heq
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := heq
    have hb : ∀ {m n : Nat}, m < 256 → n < 256 → ((m : Nat) : F) = ((n : Nat) : F) → m = n :=
      fun hm hn e => natCast_lt_inj (by omega) (by omega) e
    have e0 := hb (by omega) (by omega) h0
    have e1 := hb (by omega) (by omega) h1
    have e2 := hb (by omega) (by omega) h2
    have e3 := hb (by omega) (by omega) h3
    have e4 := hb (by omega) (by omega) h4
    have e5 := hb (by omega) (by omega) h5
    have e6 := hb (by omega) (by omega) h6
    have e7 := hb (by omega) (by omega) h7
    have hw₁ := w₁.toNat_lt
    have hw₂ := w₂.toNat_lt
    apply UInt64.toNat_inj.mp
    simp only [pow_zero, pow_one, Nat.div_one] at e0 e1 e2 e3 e4 e5 e6 e7
    norm_num at e0 e1 e2 e3 e4 e5 e6 e7
    omega
  · simp at run

/-! ## `level_struct_eq` -/

theorem RepUniv.zero_of_load {h : Heap F} {u : IxVMKUniv F} {p : SourceValue F}
    (rep : RepIxVMKUniv h u p)
    (hl : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Zero" [])) : u = .zero := by
  rcases RepUniv.of_load rep hl with ⟨-, -, rfl⟩ | ⟨_, _, hc, -⟩ | ⟨_, _, _, _, hc, -⟩ |
    ⟨_, _, _, _, hc, -⟩ | ⟨_, hc, -⟩
  · rfl
  all_goals exact absurd hc (by decide)

theorem RepUniv.succ_of_load {h : Heap F} {u : IxVMKUniv F} {p x : SourceValue F}
    (rep : RepIxVMKUniv h u p)
    (hl : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Succ" [x])) :
    ∃ v, u = .succ v ∧ RepIxVMKUniv h v x := by
  rcases RepUniv.of_load rep hl with ⟨hc, -⟩ | ⟨_, _, -, hx, rfl, r⟩ | ⟨_, _, _, _, hc, -⟩ |
    ⟨_, _, _, _, hc, -⟩ | ⟨_, hc, -⟩
  · exact absurd hc (by decide)
  · injection hx with hx; subst hx; exact ⟨_, rfl, r⟩
  all_goals exact absurd hc (by decide)

theorem RepUniv.max_of_load {h : Heap F} {u : IxVMKUniv F} {p x y : SourceValue F}
    (rep : RepIxVMKUniv h u p)
    (hl : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Max" [x, y])) :
    ∃ v w, u = .max v w ∧ RepIxVMKUniv h v x ∧ RepIxVMKUniv h w y := by
  rcases RepUniv.of_load rep hl with ⟨hc, -⟩ | ⟨_, _, hc, -⟩ | ⟨_, _, _, _, -, hx, rfl, r₁, r₂⟩ |
    ⟨_, _, _, _, hc, -⟩ | ⟨_, hc, -⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · simp only [List.cons.injEq, and_true] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨_, _, rfl, r₁, r₂⟩
  all_goals exact absurd hc (by decide)

theorem RepUniv.imax_of_load {h : Heap F} {u : IxVMKUniv F} {p x y : SourceValue F}
    (rep : RepIxVMKUniv h u p)
    (hl : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "IMax" [x, y])) :
    ∃ v w, u = .imax v w ∧ RepIxVMKUniv h v x ∧ RepIxVMKUniv h w y := by
  rcases RepUniv.of_load rep hl with ⟨hc, -⟩ | ⟨_, _, hc, -⟩ | ⟨_, _, _, _, hc, -⟩ |
    ⟨_, _, _, _, -, hx, rfl, r₁, r₂⟩ | ⟨_, hc, -⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · simp only [List.cons.injEq, and_true] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨_, _, rfl, r₁, r₂⟩
  · exact absurd hc (by decide)

theorem RepUniv.param_of_load {h : Heap F} {u : IxVMKUniv F} {p x : SourceValue F}
    (rep : RepIxVMKUniv h u p)
    (hl : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Param" [x])) :
    ∃ i, x = .field i ∧ u = .param i := by
  rcases RepUniv.of_load rep hl with ⟨hc, -⟩ | ⟨_, _, hc, -⟩ | ⟨_, _, _, _, hc, -⟩ |
    ⟨_, _, _, _, hc, -⟩ | ⟨_, -, hx, rfl⟩
  all_goals first | exact absurd hc (by decide) | skip
  injection hx with hx; exact ⟨_, hx, rfl⟩

/-- **`level_struct_eq` answers `0` or `1`, and `1` only on equal levels.** -/
theorem levelStructEq_sound : ∀ (N : Nat) {a b : SourceValue F} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}, calls.length < N →
    ObsFn W "KernelLevels::level_struct_eq" [a, b] h r h' calls →
    (r = .field 0 ∨ r = .field 1) ∧
      (r = .field 1 → ∀ u v, RepIxVMKUniv h u a → RepIxVMKUniv h v b → u = v)
  | 0, _, _, _, _, _, _, hlen, _ => absurd hlen (Nat.not_lt_zero _)
  | N + 1, a, b, h, h', r, calls, hlen, ev => by
    cases Obs.«KernelLevels::level_struct_eq».obs ev
    case Zero_Zero ld12 ld31 he _ _ =>
      subst he
      refine ⟨.inr rfl, fun _ u v ru rv => ?_⟩
      rw [RepUniv.zero_of_load ru ld12, RepUniv.zero_of_load rv ld31]
    case Succ_Succ x y cs ld12 ld72 ev90 hc =>
      subst hc
      simp only [List.length_cons] at hlen
      have ih := levelStructEq_sound N (by omega) ev90
      refine ⟨ih.1, fun hr u v ru rv => ?_⟩
      obtain ⟨u', rfl, ru'⟩ := RepUniv.succ_of_load ru ld12
      obtain ⟨v', rfl, rv'⟩ := RepUniv.succ_of_load rv ld72
      rw [ih.2 hr u' v' ru' rv']
    case Max_Max x1 x2 y1 y2 p q m cs₁ cs₂ ld12 ld143 ev174 ev196 op hc =>
      subst hc
      simp only [List.length_cons, List.length_append] at hlen
      have ih₁ := levelStructEq_sound N (by omega) ev174
      have ih₂ := levelStructEq_sound N (by omega) ev196
      obtain ⟨p', q', rfl, rfl, rfl⟩ := evalBinOp_mul_inv op
      have hp : p' = 0 ∨ p' = 1 := by
        rcases ih₁.1 with h0 | h1
        · injection h0 with h0; exact .inl h0
        · injection h1 with h1; exact .inr h1
      have hq : q' = 0 ∨ q' = 1 := by
        rcases ih₂.1 with h0 | h1
        · injection h0 with h0; exact .inl h0
        · injection h1 with h1; exact .inr h1
      refine ⟨by rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp,
        fun hr u v ru rv => ?_⟩
      have h11 : p' = 1 ∧ q' = 1 := by
        injection hr with hr
        rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp at hr ⊢
      obtain ⟨rfl, rfl⟩ := h11
      obtain ⟨u1, u2, rfl, ru1, ru2⟩ := RepUniv.max_of_load ru ld12
      obtain ⟨v1, v2, rfl, rv1, rv2⟩ := RepUniv.max_of_load rv ld143
      have ext := ev174.heap_extends
      rw [ih₁.2 rfl u1 v1 ru1 rv1, ih₂.2 rfl u2 v2 (ru2.mono ext) (rv2.mono ext)]
    case IMax_IMax x1 x2 y1 y2 p q m cs₁ cs₂ ld12 ld249 ev280 ev302 op hc =>
      subst hc
      simp only [List.length_cons, List.length_append] at hlen
      have ih₁ := levelStructEq_sound N (by omega) ev280
      have ih₂ := levelStructEq_sound N (by omega) ev302
      obtain ⟨p', q', rfl, rfl, rfl⟩ := evalBinOp_mul_inv op
      have hp : p' = 0 ∨ p' = 1 := by
        rcases ih₁.1 with h0 | h1
        · injection h0 with h0; exact .inl h0
        · injection h1 with h1; exact .inr h1
      have hq : q' = 0 ∨ q' = 1 := by
        rcases ih₂.1 with h0 | h1
        · injection h0 with h0; exact .inl h0
        · injection h1 with h1; exact .inr h1
      refine ⟨by rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp,
        fun hr u v ru rv => ?_⟩
      have h11 : p' = 1 ∧ q' = 1 := by
        injection hr with hr
        rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp at hr ⊢
      obtain ⟨rfl, rfl⟩ := h11
      obtain ⟨u1, u2, rfl, ru1, ru2⟩ := RepUniv.imax_of_load ru ld12
      obtain ⟨v1, v2, rfl, rv1, rv2⟩ := RepUniv.imax_of_load rv ld249
      have ext := ev280.heap_extends
      rw [ih₁.2 rfl u1 v1 ru1 rv1, ih₂.2 rfl u2 v2 (ru2.mono ext) (rv2.mono ext)]
    case Param_Param_n0 x y ld12 ld350 op he _ _ =>
      subst he
      refine ⟨.inr rfl, fun _ u v ru rv => ?_⟩
      obtain ⟨i, rfl, rfl⟩ := RepUniv.param_of_load ru ld12
      obtain ⟨j, rfl, rfl⟩ := RepUniv.param_of_load rv ld350
      obtain ⟨_, _, hx, hy, hz⟩ := evalBinOp_sub_inv op
      injection hx with hx; injection hy with hy; subst hx hy
      rw [field_sub_eq_zero hz.symm]
    all_goals
      subst ‹r = .field 0›
      exact ⟨.inl rfl, fun h => absurd h.symm field_one_ne_zero⟩

/-! ## `klimbs_eq` and `literal_eq` -/

/-- A represented list's cells carry the list's enum name. -/
theorem RepList.enum_of_load {α : Type} {enumName : String}
    {R : Heap F → α → SourceValue F → Prop} {h : Heap F} {xs : List α} {p : SourceValue F}
    {n c : String} {vs : List (SourceValue F)}
    (rep : RepList enumName R h xs p) (hl : loadValue h p = .ok (.construct n c vs)) :
    n = enumName := by
  cases rep with
  | nil cell =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with hn _ _; exact hn.symm
  | cons cell _ _ =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with hn _ _; exact hn.symm

/-- **`klimbs_eq` answers `1` only on equal limb lists.** The list's enum name is
a parameter: `klimbs_eq` loads cells of `Lists::Node<[Field; 8]>`, so a list
represented under any other name has no derivation reading it. -/
theorem klimbsEq_sound : ∀ (N : Nat) {E : String} {a b : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}, calls.length < N →
    ObsFn W "KernelLevels::klimbs_eq" [a, b] h (.field 1) h' calls →
    ∀ xs ys, RepList E RepU64 h xs a → RepList E RepU64 h ys b → xs = ys
  | 0, _, _, _, _, _, _, hlen, _ => absurd hlen (Nat.not_lt_zero _)
  | N + 1, E, a, b, h, h', calls, hlen, ev => by
    intro xs ys rx ry
    cases Obs.«KernelLevels::klimbs_eq».obs ev
    case Nil_Nil ld12 ld31 _ _ _ =>
      obtain rfl := RepList.enum_of_load rx ld12
      rw [RepList.nil_of_load rx ld12, RepList.nil_of_load ry ld31]
    case Cons_Cons_n1 x xr y yr m cs₁ cs₂ ld12 ld77 ev118 ev154 hc =>
      subst hc
      simp only [List.length_cons, List.length_append] at hlen
      obtain rfl := RepList.enum_of_load rx ld12
      obtain ⟨z, zs, rfl, rz, rzs⟩ := RepList.cons_of_load rx ld12
      obtain ⟨w, ws, rfl, rw', rws⟩ := RepList.cons_of_load ry ld77
      have ext := ev118.heap_extends
      rw [u64Eq_one ev118 rz rw', klimbsEq_sound N (by omega) ev154 zs ws
        (rzs.mono repU64_heapMono₂ ext) (rws.mono repU64_heapMono₂ ext)]
    all_goals exact absurd ‹(Value.field 1 : SourceValue F) = .field 0› field_one_ne_zero

/-- **`literal_eq` on two `Nat` literals answers `1` only on equal limb lists.** -/
theorem literalEq_nat_sound {E : String} {la lb : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn W "KernelLevels::literal_eq"
      [.construct "KernelTypes::KLiteral" "Nat" [la], .construct "KernelTypes::KLiteral" "Nat" [lb]]
      h (.field 1) h' calls)
    {xs ys : List UInt64} (rx : RepList E RepU64 h xs la) (ry : RepList E RepU64 h ys lb) :
    xs = ys := by
  cases Obs.«KernelLevels::literal_eq».obs ev
  case Nat_Nat x y cs hv15 hv36 ev48 hc =>
    injection hv15 with _ _ hv15; injection hv15 with hv15
    injection hv36 with _ _ hv36; injection hv36 with hv36
    subst hv15 hv36
    exact klimbsEq_sound _ (Nat.lt_succ_self _) ev48 xs ys rx ry
  case Nat_other hne _ _ _ => exact absurd rfl (hne [lb] rfl)
  case Str_Str hne _ _ _ _ => exact absurd rfl (hne [la] rfl)
  case Str_other hne _ _ _ _ _ => exact absurd rfl (hne [la] rfl)

/-! ## `kexpr_struct_eq` -/

/-- **`kexpr_struct_eq` answers `1` only on terms with equal images**: if it
returns `1` on `a` and `b`, and they represent `A` and `B` at the same local
depth, then `A = B`. -/
theorem structEq_sound (c : Ctx) (hA : Assumed c) : ∀ (N : Nat) {a b : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}, calls.length < N →
    ObsFn W "KernelCheck::kexpr_struct_eq" [a, b] h (.field 1) h' calls →
    ∀ ta tb, RepK h ta a → RepK h tb b →
      ∀ d Γ k A B, Tr c.κ d Γ k ta A → Tr c.κ d Γ k tb B → A = B
  | 0, _, _, _, _, _, hlen, _ => absurd hlen (Nat.not_lt_zero _)
  | N + 1, a, b, h, h', calls, hlen, ev => by
    intro ta tb rta rtb d Γ k A B tA tB
    cases Obs.«KernelCheck::kexpr_struct_eq».obs ev
    case BVar_BVar_n0 x y ld12 ld36 op _ _ _ =>
      obtain ⟨i, rfl, rfl⟩ := RepK.bvar_of_load rta ld12
      obtain ⟨j, rfl, rfl⟩ := RepK.bvar_of_load rtb ld36
      obtain ⟨_, _, hx, hy, hz⟩ := evalBinOp_sub_inv op
      injection hx with hx; injection hy with hy; subst hx hy
      obtain rfl := field_sub_eq_zero hz.symm
      exact Tr.det tA tB
    case Srt_Srt x y cs ld12 ld112 ev130 hc =>
      subst hc
      simp only [List.length_cons] at hlen
      obtain ⟨u, rfl, ru⟩ := RepK.sort_of_load rta ld12
      obtain ⟨v, rfl, rv⟩ := RepK.sort_of_load rtb ld112
      obtain rfl := (levelStructEq_sound N (by omega) ev130).2 rfl u v ru rv
      exact Tr.det tA tB
    case Const_Const_n1 x xl y yl m cs₁ cs₂ ld12 ld183 ev215 ev241 hc =>
      obtain ⟨aa, als, rfl, haa, -⟩ := RepK.const_of_load rta ld12
      obtain ⟨bb, bls, rfl, hbb, -⟩ := RepK.const_of_load rtb ld183
      obtain rfl := hA.addressEq _ _ _ _ _ _ ev215 aa bb haa hbb rfl
      obtain ⟨rfl, rfl⟩ := Tr.const_inv tA
      obtain ⟨rfl, rfl⟩ := Tr.const_inv tB
      rfl
    case App_App_n1 fa xa fb xb m cs₁ cs₂ ld12 ld301 ev333 ev359 hc =>
      subst hc
      simp only [List.length_cons, List.length_append] at hlen
      obtain ⟨f₁, x₁, rfl, rf₁, rx₁⟩ := RepK.app_of_load rta ld12
      obtain ⟨f₂, x₂, rfl, rf₂, rx₂⟩ := RepK.app_of_load rtb ld301
      have ext := ev333.heap_extends
      cases tA with
      | app tf₁ tx₁ =>
        cases tB with
        | app tf₂ tx₂ =>
          rw [structEq_sound c hA N (by omega) ev333 _ _ rf₁ rf₂ d Γ k _ _ tf₁ tf₂,
            structEq_sound c hA N (by omega) ev359 _ _ (rx₁.mono ext) (rx₂.mono ext) d Γ k _ _
              tx₁ tx₂]
    case Lam_Lam_n1 ta' ba tb' bb m cs₁ cs₂ ld12 ld419 ev451 ev477 hc =>
      subst hc
      simp only [List.length_cons, List.length_append] at hlen
      obtain ⟨t₁, b₁, rfl, rt₁, rb₁⟩ := RepK.lam_of_load rta ld12
      obtain ⟨t₂, b₂, rfl, rt₂, rb₂⟩ := RepK.lam_of_load rtb ld419
      have ext := ev451.heap_extends
      cases tA with
      | lam tt₁ tb₁ =>
        cases tB with
        | lam tt₂ tb₂ =>
          rw [structEq_sound c hA N (by omega) ev451 _ _ rt₁ rt₂ d Γ k _ _ tt₁ tt₂,
            structEq_sound c hA N (by omega) ev477 _ _ (rb₁.mono ext) (rb₂.mono ext) d Γ (k + 1)
              _ _ tb₁ tb₂]
    case Forall_Forall_n1 da xa db xb m cs₁ cs₂ ld12 ld537 ev569 ev595 hc =>
      subst hc
      simp only [List.length_cons, List.length_append] at hlen
      obtain ⟨t₁, b₁, rfl, rt₁, rb₁⟩ := RepK.forallE_of_load rta ld12
      obtain ⟨t₂, b₂, rfl, rt₂, rb₂⟩ := RepK.forallE_of_load rtb ld537
      have ext := ev569.heap_extends
      cases tA with
      | forallE tt₁ tb₁ =>
        cases tB with
        | forallE tt₂ tb₂ =>
          rw [structEq_sound c hA N (by omega) ev569 _ _ rt₁ rt₂ d Γ k _ _ tt₁ tt₂,
            structEq_sound c hA N (by omega) ev595 _ _ (rb₁.mono ext) (rb₂.mono ext) d Γ (k + 1)
              _ _ tb₁ tb₂]
    case Let_Let_n1_n1 ld12 _ _ _ _ _ =>
      obtain ⟨_, _, _, rfl⟩ := RepK.let_of_load rta ld12
      exact (Tr.let_inv tA).elim
    case Lit_Lit x y cs ld12 ld820 ev838 hc =>
      rcases RepK.lit_of_load rta ld12 with ⟨l₁, p₁, rfl, rfl, rl₁⟩ | ⟨_, rfl⟩
      · rcases RepK.lit_of_load rtb ld820 with ⟨l₂, p₂, rfl, rfl, rl₂⟩ | ⟨_, rfl⟩
        · obtain rfl := literalEq_nat_sound ev838 rl₁ rl₂
          exact Tr.det tA tB
        · cases tB
      · cases tA
    case Proj_Proj_n1_n0 ld12 _ _ _ _ _ =>
      obtain ⟨_, _, _, rfl⟩ := RepK.proj_of_load rta ld12
      exact (Tr.proj_inv tA).elim
    all_goals exact absurd ‹(Value.field 1 : SourceValue F) = .field 0› field_one_ne_zero

end IxVM.Refinement.Core
