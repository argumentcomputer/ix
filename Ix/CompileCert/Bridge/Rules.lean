import Ix.CompileCert.Bridge.Denote

/-!
# M7 X2: conversion soundness in the checker's model, rule by rule

`SemEq cval env φ ρ a b`: `a` and `b` denote the same set (both denote; the public reading is a
partial function, `Kernel.Denotes_functional`). It is an equivalence on denoting terms and a
congruence for application, projection and the binders (domains equal, bodies equal on the
domain, regimes equal).

Every rule of X1's `Conv` is sound **under its own semantic premise**, and only under it (an
untyped β or η is false in the set model: `app (lamR 1 A F) x = ∅` off the domain,
`app_lamR_of_not_mem`; see the report §1.3):

* `semEq_beta`: `(λ^m t. b) a ≡ b[0 := a]` when the argument lies in the redex's own domain;
  `semEq_beta_graph`: in the graph regime that premise follows from the application's typing
  (`⟦λ⟧ ∈ piR v A B`, `⟦a⟧ ∈ A`, domain uniqueness);
* `semEq_eta`: `λ^m t. f↑ #0 ≡ f` when `⟦f⟧ ∈ piR (regime m) ⟦t⟧ B`;
* `semEq_delta`: `c.{us} ≡ v[ps := us]` for an installed definition `c := v` of a strong model
  (`definition_values` and `denotes_levels`);
* `semEq_theorem`: an installed theorem with an equation statement, at a typed instance, relates
  its two sides (`StrongInstalledModel.theorem_eq`; how library lemmas enter a semantic proof).
-/

namespace Ix.CompileCert.Bridge

open Kernel (Denotes push)
open Kernel.SetTheory Kernel.SetModel

universe u

section SemEq

variable {V : Type u} [Kernel.SetTheory V] {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

variable (cval env φ) in
/-- Two terms denote the same set. -/
def SemEq (ρ : Nat → V) (a b : Kernel.Expr) : Prop :=
  ∃ v, Denotes cval env φ ρ a v ∧ Denotes cval env φ ρ b v

theorem SemEq.refl {ρ : Nat → V} {a : Kernel.Expr} {v : V} (h : Denotes cval env φ ρ a v) :
    SemEq cval env φ ρ a a := ⟨v, h, h⟩

theorem SemEq.symm {ρ : Nat → V} {a b : Kernel.Expr} (h : SemEq cval env φ ρ a b) :
    SemEq cval env φ ρ b a := let ⟨v, ha, hb⟩ := h; ⟨v, hb, ha⟩

theorem SemEq.trans {ρ : Nat → V} {a b c : Kernel.Expr} (h1 : SemEq cval env φ ρ a b)
    (h2 : SemEq cval env φ ρ b c) : SemEq cval env φ ρ a c := by
  obtain ⟨v, ha, hb⟩ := h1
  obtain ⟨w, hb', hc⟩ := h2
  obtain rfl := Kernel.Denotes_functional hb hb'
  exact ⟨v, ha, hc⟩

theorem SemEq.left {ρ : Nat → V} {a b : Kernel.Expr} (h : SemEq cval env φ ρ a b) :
    ∃ v, Denotes cval env φ ρ a v := let ⟨v, ha, _⟩ := h; ⟨v, ha⟩

theorem SemEq.right {ρ : Nat → V} {a b : Kernel.Expr} (h : SemEq cval env φ ρ a b) :
    ∃ v, Denotes cval env φ ρ b v := let ⟨v, _, hb⟩ := h; ⟨v, hb⟩

/-- Read the common value off one side. -/
theorem SemEq.value {ρ : Nat → V} {a b : Kernel.Expr} {v : V} (h : SemEq cval env φ ρ a b)
    (ha : Denotes cval env φ ρ a v) : Denotes cval env φ ρ b v := by
  obtain ⟨w, ha', hb⟩ := h
  rw [Kernel.Denotes_functional ha ha']; exact hb

/-! ### Congruences -/

theorem SemEq.app {ρ : Nat → V} {f f' a a' : Kernel.Expr} (hf : SemEq cval env φ ρ f f')
    (ha : SemEq cval env φ ρ a a') : SemEq cval env φ ρ (.app f a) (.app f' a') := by
  obtain ⟨F, h1, h2⟩ := hf
  obtain ⟨X, h3, h4⟩ := ha
  exact ⟨_, .app h1 h3, .app h2 h4⟩

/-- Two lists related pointwise. -/
inductive KForall2 {α : Type} (R : α → α → Prop) : List α → List α → Prop
  | nil : KForall2 R [] []
  | cons {a b : α} {as bs : List α} : R a b → KForall2 R as bs → KForall2 R (a :: as) (b :: bs)

theorem SemEq.appN {ρ : Nat → V} : ∀ {f f' : Kernel.Expr} {as as' : List Kernel.Expr},
    SemEq cval env φ ρ f f' → KForall2 (SemEq cval env φ ρ) as as' →
      SemEq cval env φ ρ (Kernel.Expr.mkAppN f as) (Kernel.Expr.mkAppN f' as')
  | _, _, [], [], hf, .nil => hf
  | _, _, _ :: _, _ :: _, hf, .cons ha hs => by
    simp only [Kernel.Expr.mkAppN]; exact SemEq.appN (hf.app ha) hs

theorem SemEq.proj {ρ : Nat → V} {s : Kernel.Name} {i : Nat} {e e' : Kernel.Expr} {X : V}
    (he : SemEq cval env φ ρ e e') (h : Denotes cval env φ ρ (.proj s i e) X) :
    SemEq cval env φ ρ (.proj s i e) (.proj s i e') := by
  refine ⟨X, h, ?_⟩
  cases h with
  | proj_table ht hd => exact .proj_table ht (he.value hd)
  | proj_fst ht hd => exact .proj_fst ht (he.value hd)
  | proj_snd ht hd => exact .proj_snd ht (he.value hd)

/-- The λ congruence: equal domains, bodies equal on the domain, equal regimes. -/
theorem SemEq.lam {ρ : Nat → V} {t t' b b' : Kernel.Expr} {m m' : Kernel.BinderMeta} {Λ : V}
    (hl : Denotes cval env φ ρ (.lam t b m) Λ) (ht : SemEq cval env φ ρ t t')
    (hb : ∀ A, Denotes cval env φ ρ t A → ∀ x, x ∈ˢ A → SemEq cval env φ (push x ρ) b b')
    (hm : Kernel.regime φ m.pw = Kernel.regime φ m'.pw) :
    SemEq cval env φ ρ (.lam t b m) (.lam t' b' m') := by
  refine ⟨Λ, hl, ?_⟩
  cases hl with
  | lam hA hF hP =>
    rw [hm]
    exact .lam (ht.value hA) (fun x hx => (hb _ hA x hx).value (hF x hx)) (by rw [← hm]; exact hP)

/-- The ∀ congruence. -/
theorem SemEq.pi {ρ : Nat → V} {t t' b b' : Kernel.Expr} {m m' : Kernel.BinderMeta} {P : V}
    (hl : Denotes cval env φ ρ (.forallE t b m) P) (ht : SemEq cval env φ ρ t t')
    (hb : ∀ A, Denotes cval env φ ρ t A → ∀ x, x ∈ˢ A → SemEq cval env φ (push x ρ) b b')
    (hm : Kernel.regime φ m.pw = Kernel.regime φ m'.pw) :
    SemEq cval env φ ρ (.forallE t b m) (.forallE t' b' m') := by
  refine ⟨P, hl, ?_⟩
  cases hl with
  | pi hA hB hP =>
    rw [hm]
    exact .pi (ht.value hA) (fun x hx => (hb _ hA x hx).value (hB x hx)) (by rw [← hm]; exact hP)

/-! ### β -/

/-- An abstraction applied on its domain computes, in both regimes. -/
theorem app_lam_value {A X : V} {F : V → V} {r : Nat} (hX : X ∈ˢ A)
    (hP : r = 0 → ∀ x, x ∈ˢ A → F x = pt) : app (lamR r A F) X = F X := by
  by_cases hr : r = 0
  · rw [hr, lamR_zero, app_pt]; exact (hP hr X hX).symm
  · exact app_lamR_pos hr hX

/-- **β**: a redex whose argument lies in its abstraction's own domain denotes what the
substituted body denotes. -/
theorem semEq_beta {ρ : Nat → V} {t b a : Kernel.Expr} {m : Kernel.BinderMeta} {Λ X : V}
    (hl : Denotes cval env φ ρ (.lam t b m) Λ) (ha : Denotes cval env φ ρ a X)
    (hdom : ∀ A, Denotes cval env φ ρ t A → X ∈ˢ A) :
    SemEq cval env φ ρ (.app (.lam t b m) a) (b.instantiate1Lift a 0) := by
  cases hl with
  | @lam _ _ _ _ A F hA hF hP =>
    have hX := hdom A hA
    refine ⟨F X, ?_, denotes_inst0 (hF X hX) ha⟩
    have happ : Denotes cval env φ ρ (.app (.lam t b m) a) (app (lamR (Kernel.regime φ m.pw) A F) X) :=
      .app (.lam hA hF hP) ha
    rwa [app_lam_value hX hP] at happ

/-- A graph-regime abstraction in a graph-regime product has the product's domain. -/
theorem lam_dom_of_mem {A A' : V} {F B : V → V} {r v : Nat} (hr : r ≠ 0) (hv : v ≠ 0)
    (hmem : lamR r A F ∈ˢ piR v A' B) : A = A' := by
  have hown : lamR r A F ∈ˢ piR r A (fun x => sing (F x)) :=
    lamR_mem (fun x _ => mem_sing.mpr rfl)
  exact piR_dom_unique hr hv hown hmem

/-- **β in the graph regime**: an application typed at a graph-regime product (`⟦λ⟧ ∈ piR v A' B`,
`⟦a⟧ ∈ A'`, `v ≠ 0`) whose abstraction is graph-regime needs no further premise. -/
theorem semEq_beta_graph {ρ : Nat → V} {t b a : Kernel.Expr} {m : Kernel.BinderMeta} {Λ X A' : V}
    {B : V → V} {v : Nat} (hl : Denotes cval env φ ρ (.lam t b m) Λ) (ha : Denotes cval env φ ρ a X)
    (hpos : Kernel.regime φ m.pw ≠ 0) (hv : v ≠ 0) (hmem : Λ ∈ˢ piR v A' B) (hX : X ∈ˢ A') :
    SemEq cval env φ ρ (.app (.lam t b m) a) (b.instantiate1Lift a 0) := by
  refine semEq_beta hl ha ?_
  intro A hA
  cases hl with
  | @lam _ _ _ _ A₀ F hA₀ _ _ =>
    obtain rfl := Kernel.Denotes_functional hA hA₀
    rw [lam_dom_of_mem hpos hv hmem]; exact hX

/-! ### η -/

/-- **η**: an abstraction of a member of the product over its own domain, at its own regime, is
that member. -/
theorem semEq_eta {ρ : Nat → V} {t f : Kernel.Expr} {m : Kernel.BinderMeta} {A F : V} {B : V → V}
    (ht : Denotes cval env φ ρ t A) (hf : Denotes cval env φ ρ f F)
    (hmem : F ∈ˢ piR (Kernel.regime φ m.pw) A B) :
    SemEq cval env φ ρ (.lam t (.app (Kernel.Expr.liftLooseBVars 1 0 f) (.bvar 0)) m) f := by
  refine ⟨F, ?_, hf⟩
  have hbody : ∀ x, x ∈ˢ A →
      Denotes cval env φ (push x ρ) (.app (Kernel.Expr.liftLooseBVars 1 0 f) (.bvar 0)) (app F x) :=
    fun x _ => .app (denotes_lift_push hf x) (.bvar (ρ := push x ρ) (i := 0))
  have hP : Kernel.regime φ m.pw = 0 → ∀ x, x ∈ˢ A → app F x = pt := by
    intro h0 x _
    rw [h0] at hmem
    rw [eq_pt_of_mem_piR_zero hmem, app_pt]
  have hlam := Denotes.lam ht hbody hP
  rwa [lamR_eta hmem] at hlam

/-! ### δ, and installed theorems -/

variable (strong : StrongInstalledModel V env)

/-- **δ**: an installed definition's constant, at universe arguments `us`, denotes what its
installed value instantiated at `us` denotes. -/
theorem semEq_delta {ρ : Nat → V} {c : Kernel.Name} {header : Kernel.ConstantVal}
    {value : Kernel.Expr} {hint : Kernel.ReducibilityHint} {us : List Kernel.Level}
    (lookup : env.find? c = some (.defnInfo header value hint))
    (arity : us.length = header.levelParams.length) :
    SemEq strong.public.cval env φ ρ (.const c us)
      (value.instantiateLevelParams header.levelParams us) := by
  have present := Kernel.Semantics.Env.find?_mem lookup
  have hname : header.name = c := Kernel.Semantics.Env.find?_name lookup
  have hconst : Denotes strong.public.cval env φ ρ (.const c us)
      (strong.public.cval c (Kernel.Level.substFn φ header.levelParams us)) :=
    .const lookup arity
  refine ⟨_, hconst, ?_⟩
  have hval := strong.definition_values header value hint present
    (Kernel.Level.substFn φ header.levelParams us) ρ
  rw [hname] at hval
  exact denotes_levels (cvalLocal_of_strong strong) header.levelParams us hval

/-- **Installed theorems are model facts**: an installed theorem whose statement, at a typed
instance, is an equation, relates the two sides' values (`theorem_eq`). -/
theorem semEq_theorem {header : Kernel.ConstantVal} {proof : Kernel.Expr}
    (present : Kernel.ConstantInfo.thmInfo header proof ∈ env.consts)
    {ρ finalρ : Nat → V} {arguments : List V} {level : Kernel.Level}
    {carrier left right : Kernel.Expr}
    (typed : InstalledTelescope strong.public.cval env φ ρ header.type arguments finalρ
      (.app (.app (.app (.const Kernel.eqName [level]) carrier) left) right))
    {lv : V} (hleft : Denotes strong.public.cval env φ finalρ left lv)
    (hright : ∃ rv, Denotes strong.public.cval env φ finalρ right rv) :
    SemEq strong.public.cval env φ finalρ left right := by
  obtain ⟨rv, hr⟩ := hright
  have := strong.theorem_eq header proof present typed hleft hr
  subst this
  exact ⟨lv, hleft, hr⟩

end SemEq

end Ix.CompileCert.Bridge
