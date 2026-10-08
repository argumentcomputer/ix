import Ix.CompileCert.Bridge
import IxC.Kernel.Model.Denotes
import IxC.Kernel.Model.Annot.BitLemmas
import IxC.Kernel.Semantics.Tower.TowerLeaf
import IxC.Kernel.Verify.Abstract
import IxC.Kernel.Verify.Shift

/-!
# M7 L3-pj: installed terms have graded public readings

X2's `Graded` (`Bridge/Graded.lean`) is the public reading's counterpart of IxC's `WellDenoted`:
every application applies a member of a product to a member of its domain. IxC's install
establishes the internal grading of every stored type (`EnvModelM.type_wellDenotedV`) and of every
leaf (`EnvModel.acval_wellDenoted`, `EnvModelM.acval_validV`), and a stored definition's value reads
to its own leaf (`EnvModelM.defn_reads`). This module transports the internal grading to the public
one, along IxC's own bridge `Denotes_of_denoteMeta` (same induction, one more conjunct per clause):

* `graded_of_denoteMeta`: wherever `denoteMeta` reads a term to a graded, bit-valid reading, the
  term's closure is `Graded` at the interpreted leaves;
* `installed_type_graded`: an installed constant's type is graded at every assignment and
  valuation (the law `InstalledGraded` of the report's ledger, types);
* `installed_value_graded`: an installed definition's value likewise (values).

The per-pass proofs use them to read typing off installed terms: an application inside an
installed type or value has its argument in its function's domain.
-/

namespace Ix.CompileCert.Pj

open Kernel.Model Kernel.Semantics Kernel.SetModel Kernel.Verify Kernel.SetTheory
open Kernel.Semantics (AnnotTerm)
open Kernel.Expr (closeN)
open Bridge (Graded)

universe u

variable {V : Type u} [Kernel.SetTheory V]

private theorem wdv_fst {ρ : Nat → V} {e : AnnotTerm}
    (h : WellDenotedV V ρ (.fst e)) : WellDenotedV V ρ e := by
  obtain ⟨h1, h2⟩ := h
  rw [WellDenoted_fst] at h1
  rw [AnnotValid_fst] at h2
  exact ⟨h1.1, h2⟩

private theorem wdv_snd {ρ : Nat → V} {e : AnnotTerm}
    (h : WellDenotedV V ρ (.snd e)) : WellDenotedV V ρ e := by
  obtain ⟨h1, h2⟩ := h
  rw [WellDenoted_snd] at h1
  rw [AnnotValid_snd] at h2
  exact ⟨h1.1, h2⟩

private theorem fvarsBelow_zero_of_noFvar :
    ∀ {e : Kernel.Expr}, e.hasFvar = false → Kernel.Expr.fvarsBelow 0 e := by
  intro e
  induction e <;> simp_all [Kernel.Expr.fvarsBelow, Kernel.Expr.hasFvar]

/-- **The grading bridge**: a term whose `denoteMeta` reading is graded and bit-valid has a graded
public reading (its closure, at the interpreted leaves). -/
theorem graded_of_denoteMeta {acval : Kernel.Name → (Kernel.Name → Nat) → AnnotTerm}
    (hcl : ∀ n ψ, Kernel.Term.Term.Closed (acval n ψ).erase) {env : Kernel.Env} {φ : Kernel.Name → Nat} :
    ∀ (d : Nat) (e : Kernel.Expr) {ta : AnnotTerm},
      denoteMeta acval env φ d e = some ta →
      Kernel.Expr.fvarsBelow d e → e.looseBVarsBounded 0 = true →
      ∀ ρ : Nat → V, WellDenotedV V ρ ta →
        Graded (cvalOf (V := V) acval) env φ ρ (closeN d e) := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u =>
    intro ta _ _ _ ρ _
    show Graded _ _ _ _ (Kernel.Expr.sort u)
    trivial
  | case2 d idx ty =>
    intro ta _ _ _ ρ _
    show Graded _ _ _ _ (Kernel.Expr.bvar (0 + (d - 1 - idx)))
    trivial
  | case3 d n us ci hf hlen =>
    intro ta h hfb hlb ρ hw
    exact ⟨_, Denotes_of_denoteMeta hcl d (.const n us) h hfb hlb ρ hw⟩
  | case4 d n us ci hf hlen =>
    intro ta h
    rw [denoteMeta, hf] at h
    dsimp only at h
    simp [hlen] at h
  | case5 d n us hf =>
    intro ta h
    rw [denoteMeta, hf] at h
    exact nomatch h
  | case6 d ty body mb ihty ihbody =>
    intro ta h hfb hlb ρ hw
    have hwhole := Denotes_of_denoteMeta hcl d (.forallE ty body mb) h hfb hlb ρ hw
    obtain ⟨tA, bA, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
    have hfb' : Kernel.Expr.fvarsBelow d ty ∧ Kernel.Expr.fvarsBelow d body := hfb
    have hlb' : (ty.looseBVarsBounded 0 && body.looseBVarsBounded 1) = true := hlb
    rw [Bool.and_eq_true] at hlb'
    obtain ⟨hw1, hw2⟩ := hw
    rw [WellDenoted_pi] at hw1
    rw [AnnotValid_pi] at hw2
    have hA := Denotes_of_denoteMeta hcl d ty hta hfb'.1 hlb'.1 ρ ⟨hw1.1, hw2.1⟩
    show Graded _ _ _ _ (Kernel.Expr.forallE (closeN d ty 0) (closeN d body 1) mb)
    refine ⟨ihty hta hfb'.1 hlb'.1 ρ ⟨hw1.1, hw2.1⟩, _, hA, fun x hx => ?_, fun h0 x hx y hy => ?_⟩
    · rw [push_eq_cons]
      have hb := ihbody hba (Kernel.Expr.fvarsBelow_instantiate1 0 hfb'.2)
        (Ix.Kernel.looseBVarsBounded_instantiate1 body 0 hlb'.2) (cons x ρ)
        ⟨hw1.2 x hx, hw2.2.1 x hx⟩
      rwa [Kernel.Expr.closeN_instantiate1 body 0 hlb'.2 hfb'.2] at hb
    · have hbd := Denotes_of_denoteMeta hcl (d + 1) _ hba (Kernel.Expr.fvarsBelow_instantiate1 0 hfb'.2)
        (Ix.Kernel.looseBVarsBounded_instantiate1 body 0 hlb'.2) (cons x ρ) ⟨hw1.2 x hx, hw2.2.1 x hx⟩
      rw [Kernel.Expr.closeN_instantiate1 body 0 hlb'.2 hfb'.2, ← push_eq_cons] at hbd
      rw [Kernel.Denotes_functional hy hbd, univ_zero, push_eq_cons]
      rw [regime_eq_pwBit] at h0
      exact hw2.2.2 h0 x hx
  | case7 d ty body mb ihty ihbody =>
    intro ta h hfb hlb ρ hw
    obtain ⟨tA, bA, hta, hba, rfl⟩ := denoteMeta_lam_inv h
    have hfb' : Kernel.Expr.fvarsBelow d ty ∧ Kernel.Expr.fvarsBelow d body := hfb
    have hlb' : (ty.looseBVarsBounded 0 && body.looseBVarsBounded 1) = true := hlb
    rw [Bool.and_eq_true] at hlb'
    obtain ⟨hw1, hw2⟩ := hw
    rw [WellDenoted_lam] at hw1
    rw [AnnotValid_lam] at hw2
    obtain ⟨hwA, hwb, B, hfib, hzero⟩ := hw1
    have hA := Denotes_of_denoteMeta hcl d ty hta hfb'.1 hlb'.1 ρ ⟨hwA, hw2.1⟩
    show Graded _ _ _ _ (Kernel.Expr.lam (closeN d ty 0) (closeN d body 1) mb)
    refine ⟨ihty hta hfb'.1 hlb'.1 ρ ⟨hwA, hw2.1⟩, _, hA, fun x hx => ?_, fun h0 x hx y hy => ?_⟩
    · rw [push_eq_cons]
      have hb := ihbody hba (Kernel.Expr.fvarsBelow_instantiate1 0 hfb'.2)
        (Ix.Kernel.looseBVarsBounded_instantiate1 body 0 hlb'.2) (cons x ρ)
        ⟨hwb x hx, hw2.2 x hx⟩
      rwa [Kernel.Expr.closeN_instantiate1 body 0 hlb'.2 hfb'.2] at hb
    · have hbd := Denotes_of_denoteMeta hcl (d + 1) _ hba (Kernel.Expr.fvarsBelow_instantiate1 0 hfb'.2)
        (Ix.Kernel.looseBVarsBounded_instantiate1 body 0 hlb'.2) (cons x ρ) ⟨hwb x hx, hw2.2 x hx⟩
      rw [Kernel.Expr.closeN_instantiate1 body 0 hlb'.2 hfb'.2, ← push_eq_cons] at hbd
      rw [Kernel.Denotes_functional hy hbd, push_eq_cons]
      rw [regime_eq_pwBit] at h0
      exact eq_pt_of_mem_univZero (hzero h0 x hx) (hfib x hx)
  | case8 d fe a ihf iha =>
    intro ta h hfb hlb ρ hw
    obtain ⟨fA, aA, hfa, haa, rfl⟩ := denoteMeta_app_inv h
    have hfb' : Kernel.Expr.fvarsBelow d fe ∧ Kernel.Expr.fvarsBelow d a := hfb
    have hlb' : (fe.looseBVarsBounded 0 && a.looseBVarsBounded 0) = true := hlb
    rw [Bool.and_eq_true] at hlb'
    obtain ⟨hw1, hw2⟩ := hw
    rw [WellDenoted_app] at hw1
    rw [AnnotValid_app] at hw2
    obtain ⟨hwf, hwa, v, A, B, hmem, hxa, hzero⟩ := hw1
    have hF := Denotes_of_denoteMeta hcl d fe hfa hfb'.1 hlb'.1 ρ ⟨hwf, hw2.1⟩
    have hX := Denotes_of_denoteMeta hcl d a haa hfb'.2 hlb'.2 ρ ⟨hwa, hw2.2⟩
    show Graded _ _ _ _ (Kernel.Expr.app (closeN d fe 0) (closeN d a 0))
    refine ⟨ihf hfa hfb'.1 hlb'.1 ρ ⟨hwf, hw2.1⟩, iha haa hfb'.2 hlb'.2 ρ ⟨hwa, hw2.2⟩,
      _, _, v, A, B, hF, hX, hmem, hxa, fun h0 x hx => ?_⟩
    rw [univ_zero]; exact hzero h0 x hx
  | case9 d ty val body =>
    intro ta h
    rw [denoteMeta] at h
    exact nomatch h
  | case10 d sn i e ihe =>
    intro ta h hfb hlb ρ hw
    have hwhole := Denotes_of_denoteMeta hcl d (.proj sn i e) h hfb hlb ρ hw
    obtain ⟨ia, hia, hcase⟩ := denoteMeta_proj_inv h
    have hfb' : Kernel.Expr.fvarsBelow d e := hfb
    have hlb' : e.looseBVarsBounded 0 = true := hlb
    show Graded _ _ _ _ (Kernel.Expr.proj sn i (closeN d e 0))
    refine ⟨?_, _, hwhole⟩
    rcases hcase with ⟨entry, hfp, rfl⟩ | ⟨hfp, hdec⟩
    · exact ihe hia hfb' hlb' ρ (wellDenotedV_of_projAV _ _ hw)
    · match i, hdec with
      | 0, hdec =>
        obtain rfl := Option.some.inj hdec
        exact ihe hia hfb' hlb' ρ (wdv_fst hw)
      | 1, hdec =>
        obtain rfl := Option.some.inj hdec
        exact ihe hia hfb' hlb' ρ (wdv_snd hw)
      | _ + 2, hdec => exact nomatch hdec
  | case11 d k hsup =>
    intro ta h hfb hlb ρ hw
    exact ⟨_, Denotes_of_denoteMeta hcl d _ h hfb hlb ρ hw⟩
  | case12 d k hsup =>
    intro ta h
    rw [denoteMeta] at h
    simp [hsup] at h
  | case13 d s hsup =>
    intro ta h hfb hlb ρ hw
    exact ⟨_, Denotes_of_denoteMeta hcl d _ h hfb hlb ρ hw⟩
  | case14 d s hsup =>
    intro ta h
    rw [denoteMeta] at h
    simp [hsup] at h
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro ta h
    cases x with
    | bvar i => rw [denoteMeta.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hxs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE ty b mb => exact absurd rfl (hpi ty b mb)
    | lam ty b mb => exact absurd rfl (hlam ty b mb)
    | app fe a => exact absurd rfl (happ fe a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

/-- **Installed types are graded**: in every strong model, every installed constant's type has a
graded public reading at every assignment and valuation. -/
theorem installed_type_graded {env : Kernel.Env} (strong : Ix.CompileCert.StrongInstalledModel V env)
    {c : Kernel.ConstantInfo} (present : c ∈ env.consts) (φ : Kernel.Name → Nat) (ρ : Nat → V) :
    Graded strong.public.cval env φ ρ c.toConstantVal.type := by
  obtain ⟨ta, hta⟩ := strong.internal.type_reads c present φ
  have hwf := strong.internal.base2.wf c present
  have hnf : c.toConstantVal.type.hasFvar = false := hwf.1
  have hlb : c.toConstantVal.type.looseBVarsBounded 0 = true := hwf.2.2.2.1
  have h := graded_of_denoteMeta (V := V) strong.internal.base2.cval_closedL 0
    c.toConstantVal.type hta (fvarsBelow_zero_of_noFvar hnf) hlb ρ
    (strong.internal.type_wellDenotedV c present φ ta hta ρ)
  rw [Kernel.Expr.closeN_of_hasFvar _ 0 0 hnf] at h
  exact h

/-- **Installed definition values are graded**: in every strong model, an installed definition's
value has a graded public reading at every assignment and valuation (its reading is the
constant's own leaf, which IxC's install grades). -/
theorem installed_value_graded {env : Kernel.Env} (strong : Ix.CompileCert.StrongInstalledModel V env)
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (present : Kernel.ConstantInfo.defnInfo header value hint ∈ env.consts) (φ : Kernel.Name → Nat) (ρ : Nat → V) :
    Graded strong.public.cval env φ ρ value := by
  have hread := strong.internal.defn_reads φ header value ⟨hint, present⟩
  have hwf := (strong.internal.base2.wf _ present).2.2.2.2.1 header value hint rfl
  have hnf : value.hasFvar = false := hwf.1
  have hlb : value.looseBVarsBounded 0 = true := hwf.2.2.2
  have h := graded_of_denoteMeta (V := V) strong.internal.base2.cval_closedL 0
    value hread (fvarsBelow_zero_of_noFvar hnf) hlb ρ
    ⟨strong.internal.base2.acval_wellDenoted header.name φ ρ, strong.internal.acval_validV header.name φ ρ⟩
  rw [Kernel.Expr.closeN_of_hasFvar _ 0 0 hnf] at h
  exact h

end Ix.CompileCert.Pj
