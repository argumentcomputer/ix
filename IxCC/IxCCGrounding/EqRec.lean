import IxCCGrounding.Tele

/-!
# F3 at `Eq.rec`, model side (`IxCCGrounding.EqRec`; G3, part C)

**Statement** (`eqRec_iota`). In every model with the laws, at every level assignment, where
`Eq`, `Eq.refl` and `Eq.rec` are stored as F3 reads them (`EqBasis`, `EqReflBasis`,
`EqRecBasis`, decided by the check): `Eq.rec` at its own level parameters, applied to six sets
that fit its stored type, is the fourth of them, the minor premise. That is what SrcEval's F3
returns at `Eq.rec`: the rule's right-hand side peeled of its four λs is the variable of the
minor's slot (`peelLams_corr`), and the major is never forced.

**Proof.** The major premise `t` lies in the denotation of its domain `@Eq α a b`, so `a` and `b`
denote the same set and `t` is the proof point (`eq_of_inhabited_pt`: `Model.mem` of `Eq` and
`Model.eq_equality`). `Eq.refl`'s set lies in its stored type, whose binders are read in regime
`0` (both data "always a proposition"), so it is the proof point, and so is `Eq.refl α a`
(`app_pt`). So the major is `Eq.refl`'s image at the recursor's own parameters, with the index
`b` equal to `a`; ι (`Laws.iota_rule` at `Eq.rec`'s one rule, constructor `Eq.refl`, no field)
gives `Eq.rec α a motive refl b t` as the rule's right-hand side applied to the first four
arguments, and β through its four λs (whose domains are the type's, so the arguments lie in them)
gives `refl`. No regime is read: β through a λ holds in regime `0` too (`app_den_lam`).

**What it assumes of the model, and why each holds in a proof-irrelevant set model.**

* `Laws.iota_rule` (ι), at `Eq.rec`'s one rule: the side that owes the laws has proved it for
  every stored rule. In the kernel's own set model in this repository `Eq.rec` is interpreted as
  "the minor premise, returned" under its six binders (`eqRecValAV`,
  `IxCK/Kernel/Model/EqTower.lean`), its tower fires to the minor premise (`eqRecRaTower_app₆`)
  and its rule's law is proved (`eqRecLaw`, `IxCK/Kernel/Model/BasisEq.lean`). ι is used here at
  a family that is a proposition (`Eq`), but only at the recursor's own parameters and with the
  index equal to the parameter, which is what the rule computes; no canonicity step is taken
  (`Laws.ctor_canon` and `Laws.proj_ctor`, whose unrestricted forms were false at propositions,
  are not used).
* `Model.mem` (every stored constant is a member of what its stored type denotes), at `Eq` and
  `Eq.refl`: it is what a model is; the kernel's model has it from its invariant's `mem_type`
  (`Model.ofEnvModelM`, `IxCK/Kernel/Model/Denotes.lean`).
* `Model.eq_equality` (`@Eq.{u} A a b` denotes `eqv a b`, the truth value of `a = b`): the kernel
  installs `Eq` from its own pins and the set model reads it as set equality (`eqv`,
  `IxCK/Kernel/SetTheory/Derive/Pt.lean`, whose only member is the proof point); the kernel's
  model proves it from its invariant's `eq_law` (`IxCK/Kernel/Model/Denotes.lean`), and in this
  repository a member of `eqv a b` identifies `a` with `b` and is the proof point
  (`eqRec_major_collapse`, `IxCK/Kernel/Model/BasisEq.lean`).

`Model.mem` and `Model.eq_equality` are fields of every `Model`, not hypotheses of `Laws`: they
add nothing to what a theorem of this library assumes, but they are part of what a model of the
environment must satisfy.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Term CId)

universe w

/-- **Peeling a Src term's λs where it corresponds to a kernel λ-telescope** leaves a term that
corresponds to the telescope's body. -/
theorem peelLams_corr {κ : CId → KKey} {lps : List Nat} :
    ∀ (bs : List (KExpr × BinderMeta)) {t : Term} {b : KExpr},
      TermCorr κ lps t (lamTele bs b) →
      ∃ t', IxCC.Src.peelLams bs.length t = some t' ∧ TermCorr κ lps t' b
  | [], t, _, h => ⟨t, rfl, h⟩
  | (A, m) :: bs, t, b, h => by
    have h' : TermCorr κ lps t (.lam A (lamTele bs b) m) := h
    cases h' with
    | lam _ hb =>
      obtain ⟨t', h1, h2⟩ := peelLams_corr bs hb
      exact ⟨t', by simpa [IxCC.Src.peelLams] using h1, h2⟩

/-- **F3's body at `Eq.rec`**: a Src rule whose right-hand side corresponds to `eqRecRhs`, peeled
of four λs, is the variable `0` (the minor premise's slot). -/
theorem peelLams_eqRecRhs {κ : CId → KKey} {lps : List Nat} {t : Term}
    (h : TermCorr κ lps t eqRecRhs) : IxCC.Src.peelLams 4 t = some (.var 0) := by
  obtain ⟨t', h1, h2⟩ := peelLams_corr eqRecPrefix h
  cases h2
  exact h1

section Sem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- **`Eq.refl`'s set is the proof point**: it lies in its stored type, whose two binders are
read in regime `0`. -/
theorem eqRefl_pt (M : Model V env) (hR : EqReflBasis env) (φ : LevelParam → Nat) :
    M.cval eqReflName φ = pt := by
  obtain ⟨cvR, hfR, _, htR⟩ := hR
  obtain ⟨TR, hTR, hKm⟩ := mem_key M hfR φ (fun _ => empty)
  simp only [ConstantInfo.toConstantVal] at hTR
  rw [htR] at hTR
  obtain ⟨_, _, _, _, _, rfl⟩ := den_pi.mp hTR
  have h0 : regime φ (PropWhen.ifAllZero []) = 0 := by simp [regime]
  rw [h0] at hKm
  exact eq_pt_of_mem_piR_zero hKm

/-- **F3 at `Eq.rec`, model side.** `Eq.rec`, at its own level parameters, applied to six sets that
fit its stored type, is the fourth, the minor premise. By `eq_of_inhabited_pt` (the major is the
proof point and the index is the parameter), `eqRefl_pt` (so the major is `Eq.refl`'s image), ι
at the one rule, and β through its right-hand side. Uses `Laws.iota_rule`, `Model.mem` and
`Model.eq_equality`; no regime is read, so no typing of the last argument's site is needed. -/
theorem eqRec_iota (M : Model V env) (hL : Laws M) (hE : EqBasis env) (hR : EqReflBasis env)
    (hB : EqRecBasis env) {φ : LevelParam → Nat} {ρ σ : BVarIdx → V} {Rt : KExpr} {As : List V}
    (hfit : Fits M.cval env φ ρ eqRecType As σ Rt) (hlen : As.length = 6) :
    ∃ Mn, As[3]? = some Mn ∧ As.foldl app (M.cval eqRecName φ) = Mn := by
  obtain ⟨cvr, krl, hfr, hty, hkc, hkr⟩ := hB
  have hK := eqRefl_pt M hR φ
  obtain ⟨cvR, hfR, hlR, htR⟩ := hR
  obtain ⟨A, a, mo, mn, b, h, rfl⟩ : ∃ A a mo mn b h, As = [A, a, mo, mn, b, h] := by
    match As, hlen with
    | [A, a, mo, mn, b, h], _ => exact ⟨A, a, mo, mn, b, h, rfl⟩
    | [], hl | [_], hl | [_, _], hl | [_, _, _], hl | [_, _, _, _], hl | [_, _, _, _, _], hl =>
      simp only [List.length_cons, List.length_nil] at hl <;> omega
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, hl => simp only [List.length_cons] at hl <;> omega
  refine ⟨mn, rfl, ?_⟩
  unfold eqRecType at hfit
  have hfit' := hfit
  rw [piTele_append] at hfit'
  -- the domains of `α`, `a` and the major premise
  obtain ⟨XA, hXA, hA⟩ := fits_get (eqRecPrefix ++ eqRecMajors) eqRecBody hfit 0 (by simp) (by simp [eqRecPrefix, eqRecMajors])
  obtain ⟨Xa, hXa, ha⟩ := fits_get (eqRecPrefix ++ eqRecMajors) eqRecBody hfit 1 (by simp) (by simp [eqRecPrefix, eqRecMajors])
  obtain ⟨Xh, hXh, hh⟩ := fits_get (eqRecPrefix ++ eqRecMajors) eqRecBody hfit 5 (by simp) (by simp [eqRecPrefix, eqRecMajors])
  have hXA' : Denotes M.cval env φ ρ (.sort (.param 0)) XA := by
    simpa [eqRecPrefix, pushAll_nil] using hXA
  have hA' : A ∈ˢ XA := by simpa using hA
  have hXa' : Denotes M.cval env φ (pushAll [A] ρ) (.bvar 0) Xa := by
    simpa [eqRecPrefix] using hXa
  have eXa : Xa = A := by
    have := den_bvar.mp hXa'
    simpa [pushAll] using this
  have ha' : a ∈ˢ A := by rw [← eXa]; simpa using ha
  have hXh' : Denotes M.cval env φ (pushAll [A, a, mo, mn, b] ρ)
      (eqAppK (.bvar 4) (.bvar 3) (.bvar 0)) Xh := by
    simpa [eqRecPrefix, eqRecMajors] using hXh
  have hh' : h ∈ˢ Xh := by simpa using hh
  -- the major: `a` and `b` are equal, and it is the proof point
  obtain ⟨⟨x, hx3, hx0⟩, hpt⟩ := eq_of_inhabited_pt M hE hXh' hh'
  have e3 : x = a := by
    have := den_bvar.mp hx3
    simpa [pushAll] using this
  have e0 : x = b := by
    have := den_bvar.mp hx0
    simpa [pushAll] using this
  have hab : a = b := e3.symm.trans e0
  -- ι at the one rule, `Eq.refl` with no field, at the recursor's own parameters
  have hRden : Denotes M.cval env φ ρ (.const eqRecName (cvr.levelParams.map .param))
      (M.cval eqRecName φ) := by
    have h1 : Denotes M.cval env φ ρ (.const eqRecName (cvr.levelParams.map .param))
        (M.cval eqRecName (Level.substFn φ cvr.levelParams (cvr.levelParams.map .param))) :=
      Denotes.const (ci := .recInfo cvr 5 4 [krl]) hfr (by simp [ConstantInfo.toConstantVal])
    rwa [substFn_self] at h1
  have hfit5 : Fits M.cval env φ ρ
      (cvr.type.instantiateLevelParams cvr.levelParams (cvr.levelParams.map .param))
      [A, a, mo, mn, b] (pushAll [A, a, mo, mn, b] ρ)
      (.forallE (eqAppK (.bvar 4) (.bvar 3) (.bvar 0)) eqRecBody bmR) := by
    rw [inst_self, hty, eqRecType]
    have := fits_prefix (bs := eqRecPrefix ++ eqRecMajors) (C := eqRecBody)
      (xs := [A, a, mo, mn, b]) (ys := [h]) hfit (by simp [eqRecPrefix, eqRecMajors])
    simpa [eqRecPrefix, eqRecMajors, piTele] using this
  have hKden : Denotes M.cval env φ ρ (.const krl.ctor [.param 0]) (M.cval eqReflName φ) := by
    rw [hkc]
    exact (den_const_param0 (ci := .ctorInfo cvR 2 0) hfR hlR).mpr rfl
  have hinstR : cvR.type.instantiateLevelParams cvR.levelParams [.param 0] = eqReflType := by
    have := inst_self [0] cvR.type
    simp only [List.map_cons, List.map_nil] at this
    rw [hlR, this, htR]
  have hfitR : Fits M.cval env φ ρ (cvR.type.instantiateLevelParams cvR.levelParams [.param 0])
      [A, a] (push a (push A ρ)) (eqAppK (.bvar 1) (.bvar 0) (.bvar 0)) := by
    rw [hinstR]
    exact .cons hXA' hA' (.cons (den_bvar.mpr rfl) ha' .nil)
  have hmaj : [A, a].foldl app (M.cval eqReflName φ) ∈ˢ Xh := by
    rw [hK]
    simp only [List.foldl_cons, List.foldl_nil, app_pt]
    rw [← hpt]
    exact hh'
  have hpar : DenotesList M.cval env φ (pushAll [A, a, mo, mn, b] ρ)
      ((eqAppK (.bvar 4) (.bvar 3) (.bvar 0)).getAppArgs.take 2) ([A, a].take 2) := by
    simp [eqAppK, getAppArgs_mkAppN, Expr.getAppArgs]
    exact .cons (den_bvar.mpr (by simp [pushAll])) (.cons (den_bvar.mpr (by simp [pushAll])) .nil)
  have hidx : DenotesList M.cval env φ (push a (push A ρ))
      ((eqAppK (.bvar 1) (.bvar 0) (.bvar 0)).getAppArgs.drop 2) ([A, a, mo, mn, b].drop 4) := by
    simp [eqAppK, getAppArgs_mkAppN, Expr.getAppArgs]
    exact .cons (den_bvar.mpr (by rw [← hab]; rfl)) .nil
  obtain ⟨H, hH, heq⟩ := hL.iota_rule eqRecName cvr 5 4 [krl] krl hfr (List.mem_singleton_self _)
    cvR 2 0 (by rw [hkc]; exact hfR) (cvr.levelParams.map .param) φ ρ (pushAll [A, a, mo, mn, b] ρ)
    (push a (push A ρ)) [A, a, mo, mn, b] [A, a] (eqAppK (.bvar 4) (.bvar 3) (.bvar 0)) eqRecBody
    (eqAppK (.bvar 1) (.bvar 0) (.bvar 0)) bmR eqName [.param 0] (M.cval eqRecName φ)
    (M.cval eqReflName φ) Xh (by simp) rfl rfl hRden hfit5
    (by simp [eqAppK, getAppFn_mkAppN, Expr.getAppFn]) hXh' hKden hfitR hmaj hpar hidx
  -- β through the rule's right-hand side
  rw [inst_self, hkr] at hH
  have hmj : [A, a].foldl app (M.cval eqReflName φ) = h := by
    rw [hK, hpt]
    simp only [List.foldl_cons, List.foldl_nil, app_pt]
  rw [hmj] at heq
  have e1 : [A, a, mo, mn, b, h].foldl app (M.cval eqRecName φ) =
      ([A, a, mo, mn, b] ++ [h]).foldl app (M.cval eqRecName φ) := rfl
  rw [e1, heq]
  have hfit4 := fits_prefix (bs := eqRecPrefix) (C := piTele eqRecMajors eqRecBody)
    (xs := [A, a, mo, mn]) (ys := [b, h]) hfit' (by simp [eqRecPrefix])
  obtain ⟨Y, hY, hYe⟩ := lamTele_app eqRecPrefix (.bvar 0) _ hH hfit4 (by simp [eqRecPrefix])
  have e2 : ([A, a, mo, mn, b].take 4 ++ [A, a].drop 2).foldl app H = [A, a, mo, mn].foldl app H := rfl
  rw [e2, hYe]
  have := den_bvar.mp hY
  simpa [pushAll] using this

end Sem

end IxCC.Grounding
