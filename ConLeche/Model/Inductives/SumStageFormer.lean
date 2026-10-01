module

public import ConLeche.Model.Inductives.SumData
import ConLeche.Verify.Inductives.SumWF
public section

/-!
# The sum former's cons (task #175 sum-types, indexed)

`stageSumFormer`: the P step at the sum's type former, for a given
list of field chains `Fss` (one per constructor, scoped at the
parameter-and-index frame — the restricted chains `rChains` at an
indexed family) — `stageFormer` with the sum leaf `sumTyAV`
and the per-constructor grading `SumFieldsOkB`.  The former is stored
with the empty capability record, so the block's own capability laws
are vacuous.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- **The sum former leaf's two hereditary premises**, from the former's
data and the chains' grading at the parameter frame. -/
theorem formerWalksS {m : EnvModel V env} {cvT : ConstantVal} {nP : Nat}
    {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData m cvT nP resSort pps)
    {Fss : (Name → Nat) → List (List AnnotTerm)}
    (hFssOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V ((pps ψ).map (·.2.2)).reverse ρ →
      SumFieldsOkB (resSort.eval ψ) ρ (Fss ψ) ∧ SumFieldsValid ρ (Fss ψ))
    (ψ : Name → Nat) (ρ : Nat → V) :
    ParamsOkS (resSort.eval ψ) ρ (Fss ψ) (pps ψ) ∧
      UnderTowerValid ρ (sumBodyAV (resSort.eval ψ) (Fss ψ)) (pps ψ) := by
  have hst := stripPisAV_mkPisAV (pps ψ) (.sort (resSort.eval ψ))
  rw [hFD.len ψ] at hst
  have htele := piTeleAV_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleAV_graded (V := V) htele (Δ₀ := [])
    (fun ρ _ => hFD.okTy ψ ρ)
  simp only [List.append_nil] at okΓ
  have hlenΓ : (((pps ψ).map (·.2.2)).reverse).length = nP := by
    simp [hFD.len ψ]
  have hent : ∀ i, i < nP → ∃ p, (pps ψ)[i]? = some p ∧
      p.2.2 = (((pps ψ).map (·.2.2)).reverse).getD (nP - 1 - i) default := by
    intro i hi
    have hil : i < (pps ψ).length := by rw [hFD.len ψ]; exact hi
    refine ⟨(pps ψ)[i], List.getElem?_eq_getElem hil, ?_⟩
    rw [getD_reverse_of_peel (hFD.len ψ) hi (List.getElem?_eq_getElem hil)]
  have hΓnil : (((pps ψ).map (·.2.2)).reverse).drop (nP - 0) = [] := by
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hlenΓ]; exact Nat.le_refl _)]
  constructor
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => ParamsOkS (resSort.eval ψ) ρ (Fss ψ) ds)
      hlenΓ (hFD.len ψ) hent okΓ
      (fun ρ hρ => (hFssOk ψ ρ hρ).1)
      (fun ρ d ds hd hok hrec => ⟨hFD.bits ψ d hd, hok.1, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat_nil V ρ)
    simpa using hw
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => UnderTowerValid ρ (sumBodyAV (resSort.eval ψ) (Fss ψ)) ds)
      hlenΓ (hFD.len ψ) hent okΓ
      (fun ρ hρ => sumBodyAV_validV (hFssOk ψ ρ hρ).2)
      (fun ρ d ds hd hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat_nil V ρ)
    simpa using hw

/-- **The P step at the sum former's cons**, for a given list of field
chains. -/
theorem stageSumFormer (mp : EnvModelM V μ env)
    (hE₀ : ConLeche.EtaFamiliesClosed env)
    {F : Nat} {p : InductiveShape} {cvT cvTa : ConstantVal}
    -- the former's `checkConstantVal` run at the block's header — its
    -- declared type or its whnf'd telescope (task #195); the stage never
    -- asks which
    (hccv : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env cvT = .ok cvTa)
    (hname₀ : cvT.name = p.cvT.name)
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp.base2 cvTa (p.nP + p.nIdx) p.resSort pps)
    (Fss : (Name → Nat) → List (List AnnotTerm))
    (hFssParams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ cvTa.levelParams, ψ₁ q = ψ₂ q) → Fss ψ₁ = Fss ψ₂)
    (hFssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ Fss ψ, FieldsBelow (p.nP + p.nIdx) Fs)
    (hFssOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V ((pps ψ).map (·.2.2)).reverse ρ →
      SumFieldsOkB (p.resSort.eval ψ) ρ (Fss ψ) ∧ SumFieldsValid ρ (Fss ψ))
    -- the block's capability record and its laws at the cons (task
    -- #210 Part A: `sumCaps` on the sum route, `nativeCaps` on
    -- the fixpoint route)
    (caps : IndCaps)
    -- the record's arities, from the install's telescope pin
    (hicw : ConLeche.IndCapsWF (.indInfo cvTa caps))
    (hTlaws : ∀ m₂ : EnvModel V ⟨.indInfo cvTa caps :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval cvTa.name
        (fun ψ => sumTyAV (p.resSort.eval ψ) (pps ψ) (Fss ψ)) →
      CapsLawsAt m₂ cvTa.name cvTa caps) :
    ∃ mp' : EnvModelM V μ ⟨.indInfo cvTa caps :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvTa.name
        (fun ψ => sumTyAV (p.resSort.eval ψ) (pps ψ) (Fss ψ)) := by
  obtain ⟨hfind, hnres, hpshape, -, -, -, type', -, -, -, -, htr', -, -, hty⟩ :=
    ConLeche.checkConstantVal_inv hccv
  have hname : cvTa.name = p.cvT.name := by rw [hty]; exact hname₀
  have hfresh : env.find? cvTa.name = none := by
    rw [hname, ← hname₀]; exact hfind
  have htr : cvTa.type.constsResolve env = true := by rw [hty]; exact htr'
  have hcb : ConstsBound env cvTa.type := constsBound_of_constsResolve _ htr
  have hwfI : ConLeche.EnvWF ⟨.indInfo cvTa caps :: env.consts⟩ :=
    ConLeche.envWF_cons_ind mp.base2.wf hccv hicw
  let A : (Name → Nat) → AnnotTerm :=
    fun ψ => sumTyAV (p.resSort.eval ψ) (pps ψ) (Fss ψ)
  have hAbelow : ∀ ψ, Term.bvarsBelow 0 (A ψ).erase := fun ψ =>
    sumTyAV_below (hFD.below ψ)
      (by rw [hFD.len ψ, Nat.zero_add]; exact hFssBelow ψ)
  have hwalks := formerWalksS hFD hFssOk
  have hreadI : ∀ ψ : Name → Nat,
      denoteMeta (acvalWith mp.base2.acval cvTa.name A)
        ⟨.indInfo cvTa caps :: env.consts⟩ ψ 0 cvTa.type
        = some (mkPisAV (pps ψ) (.sort (p.resSort.eval ψ))) := fun ψ =>
    denoteMeta_cons_mono (c₀ := .indInfo cvTa caps) hfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0 hcb (hFD.read ψ)
  have hnresI : ConLeche.reservedBasisNames.contains
      (ConstantInfo.indInfo cvTa caps).name = false := by
    show ConLeche.reservedBasisNames.contains cvTa.name = false
    rw [hname, ← hname₀]; exact hnres
  have hpshapeI : (ConstantInfo.indInfo cvTa caps).name.isProjFnShape = false := by
    show cvTa.name.isProjFnShape = false
    rw [hname, ← hname₀]; exact hpshape
  refine declStep_preserves_of_ind_member_cons mp (c₀ := .indInfo cvTa caps)
    (A := A) hfresh hnresI (Or.inl ⟨_, _, rfl⟩)
    (ConsHead.ofFresh hwfI (fun ψ => hAbelow ψ) hnresI
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h))
    (fun ψ k => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le k) (hAbelow ψ)) 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro ψ₁ ψ₂ hφ
    obtain ⟨hp, hw⟩ := hFD.params ψ₁ ψ₂ hφ
    show sumTyAV _ _ _ = sumTyAV _ _ _
    rw [hp, hw, hFssParams ψ₁ ψ₂ hφ]
  · exact fun ψ ρ => sumTyAV_wellDenoted (hwalks ψ ρ).1
  · exact fun ψ ρ => (sumTyAV_wellDenotedV (hwalks ψ ρ).1 (hwalks ψ ρ).2).2
  · exact fun ψ => ⟨_, hreadI ψ⟩
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadI ψ).symm.trans hta)
    exact hFD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadI ψ).symm.trans hta)
    exact sumTyAV_mem (hwalks ψ ρ).1
  · -- `caps_ok`: the prefix families cross; the block's own family
    -- claims nothing (the empty capability record)
    intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .indInfo cvTa caps)
      (A := A) (T := cvTa.name) hfresh
      (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshapeI
      (Or.inl ⟨cvTa, caps, rfl, rfl⟩)
      (fun T' cvT' caps' hf _ hres hcape => hE₀ T' cvT' caps' hf hcape hres)
      m₂ hac ?_
    intro cvT caps' hf _
    have hself := ConLeche.Env.find?_cons_self (ConstantInfo.indInfo cvTa caps) env
    obtain ⟨rfl, rfl⟩ :=
      ConstantInfo.indInfo.inj (Option.some.inj (hself.symm.trans hf))
    exact hTlaws m₂ hac

end ConLeche.Model
