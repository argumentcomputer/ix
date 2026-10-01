module

public import ConLeche.Model.Inductives.SumStageFormer
import ConLeche.Model.Inductives.StructStageCtor
public section

/-!
# A sum constructor's cons (task #175 sum-types, indexed)

`stageSumCtor`: the P step at constructor `j`'s cons — onto the
environment holding the former and the earlier constructors — with
the leaf `sumMkAV (resSort.eval ψ) j (ds ψ) Fs_j (uChains Fss)`.
The constructor's run was taken at the former's environment
(`checkSumCtor`) and its data crossed to the cons's environment
(`CtorDataI.cross`); the family application at the bottom — the
family at the parameters and the constructor's index expressions —
folds the former's leaf along the parameters and the index values
(`sumFormerFold`), landing in the fibre at the constructor's own index
tuple, where the point-terminated tuple lives by the index equation
(`restricted_member_intro`).  The capability laws are vacuous (the
block claims no eta or unit law).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

omit [SetTheory V] in
/-- The frame's index tuple at a consed index spine. -/
theorem frameIdx_consList {nIdx : Nat} {is : List V} (hlen : is.length = nIdx) (X : Nat → V) :
    frameIdx nIdx (consList is X) = is := by
  apply List.ext_getElem
  · simp [frameIdx, hlen]
  · intro l h1 h2
    have hl : l < nIdx := by simpa [frameIdx] using h1
    simp only [frameIdx, List.getElem_map, List.getElem_range]
    rw [consList_apply_lt _ _ _ (by omega), hlen,
      show nIdx - 1 - (nIdx - 1 - l) = l from by omega, List.getElem?_eq_getElem h2,
      Option.getD_some]

/-- **The constructor leaf's hereditary premises**: `MkPreS` along
the parameters and `UnderTowerValid` along the whole frame. -/
theorem ctorWalksGen {m : EnvModel V env} {T : Name} {lps : List Name} {cvT cvC : ConstantVal}
    {nP nF nIdx j : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ppsAll ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    {Fss Ess : (Name → Nat) → List (List AnnotTerm)}
    (_hFD : FormerData m cvT (nP + nIdx) resSort ppsAll)
    (hCD : CtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((ds ψ).drop nP).map (·.2.2)) bs →
        interp V (consList bs ρ) (ctorBodyAVI m T nP nF ψ (Es ψ))
          = sumSet (resSort.eval ψ) (sumFibre (resSort.eval ψ) (consList (idxValsAt ρ (Es ψ) bs) ρ)
              (rChains nIdx nIdx (Fss ψ) (Ess ψ))))
    (hFsj : ∀ ψ, (Fss ψ)[j]? = some (((ds ψ).drop nP).map (·.2.2)))
    (hEsj : ∀ ψ, (Ess ψ)[j]? = some (Es ψ))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ)
    (hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
      SumFieldsOkB (resSort.eval ψ) ρ (Fss ψ) ∧ SumFieldsValid ρ (Fss ψ))
    (_hIdx : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((ds ψ).drop nP).map (·.2.2)) bs →
        SpineFit ρ (((ppsAll ψ).drop nP).map (·.2.2)) (idxValsAt ρ (Es ψ) bs))
    (ψ : Name → Nat) (ρ : Nat → V) :
    MkPreS (resSort.eval ψ) j ρ (((ds ψ).drop nP).map (·.2.2)) (uChains (Fss ψ))
        (ctorBodyAVI m T nP nF ψ (Es ψ)) ((ds ψ).take nP) ∧
      UnderTowerValid ρ
        (sumInjAtAV (resSort.eval ψ) (uChains (Fss ψ)) (((ds ψ).drop nP).map (·.2.2)).length
          (numeralAV j) (mkTowerGoU (resSort.eval ψ) (((ds ψ).drop nP).map (·.2.2)) (idxEqAV [])))
        ((ds ψ).take nP ++ (ds ψ).drop nP) := by
  have hlenDs := hCD.len ψ
  have hlenP : ((ds ψ).take nP).length = nP := List.length_take_of_le (by omega)
  let Fs : List AnnotTerm := ((ds ψ).drop nP).map (·.2.2)
  have hlenFs : Fs.length = nF := by simp [Fs, hlenDs]
  have hst := stripPisAV_mkPisAV (ds ψ) (ctorBodyAVI m T nP nF ψ (Es ψ))
  rw [hlenDs] at hst
  have htele := piTeleAV_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleAV_graded (V := V) htele (Δ₀ := []) (fun ρ _ => hCD.okTy ψ ρ)
  simp only [List.append_nil] at okΓ
  have hΓlen : (((ds ψ).map (·.2.2)).reverse).length = nP + nF := by simp [hlenDs]
  have hΓplen : ((((ds ψ).take nP).map (·.2.2)).reverse).length = nP := by
    rw [List.length_reverse, List.length_map, hlenP]
  have okΓp : ∀ i, i < nP → ∀ ρ : Nat → V,
      Sat V (((((ds ψ).take nP).map (·.2.2)).reverse).drop (nP - i)) ρ →
      WellDenotedV V ρ (((((ds ψ).take nP).map (·.2.2)).reverse).getD (nP - 1 - i) default) := by
    intro i hi ρ hρ
    rw [← getD_reverse_take hlenDs hi]
    refine okΓ i (by omega) ρ ?_
    rw [drop_fields_eq hlenDs i (by omega)]
    exact hρ
  have hentP : ∀ i, i < nP → ∃ q, ((ds ψ).take nP)[i]? = some q ∧
      q.2.2 = ((((ds ψ).take nP).map (·.2.2)).reverse).getD (nP - 1 - i) default := by
    intro i hi
    have hil : i < ((ds ψ).take nP).length := by omega
    exact ⟨_, List.getElem?_eq_getElem hil,
      by rw [getD_reverse_of_peel hlenP hi (List.getElem?_eq_getElem hil)]⟩
  have hent : ∀ i, i < nP + nF → ∃ q, (ds ψ)[i]? = some q ∧
      q.2.2 = (((ds ψ).map (·.2.2)).reverse).getD (nP + nF - 1 - i) default := by
    intro i hi
    have hil : i < (ds ψ).length := by omega
    exact ⟨_, List.getElem?_eq_getElem hil,
      by rw [getD_reverse_of_peel hlenDs hi (List.getElem?_eq_getElem hil)]⟩
  have hchain : (rChains nIdx nIdx (Fss ψ) (Ess ψ))[j]? = some (rChain nIdx nIdx Fs (Es ψ)) := by
    rw [rChains_getElem?, hFsj ψ, hEsj ψ]
  constructor
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ pds => MkPreS (resSort.eval ψ) j ρ Fs (uChains (Fss ψ))
        (ctorBodyAVI m T nP nF ψ (Es ψ)) pds)
      hΓplen hlenP hentP okΓp
      (fun ρ hρ => ?_)
      (fun ρ d ds' _ hok hrec => ⟨hok.1, hrec⟩)
      0 (Nat.zero_le _) ρ (by
        rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓplen]; exact Nat.le_refl _)]
        exact Sat_nil V ρ)
    · rw [List.drop_zero] at hw; exact hw
    -- the base: at the parameter frame
    have hρt : Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ := (hiff ψ ρ).mpr hρ
    have hokFss := (hFssOkP ψ ρ hρ).1
    refine ⟨SumFieldsOkB_uChains hokFss, by rw [uChains_getElem?, hFsj ψ]; rfl, fun bs hsp => ?_⟩
    have hlenI : (idxValsAt ρ (Es ψ) bs).length = nIdx := by
      simp [idxValsAt, hCD.lenE ψ]
    refine ⟨sumFibre (resSort.eval ψ) (consList (idxValsAt ρ (Es ψ) bs) ρ)
      (rChains nIdx nIdx (Fss ψ) (Ess ψ)), ?_, ?_⟩
    · exact hfold ψ ρ hρt bs hsp
    · -- the point-terminated tuple lives in the fibre at the index tuple
      rw [sumFibre_of_getElem? hchain]
      have hshift : shiftE nIdx 0 (consList (idxValsAt ρ (Es ψ) bs) ρ) = ρ := by
        rw [← hlenI]; exact shiftE_consList _ _
      refine restricted_member_intro (Fs := liftFields nIdx 0 Fs) ?_ ?_
      · rw [spineFit_liftFields, hshift]
        exact hsp
      · rw [EqAll_idxEqsAt (hCD.lenE ψ) hsp.length_eq, hshift, frameIdx_consList hlenI]
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds' => UnderTowerValid ρ
        (sumInjAtAV (resSort.eval ψ) (uChains (Fss ψ)) Fs.length (numeralAV j)
          (mkTowerGoU (resSort.eval ψ) Fs (idxEqAV []))) ds')
      hΓlen hlenDs hent okΓ
      (fun ρ' hρ' => ?_)
      (fun ρ d ds' _ hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ (by
        rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓlen]; exact Nat.le_refl _)]
        exact Sat_nil V ρ)
    · rw [List.take_append_drop]
      rw [List.drop_zero] at hw
      exact hw
    rw [reverse_map_take_drop (ds ψ) nP] at hρ'
    have hspF := spineFit_of_sat (Δ₀ := (((ds ψ).take nP).map (·.2.2)).reverse)
      (Ds := ((ds ψ).drop nP).map (·.2.2)) hρ'
    rw [hlenFs] at hspF
    have hρp : Sat V (((ds ψ).take nP).map (·.2.2)).reverse (fun j => ρ' (j + nF)) := by
      have := Sat_drop hρ' nF
      rw [List.drop_append_of_le_length (by simp [hlenDs]),
        List.drop_eq_nil_of_le (by simp [hlenDs]), List.nil_append] at this
      exact this
    obtain ⟨-, hvAll⟩ := hFssOkP ψ _ hρp
    have hvF : FieldsValid (fun j => ρ' (j + nF)) Fs :=
      hvAll _ (List.mem_of_getElem? (hFsj ψ))
    have := sumInj_validV_at_fields (w := resSort.eval ψ) (j := j) (uChains_validV hvAll) hvF hspF
    rwa [consList_range_reverse] at this

/-- **The P step at a sum-shaped constructor's cons**, for a given fibre fold. -/
theorem stageCtorGen {T : Name}
    (hE : ConLeche.EtaFamiliesClosedExcept env T)
    {F : Nat} {lps : List Name} {nP nF nIdx j : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ env₁ : Env} {caps : IndCaps}
    (mp : EnvModelM V μ env)
    {sorts : List Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₀ env₁ T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    -- the constructor is fresh at the cons's environment and its type
    -- resolves there
    (hfresh : env.find? cvCa.name = none)
    (htr : cvCa.type.constsResolve env = true)
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hlpsC : cvCa.levelParams = lps)
    {idxArgs : List Expr}
    {ppsAll ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    {Fss Ess : (Name → Nat) → List (List AnnotTerm)}
    -- the block's own capability laws at the cons (task #210 Parts A
    -- and B), at any carrier agreeing with this one off the
    -- constructor's name and storing the constructor's leaf there
    (hTlaws : ∀ m₂ : EnvModel V ⟨.ctorInfo cvCa nP nF :: env.consts⟩,
      (∀ n, n ≠ cvCa.name → m₂.acval n = mp.base2.acval n) →
      (∀ ψ, m₂.acval cvCa.name ψ
        = sumMkAV (resSort.eval ψ) j (ds ψ) (((ds ψ).drop nP).map (·.2.2)) (uChains (Fss ψ))) →
      CapsLawsAt m₂ T cvTa caps)
    (hFD : FormerData mp.base2 cvTa (nP + nIdx) resSort ppsAll)
    (hCD : CtorDataI mp.base2 T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((ds ψ).drop nP).map (·.2.2)) bs →
        interp V (consList bs ρ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))
          = sumSet (resSort.eval ψ) (sumFibre (resSort.eval ψ) (consList (idxValsAt ρ (Es ψ) bs) ρ)
              (rChains nIdx nIdx (Fss ψ) (Ess ψ))))
    (hFsj : ∀ ψ, (Fss ψ)[j]? = some (((ds ψ).drop nP).map (·.2.2)))
    (hEsj : ∀ ψ, (Ess ψ)[j]? = some (Es ψ))
    (hFssParams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ lps, ψ₁ q = ψ₂ q) → Fss ψ₁ = Fss ψ₂)
    (hFssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ Fss ψ, FieldsBelow nP Fs)
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ)
    (hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
      SumFieldsOkB (resSort.eval ψ) ρ (Fss ψ) ∧ SumFieldsValid ρ (Fss ψ))
    (hIdx : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((ds ψ).drop nP).map (·.2.2)) bs →
        SpineFit ρ (((ppsAll ψ).drop nP).map (·.2.2)) (idxValsAt ρ (Es ψ) bs)) :
    ∃ mp' : EnvModelM V μ ⟨.ctorInfo cvCa nP nF :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvCa.name
        (fun ψ => sumMkAV (resSort.eval ψ) j (ds ψ) (((ds ψ).drop nP).map (·.2.2))
          (uChains (Fss ψ))) := by
  obtain ⟨⟨_, hccv⟩, -, -⟩ := ConLeche.checkSumCtor_shape hCtor
  obtain ⟨-, hnres, hpshape, -, hlbt, hitf, type', -, -, hann', htp, -, -, -, hty⟩ :=
    ConLeche.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  have hCname : cvCa.name = cvC.name := by rw [hty]
  have hcb : ConstsBound env cvCa.type := constsBound_of_constsResolve _ htr
  have hTC : T ≠ cvCa.name := by
    intro h; rw [h, hfresh] at hfT; exact nomatch hfT
  have hwfC : ConLeche.EnvWF ⟨.ctorInfo cvCa nP nF :: env.consts⟩ := by
    refine ConLeche.EnvWF.cons mp.base2.wf (ConLeche.structConstWF ?_ ?_ (Expr.constsResolve_mono htr) ?_
      (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq))
    · show cvCa.type.hasFvar = false; rw [hty]; exact htf'
    · show cvCa.type.allLevelParamsDefined cvCa.levelParams = true; rw [hty]; exact htp
    · show cvCa.type.looseBVarsBounded 0 = true; rw [hty]; exact hbt'
  let Fs : (Name → Nat) → List AnnotTerm := fun ψ => ((ds ψ).drop nP).map (·.2.2)
  let A : (Name → Nat) → AnnotTerm :=
    fun ψ => sumMkAV (resSort.eval ψ) j (ds ψ) (Fs ψ) (uChains (Fss ψ))
  have hAbelow : ∀ ψ, Term.bvarsBelow 0 (A ψ).erase := fun ψ =>
    sumMkAV_below (hCD.below ψ)
      ((DomsBelow.drop nP (hCD.below ψ)).fields)
      (by rw [Nat.zero_add]; exact uChains_below (hFssBelow ψ))
      (by show nP + (((ds ψ).drop nP).map (·.2.2)).length = (ds ψ).length
          simp [hCD.len ψ])
  have hwalks := ctorWalksGen hFD hCD hfold hFsj hEsj hiff hFssOkP hIdx
  have hz : ∀ ψ, ∀ d ∈ (ds ψ).take nP ++ (ds ψ).drop nP,
      (resSort.eval ψ = 0 ↔ d.2.1 = 0) := by
    intro ψ d hd
    rw [List.take_append_drop] at hd
    exact hCD.bits ψ d hd
  have hreadC : ∀ ψ : Name → Nat,
      denoteMeta (acvalWith mp.base2.acval cvCa.name A)
        ⟨.ctorInfo cvCa nP nF :: env.consts⟩ ψ 0 cvCa.type
        = some (mkPisAV (ds ψ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))) := fun ψ =>
    denoteMeta_cons_mono (c₀ := .ctorInfo cvCa nP nF) hfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0 hcb (hCD.read ψ)
  have hnresC : ConLeche.reservedBasisNames.contains
      (ConstantInfo.ctorInfo cvCa nP nF).name = false := by
    show ConLeche.reservedBasisNames.contains cvCa.name = false
    rw [hCname]; exact hnres
  have hpshapeC : (ConstantInfo.ctorInfo cvCa nP nF).name.isProjFnShape = false := by
    show cvCa.name.isProjFnShape = false
    rw [hCname]; exact hpshape
  refine declStep_preserves_of_ind_member_cons mp (c₀ := .ctorInfo cvCa nP nF)
    (A := A) hfresh hnresC (Or.inr ⟨_, _, _, rfl⟩)
    (ConsHead.ofFresh hwfC (fun ψ => hAbelow ψ) hnresC
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h))
    (fun ψ k => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le k) (hAbelow ψ)) 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro ψ₁ ψ₂ hφ
    have hφT : ∀ q ∈ cvTa.levelParams, ψ₁ q = ψ₂ q := by rw [hlpsT, ← hlpsC]; exact hφ
    obtain ⟨-, hw⟩ := hFD.params ψ₁ ψ₂ hφT
    show sumMkAV _ j (ds ψ₁) (((ds ψ₁).drop nP).map (·.2.2)) (uChains (Fss ψ₁))
      = sumMkAV _ j (ds ψ₂) (((ds ψ₂).drop nP).map (·.2.2)) (uChains (Fss ψ₂))
    rw [hw, (hCD.params ψ₁ ψ₂ hφ).1, hFssParams ψ₁ ψ₂ (by rw [← hlpsC]; exact hφ)]
  · intro ψ ρ
    have := sumMkAV_wellDenotedV (V := V) (hz ψ) (hwalks ψ ρ).1 (hwalks ψ ρ).2
    rw [List.take_append_drop] at this
    exact this.1
  · intro ψ ρ
    have := sumMkAV_wellDenotedV (V := V) (hz ψ) (hwalks ψ ρ).1 (hwalks ψ ρ).2
    rw [List.take_append_drop] at this
    exact this.2
  · exact fun ψ => ⟨_, hreadC ψ⟩
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadC ψ).symm.trans hta)
    exact hCD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadC ψ).symm.trans hta)
    have := sumMkAV_mem (V := V) (hz ψ) (hwalks ψ ρ).1
    rw [List.take_append_drop] at this
    exact this
  · -- `caps_ok`: nothing is claimed by the block's family
    intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .ctorInfo cvCa nP nF) (A := A)
      (T := T) hfresh (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshapeC
      (Or.inr fun _ _ h => nomatch h) ?_ m₂ hac ?_
    · intro T' cvT' caps' hf hne hres hcape
      exact hE T' cvT' caps' hf hne hcape hres
    · intro cvT caps' hf _
      have hfT' : (⟨.ctorInfo cvCa nP nF :: env.consts⟩ : Env).find? T
          = some (.indInfo cvTa caps) := by
        rw [ConLeche.Env.find?_cons, if_neg (fun h => hTC h.symm)]
        exact hfT
      obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT'.symm.trans hf))
      refine hTlaws m₂ (fun n hn => ?_) (fun ψ => ?_)
      · rw [hac]
        exact acvalWith_ne hn
      · rw [hac]
        exact congrFun acvalWith_self ψ

end ConLeche.Model
