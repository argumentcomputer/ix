module

import ConLeche.Semantics.Tower.FixSquashI
public import ConLeche.Semantics.Tower.FixIhI
public import ConLeche.Semantics.Tower.FixElemI

@[expose] public section

/-!
# The recursive family's recursor: the fixed point and its leaf (task #188, indexed)

The tail of `FixRecCoreI.lean` (the step, the premise `FixPre`): the
recursor body's facts at every walk leaf, the step's facts, the fixed
point (the semantic candidate `rStar`, its membership and fixedness —
three regimes: the point at a small eliminator, the rank recursion over
the ω-iterate at a `Type`-valued family, and the recursion equation's
unique solution at the squash regime, task #202 A2), the selection and
the leaf's iota laws.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Term (Term)

universe uv

variable {V : Type uv} [SetTheory V]

variable {ℓ w u nP : Nat} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
  {rds : List (Nat × Nat × AnnotTerm)} {s : Nat}

section Rec

/-- **The recursor body's facts** at a walk leaf: graded, in the
conclusion, a truth value at level zero. -/
theorem body_facts (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) (ρb : Nat → V) {r : V}
    (hr : r ∈ˢ interp V ρb (recTyAV Fss.length Ids.length rds)) {as : List V} {t : V}
    (hsp : SpineFit (cons r ρb) (rds.map (·.2.2)) (as ++ [t])) :
    WellDenoted V (consList (as ++ [t]) (cons r ρb)) (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss) ∧
    interp V (consList (as ++ [t]) (cons r ρb)) (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss)
      ∈ˢ interp V (consList (as ++ [t]) (cons r ρb)) (recConcAV Fss.length Ids.length) ∧
    (ℓ = 0 → interp V (consList (as ++ [t]) (cons r ρb)) (recConcAV Fss.length Ids.length)
      ∈ˢ (univZero : V)) := by
  have hKI := fixKI_of h ρb hr hsp
  obtain ⟨-, ht⟩ := h.hK (cons r ρb) as t hsp
  rw [← consList_snoc']
  have hfr : RecFrameS 1 (consList as (cons r ρb)) (cons t (consList as (cons r ρb))) := by
    unfold RecFrameS
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  obtain ⟨hMv, -⟩ := motApp_facts hfr hKI.hyp.toRecHypCore
  have hconc : interp V (cons t (consList as (cons r ρb))) (recConcAV Fss.length Ids.length)
      = SetTheory.app (frMi Fss.length Ids.length (consList as (cons r ρb))) t := by
    unfold recConcAV
    rw [interp_app, hMv, interp_bvar, cons_zero]
  have hfitI := hKI.hyp.hfit
  have ht' : t ∈ˢ sumSet w (sumFibre w (consList as (cons r ρb))
      (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)) := by
    rw [← hKI.hyp.hfam]
    exact ht
  -- the squash regime: the body's facts from `sqFixBody_facts`
  have hsqfacts : w = 0 → ℓ ≠ 0 →
      WellDenoted V (cons t (consList as (cons r ρb))) (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss) ∧
      interp V (cons t (consList as (cons r ρb))) (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss)
        ∈ˢ SetTheory.app (frMi Fss.length Ids.length (consList as (cons r ρb))) t := by
    intro hw hℓ
    subst hw
    rw [fixRecBodyAVI_sq hℓ]
    have hlen_as : as.length = nP + 1 + Fss.length + Ids.length := by
      have := hsp.length_eq
      rw [List.length_append, List.length_singleton, List.length_map, h.hlen] at this
      omega
    obtain ⟨ps, ms, is, M, rfl, hlenP, hlenM, hlenI⟩ := kframe_split3 hlen_as
    have hKI' := hKI
    have ht₁ := ht
    rw [consList_kframe] at hKI' ht₁ ⊢
    have ht' : t ∈ˢ SetTheory.app
        (fixFamI u 0 (consList ps (cons r ρb)) Ids Ids.length rss tlss Eiss Fss₀ Ess) (tupW u is) := by
      unfold famK at ht₁
      rwa [kframe_frP' hlenI hlenM, kframe_frameIdx' hlenI] at ht₁
    have hf := sqFixBody_facts hℓ hlenP hlenM hlenI hKI' ht'
    refine ⟨hf.1, ?_⟩
    unfold frMi
    rw [kframe_frameIdx' hlenI, kframe_frM' hlenI hlenM]
    have hfam' := famApp_mem_univ
      (fixFamI_mem u 0 (consList ps (cons r ρb)) Ids rss tlss Eiss Fss₀ Ess) (tupW u is)
    rw [univ_zero] at hfam'
    have htpt : t = pt := eq_pt_of_mem_univZero hfam' ht'
    subst htpt
    exact hf.2.2
  refine ⟨?_, ?_, fun h0 => by rw [hconc]; exact hKI.hyp.hM0 h0 t⟩
  · -- graded
    by_cases hw : w = 0
    · by_cases hℓ : ℓ = 0
      · subst hw; rw [fixRecBodyAVI_zero hℓ]; trivial
      · exact (hsqfacts hw hℓ).1
    · rw [fixRecBodyAVI_pos hw]
      have hcase := caseRec_factsI hw hKI.hyp
        (fun D' j' σ' hfr' hj' => FixKI.ihArgsOk_tele hKI hw hfr' hj') Fss.length (D := 1) (j := 0)
        (σ := cons t (consList as (cons r ρb))) (k := .fst (.bvar 0)) hfr (Nat.zero_add _)
      have hok0 := major_fst_wellDenoted hw hKI.hyp.hok (σ := cons t (consList as (cons r ρb))) ht'
      have hok1 := major_snd_wellDenoted hw hKI.hyp.hok (σ := cons t (consList as (cons r ρb))) ht'
      obtain ⟨i, a, ha, hta⟩ := sumSet_elim hw ht'
      have htag : interp V (cons t (consList as (cons r ρb))) (.fst (.bvar 0)) = vnat i := by
        rw [interp_fst, interp_bvar, cons_zero, hta, sfst_inj]
      have hpay : interp V (cons t (consList as (cons r ρb))) (.snd (.bvar 0)) = a := by
        rw [interp_snd, interp_bvar, cons_zero, hta, ssnd_inj]
      have hkω : interp V (cons t (consList as (cons r ρb))) (.fst (.bvar 0)) ∈ˢ (omega : V) := by
        rw [htag]; exact vnat_mem_omega i
      obtain ⟨hmem, -⟩ := hcase.1 hkω
      rw [htag, motSem_vnat, Nat.zero_add] at hmem
      rw [WellDenoted_app]
      refine ⟨hcase.2 hok0 (fun _ => hkω), hok1, ℓ, _, _, hmem, ?_, ?_⟩
      · rw [hpay]; exact ha
      · intro h0 y _
        exact hKI.hyp.hM0 h0 _
  · -- in the conclusion
    rw [hconc]
    by_cases hw : w = 0
    · by_cases h0 : ℓ = 0
      · subst hw
        rw [fixRecBodyAVI_zero h0, interp_prf]
        obtain ⟨y, hy⟩ := famK_inhab_zero_ind hKI.toFixKI₀ h0 _ t hfitI ht
        have := eq_pt_of_mem_univZero (hKI.hyp.hM0 h0 t) hy
        subst this
        exact hy
      · exact (hsqfacts hw h0).2
    · rw [fixRecBodyAVI_pos hw]
      have hcase := caseRec_factsI hw hKI.hyp
        (fun D' j' σ' hfr' hj' => FixKI.ihArgsOk_tele hKI hw hfr' hj') Fss.length (D := 1) (j := 0)
        (σ := cons t (consList as (cons r ρb))) (k := .fst (.bvar 0)) hfr (Nat.zero_add _)
      obtain ⟨i, a, ha, hta⟩ := sumSet_elim hw ht'
      have htag : interp V (cons t (consList as (cons r ρb))) (.fst (.bvar 0)) = vnat i := by
        rw [interp_fst, interp_bvar, cons_zero, hta, sfst_inj]
      have hpay : interp V (cons t (consList as (cons r ρb))) (.snd (.bvar 0)) = a := by
        rw [interp_snd, interp_bvar, cons_zero, hta, ssnd_inj]
      have hkω : interp V (cons t (consList as (cons r ρb))) (.fst (.bvar 0)) ∈ˢ (omega : V) := by
        rw [htag]; exact vnat_mem_omega i
      obtain ⟨hmem, -⟩ := hcase.1 hkω
      rw [htag, motSem_vnat, Nat.zero_add] at hmem
      rw [interp_app, hpay]
      have := app_mem_piR hmem ha (fun h0 y _ => hKI.hyp.hM0 h0 _)
      rwa [injW_pos hw, ← hta] at this

/-- The semantic step at a bottom. -/
noncomputable def stepVI (ℓ w nP : Nat) (Fss Ess : List (List AnnotTerm)) (Ids : List AnnotTerm)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (rds : List (Nat × Nat × AnnotTerm)) (s : Nat)
    (ρb : Nat → V) : V :=
  lamR s (interp V ρb (recTyAV Fss.length Ids.length rds)) fun r =>
    lamTower ℓ (cons r ρb) rds fun σ => interp V σ (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss)

/-- **The step's facts**: its value, its membership in
`RecTy → RecTy`, its grading. -/
theorem stepAV_facts (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) (ρb : Nat → V) :
    interp V ρb (fixStepAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s) = stepVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb ∧
    stepVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb
      ∈ˢ piR (s) (interp V ρb (recTyAV Fss.length Ids.length rds))
          (fun _ => interp V ρb (recTyAV Fss.length Ids.length rds)) ∧
    WellDenoted V ρb (fixStepAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s) := by
  have hleaf : ∀ r, r ∈ˢ interp V ρb (recTyAV Fss.length Ids.length rds) →
      ∀ bs, SpineFit (cons r ρb) (rds.map (·.2.2)) bs →
        WellDenoted V (consList bs (cons r ρb)) (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss) ∧
        interp V (consList bs (cons r ρb)) (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss)
          ∈ˢ interp V (consList bs (cons r ρb)) (recConcAV Fss.length Ids.length) ∧
        (ℓ = 0 → interp V (consList bs (cons r ρb)) (recConcAV Fss.length Ids.length) ∈ˢ (univZero : V)) := by
    intro r hr bs hsp
    rcases List.eq_nil_or_concat bs with rfl | ⟨as, t, rfl⟩
    · have := hsp.length_eq
      rw [List.length_map, h.hlen] at this
      simp at this
    · rw [List.concat_eq_append] at hsp ⊢
      exact body_facts h ρb hr hsp
  have hmemTower : ∀ r, r ∈ˢ interp V ρb (recTyAV Fss.length Ids.length rds) →
      lamTower ℓ (cons r ρb) rds (fun σ => interp V σ (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss))
        ∈ˢ interp V ρb (recTyAV Fss.length Ids.length rds) := by
    intro r hr
    rw [recTy_bottom h ρb (cons r ρb)]
    exact lamTower_mem h.hz (towerWalk_of_leaves fun bs hsp => ⟨(hleaf r hr bs hsp).2.1, (hleaf r hr bs hsp).2.2⟩)
  refine ⟨?_, ?_, ?_⟩
  · unfold fixStepAVI stepVI
    rw [interp_lam]
    exact lamR_congr fun r _ => interp_mkLamsC ℓ _ rds (cons r ρb)
  · unfold stepVI
    exact lamR_mem fun r hr => hmemTower r hr
  · unfold fixStepAVI
    rw [WellDenoted_lam]
    refine ⟨(h.hRecTy ρb).2, fun r hr => ?_, fun _ => interp V ρb (recTyAV Fss.length Ids.length rds),
      fun r hr => ?_, fun h0 _ _ => ?_⟩
    · exact mkLamsC_wellDenoted h.hz (underTowerOk_of_walk (h.hdoms (cons r ρb)) (hleaf r hr))
    · rw [interp_mkLamsC]
      exact hmemTower r hr
    · have := (h.hRecTy ρb).1
      rwa [h0, univ_zero] at this

/-! ## The body's iota at a walk leaf -/

/-- The recursive route's data at a K-frame `(ρb, r, p⃗, M, m⃗, ı⃗)`:
the block `(p⃗, M, m⃗)` and the index tuple. -/
theorem kframe_split (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) {ρ : Nat → V} {as : List V}
    {t : V} (hsp : SpineFit ρ (rds.map (·.2.2)) (as ++ [t])) :
    ∃ as₀ is, as = as₀ ++ is ∧ as₀.length = nP + 1 + Fss.length ∧ is.length = Ids.length := by
  have hlen_as : as.length = nP + 1 + Fss.length + Ids.length := by
    have := hsp.length_eq
    rw [List.length_append, List.length_singleton, List.length_map, h.hlen] at this
    omega
  exact ⟨as.take (nP + 1 + Fss.length), as.drop (nP + 1 + Fss.length), (List.take_append_drop _ _).symm,
    by rw [List.length_take]; omega, by rw [List.length_drop]; omega⟩

omit [SetTheory V] in
/-- The parameter frame of a K-frame over a bottom: the bottom under
the parameters. -/
theorem frP_block {ρb : Nat → V} {as₀ is : List V} (hl₀ : as₀.length = nP + 1 + Fss.length)
    (hli : is.length = Ids.length) :
    frP Fss.length Ids.length (consList (as₀ ++ is) ρb) = consList (as₀.take nP) ρb := by
  rw [frP_of Fss.length Ids.length hli]
  have hsplit : as₀ = as₀.take nP ++ as₀.drop nP := (List.take_append_drop _ _).symm
  conv => lhs; rw [hsplit]
  rw [consList_append, show Fss.length + 1 = (as₀.drop nP).length from by
    rw [List.length_drop]; omega, shiftE_consList]

/-- **The body's iota** at a walk leaf whose major is a constructor
value: the minor at the fields and the ih values (the λ-towers over the
recursive fields' telescopes of the function at the block, the calls'
index values and the field applied to the telescope's values). -/
theorem body_iota (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) (hw : w ≠ 0) (hℓ : ℓ ≠ 0)
    (ρb : Nat → V) {r : V} (hr : r ∈ˢ interp V ρb (recTyAV Fss.length Ids.length rds))
    {as : List V} {t : V} (hsp : SpineFit (cons r ρb) (rds.map (·.2.2)) (as ++ [t]))
    {j : Nat} (hj : j < Fss.length) {fs : List V} (hlen : fs.length = (Fss.getD j []).length)
    (hmaj : t = inj j (mkTower (fs ++ [pt]))) :
    interp V (consList (as ++ [t]) (cons r ρb)) (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss)
      = (fs ++ (recIdx (rss.getD j []) (Fss.getD j []).length).map fun i =>
          lamTower ℓ (consList (fs.take i) (frP Fss.length Ids.length (consList as (cons r ρb))))
            ((tlss.getD j []).getD i []) fun σ' =>
              (frKSpine nP Fss.length Ids.length (consList as (cons r ρb)) ++
                (((Eiss.getD j []).getD i []).map (interp V σ')) ++
                [(frameIdx ((tlss.getD j []).getD i []).length σ').foldl SetTheory.app (fs.getD i pt)]).foldl
                SetTheory.app r).foldl SetTheory.app
          (frMs Fss.length Ids.length (consList as (cons r ρb)) j) := by
  have hKI := fixKI_of h ρb hr hsp
  obtain ⟨-, ht⟩ := h.hK (cons r ρb) as t hsp
  rw [← consList_snoc']
  have hfr : RecFrameS 1 (consList as (cons r ρb)) (cons t (consList as (cons r ρb))) := by
    unfold RecFrameS
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  have ht' : t ∈ˢ sumSet w (sumFibre w (consList as (cons r ρb))
      (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)) := by
    rw [← hKI.hyp.hfam]; exact ht
  have hlen_as : as.length = nP + 1 + Fss.length + Ids.length := by
    have := hsp.length_eq
    rw [List.length_append, List.length_singleton, List.length_map, h.hlen] at this
    omega
  rw [fixRecBodyAVI_pos hw]
  have hcase := caseRec_factsI hw hKI.hyp
    (fun D' j' σ' hfr' hj' => FixKI.ihArgsOk_tele hKI hw hfr' hj') Fss.length (D := 1) (j := 0)
    (σ := cons t (consList as (cons r ρb))) (k := .fst (.bvar 0)) hfr (Nat.zero_add _)
  have htag : interp V (cons t (consList as (cons r ρb))) (.fst (.bvar 0)) = vnat j := by
    rw [interp_fst, interp_bvar, cons_zero, hmaj, sfst_inj]
  have hpay : interp V (cons t (consList as (cons r ρb))) (.snd (.bvar 0)) = mkTower (fs ++ [pt]) := by
    rw [interp_snd, interp_bvar, cons_zero, hmaj, ssnd_inj]
  have hkω : interp V (cons t (consList as (cons r ρb))) (.fst (.bvar 0)) ∈ˢ (omega : V) := by
    rw [htag]; exact vnat_mem_omega j
  have hsel := (hcase.1 hkω).2 j htag hj
  rw [Nat.zero_add] at hsel
  rw [interp_app, hsel, hpay]
  -- the payload is in the fibre
  obtain ⟨j', a, ha, hta⟩ := sumSet_elim hw ht'
  rw [hmaj] at hta
  obtain ⟨rfl, rfl⟩ := inj_inj hta
  unfold baseSemI
  rw [app_lamR_pos hℓ ha, ihValsI_mk hlen, frR_of nP Fss.length Ids.length hlen_as]
  congr 2
  rw [← projList_eq_map_range, ← hlen]
  apply List.ext_getElem
  · rw [projList_length]
  · intro i h1 h2
    rw [projList_get _ _ _ (by rwa [projList_length] at h1), projS_mkTower_getD h2,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-! ## The candidate fixed point -/

/-- The candidate's body at a leaf frame: the point at level zero,
else the recursor's graph's selector at the major's element (the
squash regime's at the tuple). -/
noncomputable def gStar (ℓ u w : Nat) (Fss Ess Fss₀ : List (List AnnotTerm)) (Ids : List AnnotTerm)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (σ : Nat → V) : V :=
  if ℓ = 0 then pt
  else if w = 0 then
    recSel (sqGraph ℓ u (frP Fss.length Ids.length (shiftE 1 0 σ)) (frM Fss.length Ids.length (shiftE 1 0 σ)) Ids
      (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 []) (Fss.getD 0 []).length
      (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) (frMs Fss.length Ids.length (shiftE 1 0 σ) 0))
      (tupW u (frameIdx Ids.length (shiftE 1 0 σ)))
  else
    recSel (elemGraph ℓ u (frP Fss.length Ids.length (shiftE 1 0 σ)) (frM Fss.length Ids.length (shiftE 1 0 σ)) Ids
      rss tlss Eiss Fss (frMsL Fss.length Ids.length (shiftE 1 0 σ))
      (famK u w (shiftE 1 0 σ) Fss Ess Fss₀ Ids rss tlss Eiss))
      (kpair (tupW u (frameIdx Ids.length (shiftE 1 0 σ))) (σ 0))

/-- The candidate: the semantic tower over the recursor's binder data. -/
noncomputable def rStar (ℓ w u : Nat) (Fss Ess Fss₀ : List (List AnnotTerm)) (Ids : List AnnotTerm)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (rds : List (Nat × Nat × AnnotTerm))
    (ρb : Nat → V) : V :=
  lamTower ℓ ρb rds (gStar ℓ u w Fss Ess Fss₀ Ids rss tlss Eiss)

omit [SetTheory V] in
theorem leaf_zero (as : List V) (t : V) (ρb : Nat → V) : consList (as ++ [t]) ρb 0 = t := by
  rw [← consList_snoc', cons_zero]

/-- The conclusion at a walk leaf over a K-frame with the core package. -/
theorem conc_leaf {K : Nat → V} (h0 : FixKI₀ ℓ w u K Fss Ess Fss₀ Ids rss tlss Eiss) (t : V) :
    interp V (cons t K) (recConcAV Fss.length Ids.length)
      = SetTheory.app ((frameIdx Ids.length K).foldl SetTheory.app (frM Fss.length Ids.length K)) t := by
  have hfr : RecFrameS 1 K (cons t K) := by
    unfold RecFrameS
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  obtain ⟨hMv, -⟩ := motApp_facts hfr h0.hyp.toRecHypCore
  unfold recConcAV
  rw [interp_app, hMv, interp_bvar, cons_zero]
  rfl

/-- **The candidate's body lands in the conclusion** at every walk
leaf. -/
theorem gStar_leaf (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) (ρb : Nat → V)
    {as : List V} {t : V} (hsp : SpineFit ρb (rds.map (·.2.2)) (as ++ [t])) :
    gStar ℓ u w Fss Ess Fss₀ Ids rss tlss Eiss (consList (as ++ [t]) ρb)
      ∈ˢ interp V (consList (as ++ [t]) ρb) (recConcAV Fss.length Ids.length) := by
  obtain ⟨h0, ht⟩ := h.hK ρb as t hsp
  rw [← consList_snoc', conc_leaf h0 t]
  unfold gStar
  rw [shiftE_succ_cons, shiftE_zero_zero, cons_zero]
  have hfit := h0.hyp.hfit
  by_cases hℓ : ℓ = 0
  · rw [if_pos hℓ]
    by_cases hw : w = 0
    · subst hw
      obtain ⟨y, hy⟩ := famK_inhab_zero_ind h0 hℓ _ t hfit ht
      have := eq_pt_of_mem_univZero (h0.hyp.hM0 hℓ t) hy
      subst this; exact hy
    · obtain ⟨y, hy⟩ := famK_inhab_zero_pos h0 hw hℓ _ t hfit ht
      have := eq_pt_of_mem_univZero (h0.hyp.hM0 hℓ t) hy
      subst this; exact hy
  · rw [if_neg hℓ]
    by_cases hw : w = 0
    · subst hw
      rw [if_pos rfl]
      have hfam' := famApp_mem_univ
        (fixFamI_mem u 0 (frP Fss.length Ids.length (consList as ρb)) Ids rss tlss Eiss Fss₀ Ess)
        (tupW u (frameIdx Ids.length (consList as ρb)))
      rw [univ_zero] at hfam'
      have ht' := ht
      unfold famK at ht'
      have htpt : t = pt := eq_pt_of_mem_univZero hfam' ht'
      subst htpt
      exact (sqK_facts hℓ h0 rfl rfl rfl _ pt hfit ht').2.1
    · rw [if_neg hw]
      exact (elemK_facts h0 hw hℓ hfit ht).1

/-- **The candidate inhabits the recursor's type.** -/
theorem rStar_mem (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) (ρb : Nat → V) :
    rStar ℓ w u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb ∈ˢ interp V ρb (recTyAV Fss.length Ids.length rds) := by
  unfold rStar recTyAV
  refine lamTower_mem h.hz (towerWalk_of_leaves fun bs hsp => ?_)
  rcases List.eq_nil_or_concat bs with rfl | ⟨as, t, rfl⟩
  · have := hsp.length_eq
    rw [List.length_map, h.hlen] at this
    simp at this
  · rw [List.concat_eq_append] at hsp ⊢
    exact ⟨gStar_leaf h ρb hsp, fun h0 => h.hconc0 h0 ρb _ hsp⟩

/-- The candidate's application along a fitting spine (nonzero level). -/
theorem rStar_fold (_h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) (hℓ : ℓ ≠ 0) (ρb : Nat → V)
    {bs : List V} (hsp : SpineFit ρb (rds.map (·.2.2)) bs) :
    bs.foldl SetTheory.app (rStar ℓ w u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb)
      = gStar ℓ u w Fss Ess Fss₀ Ids rss tlss Eiss (consList bs ρb) :=
  lamTower_fold hℓ hsp

omit [SetTheory V] in
/-- The K-frame's minors over two bottoms. -/
theorem frMs_bottom {as₀ is : List V} (hl₀ : as₀.length = nP + 1 + Fss.length) (hli : is.length = Ids.length)
    (ρ₁ ρ₂ : Nat → V) {j : Nat} (hj : j < Fss.length) :
    frMs Fss.length Ids.length (consList (as₀ ++ is) ρ₁) j
      = frMs Fss.length Ids.length (consList (as₀ ++ is) ρ₂) j := by
  rw [frMs_of Fss.length Ids.length hli ρ₁ hj, frMs_of Fss.length Ids.length hli ρ₂ hj]
  exact agreeOff_consList_ge as₀ ρ₁ ρ₂ _ (by omega)

/-- The elements' graph at a K-frame depends on the block only. -/
theorem elemGraph_block {ρb : Nat → V} {as₀ is is' : List V}
    (hli : is.length = Ids.length) (hli' : is'.length = Ids.length) :
    elemGraph ℓ u (frP Fss.length Ids.length (consList (as₀ ++ is) ρb))
        (frM Fss.length Ids.length (consList (as₀ ++ is) ρb)) Ids rss tlss Eiss Fss
        (frMsL Fss.length Ids.length (consList (as₀ ++ is) ρb))
        (famK u w (consList (as₀ ++ is) ρb) Fss Ess Fss₀ Ids rss tlss Eiss)
      = elemGraph ℓ u (frP Fss.length Ids.length (consList (as₀ ++ is') ρb))
        (frM Fss.length Ids.length (consList (as₀ ++ is') ρb)) Ids rss tlss Eiss Fss
        (frMsL Fss.length Ids.length (consList (as₀ ++ is') ρb))
        (famK u w (consList (as₀ ++ is') ρb) Fss Ess Fss₀ Ids rss tlss Eiss) := by
  have hMs : frMsL Fss.length Ids.length (consList (as₀ ++ is) ρb)
      = frMsL Fss.length Ids.length (consList (as₀ ++ is') ρb) := by
    unfold frMsL
    apply List.map_congr_left
    intro j hj
    rw [frMs_of Fss.length Ids.length hli ρb (List.mem_range.mp hj),
      frMs_of Fss.length Ids.length hli' ρb (List.mem_range.mp hj)]
  unfold famK
  rw [frP_of Fss.length Ids.length hli, frP_of Fss.length Ids.length hli', frM_of Fss.length Ids.length hli,
    frM_of Fss.length Ids.length hli', hMs]

set_option maxHeartbeats 3200000 in
/-- **The candidate's body is the unfolding's body** at every walk
leaf: the fixed-point equation, leafwise — both are the minor at the
major's fields and the ih towers, the body's folding the candidate
along the recursive calls' spines (which land at the leaf frames over
the tower's own bottom), the candidate's the graph's selector at the
calls' elements (the recursion equation). -/
theorem leaf_eq (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) (hw : w ≠ 0) (hℓ : ℓ ≠ 0)
    (ρb : Nat → V) {as : List V} {t : V}
    (hsp : SpineFit (cons (rStar ℓ w u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb) ρb) (rds.map (·.2.2)) (as ++ [t])) :
    interp V (consList (as ++ [t]) (cons (rStar ℓ w u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb) ρb))
        (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss)
      = gStar ℓ u w Fss Ess Fss₀ Ids rss tlss Eiss (consList (as ++ [t]) ρb) := by
  have hR := rStar_mem h ρb
  have hcl : ∀ k d, rds[k]? = some d → Term.bvarsBelow (([] : List V).length + k) d.2.2.erase := by
    simpa using h.hclosed
  have hsp₀ : SpineFit ρb (rds.map (·.2.2)) (as ++ [t]) :=
    spineFit_closed_bottom (as := []) (ρ₁ := cons (rStar ℓ w u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb) ρb) hcl hsp
  obtain ⟨h0, ht⟩ := h.hK ρb as t hsp₀
  obtain ⟨as₀, is, rfl, hl₀, hli⟩ := kframe_split h hsp₀
  have hfi : frameIdx Ids.length (consList (as₀ ++ is) ρb) = is := frameIdx_of Ids.length hli ρb
  have hfit : SpineFit (frP Fss.length Ids.length (consList (as₀ ++ is) ρb)) Ids is := by
    have := h0.hyp.hfit; rwa [hfi] at this
  rw [hfi] at ht
  have hfam : ∀ t', SetTheory.app (famK u w (consList (as₀ ++ is) ρb) Fss Ess Fss₀ Ids rss tlss Eiss) t'
      ∈ˢ (univ w : V) :=
    fun t' => famApp_mem_univ (fixFamI_mem u w (frP Fss.length Ids.length (consList (as₀ ++ is) ρb)) Ids rss tlss
      Eiss Fss₀ Ess) t'
  obtain ⟨j, fs, hmaj, hj, hlen, hspR, hidx, hslots⟩ := famK_elim h0 hw hfit ht
  -- the left-hand side: the body's iota
  rw [body_iota h hw hℓ ρb hR hsp hj hlen hmaj, frMs_bottom (nP := nP) hl₀ hli (cons _ ρb) ρb hj]
  -- the right-hand side: the recursion equation
  unfold gStar
  rw [if_neg hℓ, if_neg hw, shiftE_leaf, leaf_zero, hfi, (elemK_facts h0 hw hℓ hfit ht).2, hmaj]
  unfold elemSt
  rw [elemTag_mk, elemFields_mk _ hlen, frMsL_getD Fss.length Ids.length _ hj]
  congr 2
  unfold elemIhs
  apply List.map_congr_left
  intro i hi
  obtain ⟨hik, -⟩ := mem_recIdx.mp hi
  obtain ⟨hslot, hmem⟩ := hslots i hi
  -- the parameter prefix fits
  have hpre : SpineFit ρb ((rds.take (nP + 1 + Fss.length)).map (·.2.2)) as₀ := by
    have := spineFit_prefix (as := as₀) (bs := is ++ [t]) (by rw [← List.append_assoc]; exact hsp₀)
    rwa [hl₀, ← List.map_take] at this
  have hshift : shiftE (Fss.length + 1) 0 (consList as₀ ρb) = frP Fss.length Ids.length (consList (as₀ ++ is) ρb) :=
    (frP_of Fss.length Ids.length hli ρb).symm
  -- the towers agree: the telescope and the index expressions do not see the bottom
  have hlenPre : (as₀.take nP ++ fs.take i).length = nP + i := by
    rw [List.length_append, List.length_take, List.length_take, hlen, Nat.min_eq_left (by omega),
      Nat.min_eq_left (Nat.le_of_lt hik)]
  have hcl' : ∀ k d, ((tlss.getD j []).getD i [])[k]? = some d →
      Term.bvarsBelow ((as₀.take nP ++ fs.take i).length + k) d.2.2.erase := by
    intro k d hd
    rw [hlenPre]
    have hk : k < ((tlss.getD j []).getD i []).length := (List.getElem?_eq_some_iff.mp hd).1
    have := (h.hTbelow j i).getD_below k hk
    rwa [List.getD_eq_getElem?_getD, hd, Option.getD_some] at this
  rw [frP_block (nP := nP) hl₀ hli, frP_block (nP := nP) hl₀ hli, ← consList_append, ← consList_append]
  refine lamTower_congr_bottom hcl' fun bs hbs => ?_
  have hbs₂ : SpineFit (consList (as₀.take nP ++ fs.take i) ρb) (((tlss.getD j []).getD i []).map (·.2.2)) bs :=
    spineFit_closed_bottom hcl' hbs
  have hlenbs : bs.length = ((tlss.getD j []).getD i []).length := by rw [hbs.length_eq, List.length_map]
  have hEq : ((Eiss.getD j []).getD i []).map
      (interp V (consList (as₀.take nP ++ fs.take i ++ bs)
        (cons (rStar ℓ w u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb) ρb)))
      = ((Eiss.getD j []).getD i []).map (interp V (consList (as₀.take nP ++ fs.take i ++ bs) ρb)) := by
    apply List.map_congr_left
    intro E hE
    exact interp_closed_bottom (h.hEbelow j i E hE) (by rw [List.length_append, hlenPre, hlenbs]) _ _
  have hfrI : ∀ ρ : Nat → V, frameIdx ((tlss.getD j []).getD i []).length (consList (as₀.take nP ++ fs.take i ++ bs) ρ) = bs := by
    intro ρ
    rw [consList_append, ← hlenbs]
    exact frameIdx_consList' bs _
  rw [frKSpine_of nP Fss.length Ids.length hl₀ hli, hEq, hfrI, hfrI]
  -- the call's element is a predecessor; the selector there is the candidate's leaf
  have hbs₃ : SpineFit (consList (fs.take i) (frP Fss.length Ids.length (consList (as₀ ++ is) ρb)))
      (((tlss.getD j []).getD i []).map (·.2.2)) bs := by
    rw [frP_block (nP := nP) hl₀ hli, ← consList_append]; exact hbs₂
  obtain ⟨-, hvsp⟩ := hslot.2.2 bs hbs₃
  rw [consList_append (fs.take i) bs] at hvsp
  have hfmem := slotSet_fold_mem hfam hmem hbs₃
  have hpred := (mem_elemPred_mk (t := tupW u is) hlen).mpr
    ⟨mk_mem_elemSet (tupW_mem hvsp) hfmem, i, hi, bs, hbs₃, rfl⟩
  have hspi := h.hspine ρb as₀ hpre _ (bs.foldl SetTheory.app (fs.getD i pt)) (by rw [hshift]; exact hvsp)
    (by rw [hshift]; exact hfmem)
  have hvsp' := hvsp
  rw [frP_block (nP := nP) hl₀ hli, ← consList_append (as₀.take nP) (fs.take i) ρb,
    ← consList_append (as₀.take nP ++ fs.take i) bs ρb] at hpred hspi hvsp'
  rw [app_graph hpred, rStar_fold h hℓ ρb hspi]
  unfold gStar
  rw [if_neg hℓ, if_neg hw, shiftE_leaf, leaf_zero, frameIdx_of Ids.length hvsp'.length_eq ρb,
    elemGraph_block hvsp'.length_eq hli, frP_block (nP := nP) hl₀ hli]

set_option maxHeartbeats 3200000 in
/-- **The body's value is the candidate's leaf** at the squash regime
(task #202 A2): both are the minor at the source spine and the
recursor at the predecessors — the body's ih towers fold the candidate
along the recursive calls' spines, which land at the leaf frames over
the tower's own bottom. -/
theorem leaf_eq_sq (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) (hw : w = 0) (hℓ : ℓ ≠ 0)
    (ρb : Nat → V) {as : List V} {t : V}
    (hsp : SpineFit (cons (rStar ℓ w u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb) ρb) (rds.map (·.2.2)) (as ++ [t])) :
    interp V (consList (as ++ [t]) (cons (rStar ℓ w u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb) ρb))
        (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss)
      = gStar ℓ u w Fss Ess Fss₀ Ids rss tlss Eiss (consList (as ++ [t]) ρb) := by
  subst hw
  have hR := rStar_mem h ρb
  have hcl : ∀ k d, rds[k]? = some d → Term.bvarsBelow (([] : List V).length + k) d.2.2.erase := by
    simpa using h.hclosed
  have hsp₀ : SpineFit ρb (rds.map (·.2.2)) (as ++ [t]) :=
    spineFit_closed_bottom (as := []) (ρ₁ := cons (rStar ℓ 0 u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb) ρb) hcl hsp
  obtain ⟨h0, ht⟩ := h.hK ρb as t hsp₀
  have hKI := fixKI_of h ρb hR hsp
  obtain ⟨-, ht₁⟩ := h.hK (cons (rStar ℓ 0 u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb) ρb) as t hsp
  have hlen_as : as.length = nP + 1 + Fss.length + Ids.length := by
    have := hsp₀.length_eq
    rw [List.length_append, List.length_singleton, List.length_map, h.hlen] at this
    omega
  obtain ⟨ps, ms, is, M, rfl, hlenP, hlenM, hlenI⟩ := kframe_split3 hlen_as
  have hlen₀ : (ps ++ [M] ++ ms).length = nP + 1 + Fss.length := by
    simp only [List.length_append, List.length_singleton]; omega
  obtain ⟨hle, -, -⟩ := h0.hsq rfl hℓ
  rw [consList_kframe] at hKI ht₁ h0 ht
  have hfrP₀ := kframe_frP' (ρP := consList ps ρb) (M := M) hlenI hlenM
  have hfrP₁ := kframe_frP' (ρP := consList ps (cons (rStar ℓ 0 u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb) ρb))
    (M := M) hlenI hlenM
  have hfrM₀ := kframe_frM' (ρP := consList ps ρb) (M := M) hlenI hlenM
  have hfrI₀ := kframe_frameIdx' (nIdx := Ids.length) hlenI (consList ms (cons M (consList ps ρb)))
  have ht' : t ∈ˢ SetTheory.app (fixFamI u 0 (consList ps ρb) Ids Ids.length rss tlss Eiss Fss₀ Ess)
      (tupW u is) := by
    unfold famK at ht; rwa [hfrP₀, hfrI₀] at ht
  have ht₁' : t ∈ˢ SetTheory.app
      (fixFamI u 0 (consList ps (cons (rStar ℓ 0 u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb) ρb)) Ids Ids.length
        rss tlss Eiss Fss₀ Ess) (tupW u is) := by
    unfold famK at ht₁; rwa [hfrP₁, kframe_frameIdx' hlenI] at ht₁
  have hfit : SpineFit (consList ps ρb) Ids is := by
    have := h0.hyp.hfit; rwa [hfrP₀, hfrI₀] at this
  have hsingle : Fss.length = 1 := by
    have hX := h0.hX
    have hreal := h0.hreal
    rw [hfrP₀] at hX hreal
    exact fam_single_of_mem hX hreal hle hfit ht'
  have hfrMs₀ := kframe_frMs' (ρP := consList ps ρb) (M := M) hlenI hlenM (by omega)
  -- the left-hand side: the body's value
  rw [← consList_snoc', consList_kframe, fixRecBodyAVI_sq hℓ]
  have hf := sqFixBody_facts hℓ hlenP hlenM hlenI hKI ht₁'
  rw [hf.2.1]
  -- the right-hand side: the selector's recursion equation
  have hfam' := famApp_mem_univ (fixFamI_mem u 0 (consList ps ρb) Ids rss tlss Eiss Fss₀ Ess) (tupW u is)
  rw [univ_zero] at hfam'
  have htpt : t = pt := eq_pt_of_mem_univZero hfam' ht'
  subst htpt
  unfold gStar
  rw [if_neg hℓ, if_pos rfl, shiftE_leaf, consList_kframe, hfrP₀, hfrM₀, hfrMs₀, hfrI₀]
  have hK := sqK_facts hℓ (ρP := consList ps ρb) (M := M) (m := ms.getD 0 pt) h0 hfrP₀ hfrM₀ hfrMs₀ is pt hfit ht'
  rw [hK.2.2]
  obtain ⟨-, hfit₀, -⟩ := sqK_source hℓ h0 hfrP₀ hfit ht'
  have hfam : ∀ t', SetTheory.app (fixFamI u 0 (consList ps ρb) Ids Ids.length rss tlss Eiss Fss₀ Ess) t'
      ∈ˢ (univZero : V) := by
    intro t'
    have := famApp_mem_univ (fixFamI_mem u 0 (consList ps ρb) Ids rss tlss Eiss Fss₀ Ess) t'
    rwa [univ_zero] at this
  have hfam₀ : ∀ t', SetTheory.app (fixFamI u 0 (consList ps ρb) Ids Ids.length rss tlss Eiss Fss₀ Ess) t'
      ∈ˢ (univ 0 : V) := by
    intro t'; rw [univ_zero]; exact hfam t'
  have hlenF₀ : (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)).length = (Fss.getD 0 []).length := by
    rw [srcVals_length, srcList_length]
  -- the parameter prefix fits
  have hpre : SpineFit ρb ((rds.take (nP + 1 + Fss.length)).map (·.2.2)) (ps ++ [M] ++ ms) := by
    have := spineFit_prefix (as := ps ++ [M] ++ ms) (bs := is ++ [pt])
      (by rw [← List.append_assoc]; exact hsp₀)
    rwa [hlen₀, ← List.map_take] at this
  have hshift : shiftE (Fss.length + 1) 0 (consList (ps ++ [M] ++ ms) ρb) = consList ps ρb := by
    rw [List.append_assoc, consList_append, show Fss.length + 1 = ([M] ++ ms).length from by simp [hlenM],
      shiftE_consList]
  -- the ih towers agree
  unfold sqIhValsK
  congr 2
  apply List.map_congr_left
  intro i hi
  obtain ⟨hik, -⟩ := mem_recIdx.mp hi
  obtain ⟨hslotfit, hslotmem⟩ := fixKI₀_slot h0 hfrP₀ hsingle _ hfit₀ i hi
  have hfpt : (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)).getD i pt = pt :=
    eq_pt_of_mem_slotSet_zero hfam hslotmem
  have hlenPre : (ps ++ (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)).take i).length = nP + i := by
    rw [List.length_append, List.length_take, hlenF₀, hlenP, Nat.min_eq_left (Nat.le_of_lt hik)]
  have hcl' : ∀ k d, ((tlss.getD 0 []).getD i [])[k]? = some d →
      Term.bvarsBelow ((ps ++ (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)).take i).length + k)
        d.2.2.erase := by
    intro k d hd
    rw [hlenPre]
    have hk : k < ((tlss.getD 0 []).getD i []).length := (List.getElem?_eq_some_iff.mp hd).1
    have := (h.hTbelow 0 i).getD_below k hk
    rwa [List.getD_eq_getElem?_getD, hd, Option.getD_some] at this
  rw [← consList_append, ← consList_append]
  refine lamTower_congr_bottom hcl' fun bs hbs => ?_
  have hbs₂ : SpineFit (consList (ps ++ (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)).take i) ρb)
      (((tlss.getD 0 []).getD i []).map (·.2.2)) bs := spineFit_closed_bottom hcl' hbs
  have hlenbs : bs.length = ((tlss.getD 0 []).getD i []).length := by rw [hbs.length_eq, List.length_map]
  have hEq : ((Eiss.getD 0 []).getD i []).map
      (interp V (consList (ps ++ (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)).take i ++ bs)
        (cons (rStar ℓ 0 u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb) ρb)))
      = ((Eiss.getD 0 []).getD i []).map
        (interp V (consList (ps ++ (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length)).take i ++ bs) ρb)) := by
    apply List.map_congr_left
    intro E hE
    exact interp_closed_bottom (h.hEbelow 0 i E hE)
      (by rw [List.length_append, hlenPre, hlenbs]) _ _
  -- the leaf: the candidate folded along the recursive call's spine
  show ((ps ++ [M]) ++ ms ++ ((Eiss.getD 0 []).getD i []).map (interp V _) ++
      [(frameIdx ((tlss.getD 0 []).getD i []).length _).foldl SetTheory.app _]).foldl SetTheory.app _
    = recSel _ (tupW u _)
  rw [hEq, hfpt, foldl_app_pt']
  -- the call's index values fit, the field's value is a proof at their tuple
  rw [consList_append] at hbs₂
  obtain ⟨-, hv⟩ := hslotfit.2.2 bs hbs₂
  rw [consList_append, ← consList_append ps, ← consList_append (ps ++ _)] at hv
  have hf := slotSet_fold_mem hfam₀ hslotmem hbs₂
  rw [hfpt, foldl_app_pt', ← consList_append ps, ← consList_append (ps ++ _)] at hf
  have hsp' := h.hspine ρb (ps ++ [M] ++ ms) hpre _ pt (by rw [hshift]; exact hv) (by rw [hshift]; exact hf)
  rw [rStar_fold h hℓ ρb hsp']
  unfold gStar
  rw [if_neg hℓ, if_pos rfl, shiftE_leaf, consList_kframe, kframe_frP' (M := M) hv.length_eq hlenM,
    kframe_frM' hv.length_eq hlenM, kframe_frMs' hv.length_eq hlenM (by omega),
    kframe_frameIdx' hv.length_eq]

/-- **The candidate is a fixed point of the step.** -/
theorem rStar_fixed (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) (ρb : Nat → V) :
    SetTheory.app (stepVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb) (rStar ℓ w u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb)
      = rStar ℓ w u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb := by
  by_cases hu : s = 0
  · have hℓ : ℓ = 0 := (recSort_zero_iff h).mp hu
    unfold stepVI rStar
    rw [hu, lamR_zero, app_pt]
    cases hr : rds with
    | nil => have := h.hlen; rw [hr] at this; simp at this
    | cons d ds =>
      show pt = lamR ℓ _ _
      rw [hℓ, lamR_zero]
  · have hℓ : ℓ ≠ 0 := fun h0 => hu ((recSort_zero_iff h).mpr h0)
    unfold stepVI
    rw [app_lamR_pos hu (rStar_mem h ρb)]
    have hcl : ∀ k d, rds[k]? = some d → Term.bvarsBelow (([] : List V).length + k) d.2.2.erase := by
      simpa using h.hclosed
    have := lamTower_congr_bottom (m := ℓ) (ds := rds) (as := [])
      (ρ₁ := cons (rStar ℓ w u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb) ρb) (ρ₂ := ρb)
      (g₁ := fun σ => interp V σ (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss))
      (g₂ := gStar ℓ u w Fss Ess Fss₀ Ids rss tlss Eiss) hcl ?_
    · exact this
    · intro bs hsp
      simp only [List.nil_append, consList_nil] at hsp ⊢
      rcases List.eq_nil_or_concat bs with rfl | ⟨as, t, rfl⟩
      · have := hsp.length_eq
        rw [List.length_map, h.hlen] at this
        simp at this
      · rw [List.concat_eq_append] at hsp ⊢
        by_cases hw : w = 0
        · exact leaf_eq_sq h hw hℓ ρb hsp
        · exact leaf_eq h hw hℓ ρb hsp

/-! ## The selection -/

/-- The sigma type's fibre function. -/
noncomputable def sigBKI (ℓ w nP : Nat) (Fss Ess : List (List AnnotTerm)) (Ids : List AnnotTerm)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (rds : List (Nat × Nat × AnnotTerm)) (s : Nat)
    (ρb : Nat → V) : V :=
  lamR 1 (interp V ρb (recTyAV Fss.length Ids.length rds)) fun r =>
    eqv (SetTheory.app (stepVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb) r) r

/-- The sigma type's value. -/
noncomputable def sigKI (ℓ w nP : Nat) (Fss Ess : List (List AnnotTerm)) (Ids : List AnnotTerm)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (rds : List (Nat × Nat × AnnotTerm)) (s : Nat)
    (ρb : Nat → V) : V :=
  sigmaSet s (interp V ρb (recTyAV Fss.length Ids.length rds))
    fun r => SetTheory.app (sigBKI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb) r

theorem sigBKI_app {ρb : Nat → V} {r : V} (hr : r ∈ˢ interp V ρb (recTyAV Fss.length Ids.length rds)) :
    SetTheory.app (sigBKI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb) r
      = eqv (SetTheory.app (stepVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb) r) r :=
  app_lamR_pos Nat.one_ne_zero hr

theorem sigBKI_mem (ρb : Nat → V) :
    sigBKI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb
      ∈ˢ psigmaFibreSpace V 0 (interp V ρb (recTyAV Fss.length Ids.length rds)) :=
  lamR_mem fun _ _ => by rw [univ_zero]; exact eqv_mem_univZero _ _

omit [SetTheory V] in
theorem max_zero' (u : Nat) : Nat.max u 0 = u := Nat.max_zero _

theorem psigmaV_mem_gen (u v : Nat) :
    psigmaV V u v ∈ˢ piR (Nat.max u v + 1) (univ u : V)
      (fun A => piR (Nat.max u v + 1) (psigmaFibreSpace V v A) fun _ => (univ (Nat.max u v) : V)) :=
  lamR_mem fun _ hA => lamR_mem fun _ hB => sigma_mem_univ hA (fun _ hx => psigmaFibre_apply V hB hx)

/-- `pt` witnesses the double negation of an inhabited set. -/
theorem pt_mem_dnegSpace2' {A x : V} (hx : x ∈ˢ A) : (pt : V) ∈ˢ dnegSpace V A := by
  unfold dnegSpace
  have h1 : piR 0 A (fun _ => (empty : V)) = empty := by
    rw [piR_zero]
    exact truthVal_eq_empty fun hf => not_mem_empty _ (hf x hx).choose_spec
  rw [h1, piR_zero_empty]
  exact pt_mem_unitSet

/-- **The sigma type's facts**: its value, its formation, its grading. -/
theorem fixSigAVI_facts (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) (ρb : Nat → V) :
    interp V ρb (fixSigAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s) = sigKI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb ∧
      sigKI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb ∈ˢ (univ (s) : V) ∧
      WellDenoted V ρb (fixSigAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s) := by
  obtain ⟨hTu, hTok⟩ := h.hRecTy ρb
  obtain ⟨hsv, hsm, hsok⟩ := stepAV_facts h ρb
  have hu0 : s = 0 → interp V ρb (recTyAV Fss.length Ids.length rds) ∈ˢ (univZero : V) := by
    intro h0; have := hTu; rwa [h0, univ_zero] at this
  -- the pieces under the sigma's λ
  have hT1 : ∀ r : V, interp V (cons r ρb) ((recTyAV Fss.length Ids.length rds).liftN 1 0)
      = interp V ρb (recTyAV Fss.length Ids.length rds) := by
    intro r; rw [interp_liftN, shiftE_succ_cons, shiftE_zero_zero]
  have hs1 : ∀ r : V, interp V (cons r ρb) ((fixStepAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s).liftN 1 0)
      = stepVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb := by
    intro r; rw [interp_liftN, shiftE_succ_cons, shiftE_zero_zero, hsv]
  have hs1ok : ∀ r : V, WellDenoted V (cons r ρb) ((fixStepAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s).liftN 1 0) := by
    intro r; rw [WellDenoted_liftN, shiftE_succ_cons, shiftE_zero_zero]; exact hsok
  have hbody : ∀ r : V, r ∈ˢ interp V ρb (recTyAV Fss.length Ids.length rds) →
      interp V (cons r ρb) (.eqE
        (.app ((fixStepAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s).liftN 1 0) (.bvar 0)) (.bvar 0))
        = eqv (SetTheory.app (stepVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb) r) r ∧
      WellDenoted V (cons r ρb) (.eqE
        (.app ((fixStepAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s).liftN 1 0) (.bvar 0)) (.bvar 0)) := by
    intro r hr
    refine ⟨?_, ?_⟩
    · rw [interp_eqE, interp_app, hs1, interp_bvar, cons_zero]
    · rw [WellDenoted_eqE, WellDenoted_app]
      refine ⟨⟨hs1ok r, trivial, s, interp V ρb (recTyAV Fss.length Ids.length rds),
        fun _ => interp V ρb (recTyAV Fss.length Ids.length rds), ?_, ?_, fun h0 _ _ => hu0 h0⟩, trivial⟩
      · rw [hs1]; exact hsm
      · rw [interp_bvar, cons_zero]; exact hr
  have hlamv : interp V ρb (.lam 1 (recTyAV Fss.length Ids.length rds)
      (.eqE
        (.app ((fixStepAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s).liftN 1 0) (.bvar 0)) (.bvar 0)))
      = sigBKI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb := by
    unfold sigBKI
    rw [interp_lam]
    exact lamR_congr fun r hr => (hbody r hr).1
  have hps := psigmaV_mem_gen (V := V) (s) 0
  rw [max_zero'] at hps
  have hv : interp V ρb (fixSigAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s) = sigKI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb := by
    show SetTheory.app (SetTheory.app (psigmaV V (s) 0)
      (interp V ρb (recTyAV Fss.length Ids.length rds))) (interp V ρb (.lam 1 _ _)) = _
    rw [hlamv, psigmaV_app V hTu (sigBKI_mem ρb), max_zero']
    rfl
  refine ⟨hv, ?_, ?_⟩
  · have := sigma_mem_univ (u := s) (v := 0) hTu
      (fun r hr => psigmaFibre_apply V (sigBKI_mem (ℓ := ℓ) (w := w) (nP := nP) (Fss := Fss) (Ess := Ess)
        (Ids := Ids) (rss := rss) (tlss := tlss) (Eiss := Eiss) (rds := rds) (s := s) ρb) hr)
    rwa [max_zero'] at this
  · show WellDenoted V ρb (.app (.app (.const .psigma [s, 0]) _) _)
    rw [WellDenoted_app]
    refine ⟨?_, ?_, ?_⟩
    · rw [WellDenoted_app]
      exact ⟨trivial, hTok, s + 1, univ (s),
        fun A => piR (s + 1) (psigmaFibreSpace V 0 A) fun _ => (univ (s) : V),
        hps, hTu, fun h => absurd h (Nat.succ_ne_zero _)⟩
    · rw [WellDenoted_lam]
      refine ⟨hTok, fun r hr => (hbody r hr).2, fun _ => (univ 0 : V), fun r hr => ?_,
        fun h => absurd h Nat.one_ne_zero⟩
      rw [(hbody r hr).1, univ_zero]; exact eqv_mem_univZero _ _
    · refine ⟨s + 1, psigmaFibreSpace V 0 (interp V ρb (recTyAV Fss.length Ids.length rds)),
        fun _ => (univ (s) : V), ?_, ?_, fun h => absurd h (Nat.succ_ne_zero _)⟩
      · show SetTheory.app (psigmaV V (s) 0) (interp V ρb (recTyAV Fss.length Ids.length rds)) ∈ˢ _
        exact app_mem_piR_pos (Nat.succ_ne_zero _) hps hTu
      · rw [hlamv]; exact sigBKI_mem ρb

/-- **The selected fixed point** — the recursor leaf's value: in the
recursor's type, a fixed point of the step, graded. -/
theorem fixSelAVI_facts (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) (ρb : Nat → V) :
    interp V ρb (fixSelAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s)
        ∈ˢ interp V ρb (recTyAV Fss.length Ids.length rds) ∧
      SetTheory.app (stepVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb)
          (interp V ρb (fixSelAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s))
        = interp V ρb (fixSelAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s) ∧
      WellDenoted V ρb (fixSelAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s) := by
  obtain ⟨hSv, hSu, hSok⟩ := fixSigAVI_facts h ρb
  obtain ⟨hTu, hTok⟩ := h.hRecTy ρb
  have hu0 : s = 0 → interp V ρb (recTyAV Fss.length Ids.length rds) ∈ˢ (univZero : V) := by
    intro h0; have := hTu; rwa [h0, univ_zero] at this
  -- the sigma type is inhabited by the candidate
  have hr₀ := rStar_mem h ρb
  have hfix₀ := rStar_fixed h ρb
  have hSne : ∃ x, x ∈ˢ sigKI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb := by
    by_cases hu : s = 0
    · refine ⟨pt, ?_⟩
      unfold sigKI
      subst hu
      exact pt_mem_sigma (a := rStar ℓ w u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb) (b := pt) hr₀
        (by rw [sigBKI_app hr₀, hfix₀]; exact pt_mem_eqv_self _)
    · refine ⟨spair (rStar ℓ w u Fss Ess Fss₀ Ids rss tlss Eiss rds ρb) pt, ?_⟩
      exact spair_mem hu hr₀ (by rw [sigBKI_app hr₀, hfix₀]; exact pt_mem_eqv_self _)
  have hchoice : interp V ρb (AnnotTerm.mkAppN (.const .choice [s])
      [fixSigAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s, .prf]) = schoice (sigKI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb) := by
    show SetTheory.app (SetTheory.app (choiceV V (s))
      (interp V ρb (fixSigAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s))) pt = _
    rw [hSv]
    exact choiceV_app V hSu (pt_mem_dnegSpace2' hSne.choose_spec)
  have hsel := schoice_mem hSne.choose_spec
  obtain ⟨a, b, ha, hb, hz, hpos⟩ := mem_sigma_elim hsel
  rw [sigBKI_app ha] at hb
  have hfixa : SetTheory.app (stepVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb) a = a := eq_of_mem_eqv hb
  have hval : interp V ρb (fixSelAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s) = a := by
    show sfst (interp V ρb (AnnotTerm.mkAppN (.const .choice [s]) [_, .prf])) = a
    rw [hchoice]
    by_cases hu : s = 0
    · rw [hz hu, sfst_pt]
      exact (eq_pt_of_mem_univZero (hu0 hu) ha).symm
    · rw [hpos hu, sfst_spair]
  refine ⟨by rw [hval]; exact ha, by rw [hval]; exact hfixa, ?_⟩
  have hchoiceV : choiceV V (s) ∈ˢ piR (s) (univ (s) : V)
      (fun A => piR (s) (dnegSpace V A) fun _ => A) :=
    lamR_mem fun _ _ => lamR_mem fun _ hh => schoice_mem (exists_mem_of_dneg V hh).choose_spec
  show WellDenoted V ρb (.fst (AnnotTerm.mkAppN (.const .choice [s])
    [fixSigAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s, .prf]))
  rw [WellDenoted_fst]
  refine ⟨?_, s, 0, interp V ρb (recTyAV Fss.length Ids.length rds),
    fun r => SetTheory.app (sigBKI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb) r, ?_, ?_, ?_⟩
  · show WellDenoted V ρb (.app (.app (.const .choice [s]) _) .prf)
    rw [WellDenoted_app]
    refine ⟨?_, trivial, s, dnegSpace V (sigKI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb),
      fun _ => sigKI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb, ?_, ?_, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨trivial, hSok, s, univ (s),
        fun A => piR (s) (dnegSpace V A) fun _ => A, hchoiceV, hSv ▸ hSu, fun hu0 A _ => ?_⟩
      show piR (s) _ _ ∈ˢ _
      rw [hu0]; exact piR_zero_mem_univZero
    · show SetTheory.app (choiceV V (s)) (interp V ρb (fixSigAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s)) ∈ˢ _
      rw [hSv]
      refine app_mem_piR hchoiceV hSu (fun hu0 A _ => ?_)
      show piR (s) _ _ ∈ˢ _
      rw [hu0]; exact piR_zero_mem_univZero
    · exact pt_mem_dnegSpace2' hSne.choose_spec
    · intro hu0 _ _
      subst hu0
      rwa [univ_zero] at hSu
  · rw [hchoice, max_zero']; exact hsel
  · exact hTu
  · intro r hr
    show SetTheory.app (sigBKI ℓ w nP Fss Ess Ids rss tlss Eiss rds s ρb) r ∈ˢ _
    rw [sigBKI_app hr, univ_zero]; exact eqv_mem_univZero _ _

/-! ## The leaf -/

/-- The recursor leaf: the selected fixed point (a closed term). -/
def nativeRecAVI (ℓ w nP : Nat) (Fss Ess : List (List AnnotTerm)) (Ids : List AnnotTerm)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (rds : List (Nat × Nat × AnnotTerm)) (s : Nat) :
    AnnotTerm :=
  fixSelAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s

/-- **The leaf inhabits the recursor's type's reading.** -/
theorem nativeRecAVI_mem (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) (ρb : Nat → V) :
    interp V ρb (nativeRecAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s)
      ∈ˢ interp V ρb (mkPisAV rds (recConcAV Fss.length Ids.length)) :=
  (fixSelAVI_facts h ρb).1

/-- **The leaf is graded.** -/
theorem nativeRecAVI_wellDenoted (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) (ρb : Nat → V) :
    WellDenoted V ρb (nativeRecAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s) :=
  (fixSelAVI_facts h ρb).2.2

/-- **The recursor's iota**: at a fitting spine whose major is
constructor `j`'s value, the recursor at the spine is minor `j` at the
fields and at the inductive hypotheses — the λ-towers over the
recursive fields' telescopes of the recursor itself at the block, the
calls' index values and the field applied to the telescope's values. -/
theorem nativeRecAVI_iota (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) (hw : w ≠ 0)
    (hℓ : ℓ ≠ 0) (ρb : Nat → V) {as : List V} {t : V} (hsp : SpineFit ρb (rds.map (·.2.2)) (as ++ [t]))
    {j : Nat} (hj : j < Fss.length) {fs : List V} (hlen : fs.length = (Fss.getD j []).length)
    (hmaj : t = inj j (mkTower (fs ++ [pt]))) :
    (as ++ [t]).foldl SetTheory.app (interp V ρb (nativeRecAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s))
      = (fs ++ (recIdx (rss.getD j []) (Fss.getD j []).length).map fun i =>
          lamTower ℓ (consList (fs.take i) (frP Fss.length Ids.length (consList as ρb)))
            ((tlss.getD j []).getD i []) fun σ' =>
              (frKSpine nP Fss.length Ids.length (consList as ρb) ++
                (((Eiss.getD j []).getD i []).map (interp V σ')) ++
                [(frameIdx ((tlss.getD j []).getD i []).length σ').foldl SetTheory.app (fs.getD i pt)]).foldl
                SetTheory.app
                (interp V ρb (nativeRecAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s))).foldl SetTheory.app
          (frMs Fss.length Ids.length (consList as ρb) j) := by
  obtain ⟨hR, hfix, -⟩ := fixSelAVI_facts h ρb
  have hu : s ≠ 0 := fun h0 => hℓ ((recSort_zero_iff h).mp h0)
  have hcl : ∀ k d, rds[k]? = some d → Term.bvarsBelow (([] : List V).length + k) d.2.2.erase := by
    simpa using h.hclosed
  -- the spine fits over the function too
  have hsp' : SpineFit (cons (interp V ρb (fixSelAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s)) ρb)
      (rds.map (·.2.2)) (as ++ [t]) :=
    spineFit_closed_bottom (as := []) (ρ₁ := ρb) hcl hsp
  obtain ⟨as₀, is, rfl, hl₀, hli⟩ := kframe_split h hsp
  -- unfold once, then fold the tower along the spine
  unfold nativeRecAVI
  conv => lhs; rw [← hfix]
  unfold stepVI
  rw [app_lamR_pos hu hR, lamTower_fold hℓ hsp']
  rw [body_iota h hw hℓ ρb hR hsp' hj hlen hmaj]
  rw [frMs_bottom (nP := nP) hl₀ hli (cons _ ρb) ρb hj]
  congr 2
  apply List.map_congr_left
  intro i hi
  obtain ⟨hik, -⟩ := mem_recIdx.mp hi
  have hlenPre : (as₀.take nP ++ fs.take i).length = nP + i := by
    rw [List.length_append, List.length_take, List.length_take, hlen, Nat.min_eq_left (by omega),
      Nat.min_eq_left (Nat.le_of_lt hik)]
  have hcl' : ∀ k d, ((tlss.getD j []).getD i [])[k]? = some d →
      Term.bvarsBelow ((as₀.take nP ++ fs.take i).length + k) d.2.2.erase := by
    intro k d hd
    rw [hlenPre]
    have hk : k < ((tlss.getD j []).getD i []).length := (List.getElem?_eq_some_iff.mp hd).1
    have := (h.hTbelow j i).getD_below k hk
    rwa [List.getD_eq_getElem?_getD, hd, Option.getD_some] at this
  rw [frP_block (nP := nP) hl₀ hli, frP_block (nP := nP) hl₀ hli, ← consList_append, ← consList_append,
    frKSpine_of nP Fss.length Ids.length hl₀ hli, frKSpine_of nP Fss.length Ids.length hl₀ hli]
  refine lamTower_congr_bottom hcl' fun bs hbs => ?_
  have hlenbs : bs.length = ((tlss.getD j []).getD i []).length := by rw [hbs.length_eq, List.length_map]
  have hEq : ((Eiss.getD j []).getD i []).map
      (interp V (consList (as₀.take nP ++ fs.take i ++ bs)
        (cons (interp V ρb (fixSelAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s)) ρb)))
      = ((Eiss.getD j []).getD i []).map (interp V (consList (as₀.take nP ++ fs.take i ++ bs) ρb)) := by
    apply List.map_congr_left
    intro E hE
    exact interp_closed_bottom (h.hEbelow j i E hE) (by rw [List.length_append, hlenPre, hlenbs]) _ _
  have hfrI : ∀ ρ : Nat → V, frameIdx ((tlss.getD j []).getD i []).length (consList (as₀.take nP ++ fs.take i ++ bs) ρ) = bs := by
    intro ρ
    rw [consList_append, ← hlenbs]
    exact frameIdx_consList' bs _
  rw [hEq, hfrI, hfrI]

/-- **The squash body's ih values do not see the bottom**: the
telescopes and the index expressions are scoped at the field's frame
(task #202 A2). -/
theorem sqIhValsK_bottom (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s)
    {ps : List V} (hlenP : ps.length = nP) (ms : List V) (M r : V) {fs : List V}
    (hlenF : fs.length = (Fss.getD 0 []).length) (ρ₁ ρ₂ : Nat → V) :
    sqIhValsK ℓ (consList ps ρ₁) ps ms M r (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 [])
        (Fss.getD 0 []).length fs
      = sqIhValsK ℓ (consList ps ρ₂) ps ms M r (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 [])
        (Fss.getD 0 []).length fs := by
  unfold sqIhValsK
  apply List.map_congr_left
  intro i hi
  obtain ⟨hik, -⟩ := mem_recIdx.mp hi
  have hlenPre : (ps ++ fs.take i).length = nP + i := by
    rw [List.length_append, List.length_take, hlenF, hlenP, Nat.min_eq_left (Nat.le_of_lt hik)]
  have hcl' : ∀ k d, ((tlss.getD 0 []).getD i [])[k]? = some d →
      Term.bvarsBelow ((ps ++ fs.take i).length + k) d.2.2.erase := by
    intro k d hd
    rw [hlenPre]
    have hk : k < ((tlss.getD 0 []).getD i []).length := (List.getElem?_eq_some_iff.mp hd).1
    have := (h.hTbelow 0 i).getD_below k hk
    rwa [List.getD_eq_getElem?_getD, hd, Option.getD_some] at this
  rw [← consList_append, ← consList_append]
  refine lamTower_congr_bottom hcl' fun bs hbs => ?_
  have hlenbs : bs.length = ((tlss.getD 0 []).getD i []).length := by
    rw [hbs.length_eq, List.length_map]
  have hEq : ((Eiss.getD 0 []).getD i []).map (interp V (consList (ps ++ fs.take i ++ bs) ρ₁))
      = ((Eiss.getD 0 []).getD i []).map (interp V (consList (ps ++ fs.take i ++ bs) ρ₂)) := by
    apply List.map_congr_left
    intro E hE
    exact interp_closed_bottom (h.hEbelow 0 i E hE)
      (by rw [List.length_append, hlenPre, hlenbs]) _ _
  have hfi : ∀ ρ : Nat → V, frameIdx ((tlss.getD 0 []).getD i []).length
      (consList (ps ++ fs.take i ++ bs) ρ) = bs := by
    intro ρ
    rw [consList_append, ← hlenbs, frameIdx_consList']
  rw [hEq, hfi, hfi]

/-- **The recursor's iota at the squash regime** (task #202 A2): at a
fitting spine `p⃗ M m⃗ ı⃗ t` (the major a proof), the recursor is the
(only) minor at the source spine — the fields read off the index
values — and the ih values, the λ-towers over the recursive fields'
telescopes of the recursor at the block, the calls' index values and
the field applied along the telescope. -/
theorem nativeRecAVI_iota_sq (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s)
    (hw : w = 0) (hℓ : ℓ ≠ 0) (ρb : Nat → V) {ps ms is : List V} {M t : V}
    (hlenP : ps.length = nP) (hlenM : ms.length = Fss.length) (hlenI : is.length = Ids.length)
    (hsp : SpineFit ρb (rds.map (·.2.2)) (ps ++ [M] ++ ms ++ is ++ [t])) :
    (ps ++ [M] ++ ms ++ is ++ [t]).foldl SetTheory.app
        (interp V ρb (nativeRecAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s))
      = (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) ++
          sqIhValsK ℓ (consList ps ρb) ps ms M
            (interp V ρb (nativeRecAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s))
            (rss.getD 0 []) (tlss.getD 0 []) (Eiss.getD 0 []) (Fss.getD 0 []).length
            (srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length))).foldl
          SetTheory.app (ms.getD 0 pt) := by
  subst hw
  obtain ⟨hR, hfix, -⟩ := fixSelAVI_facts h ρb
  have hu : s ≠ 0 := fun h0 => hℓ ((recSort_zero_iff h).mp h0)
  have hcl : ∀ k d, rds[k]? = some d → Term.bvarsBelow (([] : List V).length + k) d.2.2.erase := by
    simpa using h.hclosed
  unfold nativeRecAVI
  generalize hr : interp V ρb (fixSelAVI ℓ 0 nP Fss Ess Ids rss tlss Eiss rds s) = r at hR hfix ⊢
  have hsp' : SpineFit (cons r ρb) (rds.map (·.2.2)) (ps ++ [M] ++ ms ++ is ++ [t]) :=
    spineFit_closed_bottom (as := []) (ρ₁ := ρb) hcl hsp
  -- unfold once, then fold the tower along the spine
  conv => lhs; rw [← hfix]
  unfold stepVI
  rw [app_lamR_pos hu hR, lamTower_fold hℓ hsp']
  -- the K-frame package over the function
  have hKI := fixKI_of h ρb hR hsp'
  obtain ⟨-, ht₁⟩ := h.hK (cons r ρb) (ps ++ [M] ++ ms ++ is) t hsp'
  rw [consList_kframe] at hKI ht₁
  have ht₁' : t ∈ˢ SetTheory.app
      (fixFamI u 0 (consList ps (cons r ρb)) Ids Ids.length rss tlss Eiss Fss₀ Ess) (tupW u is) := by
    unfold famK at ht₁
    rwa [kframe_frP' (M := M) hlenI hlenM, kframe_frameIdx' hlenI] at ht₁
  rw [← consList_snoc', consList_kframe, fixRecBodyAVI_sq hℓ]
  have hf := sqFixBody_facts hℓ hlenP hlenM hlenI hKI ht₁'
  rw [hf.2.1, sqIhValsK_bottom h hlenP ms M r (by rw [srcVals_length, srcList_length]) (cons r ρb) ρb]

end Rec

end ConLeche.Semantics
