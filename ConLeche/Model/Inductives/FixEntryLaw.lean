module

import ConLeche.Model.Inductives.StructBodyFrames
public import ConLeche.Model.Inductives.FixRealChains
public section

/-!
# The projection entry's law on the fixpoint route's carrier (task #210 Part A)

The three clauses of `TowerEntryLaw` at a STRUCTURE-LIKE block on the
fixpoint route — one constructor, no index — whose carrier is the
TAGGED tower: the family's fibre at the (empty) index tuple is the sum
route's restricted tagged union over the one constructor,
`sumSet w (sumFibre w ρ [Fs ++ [idxEqAV []]])` (`fixFamI_app_eq_sum`),
whose elements are `inj 0 (mkTower (fs ++ [pt]))` with `fs` fitting the
fields.  So field `i` is `projS (i + 1)` of a member (the tag in front,
`ProjTable.off = 1`), the tuple below the tag is `dropS 1`, and the
laws are the direct structure's (`StructEntryLawP`) with one pair
component to cross:

* **(A) the typing law** (`fixEntryTypingCore`): a member projects at
  `i + 1` into the body's residual — the graph regime by the tower's
  projection membership below the tag, the squash regime by the point;
* **(B) the iota law** (`fixEntryIotaCore`/`fixEntryIotaCoreZero`): the
  projection of a graded constructor application is the selected field
  (`sumMkAV_fold`: the application folds to the tagged tuple);
* **(C) the η law** (`fixEntryEtaCore`): a member is the constructor at
  the parameters and its own projections below the tag.

`fixFibre_elim`/`fixFibre_zero_elim` are the one-constructor fibre's
eliminations, `wellDenoted_proj1_sum`/`wellDenoted_proj1_pt` grade the tag
projection.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps BinderMeta ProjEntry)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The one-constructor fibre -/

/-- The elements of the one-constructor fibre in the graph regime:
tagged point-terminated tuples fitting the fields, the tuple a member
of the restricted tower. -/
theorem fixFibre_elim {w : Nat} (hw : w ≠ 0) {ρ' : Nat → V} {Fs : List AnnotTerm} {x : V}
    (hx : x ∈ˢ sumSet w (sumFibre w ρ' [Fs ++ [idxEqAV []]])) :
    ∃ fs : List V, x = inj 0 (mkTower (fs ++ [pt])) ∧ SpineFit ρ' Fs fs ∧
      mkTower (fs ++ [pt]) ∈ˢ towerSet w (teleOfFields ρ' (Fs ++ [idxEqAV []])) := by
  obtain ⟨j, a, ha, rfl⟩ := sumSet_elim hw hx
  cases j with
  | zero =>
    rw [sumFibre_of_getElem? rfl] at ha
    obtain ⟨hfit, heta⟩ := towerSet_elim_teleOfFields hw ha
    obtain ⟨fs, hfs, hsp, -⟩ := spineFit_append_idxEq.mp hfit
    refine ⟨fs, ?_, hsp, ?_⟩
    · rw [heta, hfs]
    · rw [← hfs, ← heta]; exact ha
  | succ j =>
    rw [sumFibre_of_ge (by simp)] at ha
    exact absurd ha (not_mem_empty _)

/-- The one-constructor fibre in the squash regime: the point, with a
fitting field spine. -/
theorem fixFibre_zero_elim {ρ' : Nat → V} {Fs : List AnnotTerm} {x : V}
    (hx : x ∈ˢ sumSet 0 (sumFibre 0 ρ' [Fs ++ [idxEqAV []]])) :
    x = pt ∧ ∃ fs : List V, SpineFit ρ' Fs fs := by
  obtain ⟨rfl, j, a, ha⟩ := sumSet_zero_elim hx
  refine ⟨rfl, ?_⟩
  cases j with
  | zero =>
    rw [sumFibre_of_getElem? rfl] at ha
    obtain ⟨-, as, hfits⟩ := towerSet_zero_elim _ ha
    obtain ⟨fs, -, hsp, -⟩ := spineFit_append_idxEq.mp (fitsS_teleOfFields.mp hfits)
    exact ⟨fs, hsp⟩
  | succ j =>
    rw [sumFibre_of_ge (by simp)] at ha
    exact absurd ha (not_mem_empty _)

/-- The tuple below the tag. -/
theorem dropS_one_inj (j : Nat) (a : V) : dropS 1 (inj j a) = a := by
  show ssnd (spair (vnat j) a) = a
  exact ssnd_spair _ _

/-- A projection past the tag is the tuple's. -/
theorem projS_succ_inj (i j : Nat) (a : V) : projS (i + 1) (inj j a) = projS i a := by
  rw [projS_add_dropS, dropS_one_inj]

/-- The restricted chain of the one constructor at no index is the
unrestricted one. -/
theorem fieldsBound_append_idxEq {w : Nat} {ρ' : Nat → V} {Fs : List AnnotTerm} (hw : w ≠ 0)
    (hok : FieldsOkB w ρ' Fs) : FieldsBound w ρ' (Fs ++ [idxEqAV []]) :=
  (FieldsOkB_append_idxEq hok fun _ _ _ he => absurd he List.not_mem_nil).toBound hw

/-! ## The tag projection's grading -/

/-- `.snd` of a member of the tagged union is graded: the union is a
Σ over the numerals whose fibres are bounded towers. -/
theorem wellDenoted_proj1_sum {w : Nat} (hw : w ≠ 0) {ρ' ρ : Nat → V} {Fs : List AnnotTerm}
    {e : AnnotTerm} (hb : FieldsBound w ρ' (Fs ++ [idxEqAV []]))
    (hok : WellDenoted V ρ e)
    (hval : interp V ρ e ∈ˢ sumSet w (sumFibre w ρ' [Fs ++ [idxEqAV []]])) :
    WellDenoted V ρ (.snd e) := by
  rw [WellDenoted_snd]
  refine ⟨hok, w, w, omega, natFibre (sumFibre w ρ' [Fs ++ [idxEqAV []]]), ?_, ?_, ?_⟩
  · rw [nat_max_self]; exact hval
  · obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    exact omega_mem_univ_succ w'
  · intro k hk
    obtain ⟨j, rfl, hfib⟩ := natFibre_of_mem _ hk
    rw [hfib]
    cases j with
    | zero =>
      rw [sumFibre_of_getElem? rfl]
      exact towerSet_mem_univ _ (boundS_teleOfFields.mpr hb)
    | succ j =>
      rw [sumFibre_of_ge (by simp)]
      exact empty_mem_univ w

/-- `.snd` of the point is graded (the squash regime). -/
theorem wellDenoted_proj1_pt {ρ : Nat → V} {e : AnnotTerm} (hok : WellDenoted V ρ e)
    (hpt : interp V ρ e = (pt : V)) : WellDenoted V ρ (.snd e) := by
  rw [WellDenoted_snd]
  refine ⟨hok, 0, 0, unitSet, fun _ => unitSet, ?_, unitSet_mem_univ 0,
    fun _ _ => unitSet_mem_univ 0⟩
  rw [hpt, nat_max_self]
  exact pt_mem_sigma pt_mem_unitSet pt_mem_unitSet

/-- The projection reading past the tag, graded at a member of the
one-constructor fibre (both regimes). -/
theorem wellDenoted_projAV_succ_fibre {w i : Nat} {ρ' ρ : Nat → V} {Fs : List AnnotTerm}
    {e : AnnotTerm} (hokB : w ≠ 0 → FieldsOkB w ρ' Fs)
    (hok : WellDenoted V ρ e)
    (hval : interp V ρ e ∈ˢ sumSet w (sumFibre w ρ' [Fs ++ [idxEqAV []]]))
    (hi : i < Fs.length) : WellDenoted V ρ (projAV (i + 1) e) := by
  show WellDenoted V ρ (projAV i (.snd e))
  by_cases hw : w = 0
  · subst hw
    obtain ⟨hpt, -⟩ := fixFibre_zero_elim hval
    refine wellDenoted_projAV_pt (wellDenoted_proj1_pt hok hpt) ?_
    rw [interp_snd, hpt, ssnd_pt]
  · obtain ⟨fs, heq, -, hmem⟩ := fixFibre_elim hw hval
    have hb := fieldsBound_append_idxEq hw (hokB hw)
    refine wellDenoted_projAV_tower hb hmem (wellDenoted_proj1_sum hw hb hok hval) ?_
      (by rw [List.length_append, List.length_singleton]; omega)
    rw [interp_snd, heq]
    exact ssnd_spair _ _

/-! ## (A) the typing law -/

theorem fixEntryTypingCore {u w nP nF i : Nat} {pps ds eds : List (Nat × Nat × AnnotTerm)}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {eiss : List (List (List AnnotTerm))} {Fss₀ Ess : List (List AnnotTerm)}
    {R : AnnotTerm} {sorts : List Level} {ψ : Name → Nat}
    (hlenDs : ds.length = nP + nF) (hlenPps : pps.length = nP) (hlenEds : eds.length = nP + 1)
    (hiff : ∀ ρ : Nat → V, Sat V (pps.map (·.2.2)).reverse ρ ↔
      Sat V ((ds.take nP).map (·.2.2)).reverse ρ)
    (hokB : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      FieldsOkB w ρ ((ds.drop nP).map (·.2.2)))
    (hsorts : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      ∀ j, j < nF → ∀ as : List V,
        SpineFit ρ (((ds.drop nP).map (·.2.2)).take j) as →
        interp V (consList as ρ) (((ds.drop nP).map (·.2.2)).getD j default)
          ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    {used : Nat → Bool}
    (hguard : w = 0 → (sorts.getD i .zero).eval ψ = 0 ∧
      ∀ j, j < i → used j = true → (sorts.getD j .zero).eval ψ = 0)
    (hfree : ∀ j, j < i → used j = false →
      ∃ X : AnnotTerm, ((ds.drop nP).map (·.2.2)).getD i default = X.liftN 1 (i - 1 - j))
    (hi : i < nF)
    -- the family at the parameters is the one-constructor fibre
    (hfold : ∀ (ρ : Nat → V) (ts : List V), SpineFit ρ (pps.map (·.2.2)) ts →
      ts.foldl SetTheory.app (interp V ρ (nativeTyAVI u w pps [] rss tlss eiss Fss₀ Ess))
        = sumSet w (sumFibre w (consList ts ρ) [((ds.drop nP).map (·.2.2)) ++ [idxEqAV []]]))
    (hres : ∀ ρ : Nat → V,
      ρ 0 ∈ˢ sumSet w (sumFibre w (fun j => ρ (j + 1)) [((ds.drop nP).map (·.2.2)) ++ [idxEqAV []]]) →
      Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) →
      interp V ρ R
        = interp V (consList (projList i (dropS 1 (ρ 0))) (fun j => ρ (j + 1)))
            (((ds.drop nP).map (·.2.2)).getD i default))
    (hokR : ∀ ρ : Nat → V,
      ρ 0 ∈ˢ sumSet w (sumFibre w (fun j => ρ (j + 1)) [((ds.drop nP).map (·.2.2)) ++ [idxEqAV []]]) →
      Sat V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) →
      WellDenotedV V ρ R) :
    ∀ (ρ : Nat → V) (vs : List AnnotTerm) (x rest : AnnotTerm),
      vs.length = nP →
      WellDenotedV V ρ (AnnotTerm.mkAppN (nativeTyAVI u w pps [] rss tlss eiss Fss₀ Ess) vs) →
      WellDenotedV V ρ x →
      interp V ρ x ∈ˢ interp V ρ
        (AnnotTerm.mkAppN (nativeTyAVI u w pps [] rss tlss eiss Fss₀ Ess) vs) →
      ConLeche.Model.AnnotTerm.peelPis (mkPisAV eds R) (vs ++ [x]) = some rest →
      WellDenotedV V ρ (projAV (i + 1) x) ∧ WellDenotedV V ρ rest ∧
        interp V ρ (projAV (i + 1) x) ∈ˢ interp V ρ rest := by
  intro ρ vs x rest hlenVs hokApp hokx hmem hpeel
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  -- the parameter fit
  have hsp : SpineFit ρ (pps.map (·.2.2)) (vs.map (interp V ρ)) := by
    have h := spineFit_of_wellDenotedV_mkAppN_lam (lds := pps.map fun d => (w + 1, d.2.2))
      (b := .app ((fixBodyAVI u w [] 0 rss tlss eiss Fss₀ Ess).liftN 0 0) (mkTowerGo u []))
      (σ := ρ)
      (fun d hd => by obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd; exact Nat.succ_ne_zero w)
      hokApp rfl (by simp [hlenVs, hlenPps])
    simpa [List.map_map, Function.comp_def] using h
  have hlenAs : (vs.map (interp V ρ)).length = nP := by simp [hlenVs]
  -- the member of the fibre
  have hx : interp V ρ x ∈ˢ sumSet w
      (sumFibre w (consList (vs.map (interp V ρ)) ρ) [((ds.drop nP).map (·.2.2)) ++ [idxEqAV []]]) := by
    rw [interp_mkAppN_foldl, hfold ρ _ hsp] at hmem
    exact hmem
  -- the constructor's parameter frame
  have hspC : SpineFit ρ ((ds.take nP).map (·.2.2)) (vs.map (interp V ρ)) :=
    (spineFit_iff_of_sat_iff (by simp [hlenPps, hlenDs]) hiff ρ _ (by simp [hlenVs, hlenPps])).mp hsp
  have hsatC : Sat V ((ds.take nP).map (·.2.2)).reverse (consList (vs.map (interp V ρ)) ρ) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hspC
    rwa [List.append_nil] at this
  -- the frame at the subject's chain
  have hchain : chain V ρ (vs ++ [x]) = cons (interp V ρ x) (consList (vs.map (interp V ρ)) ρ) := by
    unfold chain
    rw [consN_eq_consList, List.map_append, consList_append]
    rfl
  have hframeX : (cons (interp V ρ x) (consList (vs.map (interp V ρ)) ρ)) 0 ∈ˢ sumSet w
      (sumFibre w (fun j => (cons (interp V ρ x) (consList (vs.map (interp V ρ)) ρ)) (j + 1))
        [((ds.drop nP).map (·.2.2)) ++ [idxEqAV []]]) := hx
  have hframeS : Sat V ((ds.take nP).map (·.2.2)).reverse
      (fun j => (cons (interp V ρ x) (consList (vs.map (interp V ρ)) ρ)) (j + 1)) := hsatC
  -- the residual
  have hrest : rest = ConLeche.Model.AnnotTerm.instSeq (vs ++ [x]) nP R := by
    have h := peelPis_of_piTeleAV (nP + 1) (by rw [← hlenEds]; exact piTeleAV_mkPisAV eds R)
      (ws := vs ++ [x]) (by simp [hlenVs])
    rw [hpeel] at h
    have := Option.some.inj h
    rwa [Nat.add_sub_cancel] at this
  have hlen' : ConLeche.Model.AnnotTerm.instSeq (vs ++ [x]) nP R
      = ConLeche.Model.AnnotTerm.instSeq (vs ++ [x]) ((vs ++ [x]).length - 1) R := by
    simp [hlenVs]
  have hinterpRest : interp V ρ rest
      = interp V (consList (projList i (dropS 1 (interp V ρ x))) (consList (vs.map (interp V ρ)) ρ))
          (((ds.drop nP).map (·.2.2)).getD i default) := by
    rw [hrest, hlen', interp_instSeq, hchain, hres _ hframeX hframeS]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · -- the projection's grading
    exact ⟨wellDenoted_projAV_succ_fibre (fun hw => hokB _ hsatC) hokx.1 hx (by rw [hlenFs]; exact hi),
      projAV_validV hokx.2⟩
  · -- the residual's grading
    rw [hrest, hlen']
    refine wellDenotedV_instSeq _ ?_ ?_
    · intro w' hw'
      rcases List.mem_append.mp hw' with h | h
      · exact WellDenotedV_mkAppN_args vs hokApp w' h
      · rw [List.mem_singleton] at h; subst h; exact hokx
    · rw [hchain]; exact hokR _ hframeX hframeS
  · -- the membership
    rw [hinterpRest, projAV_interp]
    by_cases hw : w = 0
    · -- squash: the point in the proof field at the point prefix,
      -- which agrees with a fitting prefix at every used slot
      subst hw
      obtain ⟨hpt, as', hspAs⟩ := fixFibre_zero_elim hx
      obtain ⟨hpre, hnext⟩ := spineFit_prefix_next hspAs (by rw [hlenFs]; exact hi)
      have hz := hsorts _ hsatC i hi _ hpre
      rw [(hguard rfl).1] at hz
      have hval := mem_univ_zero hz hnext
      rw [hval] at hnext
      rw [hpt, projS_pt, dropS_pt, projList_pt]
      have hlenTake : (as'.take i).length = i := spineFit_take_length hspAs (by rw [hlenFs]; omega)
      rw [interp_congr_lifts i
        (free_of_diff hlenDs hi (hsorts _ hsatC) (hguard rfl).2 hfree hspAs)
        (consList_prefix_agree hlenTake _).2]
      exact hnext
    · -- graph: the tower's projection membership below the tag
      obtain ⟨fs, heq, -, hmem'⟩ := fixFibre_elim hw hx
      rw [heq, projS_succ_inj, dropS_one_inj]
      have h := projS_mem_teleOfFields (fun h0 => absurd h0 hw) hmem' (i := i)
        (by rw [List.length_append, List.length_singleton, hlenFs]; omega)
      rw [List.getElem_append_left (by rw [hlenFs]; exact hi)] at h
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenFs]; exact hi)]
      exact h

/-! ## (B) the iota law -/

theorem fixEntryIotaCore {w nP nF i : Nat} {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}
    (hw : w ≠ 0) (hlenDs : ds.length = nP + nF) (hi : i < nF)
    (hokB : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      FieldsOkB w ρ ((ds.drop nP).map (·.2.2)))
    (ys : List AnnotTerm) (hlen : ys.length = nP + nF)
    (hok : WellDenotedV V ρ (AnnotTerm.mkAppN
      (sumMkAV w 0 ds ((ds.drop nP).map (·.2.2)) (uChains [(ds.drop nP).map (·.2.2)])) ys)) :
    interp V ρ (projAV (i + 1) (AnnotTerm.mkAppN
        (sumMkAV w 0 ds ((ds.drop nP).map (·.2.2)) (uChains [(ds.drop nP).map (·.2.2)])) ys))
      = interp V ρ (ys.getD (nP + i) default) := by
  have hsp : SpineFit ρ (ds.map (·.2.2)) (ys.map (interp V ρ)) := by
    have h := spineFit_of_wellDenotedV_mkAppN_lam (lds := ds.map fun d => (w, d.2.2))
      (b := sumInjAtAV w (uChains [(ds.drop nP).map (·.2.2)]) ((ds.drop nP).map (·.2.2)).length
        (numeralAV 0) (mkTowerGoU w ((ds.drop nP).map (·.2.2)) (idxEqAV [])))
      (σ := ρ)
      (fun d hd => by obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd; exact hw)
      hok rfl (by simp [hlen, hlenDs])
    simpa [List.map_map, Function.comp_def] using h
  rw [show ds.map (·.2.2) = (ds.take nP).map (·.2.2) ++ (ds.drop nP).map (·.2.2) from by
    rw [← List.map_append, List.take_append_drop]] at hsp
  obtain ⟨as, bs, heq, hsp₁, hsp₂⟩ := spineFit_append_inv hsp
  have hlenAs : as.length = nP := by rw [hsp₁.length_eq]; simp [hlenDs]
  have hlenBs : bs.length = nF := by rw [hsp₂.length_eq]; simp [hlenDs]
  have hsat : Sat V ((ds.take nP).map (·.2.2)).reverse (consList as ρ) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
    rwa [List.append_nil] at this
  have hokU : SumFieldsOkB w (consList as ρ) (uChains [(ds.drop nP).map (·.2.2)]) := by
    intro Fs' hFs'
    simp only [uChains, List.map_cons, List.map_nil, List.mem_singleton] at hFs'
    subst hFs'
    exact FieldsOkB_append_idxEq (hokB _ hsat) fun _ _ e he => absurd he List.not_mem_nil
  have hfold := sumMkAV_fold (pds := ds.take nP) (fds := ds.drop nP) (j := 0) hw hsp₁ hsp₂
    hokU rfl
  rw [List.take_append_drop] at hfold
  rw [projAV_interp, interp_mkAppN_foldl, heq, hfold, projS_succ_inj,
    projS_mkTower_getD (by rw [hlenBs]; exact hi)]
  -- the selected argument
  have hlt : nP + i < ys.length := by omega
  rw [List.getD_eq_getElem?_getD (l := ys), List.getElem?_eq_getElem hlt, Option.getD_some]
  have h1 : (ys.map (interp V ρ))[nP + i]? = some (interp V ρ ys[nP + i]) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl
  rw [heq, List.getElem?_append_right (by omega), hlenAs, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem (by rw [hlenBs]; exact hi)] at h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenBs]; exact hi), Option.getD_some]
  exact Option.some.inj h1

/-- The iota law at a squash instantiation: the constructor application
is the point, so is its projection, and the selected field is a
proposition's member. -/
theorem fixEntryIotaCoreZero {nP nF i : Nat} {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}
    {sorts : List Level} {ψ : Name → Nat}
    (hlenDs : ds.length = nP + nF) (hi : i < nF)
    (hsorts : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      ∀ j, j < nF → ∀ as : List V,
        SpineFit ρ (((ds.drop nP).map (·.2.2)).take j) as →
        interp V (consList as ρ) (((ds.drop nP).map (·.2.2)).getD j default)
          ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    (hz : (sorts.getD i .zero).eval ψ = 0)
    (ys : List AnnotTerm) (hlen : ys.length = nP + nF)
    (hsp : SpineFit ρ (ds.map (·.2.2)) (ys.map (interp V ρ))) :
    interp V ρ (projAV (i + 1) (AnnotTerm.mkAppN
        (sumMkAV 0 0 ds ((ds.drop nP).map (·.2.2)) (uChains [(ds.drop nP).map (·.2.2)])) ys))
      = interp V ρ (ys.getD (nP + i) default) := by
  rw [projAV_interp, interp_mkAppN_foldl, sumMkAV_zero, foldl_app_pt, projS_pt]
  rw [show ds.map (·.2.2) = (ds.take nP).map (·.2.2) ++ (ds.drop nP).map (·.2.2) from by
    rw [← List.map_append, List.take_append_drop]] at hsp
  obtain ⟨as, bs, heq, hsp₁, hsp₂⟩ := spineFit_append_inv hsp
  have hlenAs : as.length = nP := by rw [hsp₁.length_eq]; simp [hlenDs]
  have hlenBs : bs.length = nF := by rw [hsp₂.length_eq]; simp [hlenDs]
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hsat : Sat V ((ds.take nP).map (·.2.2)).reverse (consList as ρ) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
    rwa [List.append_nil] at this
  obtain ⟨hpre, hnext⟩ := spineFit_prefix_next hsp₂ (by rw [hlenFs]; exact hi)
  have hz' := hsorts _ hsat i hi _ hpre
  rw [hz] at hz'
  have hval : bs.getD i pt = pt := mem_univ_zero hz' hnext
  have hlt : nP + i < ys.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  have h1 : (ys.map (interp V ρ))[nP + i]? = some (interp V ρ ys[nP + i]) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl
  rw [heq, List.getElem?_append_right (by omega), hlenAs, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem (by rw [hlenBs]; exact hi)] at h1
  have h2 : bs[i] = bs.getD i pt := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenBs]; exact hi)]
    rfl
  rw [← Option.some.inj h1, h2, hval]

/-! ## (C) the η law -/

theorem fixEntryEtaCore {u w nP nF : Nat} {pps ds : List (Nat × Nat × AnnotTerm)}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {eiss : List (List (List AnnotTerm))} {Fss₀ Ess : List (List AnnotTerm)} {ρ : Nat → V}
    (hlenDs : ds.length = nP + nF) (hlenPps : pps.length = nP)
    (hiff : ∀ ρ : Nat → V, Sat V (pps.map (·.2.2)).reverse ρ ↔
      Sat V ((ds.take nP).map (·.2.2)).reverse ρ)
    (hokB : ∀ ρ : Nat → V, Sat V ((ds.take nP).map (·.2.2)).reverse ρ →
      FieldsOkB w ρ ((ds.drop nP).map (·.2.2)))
    (hfold : ∀ (ρ : Nat → V) (ts : List V), SpineFit ρ (pps.map (·.2.2)) ts →
      ts.foldl SetTheory.app (interp V ρ (nativeTyAVI u w pps [] rss tlss eiss Fss₀ Ess))
        = sumSet w (sumFibre w (consList ts ρ) [((ds.drop nP).map (·.2.2)) ++ [idxEqAV []]]))
    (ts : List V) (x : V) (hlen : ts.length = nP)
    (hsp : SpineFit ρ (pps.map (·.2.2)) ts)
    (hx : x ∈ˢ ts.foldl SetTheory.app
      (interp V ρ (nativeTyAVI u w pps [] rss tlss eiss Fss₀ Ess))) :
    x = (ts ++ (List.range nF).map fun j => projS (j + 1) x).foldl SetTheory.app
      (interp V ρ (sumMkAV w 0 ds ((ds.drop nP).map (·.2.2))
        (uChains [(ds.drop nP).map (·.2.2)]))) := by
  rw [hfold ρ ts hsp] at hx
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  by_cases hw : w = 0
  · subst hw
    obtain ⟨hpt, -⟩ := fixFibre_zero_elim hx
    rw [hpt, sumMkAV_zero, foldl_app_pt]
  · obtain ⟨fs, heq, hspF, -⟩ := fixFibre_elim hw hx
    have hlenF : fs.length = nF := by rw [hspF.length_eq, hlenFs]
    have hsp₁ : SpineFit ρ ((ds.take nP).map (·.2.2)) ts :=
      (spineFit_iff_of_sat_iff (by simp [hlenPps, hlenDs]) hiff ρ ts (by simp [hlen, hlenPps])).mp hsp
    have hsat : Sat V ((ds.take nP).map (·.2.2)).reverse (consList ts ρ) := by
      have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
      rwa [List.append_nil] at this
    have hokU : SumFieldsOkB w (consList ts ρ) (uChains [(ds.drop nP).map (·.2.2)]) := by
      intro Fs' hFs'
      simp only [uChains, List.map_cons, List.map_nil, List.mem_singleton] at hFs'
      subst hFs'
      exact FieldsOkB_append_idxEq (hokB _ hsat) fun _ _ e he => absurd he List.not_mem_nil
    have hfold' := sumMkAV_fold (pds := ds.take nP) (fds := ds.drop nP) (j := 0) hw hsp₁ hspF
      hokU rfl
    rw [List.take_append_drop] at hfold'
    -- the projections past the tag are the tuple's fields
    have hprojs : ((List.range nF).map fun j => projS (j + 1) x) = fs := by
      rw [heq]
      have h1 : ((List.range nF).map fun j => projS (j + 1) (inj 0 (mkTower (fs ++ [pt]))))
          = (List.range nF).map fun j => projS j (mkTower (fs ++ [pt])) :=
        List.map_congr_left fun j _ => projS_succ_inj j 0 _
      rw [h1, ← projList_eq_map_range, ← hlenF, projList_mkTower_take (Nat.le_refl _),
        List.take_length]
    rw [hprojs, hfold', heq]

end ConLeche.Model
