module

public import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Inductives.StructIntro
public section

/-!
# The projection entry's kit, continued (task #175 W4c, P3 module 7, part 3)

* the grading is a congruence below a variable bound
  (`WellDenotedV_congr_below`, `interp_congr_below`'s twin for the two
  truthfulness halves);
* the field chain's per-field grading at a fitting prefix
  (`fieldsOkB_getD`, `fieldsValid_getD`);
* the entry residual's chain frame: the readings of the opened
  parameters and the earlier projections, and their value chain
  against the subject's projection spine (`chain_entry_agree`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps StructParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Grading below a bound -/

omit [SetTheory V] in
theorem cons_agree_below {k : Nat} {ρ ρ' : Nat → V} (hag : ∀ i, i < k → ρ i = ρ' i)
    (x : V) : ∀ i, i < k + 1 → cons x ρ i = cons x ρ' i := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i => exact hag i (Nat.lt_of_succ_lt_succ hi)

theorem WellDenoted_congr_below :
    ∀ (e : AnnotTerm) (k : Nat) (ρ ρ' : Nat → V),
      Term.bvarsBelow k e.erase → (∀ i, i < k → ρ i = ρ' i) →
      (WellDenoted V ρ e ↔ WellDenoted V ρ' e) := by
  intro e
  induction e with
  | bvar i => intros; simp
  | sort u => intros; simp
  | const c us => intros; simp
  | prf => intros; simp
  | app f a ihf iha =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_app, WellDenoted_app, ihf k ρ ρ' hb.1 hag, iha k ρ ρ' hb.2 hag,
      interp_congr_below V f k ρ ρ' hb.1 hag, interp_congr_below V a k ρ ρ' hb.2 hag]
  | lam v A b ihA ihb =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_lam, WellDenoted_lam, ihA k ρ ρ' hb.1 hag,
      interp_congr_below V A k ρ ρ' hb.1 hag]
    constructor
    · rintro ⟨h1, h2, B, hB, hB0⟩
      refine ⟨h1, fun x hx => (ihb (k + 1) _ _ hb.2 (cons_agree_below hag x)).mp (h2 x hx),
        B, fun x hx => ?_, hB0⟩
      rw [← interp_congr_below V b (k + 1) _ _ hb.2 (cons_agree_below hag x)]
      exact hB x hx
    · rintro ⟨h1, h2, B, hB, hB0⟩
      refine ⟨h1, fun x hx => (ihb (k + 1) _ _ hb.2 (cons_agree_below hag x)).mpr (h2 x hx),
        B, fun x hx => ?_, hB0⟩
      rw [interp_congr_below V b (k + 1) _ _ hb.2 (cons_agree_below hag x)]
      exact hB x hx
  | pi u v A B ihA ihB =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_pi, WellDenoted_pi, ihA k ρ ρ' hb.1 hag,
      interp_congr_below V A k ρ ρ' hb.1 hag]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (ihB (k + 1) _ _ hb.2 (cons_agree_below hag x)).mp (h2 x hx)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (ihB (k + 1) _ _ hb.2 (cons_agree_below hag x)).mpr (h2 x hx)⟩
  | eqE a b iha ihb =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_eqE, WellDenoted_eqE, iha k ρ ρ' hb.1 hag, ihb k ρ ρ' hb.2 hag]
  | fst e ihe =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_fst, WellDenoted_fst, ihe k ρ ρ' hb hag,
      interp_congr_below V e k ρ ρ' hb hag]
  | snd e ihe =>
    intro k ρ ρ' hb hag
    rw [WellDenoted_snd, WellDenoted_snd, ihe k ρ ρ' hb hag,
      interp_congr_below V e k ρ ρ' hb hag]

theorem AnnotValid_congr_below :
    ∀ (e : AnnotTerm) (k : Nat) (ρ ρ' : Nat → V),
      Term.bvarsBelow k e.erase → (∀ i, i < k → ρ i = ρ' i) →
      (AnnotValid V ρ e ↔ AnnotValid V ρ' e) := by
  intro e
  induction e with
  | bvar i => intros; simp [AnnotValid]
  | sort u => intros; simp [AnnotValid]
  | const c us => intros; simp [AnnotValid]
  | prf => intros; simp [AnnotValid]
  | app f a ihf iha =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_app, AnnotValid_app, ihf k ρ ρ' hb.1 hag, iha k ρ ρ' hb.2 hag]
  | lam v A b ihA ihb =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_lam, AnnotValid_lam, ihA k ρ ρ' hb.1 hag,
      interp_congr_below V A k ρ ρ' hb.1 hag]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (ihb (k + 1) _ _ hb.2 (cons_agree_below hag x)).mp (h2 x hx)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (ihb (k + 1) _ _ hb.2 (cons_agree_below hag x)).mpr (h2 x hx)⟩
  | pi u v A B ihA ihB =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_pi, AnnotValid_pi, ihA k ρ ρ' hb.1 hag,
      interp_congr_below V A k ρ ρ' hb.1 hag]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun x hx => (ihB (k + 1) _ _ hb.2 (cons_agree_below hag x)).mp (h2 x hx),
        fun h0 x hx => ?_⟩
      rw [← interp_congr_below V B (k + 1) _ _ hb.2 (cons_agree_below hag x)]
      exact h3 h0 x hx
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun x hx => (ihB (k + 1) _ _ hb.2 (cons_agree_below hag x)).mpr (h2 x hx),
        fun h0 x hx => ?_⟩
      rw [interp_congr_below V B (k + 1) _ _ hb.2 (cons_agree_below hag x)]
      exact h3 h0 x hx
  | eqE a b iha ihb =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_eqE, AnnotValid_eqE, iha k ρ ρ' hb.1 hag, ihb k ρ ρ' hb.2 hag]
  | fst e ihe =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_fst, AnnotValid_fst, ihe k ρ ρ' hb hag]
  | snd e ihe =>
    intro k ρ ρ' hb hag
    rw [AnnotValid_snd, AnnotValid_snd, ihe k ρ ρ' hb hag]

theorem WellDenotedV_congr_below (e : AnnotTerm) (k : Nat) (ρ ρ' : Nat → V)
    (hb : Term.bvarsBelow k e.erase) (hag : ∀ i, i < k → ρ i = ρ' i) :
    WellDenotedV V ρ e ↔ WellDenotedV V ρ' e := by
  unfold WellDenotedV
  rw [WellDenoted_congr_below e k ρ ρ' hb hag, AnnotValid_congr_below e k ρ ρ' hb hag]

/-! ## The field chain, indexed -/

theorem fieldsValid_drop :
    ∀ {Fs₁ : List AnnotTerm} {as : List V} {Fs₂ : List AnnotTerm} {ρ : Nat → V},
      FieldsValid ρ (Fs₁ ++ Fs₂) → SpineFit ρ Fs₁ as →
      FieldsValid (consList as ρ) Fs₂
  | [], [], _, _, h, _ => h
  | [], _ :: _, _, _, _, hsp => hsp.elim
  | _ :: _, [], _, _, _, hsp => hsp.elim
  | F :: Fs₁, a :: as, Fs₂, ρ, h, hsp => by
    rw [consList_cons]
    exact fieldsValid_drop (h.2 a hsp.1) hsp.2

/-- Field `j`'s domain is graded at every fitting prefix. -/
theorem fieldsOkB_getD {w : Nat} {Fs : List AnnotTerm} {ρ : Nat → V}
    (h : FieldsOkB w ρ Fs) {j : Nat} (hj : j < Fs.length) {bs : List V}
    (hsp : SpineFit ρ (Fs.take j) bs) :
    WellDenoted V (consList bs ρ) (Fs.getD j default) := by
  have hsplit : Fs = Fs.take j ++ Fs.drop j := (List.take_append_drop j Fs).symm
  rw [hsplit] at h
  have h2 := FieldsOkB.drop h hsp
  rw [List.drop_eq_getElem_cons hj] at h2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact h2.1

theorem fieldsValid_getD {Fs : List AnnotTerm} {ρ : Nat → V}
    (h : FieldsValid ρ Fs) {j : Nat} (hj : j < Fs.length) {bs : List V}
    (hsp : SpineFit ρ (Fs.take j) bs) :
    AnnotValid V (consList bs ρ) (Fs.getD j default) := by
  have hsplit : Fs = Fs.take j ++ Fs.drop j := (List.take_append_drop j Fs).symm
  rw [hsplit] at h
  have h2 := fieldsValid_drop h hsp
  rw [List.drop_eq_getElem_cons hj] at h2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact h2.1

/-! ## The residual's chain frame -/

/-- The readings of the opened parameters at the entry's full depth. -/
@[expose] def entryParamBvars (nP : Nat) : List AnnotTerm :=
  (List.range nP).map fun k => AnnotTerm.bvar (nP - k)

/-- The readings of the earlier projections of the subject, at the
table's projection offset `off` (task #210 Part A: `projS (j + off)`
is field `j` of a carrier whose tuple tower sits below `off` leading
pair components). -/
@[expose] def entryProjAVs (off i : Nat) : List AnnotTerm :=
  (List.range i).map fun j => projAV (j + off) (.bvar 0)

omit [SetTheory V] in
theorem entryParamBvars_length (nP : Nat) : (entryParamBvars nP).length = nP := by
  simp [entryParamBvars]

omit [SetTheory V] in
theorem entryProjAVs_length (off i : Nat) : (entryProjAVs off i).length = i := by
  simp [entryProjAVs]

/-- The opened parameters read to `entryParamBvars` at depth `nP + 1`. -/
theorem denoteMetaSpine_entryParams {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {nP : Nat} {fvsP : List Expr}
    (hidx : ∀ (k : Nat) (x : Expr), fvsP[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hlen : fvsP.length = nP) :
    DenoteMetaSpine acval env φ (nP + 1) fvsP (entryParamBvars nP) := by
  have h := denoteMetaSpine_fvars (acval := acval) (env := env) (φ := φ) (nP + 1) fvsP 0
    (fun k x hx => by obtain ⟨ty, rfl⟩ := hidx k x hx; exact ⟨ty, by rw [Nat.zero_add]⟩)
  rw [hlen] at h
  have e : ((List.range nP).map fun k => AnnotTerm.bvar (nP + 1 - 1 - (0 + k)))
      = entryParamBvars nP := by
    unfold entryParamBvars
    apply List.map_congr_left
    intro k _
    congr 1
    omega
  rw [e] at h
  exact h

/-- The earlier projections of the subject read to `entryProjAVs` at
depth `nP + 1`, through the stored tower entries. -/
theorem denoteMetaSpine_entryProjs {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {nP off : Nat} {T : Name} {sdom : Expr}
    (hprev : ∀ j, j < i → ∃ entry, env.findProj? T j = some entry ∧ entry.off = off) :
    DenoteMetaSpine acval env φ (nP + 1)
      ((List.range i).map fun j => Expr.proj T j (.fvar nP sdom)) (entryProjAVs off i) := by
  unfold entryProjAVs
  suffices ∀ (l : List Nat), (∀ j ∈ l, j < i) →
      DenoteMetaSpine acval env φ (nP + 1)
        (l.map fun j => Expr.proj T j (.fvar nP sdom))
        (l.map fun j => projAV (j + off) (.bvar 0)) from
    this (List.range i) (fun j hj => List.mem_range.mp hj)
  intro l
  induction l with
  | nil => intro _; exact .nil
  | cons j l ih =>
    intro hl
    obtain ⟨entry, hfe, hoff⟩ := hprev j (hl j List.mem_cons_self)
    simp only [List.map_cons]
    refine .cons ?_ (ih fun j' hj' => hl j' (List.mem_cons_of_mem _ hj'))
    rw [denoteMeta_proj_tower hfe (denoteMeta_fvar acval (nP + 1) nP sdom),
      show nP + 1 - 1 - nP = 0 from by omega, hoff]

/-- **The chain frame agrees with the projection spine's frame** below
the field's depth: the parameter readings pick the frame's parameter
values, the projection readings the subject's projections. -/
theorem chain_entry_agree (nP off i : Nat) (ρ : Nat → V) :
    ∀ n, n < nP + i →
      chain V ρ (entryParamBvars nP ++ entryProjAVs off i) n
        = consList (projList i (dropS off (ρ 0))) (fun j => ρ (j + 1)) n := by
  intro n hn
  have hlen : (entryParamBvars nP ++ entryProjAVs off i).length = nP + i := by
    simp [entryParamBvars_length, entryProjAVs_length]
  rw [chain_lt (by rw [hlen]; exact hn), hlen]
  rcases Nat.lt_or_ge n i with hni | hni
  · -- a projection slot
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right
      (by rw [entryParamBvars_length]; omega), entryParamBvars_length]
    unfold entryProjAVs
    rw [List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some, projAV_interp, interp_bvar]
    rw [consList_apply_lt _ _ _ (by rw [projList_length]; exact hni), projList_length,
      projList_eq_map_range, List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some]
    rw [projS_add_dropS, show nP + i - 1 - n - nP = i - 1 - n from by omega]
  · -- a parameter slot
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left
      (by rw [entryParamBvars_length]; omega)]
    unfold entryParamBvars
    rw [List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some, interp_bvar]
    have := consList_apply_add (projList i (dropS off (ρ 0))) (fun j => ρ (j + 1)) (n - i)
    rw [projList_length, show n - i + i = n from by omega] at this
    rw [this]
    congr 1
    omega

end ConLeche.Model
