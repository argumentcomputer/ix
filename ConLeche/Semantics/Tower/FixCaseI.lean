module

import ConLeche.Semantics.Tower.SumRecCase
public import ConLeche.Semantics.Tower.FixFamI

@[expose] public section

/-!
# The recursive recursor's case split, spelled (task #188, indexed)

The one-step unfolding of a recursive family's recursor is the sum
route's case split (`ConLeche/Semantics/Tower/SumRecCase.lean`) with the
**inductive hypotheses** supplied: constructor `j`'s branch is

    λ (y : T_j), m_j (y.0) … (y.(nF-1)) ih₁ … ih_m

where the ih arguments are ABSTRACT here: a function `ihArgs D j` of the
depth `D` (below the K-frame) and the constructor, spelled at the
payload frame (`y = bvar 0` at depth `D + 1`).  The recursor module
(`FixRecI.lean`) supplies them — the function being unfolded applied
to the parameters, the motive, the minors, the recursive field's index
expressions (read at the payload's projections, by substitution) and
the field — and discharges the one hypothesis the case split asks of
them (`IhArgsOk`): at every payload of the fibre they are graded and
their values lie in the ih domains (`ihDoms j f⃗`, a function of the
payload's fields).  The minors' spaces are the sum route's `minorSpI`
with the conclusion replaced by the **ih tower** `ihSpL` over those
domains (`RecHypI.hms`).  The stage motives, the `Nat.rec` tower and the
frame arithmetic are the sum route's verbatim (`caseMotiveAV`,
`motive_facts`); only the branch changes (`caseBaseAVI`, `base_factsI`)
and the facts are re-run (`caseRec_factsI`).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The ih tower -/

/-- The ih tower: the non-dependent Π-tower over a list of domains,
ending in `C`. -/
noncomputable def ihSpL (ℓ : Nat) (C : V) : List V → V
  | [] => C
  | A :: As => piR ℓ A fun _ => ihSpL ℓ C As

theorem ihSpL_zero_univZero {ℓ : Nat} {C : V} (h0 : ℓ = 0) (hC : C ∈ˢ (univZero : V)) :
    ∀ As, ihSpL ℓ C As ∈ˢ (univZero : V)
  | [] => hC
  | _ :: _ => by
    show piR ℓ _ _ ∈ˢ _
    rw [h0]
    exact piR_zero_mem_univZero

/-- The graded fold of an ih-tower member along graded ih arguments. -/
theorem ihSpL_spine {ℓ : Nat} {C : V} (hC0 : ℓ = 0 → C ∈ˢ (univZero : V)) :
    ∀ {As : List V} {args : List AnnotTerm} {f : AnnotTerm} {σ : Nat → V},
      WellDenoted V σ f → interp V σ f ∈ˢ ihSpL ℓ C As →
      args.length = As.length →
      (∀ l, l < As.length → WellDenoted V σ (args.getD l default) ∧
        interp V σ (args.getD l default) ∈ˢ As.getD l pt) →
      (ℓ = 0 → ∀ A ∈ As, A ∈ˢ (univZero : V)) →
      WellDenoted V σ (AnnotTerm.mkAppN f args) ∧ interp V σ (AnnotTerm.mkAppN f args) ∈ˢ C
  | [], [], _, _, hokf, hmf, _, _, _ => ⟨hokf, hmf⟩
  | [], _ :: _, _, _, _, _, hlen, _, _ => nomatch hlen
  | _ :: _, [], _, _, _, _, hlen, _, _ => nomatch hlen
  | A :: As, a :: args, f, σ, hokf, hmf, hlen, hargs, hz => by
    have hB0 : ℓ = 0 → ∀ x, x ∈ˢ A → ihSpL ℓ C As ∈ˢ (univZero : V) :=
      fun h0 _ _ => ihSpL_zero_univZero h0 (hC0 h0) As
    have h0 := hargs 0 (by simp)
    simp only [List.getD_cons_zero] at h0
    have happ : SetTheory.app (interp V σ f) (interp V σ a) ∈ˢ ihSpL ℓ C As :=
      app_mem_piR hmf h0.2 hB0
    have hoka : WellDenoted V σ (.app f a) := by
      rw [WellDenoted_app]
      exact ⟨hokf, h0.1, ℓ, _, _, hmf, h0.2, hB0⟩
    rw [AnnotTerm.mkAppN_cons]
    refine ihSpL_spine hC0 (As := As) (args := args) hoka happ (by simpa using hlen) ?_
      (fun h0 A hA => hz h0 A (List.mem_cons_of_mem _ hA))
    intro l hl
    have := hargs (l + 1) (by simpa using hl)
    simpa only [List.getD_cons_succ] using this

/-- The semantic fold of an ih-tower member along ih values. -/
theorem ihSpL_fold {ℓ : Nat} {C : V} (hC0 : ℓ = 0 → C ∈ˢ (univZero : V)) :
    ∀ {As vs : List V} {x : V}, x ∈ˢ ihSpL ℓ C As → vs.length = As.length →
      (∀ l, l < As.length → vs.getD l pt ∈ˢ As.getD l pt) →
      vs.foldl SetTheory.app x ∈ˢ C
  | [], [], x, hx, _, _ => hx
  | [], _ :: _, _, _, hlen, _ => nomatch hlen
  | _ :: _, [], _, _, hlen, _ => nomatch hlen
  | A :: As, v :: vs, x, hx, hlen, hg => by
    rw [List.foldl_cons]
    refine ihSpL_fold hC0 (As := As) (vs := vs) ?_ (by simpa using hlen) ?_
    · have h0 := hg 0 (by simp)
      simp only [List.getD_cons_zero] at h0
      exact app_mem_piR hx h0 (fun h0 _ _ => ihSpL_zero_univZero h0 (hC0 h0) As)
    · intro l hl
      have := hg (l + 1) (by simpa using hl)
      simpa only [List.getD_cons_succ] using this

/-- At a zero elimination level an ih tower is inhabited exactly when
its conclusion is, given the domains inhabited. -/
theorem ihSpL_zero_inhab {C : V} :
    ∀ {As : List V} {x : V}, x ∈ˢ ihSpL 0 C As →
      (∀ A ∈ As, ∃ z, z ∈ˢ A) → ∃ y, y ∈ˢ C
  | [], x, hx, _ => ⟨x, hx⟩
  | A :: As, x, hx, hg => by
    have hx' : x ∈ˢ piR 0 A (fun _ => ihSpL 0 C As) := hx
    rw [piR_zero] at hx'
    obtain ⟨z, hz⟩ := hg A List.mem_cons_self
    obtain ⟨y, hy⟩ := of_mem_truthVal hx' z hz
    exact ihSpL_zero_inhab hy (fun A hA => hg A (List.mem_cons_of_mem _ hA))

omit [SetTheory V] in
theorem AnnotTerm.mkAppN_append (f : AnnotTerm) :
    ∀ (as bs : List AnnotTerm), AnnotTerm.mkAppN f (as ++ bs) = AnnotTerm.mkAppN (AnnotTerm.mkAppN f as) bs
  | [], _ => rfl
  | a :: as, bs => by
    rw [List.cons_append, AnnotTerm.mkAppN_cons, AnnotTerm.mkAppN_cons]
    exact AnnotTerm.mkAppN_append (.app f a) as bs

/-! ## The spelled pieces -/

/-- Constructor `j`'s branch with abstract inductive-hypothesis
arguments (`ihArgs D j`, spelled at the payload frame at depth `D + 1`). -/
def caseBaseAVI (ℓ w : Nat) (Fss : List (List AnnotTerm)) (ar : Nat → Nat)
    (ihArgs : Nat → Nat → List AnnotTerm) (n nIdx D j : Nat) : AnnotTerm :=
  .lam ℓ ((towerBodyAV w (Fss.getD j [])).liftN D 0)
    (AnnotTerm.mkAppN (.bvar (D + 1 + nIdx + n - 1 - j))
      (((List.range (ar j)).map fun i => projAV i (.bvar 0)) ++ ihArgs D j))

/-- The case recursor with inductive hypotheses from stage `j` with
`r` constructors remaining, at depth `D`, on the tag `k`. -/
def caseRecAVI (ℓ w : Nat) (Fss : List (List AnnotTerm)) (ar : Nat → Nat)
    (ihArgs : Nat → Nat → List AnnotTerm) (n nIdx : Nat) : Nat → Nat → Nat → AnnotTerm → AnnotTerm
  | 0, _, _, _ => .lam ℓ (.const .empty [w]) .prf
  | r + 1, D, j, k =>
    natRecAV (imaxN w ℓ) (caseMotiveAV ℓ w Fss n nIdx D j) (caseBaseAVI ℓ w Fss ar ihArgs n nIdx D j)
      (.lam (imaxN w ℓ) natAV (.lam (imaxN w ℓ) (caseMotiveBodyAV ℓ w Fss n nIdx D j)
        (caseRecAVI ℓ w Fss ar ihArgs n nIdx r (D + 2) (j + 1) (.bvar 1))))
      k

/-- Constructor `j`'s branch, semantically: the minor applied along
the payload's first `nF` projections and then along the ih values
(`ihVals j y`). -/
noncomputable def baseSemI (ℓ : Nat) (f : Nat → V) (ms : Nat → V) (nF : Nat)
    (ihVals : Nat → V → List V) (j : Nat) : V :=
  lamR ℓ (f j) fun y =>
    (((List.range nF).map fun i => projS i y) ++ ihVals j y).foldl SetTheory.app (ms j)

/-! ## The hypotheses -/

/-- The recursive route's K-frame hypotheses: the sum route's core and
the minors in their ih-extended spaces — the ih domains `ihDoms j f⃗` a
function of the fields. -/
structure RecHypI (ℓ w : Nat) (ρ₀ : Nat → V) (Fss Ess : List (List AnnotTerm))
    (Ids : List AnnotTerm) (famAt : List V → V) (ihDoms : Nat → List V → List V) : Prop
    extends RecHypCore ℓ w ρ₀ Fss Ess Ids famAt where
  hms : ∀ j, j < Fss.length →
    frMs Fss.length Ids.length ρ₀ j
      ∈ˢ minorSpI ℓ
        (fun fs => ihSpL ℓ
          (concI w (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀) (Ess.getD j []) j fs)
          (ihDoms j fs))
        (Fss.getD j []) (frP Fss.length Ids.length ρ₀) []
  hdoms0 : ℓ = 0 → ∀ j fs, ∀ A ∈ ihDoms j fs, A ∈ˢ (univZero : V)

namespace RecHypI

variable {ℓ w : Nat} {ρ₀ : Nat → V} {Fss Ess : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {famAt : List V → V} {ihDoms : Nat → List V → List V}

/-- At a zero elimination level the minors are the point. -/
theorem minor_pt (h : RecHypI ℓ w ρ₀ Fss Ess Ids famAt ihDoms) (h0 : ℓ = 0) {j : Nat}
    (hj : j < Fss.length) : frMs Fss.length Ids.length ρ₀ j = pt :=
  eq_pt_of_mem_univZero
    (h0 ▸ minorSpI_zero_univZero h0
      (fun fs => ihSpL_zero_univZero h0 (h.conc_univZero h0 hj fs) _) _ _ _)
    (h.hms j hj)

end RecHypI

/-- The ih arguments' obligation at a frame `σ` at depth `D`: at every
payload of constructor `j`'s fibre the arguments read to the ih values
`ihVals j y` (a function of the K-frame and the payload alone), are as
many as the ih domains, graded, and their values lie in the domains. -/
def IhArgsOk (w : Nat) (ρ₀ σ : Nat → V) (Fss Ess : List (List AnnotTerm)) (Ids : List AnnotTerm)
    (ihDoms : Nat → List V → List V) (ihVals : Nat → V → List V)
    (ihArgs : Nat → Nat → List AnnotTerm) (D j : Nat) : Prop :=
  ∀ y, y ∈ˢ sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) j →
    (ihArgs D j).map (interp V (cons y σ)) = ihVals j y ∧
    (ihArgs D j).length = (ihDoms j (projList (Fss.getD j []).length y)).length ∧
    ∀ l, l < (ihDoms j (projList (Fss.getD j []).length y)).length →
      WellDenoted V (cons y σ) ((ihArgs D j).getD l default) ∧
      interp V (cons y σ) ((ihArgs D j).getD l default)
        ∈ˢ (ihDoms j (projList (Fss.getD j []).length y)).getD l pt

/-! ## The base branch -/

/-- Constructor `j`'s branch with ihs (graph regime): its value, its
grading, its membership in the stage motive at the numeral `0`. -/
theorem base_factsI {ℓ w D : Nat} (hw : w ≠ 0) {ρ₀ σ : Nat → V} {Fss Ess : List (List AnnotTerm)}
    {Ids : List AnnotTerm} {famAt : List V → V} {ihDoms : Nat → List V → List V}
    {ihVals : Nat → V → List V} {ihArgs : Nat → Nat → List AnnotTerm}
    (hfr : RecFrameS D ρ₀ σ) (hyp : RecHypI ℓ w ρ₀ Fss Ess Ids famAt ihDoms)
    {j : Nat} (hj : j < Fss.length)
    (hih : IhArgsOk w ρ₀ σ Fss Ess Ids ihDoms ihVals ihArgs D j) :
    interp V σ (caseBaseAVI ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          (fun j => (Fss.getD j []).length) ihArgs Fss.length Ids.length D j)
        = baseSemI ℓ (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
            (frMs Fss.length Ids.length ρ₀) (Fss.getD j []).length ihVals j ∧
      WellDenoted V σ (caseBaseAVI ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          (fun j => (Fss.getD j []).length) ihArgs Fss.length Ids.length D j) ∧
      interp V σ (caseBaseAVI ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          (fun j => (Fss.getD j []).length) ihArgs Fss.length Ids.length D j)
        ∈ˢ motSem ℓ w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
            (frMi Fss.length Ids.length ρ₀) j (vnat 0) := by
  have hjF := hyp.rChain_getElem? hj
  have hokF : FieldsOkB w ρ₀
      (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j [])) :=
    hyp.hok _ (List.mem_of_getElem? hjF)
  have hfj : sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) j
      = towerSet w (teleOfFields ρ₀
          (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j []))) :=
    sumFibre_of_getElem? hjF
  have hgetD : (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess).getD j []
      = rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j []) := by
    rw [List.getD_eq_getElem?_getD, hjF]; rfl
  have hdomv : interp V σ ((towerBodyAV w
        ((rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess).getD j [])).liftN D 0)
      = towerSet w (teleOfFields ρ₀
          (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j []))) := by
    rw [interp_liftN, hfr, hgetD]
    exact towerBodyAV_interp (fun hw => hokF.toBound hw)
  have hokdom : WellDenoted V σ ((towerBodyAV w
      ((rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess).getD j [])).liftN D 0) := by
    rw [WellDenoted_liftN, hfr, hgetD]
    exact towerBodyAV_wellDenoted hokF
  have hminor : ∀ y : V, cons y σ (D + 1 + Ids.length + Fss.length - 1 - j)
      = frMs Fss.length Ids.length ρ₀ j :=
    fun y => (hfr.push y).minor hj
  have hms := hyp.hms j hj
  have hEslen : (Ess.getD j []).length = Ids.length := hyp.hEs j hj
  have hc0 : ℓ = 0 → ∀ acc, concI w (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀)
      (Ess.getD j []) j acc ∈ˢ (univZero : V) :=
    fun h0 acc => hyp.conc_univZero h0 hj acc
  -- the body at a payload: the minor's fold along the projections and the ihs
  have hbody : ∀ y : V, y ∈ˢ towerSet w (teleOfFields ρ₀
        (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j []))) →
      WellDenoted V (cons y σ) (AnnotTerm.mkAppN (.bvar (D + 1 + Ids.length + Fss.length - 1 - j))
        (((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)) ++ ihArgs D j)) ∧
      interp V (cons y σ) (AnnotTerm.mkAppN (.bvar (D + 1 + Ids.length + Fss.length - 1 - j))
        (((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)) ++ ihArgs D j))
        = (((List.range (Fss.getD j []).length).map fun i => projS i y) ++ ihVals j y).foldl
            SetTheory.app (frMs Fss.length Ids.length ρ₀ j) ∧
      interp V (cons y σ) (AnnotTerm.mkAppN (.bvar (D + 1 + Ids.length + Fss.length - 1 - j))
        (((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)) ++ ihArgs D j))
        ∈ˢ SetTheory.app (frMi Fss.length Ids.length ρ₀) (injW w j y) := by
    intro y hy
    have hyf : y ∈ˢ sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) j := by
      rw [hfj]; exact hy
    obtain ⟨hvals, hihlen, hihok⟩ := hih y hyf
    have hpv : ∀ i, interp V (cons y σ) (projAV i (.bvar 0)) = projS i y := by
      intro i; rw [projAV_interp, interp_bvar]; rfl
    have hval : interp V (cons y σ) (AnnotTerm.mkAppN (.bvar (D + 1 + Ids.length + Fss.length - 1 - j))
        (((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)) ++ ihArgs D j))
        = (((List.range (Fss.getD j []).length).map fun i => projS i y) ++ ihVals j y).foldl
            SetTheory.app (frMs Fss.length Ids.length ρ₀ j) := by
      rw [interp_mkAppN, ← List.foldl_map (f := interp V (cons y σ)) (g := SetTheory.app),
        interp_bvar, hminor, List.map_append, hvals, List.map_map]
      congr 2
      apply List.map_congr_left
      intro i _
      exact hpv i
    -- the payload's projections: fitting, the index equation, the eta
    have helim := restricted_member_elim hw
      (Fs := liftFields (Ids.length + Fss.length + 1) 0 (Fss.getD j []))
      (eqs := idxEqsAt (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []).length (Ess.getD j []))
      (ρ := ρ₀) (y := y) hy
    rw [liftFields_length] at helim
    obtain ⟨hspL, hlast, hall, heta⟩ := helim
    have hspP : SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD j [])
        (projList (Fss.getD j []).length y) :=
      (spineFit_liftFields (Ids.length + Fss.length + 1)).mp hspL
    have hidx : idxValsAt (frP Fss.length Ids.length ρ₀) (Ess.getD j [])
        (projList (Fss.getD j []).length y) = frameIdx Ids.length ρ₀ :=
      (EqAll_idxEqsAt hEslen (projList_length _ _)).mp hall
    -- the projection spine fits the field chain
    have hbnd : FieldsBound w ρ₀
        (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j [])) :=
      hokF.toBound hw
    have hlenR : (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j [])).length
        = (Fss.getD j []).length + 1 := rChain_length _ _ _ _
    have hpok : ∀ i, i < (Fss.getD j []).length → WellDenoted V (cons y σ) (projAV i (.bvar 0)) := by
      intro i hi
      exact projAV_wellDenoted_tower (by simp) (by rw [interp_bvar]; exact hy) hbnd (by omega)
    have hfit : ArgsOkFit (cons y σ)
        ((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0))
        (Fss.getD j []) (frP Fss.length Ids.length ρ₀) := by
      rw [List.range_eq_range']
      refine argsOkFit_of_projSpine (y := y) ?_ ?_ ?_
      · rw [← List.range_eq_range', ← projList_eq_map_range]; exact hspP
      · intro i _ hi
        exact hpok i (by omega)
      · exact hpv
    have hmap : (((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)).map
        (interp V (cons y σ))) = projList (Fss.getD j []).length y := by
      rw [List.map_map, projList_eq_map_range]
      apply List.map_congr_left
      intro i _
      exact hpv i
    -- the conclusion at the projections
    have hconv : concI w (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀) (Ess.getD j []) j
        (projList (Fss.getD j []).length y)
        = SetTheory.app (frMi Fss.length Ids.length ρ₀) (injW w j y) := by
      unfold concI ctorValI frMi
      rw [hidx, if_neg hw, injW_pos hw, ← heta]
    -- the fold along the fields lands in the ih tower
    have hsp := minorSpI_spine (V := V)
      (c := fun fs => ihSpL ℓ
        (concI w (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀) (Ess.getD j []) j fs)
        (ihDoms j fs))
      (fun h0 fs => ihSpL_zero_univZero h0 (hc0 h0 fs) _) (Fs := Fss.getD j [])
      (args := (List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0))
      (ρf := frP Fss.length Ids.length ρ₀) (acc := [])
      (f := .bvar (D + 1 + Ids.length + Fss.length - 1 - j)) (σ := cons y σ) (by simp)
      (by rw [interp_bvar, hminor]; exact hms) hfit
    rw [List.nil_append, hmap] at hsp
    -- then along the ihs
    have hih' := ihSpL_spine (V := V) (ℓ := ℓ)
      (C := concI w (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀) (Ess.getD j [])
        j (projList (Fss.getD j []).length y))
      (fun h0 => hc0 h0 _)
      (As := ihDoms j (projList (Fss.getD j []).length y))
      (args := ihArgs D j)
      (σ := cons y σ) hsp.1 hsp.2 hihlen hihok (fun h0 A hA => hyp.hdoms0 h0 j _ A hA)
    rw [← AnnotTerm.mkAppN_append] at hih'
    rw [hconv] at hih'
    exact ⟨hih'.1, hval, hih'.2⟩
  refine ⟨?_, ?_, ?_⟩
  · show lamR ℓ _ _ = _
    unfold baseSemI
    rw [hdomv, hfj]
    exact lamR_congr fun y hy => (hbody y hy).2.1
  · show WellDenoted V σ (.lam ℓ _ _)
    rw [WellDenoted_lam]
    refine ⟨hokdom, fun y hy => (hbody y (hdomv ▸ hy)).1,
      fun y => SetTheory.app (frMi Fss.length Ids.length ρ₀) (injW w j y),
      fun y hy => (hbody y (hdomv ▸ hy)).2.2, fun h0 y hy => ?_⟩
    have := hyp.hMapp (injW_mem (f := sumFibre w ρ₀
      (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)) (i := j)
      (by rw [hfj]; exact hdomv ▸ hy))
    rwa [h0, univ_zero] at this
  · show lamR ℓ _ _ ∈ˢ _
    rw [motSem_vnat]
    simp only [Nat.add_zero]
    rw [hfj, hdomv]
    exact lamR_mem fun y hy => (hbody y hy).2.2

/-! ## The case recursor -/

/-- **The case recursor's facts** with inductive hypotheses (graph
regime): `caseRec_facts` re-run with the ih branch.  The ih obligation
is asked at every frame the nesting reaches. -/
theorem caseRec_factsI {ℓ w : Nat} (hw : w ≠ 0) {ρ₀ : Nat → V} {Fss Ess : List (List AnnotTerm)}
    {Ids : List AnnotTerm} {famAt : List V → V} {ihDoms : Nat → List V → List V}
    {ihVals : Nat → V → List V} {ihArgs : Nat → Nat → List AnnotTerm}
    (hyp : RecHypI ℓ w ρ₀ Fss Ess Ids famAt ihDoms)
    (hih : ∀ (D' j' : Nat) (σ' : Nat → V), RecFrameS D' ρ₀ σ' → j' < Fss.length →
      IhArgsOk w ρ₀ σ' Fss Ess Ids ihDoms ihVals ihArgs D' j') :
    ∀ (r : Nat) {D j : Nat} {σ : Nat → V} {k : AnnotTerm},
      RecFrameS D ρ₀ σ → j + r = Fss.length →
      ((interp V σ k ∈ˢ (omega : V) →
        interp V σ (caseRecAVI ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
            (fun j => (Fss.getD j []).length) ihArgs Fss.length Ids.length r D j k)
          ∈ˢ motSem ℓ w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
              (frMi Fss.length Ids.length ρ₀) j (interp V σ k) ∧
        ∀ i, interp V σ k = vnat i → i < r →
          interp V σ (caseRecAVI ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
              (fun j => (Fss.getD j []).length) ihArgs Fss.length Ids.length r D j k)
            = baseSemI ℓ (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
                (frMs Fss.length Ids.length ρ₀) (Fss.getD (j + i) []).length ihVals (j + i)) ∧
      (WellDenoted V σ k → (ℓ ≠ 0 → interp V σ k ∈ˢ (omega : V)) →
        WellDenoted V σ (caseRecAVI ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          (fun j => (Fss.getD j []).length) ihArgs Fss.length Ids.length r D j k)))
  | 0, D, j, σ, k, hfr, hjr => by
    refine ⟨fun hk => ⟨?_, fun i _ hi => absurd hi (Nat.not_lt_zero i)⟩, fun _ _ => ?_⟩
    · obtain ⟨i, hki⟩ := mem_omega_iff.mp hk
      rw [hki, motSem_vnat]
      show lamR ℓ (empty : V) _ ∈ˢ _
      rw [sumFibre_of_ge (by rw [hyp.rChains_length']; omega)]
      exact lamR_mem fun _ hx => absurd hx (not_mem_empty _)
    · show WellDenoted V σ (.lam ℓ (.const .empty [w]) .prf)
      rw [WellDenoted_lam]
      exact ⟨trivial, fun _ hx => absurd hx (not_mem_empty _), fun _ => unitSet,
        fun _ hx => absurd hx (not_mem_empty _), fun _ _ hx => absurd hx (not_mem_empty _)⟩
  | r + 1, D, j, σ, k, hfr, hjr => by
    have hjn : j < Fss.length := by omega
    obtain ⟨hMv, hMsp, hMapp, hMok⟩ := motive_facts hfr hyp.toRecHypCore j
    obtain ⟨hzv, hzok, hzm⟩ := base_factsI hw hfr hyp hjn (hih D j σ hfr hjn)
    generalize hR : rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess = Fss' at *
    generalize hAr : (fun j => (Fss.getD j []).length) = ar at *
    have hz : interp V σ (caseBaseAVI ℓ w Fss' ar ihArgs Fss.length Ids.length D j)
        ∈ˢ SetTheory.app (interp V σ (caseMotiveAV ℓ w Fss' Fss.length Ids.length D j)) natzero := by
      rw [hMapp natzero natzero_mem, natzero_eq_vnat]; exact hzm
    -- the step's inner recursor at every step frame
    have hinner : ∀ (a b : V), b ∈ˢ (omega : V) →
        interp V (cons a (cons b σ))
            (caseRecAVI ℓ w Fss' ar ihArgs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))
          ∈ˢ motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) (j + 1) b ∧
        (∀ i, b = vnat i → i < r →
          interp V (cons a (cons b σ))
              (caseRecAVI ℓ w Fss' ar ihArgs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))
            = baseSemI ℓ (sumFibre w ρ₀ Fss') (frMs Fss.length Ids.length ρ₀)
                (Fss.getD (j + 1 + i) []).length ihVals (j + 1 + i)) ∧
        WellDenoted V (cons a (cons b σ))
          (caseRecAVI ℓ w Fss' ar ihArgs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1)) := by
      intro a b hb
      have h := caseRec_factsI hw hyp hih r (D := D + 2) (j := j + 1) (σ := cons a (cons b σ))
        (k := .bvar 1) (hfr.step a b) (by omega)
      rw [hR, hAr] at h
      have hb' : interp V (cons a (cons b σ)) (.bvar 1) ∈ˢ (omega : V) := by
        rw [interp_bvar]; exact hb
      refine ⟨(h.1 hb').1, fun i hi hir => (h.1 hb').2 i (by rw [interp_bvar]; exact hi) hir,
        h.2 trivial (fun _ => hb')⟩
    -- the motive at a successor is the next stage's motive
    have hsucc : ∀ (i : Nat), motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (vnat (i + 1))
        = motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) (j + 1) (vnat i) := by
      intro i
      rw [motSem_vnat, motSem_vnat, show j + (i + 1) = j + 1 + i from by omega]
    -- the step: its value and its membership in the step space
    have hsv : interp V σ (.lam (imaxN w ℓ) natAV (.lam (imaxN w ℓ)
          (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j)
          (caseRecAVI ℓ w Fss' ar ihArgs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))))
        = lamR (imaxN w ℓ) omega fun b =>
            lamR (imaxN w ℓ) (interp V (cons b σ) (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j))
              fun a => interp V (cons a (cons b σ))
                (caseRecAVI ℓ w Fss' ar ihArgs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1)) := rfl
    have hmb := fun (b : V) (hb : b ∈ˢ (omega : V)) => motiveBody_facts hfr hyp.toRecHypCore j hb
    rw [hR] at hmb
    have hs : interp V σ (.lam (imaxN w ℓ) natAV (.lam (imaxN w ℓ)
          (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j)
          (caseRecAVI ℓ w Fss' ar ihArgs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))))
        ∈ˢ natStepSpace V (imaxN w ℓ) (interp V σ (caseMotiveAV ℓ w Fss' Fss.length Ids.length D j)) := by
      rw [hsv]
      unfold natStepSpace
      refine lamR_mem fun b hb => ?_
      rw [hMapp b hb, hMapp (natsucc b) (natsucc_mem hb), (hmb b hb).1]
      refine lamR_mem fun a _ => ?_
      obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
      rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
      exact (hinner a _ hb).1
    refine ⟨fun hk => ⟨?_, ?_⟩, fun hokk hkω => ?_⟩
    · -- membership
      have h := natRecAV_mem hMsp hz hs hk
      rwa [hMapp _ hk] at h
    · -- iota
      intro i hi hir
      show interp V σ (natRecAV (imaxN w ℓ) _ _ _ k) = _
      rw [interp_natRecAV hMsp hz hs hk, hi, natrec_vnat]
      -- the iteration's values inhabit the stage motive
      have hiter : ∀ i', natIter (interp V σ (caseBaseAVI ℓ w Fss' ar ihArgs Fss.length Ids.length D j))
          (interp V σ (.lam (imaxN w ℓ) natAV (.lam (imaxN w ℓ)
            (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j)
            (caseRecAVI ℓ w Fss' ar ihArgs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))))) i'
          ∈ˢ motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (vnat i') := by
        intro i'
        have h := natRecV_mem_fibre V hMsp hz hs (vnat_mem_omega i')
        rwa [natrec_vnat, hMapp _ (vnat_mem_omega i')] at h
      cases i with
      | zero =>
        rw [Nat.add_zero]
        exact hzv
      | succ i =>
        show SetTheory.app (SetTheory.app _ (vnat i)) (natIter _ _ i) = _
        by_cases h0 : ℓ = 0
        · -- the zero level: everything is the point
          have hz' : imaxN w ℓ = 0 := (imaxN_eq_zero_iff w ℓ).mpr h0
          rw [hsv, hz', lamR_zero, app_pt, app_pt]
          unfold baseSemI
          rw [h0, lamR_zero]
        · have hz' : imaxN w ℓ ≠ 0 := fun h => h0 ((imaxN_eq_zero_iff w ℓ).mp h)
          rw [hsv, app_lamR_pos hz' (vnat_mem_omega i),
            app_lamR_pos hz' (by
              rw [(hmb _ (vnat_mem_omega i)).1]
              exact hiter i),
            (hinner _ _ (vnat_mem_omega i)).2.1 i rfl (by omega),
            show j + 1 + i = j + (i + 1) from by omega]
    · -- the grading
      by_cases h0 : ℓ = 0
      · -- the point-headed spine
        have hz' : imaxN w ℓ = 0 := (imaxN_eq_zero_iff w ℓ).mpr h0
        refine (mkAppN_wellDenoted_of_pt_head (f := .const .natRec [imaxN w ℓ]) (σ := σ) trivial
          (by show natRecV V (imaxN w ℓ) = pt; rw [hz', natRecV, lamR_zero]) ?_).1
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact hMok
        · exact hzok
        · rw [WellDenoted_lam]
          refine ⟨trivial, fun b hb => ?_, fun b => piR (imaxN w ℓ)
              (motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j b)
              (fun _ => motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (natsucc b)),
            fun b hb => ?_, fun _ b hb => by rw [hz']; exact piR_zero_mem_univZero⟩
          · rw [WellDenoted_lam]
            refine ⟨(hmb b hb).2, fun a _ => (hinner a b hb).2.2,
              fun _ => motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (natsucc b),
              fun a _ => ?_, fun _ a _ => ?_⟩
            · obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
              rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
              exact (hinner a _ hb).1
            · obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
              rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc,
                motSem_vnat, h0]
              exact piR_zero_mem_univZero
          · show lamR (imaxN w ℓ) (interp V (cons b σ) (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j))
              (fun a => interp V (cons a (cons b σ))
                (caseRecAVI ℓ w Fss' ar ihArgs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))) ∈ˢ piR (imaxN w ℓ) _ _
            rw [(hmb b hb).1]
            refine lamR_mem fun a _ => ?_
            obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
            rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
            exact (hinner a _ hb).1
        · exact hokk
      · -- `Nat.rec`'s own chain
        refine natRecAV_wellDenoted hMok hzok ?_ hokk hMsp hz hs (hkω h0)
        rw [WellDenoted_lam]
        refine ⟨trivial, fun b hb => ?_, fun b => piR (imaxN w ℓ)
            (motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j b)
            (fun _ => motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (natsucc b)),
          fun b hb => ?_, fun h => absurd ((imaxN_eq_zero_iff w ℓ).mp h) h0⟩
        · rw [WellDenoted_lam]
          refine ⟨(hmb b hb).2, fun a _ => (hinner a b hb).2.2,
            fun _ => motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (natsucc b),
            fun a _ => ?_, fun h => absurd ((imaxN_eq_zero_iff w ℓ).mp h) h0⟩
          obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
          rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
          exact (hinner a _ hb).1
        · show lamR (imaxN w ℓ) (interp V (cons b σ) (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j))
            (fun a => interp V (cons a (cons b σ))
              (caseRecAVI ℓ w Fss' ar ihArgs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))) ∈ˢ piR (imaxN w ℓ) _ _
          rw [(hmb b hb).1]
          refine lamR_mem fun a _ => ?_
          obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
          rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
          exact (hinner a _ hb).1

end ConLeche.Semantics
