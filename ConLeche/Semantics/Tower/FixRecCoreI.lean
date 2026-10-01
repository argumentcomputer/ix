module

import ConLeche.Semantics.Tower.FixCaseI
import ConLeche.Semantics.Tower.SumRec
public import ConLeche.Semantics.Tower.SumWire
public import ConLeche.Semantics.Tower.IhSpell

@[expose] public section

/-!
# The recursive family's recursor, core: the step and the premise (task #188, indexed)

The recursor of a directly installed recursive family is spelled as a
**closed** term — a fixed point of its one-step unfolding over the
recursor's whole type `RecTy = Π p⃗ M m⃗ ı⃗ t, M ı⃗ t`, selected by
`Classical.choice`:

    Step := λ (r : RecTy). λ p⃗ M m⃗ ı⃗ t. case_r t     (`fixStepAVI`)
    Σ    := Σ' (r : RecTy), Step r = r                 (`fixSigAVI`)
    Sel  := (choice Σ prf).1                           (`fixSelAVI`; the leaf)

The function being unfolded thus sits at the BOTTOM of every frame of
the case split — below the parameters — so the sum route's K-frame
arithmetic (`(p⃗, M, m⃗, ı⃗)` above the frame's tail) applies unchanged,
and the recursor type's binder data, being closed, needs no lifting
under `λ r`.  The inductive hypothesis for a recursive field `f_i`
(with index expressions `e⃗_i` at the earlier fields) is
`r p⃗ M m⃗ e⃗_i f_i`, the index expressions read at the payload's
projections by SUBSTITUTION (`substProj`: `interp_inst0` at each field
binder — no λ-tower).  The case split's abstract ih obligation
(`IhArgsOk`, `FixCaseI.lean`) is discharged here.

The certificate `prf : ¬¬Σ` is the existence of a fixed point,
exhibited by rank recursion over the ω-iterate family (`fixSem`, as in
the non-indexed checkpoint): the candidate is the semantic λ-tower over
the recursor's binder data (`lamTower`) whose body at a leaf frame is the
major's own stage's value.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Term (Term)

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## Substitution of the payload's projections -/

/-- Substitute the `i` innermost (virtual) field variables by the
projections of the payload `y = bvar 0` below them. -/
def substProj : Nat → AnnotTerm → AnnotTerm
  | 0, e => e
  | i + 1, e => substProj i (e.inst (projAV i (.bvar i)))

theorem interp_substProj (σ : Nat → V) (y : V) :
    ∀ (i : Nat) (e : AnnotTerm),
      interp V (cons y σ) (substProj i e) = interp V (consList (projList i y) (cons y σ)) e
  | 0, _ => rfl
  | i + 1, e => by
    show interp V (cons y σ) (substProj i (e.inst (projAV i (.bvar i)))) = _
    rw [interp_substProj σ y i, interp_inst0, projAV_interp, interp_bvar]
    have hy : consList (projList i y) (cons y σ) i = y := by
      have := consList_apply_add (projList i y) (cons y σ) 0
      rwa [Nat.zero_add, projList_length] at this
    rw [hy, consList_snoc', ← projList_snoc]

theorem WellDenoted_substProj (σ : Nat → V) (y : V) :
    ∀ (i : Nat) (e : AnnotTerm),
      (∀ m, m < i → WellDenoted V (consList (projList m y) (cons y σ)) (projAV m (.bvar m))) →
      (WellDenoted V (cons y σ) (substProj i e) ↔
        WellDenoted V (consList (projList i y) (cons y σ)) e)
  | 0, _, _ => Iff.rfl
  | i + 1, e, hp => by
    show WellDenoted V (cons y σ) (substProj i (e.inst (projAV i (.bvar i)))) ↔ _
    rw [WellDenoted_substProj σ y i _ (fun m hm => hp m (by omega)),
      WellDenoted_inst0 V (hp i (by omega)), projAV_interp, interp_bvar]
    have hy : consList (projList i y) (cons y σ) i = y := by
      have := consList_apply_add (projList i y) (cons y σ) 0
      rwa [Nat.zero_add, projList_length] at this
    rw [hy, consList_snoc', ← projList_snoc]

omit [SetTheory V] in
theorem shiftE_add' (a b : Nat) (ρ : Nat → V) : shiftE (a + b) 0 ρ = shiftE b 0 (shiftE a 0 ρ) := by
  rw [shiftE_zero, shiftE_zero, shiftE_zero]
  funext i
  show ρ (i + (a + b)) = ρ (i + b + a)
  congr 1
  omega

/-! ## The Π-tower's fold and application chain -/

/-- A member of a Π-tower's reading, applied along a fitting spine,
lands in the conclusion's reading at the spine's frame. -/
theorem mkPisAV_fold_mem {m : Nat} {C : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {f : V} {as : List V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) →
      (m = 0 → ∀ as', SpineFit ρ (ds.map (·.2.2)) as' → interp V (consList as' ρ) C ∈ˢ (univZero : V)) →
      f ∈ˢ interp V ρ (mkPisAV ds C) → SpineFit ρ (ds.map (·.2.2)) as →
      as.foldl SetTheory.app f ∈ˢ interp V (consList as ρ) C
  | [], _, _, [], _, _, hf, _ => hf
  | [], _, _, _ :: _, _, _, _, hsp => hsp.elim
  | _ :: _, _, _, [], _, _, _, hsp => hsp.elim
  | d :: ds, ρ, f, a :: as, hz, h0, hf, hsp => by
    have hf' : f ∈ˢ piR d.2.1 (interp V ρ d.2.2)
        (fun x => interp V (cons x ρ) (mkPisAV ds C)) := hf
    have hB0 : d.2.1 = 0 → ∀ x, x ∈ˢ interp V ρ d.2.2 →
        interp V (cons x ρ) (mkPisAV ds C) ∈ˢ (univZero : V) := by
      intro hd x hx
      have hm : m = 0 := (hz d (.head _)).mpr hd
      cases ds with
      | nil =>
        have := h0 hm [x] ⟨hx, trivial⟩
        rw [consList_cons, consList_nil] at this
        exact this
      | cons d' ds' =>
        show piR d'.2.1 _ _ ∈ˢ _
        rw [(hz d' (.tail _ (.head _))).mp hm]
        exact piR_zero_mem_univZero
    rw [List.foldl_cons]
    refine mkPisAV_fold_mem (ds := ds) (ρ := cons a ρ) (f := SetTheory.app f a) (as := as)
      (fun d' hd' => hz d' (.tail _ hd')) ?_ (app_mem_piR hf' hsp.1 hB0) hsp.2
    intro hm as' hsp'
    have := h0 hm (a :: as') ⟨hsp.1, hsp'⟩
    rwa [consList_cons] at this

/-- The application chain of a Π-tower member along a fitting spine is
graded. -/
theorem appChainOk_of_mkPisAV' {m : Nat} {C : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {f : V} {as : List V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) →
      (m = 0 → ∀ as', SpineFit ρ (ds.map (·.2.2)) as' → interp V (consList as' ρ) C ∈ˢ (univZero : V)) →
      f ∈ˢ interp V ρ (mkPisAV ds C) → SpineFit ρ (ds.map (·.2.2)) as → AppChainOk f as
  | [], _, _, [], _, _, _, _ => fun l hl => absurd hl (Nat.not_lt_zero _)
  | [], _, _, _ :: _, _, _, _, hsp => hsp.elim
  | _ :: _, _, _, [], _, _, _, hsp => hsp.elim
  | d :: ds, ρ, f, a :: as, hz, h0, hf, hsp => by
    have hf' : f ∈ˢ piR d.2.1 (interp V ρ d.2.2)
        (fun x => interp V (cons x ρ) (mkPisAV ds C)) := hf
    have hB0 : d.2.1 = 0 → ∀ x, x ∈ˢ interp V ρ d.2.2 →
        interp V (cons x ρ) (mkPisAV ds C) ∈ˢ (univZero : V) := by
      intro hd x hx
      have hm : m = 0 := (hz d (.head _)).mpr hd
      cases ds with
      | nil =>
        have := h0 hm [x] ⟨hx, trivial⟩
        rw [consList_cons, consList_nil] at this
        exact this
      | cons d' ds' =>
        show piR d'.2.1 _ _ ∈ˢ _
        rw [(hz d' (.tail _ (.head _))).mp hm]
        exact piR_zero_mem_univZero
    intro l hl
    cases l with
    | zero =>
      refine ⟨d.2.1, interp V ρ d.2.2, fun x => interp V (cons x ρ) (mkPisAV ds C), ?_, ?_, hB0⟩
      · simpa using hf'
      · simpa using hsp.1
    | succ l =>
      have ih := appChainOk_of_mkPisAV' (ds := ds) (ρ := cons a ρ) (f := SetTheory.app f a)
        (as := as) (fun d' hd' => hz d' (.tail _ hd'))
        (fun hm as' hsp' => by
          have := h0 hm (a :: as') ⟨hsp.1, hsp'⟩
          rwa [consList_cons] at this)
        (app_mem_piR hf' hsp.1 hB0) hsp.2 l (by simpa using hl)
      obtain ⟨v, A, B, h1, h2, h3⟩ := ih
      refine ⟨v, A, B, ?_, ?_, h3⟩
      · simpa only [List.take_succ_cons, List.foldl_cons] using h1
      · simpa only [List.getD_cons_succ] using h2

/-! ## The semantic λ-tower over binder data -/

/-- The semantic λ-tower over binder data, with a body given as a
function of the leaf frame. -/
noncomputable def lamTower (m : Nat) : (Nat → V) → List (Nat × Nat × AnnotTerm) → ((Nat → V) → V) → V
  | ρ, [], g => g ρ
  | ρ, d :: ds, g => lamR m (interp V ρ d.2.2) fun a => lamTower m (cons a ρ) ds g

/-- The tower's walk premise: at every leaf frame reached the body is
in the conclusion's reading (a truth value at a zero bit). -/
def TowerWalk (m : Nat) (C : AnnotTerm) (g : (Nat → V) → V) :
    (Nat → V) → List (Nat × Nat × AnnotTerm) → Prop
  | ρ, [] => g ρ ∈ˢ interp V ρ C ∧ (m = 0 → interp V ρ C ∈ˢ (univZero : V))
  | ρ, d :: ds => ∀ a, a ∈ˢ interp V ρ d.2.2 → TowerWalk m C g (cons a ρ) ds

/-- **The tower inhabits the Π-tower's reading.** -/
theorem lamTower_mem {m : Nat} {C : AnnotTerm} {g : (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) → TowerWalk m C g ρ ds →
      lamTower m ρ ds g ∈ˢ interp V ρ (mkPisAV ds C)
  | [], _, _, h => h.1
  | d :: ds, ρ, hz, h => by
    show lamR m (interp V ρ d.2.2) (fun a => lamTower m (cons a ρ) ds g)
      ∈ˢ piR d.2.1 (interp V ρ d.2.2) fun a => interp V (cons a ρ) (mkPisAV ds C)
    exact lamR_mem_zero_agree (hz d (.head _))
      fun a ha => lamTower_mem (fun d' hd' => hz d' (.tail _ hd')) (h a ha)

/-- The constant-bit spelled tower reads to the semantic tower. -/
theorem interp_mkLamsC (m : Nat) (b : AnnotTerm) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (ρ : Nat → V),
      interp V ρ (mkLamsC m ds b) = lamTower m ρ ds (fun σ => interp V σ b)
  | [], _ => rfl
  | d :: ds, ρ => by
    show lamR m (interp V ρ d.2.2) (fun a => interp V (cons a ρ) (mkLamsC m ds b)) = _
    unfold lamTower
    exact lamR_congr fun a _ => interp_mkLamsC m b ds (cons a ρ)

omit [SetTheory V] in
/-- Two frames agreeing below a depth. -/
theorem agreeOff_consList_ge : ∀ (as : List V) (ρ₁ ρ₂ : Nat → V),
    AgreeOff (fun i => as.length ≤ i) (consList as ρ₁) (consList as ρ₂)
  | [], _, _ => fun i hi => absurd (Nat.zero_le i) hi
  | a :: as, ρ₁, ρ₂ => by
    rw [consList_cons, consList_cons]
    intro i hi
    simp only [List.length_cons] at hi
    have hi' : i < as.length + 1 := Nat.lt_of_not_le hi
    by_cases h : i < as.length
    · exact agreeOff_consList_ge as (cons a ρ₁) (cons a ρ₂) i (by omega)
    · have hi'' : i = as.length := by omega
      subst hi''
      have h1 := consList_apply_add as (cons a ρ₁) 0
      have h2 := consList_apply_add as (cons a ρ₂) 0
      rw [Nat.zero_add] at h1 h2
      rw [h1, h2, cons_zero, cons_zero]

/-- **Bottom-frame independence** of a tower over closed binder data:
the domains are closed at their depth, so the readings agree at any
two bottoms; the bodies must agree at corresponding leaf frames. -/
theorem lamTower_congr_bottom {m : Nat} {g₁ g₂ : (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {as : List V} {ρ₁ ρ₂ : Nat → V},
      (∀ k d, ds[k]? = some d → Term.bvarsBelow (as.length + k) d.2.2.erase) →
      (∀ bs, SpineFit (consList as ρ₁) (ds.map (·.2.2)) bs →
        g₁ (consList (as ++ bs) ρ₁) = g₂ (consList (as ++ bs) ρ₂)) →
      lamTower m (consList as ρ₁) ds g₁ = lamTower m (consList as ρ₂) ds g₂
  | [], as, ρ₁, ρ₂, _, hg => by
    show g₁ (consList as ρ₁) = g₂ (consList as ρ₂)
    have := hg [] trivial
    simpa using this
  | d :: ds, as, ρ₁, ρ₂, hcl, hg => by
    show lamR m (interp V (consList as ρ₁) d.2.2) (fun a => lamTower m (cons a (consList as ρ₁)) ds g₁)
      = lamR m (interp V (consList as ρ₂) d.2.2) (fun a => lamTower m (cons a (consList as ρ₂)) ds g₂)
    have hdom : interp V (consList as ρ₁) d.2.2 = interp V (consList as ρ₂) d.2.2 :=
      interp_congr_noBVar d.2.2 (NoBVar_of_bvarsBelow (by simpa using hcl 0 d rfl) fun _ hi => hi)
        (agreeOff_consList_ge as ρ₁ ρ₂)
    rw [hdom]
    refine lamR_congr fun a ha => ?_
    rw [consList_snoc', consList_snoc']
    refine lamTower_congr_bottom (as := as ++ [a]) ?_ ?_
    · intro k d' hd'
      have := hcl (k + 1) d' (by simpa using hd')
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    · intro bs hbs
      have := hg (a :: bs) ⟨by show a ∈ˢ interp V (consList as ρ₁) d.2.2; rw [hdom]; exact ha,
        by rw [consList_snoc']; exact hbs⟩
      simpa [List.append_assoc] using this

/-! ## The K-frame's accessors -/

/-- The unfolded function's value: the entry just below the parameters. -/
noncomputable def frR (nP n nIdx : Nat) (ρ₀ : Nat → V) : V := frP n nIdx ρ₀ nP

/-- The minors' values, in order. -/
noncomputable def frMsL (n nIdx : Nat) (ρ₀ : Nat → V) : List V := (List.range n).map (frMs n nIdx ρ₀)

theorem frMsL_getD (n nIdx : Nat) (ρ₀ : Nat → V) {j : Nat} (hj : j < n) :
    (frMsL n nIdx ρ₀).getD j pt = frMs n nIdx ρ₀ j := by
  unfold frMsL
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some]

/-- The frame below the unfolded function. -/
noncomputable def frBelow (nP n nIdx : Nat) (ρ₀ : Nat → V) : Nat → V :=
  shiftE (nIdx + n + 1 + nP + 1) 0 ρ₀

/-- The K-frame's `(p⃗, M, m⃗)` part as a spine. -/
noncomputable def frKSpine (nP n nIdx : Nat) (ρ₀ : Nat → V) : List V :=
  frameIdx (nP + 1 + n) (shiftE nIdx 0 ρ₀)

omit [SetTheory V] in
/-- The frame below the function, consed with the function and the
`(p⃗, M, m⃗, ı⃗)` spine, is the K-frame. -/
theorem consList_frKSpine (nP n nIdx : Nat) (ρ₀ : Nat → V) :
    consList (frKSpine nP n nIdx ρ₀ ++ frameIdx nIdx ρ₀) (cons (frR nP n nIdx ρ₀) (frBelow nP n nIdx ρ₀))
      = ρ₀ := by
  have h1 : cons (frR nP n nIdx ρ₀) (frBelow nP n nIdx ρ₀) = shiftE (nIdx + n + 1 + nP) 0 ρ₀ := by
    funext i
    cases i with
    | zero =>
      show frP n nIdx ρ₀ nP = shiftE (nIdx + n + 1 + nP) 0 ρ₀ 0
      unfold frP
      rw [shiftE_zero, shiftE_zero]
      show ρ₀ (nP + (nIdx + n + 1)) = ρ₀ (0 + (nIdx + n + 1 + nP))
      congr 1; omega
    | succ i =>
      show frBelow nP n nIdx ρ₀ i = shiftE (nIdx + n + 1 + nP) 0 ρ₀ (i + 1)
      unfold frBelow
      rw [shiftE_zero, shiftE_zero]
      show ρ₀ (i + (nIdx + n + 1 + nP + 1)) = ρ₀ (i + 1 + (nIdx + n + 1 + nP))
      congr 1; omega
  have h2 : shiftE (nIdx + n + 1 + nP) 0 ρ₀ = shiftE (nP + 1 + n) 0 (shiftE nIdx 0 ρ₀) := by
    rw [← shiftE_add']; congr 1; omega
  rw [h1, h2, consList_append]
  unfold frKSpine
  rw [consList_frameIdx (nP + 1 + n) (shiftE nIdx 0 ρ₀)]
  exact consList_frameIdx nIdx ρ₀

/-! ## The inductive hypothesis arguments -/

/-- `substProj` under `m` binders: substitute the `i` field variables
sitting `m` binders up by the projections of the payload below them. -/
def substProjAt (m : Nat) : Nat → AnnotTerm → AnnotTerm
  | 0, e => e
  | i + 1, e => substProjAt m i (e.inst (projAV i (.bvar i)) m)

omit [SetTheory V] in
theorem substProjAt_zero : ∀ (i : Nat) (e : AnnotTerm), substProjAt 0 i e = substProj i e
  | 0, _ => rfl
  | i + 1, _ => substProjAt_zero i _

/-- A recursive field's telescope at the payload frame: binder `k`'s
domain lifted past the `(p⃗, M, m⃗)` block under the `i` field variables
and the `k` earlier telescope binders, the field variables replaced by
the payload's projections. -/
def ihTeleAt (nIdx n D i : Nat) (tl : List (Nat × Nat × AnnotTerm)) : List (Nat × Nat × AnnotTerm) :=
  (List.range tl.length).map fun k =>
    let d := tl.getD k default
    (d.1, d.2.1, substProjAt k i (d.2.2.liftN (D + nIdx + n + 2) (i + k)))

omit [SetTheory V] in
@[simp] theorem ihTeleAt_nil (nIdx n D i : Nat) : ihTeleAt nIdx n D i [] = [] := rfl

/-- The ih argument for recursive field `i` at the payload frame (depth
`D + 1`): under the field's telescope (a λ-tower at the elimination
level `ℓ`, empty at a finitary field), the unfolded function at the
`(p⃗, M, m⃗)` block, the field's index expressions (read at the
payload's projections, under the telescope) and the field applied to
the telescope's variables — `λ a⃗, r p⃗ M m⃗ e⃗_i(a⃗) (f_i a⃗)`. -/
def ihArgAV (ℓ nP n nIdx D i : Nat) (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm) : AnnotTerm :=
  let m := tl.length
  mkLamsC ℓ (ihTeleAt nIdx n D i tl)
    (AnnotTerm.mkAppN (.bvar (D + 1 + nIdx + n + 1 + nP + m))
      (idxVarsAV (nP + 1 + n) (D + 1 + nIdx + m) ++
        Eis.map (fun E => substProjAt m i (E.liftN (D + nIdx + n + 2) (i + m))) ++
        [AnnotTerm.mkAppN (projAV i (.bvar m)) (teleVarsAV m)]))

omit [SetTheory V] in

/-- The ih arguments of constructor `j`. -/
def ihArgsI (ℓ nP n nIdx : Nat) (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss : List (List (List AnnotTerm))) (ar : Nat → Nat) (D j : Nat) : List AnnotTerm :=
  (recIdx (rss.getD j []) (ar j)).map fun i =>
    ihArgAV ℓ nP n nIdx D i ((tlss.getD j []).getD i []) ((Eiss.getD j []).getD i [])

/-- The ih domains at a field spine: under the field's telescope (a
nested product at the elimination level `ℓ`), the motive at the
field's index values at the field applied to the telescope's values —
at a finitary field the motive at the index values at the field. -/
noncomputable def ihDomsI (ℓ : Nat) (ρp : Nat → V) (M : V) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm)))
    (ar : Nat → Nat) (j : Nat) (fs : List V) : List V :=
  (recIdx (rss.getD j []) (ar j)).map fun i =>
    piTele ℓ (teleOfFields (consList (fs.take i) ρp) (((tlss.getD j []).getD i []).map (·.2.2)))
      (fun as => SetTheory.app
        ((((Eiss.getD j []).getD i []).map (interp V (consList as (consList (fs.take i) ρp)))).foldl
          SetTheory.app M)
        (as.foldl SetTheory.app (fs.getD i pt))) []

/-- The ih values at a payload: under the field's telescope (a λ-tower
at the elimination level `ℓ`), the function at the spine and the field
applied to the telescope's values. -/
noncomputable def ihValsI (ℓ : Nat) (ρp : Nat → V) (rV : V) (kspine : List V) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm)))
    (ar : Nat → Nat) (j : Nat) (y : V) : List V :=
  (recIdx (rss.getD j []) (ar j)).map fun i =>
    lamTower ℓ (consList (projList i y) ρp) ((tlss.getD j []).getD i []) fun σ' =>
      (kspine ++ (((Eiss.getD j []).getD i []).map (interp V σ'))
        ++ [(frameIdx ((tlss.getD j []).getD i []).length σ').foldl SetTheory.app (projS i y)]).foldl
        SetTheory.app rV

section IhFacts

variable {ℓ w u nP : Nat} {ρ₀ σ : Nat → V} {Fss Ess : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {D : Nat}

theorem rAt_interp (hfr : RecFrameS D ρ₀ σ) (y : V) :
    interp V (cons y σ) (.bvar (D + 1 + Ids.length + Fss.length + 1 + nP))
      = frR nP Fss.length Ids.length ρ₀ := by
  rw [interp_bvar, show D + 1 + Ids.length + Fss.length + 1 + nP
      = (D + 1) + (Ids.length + Fss.length + 1 + nP) from by omega, (hfr.push y).apply]
  unfold frR frP
  rw [shiftE_zero]
  show ρ₀ _ = ρ₀ _
  congr 1
  omega

omit [SetTheory V] in
/-- The payload frame's shift by the K-frame's depth over the
parameter frame. -/
theorem shiftE_payload (hfr : RecFrameS D ρ₀ σ) (y : V) :
    shiftE (D + Ids.length + Fss.length + 2) 0 (cons y σ) = frP Fss.length Ids.length ρ₀ := by
  rw [show D + Ids.length + Fss.length + 2 = (D + 1) + (Ids.length + Fss.length + 1) from by omega,
    shiftE_add', shiftE_succ_cons, hfr]
  rfl

end IhFacts

/-! ## The K-frame package and the ih obligation -/

/-- The real-chain relation, walked down to a recursive position along a
fitting field spine: the index expressions there are graded and fit,
and the real domain reads to the carrier at their tuple. -/
theorem chainRealI_at {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {μ : V} {rs : List Bool}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} :
    ∀ (Fs₀ Fs : List AnnotTerm) (i₀ : Nat) (as fs : List V), as.length = i₀ →
      ChainRealI μ u w ρp Ids rs tls Eis i₀ as Fs₀ Fs → SpineFit (consList as ρp) Fs fs →
      ∀ l, l < Fs.length → rs.getD (i₀ + l) false = true →
        SlotFit u w ρp Ids (tls.getD (i₀ + l) []) (Eis.getD (i₀ + l) []) (as ++ fs.take l) ∧
        interp V (consList (as ++ fs.take l) ρp) (Fs.getD l default)
          = slotSet w u (consList (as ++ fs.take l) ρp) (tls.getD (i₀ + l) []) (Eis.getD (i₀ + l) []) μ
  | [], [], _, _, _, _, _, _, _, hl, _ => absurd hl (Nat.not_lt_zero _)
  | [], _ :: _, _, _, _, _, hc, _, _, _, _ => hc.elim
  | _ :: _, [], _, _, _, _, hc, _, _, _, _ => hc.elim
  | _ :: _, _ :: _, _, _, [], _, _, hsp, _, _, _ => hsp.elim
  | F₀ :: Fs₀, F :: Fs, i₀, as, f :: fs, hi, hc, hsp, l, hl, hr => by
    subst hi
    obtain ⟨hhead, htail⟩ := hc
    cases l with
    | zero =>
      rw [Nat.add_zero] at hr ⊢
      rw [if_pos hr] at hhead
      simpa using hhead
    | succ l =>
      have ih := chainRealI_at Fs₀ Fs (as.length + 1) (as ++ [f]) fs (length_snoc' f as)
        (htail f hsp.1) (by rw [← consList_snoc']; exact hsp.2) l (by simpa using hl)
        (by rw [show as.length + 1 + l = as.length + (l + 1) from by omega]; exact hr)
      rw [show as.length + 1 + l = as.length + (l + 1) from by omega] at ih
      simpa [List.append_assoc] using ih

/-- The recursor's conclusion `M ı⃗ t`, read at a walk frame. -/
theorem recConcAV_at {n nIdx : Nat} {ρ₁ : Nat → V} (vals : List V) (hlen : vals.length = nIdx) (f : V) :
    interp V (cons f (consList vals ρ₁)) (recConcAV n nIdx)
      = SetTheory.app (vals.foldl SetTheory.app (ρ₁ n)) f := by
  have hfr : RecFrameS 1 (consList vals ρ₁) (cons f (consList vals ρ₁)) := by
    unfold RecFrameS
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  unfold recConcAV motAppAV
  rw [interp_app, interp_mkAppN, ← List.foldl_map (f := interp V (cons f (consList vals ρ₁)))
    (g := SetTheory.app), map_idxVarsAV_interp hfr, interp_bvar, interp_bvar, cons_zero]
  have hM : cons f (consList vals ρ₁) (1 + nIdx + n) = ρ₁ n := by
    rw [show 1 + nIdx + n = (n + vals.length) + 1 from by omega, cons_succ, consList_apply_add]
  have hI : frameIdx nIdx (consList vals ρ₁) = vals := by
    rw [← hlen]; exact frameIdx_consList' vals ρ₁
  rw [hM, hI]

/-- **The K-frame package of the recursive family's recursor**: the
case split's hypotheses (with the family as `famAt` and the ih
domains at the motive), the family's functor facts at the parameter
frame, the identification of the real chains, and the unfolded
function's typing at the recursor's type (a closed Π-tower over the
binder data `rds`, read at the frame below the function) with the
spine-fit of the ih application. -/
structure FixKI₀ (ℓ w u : Nat) (ρ₀ : Nat → V) (Fss Ess Fss₀ : List (List AnnotTerm))
    (Ids : List AnnotTerm) (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) : Prop where
  hyp : RecHypI ℓ w ρ₀ Fss Ess Ids
    (fun is => SetTheory.app
      (fixFamI u w (frP Fss.length Ids.length ρ₀) Ids Ids.length rss tlss Eiss Fss₀ Ess) (tupW u is))
    (ihDomsI ℓ (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀) rss tlss Eiss
      (fun j => (Fss.getD j []).length))
  hX : XChainsOk u w (frP Fss.length Ids.length ρ₀) Ids rss tlss Eiss Fss₀ Ess
  hreal : ChainsRealI (fixFamI u w (frP Fss.length Ids.length ρ₀) Ids Ids.length rss tlss Eiss Fss₀ Ess)
    u w (frP Fss.length Ids.length ρ₀) Ids rss tlss Eiss Fss₀ Fss Ess
  /-- the squash regime (`Prop`-valued family, large eliminator; task
  #202 A2): at most one constructor (none at all since task #210 Part
  B: the family is then empty and every clause below is vacuous), and
  every field not sourced by an index expression is a `Prop` (the
  kernel's subsingleton criterion) -/
  hsq : w = 0 → ℓ ≠ 0 → Fss.length ≤ 1 ∧
    FieldsOkB 0 (frP Fss.length Ids.length ρ₀) (Fss.getD 0 []) ∧
    ∀ j, j < (Fss.getD 0 []).length → srcOfEs (Ess.getD 0 []) (Fss.getD 0 []).length j = none →
      ∀ fs : List V, SpineFit (frP Fss.length Ids.length ρ₀) ((Fss.getD 0 []).take j) fs →
        interp V (consList fs (frP Fss.length Ids.length ρ₀)) ((Fss.getD 0 []).getD j default)
          ∈ˢ (univZero : V)

/-- `FixKI₀` plus the unfolded function's typing at the recursor's type
(a closed Π-tower over the binder data `rds`, read at the frame below
the function) with the spine-fit of the ih application and the
conclusion's zero-level condition. -/
structure FixKI (ℓ w u nP : Nat) (ρ₀ : Nat → V) (Fss Ess Fss₀ : List (List AnnotTerm))
    (Ids : List AnnotTerm) (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm)))
    (rds : List (Nat × Nat × AnnotTerm)) : Prop
    extends FixKI₀ ℓ w u ρ₀ Fss Ess Fss₀ Ids rss tlss Eiss where
  hz : ∀ d ∈ rds, (ℓ = 0 ↔ d.2.1 = 0)
  hrV : frR nP Fss.length Ids.length ρ₀
    ∈ˢ interp V (cons (frR nP Fss.length Ids.length ρ₀) (frBelow nP Fss.length Ids.length ρ₀))
      (mkPisAV rds (recConcAV Fss.length Ids.length))
  hspine : ∀ (vals : List V) (f : V), SpineFit (frP Fss.length Ids.length ρ₀) Ids vals →
    f ∈ˢ SetTheory.app
      (fixFamI u w (frP Fss.length Ids.length ρ₀) Ids Ids.length rss tlss Eiss Fss₀ Ess) (tupW u vals) →
    SpineFit (cons (frR nP Fss.length Ids.length ρ₀) (frBelow nP Fss.length Ids.length ρ₀))
      (rds.map (·.2.2)) (frKSpine nP Fss.length Ids.length ρ₀ ++ vals ++ [f])
  hspineLen : rds.length = nP + 1 + Fss.length + Ids.length + 1
  hconc0 : ℓ = 0 → ∀ as', SpineFit (cons (frR nP Fss.length Ids.length ρ₀) (frBelow nP Fss.length Ids.length ρ₀))
    (rds.map (·.2.2)) as' →
    interp V (consList as' (cons (frR nP Fss.length Ids.length ρ₀) (frBelow nP Fss.length Ids.length ρ₀)))
      (recConcAV Fss.length Ids.length) ∈ˢ (univZero : V)

namespace FixKI

variable {ℓ w u nP : Nat} {ρ₀ : Nat → V} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {rds : List (Nat × Nat × AnnotTerm)}

/-- The block frame `(p⃗, M, m⃗)` over the function is the K-frame's
shift past the indices. -/
theorem block_frame (_h : FixKI ℓ w u nP ρ₀ Fss Ess Fss₀ Ids rss tlss Eiss rds) :
    consList (frKSpine nP Fss.length Ids.length ρ₀)
        (cons (frR nP Fss.length Ids.length ρ₀) (frBelow nP Fss.length Ids.length ρ₀))
      = shiftE Ids.length 0 ρ₀ := by
  have hk := consList_frKSpine nP Fss.length Ids.length ρ₀
  rw [consList_append] at hk
  have h := shiftE_consList (frameIdx Ids.length ρ₀)
    (consList (frKSpine nP Fss.length Ids.length ρ₀)
      (cons (frR nP Fss.length Ids.length ρ₀) (frBelow nP Fss.length Ids.length ρ₀)))
  rw [frameIdx_length, hk] at h
  exact h.symm

/-- The conclusion at a spine frame is the motive at the index values
at the major. -/
theorem conc_at (h : FixKI ℓ w u nP ρ₀ Fss Ess Fss₀ Ids rss tlss Eiss rds) {vals : List V}
    (hlen : vals.length = Ids.length) (f : V) :
    interp V (consList (frKSpine nP Fss.length Ids.length ρ₀ ++ vals ++ [f])
        (cons (frR nP Fss.length Ids.length ρ₀) (frBelow nP Fss.length Ids.length ρ₀)))
        (recConcAV Fss.length Ids.length)
      = SetTheory.app (vals.foldl SetTheory.app (frM Fss.length Ids.length ρ₀)) f := by
  rw [consList_append, consList_append]
  have := recConcAV_at (n := Fss.length) (nIdx := Ids.length)
    (ρ₁ := consList (frKSpine nP Fss.length Ids.length ρ₀)
      (cons (frR nP Fss.length Ids.length ρ₀) (frBelow nP Fss.length Ids.length ρ₀))) vals hlen f
  show interp V (cons f _) _ = _
  rw [this, h.block_frame, shiftE_zero]
  unfold frM
  show SetTheory.app (vals.foldl SetTheory.app (ρ₀ (Fss.length + Ids.length))) f = _
  rw [Nat.add_comm]

/-- The membership of the function's application at a fitting spine
in the conclusion. -/
theorem app_mem (h : FixKI ℓ w u nP ρ₀ Fss Ess Fss₀ Ids rss tlss Eiss rds) {vals : List V}
    (hsp : SpineFit (frP Fss.length Ids.length ρ₀) Ids vals) {f : V}
    (hf : f ∈ˢ SetTheory.app
      (fixFamI u w (frP Fss.length Ids.length ρ₀) Ids Ids.length rss tlss Eiss Fss₀ Ess) (tupW u vals)) :
    (frKSpine nP Fss.length Ids.length ρ₀ ++ vals ++ [f]).foldl SetTheory.app
        (frR nP Fss.length Ids.length ρ₀)
      ∈ˢ SetTheory.app (vals.foldl SetTheory.app (frM Fss.length Ids.length ρ₀)) f := by
  have := mkPisAV_fold_mem h.hz h.hconc0 h.hrV (h.hspine vals f hsp hf)
  rwa [h.conc_at hsp.length_eq f] at this

/-- The application chain of the function at a fitting spine is
graded. -/
theorem app_chain (h : FixKI ℓ w u nP ρ₀ Fss Ess Fss₀ Ids rss tlss Eiss rds) {vals : List V}
    (hsp : SpineFit (frP Fss.length Ids.length ρ₀) Ids vals) {f : V}
    (hf : f ∈ˢ SetTheory.app
      (fixFamI u w (frP Fss.length Ids.length ρ₀) Ids Ids.length rss tlss Eiss Fss₀ Ess) (tupW u vals)) :
    AppChainOk (frR nP Fss.length Ids.length ρ₀) (frKSpine nP Fss.length Ids.length ρ₀ ++ vals ++ [f]) :=
  appChainOk_of_mkPisAV' h.hz h.hconc0 h.hrV (h.hspine vals f hsp hf)

/-- The `l`-th value of a fitting spine is in the `l`-th domain at the
prefix. -/
theorem spineFit_getD_mem' {ρ : Nat → V} :
    ∀ {Fs : List AnnotTerm} {as : List V} {l : Nat}, SpineFit ρ Fs as → l < Fs.length →
      as.getD l pt ∈ˢ interp V (consList (as.take l) ρ) (Fs.getD l default)
  | [], _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | _ :: _, [], _, h, _ => h.elim
  | F :: Fs, a :: as, 0, h, _ => by simpa using h.1
  | F :: Fs, a :: as, l + 1, h, hl => by
    simp only [List.getD_cons_succ, List.take_succ_cons, consList_cons]
    exact spineFit_getD_mem' (Fs := Fs) (as := as) (l := l) h.2 (by simpa using hl)

end FixKI

/-! ## The rank recursion -/

open Classical in
/-- The numeral of a tag (junk off `ω`). -/
noncomputable def natIdx (k : V) : Nat :=
  if h : ∃ i, k = vnat i then Classical.choose h else 0

theorem natIdx_vnat (i : Nat) : natIdx (vnat i : V) = i := by
  unfold natIdx
  rw [dif_pos ⟨i, rfl⟩]
  exact (vnat_inj (Classical.choose_spec (⟨i, rfl⟩ : ∃ i', (vnat i : V) = vnat i'))).symm

/-- The semantic fold of a minor-space member along a fitting spine. -/
theorem minorSpI_fold {ℓ : Nat} {c : List V → V} (hc0 : ℓ = 0 → ∀ acc, c acc ∈ˢ (univZero : V)) :
    ∀ {Fs : List AnnotTerm} {ρf : Nat → V} {acc : List V} {m : V} {as : List V},
      m ∈ˢ minorSpI ℓ c Fs ρf acc → SpineFit ρf Fs as →
      as.foldl SetTheory.app m ∈ˢ c (acc ++ as)
  | [], _, acc, m, [], hm, _ => by simpa [minorSpI] using hm
  | [], _, _, _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, _, _, [], _, hsp => hsp.elim
  | F :: Fs, ρf, acc, m, a :: as, hm, hsp => by
    have happ : SetTheory.app m a ∈ˢ minorSpI ℓ c Fs (cons a ρf) (acc ++ [a]) :=
      app_mem_piR hm hsp.1 (fun h0 x _ => minorSpI_zero_univZero h0 (hc0 h0) Fs (cons x ρf) (acc ++ [x]))
    have := minorSpI_fold hc0 (Fs := Fs) (as := as) happ hsp.2
    rw [List.append_assoc, List.singleton_append] at this
    rw [List.foldl_cons]
    exact this

section KRec

variable {ℓ w u : Nat} {K : Nat → V} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}

/-- The family at a K-frame. -/
noncomputable def famK (u w : Nat) (K : Nat → V) (Fss Ess Fss₀ : List (List AnnotTerm))
    (Ids : List AnnotTerm) (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) : V :=
  fixFamI u w (frP Fss.length Ids.length K) Ids Ids.length rss tlss Eiss Fss₀ Ess

end KRec

/-! ## Closed binder data at any bottom -/

/-- A term closed at depth `k` reads the same at any two frames
agreeing below `k`. -/
theorem interp_closed_bottom {e : AnnotTerm} {k : Nat} (hcl : Term.bvarsBelow k e.erase)
    {as : List V} (hlen : as.length = k) (ρ₁ ρ₂ : Nat → V) :
    interp V (consList as ρ₁) e = interp V (consList as ρ₂) e :=
  interp_congr_noBVar e (NoBVar_of_bvarsBelow hcl fun _ hi => hlen ▸ hi)
    (agreeOff_consList_ge as ρ₁ ρ₂)

/-- A spine fits closed binder data at any bottom. -/
theorem spineFit_closed_bottom :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {as bs : List V} {ρ₁ ρ₂ : Nat → V},
      (∀ k d, ds[k]? = some d → Term.bvarsBelow (as.length + k) d.2.2.erase) →
      SpineFit (consList as ρ₁) (ds.map (·.2.2)) bs → SpineFit (consList as ρ₂) (ds.map (·.2.2)) bs
  | [], _, [], _, _, _, h => h
  | [], _, _ :: _, _, _, _, h => h.elim
  | _ :: _, _, [], _, _, _, h => h.elim
  | d :: ds, as, b :: bs, ρ₁, ρ₂, hcl, h => by
    refine ⟨?_, ?_⟩
    · have := h.1
      rwa [interp_closed_bottom (by simpa using hcl 0 d rfl) (as := as) rfl ρ₁ ρ₂] at this
    · have h2 := h.2
      rw [consList_snoc'] at h2 ⊢
      refine spineFit_closed_bottom (as := as ++ [b]) ?_ h2
      intro k d' hd'
      have := hcl (k + 1) d' (by simpa using hd')
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- The Π-tower over closed binder data reads the same at any bottom. -/
theorem mkPisAV_closed_bottom {C : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {as : List V} {ρ₁ ρ₂ : Nat → V},
      (∀ k d, ds[k]? = some d → Term.bvarsBelow (as.length + k) d.2.2.erase) →
      Term.bvarsBelow (as.length + ds.length) C.erase →
      interp V (consList as ρ₁) (mkPisAV ds C) = interp V (consList as ρ₂) (mkPisAV ds C)
  | [], as, ρ₁, ρ₂, _, hC => by
    show interp V (consList as ρ₁) C = interp V (consList as ρ₂) C
    exact interp_closed_bottom (by simpa using hC) rfl ρ₁ ρ₂
  | d :: ds, as, ρ₁, ρ₂, hcl, hC => by
    show piR d.2.1 (interp V (consList as ρ₁) d.2.2) (fun a => interp V (cons a (consList as ρ₁)) (mkPisAV ds C))
      = piR d.2.1 (interp V (consList as ρ₂) d.2.2) (fun a => interp V (cons a (consList as ρ₂)) (mkPisAV ds C))
    rw [interp_closed_bottom (by simpa using hcl 0 d rfl) (as := as) rfl ρ₁ ρ₂]
    refine piR_congr fun a _ => ?_
    rw [consList_snoc', consList_snoc']
    refine mkPisAV_closed_bottom (as := as ++ [a]) ?_ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hC)
    intro k d' hd'
    have := hcl (k + 1) d' (by simpa using hd')
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-! ## The spelled recursor -/

/-- The recursor's type, spelled: the Π-tower over its binder data
ending in `M ı⃗ t`. -/
def recTyAV (n nIdx : Nat) (rds : List (Nat × Nat × AnnotTerm)) : AnnotTerm :=
  mkPisAV rds (recConcAV n nIdx)

/-- The recursor body under the major, at depth `1` below the K-frame:
the case split with the ih arguments (graph regime); at a squash
instantiation the point (small eliminator) or the squash regime's body
(`sqFixBodyAV`: the minor at the fields read off the indices, task
#202 A2). -/
def fixRecBodyAVI (ℓ w nP : Nat) (Fss Ess : List (List AnnotTerm)) (Ids : List AnnotTerm)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) : AnnotTerm :=
  if w = 0 then
    (if ℓ = 0 then .prf
     else sqFixBodyAV ℓ nP Fss.length Ids.length (Fss.getD 0 []) (Ess.getD 0 []) (rss.getD 0 [])
       (tlss.getD 0 []) (Eiss.getD 0 []))
  else .app (caseRecAVI ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
      (fun j => (Fss.getD j []).length)
      (ihArgsI ℓ nP Fss.length Ids.length rss tlss Eiss (fun j => (Fss.getD j []).length))
      Fss.length Ids.length Fss.length 1 0 (.fst (.bvar 0)))
    (.snd (.bvar 0))

theorem fixRecBodyAVI_zero {ℓ : Nat} (h0 : ℓ = 0) (nP : Nat) (Fss Ess : List (List AnnotTerm)) (Ids : List AnnotTerm)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) :
    fixRecBodyAVI ℓ 0 nP Fss Ess Ids rss tlss Eiss = .prf := by
  unfold fixRecBodyAVI; rw [if_pos rfl, if_pos h0]

theorem fixRecBodyAVI_sq {ℓ : Nat} (hℓ : ℓ ≠ 0) (nP : Nat) (Fss Ess : List (List AnnotTerm)) (Ids : List AnnotTerm)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) :
    fixRecBodyAVI ℓ 0 nP Fss Ess Ids rss tlss Eiss
      = sqFixBodyAV ℓ nP Fss.length Ids.length (Fss.getD 0 []) (Ess.getD 0 []) (rss.getD 0 [])
          (tlss.getD 0 []) (Eiss.getD 0 []) := by
  unfold fixRecBodyAVI; rw [if_pos rfl, if_neg hℓ]

theorem fixRecBodyAVI_pos {w : Nat} (hw : w ≠ 0) (ℓ nP : Nat) (Fss Ess : List (List AnnotTerm))
    (Ids : List AnnotTerm) (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) :
    fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss
      = .app (caseRecAVI ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          (fun j => (Fss.getD j []).length)
          (ihArgsI ℓ nP Fss.length Ids.length rss tlss Eiss (fun j => (Fss.getD j []).length))
          Fss.length Ids.length Fss.length 1 0 (.fst (.bvar 0)))
        (.snd (.bvar 0)) := if_neg hw

/-- The one-step unfolding `λ r. λ p⃗ M m⃗ ı⃗ t. body`. -/
def fixStepAVI (ℓ w nP : Nat) (Fss Ess : List (List AnnotTerm)) (Ids : List AnnotTerm)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (rds : List (Nat × Nat × AnnotTerm)) (s : Nat) :
    AnnotTerm :=
  .lam (s) (recTyAV Fss.length Ids.length rds)
    (mkLamsC ℓ rds (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss))

/-- `Σ' (r : RecTy), Step r = r`. -/
def fixSigAVI (ℓ w nP : Nat) (Fss Ess : List (List AnnotTerm)) (Ids : List AnnotTerm)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (rds : List (Nat × Nat × AnnotTerm)) (s : Nat) :
    AnnotTerm :=
  AnnotTerm.mkAppN (.const .psigma [s, 0]) [recTyAV Fss.length Ids.length rds,
    .lam 1 (recTyAV Fss.length Ids.length rds)
      (.eqE
        (.app ((fixStepAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s).liftN 1 0) (.bvar 0)) (.bvar 0))]

/-- The selected fixed point `(choice Σ prf).1` — **the recursor leaf**
(a closed term). -/
def fixSelAVI (ℓ w nP : Nat) (Fss Ess : List (List AnnotTerm)) (Ids : List AnnotTerm)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (rds : List (Nat × Nat × AnnotTerm)) (s : Nat) :
    AnnotTerm :=
  .fst (AnnotTerm.mkAppN (.const .choice [s])
    [fixSigAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s, .prf])

/-! ## The premise -/

/-- The domains of binder data graded along every fitting walk. -/
def DomsWalk : (Nat → V) → List (Nat × Nat × AnnotTerm) → Prop
  | _, [] => True
  | ρ, d :: ds => WellDenoted V ρ d.2.2 ∧ ∀ a, a ∈ˢ interp V ρ d.2.2 → DomsWalk (cons a ρ) ds

/-- `UnderTowerOk` from the domain walk and the base facts at every
fitting leaf. -/
theorem underTowerOk_of_walk {m : Nat} {b C : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      DomsWalk ρ ds →
      (∀ as, SpineFit ρ (ds.map (·.2.2)) as →
        WellDenoted V (consList as ρ) b ∧ interp V (consList as ρ) b ∈ˢ interp V (consList as ρ) C ∧
        (m = 0 → interp V (consList as ρ) C ∈ˢ (univZero : V))) →
      UnderTowerOk m ρ b C ds
  | [], ρ, _, hb => by
    have := hb [] trivial
    simp only [consList_nil] at this
    exact this
  | d :: ds, ρ, hw, hb => by
    refine ⟨hw.1, fun a ha => underTowerOk_of_walk (hw.2 a ha) fun as hsp => ?_⟩
    have := hb (a :: as) ⟨ha, hsp⟩
    rwa [consList_cons] at this

/-- **The recursor's premise** — frame-generic (every field holds at
every bottom frame `ρb`): the binder data's bits zero-agree with the
elimination level, the data are closed, the domains are graded along
every walk, at every K-frame reached the case split's package holds
and the major's domain reads to the carrier at the frame's index tuple,
the index and major binders admit the ih spine, the conclusion is a
truth value at level zero, and the recursor's type reads to a graded
member of its sort's universe. -/
structure FixPre (V : Type uv) [SetTheory V] (ℓ w u nP : Nat) (Fss Ess Fss₀ : List (List AnnotTerm)) (Ids : List AnnotTerm)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) (rds : List (Nat × Nat × AnnotTerm)) (s : Nat) :
    Prop where
  hz : ∀ d ∈ rds, (ℓ = 0 ↔ d.2.1 = 0)
  hlen : rds.length = nP + 1 + Fss.length + Ids.length + 1
  hclosed : ∀ k d, rds[k]? = some d → Term.bvarsBelow k d.2.2.erase
  hs0 : s = 0 ↔ ℓ = 0
  hdoms : ∀ ρb : Nat → V, DomsWalk ρb rds
  hK : ∀ (ρb : Nat → V) (as : List V) (t : V), SpineFit ρb (rds.map (·.2.2)) (as ++ [t]) →
    FixKI₀ ℓ w u (consList as ρb) Fss Ess Fss₀ Ids rss tlss Eiss ∧
    t ∈ˢ SetTheory.app (famK u w (consList as ρb) Fss Ess Fss₀ Ids rss tlss Eiss)
      (tupW u (frameIdx Ids.length (consList as ρb)))
  hspine : ∀ (ρb : Nat → V) (as : List V), SpineFit ρb ((rds.take (nP + 1 + Fss.length)).map (·.2.2)) as →
    ∀ (vals : List V) (f : V), SpineFit (shiftE (Fss.length + 1) 0 (consList as ρb)) Ids vals →
    f ∈ˢ SetTheory.app
      (fixFamI u w (shiftE (Fss.length + 1) 0 (consList as ρb)) Ids Ids.length rss tlss Eiss Fss₀ Ess)
      (tupW u vals) →
    SpineFit ρb (rds.map (·.2.2)) (as ++ vals ++ [f])
  hconc0 : ℓ = 0 → ∀ (ρb : Nat → V) (as' : List V), SpineFit ρb (rds.map (·.2.2)) as' →
    interp V (consList as' ρb) (recConcAV Fss.length Ids.length) ∈ˢ (univZero : V)
  hRecTy : ∀ ρb : Nat → V,
    interp V ρb (recTyAV Fss.length Ids.length rds) ∈ˢ (univ (s) : V) ∧
    WellDenoted V ρb (recTyAV Fss.length Ids.length rds)
  hEbelow : ∀ j i, ∀ E ∈ (Eiss.getD j []).getD i [],
    Term.bvarsBelow (nP + i + ((tlss.getD j []).getD i []).length) E.erase
  /-- the recursive fields' telescopes are scoped at the field's frame (task #202) -/
  hTbelow : ∀ j i, DomsBelow (nP + i) ((tlss.getD j []).getD i [])

/-! ## K-frames of the walk -/

section WalkFrames

variable {u w : Nat} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm} {rss : List (List Bool)}
  {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}

omit [SetTheory V] in
/-- The K-frame of a leaf frame. -/
theorem shiftE_leaf (as : List V) (t : V) (ρb : Nat → V) :
    shiftE 1 0 (consList (as ++ [t]) ρb) = consList as ρb := by
  rw [← consList_snoc', show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]

omit [SetTheory V] in
/-- The function slot of a K-frame `(ρb, r, p⃗, M, m⃗, ı⃗)`. -/
theorem frR_of (nP n nIdx : Nat) {as : List V} (hlen : as.length = nP + 1 + n + nIdx) (r : V)
    (ρb : Nat → V) : frR nP n nIdx (consList as (cons r ρb)) = r := by
  unfold frR frP
  rw [shiftE_zero]
  show consList as (cons r ρb) (nP + (nIdx + n + 1)) = r
  have := consList_apply_add as (cons r ρb) 0
  rw [Nat.zero_add, hlen, show nP + 1 + n + nIdx = nP + (nIdx + n + 1) from by omega] at this
  rw [this]; rfl

omit [SetTheory V] in
/-- The frame below the function slot. -/
theorem frBelow_of (nP n nIdx : Nat) {as : List V} (hlen : as.length = nP + 1 + n + nIdx) (r : V)
    (ρb : Nat → V) : frBelow nP n nIdx (consList as (cons r ρb)) = ρb := by
  unfold frBelow
  rw [show nIdx + n + 1 + nP + 1 = as.length + 1 from by omega, shiftE_consList_add,
    shiftE_succ_cons, shiftE_zero_zero]

omit [SetTheory V] in
/-- The parameter frame of a K-frame over a bottom: the bottom under
the parameters, i.e. the shift of the block frame past the motive and
the minors. -/
theorem frP_of (n nIdx : Nat) {as is : List V} (hlen : is.length = nIdx) (ρb : Nat → V) :
    frP n nIdx (consList (as ++ is) ρb) = shiftE (n + 1) 0 (consList as ρb) := by
  unfold frP
  rw [consList_append, show nIdx + n + 1 = is.length + (n + 1) from by omega, shiftE_consList_add]

omit [SetTheory V] in
/-- The block spine of a K-frame over a bottom. -/
theorem frKSpine_of (nP n nIdx : Nat) {as is : List V} (hlen : as.length = nP + 1 + n)
    (hilen : is.length = nIdx) (ρb : Nat → V) :
    frKSpine nP n nIdx (consList (as ++ is) ρb) = as := by
  unfold frKSpine
  rw [consList_append, ← hilen, shiftE_consList, ← hlen]
  exact frameIdx_consList' as ρb

omit [SetTheory V] in
/-- The index tuple of a K-frame over a bottom. -/
theorem frameIdx_of (nIdx : Nat) {as is : List V} (hilen : is.length = nIdx) (ρb : Nat → V) :
    frameIdx nIdx (consList (as ++ is) ρb) = is := by
  rw [consList_append, ← hilen]
  exact frameIdx_consList' is _

omit [SetTheory V] in
/-- The minors of a K-frame over a bottom depend on the block only. -/
theorem frMs_of (n nIdx : Nat) {as is : List V} (hilen : is.length = nIdx) (ρb : Nat → V) {j : Nat}
    (hj : j < n) : frMs n nIdx (consList (as ++ is) ρb) j = consList as ρb (n - 1 - j) := by
  unfold frMs
  rw [consList_append, show nIdx + n - 1 - j = (n - 1 - j) + is.length from by omega,
    consList_apply_add]

omit [SetTheory V] in
theorem frM_of (n nIdx : Nat) {as is : List V} (hilen : is.length = nIdx) (ρb : Nat → V) :
    frM n nIdx (consList (as ++ is) ρb) = consList as ρb n := by
  unfold frM
  rw [consList_append, show nIdx + n = n + is.length from by omega, consList_apply_add]

/-- The fold of a semantic tower along a fitting spine (nonzero bit). -/
theorem lamTower_fold {m : Nat} (hm : m ≠ 0) {g : (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {bs : List V},
      SpineFit ρ (ds.map (·.2.2)) bs → bs.foldl SetTheory.app (lamTower m ρ ds g) = g (consList bs ρ)
  | [], _, [], _ => rfl
  | [], _, _ :: _, hsp => hsp.elim
  | _ :: _, _, [], hsp => hsp.elim
  | d :: ds, ρ, b :: bs, hsp => by
    show bs.foldl SetTheory.app (SetTheory.app (lamR m (interp V ρ d.2.2)
      fun a => lamTower m (cons a ρ) ds g) b) = _
    rw [app_lamR_pos hm hsp.1, consList_cons]
    exact lamTower_fold hm hsp.2

end WalkFrames

/-! ## The squash regime's stages -/

section KRecZero

variable {ℓ w u : Nat} {K : Nat → V} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}

theorem mem_piTele_zero {B : List V → V} :
    ∀ {k : Nat} {T : TeleS V k} {acc : List V} {x : V}, x ∈ˢ piTele 0 T B acc →
      ∀ as, FitsS T as → ∃ y, y ∈ˢ B (acc ++ as)
  | _, .nil, acc, x, hx, [], _ => ⟨x, by simpa [piTele] using hx⟩
  | _, .nil, _, _, _, _ :: _, hfit => hfit.elim
  | _, .cons _ _, _, _, _, [], hfit => hfit.elim
  | _, .cons A T, acc, x, hx, a :: as, hfit => by
    have hx' : x ∈ˢ piR 0 A (fun a => piTele 0 (T a) B (acc ++ [a])) := hx
    rw [piR_zero] at hx'
    obtain ⟨y, hy⟩ := (mem_truthVal.mp hx').1 a hfit.1
    have := mem_piTele_zero (T := T a) (acc := acc ++ [a]) hy as hfit.2
    simpa [List.append_assoc] using this

/-- A nested product at level `0` is inhabited when its body is under
every fitting spine. -/
theorem piTele_zero_inhab_of {B : List V → V} :
    ∀ {k : Nat} {T : TeleS V k} {acc : List V},
      (∀ as, FitsS T as → ∃ y, y ∈ˢ B (acc ++ as)) → ∃ z, z ∈ˢ piTele 0 T B acc
  | _, .nil, acc, h => by
    have := h [] trivial
    simpa [piTele] using this
  | _, .cons A T, acc, h => by
    refine ⟨pt, ?_⟩
    show pt ∈ˢ piR 0 A (fun a => piTele 0 (T a) B (acc ++ [a]))
    rw [piR_zero]
    refine mem_truthVal.mpr ⟨fun a ha => ?_, rfl⟩
    refine piTele_zero_inhab_of (T := T a) (acc := acc ++ [a]) fun as has => ?_
    have := h (a :: as) ⟨ha, has⟩
    simpa [List.append_assoc] using this

/-- A member of a slot's value at level `0` is the point. -/
theorem eq_pt_of_mem_slotSet_zero {u : Nat} {ρ : Nat → V} {tl : List (Nat × Nat × AnnotTerm)}
    {Eis : List AnnotTerm} {X : V} (hX : ∀ t, SetTheory.app X t ∈ˢ (univZero : V)) {f : V}
    (hf : f ∈ˢ slotSet 0 u ρ tl Eis X) : f = pt := by
  unfold slotSet at hf
  cases tl with
  | nil =>
    exact eq_pt_of_mem_univZero (hX _) hf
  | cons d tl =>
    change f ∈ˢ piR 0 _ _ at hf
    rw [piR_zero] at hf
    exact (mem_truthVal.mp hf).2

/-- **Inhabitation at a zero elimination level by lfp induction**
(squash regime, task #202): at a `Prop`-valued block whose recursive
fields may be reflexive, the motive is inhabited at every member of
the carrier — the property is closed under the functor: at a member
of constructor `j`'s tower over the X-chain at the family of members
satisfying it, the minor's ih tower is inhabited (every ih domain is,
pointwise under the field's telescope), so its conclusion is. -/
theorem famK_inhab_zero_ind (h : FixKI₀ ℓ 0 u K Fss Ess Fss₀ Ids rss tlss Eiss) (h0 : ℓ = 0) :
    ∀ (is : List V) (t : V), SpineFit (frP Fss.length Ids.length K) Ids is →
      t ∈ˢ SetTheory.app (famK u 0 K Fss Ess Fss₀ Ids rss tlss Eiss) (tupW u is) →
      ∃ y, y ∈ˢ SetTheory.app (is.foldl SetTheory.app (frM Fss.length Ids.length K)) t := by
  have hX := h.hX
  have hIds : IdxOk u (frP Fss.length Ids.length K) Ids := hX.hI
  obtain ⟨hl₀, hlE, hEs, hlenj, hc⟩ := h.hreal
  -- the property
  let P : V → V → Prop := fun i x => ∀ is, SpineFit (frP Fss.length Ids.length K) Ids is → i = tupW u is →
    ∃ y, y ∈ˢ SetTheory.app (is.foldl SetTheory.app (frM Fss.length Ids.length K)) x
  have hμS : fixFamI u 0 (frP Fss.length Ids.length K) Ids Ids.length rss tlss Eiss Fss₀ Ess ∈ˢ lfpFamSpace V 0 (idxSet u (frP Fss.length Ids.length K) Ids) := fixFamI_mem u 0 (frP Fss.length Ids.length K) Ids rss tlss Eiss Fss₀ Ess
  have hfibre : ∀ t', SetTheory.app (fixFamI u 0 (frP Fss.length Ids.length K) Ids Ids.length rss tlss Eiss Fss₀ Ess) t' ∈ˢ (univZero : V) := by
    intro t'
    by_cases ht' : t' ∈ˢ idxSet u (frP Fss.length Ids.length K) Ids
    · rw [lfpFamSpace_eq] at hμS
      have := famSpace_app hμS ht'
      rwa [univ_zero] at this
    · rw [lfpFamSpace_eq] at hμS
      rw [app_off_dom_piR_pos (Nat.succ_ne_zero 0) hμS ht']
      exact mem_univZero.mpr (empty_subset _)
  have hind := lfpFamSet_induction (w := 0) (I := idxSet u (frP Fss.length Ids.length K) Ids)
    (F := fixFunVI u 0 (frP Fss.length Ids.length K) Ids Ids.length rss tlss Eiss Fss₀ Ess) (fixFunVI_closed_exists hX)
    (fixFunVI_mono hX) P ?_
  · intro is t hsp ht
    exact hind (tupW u is) (tupW_mem hsp) t ht is hsp rfl
  intro i hi x hx is hsp hi'
  subst hi'
  -- the induction family
  let S := graph (fun i => sep (SetTheory.app (lfpFamSet 0 (idxSet u (frP Fss.length Ids.length K) Ids)
    (fixFunVI u 0 (frP Fss.length Ids.length K) Ids Ids.length rss tlss Eiss Fss₀ Ess)) i) (P i)) (idxSet u (frP Fss.length Ids.length K) Ids)
  have hSmem : S ∈ˢ lfpFamSpace V 0 (idxSet u (frP Fss.length Ids.length K) Ids) := by
    rw [lfpFamSpace_eq]
    refine graph_mem_famSpace fun i hi => ?_
    rw [univ_zero]
    exact mem_univZero.mpr fun z hz => mem_univZero.mp (hfibre i) z (mem_sep.mp hz).1
  have hSle : FamLe (idxSet u (frP Fss.length Ids.length K) Ids) S (fixFamI u 0 (frP Fss.length Ids.length K) Ids Ids.length rss tlss Eiss Fss₀ Ess) := by
    intro i hi y hy
    rw [app_graph hi] at hy
    exact (mem_sep.mp hy).1
  rw [fixFunVI_app hSmem, famFI_app (tupW_mem hsp)] at hx
  obtain ⟨rfl, j, fs, hj₀, hlen₀, hspX, hall⟩ := fixStepI_zero_elim hx
  have hj : j < Fss.length := hl₀ ▸ hj₀
  have hfit := hX.hfit S hSmem _ (tupW_mem hsp) j hj₀
  have hspR := spineFit_real_of_XI hIds hSle (Fss₀.getD j []) (Fss.getD j []) 0 [] fs rfl (hc j hj) hfit hspX
  have hlen : fs.length = (Fss.getD j []).length := by rw [hlen₀]; exact hlenj j hj
  have hidx : idxValsAt (frP Fss.length Ids.length K) (Ess.getD j []) fs = is := by
    rw [← hlen₀] at hall
    exact idxValsAt_of_eqsXI hIds hsp (hEs j hj) hall
  -- the minor's conclusion is inhabited once every ih domain is
  have hms := h.hyp.hms j hj
  rw [h0] at hms
  obtain ⟨x, hx⟩ := minorSpI_zero_inhab hms hspR
  rw [List.nil_append] at hx
  have := ihSpL_zero_inhab hx ?_
  · unfold concI ctorValI at this
    rwa [hidx, if_pos rfl] at this
  · intro A hA
    unfold ihDomsI at hA
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hA
    obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
    -- the field lies in the slot at the induction family
    have hslot := fitsXI_slot_mem hIds (Fss₀.getD j []) 0 [] fs rfl hfit hspX i (by rw [hlen]; simpa using hik)
      (by rw [Nat.zero_add]; exact hri)
    rw [Nat.zero_add, List.nil_append] at hslot
    obtain ⟨hf, hmem⟩ := hslot
    have hfpt : fs.getD i pt = pt := eq_pt_of_mem_slotSet_zero (fun t' => by
      by_cases ht' : t' ∈ˢ idxSet u (frP Fss.length Ids.length K) Ids
      · rw [app_graph ht']
        exact mem_univZero.mpr fun z hz => mem_univZero.mp (hfibre t') z (mem_sep.mp hz).1
      · rw [lfpFamSpace_eq] at hSmem
        rw [app_off_dom_piR_pos (Nat.succ_ne_zero 0) hSmem ht']
        exact mem_univZero.mpr (empty_subset _)) hmem
    refine piTele_zero_inhab_of fun as has => ?_
    have has' : SpineFit (consList (fs.take i) (frP Fss.length Ids.length K)) (((tlss.getD j []).getD i []).map (·.2.2)) as :=
      fitsS_teleOfFields.mp has
    obtain ⟨-, hvsp⟩ := hf.2.2 as has'
    unfold slotSet at hmem
    obtain ⟨z, hz⟩ := mem_piTele_zero hmem as has
    rw [List.nil_append, ← consList_append] at hz
    rw [app_graph (tupW_mem hvsp)] at hz
    obtain ⟨hzμ, hPz⟩ := mem_sep.mp hz
    have hzpt : z = pt := eq_pt_of_mem_univZero (hfibre _) hzμ
    obtain ⟨y, hy⟩ := hPz _ hvsp rfl
    refine ⟨y, ?_⟩
    simp only [List.nil_append]
    rw [hfpt, foldl_app_pt', ← consList_append, ← hzpt]
    exact hy

end KRecZero

/-! ## The recursor's semantics -/

section Rec

variable {ℓ w u nP s : Nat} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {rds : List (Nat × Nat × AnnotTerm)}

theorem recConcAV_below (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) :
    Term.bvarsBelow rds.length (recConcAV Fss.length Ids.length).erase := by
  have hlt : Ids.length + Fss.length < rds.length - 1 := by rw [h.hlen]; omega
  have := motAppAV_below (D' := 1) (K := rds.length - 1) hlt
  rw [show rds.length - 1 + 1 = rds.length from by rw [h.hlen]; omega] at this
  exact ⟨this, show 0 < rds.length by rw [h.hlen]; omega⟩

/-- The recursor type's reading is bottom-independent. -/
theorem recTy_bottom (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) (ρ₁ ρ₂ : Nat → V) :
    interp V ρ₁ (recTyAV Fss.length Ids.length rds) = interp V ρ₂ (recTyAV Fss.length Ids.length rds) := by
  unfold recTyAV
  have := mkPisAV_closed_bottom (C := recConcAV Fss.length Ids.length) (ds := rds) (as := [])
    (ρ₁ := ρ₁) (ρ₂ := ρ₂) (by simpa using h.hclosed) (by simpa using recConcAV_below h)
  simpa using this

theorem recSort_zero_iff (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) :
    s = 0 ↔ ℓ = 0 := h.hs0

/-- A spine fitting a chain fits a prefix of it. -/
theorem spineFit_prefix {ρ : Nat → V} {Ds : List AnnotTerm} {as bs : List V}
    (h : SpineFit ρ Ds (as ++ bs)) : SpineFit ρ (Ds.take as.length) as := by
  have hlen : (as ++ bs).length = Ds.length := h.length_eq
  have hsplit : Ds = Ds.take as.length ++ Ds.drop as.length := (List.take_append_drop _ _).symm
  rw [hsplit] at h
  obtain ⟨as₁, as₂, heq, h1, -⟩ := spineFit_append_split h
  have hl₁ : as₁.length = as.length := by
    rw [h1.length_eq, List.length_take]
    rw [List.length_append] at hlen
    omega
  obtain ⟨rfl, -⟩ := List.append_inj heq hl₁.symm
  exact h1

/-- The tower walk from the leaves. -/
theorem towerWalk_of_leaves {m : Nat} {C : AnnotTerm} {g : (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      (∀ bs, SpineFit ρ (ds.map (·.2.2)) bs →
        g (consList bs ρ) ∈ˢ interp V (consList bs ρ) C ∧ (m = 0 → interp V (consList bs ρ) C ∈ˢ (univZero : V))) →
      TowerWalk m C g ρ ds
  | [], ρ, hb => by
    have := hb [] trivial
    simp only [consList_nil] at this
    exact this
  | d :: ds, ρ, hb => fun a ha => towerWalk_of_leaves fun bs hsp => by
    have := hb (a :: bs) ⟨ha, hsp⟩
    rwa [consList_cons] at this

/-- The K-frame package with the function, at a walk K-frame over
`cons r ρb` with `r` in the recursor's type. -/
theorem fixKI_of (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s) (ρb : Nat → V) {r : V}
    (hr : r ∈ˢ interp V ρb (recTyAV Fss.length Ids.length rds)) {as : List V} {t : V}
    (hsp : SpineFit (cons r ρb) (rds.map (·.2.2)) (as ++ [t])) :
    FixKI ℓ w u nP (consList as (cons r ρb)) Fss Ess Fss₀ Ids rss tlss Eiss rds := by
  obtain ⟨h0, -⟩ := h.hK (cons r ρb) as t hsp
  have hlen_as : as.length = nP + 1 + Fss.length + Ids.length := by
    have := hsp.length_eq
    rw [List.length_append, List.length_singleton, List.length_map, h.hlen] at this
    omega
  obtain ⟨as₀, is, rfl, hl₀, hli⟩ : ∃ as₀ is, as = as₀ ++ is ∧ as₀.length = nP + 1 + Fss.length ∧
      is.length = Ids.length :=
    ⟨as.take (nP + 1 + Fss.length), as.drop (nP + 1 + Fss.length), (List.take_append_drop _ _).symm,
      by rw [List.length_take]; omega, by rw [List.length_drop]; omega⟩
  refine ⟨h0, h.hz, ?_, ?_, h.hlen, ?_⟩
  · rw [frR_of nP Fss.length Ids.length hlen_as, frBelow_of nP Fss.length Ids.length hlen_as]
    show r ∈ˢ interp V (cons r ρb) (recTyAV Fss.length Ids.length rds)
    rw [recTy_bottom h (cons r ρb) ρb]
    exact hr
  · intro vals f hv hf
    rw [frR_of nP Fss.length Ids.length hlen_as, frBelow_of nP Fss.length Ids.length hlen_as,
      frKSpine_of nP Fss.length Ids.length hl₀ hli]
    have hsp₀ : SpineFit (cons r ρb) ((rds.take (nP + 1 + Fss.length)).map (·.2.2)) as₀ := by
      have := spineFit_prefix (as := as₀) (bs := is ++ [t]) (by rw [← List.append_assoc]; exact hsp)
      rwa [hl₀, ← List.map_take] at this
    rw [frP_of Fss.length Ids.length hli] at hv hf
    exact h.hspine (cons r ρb) as₀ hsp₀ vals f hv hf
  · intro h0 as' hsp'
    rw [frR_of nP Fss.length Ids.length hlen_as, frBelow_of nP Fss.length Ids.length hlen_as] at hsp' ⊢
    exact h.hconc0 h0 (cons r ρb) as' hsp'

end Rec

end ConLeche.Semantics
