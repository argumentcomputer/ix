/-
  The area search computes the specification's search, part 5: the
  separation check. `sepCheckA` (reach labels over the area) equals
  `sepCheckL` (reach labels over the closure) (`sepCheckA_eq`).
-/
module

public import Ix.Sharing.Exact.AreaProof4
import all Ix.Sharing.Exact.Basic
import all Ix.Sharing.Exact.Dag
import all Ix.Sharing.Exact.Dictionary
import all Ix.Sharing.Exact.UniformSearch
import all Ix.Sharing.Exact.UniformSearchLocal
import all Ix.Sharing.Exact.AreaSearch
import all Ix.Sharing.Exact.AreaProof
import all Ix.Sharing.Exact.AreaProof2
import all Ix.Sharing.Exact.AreaProof3
import all Ix.Sharing.Exact.AreaProof4

public section

namespace Ix.Sharing.Exact.AreaProof

open Ix.Sharing.Exact
open Ix.Sharing.Exact.LocalSearch (PosFn)

/-! ## Folds and checks over arrays -/

theorem arr_foldl_congr {α β : Type} (a : Array α) (f g : β → α → β)
    (h : ∀ x ∈ a.toList, ∀ b, f b x = g b x) (init : β) : a.foldl f init = a.foldl g init := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  generalize a.toList = l at h
  induction l generalizing init with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [h x List.mem_cons_self]
    exact ih _ (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem arr_all_congr {α : Type} (a : Array α) (p q : α → Bool)
    (h : ∀ x ∈ a.toList, p x = q x) : a.all p = a.all q := by
  rw [← Array.all_toList, ← Array.all_toList]
  generalize a.toList = l at h
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.all_cons]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-! ## Local folds as fixed points -/

theorem localFold_entries {V : Type} [Inhabited V] (k : Nat) (xsAt : Nat → Nat)
    (G : Array V → Nat → Nat → V) (m : Nat) :
    (foldRange (fun L i => L.push (G L i (xsAt i))) 0 m (Array.mkEmpty k)).size = m ∧
      ∀ q, q < m → (foldRange (fun L i => L.push (G L i (xsAt i))) 0 m (Array.mkEmpty k))[q]! =
        G (foldRange (fun L i => L.push (G L i (xsAt i))) 0 q (Array.mkEmpty k)) q (xsAt q) := by
  induction m with
  | zero => exact ⟨by simp [Ix.Sharing.Exact.LocalSearch.foldRange_zero],
      fun q hq => absurd hq (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨s, he⟩ := ih
    rw [Ix.Sharing.Exact.LocalSearch.foldRange_succ, Nat.zero_add]
    refine ⟨by rw [Array.size_push, s], fun q hq => ?_⟩
    rw [push_read, s]
    by_cases hqm : q < m
    · rw [if_pos hqm]; exact he q hqm
    · have hq' : q = m := by omega
      subst hq'
      simp

theorem readAtF_some {α : Type} [Inhabited α] {posf : Nat → Option Nat} {L : Array α}
    {base : Nat → α} {u j : Nat} (hp : posf u = some j) (hj : j < L.size) :
    readAtF posf L id base u = L[j]! := by
  unfold readAtF; rw [hp]; simp [hj]

theorem readAtF_none {α : Type} [Inhabited α] {posf : Nat → Option Nat} {L : Array α}
    {base : Nat → α} {u : Nat} (hp : posf u = none) : readAtF posf L id base u = base u := by
  unfold readAtF; rw [hp]

/-- The reader of a local fold whose step reads only below the term is a
fixed point of the step at the fold's terms and the base elsewhere. -/
theorem localFold_fix {V : Type} [Inhabited V] (xs pos : Array Nat) (hinc : strictInc xs = true)
    (hpos : PosFn xs.size (xs[·]!) (posOf pos)) (base : Nat → V) (F : (Nat → V) → Nat → V)
    (hF : ∀ g g' t, InA xs t → (∀ u, u < t → g u = g' u) → F g t = F g' t) (t : Nat) :
    (InA xs t →
      readAtF (posOf pos) (localFold xs.size (xs[·]!)
        (fun L _ t => F (readAtF (posOf pos) L id base) t)) id base t =
      F (readAtF (posOf pos) (localFold xs.size (xs[·]!)
        (fun L _ t => F (readAtF (posOf pos) L id base) t)) id base) t) ∧
    (¬ InA xs t → readAtF (posOf pos) (localFold xs.size (xs[·]!)
        (fun L _ t => F (readAtF (posOf pos) L id base) t)) id base t = base t) := by
  have hL := localFold_entries xs.size (xs[·]!) (fun L _ t => F (readAtF (posOf pos) L id base) t)
  have hLk : localFold xs.size (xs[·]!) (fun L _ t => F (readAtF (posOf pos) L id base) t) =
      foldRange (fun L i => L.push (F (readAtF (posOf pos) L id base) xs[i]!)) 0 xs.size
        (Array.mkEmpty xs.size) := rfl
  rw [hLk]
  constructor
  · rintro ⟨j, hj, hjt⟩
    rw [readAtF_some ((hpos t j).mpr ⟨hj, hjt⟩) (by rw [(hL xs.size).1]; exact hj),
      (hL xs.size).2 j hj, hjt]
    apply hF _ _ t ⟨j, hj, hjt⟩
    intro u hu
    cases hp : posOf pos u with
    | none => rw [readAtF_none hp, readAtF_none hp]
    | some q =>
      obtain ⟨hq, hqu⟩ := (hpos u q).mp hp
      simp only at hqu
      have hqj : q < j := (strictInc_lt_iff hinc hq hj).mp (by rw [hqu, hjt]; exact hu)
      rw [readAtF_some hp (by rw [(hL j).1]; exact hqj),
        readAtF_some hp (by rw [(hL xs.size).1]; exact hq), (hL j).2 q hqj, (hL xs.size).2 q hq]
  · intro hn
    cases hp : posOf pos t with
    | none => exact readAtF_none hp
    | some q => exact absurd ⟨q, ((hpos t q).mp hp).1, ((hpos t q).mp hp).2⟩ hn

/-! ## Reach labels over the area -/

/-- The reach-label step at `t` from the labels `g` of the other terms. -/
def reachF (dag : Dag) (opq : Nat → Bool) (lab : Nat → Option Nat) (g : Nat → Option (Option Nat))
    (t : Nat) : Option (Option Nat) :=
  (dag.node t).children.foldl (fun v c => labelJoin v (if opq c then (lab c).map some else g c))
    ((lab t).map some)

theorem reachLabelsL_eq (dag : Dag) (xs pos : Array Nat) (opq : Nat → Bool)
    (lab : Nat → Option Nat) :
    reachLabelsL dag xs pos opq lab = localFold xs.size (xs[·]!)
      (fun L _ t => reachF dag opq lab (readAtF (posOf pos) L id (fun _ => none)) t) := by
  unfold reachLabelsL reachF
  rfl

theorem labelJoin_none_fold (l : List Nat) :
    l.foldl (fun v (_ : Nat) => labelJoin v none) none = none := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons]; exact ih

section Reach

variable {dag : Dag} (h : DagOK dag)

include h in
theorem reachF_congr (opq : Nat → Bool) (lab : Nat → Option Nat) (xs : Array Nat)
    (hlt : ∀ u, InA xs u → u < dag.size) (g g' : Nat → Option (Option Nat)) (t : Nat)
    (ht : InA xs t) (hg : ∀ u, u < t → g u = g' u) : reachF dag opq lab g t = reachF dag opq lab g' t := by
  unfold reachF
  apply arr_foldl_congr
  intro c hc b
  rw [hg c (h.child_lt (hlt t ht) (Array.mem_toList_iff.mp hc))]

include h in
/-- **Reach labels over the area.** With labels only on non-opaque area terms,
the area closed upward through its non-opaque terms and inside the closure,
the reach labels over the area agree with those over the closure at every area
term. -/
theorem reach_area (opq : Nat → Bool) (lab : Nat → Option Nat) (opaq : Nat → Bool)
    (area posA closure posC : Array Nat)
    (hincA : strictInc area = true) (hposA : PosFn area.size (area[·]!) (posOf posA))
    (hincC : strictInc closure = true) (hposC : PosFn closure.size (closure[·]!) (posOf posC))
    (hAlt : ∀ u, InA area u → u < dag.size) (hClt : ∀ u, InA closure u → u < dag.size)
    (hopq : ∀ u, opaq u = true → opq u = true)
    (hlab : ∀ u, lab u ≠ none → InA area u ∧ opaq u = false)
    (hclose : ∀ y q, InA area y → opaq y = false → q < dag.size →
      y ∈ (dag.node q).children → InA area q)
    (hAC : ∀ u, InA area u → InA closure u) (v : Nat) (hv : InA area v) :
    readAtF (posOf posC) (reachLabelsL dag closure posC opq lab) id (fun _ => none) v =
      readAtF (posOf posA) (reachLabelsL dag area posA opq lab) id (fun _ => none) v := by
  rw [reachLabelsL_eq, reachLabelsL_eq]
  have fixC := localFold_fix closure posC hincC hposC (fun _ => none) (reachF dag opq lab)
    (fun g g' t ht hg => reachF_congr h opq lab closure hClt g g' t ht hg)
  have fixA := localFold_fix area posA hincA hposA (fun _ => none) (reachF dag opq lab)
    (fun g g' t ht hg => reachF_congr h opq lab area hAlt g g' t ht hg)
  generalize readAtF (posOf posC) (localFold closure.size (closure[·]!)
    (fun L _ t => reachF dag opq lab (readAtF (posOf posC) L id (fun _ => none)) t)) id
    (fun _ => none) = Rc at fixC
  generalize readAtF (posOf posA) (localFold area.size (area[·]!)
    (fun L _ t => reachF dag opq lab (readAtF (posOf posA) L id (fun _ => none)) t)) id
    (fun _ => none) = Ra at fixA
  have key : ∀ u, (InA area u → Rc u = Ra u) ∧ (¬ InA area u → Rc u = none) := by
    intro u
    induction u using Nat.strongRecOn with
    | _ u ih =>
      constructor
      · intro hu
        rw [(fixC u).1 (hAC u hu), (fixA u).1 hu]
        unfold reachF
        apply arr_foldl_congr
        intro c hc b
        have hcu := h.child_lt (hAlt u hu) (Array.mem_toList_iff.mp hc)
        by_cases hoc : opq c = true
        · simp only [hoc, if_true]
        · simp only [hoc, Bool.false_eq_true, if_false]
          by_cases hca : InA area c
          · rw [(ih c hcu).1 hca]
          · rw [(ih c hcu).2 hca, (fixA c).2 hca]
      · intro hu
        by_cases huc : InA closure u
        · rw [(fixC u).1 huc]
          unfold reachF
          have hlu : lab u = none := by
            cases hl : lab u with
            | none => rfl
            | some k => exact absurd (hlab u (by rw [hl]; simp)).1 hu
          rw [hlu, Option.map_none]
          rw [arr_foldl_congr _ _ (fun v _ => labelJoin v none) ?_, ← Array.foldl_toList]
          · exact labelJoin_none_fold _
          · intro c hc b
            have hcm := Array.mem_toList_iff.mp hc
            have hcu := h.child_lt (hClt u huc) hcm
            by_cases hoc : opq c = true
            · simp only [hoc, if_true]
              have : lab c = none := by
                cases hl : lab c with
                | none => rfl
                | some k =>
                  obtain ⟨hca, hco⟩ := hlab c (by rw [hl]; simp)
                  exact absurd (hclose c u hca hco (hClt u huc) hcm) hu
              rw [this, Option.map_none]
            · simp only [hoc, Bool.false_eq_true, if_false]
              have hca : ¬ InA area c := by
                intro hca
                have hco : opaq c = false := by
                  cases hq : opaq c
                  · rfl
                  · exact absurd (hopq c hq) hoc
                exact hu (hclose c u hca hco (hClt u huc) hcm)
              rw [(ih c hcu).2 hca]
        · exact (fixC u).2 huc
  exact (key v).1 hv

include h in
/-- The separation check over the area and over the closure, with the
labels of `sepLab`. -/
theorem sep_core (members g inRed outRed : Array Nat) (opqR opaq : Nat → Bool)
    (area posA closure posC : Array Nat)
    (hincA : strictInc area = true) (hposA : PosFn area.size (area[·]!) (posOf posA))
    (hincC : strictInc closure = true) (hposC : PosFn closure.size (closure[·]!) (posOf posC))
    (hAlt : ∀ u, InA area u → u < dag.size) (hClt : ∀ u, InA closure u → u < dag.size)
    (hopq : ∀ u, opaq u = true → opqR u = true)
    (hmem : ∀ m, members.contains m = true → InA area m ∧ opaq m = false)
    (hclose : ∀ y q, InA area y → opaq y = false → q < dag.size →
      y ∈ (dag.node q).children → InA area q)
    (hAC : ∀ u, InA area u → InA closure u) :
    (g.all (fun t => (decide (t < dag.size) && members.contains t) &&
        sepLab dag.size members g inRed outRed t == some 1) &&
      members.all fun v => (decide (v < dag.size) && outRed.contains v) || opqR v ||
        readAtF (posOf posA) (reachLabelsL dag area posA opqR
          (sepLab dag.size members g inRed outRed)) id (fun _ => none) v != some none) =
    (g.all (fun t => (decide (t < dag.size) && members.contains t) &&
        sepLab dag.size members g inRed outRed t == some 1) &&
      members.all fun v => (decide (v < dag.size) && outRed.contains v) || opqR v ||
        readAtF (posOf posC) (reachLabelsL dag closure posC opqR
          (sepLab dag.size members g inRed outRed)) id (fun _ => none) v != some none) := by
  cases hG : g.all (fun t => (decide (t < dag.size) && members.contains t) &&
      sepLab dag.size members g inRed outRed t == some 1) with
  | false => rfl
  | true =>
    simp only [Bool.true_and]
    have hgm : ∀ u, g.contains u = true → members.contains u = true := by
      intro u hu
      have := Array.all_eq_true'.mp hG u (Array.contains_iff_mem.mp hu)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.2
    have hlab : ∀ u, sepLab dag.size members g inRed outRed u ≠ none → InA area u ∧ opaq u = false := by
      intro u hu
      apply hmem
      unfold sepLab at hu
      split at hu
      · split at hu
        · exact absurd rfl hu
        · split at hu
          · exact hgm u (by assumption)
          · split at hu
            · assumption
            · exact absurd rfl hu
      · exact absurd rfl hu
    apply arr_all_congr
    intro v hv
    have hvA := (hmem v (Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp hv))).1
    rw [reach_area h opqR _ opaq area posA closure posC hincA hposA hincC hposC hAlt hClt hopq
      hlab hclose hAC v hvA]

end Reach

/-- The light context of a component: its context without the closure. -/
abbrev lightCx (cx : SCtx) : SCtx := { cx with closure := #[], rootsC := #[], storedInC := #[] }

/-- **Separation check.** `sepCheckA` on the light context is `sepCheckL`. -/
theorem sepCheckA_eq {cx : SCtx} {posA posC : Array Nat}
    (hr : Ix.Sharing.Exact.LocalSearch.Ready cx posA posC) (hdag : DagOK cx.up.prep.dag)
    (hmem : ∀ m, cx.members.contains m = true → InA cx.area m ∧ cx.up.opaq[m]! = false)
    (hclose : ∀ y q, InA cx.area y → cx.up.opaq[y]! = false → q < cx.up.prep.dag.size →
      y ∈ (cx.up.prep.dag.node q).children → InA cx.area q)
    (hAC : ∀ y, InA cx.area y → InA cx.closure y) (g inRed outRed : Array Nat) :
    sepCheckA (lightCx cx) posA g inRed outRed = sepCheckL cx posA posC g inRed outRed := by
  obtain ⟨_, _, _, _, _, _, _, _, hareaLt, hclLt⟩ :=
    Ix.Sharing.Exact.LocalSearch.localSearchOK_spec hr.ok
  obtain ⟨hincA, hincC⟩ := Ix.Sharing.Exact.LocalSearch.localSearchOK_inc hr.ok
  unfold sepCheckA sepCheckL
  exact sep_core hdag cx.members g inRed outRed
    (fun t => opqArrR cx posA (reboundL cx posA outRed) inRed t) (cx.up.opaq[·]!)
    cx.area posA cx.closure posC hincA hr.area hincC hr.closure
    (fun u ⟨j, hj, hju⟩ => hju ▸ hareaLt j hj) (fun u ⟨j, hj, hju⟩ => hju ▸ hclLt j hj)
    (fun u hu => by unfold opqArrR; simp [hu]) hmem hclose hAC

/-- **The area search block** is the local search block, given the component
cost and the separation check. -/
theorem block_eq (cx : SCtx) (posA posC : Array Nat) (tb : TBase) (aux : AAux)
    (fb : Unit → SCtx × Array Nat) (limits : Limits)
    (hphi : ∀ avail stored, phiA (lightCx cx) posA tb aux fb avail stored =
      phiEL2 cx posA posC avail stored)
    (hsep : ∀ g i o, sepCheckA (lightCx cx) posA g i o = sepCheckL cx posA posC g i o) :
    ∀ fuel,
    (∀ g inAll outAll st, solvePA (lightCx cx) posA tb aux fb limits fuel g inAll outAll st =
      solvePL cx posA posC limits fuel g inAll outAll st) ∧
    (∀ g inRed outRed st, solveBodyA (lightCx cx) posA tb aux fb limits fuel g inRed outRed st =
      solveBodyL cx posA posC limits fuel g inRed outRed st) ∧
    (∀ phi0 inCtx outAll nOutCtx localIn und ct st,
      nodePA (lightCx cx) posA tb aux fb limits fuel phi0 inCtx outAll nOutCtx localIn und ct st =
        nodePL cx posA posC limits fuel phi0 inCtx outAll nOutCtx localIn und ct st) ∧
    (∀ inAll outAll grps comb st,
      splitPA (lightCx cx) posA tb aux fb limits fuel inAll outAll grps comb st =
        splitPL cx posA posC limits fuel inAll outAll grps comb st)
  | 0 => by
    refine ⟨fun _ _ _ _ => ?_, fun _ _ _ _ => ?_, fun _ _ _ _ _ _ _ _ => ?_,
      fun _ _ _ _ _ => ?_⟩
    · simp only [solvePA, solvePL]
    · simp only [solveBodyA, solveBodyL]
    · simp only [nodePA, nodePL]
    · simp only [splitPA, splitPL]
  | fuel + 1 => by
    obtain ⟨ihP, ihB, ihN, ihS⟩ := block_eq cx posA posC tb aux fb limits hphi hsep fuel
    refine ⟨fun g inAll outAll st => ?_, fun g inRed outRed st => ?_,
      fun phi0 inCtx outAll nOutCtx localIn und ct st => ?_,
      fun inAll outAll grps comb st => ?_⟩
    · simp only [solvePA, solvePL, hsep, ihB] <;> rfl
    · simp only [solveBodyA, solveBodyL, hphi, ihN] <;> rfl
    · simp only [nodePA, nodePL, hphi, ihN, ihS] <;> rfl
    · cases grps with
      | nil => simp only [splitPA, splitPL]
      | cons grp grps => simp only [splitPA, splitPL, ihP, ihS]

end Ix.Sharing.Exact.AreaProof

end
