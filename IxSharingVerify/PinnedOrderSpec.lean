import IxSharingVerify.UniformOptimizer
import Ix.Sharing.Exact.PinnedDeps
import IxC.Kernel.Audit.Axioms

/-!
# The pinned order lists stored descendants first

`pinnedOrder` orders a stored set so that every entry's nearest stored
descendants come before it: `pinnedDeps` walks down from each stored term
(a depth-first search with a visited set and the fuel `4 · n + 4`) and
`pinnedPlace` repeatedly places a remaining term whose walk results are all
placed. Materialization relies on this: an entry may only reference entries
before it.

* `walk_spec`: the walk stops with an empty stack within its fuel, returns
  only stored strict descendants, and returns every stored term reachable
  through unstored terms;
* `pinnedDeps_ok`: hence each stored term's dependencies are stored strict
  descendants, and every stored strict descendant is a dependency or lies
  below one;
* `pinnedOrder_backward`: in the pinned order every stored strict
  descendant of an entry comes before it.
-/

namespace Ix.Sharing.Verify.Pinned

open Ix.Sharing.Exact
open Ix.Sharing.Verify.SharingExact (Desc Below Desc.trans child_eq_getElem NodeArity)
open Ix.Sharing.Verify.UniformModel (DagWF dag_node_eq pinnedPick_mem pinnedPlace_perm
  pinnedOrder_perm toList_erase)

/-! ## The DAG -/

theorem node_children_out {dag : Dag} {t : Nat} (ht : ¬ t < dag.size) :
    (dag.node t).children.size = 0 := by
  have : dag.node t = default := by
    simp only [Dag.node, Array.getElem?_eq_none (Nat.le_of_not_lt ht), Option.getD_none]
  rw [this]
  rfl

theorem child_mem {dag : Dag} {t k : Nat} (hk : k < (dag.node t).children.size) :
    (dag.node t).child k ∈ (dag.node t).children := by
  rw [child_eq_getElem _ k hk]
  exact Array.getElem_mem hk

theorem desc_le {dag : Dag} (hwf : DagWF dag) {a b : Nat} (h : Desc dag a b) : b ≤ a := by
  induction h with
  | refl => exact Nat.le_refl _
  | @child t u k hk _ ih =>
    by_cases ht : t < dag.size
    · have := hwf.child_lt ht (child_mem hk)
      omega
    · rw [node_children_out ht] at hk
      omega

theorem below_lt {dag : Dag} (hwf : DagWF dag) {a b : Nat} (h : Below dag a b) : b < a := by
  obtain ⟨k, hk, d⟩ := h
  have le := desc_le hwf d
  by_cases ha : a < dag.size
  · have := hwf.child_lt ha (child_mem hk)
    omega
  · rw [node_children_out ha] at hk
    omega

theorem below_of_child {dag : Dag} {t c : Nat} (hc : c ∈ (dag.node t).children) : Below dag t c := by
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hc
  exact ⟨k, hk, by rw [child_eq_getElem _ k hk]; exact .refl _⟩

theorem below_trans_child {dag : Dag} {t u c : Nat} (h : Below dag t u)
    (hc : c ∈ (dag.node u).children) : Below dag t c := by
  obtain ⟨k, hk, d⟩ := h
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hc
  exact ⟨k, hk, Desc.trans d (.child j hj (by rw [child_eq_getElem _ j hj]; exact .refl _))⟩

theorem arity_le_three (h : Head) : h.arity ≤ 3 := by
  cases h <;> simp [Head.arity]

theorem children_le_three {dag : Dag} (hwf : DagWF dag) (t : Nat) :
    (dag.node t).children.size ≤ 3 := by
  by_cases ht : t < dag.size
  · have := hwf.arity t ht
    rw [← dag_node_eq ht] at this
    rw [this]
    exact arity_le_three _
  · rw [node_children_out ht]
    omega

/-! ## Unvisited terms -/

/-- Terms of the DAG not yet visited. -/
def unseen (n : Nat) (seen : Std.HashSet Nat) : Nat :=
  (List.range n).countP fun v => !seen.contains v

theorem countP_insert (seen : Std.HashSet Nat) (u : Nat) (fresh : seen.contains u = false) :
    ∀ (l : List Nat), u ∈ l → l.Nodup →
      l.countP (fun v => !(seen.insert u).contains v) + 1 = l.countP (fun v => !seen.contains v)
  | [], member, _ => by simp at member
  | x :: xs, member, nodup => by
    have xsNodup := (List.nodup_cons.mp nodup).2
    rw [List.countP_cons, List.countP_cons]
    by_cases hx : x = u
    · subst hx
      have outside : x ∉ xs := (List.nodup_cons.mp nodup).1
      have same : xs.countP (fun v => !(seen.insert x).contains v) =
          xs.countP (fun v => !seen.contains v) := by
        apply List.countP_congr
        intro v hv
        have ne : (x == v) = false := by
          rw [beq_eq_false_iff_ne]
          intro h
          subst h
          exact outside hv
        simp [Std.HashSet.contains_insert, ne]
      have h1 : (!(seen.insert x).contains x) = false := by simp [Std.HashSet.contains_insert]
      have h2 : (!seen.contains x) = true := by simp [fresh]
      rw [same, h1, h2]
      simp
    · have inner := countP_insert seen u fresh xs
        (by rcases List.mem_cons.mp member with h | h; exact absurd h.symm hx; exact h) xsNodup
      have ne : (u == x) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h => hx h.symm
      have same1 : (!(seen.insert u).contains x) = (!seen.contains x) := by
        simp [Std.HashSet.contains_insert, ne]
      rw [same1]
      omega

theorem unseen_insert (n : Nat) (seen : Std.HashSet Nat) (u : Nat) (hu : u < n)
    (fresh : seen.contains u = false) : unseen n (seen.insert u) + 1 = unseen n seen :=
  countP_insert seen u fresh (List.range n) (List.mem_range.mpr hu) List.nodup_range

theorem unseen_le (n : Nat) (seen : Std.HashSet Nat) : unseen n seen ≤ n := by
  unfold unseen
  exact Nat.le_trans (List.countP_le_length) (by simp)

/-! ## One walk -/

section Walk

variable (dag : Dag) (isStored : Array Bool) (t : Nat)

/-- The state of the walk from `t`. -/
structure WalkInv (seen : Std.HashSet Nat) (stack out : Array Nat) : Prop where
  stackOK : ∀ x ∈ stack.toList, x < dag.size ∧ Below dag t x
  seenOK : ∀ v, seen.contains v = true → v < dag.size ∧ Below dag t v
  outOK : ∀ v ∈ out.toList, isStored[v]! = true ∧ Below dag t v
  seenOut : ∀ v, seen.contains v = true → isStored[v]! = true → v ∈ out.toList
  start : ∀ c ∈ (dag.node t).children.toList, seen.contains c = true ∨ c ∈ stack.toList
  closed : ∀ v, seen.contains v = true → isStored[v]! = false →
    ∀ c ∈ (dag.node v).children.toList, seen.contains c = true ∨ c ∈ stack.toList

theorem walkInv_initial (hwf : DagWF dag) (ht : t < dag.size) :
    WalkInv dag isStored t ∅ (dag.node t).children #[] where
  stackOK := fun x hx => by
    have member := Array.mem_toList_iff.mp hx
    exact ⟨Nat.lt_trans (hwf.child_lt ht member) ht, below_of_child member⟩
  seenOK := fun v h => by simp at h
  outOK := fun v h => by simp at h
  seenOut := fun v h => by simp at h
  start := fun c hc => Or.inr hc
  closed := fun v h => by simp at h

/-- One step of the walk keeps its state invariant and lowers the measure
`stack.size + 3 · unseen`. -/
theorem walk_step (hwf : DagWF dag) {seen : Std.HashSet Nat} {stack out : Array Nat} {u : Nat}
    (inv : WalkInv dag isStored t seen stack out) (back : stack.back? = some u) :
    let next := if seen.contains u then (seen, stack.pop, out)
      else if isStored[u]! then (seen.insert u, stack.pop, out.push u)
      else (seen.insert u, stack.pop ++ (dag.node u).children, out)
    WalkInv dag isStored t next.1 next.2.1 next.2.2 ∧
      next.2.1.size + 3 * unseen dag.size next.1 + 1 ≤ stack.size + 3 * unseen dag.size seen := by
  obtain ⟨rest, rfl⟩ := Array.back?_eq_some_iff.mp back
  have uOK := inv.stackOK u (by simp)
  have popEq : (rest.push u).pop = rest := Array.pop_push
  have restSub : ∀ x ∈ rest.toList, x ∈ (rest.push u).toList := fun x hx => by simp [hx]
  have split : ∀ c, c ∈ (rest.push u).toList → c = u ∨ c ∈ rest.toList := by
    intro c hc
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hc
    rcases hc with h | h
    · exact Or.inr h
    · exact Or.inl h
  dsimp only
  rw [popEq]
  by_cases hs : seen.contains u = true
  · simp only [hs, ↓reduceIte]
    refine ⟨⟨fun x hx => inv.stackOK x (restSub x hx), inv.seenOK, inv.outOK, inv.seenOut, ?_, ?_⟩,
      by simp; omega⟩
    · intro c hc
      rcases inv.start c hc with h | h
      · exact Or.inl h
      · rcases split c h with rfl | h
        · exact Or.inl hs
        · exact Or.inr h
    · intro v hv hst c hc
      rcases inv.closed v hv hst c hc with h | h
      · exact Or.inl h
      · rcases split c h with rfl | h
        · exact Or.inl hs
        · exact Or.inr h
  · have fresh : seen.contains u = false := by simpa using hs
    have fewer := unseen_insert dag.size seen u uOK.1 fresh
    have covered : ∀ c, seen.contains c = true ∨ c ∈ (rest.push u).toList →
        (seen.insert u).contains c = true ∨ c ∈ rest.toList := by
      intro c h
      rcases h with h | h
      · exact Or.inl (by simp [Std.HashSet.contains_insert, h])
      · rcases split c h with rfl | h
        · exact Or.inl (by simp [Std.HashSet.contains_insert])
        · exact Or.inr h
    have seenNew : ∀ v, (seen.insert u).contains v = true → v = u ∨ seen.contains v = true := by
      intro v hv
      simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hv
      rcases hv with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    simp only [fresh, Bool.false_eq_true, ↓reduceIte]
    by_cases stored : isStored[u]! = true
    · simp only [stored, ↓reduceIte]
      refine ⟨⟨fun x hx => inv.stackOK x (restSub x hx), ?_, ?_, ?_, ?_, ?_⟩, by simp; omega⟩
      · intro v hv
        rcases seenNew v hv with rfl | h
        · exact uOK
        · exact inv.seenOK v h
      · intro v hv
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hv
        rcases hv with h | rfl
        · exact inv.outOK v h
        · exact ⟨stored, uOK.2⟩
      · intro v hv hst
        rcases seenNew v hv with rfl | h
        · simp
        · simp [inv.seenOut v h hst]
      · intro c hc
        exact covered c (inv.start c hc)
      · intro v hv hst c hc
        rcases seenNew v hv with rfl | h
        · rw [stored] at hst; cases hst
        · exact covered c (inv.closed v h hst c hc)
    · have unstored : isStored[u]! = false := by simpa using stored
      simp only [unstored, Bool.false_eq_true, ↓reduceIte]
      have childBound := children_le_three hwf u
      have covered' : ∀ c, seen.contains c = true ∨ c ∈ (rest.push u).toList →
          (seen.insert u).contains c = true ∨ c ∈ (rest ++ (dag.node u).children).toList := by
        intro c h
        rcases covered c h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])
      refine ⟨⟨?_, ?_, inv.outOK, ?_, ?_, ?_⟩, by simp; omega⟩
      · intro x hx
        simp only [Array.toList_append, List.mem_append] at hx
        rcases hx with h | h
        · exact inv.stackOK x (restSub x h)
        · have member := Array.mem_toList_iff.mp h
          exact ⟨Nat.lt_trans (hwf.child_lt uOK.1 member) uOK.1, below_trans_child uOK.2 member⟩
      · intro v hv
        rcases seenNew v hv with rfl | h
        · exact uOK
        · exact inv.seenOK v h
      · intro v hv hst
        rcases seenNew v hv with rfl | h
        · rw [unstored] at hst; cases hst
        · exact inv.seenOut v h hst
      · intro c hc
        exact covered' c (inv.start c hc)
      · intro v hv hst c hc
        rcases seenNew v hv with rfl | h
        · exact Or.inr (by simp [hc])
        · exact covered' c (inv.closed v h hst c hc)

/-- Within enough fuel the walk empties its stack, keeping its invariant. -/
theorem walk_spec (hwf : DagWF dag) :
    ∀ (fuel : Nat) (seen : Std.HashSet Nat) (stack out : Array Nat),
      WalkInv dag isStored t seen stack out → stack.size + 3 * unseen dag.size seen ≤ fuel →
      (pinnedWalkSpec dag isStored fuel seen stack out).2.1 = #[] ∧
        WalkInv dag isStored t (pinnedWalkSpec dag isStored fuel seen stack out).1
          (pinnedWalkSpec dag isStored fuel seen stack out).2.1
          (pinnedWalkSpec dag isStored fuel seen stack out).2.2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro seen stack out inv bound
    have empty : stack = #[] := Array.size_eq_zero_iff.mp (by omega)
    exact ⟨empty, inv⟩
  | succ fuel ih =>
    intro seen stack out inv bound
    cases back : stack.back? with
    | none =>
      have empty : stack = #[] := Array.back?_eq_none_iff.mp back
      simp only [pinnedWalkSpec, back, Option.elim_none]
      exact ⟨empty, inv⟩
    | some u =>
      obtain ⟨next, fewer⟩ := walk_step dag isStored t hwf inv back
      simp only [pinnedWalkSpec, back, Option.elim_some]
      by_cases hs : seen.contains u = true
      · simp only [hs, ↓reduceIte] at next fewer ⊢
        exact ih _ _ _ next (by omega)
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at next fewer ⊢
        split
        · rename_i stored
          simp only [stored, ↓reduceIte] at next fewer
          exact ih _ _ _ next (by omega)
        · rename_i stored
          simp only [stored, Bool.false_eq_true, ↓reduceIte] at next fewer
          exact ih _ _ _ next (by omega)

/-- Terms reachable from a child of `t` through unstored terms. -/
inductive Clean : Nat → Prop
  | start {c : Nat} : c ∈ (dag.node t).children → Clean c
  | step {v c : Nat} : Clean v → isStored[v]! = false → c ∈ (dag.node v).children → Clean c

theorem clean_seen {seen : Std.HashSet Nat} {out : Array Nat}
    (inv : WalkInv dag isStored t seen #[] out) {v : Nat} (h : Clean dag isStored t v) :
    seen.contains v = true := by
  induction h with
  | start hc =>
    rcases inv.start _ (Array.mem_toList_iff.mpr hc) with h | h
    · exact h
    · simp at h
  | step _ hst hc ih =>
    rcases inv.closed _ ih hst _ (Array.mem_toList_iff.mpr hc) with h | h
    · exact h
    · simp at h

/-- A stored strict descendant of `t` is reachable through unstored terms,
or lies below such a stored term. -/
theorem nearest_of_below {d : Nat} (stored : isStored[d]! = true) :
    ∀ {x : Nat}, Clean dag isStored t x → Desc dag x d →
      ∃ d', Clean dag isStored t d' ∧ isStored[d']! = true ∧ (d' = d ∨ Below dag d' d) := by
  intro x clean desc
  induction desc with
  | refl => exact ⟨_, clean, stored, Or.inl rfl⟩
  | @child y u k hk rest ih =>
    by_cases hy : isStored[y]! = true
    · exact ⟨y, clean, hy, Or.inr ⟨k, hk, rest⟩⟩
    · exact ih stored (Clean.step clean (by simpa using hy) (child_mem hk))

end Walk

/-! ## All walks -/

theorem foldl_insert_getD (F : Nat → Array Nat) :
    ∀ (l : List Nat) (m : Std.HashMap Nat (Array Nat)) (t : Nat),
      (l.foldl (fun deps s => deps.insert s (F s)) m).getD t #[] =
        if t ∈ l then F t else m.getD t #[]
  | [], m, t => by simp
  | s :: l, m, t => by
    simp only [List.foldl_cons]
    rw [foldl_insert_getD F l _ t, Std.HashMap.getD_insert]
    by_cases hl : t ∈ l
    · simp [hl]
    · by_cases hs : s = t
      · subst hs; simp
      · simp [hl, hs, Ne.symm hs]

/-- The membership flags of `pinnedDeps`. -/
theorem isStored_spec (n : Nat) (stored : List Nat) (hin : ∀ s ∈ stored, s < n) (u : Nat) :
    (stored.foldl (fun acc t => acc.set! t true) (Array.replicate n false))[u]! = true ↔
      u ∈ stored := by
  suffices h : ∀ (l : List Nat) (acc : Array Bool), acc.size = n → (∀ s ∈ l, s < n) →
      ((l.foldl (fun acc t => acc.set! t true) acc)[u]! = true ↔ u ∈ l ∨ acc[u]! = true) by
    rw [h stored _ (by simp) hin]
    by_cases hu : u < n
    · simp [getElem!_pos (Array.replicate n false) u (by simpa using hu)]
    · simp [getElem!_neg (Array.replicate n false) u (by simpa using hu)]
  intro l
  induction l with
  | nil => intro acc _ _; simp
  | cons x xs ih =>
    intro acc size bound
    simp only [List.foldl_cons]
    rw [ih _ (by simp [size]) (fun s hs => bound s (List.mem_cons_of_mem _ hs))]
    have hx := bound x List.mem_cons_self
    rw [Ix.Sharing.Verify.SharingExact.setBang_getElem!]
    by_cases hux : x = u
    · subst hux
      simp [size, hx]
    · simp [hux, Ne.symm hux]

/-- What `pinnedDeps` gives a stored term. -/
structure DepsOK (dag : Dag) (stored : List Nat) (deps : Std.HashMap Nat (Array Nat)) : Prop where
  sound : ∀ t ∈ stored, ∀ d ∈ (deps.getD t #[]).toList, d ∈ stored ∧ Below dag t d
  complete : ∀ t ∈ stored, ∀ d ∈ stored, Below dag t d →
    ∃ d' ∈ (deps.getD t #[]).toList, d' = d ∨ Below dag d' d

theorem pinnedDeps_ok {dag : Dag} (hwf : DagWF dag) (stored : Array Nat)
    (hin : ∀ s ∈ stored.toList, s < dag.size) :
    DepsOK dag stored.toList (pinnedDeps dag stored) := by
  rw [pinnedDeps_eq_alt, pinnedDepsAlt_eq_foldl, ← Array.foldl_toList]
  generalize hS : stored.foldl (fun acc t => acc.set! t true) (Array.replicate dag.size false) = isStored
  have flags : ∀ u, isStored[u]! = true ↔ u ∈ stored.toList := by
    intro u
    rw [← hS, ← Array.foldl_toList]
    exact isStored_spec dag.size stored.toList hin u
  have lookup := foldl_insert_getD (fun t => (pinnedWalkSpec dag isStored (4 * dag.size + 4) ∅
    (dag.node t).children #[]).2.2) stored.toList {}
  have walked : ∀ t ∈ stored.toList,
      let r := pinnedWalkSpec dag isStored (4 * dag.size + 4) ∅ (dag.node t).children #[]
      r.2.1 = #[] ∧ WalkInv dag isStored t r.1 r.2.1 r.2.2 := by
    intro t ht
    apply walk_spec dag isStored t hwf _ _ _ _ (walkInv_initial dag isStored t hwf (hin t ht))
    have := children_le_three hwf t
    have := unseen_le dag.size ∅
    omega
  constructor
  · intro t ht d hd
    rw [lookup t, ite_eq_left ht] at hd
    obtain ⟨_, inv⟩ := walked t ht
    obtain ⟨st, below⟩ := inv.outOK d hd
    exact ⟨(flags d).mp st, below⟩
  · intro t ht d hd below
    rw [lookup t, ite_eq_left ht]
    obtain ⟨empty, inv⟩ := walked t ht
    rw [empty] at inv
    obtain ⟨k, hk, desc⟩ := below
    obtain ⟨d', clean, st, close⟩ := nearest_of_below dag isStored t ((flags d).mpr hd)
      (Clean.start (child_mem hk)) desc
    exact ⟨d', inv.seenOut d' (clean_seen dag isStored t inv clean) st, close⟩

/-! ## Placement -/

/-- Each placed term has its dependencies placed before it. -/
def Respects (deps : Std.HashMap Nat (Array Nat)) (order : List Nat) : Prop :=
  ∀ k (hk : k < order.length), ∀ d ∈ (deps.getD order[k] #[]).toList,
    ∃ j, ∃ hj : j < k, order[j]'(by omega) = d

theorem respects_push {deps : Std.HashMap Nat (Array Nat)} {order : List Nat} {x : Nat}
    (h : Respects deps order) (ready : ∀ d ∈ (deps.getD x #[]).toList, d ∈ order) :
    Respects deps (order ++ [x]) := by
  intro k hk d hd
  by_cases old : k < order.length
  · rw [List.getElem_append_left old] at hd
    obtain ⟨j, hj, same⟩ := h k old d hd
    exact ⟨j, hj, by rw [List.getElem_append_left (by omega)]; exact same⟩
  · have last : k = order.length := by simp at hk; omega
    subst last
    rw [List.getElem_append_right (by omega)] at hd
    simp only [Nat.sub_self, List.getElem_cons_zero] at hd
    obtain ⟨j, hj, same⟩ := List.getElem_of_mem (ready d hd)
    exact ⟨j, hj, by rw [List.getElem_append_left hj]; exact same⟩

/-- A term is ready when every dependency is placed. -/
theorem ready_iff (deps : Std.HashMap Nat (Array Nat)) (placed : Std.HashSet Nat) (t : Nat) :
    (deps.getD t #[]).all placed.contains = true ↔
      ∀ d ∈ (deps.getD t #[]).toList, placed.contains d = true := by
  rw [Array.all_eq_true']
  simp only [Array.mem_toList_iff]

/-- The pick is a ready remaining term; there is none only if no remaining
term is ready. -/
theorem pinnedPick_cases (deg : Array Nat) (deps : Std.HashMap Nat (Array Nat))
    (placed : Std.HashSet Nat) (remaining : Array Nat) :
    (pinnedPick deg deps placed remaining = none →
        ∀ t ∈ remaining.toList, (deps.getD t #[]).all placed.contains = false) ∧
      ∀ p, pinnedPick deg deps placed remaining = some p →
        p ∈ remaining.toList ∧ (deps.getD p #[]).all placed.contains = true := by
  let g : Option Nat → Nat → Option Nat := fun acc t =>
    match acc with
    | none => some t
    | some a => if deg[t]! > deg[a]! || (deg[t]! == deg[a]! && t < a) then some t else acc
  have alwaysSome : ∀ (l : List Nat) (acc : Option Nat), l ≠ [] → (l.foldl g acc).isSome = true := by
    intro l
    induction l with
    | nil => intro _ h; exact absurd rfl h
    | cons x xs ih =>
      intro acc _
      simp only [List.foldl_cons]
      cases xs with
      | nil =>
        simp only [List.foldl_nil]
        cases acc with
        | none => rfl
        | some a => simp only [g]; split <;> rfl
      | cons y ys => exact ih _ (by simp)
  have pickEq : pinnedPick deg deps placed remaining =
      (remaining.toList.filter fun t => (deps.getD t #[]).all placed.contains).foldl g none := by
    unfold pinnedPick
    rw [← Array.foldl_toList, Array.toList_filter]
    rfl
  constructor
  · intro noPick t ht
    cases hr : (deps.getD t #[]).all placed.contains with
    | false => rfl
    | true =>
      exfalso
      have nonempty : (remaining.toList.filter fun t => (deps.getD t #[]).all placed.contains) ≠ [] :=
        List.ne_nil_of_mem (List.mem_filter.mpr ⟨ht, hr⟩)
      have := alwaysSome _ none nonempty
      rw [← pickEq, noPick] at this
      cases this
  · intro p hp
    rw [pickEq] at hp
    rcases Ix.Sharing.Verify.SharingExact.foldl_some_mem g (by
        intro b o r hb
        cases b with
        | none => simp only [g, Option.some.injEq] at hb; exact Or.inl hb.symm
        | some b =>
          simp only [g] at hb
          split at hb
          · simp only [Option.some.injEq] at hb; exact Or.inl hb.symm
          · exact Or.inr hb) _ _ _ hp with hm | hm
    · exact List.mem_filter.mp hm
    · cases hm

theorem pinnedPlace_spec {dag : Dag} (hwf : DagWF dag) (deg : Array Nat)
    {stored : List Nat} {deps : Std.HashMap Nat (Array Nat)} (ok : DepsOK dag stored deps) :
    ∀ (fuel : Nat) (order remaining : Array Nat) (placed : Std.HashSet Nat),
      (order.toList ++ remaining.toList).Perm stored →
      (∀ x, placed.contains x = true ↔ x ∈ order.toList) →
      Respects deps order.toList → remaining.size ≤ fuel →
      Respects deps (pinnedPlace deg deps fuel order remaining placed).toList := by
  intro fuel
  induction fuel with
  | zero =>
    intro order remaining placed _ _ resp size
    have empty : remaining = #[] := Array.size_eq_zero_iff.mp (by omega)
    subst empty
    simpa [pinnedPlace] using resp
  | succ fuel ih =>
    intro order remaining placed perm placedIff resp size
    obtain ⟨noneCase, someCase⟩ := pinnedPick_cases deg deps placed remaining
    simp only [pinnedPlace]
    split
    · rename_i none
      have notReady := noneCase none
      -- some remaining term would be ready, so nothing remains
      have readyExists : ∀ x, x ∈ remaining.toList →
          ∃ r ∈ remaining.toList, (deps.getD r #[]).all placed.contains = true := by
        intro x
        induction x using Nat.strongRecOn with
        | _ x ihx =>
          intro hx
          cases hr : (deps.getD x #[]).all placed.contains with
          | true => exact ⟨x, hx, hr⟩
          | false =>
            have xStored : x ∈ stored := perm.subset (List.mem_append_right _ hx)
            have : ¬ ∀ d ∈ (deps.getD x #[]).toList, placed.contains d = true := by
              rw [← ready_iff, hr]; simp
            obtain ⟨d, hd, unplaced⟩ : ∃ d ∈ (deps.getD x #[]).toList, ¬ placed.contains d = true := by
              simpa using this
            obtain ⟨dStored, below⟩ := ok.sound x xStored d hd
            have dLt := below_lt hwf below
            have dRemaining : d ∈ remaining.toList := by
              rcases List.mem_append.mp (perm.symm.subset dStored) with h | h
              · exact absurd ((placedIff d).mpr h) unplaced
              · exact h
            exact ihx d dLt dRemaining
      cases hr : remaining.toList with
      | nil =>
        have : remaining = #[] := Array.toList_inj.mp (by simpa using hr)
        subst this
        simpa using resp
      | cons x xs =>
        obtain ⟨r, hr', ready⟩ := readyExists x (by rw [hr]; exact List.mem_cons_self)
        rw [notReady r hr'] at ready
        cases ready
    · rename_i pick hpick
      obtain ⟨member, ready⟩ := someCase pick hpick
      rw [ready_iff] at ready
      apply ih
      · rw [Array.toList_push, toList_erase, List.append_assoc]
        refine List.Perm.trans ?_ perm
        exact List.Perm.append_left _ (List.perm_cons_erase member).symm
      · intro x
        rw [Std.HashSet.contains_insert, Array.toList_push, List.mem_append, List.mem_singleton,
          Bool.or_eq_true, beq_iff_eq, placedIff x]
        constructor
        · rintro (h | h)
          · exact Or.inr h.symm
          · exact Or.inl h
        · rintro (h | h)
          · exact Or.inr h
          · exact Or.inl h.symm
      · rw [Array.toList_push]
        exact respects_push resp (fun d hd => (placedIff d).mp (ready d hd))
      · have := List.length_erase_of_mem member
        rw [← Array.length_toList, toList_erase, this]
        simp only [Array.length_toList]
        omega

/-- **Stored descendants come first.** In the pinned order of a set of
distinct terms, every stored strict descendant of an entry is an earlier
entry. -/
theorem pinnedOrder_backward {dag : Dag} (hwf : DagWF dag) (deg : Array Nat) (stored : Array Nat)
    (hin : ∀ s ∈ stored.toList, s < dag.size) (nodup : stored.toList.Nodup) :
    ∀ (k j : Nat) (hk : k < (pinnedOrder dag deg stored).size)
      (hj : j < (pinnedOrder dag deg stored).size),
      Below dag (pinnedOrder dag deg stored)[k] (pinnedOrder dag deg stored)[j] → j < k := by
  have ok := pinnedDeps_ok hwf stored hin
  have perm := pinnedOrder_perm dag deg stored
  have resp : Respects (pinnedDeps dag stored) (pinnedOrder dag deg stored).toList := by
    unfold pinnedOrder
    exact pinnedPlace_spec hwf deg ok stored.size #[] stored {} (by simp) (by simp) (by
      intro k hk; simp at hk) (Nat.le_refl _)
  generalize pinnedOrder dag deg stored = order at perm resp ⊢
  have orderNodup : order.toList.Nodup := perm.nodup_iff.mpr nodup
  have claim : ∀ x, ∀ k (hk : k < order.toList.length), order.toList[k] = x →
      ∀ j (hj : j < order.toList.length), Below dag x order.toList[j] → j < k := by
    intro x
    induction x using Nat.strongRecOn with
    | _ x ih =>
      intro k hk hx j hj below
      have xStored : x ∈ stored.toList := perm.subset (hx ▸ List.getElem_mem hk)
      have jStored : order.toList[j] ∈ stored.toList := perm.subset (List.getElem_mem hj)
      obtain ⟨d', hd', close⟩ := ok.complete x xStored _ jStored below
      obtain ⟨i, hi, atI⟩ := resp k hk d' (hx ▸ hd')
      rcases close with same | further
      · have : i = j := (orderNodup.getElem_inj (hi := by omega) (hj := hj)).mp (atI.trans same)
        omega
      · have d'Lt : d' < x := below_lt hwf (ok.sound x xStored d' hd').2
        have := ih d' d'Lt i (by omega) atI j hj further
        omega
  intro k j hk hj below
  have hk' : k < order.toList.length := by simpa using hk
  have hj' : j < order.toList.length := by simpa using hj
  exact claim order.toList[k] k hk' rfl j hj' (by simpa only [Array.getElem_toList] using below)

end Ix.Sharing.Verify.Pinned

#guard_kernel_axioms Ix.Sharing.Verify.Pinned.pinnedDeps_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Pinned.pinnedOrder_backward [propext, Classical.choice, Quot.sound]
