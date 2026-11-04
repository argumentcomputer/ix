import Ix.Cert.SourceTrace
import Ix.LeanIngress.Theorems

/-! # Quotient Source's schedule: each group once, its references first

`Ix.LeanIngress.orderOf` orders the groups by a depth-first postorder (`Order.dfs`). The walk
emits a node of its range when it finishes it, and marks it finished then, so it emits each
node of its range at most once (`dfs_nodup`). `scheduleOf` lets a group through only when every
group it references (`Graph.hard`) has a smaller position, a group's position being the last
index the order lists it at; on an order whose every entry is a group, each group is listed
once, so its position is its index, and a group the schedule lets through has every group it
references at an earlier index of the schedule (`hard_before`). -/

namespace Ix.Cert.ScheduleOrder

open Ix.LeanIngress
open Ix.LeanIngress.Order (Walk walk pushSuccs root dfs)

/-! ## The walk emits each node of its range once -/

/-- What a walk has emitted: its finished marks cover the range, and the nodes of the range
it emitted are distinct and finished. -/
structure Emitted (n : Nat) (w : Walk) : Prop where
  done_size : w.done.size = n
  nodup : (w.out.toList.filter fun x => decide (x < n)).Nodup
  done : ∀ x ∈ w.out, x < n → w.done[x]! = true

theorem Emitted.enter {n : Nat} {w : Walk} (h : Emitted n w) (x : Nat) : Emitted n (w.enter x) :=
  ⟨h.done_size, h.nodup, h.done⟩

theorem Emitted.leave {n : Nat} {w : Walk} (h : Emitted n w) (x : Nat) : Emitted n (w.leave x) :=
  ⟨h.done_size, h.nodup, h.done⟩

/-- Finishing an unfinished node of the range emits it for the first time. -/
theorem Emitted.finish {n : Nat} {w : Walk} (h : Emitted n w) {x : Nat} (hx : x < n)
    (hd : w.done[x]! = false) : Emitted n (w.finish x) := by
  refine ⟨by simp [Walk.finish, h.done_size], ?_, fun y hy hyn => ?_⟩
  · simp only [Walk.finish, Array.toList_push, List.filter_append, hx, decide_true,
      List.filter_cons_of_pos, List.filter_nil]
    refine List.nodup_append.mpr ⟨h.nodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
      fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    intro e
    subst e
    have := h.done a (Array.mem_toList_iff.mp (List.mem_filter.mp ha).1) hx
    rw [hd] at this
    cases this
  · simp only [Walk.finish] at hy ⊢
    by_cases e : x = y
    · subst e
      exact Order.getElem!_set!_true (by rw [h.done_size]; exact hx)
    · rw [Order.getElem!_set!_ne e]
      rcases Array.mem_push.mp hy with hy | hy
      · exact h.done y hy hyn
      · exact absurd hy.symm e

/-- Emitting a node outside the range changes nothing the range sees. -/
theorem Emitted.emit {n : Nat} {w : Walk} (h : Emitted n w) {x : Nat} (hx : ¬ x < n) :
    Emitted n (w.emit x) := by
  refine ⟨h.done_size, ?_, fun y hy hyn => ?_⟩
  · simp only [Walk.emit, Array.toList_push, List.filter_append, hx, decide_false,
      List.filter_cons_of_neg, List.filter_nil, List.append_nil, Bool.false_eq_true, not_false_eq_true]
    exact h.nodup
  · rcases Array.mem_push.mp hy with hy | hy
    · exact h.done y hy hyn
    · subst hy; exact absurd hyn hx

/-- `pushSuccs` pushes only visit entries. -/
theorem finishing_pushSuccs (w : Walk) (succs : Array Nat) (stack : List (Nat × Bool)) (x : Nat)
    (h : (x, true) ∈ pushSuccs w succs stack) : (x, true) ∈ stack := by
  unfold pushSuccs at h
  rw [← Array.foldl_toList] at h
  generalize succs.toList = l at h
  induction l generalizing stack with
  | nil => exact h
  | cons d ds ih =>
    rw [List.foldl_cons] at h
    have := ih _ h
    split at this
    · exact this
    · rcases List.mem_cons.mp this with e | e
      · cases e
      · exact e

/-- **The walk keeps what it emitted**, from a stack whose finishing entries are in range. -/
theorem walk_emitted (n : Nat) (succs : Nat → Array Nat) :
    ∀ (fuel : Nat) (stack : List (Nat × Bool)) (w : Walk), Emitted n w →
      (∀ x, (x, true) ∈ stack → x < n) → Emitted n (walk n succs fuel stack w) := by
  intro fuel
  induction fuel with
  | zero => intro stack w h _; cases stack <;> exact h
  | succ fuel ih =>
    intro stack w h fin
    rcases stack with _ | ⟨⟨y, _ | _⟩, s⟩
    · exact h
    · simp only [walk]
      by_cases skip : (w.done[y]! || w.active[y]!) = true
      · simp only [skip, ↓reduceIte]
        exact ih s w h fun x hx => fin x (List.mem_cons_of_mem _ hx)
      · simp only [skip, Bool.false_eq_true, ↓reduceIte]
        by_cases hy : y < n
        · simp only [hy, ↓reduceIte]
          refine ih _ _ (h.enter y) fun x hx => ?_
          rcases List.mem_cons.mp (finishing_pushSuccs _ _ _ x hx) with e | e
          · cases e; exact hy
          · exact fin x (List.mem_cons_of_mem _ e)
        · simp only [hy, ↓reduceIte]
          exact ih s _ (h.emit hy) fun x hx => fin x (List.mem_cons_of_mem _ hx)
    · simp only [walk]
      have hy : y < n := fin y List.mem_cons_self
      have fin' : ∀ x, (x, true) ∈ s → x < n := fun x hx => fin x (List.mem_cons_of_mem _ hx)
      by_cases hd : w.done[y]! = true
      · simp only [hd, ↓reduceIte]
        exact ih s _ (h.leave y) fin'
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        exact ih s _ (h.finish hy (Bool.eq_false_iff.mpr hd)) fin'

theorem root_emitted (n : Nat) (succs : Nat → Array Nat) (fuel : Nat) (w : Walk) (h : Emitted n w)
    (r : Nat) : Emitted n (root n succs fuel w r) := by
  unfold root
  split
  · exact h
  · exact walk_emitted n succs fuel _ w h fun x hx => by
      rw [List.mem_singleton] at hx
      cases hx

theorem foldl_root_emitted (n : Nat) (succs : Nat → Array Nat) (fuel : Nat) :
    ∀ (l : List Nat) (w : Walk), Emitted n w → Emitted n (l.foldl (root n succs fuel) w)
  | [], _, h => h
  | r :: l, w, h => foldl_root_emitted n succs fuel l _ (root_emitted n succs fuel w h r)

/-- **The postorder lists each node of its range at most once.** -/
theorem dfs_nodup (n : Nat) (roots : Array Nat) (succs : Nat → Array Nat) (fuel : Nat) :
    ((dfs n roots succs fuel).toList.filter fun x => decide (x < n)).Nodup := by
  unfold dfs
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  have empty : Emitted n (Walk.empty n) :=
    ⟨by simp [Walk.empty], by simp [Walk.empty], fun x hx => by simp [Walk.empty] at hx⟩
  exact (foldl_root_emitted n succs fuel _ _ (foldl_root_emitted n succs fuel _ _ empty)).nodup

/-- **The order lists each group at most once.** -/
theorem orderOf_nodup (g : Graph) :
    ((orderOf g).toList.filter fun x => decide (x < g.groups.size)).Nodup := by
  unfold orderOf
  exact dfs_nodup _ _ _ _

/-! ## Positions -/

/-- The positions `scheduleOf` computes: the last index the order lists each group at. -/
def positions (g : Graph) : Array Nat :=
  (orderOf g).toList.zipIdx.foldl (fun pos ip => pos.set! ip.1 ip.2) (Array.replicate g.groups.size 0)

/-- What `scheduleOf` checks of a group before it lets it through. -/
def admit (g : Graph) (pos : Array Nat) (i : Nat) : Except Ix.Kernel.Reader.ReadError Converted := do
  let c ← g.converted[i]!
  if let some e := g.unplaced[i]! then throw e
  unless g.hard[i]!.all (pos[·]! < pos[i]!) do
    throw (.malformed "a reference cycle through another declaration group")
  return c

theorem scheduleOf_eq (g : Graph) : scheduleOf g = (orderOf g).map fun i => (i, admit g (positions g) i) := by
  unfold scheduleOf positions admit
  simp only [Id.run, Array.forIn_pure_yield_eq_foldl, ← Array.foldl_toList, Array.toList_zipIdx]
  rfl

theorem getElem!_set!_other {a : Array Nat} {i j v : Nat} (h : i ≠ j) : (a.set! i v)[j]! = a[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.set!,
    Array.getElem?_setIfInBounds_ne h]

theorem getElem!_set!_self {a : Array Nat} {i v : Nat} (h : i < a.size) : (a.set! i v)[i]! = v := by
  simp [h]

theorem foldl_set_other (k : Nat) :
    ∀ (L : List (Nat × Nat)) (A : Array Nat), (∀ e ∈ L, e.1 ≠ k) →
      (L.foldl (fun pos ip => pos.set! ip.1 ip.2) A)[k]! = A[k]!
  | [], _, _ => rfl
  | e :: L, A, h => by
    rw [List.foldl_cons, foldl_set_other k L _ fun e' he' => h e' (List.mem_cons_of_mem _ he')]
    exact getElem!_set!_other (h e List.mem_cons_self)

/-- The last write at a key is the only one. -/
theorem foldl_set_at {k v n : Nat} (hk : k < n) :
    ∀ (L : List (Nat × Nat)) (A : Array Nat), A.size = n → (∀ e ∈ L, e.1 = k → e.2 = v) → (k, v) ∈ L →
      (L.foldl (fun pos ip => pos.set! ip.1 ip.2) A)[k]! = v
  | [], _, _, _, h => by cases h
  | e :: L, A, hA, uniq, mem => by
    rw [List.foldl_cons]
    by_cases hL : (k, v) ∈ L
    · exact foldl_set_at hk L _ (by simp [hA]) (fun e' he' => uniq e' (List.mem_cons_of_mem _ he')) hL
    · rcases List.mem_cons.mp mem with he | he
      · subst he
        rw [foldl_set_other k L _ fun e' he' hek => hL (by
          have := uniq e' (List.mem_cons_of_mem _ he') hek
          rw [← hek, ← this]
          exact he')]
        exact getElem!_set!_self (a := A) (by rw [hA]; exact hk)
      · exact absurd he hL

/-- **On an order of distinct groups, a group's position is its index.** -/
theorem positions_at {g : Graph} (inRange : ∀ i ∈ orderOf g, i < g.groups.size) {p i : Nat}
    (hp : (orderOf g)[p]? = some i) : (positions g)[i]! = p := by
  have nodup : (orderOf g).toList.Nodup := by
    have := orderOf_nodup g
    rwa [List.filter_eq_self.mpr fun x hx => decide_eq_true (inRange x (Array.mem_toList_iff.mp hx))] at this
  have hi : i < g.groups.size := inRange i (Array.mem_of_getElem? hp)
  refine foldl_set_at hi _ _ (by simp) (fun e he hek => ?_) ?_
  · obtain ⟨a, q⟩ := e
    simp only at hek
    subst hek
    have hq := List.mem_zipIdx_iff_getElem?.mp he
    simp only at hq
    rw [← Array.getElem?_toList] at hp
    obtain ⟨hq', -⟩ := List.getElem?_eq_some_iff.mp hq
    exact nodup.eq_of_getElem?_eq hq' (hq.trans hp.symm)
  · exact List.mem_zipIdx_iff_getElem?.mpr (by simpa using hp)

/-- **A group the schedule lets through has every group it references at an earlier
index**, on an order of groups. -/
theorem hard_before {g : Graph} (inRange : ∀ i ∈ orderOf g, i < g.groups.size) {p : Nat}
    {x : Nat × Except Ix.Kernel.Reader.ReadError Converted} {conv : Converted} (hx : (scheduleOf g)[p]? = some x)
    (hc : x.2 = .ok conv) {j : Nat} (hj : j ∈ g.hard[x.1]!) (hjn : j < g.groups.size) :
    ∃ q < p, ∃ y, (scheduleOf g)[q]? = some y ∧ y.1 = j := by
  rw [scheduleOf_eq, Array.getElem?_map] at hx
  cases ho : (orderOf g)[p]? with
  | none => rw [ho] at hx; cases hx
  | some i =>
    rw [ho] at hx
    cases hx
    simp only at hj hc
    have hcheck : (g.hard[i]!.all fun k => decide ((positions g)[k]! < (positions g)[i]!)) = true := by
      unfold admit at hc
      cases hcv : g.converted[i]! with
      | error e => rw [hcv] at hc; cases hc
      | ok c =>
        simp only [hcv, bind, Except.bind] at hc
        split at hc
        · cases hc
        · cases hall : (g.hard[i]!.all fun k => decide ((positions g)[k]! < (positions g)[i]!))
          · simp [hall, throw, throwThe, MonadExceptOf.throw] at hc
          · rfl
    have hlt := of_decide_eq_true (Array.all_eq_true_iff_forall_mem.mp hcheck j hj)
    obtain ⟨q, hq⟩ := Array.getElem_of_mem (orderOf_complete g hjn)
    obtain ⟨hqn, hqe⟩ := hq
    have hqget : (orderOf g)[q]? = some j := by rw [Array.getElem?_eq_getElem hqn, hqe]
    rw [positions_at inRange hqget, positions_at inRange ho] at hlt
    refine ⟨q, hlt, (j, admit g (positions g) j), ?_, rfl⟩
    rw [scheduleOf_eq, Array.getElem?_map, hqget]
    rfl

end Ix.Cert.ScheduleOrder
