module

/-! # The Source ingress's group order: a structural depth-first postorder

`Ix.LeanIngress.orderOf` orders the declaration groups by a depth-first
postorder of their reference graph. The walk keeps an explicit stack (a
native recursion could exhaust the thread's stack on a long reference chain),
and it is structural recursion on fuel, so that its result can be reasoned
about (`mem_dfs`). Nodes are `Nat`s; `succs x` lists `x`'s successors in the
order they are pushed (the last is visited first).

* `walk` pops one stack entry per step. `(x, false)` visits `x`: a node
  finished or on the current path is skipped; a node below `n` joins the
  path, its finishing entry `(x, true)` is pushed, then the successors that
  are neither finished nor on the path; a node at or above `n` is emitted
  as it is. `(x, true)` takes `x` off the path and emits it, unless it was
  finished already.
* `dfs` walks from each root in turn, then from every node below `n` in index
  order (a pass that visits nothing when the roots hold every node).
* **The fuel** `fuelOf n D` bounds the pops when `D` bounds the successor
  lists below `n`: the potential `|stack| + (1 + D) · unvisited` falls by at
  least one per pop (a visit consumes its node's `1 + D` and pushes at most
  `1 + D` entries), so no walk runs out of fuel.
* **Coverage** (`mem_dfs`): every node below `n` is in the postorder.

The module imports nothing but core. -/

@[expose] public section

namespace Ix.LeanIngress.Order

/-- The walk's state: the nodes finished (`done`) and on the current path
(`active`), and the postorder so far (`out`). -/
structure Walk where
  done : Array Bool
  active : Array Bool
  out : Array Nat

/-- `x` joins the path. -/
def Walk.enter (w : Walk) (x : Nat) : Walk := { w with active := w.active.set! x true }

/-- `x` leaves the path, finished already. -/
def Walk.leave (w : Walk) (x : Nat) : Walk := { w with active := w.active.set! x false }

/-- `x` leaves the path, finished and emitted. -/
def Walk.finish (w : Walk) (x : Nat) : Walk :=
  { done := w.done.set! x true, active := w.active.set! x false, out := w.out.push x }

/-- `x` is emitted (a node outside the walk's range). -/
def Walk.emit (w : Walk) (x : Nat) : Walk := { w with out := w.out.push x }

/-- Push the successors `succs` that are neither finished nor on the path onto
`stack`, in order, so that the last pushed is popped first. -/
def pushSuccs (w : Walk) (succs : Array Nat) (stack : List (Nat × Bool)) : List (Nat × Bool) :=
  succs.foldl (fun st d => if w.done[d]! || w.active[d]! then st else (d, false) :: st) stack

/-- **The depth-first walk** from `stack` (its head is the top), at most `fuel`
pops. An entry `(x, false)` asks to visit `x`: a node not finished, not on
the path and below `n` is marked active, its finishing entry `(x, true)`
pushed, then its successors `succs x`; a node at or above `n` is emitted
as it is. An entry `(x, true)` finishes `x`: it leaves the path and is
emitted unless it was finished already. -/
def walk (n : Nat) (succs : Nat → Array Nat) : Nat → List (Nat × Bool) → Walk → Walk
  | 0, _, w => w
  | _ + 1, [], w => w
  | fuel + 1, (node, true) :: stack, w =>
    if w.done[node]! then walk n succs fuel stack (w.leave node)
    else walk n succs fuel stack (w.finish node)
  | fuel + 1, (node, false) :: stack, w =>
    if w.done[node]! || w.active[node]! then walk n succs fuel stack w
    else if node < n then
      walk n succs fuel (pushSuccs (w.enter node) (succs node) ((node, true) :: stack))
        (w.enter node)
    else walk n succs fuel stack (w.emit node)

/-- The empty walk over `n` nodes. -/
def Walk.empty (n : Nat) : Walk := ⟨Array.replicate n false, Array.replicate n false, #[]⟩

/-- One root of the postorder: skipped if finished, else walked. -/
def root (n : Nat) (succs : Nat → Array Nat) (fuel : Nat) (w : Walk) (r : Nat) : Walk :=
  if w.done[r]! then w else walk n succs fuel [(r, false)] w

/-- **The depth-first postorder** from `roots`, in order, then from every node
below `n`, in index order, each walked at most `fuel` pops. When the roots
already hold every node below `n`, the second pass visits nothing; it makes
the postorder cover every node whatever the roots are (`mem_dfs`). -/
def dfs (n : Nat) (roots : Array Nat) (succs : Nat → Array Nat) (fuel : Nat) : Array Nat :=
  ((Array.range n).foldl (root n succs fuel) (roots.foldl (root n succs fuel) (Walk.empty n))).out

/-- A fuel that bounds every walk's pops when `D` bounds the successor lists
of the nodes below `n` (`walk_spec`). -/
def fuelOf (n D : Nat) : Nat := 1 + (1 + D) * n

/-! ## Coverage -/

theorem getElem!_set!_ne {a : Array Bool} {i j : Nat} {v : Bool} (h : i ≠ j) :
    (a.set! i v)[j]! = a[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.set!,
    Array.getElem?_setIfInBounds_ne h]

theorem set!_of_le {a : Array Bool} {i : Nat} {v : Bool} (h : a.size ≤ i) : a.set! i v = a := by
  simp [Array.set!, Array.setIfInBounds, Nat.not_lt.mpr h]

theorem getElem!_set!_false (a : Array Bool) (i : Nat) : (a.set! i false)[i]! = false := by
  by_cases h : i < a.size
  · simp [h]
  · rw [set!_of_le (by omega)]
    simp [h]

theorem getElem!_set!_true {a : Array Bool} {i : Nat} (h : i < a.size) :
    (a.set! i true)[i]! = true := by
  simp [h]

/-- The nodes below `n` neither finished nor on the path. -/
def unvisited (n : Nat) (w : Walk) : Nat :=
  (List.range n).countP fun i => !w.done[i]! && !w.active[i]!

/-- The walk's invariant: the arrays have `n` entries, a finished node has
been emitted, and an active node's finishing entry is on the stack. -/
structure Inv (n : Nat) (stack : List (Nat × Bool)) (w : Walk) : Prop where
  done_size : w.done.size = n
  active_size : w.active.size = n
  emitted : ∀ x, w.done[x]! = true → x ∈ w.out
  onStack : ∀ x, w.active[x]! = true → (x, true) ∈ stack

theorem mem_pushSuccs (w : Walk) (succs : Array Nat) (stack : List (Nat × Bool))
    (e : Nat × Bool) (h : e ∈ stack) : e ∈ pushSuccs w succs stack := by
  unfold pushSuccs
  rw [← Array.foldl_toList]
  induction succs.toList generalizing stack with
  | nil => exact h
  | cons d ds ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact h
    · exact List.mem_cons_of_mem _ h

theorem length_pushSuccs (w : Walk) (succs : Array Nat) (stack : List (Nat × Bool)) :
    (pushSuccs w succs stack).length ≤ stack.length + succs.size := by
  unfold pushSuccs
  rw [← Array.foldl_toList, ← Array.length_toList]
  induction succs.toList generalizing stack with
  | nil => simp
  | cons d ds ih =>
    simp only [List.foldl_cons, List.length_cons]
    split
    · have := ih stack; omega
    · have := ih ((d, false) :: stack); simp only [List.length_cons] at this; omega

/-- Changing one counted element into an uncounted one lowers the count by one. -/
theorem countP_drop_one {l : List Nat} (hl : l.Nodup) {p q : Nat → Bool} {x : Nat} (hx : x ∈ l)
    (hp : p x = true) (hq : q x = false) (same : ∀ y, y ≠ x → q y = p y) :
    l.countP q + 1 = l.countP p := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.countP_cons, List.countP_cons]
    by_cases ha : a = x
    · subst ha
      have : l.countP q = l.countP p := by
        apply List.countP_congr
        intro y hy
        rw [same y (fun e => hl.1 (e ▸ hy))]
      simp [hp, hq, this]
    · have hx' : x ∈ l := by
        rcases List.mem_cons.mp hx with e | e
        · exact absurd e.symm ha
        · exact e
      have := ih hl.2 hx'
      rw [same a ha]
      omega

theorem unvisited_le (n : Nat) (w : Walk) : unvisited n w ≤ n := by
  unfold unvisited
  exact Nat.le_trans List.countP_le_length (by simp)

theorem unvisited_mono {n : Nat} {w w' : Walk}
    (h : ∀ x < n, (!w'.done[x]! && !w'.active[x]!) = true → (!w.done[x]! && !w.active[x]!) = true) :
    unvisited n w' ≤ unvisited n w :=
  List.countP_mono_left fun x hx => h x (List.mem_range.mp hx)

theorem nil_out {x : Nat} {w : Walk} (hx : x ∈ w.out ∨ ∃ b, (x, b) ∈ ([] : List (Nat × Bool))) :
    x ∈ w.out := by
  rcases hx with hx | ⟨b, hb⟩
  · exact hx
  · cases hb

theorem mem_push_of_mem {o : Array Nat} {x y : Nat} (h : x ∈ o) : x ∈ o.push y :=
  Array.mem_push.mpr (.inl h)

/-- A popped entry's node, and the rest of the stack, survive the pop. -/
theorem keep_pop {w w1 : Walk} {y : Nat} {c : Bool} {s : List (Nat × Bool)}
    (hout : ∀ x, x ∈ w.out → x ∈ w1.out) (hy : y ∈ w1.out ∨ ∃ b, (y, b) ∈ s) :
    ∀ x, (x ∈ w.out ∨ ∃ b, (x, b) ∈ (y, c) :: s) → x ∈ w1.out ∨ ∃ b, (x, b) ∈ s := by
  intro x hx
  rcases hx with hx | ⟨b, hb⟩
  · exact .inl (hout x hx)
  · rcases List.mem_cons.mp hb with e | e
    · cases e; exact hy
    · exact .inr ⟨b, e⟩

/-- Popping a visit entry keeps the active nodes' finishing entries. -/
theorem onStack_pop {n : Nat} {y : Nat} {s : List (Nat × Bool)} {w : Walk}
    (inv : Inv n ((y, false) :: s) w) : ∀ x, w.active[x]! = true → (x, true) ∈ s := by
  intro x hx
  rcases List.mem_cons.mp (inv.onStack x hx) with h | h
  · cases h
  · exact h

/-- **The walk's specification**: from a state satisfying the invariant, with
enough fuel for its potential, the walk ends with an empty stack (no node on
the path), keeps the invariant, and emits every node it started with on the
stack or in the output. -/
theorem walk_spec (n D : Nat) (succs : Nat → Array Nat) (hD : ∀ i < n, (succs i).size ≤ D) :
    ∀ (fuel : Nat) (stack : List (Nat × Bool)) (w : Walk), Inv n stack w →
      stack.length + (1 + D) * unvisited n w ≤ fuel →
      Inv n [] (walk n succs fuel stack w) ∧
        ∀ x, (x ∈ w.out ∨ ∃ b, (x, b) ∈ stack) → x ∈ (walk n succs fuel stack w).out := by
  intro fuel
  induction fuel with
  | zero =>
    intro stack w inv pot
    have hs : stack = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hs
    exact ⟨inv, fun x hx => nil_out hx⟩
  | succ fuel ih =>
    intro stack w inv pot
    rcases stack with _ | ⟨⟨y, _ | _⟩, s⟩
    · exact ⟨inv, fun x hx => nil_out hx⟩
    · -- a visit entry `(y, false)`
      simp only [walk]
      simp only [List.length_cons] at pot
      by_cases skip : (w.done[y]! || w.active[y]!) = true
      · simp only [skip, ↓reduceIte]
        have ⟨i1, o1⟩ := ih s w ⟨inv.done_size, inv.active_size, inv.emitted, onStack_pop inv⟩
          (by omega)
        refine ⟨i1, fun x hx => o1 x (keep_pop (fun _ h => h) ?_ x hx)⟩
        rcases Bool.or_eq_true_iff.mp skip with h | h
        · exact .inl (inv.emitted y h)
        · rcases List.mem_cons.mp (inv.onStack y h) with h' | h'
          · cases h'
          · exact .inr ⟨true, h'⟩
      · simp only [skip, Bool.false_eq_true, ↓reduceIte]
        have hdy : w.done[y]! = false := by
          cases h : w.done[y]! <;> simp_all
        have hay : w.active[y]! = false := by
          cases h : w.active[y]! <;> simp_all
        by_cases lt : y < n
        · simp only [lt, ↓reduceIte]
          have hya : y < w.active.size := by rw [inv.active_size]; exact lt
          have inv1 : Inv n (pushSuccs (w.enter y) (succs y) ((y, true) :: s)) (w.enter y) := by
            refine ⟨inv.done_size, by simp [Walk.enter, inv.active_size], inv.emitted,
              fun x hx => mem_pushSuccs _ _ _ _ ?_⟩
            by_cases e : y = x
            · subst e; exact List.mem_cons_self
            · simp only [Walk.enter] at hx
              rw [getElem!_set!_ne e] at hx
              exact List.mem_cons_of_mem _ (onStack_pop inv x hx)
          have drop : unvisited n (w.enter y) + 1 = unvisited n w := by
            unfold unvisited
            refine countP_drop_one List.nodup_range (List.mem_range.mpr lt)
              (by simp [hdy, hay]) ?_ (fun x e => ?_)
            · simp only [Walk.enter, getElem!_set!_true hya]; simp
            · simp only [Walk.enter]; rw [getElem!_set!_ne (Ne.symm e)]
          have pot1 : (pushSuccs (w.enter y) (succs y) ((y, true) :: s)).length +
              (1 + D) * unvisited n (w.enter y) ≤ fuel := by
            have len := length_pushSuccs (w.enter y) (succs y) ((y, true) :: s)
            have hsz := hD y lt
            simp only [List.length_cons] at len
            have : (1 + D) * unvisited n w = (1 + D) * unvisited n (w.enter y) + (1 + D) := by
              rw [← drop, Nat.mul_add, Nat.mul_one]
            omega
          have ⟨i1, o1⟩ := ih _ _ inv1 pot1
          refine ⟨i1, fun x hx => o1 x ?_⟩
          rcases hx with hx | ⟨b, hb⟩
          · exact .inl hx
          · rcases List.mem_cons.mp hb with e | e
            · cases e; exact .inr ⟨true, mem_pushSuccs _ _ _ _ List.mem_cons_self⟩
            · exact .inr ⟨b, mem_pushSuccs _ _ _ _ (List.mem_cons_of_mem _ e)⟩
        · simp only [lt, ↓reduceIte]
          have inv1 : Inv n s (w.emit y) :=
            ⟨inv.done_size, inv.active_size, fun x hx => mem_push_of_mem (inv.emitted x hx),
              fun x hx => onStack_pop inv x hx⟩
          have ⟨i1, o1⟩ := ih s _ inv1 (by simp only [unvisited, Walk.emit] at pot ⊢; omega)
          exact ⟨i1, fun x hx => o1 x (keep_pop (fun _ h => mem_push_of_mem h)
            (.inl Array.mem_push_self) x hx)⟩
    · -- a finishing entry `(y, true)`
      have onStack1 : ∀ x, (w.active.set! y false)[x]! = true → (x, true) ∈ s := by
        intro x hx
        by_cases e : y = x
        · subst e; rw [getElem!_set!_false] at hx; cases hx
        · rw [getElem!_set!_ne e] at hx
          rcases List.mem_cons.mp (inv.onStack x hx) with h | h
          · cases h; exact absurd rfl e
          · exact h
      simp only [walk]
      simp only [List.length_cons] at pot
      by_cases hd : w.done[y]! = true
      · simp only [hd, ↓reduceIte]
        have inv1 : Inv n s (w.leave y) :=
          ⟨inv.done_size, by simp [Walk.leave, inv.active_size], inv.emitted, onStack1⟩
        have : unvisited n (w.leave y) ≤ unvisited n w := unvisited_mono fun x _ hx => by
          simp only [Walk.leave] at hx
          by_cases e : y = x
          · subst e; simp [hd] at hx
          · rw [getElem!_set!_ne e] at hx; exact hx
        have ⟨i1, o1⟩ := ih s _ inv1 (by have := Nat.mul_le_mul_left (1 + D) this; omega)
        exact ⟨i1, fun x hx => o1 x (keep_pop (fun _ h => h) (.inl (inv.emitted y hd)) x hx)⟩
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        have inv1 : Inv n s (w.finish y) := by
          refine ⟨by simp [Walk.finish, inv.done_size], by simp [Walk.finish, inv.active_size],
            fun x hx => ?_, onStack1⟩
          by_cases e : y = x
          · subst e; exact Array.mem_push_self
          · simp only [Walk.finish] at hx
            rw [getElem!_set!_ne e] at hx
            exact mem_push_of_mem (inv.emitted x hx)
        have : unvisited n (w.finish y) ≤ unvisited n w := unvisited_mono fun x hxn hx => by
          simp only [Walk.finish] at hx
          by_cases e : y = x
          · subst e
            have : y < w.done.size := by rw [inv.done_size]; exact hxn
            simp [this] at hx
          · rw [getElem!_set!_ne e, getElem!_set!_ne e] at hx; exact hx
        have ⟨i1, o1⟩ := ih s _ inv1 (by have := Nat.mul_le_mul_left (1 + D) this; omega)
        exact ⟨i1, fun x hx => o1 x (keep_pop (fun _ h => mem_push_of_mem h)
          (.inl Array.mem_push_self) x hx)⟩

/-- An invariant state with an empty stack has nothing on the path. -/
theorem Inv.inactive {n : Nat} {w : Walk} (inv : Inv n [] w) (x : Nat) : w.active[x]! = false := by
  cases h : w.active[x]!
  · rfl
  · cases inv.onStack x h

/-- A root's walk: with the fuel `fuelOf n D`, the root is emitted, the
output only grows, and the state stays invariant with an empty stack. -/
theorem root_spec (n D : Nat) (succs : Nat → Array Nat) (hD : ∀ i < n, (succs i).size ≤ D)
    (w : Walk) (inv : Inv n [] w) (r : Nat) :
    Inv n [] (root n succs (fuelOf n D) w r) ∧ r ∈ (root n succs (fuelOf n D) w r).out ∧
      ∀ x, x ∈ w.out → x ∈ (root n succs (fuelOf n D) w r).out := by
  unfold root
  by_cases hd : w.done[r]! = true
  · simp only [hd, ↓reduceIte]
    exact ⟨inv, inv.emitted r hd, fun _ h => h⟩
  · simp only [hd, Bool.false_eq_true, ↓reduceIte]
    have inv0 : Inv n [(r, false)] w :=
      ⟨inv.done_size, inv.active_size, inv.emitted, fun x hx => by
        rw [inv.inactive x] at hx; cases hx⟩
    have pot : [(r, false)].length + (1 + D) * unvisited n w ≤ fuelOf n D := by
      have := Nat.mul_le_mul_left (1 + D) (unvisited_le n w)
      simp only [List.length_cons, List.length_nil, fuelOf]
      omega
    have ⟨i1, o1⟩ := walk_spec n D succs hD _ _ w inv0 pot
    exact ⟨i1, o1 r (.inr ⟨false, List.mem_singleton_self _⟩), fun x h => o1 x (.inl h)⟩

theorem empty_inv (n : Nat) : Inv n [] (Walk.empty n) := by
  refine ⟨by simp [Walk.empty], by simp [Walk.empty], fun x hx => ?_, fun x hx => ?_⟩ <;>
  · simp only [Walk.empty, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_replicate] at hx
    split at hx <;> simp at hx

/-- The roots' fold, from an invariant state: it emits every root, keeps the
invariant and the output. -/
theorem foldl_root (n D : Nat) (succs : Nat → Array Nat) (hD : ∀ i < n, (succs i).size ≤ D) :
    ∀ (l : List Nat) (w : Walk), Inv n [] w →
      (∀ x ∈ l, x ∈ (l.foldl (root n succs (fuelOf n D)) w).out) ∧
        Inv n [] (l.foldl (root n succs (fuelOf n D)) w) ∧
        ∀ x, x ∈ w.out → x ∈ (l.foldl (root n succs (fuelOf n D)) w).out := by
  intro l
  induction l with
  | nil => intro w inv; exact ⟨fun _ h => (by cases h), inv, fun _ h => h⟩
  | cons a l ih =>
    intro w inv
    have ⟨ia, ra, oa⟩ := root_spec n D succs hD w inv a
    have ⟨cov, il, ol⟩ := ih _ ia
    refine ⟨fun x hx => ?_, il, fun x h => ol x (oa x h)⟩
    rcases List.mem_cons.mp hx with e | e
    · subst e; exact ol x ra
    · exact cov x e

/-- **Coverage**: with the fuel `fuelOf n D`, every node below `n` is in the
postorder, whatever the roots. -/
theorem mem_dfs (n D : Nat) (roots : Array Nat) (succs : Nat → Array Nat)
    (hD : ∀ i < n, (succs i).size ≤ D) {i : Nat} (hi : i < n) :
    i ∈ dfs n roots succs (fuelOf n D) := by
  unfold dfs
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  have ⟨_, inv1, _⟩ := foldl_root n D succs hD roots.toList _ (empty_inv n)
  exact (foldl_root n D succs hD _ _ inv1).1 i (by simp [hi])

/-- The largest `f i` for `i < n` (`0` if none). -/
def maxBelow (n : Nat) (f : Nat → Nat) : Nat :=
  (List.range n).foldl (fun m i => max m (f i)) 0

theorem le_maxBelow {n : Nat} (f : Nat → Nat) {i : Nat} (hi : i < n) : f i ≤ maxBelow n f := by
  unfold maxBelow
  suffices ∀ (l : List Nat) (m : Nat), (i ∈ l → f i ≤ l.foldl (fun m i => max m (f i)) m) ∧
      m ≤ l.foldl (fun m i => max m (f i)) m from (this _ 0).1 (List.mem_range.mpr hi)
  intro l
  induction l with
  | nil => intro m; exact ⟨fun h => (by cases h), Nat.le_refl m⟩
  | cons a l ih =>
    intro m
    simp only [List.foldl_cons]
    have ⟨h1, h2⟩ := ih (max m (f a))
    refine ⟨fun h => ?_, Nat.le_trans (Nat.le_max_left _ _) h2⟩
    rcases List.mem_cons.mp h with e | e
    · subst e; exact Nat.le_trans (Nat.le_max_right _ _) h2
    · exact h1 e

/-- **Coverage** with the successor lists as an array and the fuel their
largest size gives. -/
theorem mem_dfs_of_array (n : Nat) (roots : Array Nat) (succs : Array (Array Nat)) {i : Nat}
    (hi : i < n) : i ∈ dfs n roots (succs[·]!) (fuelOf n (maxBelow n (succs[·]!.size))) :=
  mem_dfs n _ roots _ (fun _ hj => le_maxBelow (fun j => (succs[j]!).size) hj) hi

end Ix.LeanIngress.Order
