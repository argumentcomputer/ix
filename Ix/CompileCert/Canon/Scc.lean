import Ix.CompileCert.Canon.SccState

/-!
# M7 L1, components: the invariant of Tarjan's loop

The invariant `Inv G st` of `tarjanLoop` over a graph `G` whose successors are nodes
(`Bounded G`), in the reading of `SccState.lean`:

* the discovery numbers `ix` are injective on visited nodes and below `next`;
* the Tarjan stack holds exactly the on-stack nodes, in decreasing discovery order; the gray
  nodes (`grays`: the call stack) are on it, in decreasing order, each with an edge counter;
* every stack node has a gray node at or below it, and is reachable from every gray node
  below it;
* the low link of a stack node is at most its number and is the number of a stack node it
  reaches; a finished stack node (not gray) has a low link below its number; and the low link
  of the nearest gray node below a stack node is at most the node's;
* every explored edge of a stack node leads to a visited node, and to one whose number is at
  least the node's low link when it is still on the stack;
* the popped components hold exactly the visited nodes off the stack, each once; each is
  strongly connected; every edge leaves a component for the same or an earlier one.

`Graph.lean` (next) proves that each iteration of the loop keeps it, and derives that the
components of `condensation` are the strongly connected components with acyclic
condensation.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon

/-! ## One iteration of the loop -/

/-- The finishing branch of an iteration: pop the component if `v` is a root, then propagate
`v`'s low link to its parent. -/
def finishSt (st : TarjanState) (v : Nat) (rest : List (Nat × Nat)) : TarjanState :=
  let st1 : TarjanState := { st with calls := rest }
  let st2 := if lw st v == ix st v then st1.popComponent v else st1
  match rest with
  | (u, _) :: _ => st2.setLow u (min (lw st2 u) (lw st v))
  | [] => st2

section loop
variable (G : Array (Array Nat)) (fuel : Nat) (st : TarjanState) (v i : Nat)
  (rest : List (Nat × Nat))

theorem tarjanLoop_nil (h : st.calls = []) : tarjanLoop G (fuel + 1) st = st := by
  rw [tarjanLoop]; simp [h]

theorem tarjanLoop_zero : tarjanLoop G 0 st =
    if st.calls.isEmpty then st else { st with exhausted := true } := by
  rw [tarjanLoop]

theorem tarjanLoop_new (hc : st.calls = (v, i) :: rest) (hi : i < (succs G v).size)
    (h0 : ix st (succs G v)[i] = 0) :
    tarjanLoop G (fuel + 1) st =
      tarjanLoop G fuel (({ st with calls := (v, i + 1) :: rest } : TarjanState).visit
        (succs G v)[i]) := by
  rw [tarjanLoop]
  simp only [hc]
  simp only [succs] at hi h0
  simp only [hi, ↓reduceDIte]
  simp only [ix] at h0
  simp [h0]
  rfl

theorem tarjanLoop_on (hc : st.calls = (v, i) :: rest) (hi : i < (succs G v).size)
    (h0 : ix st (succs G v)[i] ≠ 0) (hon : os st (succs G v)[i] = true) :
    tarjanLoop G (fuel + 1) st =
      tarjanLoop G fuel (({ st with calls := (v, i + 1) :: rest } : TarjanState).setLow v
        (min (lw st v) (ix st (succs G v)[i]))) := by
  rw [tarjanLoop]
  simp only [hc]
  simp only [succs] at hi h0 hon
  simp only [hi, ↓reduceDIte]
  simp only [ix] at h0
  simp only [os] at hon
  simp [h0, hon]
  rfl

theorem tarjanLoop_done (hc : st.calls = (v, i) :: rest) (hi : i < (succs G v).size)
    (h0 : ix st (succs G v)[i] ≠ 0) (hon : os st (succs G v)[i] = false) :
    tarjanLoop G (fuel + 1) st =
      tarjanLoop G fuel ({ st with calls := (v, i + 1) :: rest } : TarjanState) := by
  rw [tarjanLoop]
  simp only [hc]
  simp only [succs] at hi h0 hon
  simp only [hi, ↓reduceDIte]
  simp only [ix] at h0
  simp only [os] at hon
  simp [h0, hon]

theorem tarjanLoop_finish (hc : st.calls = (v, i) :: rest) (hi : ¬ i < (succs G v).size) :
    tarjanLoop G (fuel + 1) st = tarjanLoop G fuel (finishSt st v rest) := by
  rw [tarjanLoop]
  simp only [hc]
  simp only [succs] at hi
  simp only [hi, ↓reduceDIte]
  unfold finishSt
  cases rest <;> rfl

end loop

/-! ## The invariant -/

/-- The gray nodes: the call stack's nodes, top first. -/
def grays (st : TarjanState) : List Nat := st.calls.map (·.1)

/-- Edge `j` of `x` (to `w`) has been explored: all of a finished node's edges, the first
`k` of a gray node with counter `k`. -/
def Expl (G : Array (Array Nat)) (st : TarjanState) (x w : Nat) : Prop :=
  ∃ j, (succs G x)[j]? = some w ∧ ∀ p ∈ st.calls, p.1 = x → j < p.2

structure Inv (G : Array (Array Nat)) (st : TarjanState) : Prop where
  szI : st.index.size = G.size
  szL : st.low.size = G.size
  szO : st.onStack.size = G.size
  next_pos : 0 < st.next
  ix_lt : ∀ v, ix st v < st.next
  ix_inj : ∀ u v, ix st u = ix st v → ix st u ≠ 0 → u = v
  on_iff : ∀ v, os st v = true ↔ v ∈ st.stack
  st_vis : ∀ v ∈ st.stack, ix st v ≠ 0
  st_sorted : st.stack.Pairwise (fun a b => ix st b < ix st a)
  calls_on : ∀ g ∈ grays st, g ∈ st.stack
  calls_le : ∀ p ∈ st.calls, p.2 ≤ (succs G p.1).size
  calls_sorted : (grays st).Pairwise (fun a b => ix st b < ix st a)
  stack_gray : ∀ x ∈ st.stack, ∃ g ∈ grays st, ix st g ≤ ix st x
  gray_reach : ∀ g ∈ grays st, ∀ x ∈ st.stack, ix st g ≤ ix st x → Reach G g x
  low_le : ∀ x ∈ st.stack, lw st x ≤ ix st x
  low_wit : ∀ x ∈ st.stack, ∃ y ∈ st.stack, ix st y = lw st x ∧ Reach G x y
  low_fin : ∀ x ∈ st.stack, x ∉ grays st → lw st x < ix st x
  low_gray : ∀ x ∈ st.stack, ∀ g ∈ grays st, ix st g ≤ ix st x →
    (∀ h ∈ grays st, ix st h ≤ ix st x → ix st h ≤ ix st g) → lw st g ≤ lw st x
  explored : ∀ x ∈ st.stack, ∀ w, Expl G st x w → ix st w ≠ 0 ∧ (w ∈ st.stack → lw st x ≤ ix st w)
  comp_iff : ∀ v, (∃ c ∈ st.comps, v ∈ c) ↔ (ix st v ≠ 0 ∧ v ∉ st.stack)
  comp_uniq : ∀ (k k' : Nat) (c c' : Array Nat) (v : Nat), st.comps[k]? = some c → st.comps[k']? = some c' → v ∈ c → v ∈ c' →
    k = k'
  comp_conn : ∀ c ∈ st.comps, ∀ u ∈ c, ∀ v ∈ c, Reach G u v
  comp_down : ∀ (k : Nat) (c : Array Nat) (u w : Nat), st.comps[k]? = some c → u ∈ c → Edge G u w →
    ∃ k' c', k' ≤ k ∧ st.comps[k']? = some c' ∧ w ∈ c'

theorem ix_ne_zero_lt {st : TarjanState} {n v : Nat} (hs : st.index.size = n) (h : ix st v ≠ 0) :
    v < n := by
  rcases Nat.lt_or_ge v n with hv | hv
  · exact hv
  · exfalso; apply h; simp only [ix]; rw [Array.getElem?_eq_none (by omega)]; rfl

theorem Inv.lt_of_stack {G st} (I : Inv G st) {v : Nat} (h : v ∈ st.stack) : v < G.size :=
  ix_ne_zero_lt I.szI (I.st_vis v h)

theorem Inv.lt_of_ix {G st} (I : Inv G st) {v : Nat} (h : ix st v ≠ 0) : v < G.size :=
  ix_ne_zero_lt I.szI h

/-! ## The initial state -/

/-- The state `condensation` starts from. -/
def initSt (n : Nat) : TarjanState :=
  { index := Array.replicate n 0, low := Array.replicate n 0, onStack := Array.replicate n false }

theorem ix_initSt (n v : Nat) : ix (initSt n) v = 0 := by
  simp only [ix, initSt, Array.getElem?_replicate]; split <;> rfl

theorem os_initSt (n v : Nat) : os (initSt n) v = false := by
  simp only [os, initSt, Array.getElem?_replicate]; split <;> rfl

theorem inv_init (G : Array (Array Nat)) : Inv G (initSt G.size) where
  szI := by simp [initSt]
  szL := by simp [initSt]
  szO := by simp [initSt]
  next_pos := by simp [initSt]
  ix_lt v := by rw [ix_initSt]; simp [initSt]
  ix_inj u v _ h := absurd (ix_initSt _ u) h
  on_iff v := by rw [os_initSt]; simp [initSt]
  st_vis v h := by simp [initSt] at h
  st_sorted := by simp [initSt]
  calls_on g h := by simp [grays, initSt] at h
  calls_le p h := by simp [initSt] at h
  calls_sorted := by simp [grays, initSt]
  stack_gray x h := by simp [initSt] at h
  gray_reach g h := by simp [grays, initSt] at h
  low_le x h := by simp [initSt] at h
  low_wit x h := by simp [initSt] at h
  low_fin x h := by simp [initSt] at h
  low_gray x h := by simp [initSt] at h
  explored x h := by simp [initSt] at h
  comp_iff v := by rw [ix_initSt]; simp [initSt]
  comp_uniq k k' c c' v h := by simp [initSt] at h
  comp_conn c h := by simp [initSt] at h
  comp_down k c u w h := by simp [initSt] at h

end Ix.CompileCert.Canon
