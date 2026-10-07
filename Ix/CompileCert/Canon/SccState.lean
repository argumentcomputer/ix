import Ix.Compile.Canon.Graph
import Ix.CompileCert.Canon.QSort
import Batteries.Tactic.OpenPrivate

/-!
# M7 L1, components: Tarjan's state and its operations

`Ix.Compile.Canon.tarjanLoop` runs Tarjan's algorithm with an explicit call stack over
arrays (`TarjanState`). This module reads the state as functions (`ix`, `lw`, `os`: the
discovery number plus one, the low link, the on-stack flag; out-of-range reads give `0`,
`0`, `false`), proves that the state's operations (`visit`, `setLow`, `popComponent`) are
function updates on in-range nodes, and splits one iteration of the loop into its four
cases (`step_*`). `Scc.lean` proves the invariant.
-/

open private Ix.Compile.Canon.TarjanState.popComponent.go from Ix.Compile.Canon.Graph

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon

/-! ## The graph -/

/-- The successors of `v` as the loop reads them. -/
def succs (G : Array (Array Nat)) (v : Nat) : Array Nat := G[v]?.getD #[]

/-- An edge `u → w` when `w` is a successor of `u`. -/
def Edge (G : Array (Array Nat)) (u w : Nat) : Prop := w ∈ succs G u

/-- Reachability (reflexive, transitive closure of `Edge`). -/
inductive Reach (G : Array (Array Nat)) : Nat → Nat → Prop
  | refl (u : Nat) : Reach G u u
  | tail {u v w : Nat} : Reach G u v → Edge G v w → Reach G u w

theorem Reach.trans {G : Array (Array Nat)} {u v w : Nat} (h₁ : Reach G u v) (h₂ : Reach G v w) :
    Reach G u w := by
  induction h₂ with
  | refl => exact h₁
  | tail _ e ih => exact .tail ih e

theorem Reach.single {G : Array (Array Nat)} {u w : Nat} (e : Edge G u w) : Reach G u w :=
  .tail (.refl u) e

/-- The graph's successors are nodes of the graph. -/
def Bounded (G : Array (Array Nat)) : Prop := ∀ v w, Edge G v w → w < G.size

/-! ## The state as functions -/

def ix (st : TarjanState) (v : Nat) : Nat := st.index[v]?.getD 0
def lw (st : TarjanState) (v : Nat) : Nat := st.low[v]?.getD 0
def os (st : TarjanState) (v : Nat) : Bool := st.onStack[v]?.getD false

theorem getD_setIfInBounds {α : Type} {a : Array α} {i j : Nat} {x d : α} (hi : i < a.size) :
    (a.setIfInBounds i x)[j]?.getD d = if j = i then x else a[j]?.getD d := by
  rw [Array.getElem?_setIfInBounds]
  by_cases h : i = j
  · subst h; simp [hi]
  · simp [h, Ne.symm h]

section visit
variable (st : TarjanState) (w : Nat)

theorem visit_index : (st.visit w).index = st.index.set! w st.next := by cases st; rfl
theorem visit_low : (st.visit w).low = st.low.set! w st.next := by cases st; rfl
theorem visit_onStack : (st.visit w).onStack = st.onStack.set! w true := by cases st; rfl
theorem visit_stack : (st.visit w).stack = w :: st.stack := by cases st; rfl
theorem visit_calls : (st.visit w).calls = (w, 0) :: st.calls := by cases st; rfl
theorem visit_next : (st.visit w).next = st.next + 1 := by cases st; rfl
theorem visit_comps : (st.visit w).comps = st.comps := by cases st; rfl
theorem visit_roots : (st.visit w).roots = st.roots := by cases st; rfl
theorem visit_exhausted : (st.visit w).exhausted = st.exhausted := by cases st; rfl

variable {st w}

theorem ix_visit (h : w < st.index.size) (v : Nat) :
    ix (st.visit w) v = if v = w then st.next else ix st v := by
  simp only [ix, visit_index, Array.set!]; exact getD_setIfInBounds h

theorem lw_visit (h : w < st.low.size) (v : Nat) :
    lw (st.visit w) v = if v = w then st.next else lw st v := by
  simp only [lw, visit_low, Array.set!]; exact getD_setIfInBounds h

theorem os_visit (h : w < st.onStack.size) (v : Nat) :
    os (st.visit w) v = if v = w then true else os st v := by
  simp only [os, visit_onStack, Array.set!]; exact getD_setIfInBounds h

end visit

section setLow
variable (st : TarjanState) (u x : Nat)

theorem setLow_index : (st.setLow u x).index = st.index := by cases st; rfl
theorem setLow_low : (st.setLow u x).low = st.low.set! u x := by cases st; rfl
theorem setLow_onStack : (st.setLow u x).onStack = st.onStack := by cases st; rfl
theorem setLow_stack : (st.setLow u x).stack = st.stack := by cases st; rfl
theorem setLow_calls : (st.setLow u x).calls = st.calls := by cases st; rfl
theorem setLow_next : (st.setLow u x).next = st.next := by cases st; rfl
theorem setLow_comps : (st.setLow u x).comps = st.comps := by cases st; rfl
theorem setLow_roots : (st.setLow u x).roots = st.roots := by cases st; rfl
theorem setLow_exhausted : (st.setLow u x).exhausted = st.exhausted := by cases st; rfl

variable {st u x}

theorem lw_setLow (h : u < st.low.size) (v : Nat) :
    lw (st.setLow u x) v = if v = u then x else lw st v := by
  simp only [lw, setLow_low, Array.set!]; exact getD_setIfInBounds h

end setLow

/-! ## Popping a component -/

/-- `popComponent.go` pops the stack down to `v`, collecting the popped nodes and clearing their
flags. -/
theorem popGo_spec (v : Nat) :
    ∀ (pre post : List Nat) (comp : Array Nat) (on : Array Bool), v ∉ pre →
      Ix.Compile.Canon.TarjanState.popComponent.go v (pre ++ v :: post) comp on =
        (post, comp ++ (pre ++ [v]).toArray,
          (pre ++ [v]).foldl (fun on w => on.set! w false) on) := by
  intro pre
  induction pre with
  | nil =>
    intro post comp on _
    simp [Ix.Compile.Canon.TarjanState.popComponent.go]
  | cons x xs ih =>
    intro post comp on hv
    have hxv : (x == v) = false := by
      simp only [List.mem_cons, not_or] at hv
      simpa using Ne.symm hv.1
    simp only [List.cons_append, Ix.Compile.Canon.TarjanState.popComponent.go, hxv,
      Bool.false_eq_true, ↓reduceIte]
    rw [ih post _ _ (fun h => hv (List.mem_cons_of_mem _ h))]
    simp

theorem foldl_set_false_size (l : List Nat) (on : Array Bool) :
    (l.foldl (fun on w => on.set! w false) on).size = on.size := by
  induction l generalizing on with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih]; simp [Array.set!]

theorem foldl_set_false_getD (l : List Nat) (on : Array Bool) (hl : ∀ w ∈ l, w < on.size)
    (u : Nat) : (l.foldl (fun on w => on.set! w false) on)[u]?.getD false =
      if u ∈ l then false else on[u]?.getD false := by
  induction l generalizing on with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun w hw => by simpa [Array.set!] using hl w (List.mem_cons_of_mem _ hw))]
    simp only [Array.set!]
    rw [getD_setIfInBounds (hl x (by simp))]
    by_cases h1 : u ∈ xs
    · simp [h1]
    · by_cases h2 : u = x <;> simp [h1, h2]

/-- Popping down to `v` when the stack is `pre ++ v :: post` with `v` not in `pre`. -/
theorem popComponent_spec (st : TarjanState) (v : Nat) (pre post : List Nat)
    (hs : st.stack = pre ++ v :: post) (hv : v ∉ pre) :
    (st.popComponent v).stack = post ∧
    (st.popComponent v).onStack = (pre ++ [v]).foldl (fun on w => on.set! w false) st.onStack ∧
    (st.popComponent v).comps = st.comps.push ((#[] ++ (pre ++ [v]).toArray).qsort (· < ·)) ∧
    (st.popComponent v).roots = st.roots.push v ∧
    (st.popComponent v).index = st.index ∧ (st.popComponent v).low = st.low ∧
    (st.popComponent v).calls = st.calls ∧ (st.popComponent v).next = st.next ∧
    (st.popComponent v).exhausted = st.exhausted := by
  obtain ⟨index, low, onStack, stack, calls, next, comps, roots, order, exhausted⟩ := st
  simp only at hs
  subst hs
  simp only [TarjanState.popComponent]
  rw [popGo_spec v pre post #[] onStack hv]
  simp

end Ix.CompileCert.Canon
