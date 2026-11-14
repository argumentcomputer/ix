import Aiur.Circuit.MemoTree
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

/-!
# Cycles must be long when depth steps are small

Every edge of a finite graph either lowers a natural rank, or keeps the rank
and lowers a field-valued depth by an integer step in `[1, B]`. A closed walk
keeps its rank, so its steps sum to zero in the field. The shortest closed walk
visits distinct nodes, at most `N` when only `N` nodes have outgoing edges, so
its steps sum to a positive integer at most `N · B`. If no such integer
vanishes in the field there is no cycle.

Over Goldilocks with the row bound `N = 2^39` and gap width `k = 24`
(`B = 2^24`), `N · B = 2^63` is below the characteristic. In characteristic
zero every bound works.
-/

namespace Aiur.Circuit.CycleLength

variable {V : Type}

/-- `w 0 → w 1 → … → w length`, `edge` oriented from caller to callee. -/
def Walk (edge : V → V → Prop) (w : Nat → V) (length : Nat) : Prop :=
  ∀ i < length, edge (w i) (w (i + 1))

theorem walk_of_transGen {edge : V → V → Prop} {u v : V} (path : Relation.TransGen edge u v) :
    ∃ w length, 0 < length ∧ w 0 = u ∧ w length = v ∧ Walk edge w length := by
  induction path with
  | @single b e =>
      refine ⟨fun i => if i = 0 then u else b, 1, Nat.one_pos, by simp, by simp, ?_⟩
      intro i hi
      obtain rfl : i = 0 := by omega
      simpa using e
  | @tail b c _ e ih =>
      obtain ⟨w, length, _, start, finish, walk⟩ := ih
      refine ⟨fun i => if i ≤ length then w i else c, length + 1, by omega, by simpa using start,
        by simp, ?_⟩
      intro i hi
      by_cases last : i = length
      · subst last
        simpa [finish] using e
      · have step := walk i (by omega)
        simpa [show i ≤ length by omega, show i + 1 ≤ length by omega] using step

/-- A shortest closed walk repeats no node, so it is no longer than the set of
nodes with outgoing edges. -/
theorem short_cycle [DecidableEq V] {edge : V → V → Prop} {rows : Finset V}
    (source : ∀ u v, edge u v → u ∈ rows) {u : V} (cycle : Relation.TransGen edge u u) :
    ∃ w length, 0 < length ∧ length ≤ rows.card ∧ w length = w 0 ∧ Walk edge w length := by
  classical
  have closedWalk : ∃ length, 0 < length ∧ ∃ w : Nat → V, w length = w 0 ∧ Walk edge w length := by
    obtain ⟨w, length, positive, start, finish, walk⟩ := walk_of_transGen cycle
    exact ⟨length, positive, w, finish.trans start.symm, walk⟩
  obtain ⟨positive, w, closed, walk⟩ := Nat.find_spec closedWalk
  refine ⟨w, Nat.find closedWalk, positive, ?_, closed, walk⟩
  -- A repeated node would close a strictly shorter walk.
  have shorter (i j : Nat) (before : i < j) (inside : j < Nat.find closedWalk)
      (same : w i = w j) : False := by
    apply Nat.find_min closedWalk (show j - i < Nat.find closedWalk by omega)
    refine ⟨by omega, fun t => w (i + t), ?_, ?_⟩
    · simp only [Nat.add_zero]
      rw [show i + (j - i) = j by omega]
      exact same.symm
    · intro t bound
      have step := walk (i + t) (by omega)
      simpa only [Nat.add_assoc] using step
  have distinct : Set.InjOn w (Finset.range (Nat.find closedWalk) : Set Nat) := by
    intro i hi j hj same
    have hi : i < Nat.find closedWalk := by simpa using hi
    have hj : j < Nat.find closedWalk := by simpa using hj
    by_contra different
    rcases Nat.lt_or_gt_of_ne different with lt | lt
    · exact shorter i j lt hj same
    · exact shorter j i lt hi same.symm
  have maps : Set.MapsTo w (Finset.range (Nat.find closedWalk) : Set Nat) (rows : Set V) := by
    intro i hi
    have hi : i < Nat.find closedWalk := by simpa using hi
    exact source _ _ (walk i hi)
  simpa using Finset.card_le_card_of_injOn w maps distinct

/-- The cycle-length lemma: small depth steps and a row bound exclude cycles. -/
theorem no_cycle {F : Type} [Field F] [DecidableEq V] {edge : V → V → Prop} {rows : Finset V}
    {N B : Nat} (source : ∀ u v, edge u v → u ∈ rows) (card : rows.card ≤ N)
    (rank : V → Nat) (depth : V → F)
    (step : ∀ u v, edge u v → rank v < rank u ∨
      rank v = rank u ∧ ∃ s : Nat, 0 < s ∧ s ≤ B ∧ depth v + (s : F) = depth u)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ N * B → (n : F) ≠ 0) (u : V) :
    ¬ Relation.TransGen edge u u := by
  intro cycle
  obtain ⟨w, length, positive, short, closed, walk⟩ := short_cycle source cycle
  have climb : ∀ i k, i + k ≤ length → rank (w (i + k)) ≤ rank (w i) := by
    intro i k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih =>
        intro bound
        have previous := ih (by omega)
        show rank (w (i + k + 1)) ≤ rank (w i)
        rcases step _ _ (walk (i + k) (by omega)) with lower | ⟨same, _⟩ <;> omega
  -- The walk returns to its rank, so no step lowers it.
  have flat : ∀ i < length, ∃ s : Nat, 0 < s ∧ s ≤ B ∧ depth (w (i + 1)) + (s : F) = depth (w i) := by
    intro i inside
    rcases step _ _ (walk i inside) with lower | ⟨_, steps⟩
    · have first := climb 0 i (by omega)
      have last := climb (i + 1) (length - (i + 1)) (by omega)
      rw [show i + 1 + (length - (i + 1)) = length by omega, closed] at last
      simp only [Nat.zero_add] at first
      omega
    · exact steps
  have total : ∀ m ≤ length, ∃ sum : Nat, m ≤ sum ∧ sum ≤ m * B ∧
      depth (w m) + (sum : F) = depth (w 0) := by
    intro m bound
    induction m with
    | zero => exact ⟨0, le_rfl, by simp, by simp⟩
    | succ m ih =>
        obtain ⟨sum, low, high, equal⟩ := ih (by omega)
        obtain ⟨s, positive, small, lowered⟩ := flat m (by omega)
        refine ⟨sum + s, by omega, ?_, ?_⟩
        · calc sum + s ≤ m * B + B := Nat.add_le_add high small
            _ = (m + 1) * B := by ring
        · rw [← equal, ← lowered]
          push_cast
          ring
  obtain ⟨sum, low, high, equal⟩ := total length le_rfl
  rw [closed] at equal
  apply characteristic sum (by omega)
    (high.trans (Nat.mul_le_mul_right B (short.trans card)))
  simpa using equal

end Aiur.Circuit.CycleLength

namespace Aiur.Circuit

variable {F : Type} {rom : WireROM F}

def RuleInstance.isNode [Field F] {system : System F} : RuleInstance system rom → Bool
  | .node .. => true
  | .table .. => false

variable [Field F] [DecidableEq F] {system : System F} {message : Message F}

/-- The nodes that are trace rows, as opposed to fixed-table claims. -/
def MemoDerivation.rows (graph : MemoDerivation system rom message) : Finset (Fin graph.size) :=
  Finset.univ.filter fun i => (graph.node i).isNode

theorem MemoDerivation.source_row (graph : MemoDerivation system rom message)
    {child parent : Fin graph.size} (dependency : graph.Dependency child parent) :
    parent ∈ graph.rows := by
  obtain ⟨j, _⟩ := dependency
  simp only [MemoDerivation.rows, Finset.mem_filter, Finset.mem_univ, true_and]
  cases node : graph.node parent with
  | node => rfl
  | table =>
      have bound := j.isLt
      simp [node, RuleInstance.premises] at bound

/-- A memo graph whose references lower a rank, or keep it and lower a depth
word by a small positive step, is acyclic once it has few enough rows. -/
theorem MemoDerivation.acyclic_of_steps (graph : MemoDerivation system rom message)
    {N B : Nat} (card : graph.rows.card ≤ N)
    (rank : Fin graph.size → Nat) (depth : Fin graph.size → F)
    (step : ∀ i j, rank (graph.target i j) < rank i ∨
      rank (graph.target i j) = rank i ∧
        ∃ s : Nat, 0 < s ∧ s ≤ B ∧ depth (graph.target i j) + (s : F) = depth i)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ N * B → (n : F) ≠ 0) : graph.Acyclic := by
  intro i cycle
  refine CycleLength.no_cycle (edge := Function.swap graph.Dependency) (rows := graph.rows)
    (fun u v dependency => graph.source_row dependency) card rank depth ?_ characteristic i cycle.swap
  rintro u v ⟨j, rfl⟩
  exact step u j

end Aiur.Circuit
