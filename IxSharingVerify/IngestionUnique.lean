import IxSharingVerify.IngestionTable

/-! Initially empty production ingestion supplies complete exact interner
indices and unique term interpretations. This discharges canonicalization's
input Run contract without strengthening the generic ingestion theorem.
Canonical result determinism follows for equal unshared root arrays; term
preservation through renumbering and totality remain separate. -/

namespace Ix.Sharing.Verify.Ingestion

open Ix.Sharing.Exact Ix.Sharing.Verify.SharingExact

/-- Every stored node is indexed at its own position. This is stronger than
sound lookup and implies that duplicate structural nodes cannot be stored. -/
def Complete (state : Interner) : Prop :=
  ∀ index, index < state.nodes.size → state.index.get? state.nodes[index]! = some index

theorem complete_empty : Complete {} := by
  intro index bound
  simp at bound

local instance : LawfulBEq Node where
  eq_of_beq := (Node.beq_iff _ _).mp
  rfl := (Node.beq_iff _ _).mpr rfl

theorem intern_complete (state : Interner) (complete : Complete state) (node : Node) :
    Complete (state.intern node).1 := by
  unfold Interner.intern
  cases found : state.index.get? node with
  | some index => exact complete
  | none =>
    intro index bound
    by_cases old : index < state.nodes.size
    · have different : state.nodes[index]! ≠ node := by
        intro same
        have prior := complete index old
        rw [same, found] at prior
        cases prior
      change (state.index.insert node state.nodes.size).get? ((state.nodes.push node)[index]!) = some index
      rw [(Retains.push state.nodes node).getElem! index old, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      split
      · rename_i same
        exact False.elim (different ((Node.beq_iff _ _).mp same).symm)
      · exact complete index old
    · have last : index = state.nodes.size := by
        change index < (state.nodes.push node).size at bound
        simp only [Array.size_push] at bound
        omega
      subst index
      change (state.index.insert node state.nodes.size).get? ((state.nodes.push node)[state.nodes.size]!) = some state.nodes.size
      rw [push_getElem!]
      simp

theorem Complete.node_injective {state : Interner} (complete : Complete state)
    (left right : Nat) (leftBound : left < state.nodes.size) (rightBound : right < state.nodes.size)
    (same : state.nodes[left]! = state.nodes[right]!) : left = right := by
  have lhs := complete left leftBound
  rw [same, complete right rightBound] at lhs
  exact (Option.some.inj lhs).symm

theorem node_eq (left right : Node) (head : left.head = right.head) (children : left.children = right.children) : left = right := by
  cases left
  cases right
  cases head
  cases children
  rfl

/-- Backward edges and node arities lift structural-node uniqueness to
uniqueness of the denoted expression, including recursively shared children. -/
theorem Complete.term_injective {state : Interner} (complete : Complete state)
    (cp : CP state.nodes) (arity : NodeArity state.nodes) :
    ∀ left, left < state.nodes.size → ∀ right, right < state.nodes.size →
      termOf state.nodes left = termOf state.nodes right → left = right := by
  intro left
  induction left using Nat.strongRecOn with
  | ind left ih =>
    intro leftBound right rightBound same
    have pieces := children_corr cp cp arity arity leftBound rightBound same
    have children : state.nodes[left]!.children = state.nodes[right]!.children := by
      apply Array.ext pieces.2.1
      intro index inLeft inRight
      have leftEarlier := cp left leftBound _ (Array.getElem_mem inLeft)
      have rightEarlier := cp right rightBound _ (Array.getElem_mem inRight)
      exact ih _ leftEarlier (Nat.lt_trans leftEarlier leftBound) _ (Nat.lt_trans rightEarlier rightBound)
        (pieces.2.2 index inLeft inRight)
    apply complete.node_injective left right leftBound rightBound
    exact node_eq _ _ pieces.1 children

def Maintains (action : IngestM α) : Prop :=
  ∀ before, Complete before.interner → ∀ value after,
    action.run before = .ok (value, after) → Complete after.interner

theorem Maintains.pure (value : α) : Maintains (pure value) := by
  intro before complete result after ran
  have same : .ok (value, before) = Except.ok (ε := SharingError) (result, after) := ran
  cases Except.ok.inj same
  exact complete

theorem Maintains.throw (error : SharingError) : Maintains (throw error : IngestM α) := by
  intro before complete result after ran
  change Except.error _ = Except.ok (result, after) at ran
  cases ran

theorem Maintains.bind {action : IngestM α} {next : α → IngestM β}
    (first : Maintains action) (last : ∀ value, Maintains (next value)) : Maintains (action >>= next) := by
  intro before complete result after ran
  obtain ⟨value, middle, firstRan, lastRan⟩ := bind_run ran
  exact last value middle (first before complete value middle firstRan) result after lastRan

theorem Maintains.liftExcept (result : Except SharingError α) : Maintains (Ix.Sharing.Exact.liftExcept result) := by
  cases result with
  | ok value => exact Maintains.pure value
  | error error => exact Maintains.throw error

theorem Maintains.internNode (limits : Limits) (node : Node) : Maintains (internNode limits node) := by
  intro before complete id after ran
  have next := intern_complete before.interner complete node
  rw [internNode_state limits before node id after ran] at next
  exact next

theorem Maintains.cached (limits : Limits) (depth : Nat) (source : Ixon.Expr) (body : IngestM Nat)
    (bodyCorrect : Maintains body) : Maintains (cached limits depth source body) := by
  intro before complete id after ran
  unfold Ix.Sharing.Verify.Ingestion.cached at ran
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at ran
  cases found : before.ptrCache.get? (exprKey source) with
  | some actual =>
    rw [found] at ran
    have same : .ok (actual, before) = Except.ok (ε := SharingError) (id, after) := ran
    cases Except.ok.inj same
    exact complete
  | none =>
    rw [found] at ran
    by_cases deep : depth > limits.maxDepth
    · simp only [deep, ↓reduceIte] at ran
      change Except.error _ = Except.ok (id, after) at ran
      cases ran
    · simp only [deep, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at ran
      cases bumped : bump before.visits 1 limits.maxExprVisits .exprVisits with
      | error error =>
        rw [bumped] at ran
        change Except.error _ = Except.ok (id, after) at ran
        cases ran
      | ok visits =>
        rw [bumped] at ran
        change ((body.run { before with visits }) >>= fun (value, state) =>
          Except.ok (value, { state with ptrCache := state.ptrCache.insert (exprKey source) value })) = .ok (id, after) at ran
        obtain ⟨⟨value, middle⟩, bodyRan, finished⟩ := bind_eq_ok ran
        have kept := bodyCorrect { before with visits } complete value middle bodyRan
        cases Except.ok.inj finished
        exact kept

theorem Maintains.ingestExpr (limits : Limits) (context : ShareCtx) (source : Ixon.Expr) :
    ∀ depth, Maintains (ingestExpr limits context depth source) := by
  induction source
  all_goals
    intro depth
    rw [ingestExpr_eq]
    apply Maintains.cached
    unfold ingestBody
    with_reducible repeat' first
      | exact Maintains.internNode _ _
      | exact Maintains.liftExcept _
      | refine Maintains.bind ?_ (fun _ => ?_)
      | dsimp only
      | apply_assumption

theorem Maintains.walk (limits : Limits) (sources : Array Ixon.Expr) (ctxOf : Nat → Array Nat → ShareCtx)
    (count : Nat) : ∀ index acc, Maintains (walk limits sources ctxOf count index acc) := by
  induction count with
  | zero => intro index acc; exact Maintains.pure acc
  | succ count ih =>
    intro index acc
    exact Maintains.bind (Maintains.ingestExpr limits _ _ 0) (fun id => ih (index + 1) (acc.push id))

theorem Maintains.ingestTable (limits : Limits) (sharing roots : Array Ixon.Expr) (allowShare : Bool) :
    Maintains (ingestTable limits sharing roots allowShare) := by
  rw [ingestTable_eq]
  split
  · exact Maintains.throw _
  · unfold tableBody
    simp only [arrayLoop_eq_walk]
    exact Maintains.bind (Maintains.walk _ _ _ _ _ _) fun _ =>
      Maintains.bind (Maintains.walk _ _ _ _ _ _) fun _ => Maintains.pure _

theorem childrenPrecede_of_cp (nodes : Array Node) (cp : CP nodes) : childrenPrecede nodes = true := by
  unfold childrenPrecede
  rw [Array.all_eq_true]
  intro index bound
  have inRange : index < nodes.size := by simpa using bound
  simp only [Array.getElem_zipIdx, Nat.zero_add]
  rw [Array.all_eq_true]
  intro child childBound
  have earlier := cp index inRange nodes[index].children[child]
    (by simpa only [getElem!_pos nodes index inRange] using Array.getElem_mem childBound)
  simpa using earlier

theorem pairs_right {relation : α → β → Prop} {property : β → Prop}
    (implies : ∀ left right, relation left right → property right)
    {left : List α} {right : List β} (rows : List.Forall₂ relation left right) :
    ∀ value ∈ right, property value := by
  induction rows with
  | nil => intro value member; simp at member
  | cons related _ ih =>
    intro value member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact implies _ _ related
    · exact ih value member

theorem Rows.bounds {context : ShareCtx} {nodes : Array Node} {sources : List Ixon.Expr} {ids : Array Nat}
    (rows : Rows context nodes sources ids) : ∀ id ∈ ids, id < nodes.size := by
  intro id member
  exact pairs_right (fun _ _ meaning => meaning.1) rows id (by simpa using member)

/-- Production ingestion supplies the complete `canonicalize_det` input
contract. Its hash-consing premise follows from executed exact interning. -/
theorem ingestTable_run (limits : Limits) (sharing roots : Array Ixon.Expr) (allowShare : Bool)
    (resolved out : Array Nat) (after : IngestState)
    (ran : (ingestTable limits sharing roots allowShare).run {} = .ok ((resolved, out), after)) :
    Run after.interner.nodes out := by
  have result := ingestTable_initial limits sharing roots allowShare resolved out after ran
  have complete := Maintains.ingestTable limits sharing roots allowShare {} complete_empty (resolved, out) after ran
  refine ⟨childrenPrecede_of_cp _ result.good.cp, result.good.arity, result.roots.bounds, ?_⟩
  intro left right leftReach rightReach same
  exact complete.term_injective result.good.cp result.good.arity left
    (reach_lt result.good.cp result.roots.bounds leftReach) right
    (reach_lt result.good.cp result.roots.bounds rightReach) same

theorem pairs_map {interpret : β → α} {left : List α} {right : List β}
    (rows : List.Forall₂ (fun value id => interpret id = value) left right) : right.map interpret = left := by
  induction rows with
  | nil => rfl
  | cons same _ ih => simp only [List.map_cons, same, ih]

theorem ingestTable_root_terms (limits : Limits) (roots : Array Ixon.Expr)
    (resolved out : Array Nat) (after : IngestState)
    (ran : (ingestTable limits #[] roots false).run {} = .ok ((resolved, out), after)) :
    out.map (termOf after.interner.nodes) = roots := by
  have rows := (ingestTable_unshared limits roots resolved out after ran).2.2
  have terms := pairs_map (pairs_mono (fun _ _ meaning => meaning.2) rows)
  apply Array.toList_inj.mp
  simpa only [Array.toList_map] using terms

/-- Successful ingestion of the same ordered anonymous roots has the same
canonical result, even under different ingestion resource limits. This is
canonical ID determinism; preservation through renumbering is separate. -/
theorem canonicalize_ingested (firstLimits secondLimits : Limits) (roots : Array Ixon.Expr)
    (firstRefs firstIds secondRefs secondIds : Array Nat) (firstState secondState : IngestState)
    (firstRan : (ingestTable firstLimits #[] roots false).run {} = .ok ((firstRefs, firstIds), firstState))
    (secondRan : (ingestTable secondLimits #[] roots false).run {} = .ok ((secondRefs, secondIds), secondState)) :
    canonicalize firstState.interner.nodes firstIds = canonicalize secondState.interner.nodes secondIds := by
  apply canonicalize_det
    (ingestTable_run firstLimits #[] roots false firstRefs firstIds firstState firstRan)
    (ingestTable_run secondLimits #[] roots false secondRefs secondIds secondState secondRan)
  rw [ingestTable_root_terms firstLimits roots firstRefs firstIds firstState firstRan,
    ingestTable_root_terms secondLimits roots secondRefs secondIds secondState secondRan]

end Ix.Sharing.Verify.Ingestion
