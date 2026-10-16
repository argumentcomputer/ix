import IxSharingVerify.SharingExactCanon
import IxSharingVerify.ExprCache

/-! Actual sharing ingestion preserves expression meaning under a sound
interner and expression cache. This covers every expression constructor and
resource-checked cache/miss path. Initially empty unshared runs return a node
denoting exactly the source expression. Table/root loop composition, DAG
canonicalization, the certified reader and all-input success remain separate. -/

namespace Ix.Sharing.Verify.Ingestion

open Ix.Sharing.Exact Ix.Sharing.Verify.SharingExact

def Retains (before after : Array Node) : Prop :=
  ∀ (index : Nat) (node : Node), before[index]? = some node → after[index]? = some node

theorem Retains.refl (nodes : Array Node) : Retains nodes nodes := fun _ _ found => found

theorem Retains.trans {before middle after : Array Node} (first : Retains before middle)
    (last : Retains middle after) : Retains before after :=
  fun index node found => last index node (first index node found)

theorem Retains.push (nodes : Array Node) (node : Node) : Retains nodes (nodes.push node) := by
  intro index value found
  have bound := (Array.getElem?_eq_some_iff.mp found).1
  rw [Array.getElem?_push_lt bound]
  rw [Array.getElem?_eq_getElem bound] at found
  exact found

theorem Retains.getElem! {before after : Array Node} (keeps : Retains before after)
    (index : Nat) (bound : index < before.size) : after[index]! = before[index]! := by
  have found := keeps index before[index] (Array.getElem?_eq_getElem bound)
  have parts := Array.getElem?_eq_some_iff.mp found
  rw [getElem!_pos before index bound, getElem!_pos after index parts.1]
  exact parts.2

/-- Appending interned nodes cannot change any earlier term's interpretation.
The recursive interpretation already checks backward edges, so this frame
requires no extra well-formedness assumption on existing nodes. -/
theorem termOf_retains {before after : Array Node} (keeps : Retains before after)
    (index : Nat) (bound : index < before.size) : termOf after index = termOf before index := by
  induction index using Nat.strongRecOn with
  | ind index ih =>
    rw [termOf_eq, termOf_eq, keeps.getElem! index bound]
    apply congrArg (before[index]!).toExpr
    funext child
    by_cases earlier : child < index
    · simp only [earlier, ↓reduceIte]
      exact ih child earlier (Nat.lt_trans earlier bound)
    · simp only [earlier, ↓reduceIte]

def IndexSound (state : Interner) : Prop :=
  ∀ node index, state.index.get? node = some index → state.nodes[index]? = some node

theorem index_empty : IndexSound {} := by
  intro node index found
  simp at found

local instance : LawfulBEq Node where
  eq_of_beq := (Node.beq_iff _ _).mp
  rfl := (Node.beq_iff _ _).mpr rfl

theorem intern_correct (before : Interner) (sound : IndexSound before) (node : Node) :
    let result := before.intern node
    IndexSound result.1 ∧ Retains before.nodes result.1.nodes ∧ result.1.nodes[result.2]? = some node := by
  unfold Interner.intern
  cases found : before.index.get? node with
  | some index => exact ⟨sound, Retains.refl _, sound node index found⟩
  | none =>
    refine ⟨?_, Retains.push _ _, Array.getElem?_push_size⟩
    intro query index got
    change (before.index.insert node before.nodes.size)[query]? = some index at got
    rw [Std.HashMap.getElem?_insert] at got
    split at got
    · rename_i equal
      have same : node = query := (Node.beq_iff _ _).mp equal
      cases same
      cases Option.some.inj got
      exact Array.getElem?_push_size
    · exact Retains.push _ _ _ _ (sound query index got)

/-- The executed node interner preserves its index invariant and every old
node interpretation. This uses its actual successful result, including the
resource guard, without assuming a hash is an injective encoding. -/
theorem internNode_correct (limits : Limits) (before : IngestState)
    (sound : IndexSound before.interner) (node : Node) (id : Nat) (after : IngestState)
    (ran : (internNode limits node).run before = .ok (id, after)) :
    IndexSound after.interner ∧ Retains before.interner.nodes after.interner.nodes ∧
      after.interner.nodes[id]? = some node ∧ after.ptrCache = before.ptrCache ∧
      after.visits = before.visits := by
  have facts := intern_correct before.interner sound node
  unfold internNode at ran
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at ran
  cases step : before.interner.intern node with
  | mk interner actual =>
    rw [step] at ran facts
    by_cases large : interner.nodes.size > limits.maxNodes
    · simp only [large, ↓reduceIte] at ran
      change Except.error _ = Except.ok (id, after) at ran
      cases ran
    · simp only [large, ↓reduceIte] at ran
      have same : .ok (actual, { before with interner }) = Except.ok (ε := SharingError) (id, after) := ran
      cases Except.ok.inj same
      exact ⟨facts.1, facts.2.1, facts.2.2, rfl, rfl⟩

theorem internNode_retains_meaning (limits : Limits) (before : IngestState)
    (sound : IndexSound before.interner) (node : Node) (id : Nat) (after : IngestState)
    (ran : (internNode limits node).run before = .ok (id, after))
    (old : Nat) (bound : old < before.interner.nodes.size) :
    termOf after.interner.nodes old = termOf before.interner.nodes old :=
  termOf_retains (internNode_correct limits before sound node id after ran).2.1 old bound

theorem toExpr_congr (node : Node) (first second : Nat → Ixon.Expr)
    (same : ∀ index, index < node.head.arity → first (node.child index) = second (node.child index)) :
    node.toExpr first = node.toExpr second := by
  cases head : node.head <;> simp only [Node.toExpr, head]
  all_goals try rfl
  all_goals
    congr 1
    all_goals apply same; simp only [head, Head.arity]; decide

theorem termOf_node (nodes : Array Node) (index : Nat) (node : Node)
    (found : nodes[index]? = some node) (arity : node.children.size = node.head.arity)
    (earlier : ∀ child ∈ node.children, child < index) :
    termOf nodes index = node.toExpr (termOf nodes) := by
  have slot := Array.getElem?_eq_some_iff.mp found
  rw [termOf_eq, getElem!_pos nodes index slot.1, slot.2]
  apply toExpr_congr
  intro child bounded
  have inBounds : child < node.children.size := by omega
  have edge := earlier node.children[child] (Array.getElem_mem inBounds)
  rw [child_eq_getElem node child inBounds]
  simp only [edge, ↓reduceIte]

theorem node_reify_retains {before after : Array Node} (keeps : Retains before after) (node : Node)
    (arity : node.children.size = node.head.arity)
    (children : ∀ child ∈ node.children, child < before.size) :
    node.toExpr (termOf after) = node.toExpr (termOf before) := by
  apply toExpr_congr
  intro child bound
  have inBounds : child < node.children.size := by omega
  rw [child_eq_getElem node child inBounds]
  exact termOf_retains keeps _ (children _ (Array.getElem_mem inBounds))

theorem push_getElem! (nodes : Array Node) (node : Node) : (nodes.push node)[nodes.size]! = node := by simp

theorem cp_push (nodes : Array Node) (cp : CP nodes) (node : Node)
    (children : ∀ child ∈ node.children, child < nodes.size) : CP (nodes.push node) := by
  intro index bound child member
  by_cases old : index < nodes.size
  · rw [(Retains.push nodes node).getElem! index old] at member
    exact cp index old child member
  · have slot : index = nodes.size := by simp only [Array.size_push] at bound; omega
    subst index
    rw [push_getElem!] at member
    exact children child member

theorem arity_push (nodes : Array Node) (arity : NodeArity nodes) (node : Node)
    (shape : node.children.size = node.head.arity) : NodeArity (nodes.push node) := by
  intro index bound
  by_cases old : index < nodes.size
  · rw [(Retains.push nodes node).getElem! index old]
    exact arity index old
  · have slot : index = nodes.size := by simp only [Array.size_push] at bound; omega
    subst index
    rw [push_getElem!]
    exact shape

/-- The actual interner returns a node interpreting as the requested head over
the already interpreted children, and preserves backward edges and arities. -/
theorem intern_meaning (before : Interner) (sound : IndexSound before)
    (cp : CP before.nodes) (arities : NodeArity before.nodes) (node : Node)
    (arity : node.children.size = node.head.arity)
    (children : ∀ child ∈ node.children, child < before.nodes.size) :
    let result := before.intern node
    CP result.1.nodes ∧ NodeArity result.1.nodes ∧
      termOf result.1.nodes result.2 = node.toExpr (termOf before.nodes) := by
  unfold Interner.intern
  cases found : before.index.get? node with
  | some index =>
    refine ⟨cp, arities, termOf_node before.nodes index node (sound node index found) arity ?_⟩
    intro child member
    have slot := Array.getElem?_eq_some_iff.mp (sound node index found)
    exact cp index slot.1 child (by simpa only [getElem!_pos before.nodes index slot.1, slot.2] using member)
  | none =>
    refine ⟨cp_push _ cp _ children, arity_push _ arities _ arity, ?_⟩
    rw [termOf_node _ _ node Array.getElem?_push_size arity children]
    exact node_reify_retains (Retains.push _ _) node arity children

def SharesValid (context : ShareCtx) : Ixon.Expr → Prop
  | .share index => ∃ id, resolveShare context index = .ok id
  | .prj _ _ value => SharesValid context value
  | .app fn arg | .lam _ fn arg | .all _ _ fn arg => SharesValid context fn ∧ SharesValid context arg
  | .letE _ type value body => SharesValid context type ∧ SharesValid context value ∧ SharesValid context body
  | _ => True

def ResolvedBounded (context : ShareCtx) (nodes : Array Node) : Prop :=
  ∀ (index id : Nat), context.resolved[index]? = some id → id < nodes.size

def expansion (context : ShareCtx) (nodes : Array Node) (index : Nat) : Ixon.Expr :=
  match context.resolved[index]? with
  | some id => termOf nodes id
  | none => default

def Represents (context : ShareCtx) (nodes : Array Node) (source : Ixon.Expr) (id : Nat) : Prop :=
  id < nodes.size ∧ SharesValid context source ∧ termOf nodes id = substShares (expansion context nodes) source

theorem Retains.bound {before after : Array Node} (keeps : Retains before after)
    (index : Nat) (bound : index < before.size) : index < after.size :=
  (Array.getElem?_eq_some_iff.mp (keeps index before[index] (Array.getElem?_eq_getElem bound))).1

theorem resolved_grows {before after : Array Node} (keeps : Retains before after)
    (context : ShareCtx) (bounded : ResolvedBounded context before) : ResolvedBounded context after :=
  fun index id found => keeps.bound id (bounded index id found)

theorem expansion_grows {before after : Array Node} (keeps : Retains before after)
    (context : ShareCtx) (bounded : ResolvedBounded context before) :
    expansion context after = expansion context before := by
  funext index
  unfold expansion
  cases found : context.resolved[index]? with
  | none => rfl
  | some id => exact termOf_retains keeps id (bounded index id found)

theorem represents_grows {before after : Array Node} (keeps : Retains before after)
    (context : ShareCtx) (bounded : ResolvedBounded context before)
    {source : Ixon.Expr} {id : Nat} (meaning : Represents context before source id) :
    Represents context after source id := by
  refine ⟨keeps.bound id meaning.1, meaning.2.1, ?_⟩
  rw [termOf_retains keeps id meaning.1, expansion_grows keeps context bounded]
  exact meaning.2.2

structure Good (context : ShareCtx) (state : IngestState) : Prop where
  index : IndexSound state.interner
  cp : CP state.interner.nodes
  arity : NodeArity state.interner.nodes
  resolved : ResolvedBounded context state.interner.nodes
  cache : ExprCache.Sound (Represents context state.interner.nodes) state.ptrCache

theorem Good.visits {context : ShareCtx} {state : IngestState} (good : Good context state) (visits : Nat) :
    Good context { state with visits } :=
  ⟨good.index, good.cp, good.arity, good.resolved, good.cache⟩

theorem Good.cache_insert {context : ShareCtx} {state : IngestState} (good : Good context state)
    (source : Ixon.Expr) (id : Nat) (meaning : Represents context state.interner.nodes source id) :
    Good context { state with ptrCache := state.ptrCache.insert (exprKey source) id } :=
  ⟨good.index, good.cp, good.arity, good.resolved, ExprCache.sound_insert good.cache (exprKey source) id meaning⟩

theorem internNode_state (limits : Limits) (before : IngestState) (node : Node) (id : Nat) (after : IngestState)
    (ran : (internNode limits node).run before = .ok (id, after)) :
    before.interner.intern node = (after.interner, id) := by
  unfold internNode at ran
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at ran
  cases step : before.interner.intern node with
  | mk interner actual =>
    rw [step] at ran
    by_cases large : interner.nodes.size > limits.maxNodes
    · simp only [large, ↓reduceIte] at ran
      change Except.error _ = Except.ok (id, after) at ran
      cases ran
    · simp only [large, ↓reduceIte] at ran
      have same : .ok (actual, { before with interner }) = Except.ok (ε := SharingError) (id, after) := ran
      cases Except.ok.inj same
      rfl

theorem internNode_good (limits : Limits) (context : ShareCtx) (before : IngestState)
    (good : Good context before) (node : Node)
    (arity : node.children.size = node.head.arity)
    (children : ∀ child ∈ node.children, child < before.interner.nodes.size)
    (id : Nat) (after : IngestState) (ran : (internNode limits node).run before = .ok (id, after)) :
    Good context after ∧ Retains before.interner.nodes after.interner.nodes ∧ id < after.interner.nodes.size ∧
      termOf after.interner.nodes id = node.toExpr (termOf before.interner.nodes) := by
  have facts := internNode_correct limits before good.index node id after ran
  have meaning := intern_meaning before.interner good.index good.cp good.arity node arity children
  rw [internNode_state limits before node id after ran] at meaning
  refine ⟨⟨facts.1, meaning.1, meaning.2.1, resolved_grows facts.2.1 context good.resolved, ?_⟩,
    facts.2.1, (Array.getElem?_eq_some_iff.mp facts.2.2.1).1, meaning.2.2⟩
  rw [facts.2.2.2.1]
  exact good.cache.mono (fun _ _ prior => represents_grows facts.2.1 context good.resolved prior)

def Checked (context : ShareCtx) (source : Ixon.Expr) (action : IngestM Nat) : Prop :=
  ∀ before, Good context before → ∀ id after, action.run before = .ok (id, after) →
    Good context after ∧ Retains before.interner.nodes after.interner.nodes ∧
      Represents context after.interner.nodes source id

theorem bind_run {action : IngestM α} {next : α → IngestM β} {before after : IngestState} {result : β}
    (ran : (action >>= next).run before = .ok (result, after)) :
    ∃ value middle, action.run before = .ok (value, middle) ∧ (next value).run middle = .ok (result, after) := by
  rw [StateT.run_bind] at ran
  obtain ⟨⟨value, middle⟩, first, last⟩ := bind_eq_ok ran
  exact ⟨value, middle, first, last⟩

def cached (limits : Limits) (depth : Nat) (source : Ixon.Expr) (body : IngestM Nat) : IngestM Nat := do
  let ptr := exprKey source
  match (← get).ptrCache.get? ptr with
  | some id => return id
  | none =>
    if depth > limits.maxDepth then throw (.resourceExhausted .depth limits.maxDepth)
    let state ← get
    let visits ← Ix.Sharing.Exact.liftExcept (bump state.visits 1 limits.maxExprVisits .exprVisits)
    set { state with visits }
    let id ← body
    modify fun state => { state with ptrCache := state.ptrCache.insert ptr id }
    return id

theorem cached_checked (context : ShareCtx) (source : Ixon.Expr) (body : IngestM Nat)
    (correct : Checked context source body) (limits : Limits) (depth : Nat) :
    Checked context source (cached limits depth source body) := by
  intro before good id after ran
  unfold cached at ran
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at ran
  cases found : before.ptrCache.get? (exprKey source) with
  | some actual =>
    rw [found] at ran
    have same : .ok (actual, before) = Except.ok (ε := SharingError) (id, after) := ran
    cases Except.ok.inj same
    exact ⟨good, Retains.refl _, ExprCache.lookup_sound good.cache (exprKey source) _ found⟩
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
        have checked := correct { before with visits } (good.visits visits) value middle bodyRan
        cases Except.ok.inj finished
        exact ⟨checked.1.cache_insert source _ checked.2.2, checked.2.1, checked.2.2⟩

def ingestBody (next : Ixon.Expr → IngestM Nat) (limits : Limits) (context : ShareCtx) : Ixon.Expr → IngestM Nat
  | .sort index => internNode limits ⟨.sort index, #[]⟩
  | .var index => internNode limits ⟨.var index, #[]⟩
  | .ref index levels => internNode limits ⟨.ref index levels, #[]⟩
  | .recur index levels => internNode limits ⟨.recur index levels, #[]⟩
  | .prj index field value => do
    let id ← next value
    internNode limits ⟨.prj index field, #[id]⟩
  | .str index => internNode limits ⟨.str index, #[]⟩
  | .nat index => internNode limits ⟨.nat index, #[]⟩
  | .app fn arg => do
    let first ← next fn
    let second ← next arg
    internNode limits ⟨.app, #[first, second]⟩
  | .lam contract type body => do
    let first ← next type
    let second ← next body
    internNode limits ⟨.lam contract, #[first, second]⟩
  | .all contract result type body => do
    let first ← next type
    let second ← next body
    internNode limits ⟨.all contract result, #[first, second]⟩
  | .letE contract type value body => do
    let first ← next type
    let second ← next value
    let third ← next body
    internNode limits ⟨.letE contract, #[first, second, third]⟩
  | .share index => Ix.Sharing.Exact.liftExcept (resolveShare context index)

theorem ingestExpr_eq (limits : Limits) (context : ShareCtx) (depth : Nat) (source : Ixon.Expr) :
    ingestExpr limits context depth source = cached limits depth source
      (ingestBody (ingestExpr limits context (depth + 1)) limits context source) := by
  rw [ingestExpr]
  cases source <;> simp only [cached, ingestBody, bind_assoc]
  all_goals rfl

theorem finish_node (limits : Limits) (context : ShareCtx) (source : Ixon.Expr)
    (before : IngestState) (good : Good context before) (node : Node)
    (arity : node.children.size = node.head.arity)
    (children : ∀ child ∈ node.children, child < before.interner.nodes.size)
    (valid : SharesValid context source)
    (meaning : node.toExpr (termOf before.interner.nodes) = substShares (expansion context before.interner.nodes) source)
    (id : Nat) (after : IngestState) (ran : (internNode limits node).run before = .ok (id, after)) :
    Good context after ∧ Retains before.interner.nodes after.interner.nodes ∧
      Represents context after.interner.nodes source id := by
  have checked := internNode_good limits context before good node arity children id after ran
  refine ⟨checked.1, checked.2.1, checked.2.2.1, valid, ?_⟩
  rw [checked.2.2.2, expansion_grows checked.2.1 context good.resolved]
  exact meaning

theorem unary_checked (context : ShareCtx) (limits : Limits) (source child : Ixon.Expr)
    (action : IngestM Nat) (correct : Checked context child action) (head : Head) (arity : head.arity = 1)
    (shape : ∀ nodes id, Represents context nodes child id → SharesValid context source ∧
      (Node.mk head #[id]).toExpr (termOf nodes) = substShares (expansion context nodes) source) :
    Checked context source (do let id ← action; internNode limits ⟨head, #[id]⟩) := by
  intro before good id after ran
  obtain ⟨childId, middle, childRan, nodeRan⟩ := bind_run ran
  have checked := correct before good childId middle childRan
  have shaped := shape middle.interner.nodes childId checked.2.2
  have finished := finish_node limits context source middle checked.1 ⟨head, #[childId]⟩
    (by simpa using arity.symm) (by intro item member; simp at member; subst item; exact checked.2.2.1)
    shaped.1 shaped.2 id after nodeRan
  exact ⟨finished.1, checked.2.1.trans finished.2.1, finished.2.2⟩

theorem pair_checked (context : ShareCtx) (limits : Limits) (source left right : Ixon.Expr)
    (first second : IngestM Nat) (leftCorrect : Checked context left first) (rightCorrect : Checked context right second)
    (head : Head) (arity : head.arity = 2)
    (shape : ∀ nodes leftId rightId, Represents context nodes left leftId → Represents context nodes right rightId →
      SharesValid context source ∧ (Node.mk head #[leftId, rightId]).toExpr (termOf nodes) =
        substShares (expansion context nodes) source) :
    Checked context source (do let leftId ← first; let rightId ← second; internNode limits ⟨head, #[leftId, rightId]⟩) := by
  intro before good id after ran
  obtain ⟨leftId, middle, firstRan, tail⟩ := bind_run ran
  obtain ⟨rightId, compiled, secondRan, nodeRan⟩ := bind_run tail
  have firstChecked := leftCorrect before good leftId middle firstRan
  have secondChecked := rightCorrect middle firstChecked.1 rightId compiled secondRan
  have retained := represents_grows secondChecked.2.1 context firstChecked.1.resolved firstChecked.2.2
  have shaped := shape compiled.interner.nodes leftId rightId retained secondChecked.2.2
  have finished := finish_node limits context source compiled secondChecked.1 ⟨head, #[leftId, rightId]⟩
    (by simpa using arity.symm) (by
      intro item member
      simp at member
      rcases member with rfl | rfl
      · exact retained.1
      · exact secondChecked.2.2.1)
    shaped.1 shaped.2 id after nodeRan
  exact ⟨finished.1, firstChecked.2.1.trans (secondChecked.2.1.trans finished.2.1), finished.2.2⟩

theorem triple_checked (context : ShareCtx) (limits : Limits) (source a b c : Ixon.Expr)
    (first second third : IngestM Nat)
    (firstCorrect : Checked context a first) (secondCorrect : Checked context b second) (thirdCorrect : Checked context c third)
    (head : Head) (arity : head.arity = 3)
    (shape : ∀ nodes aId bId cId, Represents context nodes a aId → Represents context nodes b bId → Represents context nodes c cId →
      SharesValid context source ∧ (Node.mk head #[aId, bId, cId]).toExpr (termOf nodes) =
        substShares (expansion context nodes) source) :
    Checked context source (do let aId ← first; let bId ← second; let cId ← third; internNode limits ⟨head, #[aId, bId, cId]⟩) := by
  intro before good id after ran
  obtain ⟨aId, firstState, firstRan, tail⟩ := bind_run ran
  obtain ⟨bId, secondState, secondRan, tail⟩ := bind_run tail
  obtain ⟨cId, compiled, thirdRan, nodeRan⟩ := bind_run tail
  have one := firstCorrect before good aId firstState firstRan
  have two := secondCorrect firstState one.1 bId secondState secondRan
  have three := thirdCorrect secondState two.1 cId compiled thirdRan
  have aRead := represents_grows (two.2.1.trans three.2.1) context one.1.resolved one.2.2
  have bRead := represents_grows three.2.1 context two.1.resolved two.2.2
  have shaped := shape compiled.interner.nodes aId bId cId aRead bRead three.2.2
  have finished := finish_node limits context source compiled three.1 ⟨head, #[aId, bId, cId]⟩
    (by simpa using arity.symm) (by
      intro item member
      simp at member
      rcases member with rfl | rfl | rfl
      · exact aRead.1
      · exact bRead.1
      · exact three.2.2.1)
    shaped.1 shaped.2 id after nodeRan
  exact ⟨finished.1, one.2.1.trans (two.2.1.trans (three.2.1.trans finished.2.1)), finished.2.2⟩

theorem resolveShare_slot (context : ShareCtx) (index : UInt64) (id : Nat)
    (success : resolveShare context index = .ok id) : context.resolved[index.toNat]? = some id := by
  unfold resolveShare at success
  split at success
  · cases success
  · cases slot : context.resolved[index.toNat]? with
    | some actual => simp only [slot] at success; cases Except.ok.inj success; rfl
    | none =>
      rw [slot] at success
      cases entry : context.entry with
      | none => rw [entry] at success; cases success
      | some position =>
        rw [entry] at success
        by_cases inside : index.toNat < context.tableSize <;> simp [inside] at success

theorem share_checked (context : ShareCtx) (index : UInt64) :
    Checked context (.share index) (Ix.Sharing.Exact.liftExcept (resolveShare context index)) := by
  intro before good id after ran
  cases resolved : resolveShare context index with
  | error error =>
    rw [resolved] at ran
    change Except.error _ = Except.ok (id, after) at ran
    cases ran
  | ok actual =>
    rw [resolved] at ran
    have same : .ok (actual, before) = Except.ok (ε := SharingError) (id, after) := ran
    cases Except.ok.inj same
    have slot := resolveShare_slot context index _ resolved
    refine ⟨good, Retains.refl _, good.resolved _ _ slot, ⟨_, resolved⟩, ?_⟩
    simp only [substShares, expansion, slot]

/-- The actual recursive ingestion preserves the meaning of every expression,
including sharing references, under a valid interner and cache. All constructor
steps and cache hits are discharged; no pointer-injectivity premise is used. -/
theorem ingestExpr_checked (limits : Limits) (context : ShareCtx) (depth : Nat) (source : Ixon.Expr) :
    Checked context source (ingestExpr limits context depth source) := by
  rw [ingestExpr_eq]
  apply cached_checked
  cases source
  all_goals unfold ingestBody
  all_goals dsimp only
  all_goals try
    intro before good id after ran
    apply finish_node limits context _ before good _ _ _ _ _ id after ran
    all_goals first | rfl | trivial | simp
  case prj index field value =>
    apply unary_checked context limits _ value _ (ingestExpr_checked limits context (depth + 1) value) (.prj index field) rfl
    intro nodes id meaning
    refine ⟨meaning.2.1, ?_⟩
    simp [Node.toExpr, Node.child, substShares, meaning.2.2]
  case app fn arg =>
    apply pair_checked context limits _ fn arg _ _
      (ingestExpr_checked limits context (depth + 1) fn) (ingestExpr_checked limits context (depth + 1) arg) .app rfl
    intro nodes leftId rightId left right
    refine ⟨⟨left.2.1, right.2.1⟩, ?_⟩
    simp [Node.toExpr, Node.child, substShares, left.2.2, right.2.2]
  case lam contract type body =>
    apply pair_checked context limits _ type body _ _
      (ingestExpr_checked limits context (depth + 1) type) (ingestExpr_checked limits context (depth + 1) body) (.lam contract) rfl
    intro nodes leftId rightId left right
    refine ⟨⟨left.2.1, right.2.1⟩, ?_⟩
    simp [Node.toExpr, Node.child, substShares, left.2.2, right.2.2]
  case all contract result type body =>
    apply pair_checked context limits _ type body _ _
      (ingestExpr_checked limits context (depth + 1) type) (ingestExpr_checked limits context (depth + 1) body) (.all contract result) rfl
    intro nodes leftId rightId left right
    refine ⟨⟨left.2.1, right.2.1⟩, ?_⟩
    simp [Node.toExpr, Node.child, substShares, left.2.2, right.2.2]
  case letE contract type value body =>
    apply triple_checked context limits _ type value body _ _ _
      (ingestExpr_checked limits context (depth + 1) type) (ingestExpr_checked limits context (depth + 1) value)
      (ingestExpr_checked limits context (depth + 1) body) (.letE contract) rfl
    intro nodes typeId valueId bodyId typeRead valueRead bodyRead
    refine ⟨⟨typeRead.2.1, valueRead.2.1, bodyRead.2.1⟩, ?_⟩
    simp [Node.toExpr, Node.child, substShares, typeRead.2.2, valueRead.2.2, bodyRead.2.2]
  case share index => exact share_checked context index
termination_by source

theorem good_initial (context : ShareCtx) (empty : context.resolved = #[]) : Good context {} := by
  refine ⟨index_empty, ?_, ?_, ?_, ExprCache.sound_empty _⟩
  · intro index bound
    simp at bound
  · intro index bound
    simp at bound
  · intro index id found
    simp [empty] at found

/-- A successful unshared-input walk has no hidden Share leaves; substitution
is the identity as a consequence of the checked source validity predicate. -/
theorem SharesValid.unshared {context : ShareCtx} (unshared : context.allowShare = false)
    (source : Ixon.Expr) (valid : SharesValid context source) (replacement : Nat → Ixon.Expr) :
    substShares replacement source = source := by
  induction source with
  | share index =>
    obtain ⟨id, resolved⟩ := valid
    simp [resolveShare, unshared] at resolved
  | prj index field value ih => exact congrArg (Ixon.Expr.prj index field) (ih valid)
  | app fn arg ihf iha => simp only [substShares, ihf valid.1, iha valid.2]
  | lam contract type body iht ihb => simp only [substShares, iht valid.1, ihb valid.2]
  | all contract result type body iht ihb => simp only [substShares, iht valid.1, ihb valid.2]
  | letE contract type value body iht ihv ihb =>
    simp only [substShares, iht valid.1, ihv valid.2.1, ihb valid.2.2]
  | _ => rfl

/-- Direct source preservation from the actual initially empty ingestion run.
No source shape, cache correctness or successful-output certificate is assumed. -/
theorem ingestExpr_initial (limits : Limits) (context : ShareCtx)
    (empty : context.resolved = #[]) (unshared : context.allowShare = false)
    (source : Ixon.Expr) (id : Nat) (after : IngestState)
    (ran : (ingestExpr limits context 0 source).run {} = .ok (id, after)) :
    Good context after ∧ id < after.interner.nodes.size ∧ termOf after.interner.nodes id = source := by
  have checked := ingestExpr_checked limits context 0 source {} (good_initial context empty) id after ran
  exact ⟨checked.1, checked.2.2.1,
    checked.2.2.2.2.trans (SharesValid.unshared unshared source checked.2.2.2.1 _)⟩

end Ix.Sharing.Verify.Ingestion
