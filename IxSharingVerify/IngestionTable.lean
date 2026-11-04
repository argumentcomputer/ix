import IxSharingVerify.Ingestion

/-! The actual indexed sharing-entry and root loops preserve source
meaning and order. Successful execution supplies backward-reference validity
and the table capacity bound. Re-expansion against an existing DAG preserves
its original terms. Canonical numbering and certified-reader composition
remain separate obligations. -/

namespace Ix.Sharing.Verify.Ingestion

open Ix.Sharing.Exact Ix.Sharing.Verify.SharingExact

/-- Only successful Share resolution is observable in a cached expression.
The error-reporting entry/root fields may change between loop iterations. -/
def ContextExtends (before after : ShareCtx) : Prop :=
  ∀ index id, resolveShare before index = .ok id → resolveShare after index = .ok id

def RefRetains (before after : Array Nat) : Prop :=
  ∀ (index id : Nat), before[index]? = some id → after[index]? = some id

theorem RefRetains.refl (refs : Array Nat) : RefRetains refs refs := fun _ _ found => found

theorem RefRetains.push (refs : Array Nat) (id : Nat) : RefRetains refs (refs.push id) := by
  intro index value found
  have bound := (Array.getElem?_eq_some_iff.mp found).1
  rw [Array.getElem?_push_lt bound]
  rw [Array.getElem?_eq_getElem bound] at found
  exact found

theorem context_extends {before after : ShareCtx} (mode : after.allowShare = before.allowShare)
    (refs : RefRetains before.resolved after.resolved) : ContextExtends before after := by
  intro index id success
  have slot := resolveShare_slot before index id success
  have allows : before.allowShare = true := by
    cases chosen : before.allowShare with
    | true => rfl
    | false => simp [resolveShare, chosen] at success
  simp [resolveShare, mode, allows, refs _ _ slot]

theorem SharesValid.context {before after : ShareCtx} (growth : ContextExtends before after)
    (source : Ixon.Expr) (valid : SharesValid before source) : SharesValid after source := by
  induction source with
  | share index => obtain ⟨id, found⟩ := valid; exact ⟨id, growth index id found⟩
  | prj _ _ _ ih => exact ih valid
  | app _ _ ihf iha | lam _ _ _ ihf iha | all _ _ _ _ ihf iha => exact ⟨ihf valid.1, iha valid.2⟩
  | letE _ _ _ _ iht ihv ihb => exact ⟨iht valid.1, ihv valid.2.1, ihb valid.2.2⟩
  | _ => trivial

theorem SharesValid.expansion_context {before after : ShareCtx} (growth : ContextExtends before after)
    (source : Ixon.Expr) (valid : SharesValid before source) (nodes : Array Node) :
    substShares (expansion after nodes) source = substShares (expansion before nodes) source := by
  induction source with
  | share index =>
    obtain ⟨id, found⟩ := valid
    simp only [substShares, expansion, resolveShare_slot before index id found,
      resolveShare_slot after index id (growth index id found)]
  | prj _ _ _ ih => simp only [substShares, ih valid]
  | app _ _ ihf iha | lam _ _ _ ihf iha | all _ _ _ _ ihf iha =>
    simp only [substShares, ihf valid.1, iha valid.2]
  | letE _ _ _ _ iht ihv ihb => simp only [substShares, iht valid.1, ihv valid.2.1, ihb valid.2.2]
  | _ => rfl

theorem Represents.context {before after : ShareCtx} (growth : ContextExtends before after)
    {nodes : Array Node} {source : Ixon.Expr} {id : Nat} (meaning : Represents before nodes source id) :
    Represents after nodes source id := by
  refine ⟨meaning.1, meaning.2.1.context growth source, ?_⟩
  rw [meaning.2.1.expansion_context growth source nodes]
  exact meaning.2.2

theorem Good.context {before after : ShareCtx} (growth : ContextExtends before after)
    {state : IngestState} (good : Good before state) (bounded : ResolvedBounded after state.interner.nodes) :
    Good after state :=
  ⟨good.index, good.cp, good.arity, bounded, good.cache.mono (fun _ _ meaning => meaning.context growth)⟩

theorem resolved_iff (context : ShareCtx) (nodes : Array Node) :
    ResolvedBounded context nodes ↔ ∀ id ∈ context.resolved, id < nodes.size := by
  constructor
  · intro bounded id member
    obtain ⟨index, bound, same⟩ := Array.mem_iff_getElem.mp member
    subst id
    exact bounded index _ (Array.getElem?_eq_getElem bound)
  · intro bounded index id found
    exact bounded id (Array.mem_of_getElem? found)

def tableContext (tableSize : Nat) (allowShare : Bool) (index : Nat) (resolved : Array Nat) : ShareCtx :=
  { resolved, tableSize, entry := some index, root := 0, allowShare }

def rootContext (tableSize : Nat) (allowShare : Bool) (index : Nat) (resolved : Array Nat) : ShareCtx :=
  { resolved, tableSize, entry := none, root := index, allowShare }

theorem tableContext_push (tableSize : Nat) (allowShare : Bool) (index : Nat) (resolved : Array Nat) (id : Nat) :
    ContextExtends (tableContext tableSize allowShare index resolved)
      (tableContext tableSize allowShare (index + 1) (resolved.push id)) :=
  context_extends rfl (RefRetains.push resolved id)

theorem resolved_push (context : ShareCtx) (nodes : Array Node) (bounded : ResolvedBounded context nodes)
    (id : Nat) (bound : id < nodes.size) : ResolvedBounded { context with resolved := context.resolved.push id } nodes := by
  rw [resolved_iff] at bounded ⊢
  intro value member
  simp only [Array.mem_push] at member
  rcases member with member | rfl
  · exact bounded value member
  · exact bound

def Rows (context : ShareCtx) (nodes : Array Node) (sources : List Ixon.Expr) (ids : Array Nat) : Prop :=
  List.Forall₂ (Represents context nodes) sources ids.toList

theorem pairs_mono {first second : α → β → Prop} (transform : ∀ x y, first x y → second x y)
    {left : List α} {right : List β} (rows : List.Forall₂ first left right) : List.Forall₂ second left right := by
  induction rows with
  | nil => exact .nil
  | cons related _ ih => exact .cons (transform _ _ related) ih

theorem pairs_append {related : α → β → Prop} {left tail : List α} {right rest : List β}
    (first : List.Forall₂ related left right) (last : List.Forall₂ related tail rest) :
    List.Forall₂ related (left ++ tail) (right ++ rest) := by
  induction first with
  | nil => exact last
  | cons related _ ih => exact .cons related ih

theorem pairs_length {related : α → β → Prop} {left : List α} {right : List β}
    (rows : List.Forall₂ related left right) : left.length = right.length := by
  induction rows with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem Rows.length {context : ShareCtx} {nodes : Array Node} {sources : List Ixon.Expr} {ids : Array Nat}
    (rows : Rows context nodes sources ids) : sources.length = ids.size := by
  simpa using pairs_length rows

theorem Rows.grows {context : ShareCtx} {before after : Array Node} (keeps : Retains before after)
    (bounded : ResolvedBounded context before) {sources : List Ixon.Expr} {ids : Array Nat}
    (rows : Rows context before sources ids) : Rows context after sources ids :=
  pairs_mono (fun _ _ meaning => represents_grows keeps context bounded meaning) rows

theorem Rows.context {before after : ShareCtx} (growth : ContextExtends before after)
    {nodes : Array Node} {sources : List Ixon.Expr} {ids : Array Nat} (rows : Rows before nodes sources ids) :
    Rows after nodes sources ids := pairs_mono (fun _ _ meaning => meaning.context growth) rows

theorem Rows.push {context : ShareCtx} {nodes : Array Node} {sources : List Ixon.Expr} {ids : Array Nat}
    (rows : Rows context nodes sources ids) (source : Ixon.Expr) (id : Nat) (meaning : Represents context nodes source id) :
    Rows context nodes (sources ++ [source]) (ids.push id) := by
  unfold Rows
  simpa only [Array.toList_push] using pairs_append rows (List.Forall₂.cons meaning List.Forall₂.nil)

theorem SharesValid.bounded (context : ShareCtx) (source : Ixon.Expr) (valid : SharesValid context source) :
    SharesIn (fun index => index < context.resolved.size) source := by
  induction source with
  | share index =>
    obtain ⟨id, found⟩ := valid
    exact (Array.getElem?_eq_some_iff.mp (resolveShare_slot context index id found)).1
  | prj _ _ _ ih => exact ih valid
  | app _ _ ihf iha | lam _ _ _ ihf iha | all _ _ _ _ ihf iha => exact ⟨ihf valid.1, iha valid.2⟩
  | letE _ _ _ _ iht ihv ihb => exact ⟨iht valid.1, ihv valid.2.1, ihb valid.2.2⟩
  | _ => trivial

/-- Proof view of the production indexed for-loop; no algorithm changes. -/
def walk (limits : Limits) (sources : Array Ixon.Expr) (ctxOf : Nat → Array Nat → ShareCtx) :
    Nat → Nat → Array Nat → IngestM (Array Nat)
  | 0, _, acc => pure acc
  | count + 1, index, acc => do
    let id ← ingestExpr limits (ctxOf index acc) 0 sources[index]!
    walk limits sources ctxOf count (index + 1) (acc.push id)

theorem walk_inv (limits : Limits) (sources : Array Ixon.Expr) (ctxOf : Nat → Array Nat → ShareCtx)
    (invariant : Nat → Array Nat → IngestState → Prop)
    (step : ∀ index, index < sources.size → ∀ acc before, invariant index acc before → ∀ id after,
      (ingestExpr limits (ctxOf index acc) 0 sources[index]!).run before = .ok (id, after) →
      invariant (index + 1) (acc.push id) after ∧ Retains before.interner.nodes after.interner.nodes) :
    ∀ count index, index + count ≤ sources.size → ∀ acc before, invariant index acc before → ∀ out after,
      (walk limits sources ctxOf count index acc).run before = .ok (out, after) →
      invariant (index + count) out after ∧ Retains before.interner.nodes after.interner.nodes := by
  intro count
  induction count with
  | zero =>
    intro index bounded acc before valid out after ran
    have same : .ok (acc, before) = Except.ok (ε := SharingError) (out, after) := ran
    cases Except.ok.inj same
    exact ⟨valid, Retains.refl _⟩
  | succ count ih =>
    intro index bounded acc before valid out after ran
    obtain ⟨id, middle, first, last⟩ := bind_run ran
    have next := step index (by omega) acc before valid id middle first
    have rest := ih (index + 1) (by omega) (acc.push id) middle next.1 out after last
    exact ⟨by simpa only [Nat.add_assoc, Nat.add_comm 1 count] using rest.1, next.2.trans rest.2⟩

theorem walk_eq_loop (limits : Limits) (sources : Array Ixon.Expr) (ctxOf : Nat → Array Nat → ShareCtx) :
    ∀ count index acc (items : List Nat) (_ : items = List.range' index count)
      (body : (item : Nat) → item ∈ items → Array Nat → IngestM (ForInStep (Array Nat))),
      (∀ item member acc, body item member acc = (do
        let id ← ingestExpr limits (ctxOf item acc) 0 sources[item]!
        pure (ForInStep.yield (acc.push id)))) →
      walk limits sources ctxOf count index acc = forIn' items acc body
  | 0, index, acc, items, same, body, _ => by
    rw [List.range'_zero] at same
    subst items
    rw [walk, List.forIn'_nil]
  | count + 1, index, acc, items, same, body, bodyEq => by
    rw [List.range'_succ] at same
    subst items
    rw [walk, List.forIn'_cons, bodyEq, bind_assoc]
    simp only [pure_bind]
    apply congrArg (fun next : Nat → IngestM (Array Nat) => ingestExpr limits (ctxOf index acc) 0 sources[index]! >>= next)
    funext id
    exact walk_eq_loop limits sources ctxOf count (index + 1) (acc.push id) _ rfl _
      (fun item member acc => bodyEq item _ acc)

structure Entries (sources : Array Ixon.Expr) (allowShare : Bool) (index : Nat)
    (ids : Array Nat) (state : IngestState) : Prop where
  size : ids.size = index
  good : Good (tableContext sources.size allowShare index ids) state
  rows : Rows (tableContext sources.size allowShare index ids) state.interner.nodes (sources.toList.take index) ids
  backward : ∀ position, position < index → SharesIn (fun slot => slot < position) sources[position]!

theorem take_next [Inhabited α] (sources : Array α) (index : Nat) (bound : index < sources.size) :
    sources.toList.take (index + 1) = sources.toList.take index ++ [sources[index]!] := by
  rw [List.take_succ_eq_append_getElem (by simpa using bound)]
  simp [getElem!_pos sources index bound]

theorem take_all (sources : Array α) : sources.toList.take sources.size = sources.toList := by
  simpa using (show sources.toList.take sources.toList.length = sources.toList from List.take_length)

theorem entries_step (limits : Limits) (sources : Array Ixon.Expr) (allowShare : Bool)
    (index : Nat) (bound : index < sources.size) (ids : Array Nat) (before : IngestState)
    (valid : Entries sources allowShare index ids before) (id : Nat) (after : IngestState)
    (ran : (ingestExpr limits (tableContext sources.size allowShare index ids) 0 sources[index]!).run before = .ok (id, after)) :
    Entries sources allowShare (index + 1) (ids.push id) after ∧ Retains before.interner.nodes after.interner.nodes := by
  have checked := ingestExpr_checked limits (tableContext sources.size allowShare index ids) 0 sources[index]!
    before valid.good id after ran
  have contextGrowth := tableContext_push sources.size allowShare index ids id
  have nextGood := checked.1.context contextGrowth
    (resolved_push _ after.interner.nodes checked.1.resolved id checked.2.2.1)
  have priorRows := (valid.rows.grows checked.2.1 valid.good.resolved).context contextGrowth
  have nextRows := priorRows.push sources[index]! id (checked.2.2.context contextGrowth)
  refine ⟨⟨by simp [valid.size], nextGood, ?_, ?_⟩, checked.2.1⟩
  · rw [take_next sources index bound]
    exact nextRows
  · intro position earlier
    by_cases old : position < index
    · exact valid.backward position old
    · have same : position = index := by omega
      subst position
      have bounded := SharesValid.bounded _ sources[index]! checked.2.2.2.1
      simpa only [tableContext, valid.size] using bounded

theorem entries_walk (limits : Limits) (sources : Array Ixon.Expr) (allowShare : Bool)
    (count index : Nat) (bound : index + count ≤ sources.size)
    (ids : Array Nat) (before : IngestState) (valid : Entries sources allowShare index ids before)
    (out : Array Nat) (after : IngestState)
    (ran : (walk limits sources (tableContext sources.size allowShare) count index ids).run before = .ok (out, after)) :
    Entries sources allowShare (index + count) out after ∧ Retains before.interner.nodes after.interner.nodes :=
  walk_inv limits sources (tableContext sources.size allowShare) (Entries sources allowShare)
    (entries_step limits sources allowShare) count index bound ids before valid out after ran

structure Roots (sources : Array Ixon.Expr) (tableSize : Nat) (allowShare : Bool) (resolved : Array Nat)
    (index : Nat) (ids : Array Nat) (state : IngestState) : Prop where
  size : ids.size = index
  good : Good (rootContext tableSize allowShare index resolved) state
  rows : Rows (rootContext tableSize allowShare index resolved) state.interner.nodes (sources.toList.take index) ids

theorem roots_step (limits : Limits) (sources : Array Ixon.Expr) (tableSize : Nat) (allowShare : Bool) (resolved : Array Nat)
    (index : Nat) (bound : index < sources.size) (ids : Array Nat) (before : IngestState)
    (valid : Roots sources tableSize allowShare resolved index ids before) (id : Nat) (after : IngestState)
    (ran : (ingestExpr limits (rootContext tableSize allowShare index resolved) 0 sources[index]!).run before = .ok (id, after)) :
    Roots sources tableSize allowShare resolved (index + 1) (ids.push id) after ∧ Retains before.interner.nodes after.interner.nodes := by
  have checked := ingestExpr_checked limits (rootContext tableSize allowShare index resolved) 0 sources[index]!
    before valid.good id after ran
  have contextGrowth : ContextExtends (rootContext tableSize allowShare index resolved)
      (rootContext tableSize allowShare (index + 1) resolved) := context_extends rfl (RefRetains.refl resolved)
  have priorRows := (valid.rows.grows checked.2.1 valid.good.resolved).context contextGrowth
  refine ⟨⟨by simp [valid.size], checked.1.context contextGrowth checked.1.resolved, ?_⟩, checked.2.1⟩
  rw [take_next sources index bound]
  exact priorRows.push sources[index]! id (checked.2.2.context contextGrowth)

theorem roots_walk (limits : Limits) (sources : Array Ixon.Expr) (tableSize : Nat) (allowShare : Bool) (resolved : Array Nat)
    (count index : Nat) (bound : index + count ≤ sources.size)
    (ids : Array Nat) (before : IngestState) (valid : Roots sources tableSize allowShare resolved index ids before)
    (out : Array Nat) (after : IngestState)
    (ran : (walk limits sources (fun index _ => rootContext tableSize allowShare index resolved) count index ids).run before = .ok (out, after)) :
    Roots sources tableSize allowShare resolved (index + count) out after ∧ Retains before.interner.nodes after.interner.nodes :=
  walk_inv limits sources (fun index _ => rootContext tableSize allowShare index resolved)
    (Roots sources tableSize allowShare resolved) (roots_step limits sources tableSize allowShare resolved)
    count index bound ids before valid out after ran

def arrayLoop (limits : Limits) (sources : Array Ixon.Expr) (ctxOf : Nat → Array Nat → ShareCtx)
    (initial : Array Nat) : IngestM (Array Nat) := do
  let mut acc := initial
  for h : index in [0:sources.size] do
    let id ← ingestExpr limits (ctxOf index acc) 0 sources[index]
    acc := acc.push id
  return acc

theorem arrayLoop_eq_walk (limits : Limits) (sources : Array Ixon.Expr) (ctxOf : Nat → Array Nat → ShareCtx)
    (initial : Array Nat) : arrayLoop limits sources ctxOf initial = walk limits sources ctxOf sources.size 0 initial := by
  unfold arrayLoop
  dsimp only
  simp only [bind_pure]
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  symm
  apply walk_eq_loop
  · simp [Std.Legacy.Range.size]
  · intro index member acc
    have bound : index < sources.size := by
      have found := List.mem_range'.mp member
      simp [Std.Legacy.Range.size] at found
      omega
    rw [getElem!_pos sources index bound]

def tableBody (limits : Limits) (sharing roots : Array Ixon.Expr) (allowShare : Bool) : IngestM (Array Nat × Array Nat) := do
  let resolved ← arrayLoop limits sharing (tableContext sharing.size allowShare) #[]
  let out ← arrayLoop limits roots (fun index _ => rootContext sharing.size allowShare index resolved) #[]
  return (resolved, out)

theorem ingestTable_eq (limits : Limits) (sharing roots : Array Ixon.Expr) (allowShare : Bool) :
    ingestTable limits sharing roots allowShare =
      (if sharing.size ≥ wordBound then throw (.formatBound "sharing table size" sharing.size)
       else tableBody limits sharing roots allowShare) := by
  unfold ingestTable tableBody arrayLoop tableContext rootContext
  dsimp only
  simp only [bind_pure]
  split <;> rfl

structure TableResult (sharing roots : Array Ixon.Expr) (allowShare : Bool)
    (resolved out : Array Nat) (before after : IngestState) : Prop where
  capacity : sharing.size < wordBound
  tableSize : resolved.size = sharing.size
  rootSize : out.size = roots.size
  good : Good (rootContext sharing.size allowShare roots.size resolved) after
  retained : Retains before.interner.nodes after.interner.nodes
  entries : Rows (rootContext sharing.size allowShare roots.size resolved) after.interner.nodes sharing.toList resolved
  roots : Rows (rootContext sharing.size allowShare roots.size resolved) after.interner.nodes roots.toList out
  backward : ∀ position, position < sharing.size → SharesIn (fun slot => slot < position) sharing[position]!

/-- The actual indexed entry/root loops preserve all source expressions and
their order. Entry validity yields the backward-reference rule; it is not an
assumption on the input table. The capacity bound comes from the real guard. -/
theorem ingestTable_correct (limits : Limits) (sharing roots : Array Ixon.Expr) (allowShare : Bool)
    (before : IngestState) (good : Good (tableContext sharing.size allowShare 0 #[]) before)
    (resolved out : Array Nat) (after : IngestState)
    (ran : (ingestTable limits sharing roots allowShare).run before = .ok ((resolved, out), after)) :
    TableResult sharing roots allowShare resolved out before after := by
  rw [ingestTable_eq] at ran
  by_cases large : sharing.size ≥ wordBound
  · simp only [large, ↓reduceIte] at ran
    change Except.error _ = Except.ok ((resolved, out), after) at ran
    cases ran
  · simp only [large, ↓reduceIte, tableBody, arrayLoop_eq_walk] at ran
    obtain ⟨actualRefs, middle, entriesRan, tail⟩ := bind_run ran
    obtain ⟨actualRoots, finalState, rootsRan, finished⟩ := bind_run tail
    have same : .ok ((actualRefs, actualRoots), finalState) = Except.ok (ε := SharingError) ((resolved, out), after) := finished
    cases Except.ok.inj same
    have initial : Entries sharing allowShare 0 #[] before :=
      ⟨rfl, good, by simp [Rows], by intro index bound; omega⟩
    have entries := entries_walk limits sharing allowShare sharing.size 0 (by omega) #[] before initial _ middle entriesRan
    simp only [Nat.zero_add] at entries
    have startGrowth : ContextExtends (tableContext sharing.size allowShare sharing.size resolved)
        (rootContext sharing.size allowShare 0 resolved) := context_extends rfl (RefRetains.refl resolved)
    have start : Roots roots sharing.size allowShare resolved 0 #[] middle :=
      ⟨rfl, entries.1.good.context startGrowth entries.1.good.resolved, by simp [Rows]⟩
    have rootRows := roots_walk limits roots sharing.size allowShare resolved roots.size 0 (by omega)
      #[] middle start _ after rootsRan
    simp only [Nat.zero_add] at rootRows
    have finalGrowth : ContextExtends (tableContext sharing.size allowShare sharing.size resolved)
        (rootContext sharing.size allowShare roots.size resolved) := context_extends rfl (RefRetains.refl resolved)
    refine ⟨Nat.lt_of_not_ge large, entries.1.size, rootRows.1.size, rootRows.1.good,
      entries.2.trans rootRows.2, ?_, ?_, entries.1.backward⟩
    · have meanings := (entries.1.rows.grows rootRows.2 entries.1.good.resolved).context finalGrowth
      simpa only [take_all] using meanings
    · simpa only [take_all] using rootRows.1.rows

theorem ingestTable_initial (limits : Limits) (sharing roots : Array Ixon.Expr) (allowShare : Bool)
    (resolved out : Array Nat) (after : IngestState)
    (ran : (ingestTable limits sharing roots allowShare).run {} = .ok ((resolved, out), after)) :
    TableResult sharing roots allowShare resolved out {} after :=
  ingestTable_correct limits sharing roots allowShare {} (good_initial _ rfl) resolved out after ran

theorem Rows.unshared {context : ShareCtx} (mode : context.allowShare = false)
    {nodes : Array Node} {sources : List Ixon.Expr} {ids : Array Nat} (rows : Rows context nodes sources ids) :
    List.Forall₂ (fun source id => id < nodes.size ∧ termOf nodes id = source) sources ids.toList :=
  pairs_mono (fun source _ meaning =>
    ⟨meaning.1, meaning.2.2.trans (SharesValid.unshared mode source meaning.2.1 _)⟩) rows

/-- The compiler's empty-table ingestion route preserves every root in order,
with initial cache/interner premises discharged. -/
theorem ingestTable_unshared (limits : Limits) (roots : Array Ixon.Expr)
    (resolved out : Array Nat) (after : IngestState)
    (ran : (ingestTable limits #[] roots false).run {} = .ok ((resolved, out), after)) :
    TableResult #[] roots false resolved out {} after ∧ resolved = #[] ∧
      List.Forall₂ (fun source id => id < after.interner.nodes.size ∧ termOf after.interner.nodes id = source)
        roots.toList out.toList := by
  have result := ingestTable_initial limits #[] roots false resolved out after ran
  refine ⟨result, ?_, result.roots.unshared rfl⟩
  apply Array.ext result.tableSize
  intro index _ impossible
  simp at impossible

theorem index_ofNodes (nodes : Array Node) : IndexSound (Interner.ofNodes nodes) := by
  intro node index found
  have parts := (ofNodes_get? nodes node index).mp found
  change nodes[index]? = some node
  rw [Array.getElem?_eq_getElem parts.1]
  exact congrArg some (by simpa only [getElem!_pos nodes index parts.1] using parts.2.1)

theorem good_seed (context : ShareCtx) (empty : context.resolved = #[])
    (nodes : Array Node) (cp : CP nodes) (arities : NodeArity nodes) :
    Good context { interner := Interner.ofNodes nodes } := by
  refine ⟨index_ofNodes nodes, cp, arities, ?_, ExprCache.sound_empty _⟩
  intro index id found
  simp [empty] at found

/-- Actual re-expansion against a pre-existing DAG uses the same checked
ordered loops. Missing terms may append nodes; all original terms keep their
interpretation, and every returned root denotes its expanded source. -/
theorem reexpand_correct (limits : Limits) (dag : Dag) (sharing roots : Array Ixon.Expr)
    (cp : CP dag.nodes) (arities : NodeArity dag.nodes)
    (resolved out : Array Nat) (visits : Nat)
    (ran : reexpand limits dag sharing roots = .ok (resolved, out, visits)) :
    ∃ after, TableResult sharing roots true resolved out { interner := Interner.ofNodes dag.nodes } after ∧
      after.visits = visits := by
  unfold reexpand at ran
  obtain ⟨⟨⟨actualRefs, actualRoots⟩, after⟩, ingested, finished⟩ := bind_eq_ok ran
  have same : .ok (actualRefs, actualRoots, after.visits) = Except.ok (ε := SharingError) (resolved, out, visits) := finished
  obtain ⟨refs, rootsAndVisits⟩ := Prod.mk.inj (Except.ok.inj same)
  obtain ⟨rootEq, visitEq⟩ := Prod.mk.inj rootsAndVisits
  subst actualRefs
  subst actualRoots
  exact ⟨after, ingestTable_correct limits sharing roots true _
    (good_seed _ rfl dag.nodes cp arities) resolved out after ingested, visitEq⟩

end Ix.Sharing.Verify.Ingestion
