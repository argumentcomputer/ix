import IxSharingVerify.IngestionUnique
import IxSharingVerify.TieredIdem

/-! Canonical numbering preserves interpreted roots. The actual expand
entry discharges the input invariants from production ingestion. Composed
with checked re-expansion, the actual canonical sharing entry yields an
encoding that unfolds to exactly the ordered input expressions. Certified
reader/builder composition and totality remain separate. -/

namespace Ix.Sharing.Verify.CanonicalMeaning

open Ix.Sharing.Exact Ix.Sharing.Verify.SharingExact Ix.Sharing.Verify.Ingestion

abbrev State := Array Nat × Array Node

/-- A source node's current canonical slot preserves its interpreted term. -/
def Mapped (source : Array Node) (state : State) (index : Nat) : Prop :=
  index < state.1.size ∧ state.1[index]! < state.2.size ∧
    termOf state.2 state.1[index]! = termOf source index

/-- The frozen remapped node is ready to append: every child is already in
the output and its reified expression is the source node's expression. -/
structure Ready (source : Array Node) (state : State) (item : Nat × Node) : Prop where
  slot : item.1 < state.1.size
  arity : item.2.children.size = item.2.head.arity
  children : ∀ child ∈ item.2.children, child < state.2.size
  meaning : item.2.toExpr (termOf state.2) = termOf source item.1

def place (state : State) (item : Nat × Node) : State :=
  (state.1.set! item.1 state.2.size, state.2.push item.2)

theorem place_size (state : State) (item : Nat × Node) : (place state item).1.size = state.1.size := by
  simp [place]

theorem place_new (source : Array Node) (state : State) (item : Nat × Node) (ready : Ready source state item) :
    Mapped source (place state item) item.1 := by
  have term : termOf (state.2.push item.2) state.2.size = termOf source item.1 := by
    rw [termOf_node _ _ item.2 Array.getElem?_push_size ready.arity ready.children,
      node_reify_retains (Retains.push _ _) item.2 ready.arity ready.children]
    exact ready.meaning
  simp [Mapped, place, ready.slot, term]

theorem place_retains (source : Array Node) (state : State) (item : Nat × Node) (ready : Ready source state item)
    (index : Nat) (mapped : Mapped source state index) : Mapped source (place state item) index := by
  by_cases same : item.1 = index
  · subst index
    exact place_new source state item ready
  · have lookup : (place state item).1[index]! = state.1[index]! := by
      simp only [place, setBang_getElem!, same, false_and, ↓reduceIte]
    refine ⟨by simpa only [place_size] using mapped.1, ?_, ?_⟩
    · rw [lookup]
      exact (Retains.push state.2 item.2).bound _ mapped.2.1
    · rw [lookup]
      change termOf (state.2.push item.2) state.1[index]! = termOf source index
      rw [termOf_retains (Retains.push state.2 item.2) _ mapped.2.1]
      exact mapped.2.2

theorem Ready.grows {source : Array Node} {before after : State} {item : Nat × Node}
    (ready : Ready source before item) (size : after.1.size = before.1.size) (keeps : Retains before.2 after.2) :
    Ready source after item := by
  refine ⟨by simpa only [size] using ready.slot, ready.arity, ?_, ?_⟩
  · intro child member
    exact keeps.bound child (ready.children child member)
  · rw [node_reify_retains keeps item.2 ready.arity ready.children]
    exact ready.meaning

structure Placed (source : Array Node) (before after : State) (items : List (Nat × Node)) : Prop where
  size : after.1.size = before.1.size
  cp : CP after.2
  arity : NodeArity after.2
  retained : Retains before.2 after.2
  prior : ∀ index, Mapped source before index → Mapped source after index
  added : ∀ item ∈ items, Mapped source after item.1

theorem placeFold_correct (source : Array Node) (items : List (Nat × Node)) (before : State)
    (cp : CP before.2) (arity : NodeArity before.2) (ready : ∀ item ∈ items, Ready source before item) :
    Placed source before (placeFold items before) items := by
  induction items generalizing before with
  | nil => exact ⟨rfl, cp, arity, Retains.refl _, fun _ mapped => mapped, by simp⟩
  | cons item rest ih =>
    have first := ready item (by simp)
    have keeps := Retains.push before.2 item.2
    have middleCP : CP (place before item).2 := cp_push before.2 cp item.2 first.children
    have middleArity : NodeArity (place before item).2 := arity_push before.2 arity item.2 first.arity
    have restReady : ∀ next ∈ rest, Ready source (place before item) next :=
      fun next member => (ready next (by simp [member])).grows (place_size before item) keeps
    have tail := ih (place before item) middleCP middleArity restReady
    refine ⟨tail.size.trans (place_size before item), tail.cp, tail.arity, keeps.trans tail.retained,
      fun index mapped => tail.prior index (place_retains source before item first index mapped), ?_⟩
    intro next member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact tail.prior _ (place_new source before _ first)
    · exact tail.added next member

theorem placeSorted_correct (source : Array Node) (items : List (Nat × Node)) (previous : Option Node)
    (before after : State) (cp : CP before.2) (arity : NodeArity before.2)
    (ready : ∀ item ∈ items, Ready source before item)
    (ran : placeSorted items previous before = .ok after) : Placed source before after items := by
  rw [placeSorted_eq] at ran
  split at ran
  · cases Except.ok.inj ran
    exact placeFold_correct source items before cp arity ready
  · cases ran

theorem toExpr_congr_nodes (left right : Node) (first second : Nat → Ixon.Expr) (head : left.head = right.head)
    (same : ∀ index, index < left.head.arity → first (left.child index) = second (right.child index)) :
    left.toExpr first = right.toExpr second := by
  cases chosen : left.head <;> simp only [Node.toExpr, ← head, chosen]
  all_goals try rfl
  all_goals
    congr 1
    all_goals apply same; simp only [chosen, Head.arity]; decide

theorem toExpr_map_children (node : Node) (rename : Nat → Nat) (values : Nat → Ixon.Expr)
    (arity : node.children.size = node.head.arity) :
    ({ node with children := node.children.map rename } : Node).toExpr values =
      node.toExpr (fun child => values (rename child)) := by
  apply toExpr_congr_nodes { node with children := node.children.map rename } node values (fun child => values (rename child)) rfl
  intro index bound
  have old : index < node.children.size := by simpa only [arity] using bound
  have next : index < (node.children.map rename).size := by simpa using old
  rw [child_eq_getElem _ index next, child_eq_getElem node index old]
  simp only [Array.getElem_map]

structure Invariant (source : Array Node) (roots : Array Nat) (height : Nat) (state : State) : Prop where
  size : state.1.size = source.size
  cp : CP state.2
  arity : NodeArity state.2
  mapped : ∀ index, Reach source roots index → (nodeHeights source)[index]! < height → Mapped source state index

theorem key_ready (source : Array Node) (roots : Array Nat) (run : Run source roots)
    (height : Nat) (state : State) (valid : Invariant source roots height state)
    (index : Nat) (reachable : Reach source roots index) (atHeight : (nodeHeights source)[index]! = height) :
    Ready source state (index, keyOf source state.1 index) := by
  have bound := reach_lt run.cp run.inRange reachable
  have children : ∀ child ∈ (source[index]!).children, Mapped source state child := by
    intro child member
    apply valid.mapped child (.child reachable member)
    have lower := child_height_lt source (nodeHeights source) index child member
    rw [← nodeHeights_spec run.cp index bound, atHeight] at lower
    exact lower
  refine ⟨by simpa only [valid.size] using bound, ?_, ?_, ?_⟩
  · simpa only [keyOf, Array.size_map] using run.arity index bound
  · intro child member
    change child ∈ (source[index]!).children.map (state.1[·]!) at member
    obtain ⟨original, originalMember, same⟩ := Array.mem_map.mp member
    subst child
    exact (children original originalMember).2.1
  · unfold keyOf
    rw [toExpr_map_children _ _ _ (run.arity index bound)]
    have stored : source[index]? = some source[index]! := by
      simpa only [getElem!_pos source index bound] using Array.getElem?_eq_getElem bound
    rw [termOf_node source index source[index]! stored (run.arity index bound) (run.cp index bound)]
    apply toExpr_congr
    intro position inside
    have inChildren : position < (source[index]!).children.size := by rw [run.arity index bound]; exact inside
    rw [child_eq_getElem _ position inChildren]
    exact (children _ (Array.getElem_mem inChildren)).2.2

theorem placeBucket_correct (source : Array Node) (roots : Array Nat) (run : Run source roots)
    (height : Nat) (bucket : Array Nat) (atHeight : BucketAt source roots height bucket)
    (before after : State) (valid : Invariant source roots height before)
    (ran : placeBucket source before bucket = .ok after) : Invariant source roots (height + 1) after := by
  rw [placeBucket_eq] at ran
  have ready : ∀ item ∈ sortedGroup source before.1 bucket, Ready source before item := by
    intro item member
    have fromBucket := (sortedGroup_perm source before.1 bucket).mem_iff.mp member
    obtain ⟨index, indexMember, same⟩ := List.mem_map.mp fromBucket
    subst item
    have properties := (mem_bucket run atHeight index).mp indexMember
    exact key_ready source roots run height before valid index properties.1 properties.2
  have placed := placeSorted_correct source _ none before after valid.cp valid.arity ready ran
  refine ⟨placed.size.trans valid.size, placed.cp, placed.arity, ?_⟩
  intro index reachable below
  by_cases prior : (nodeHeights source)[index]! < height
  · exact placed.prior index (valid.mapped index reachable prior)
  · have now : (nodeHeights source)[index]! = height := by omega
    have member := (mem_bucket run atHeight index).mpr ⟨reachable, now⟩
    have inSorted : (index, keyOf source before.1 index) ∈ sortedGroup source before.1 bucket :=
      (sortedGroup_perm source before.1 bucket).mem_iff.mpr (List.mem_map_of_mem member)
    exact placed.added _ inSorted

theorem fold_heights (step : State → Nat → Except SharingError State) (property : Nat → State → Prop)
    (limit : Nat)
    (next : ∀ height, height < limit → ∀ before, property height before → ∀ after,
      step before height = .ok after → property (height + 1) after) :
    ∀ count start, start + count ≤ limit → ∀ before, property start before → ∀ after,
      (List.range' start count).foldlM step before = .ok after → property (start + count) after := by
  intro count
  induction count with
  | zero =>
    intro start bound before valid after ran
    have same : Except.ok before = Except.ok (ε := SharingError) after := ran
    cases Except.ok.inj same
    exact valid
  | succ count ih =>
    intro start bound before valid after ran
    rw [List.range'_succ, List.foldlM_cons] at ran
    obtain ⟨middle, first, rest⟩ := bind_eq_ok ran
    have middleValid := next start (by omega) before valid middle first
    have finished := ih (start + 1) (by omega) middle middleValid after rest
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using finished

theorem invariant_initial (source : Array Node) (roots : Array Nat) :
    Invariant source roots 0 (Array.replicate source.size 0, #[]) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro index bound; simp at bound
  · intro index bound; simp at bound
  · intro index reachable below; omega

theorem pairs_of_map {relation : α → β → Prop} (items : List α) (f : α → β)
    (each : ∀ item ∈ items, relation item (f item)) : List.Forall₂ relation items (items.map f) := by
  induction items with
  | nil => exact .nil
  | cons item rest ih =>
    exact .cons (each item (by simp)) (ih (fun item member => each item (by simp [member])))

structure Result (source : Array Node) (roots : Array Nat) (dag : Dag) (out : Array Nat) : Prop where
  cp : CP dag.nodes
  arity : NodeArity dag.nodes
  size : out.size = roots.size
  terms : List.Forall₂ (fun original canonical => canonical < dag.nodes.size ∧
      termOf dag.nodes canonical = termOf source original) roots.toList out.toList

/-- The actual height-ordered renumbering preserves every root's interpreted
term and yields a well-formed DAG. The input contract is discharged for
production ingestion by `Ingestion.ingestTable_run`. -/
theorem canonicalize_correct (source : Array Node) (roots : Array Nat) (run : Run source roots)
    (dag : Dag) (out : Array Nat) (ran : canonicalize source roots = .ok (dag, out)) :
    Result source roots dag out := by
  let maximum := maxHeight (reachMarks source roots) (nodeHeights source) source.size
  let buckets := heightBuckets (reachMarks source roots) (nodeHeights source) maximum source.size
  let step := fun (state : State) (height : Nat) => placeBucket source state buckets[height]!
  have upper := (maxHeight_spec (reachMarks source roots) (nodeHeights source) source.size).1
  have next : ∀ height, height < maximum + 1 → ∀ before, Invariant source roots height before → ∀ after,
      step before height = .ok after → Invariant source roots (height + 1) after := by
    intro height below before valid after stepRan
    apply placeBucket_correct source roots run height buckets[height]! ?_ before after valid stepRan
    exact (heightBuckets_spec _ _ maximum source.size upper).2 height (by omega)
  rw [canonicalize_eq run] at ran
  obtain ⟨state, folded, finished⟩ := bind_eq_ok ran
  change Except.ok ((⟨state.2⟩ : Dag), roots.map (state.1[·]!)) = .ok (dag, out) at finished
  cases Except.ok.inj finished
  change (List.range (maximum + 1)).foldlM step (Array.replicate source.size 0, #[]) = .ok state at folded
  rw [List.range_eq_range'] at folded
  have valid := fold_heights step (Invariant source roots) (maximum + 1) next (maximum + 1) 0 (by omega)
    _ (invariant_initial source roots) state folded
  simp only [Nat.zero_add] at valid
  refine ⟨valid.cp, valid.arity, by simp, ?_⟩
  change List.Forall₂ _ roots.toList ((roots.map (state.1[·]!)).toList)
  rw [Array.toList_map]
  apply pairs_of_map
  intro original member
  have inRoots : original ∈ roots := by simpa using member
  have bound := run.inRange original inRoots
  have reached : Reach source roots original := .root inRoots
  have marked := (reachMarks_spec run.cp run.inRange original bound).mpr reached
  have below : (nodeHeights source)[original]! < maximum + 1 := Nat.lt_succ_of_le (upper original bound marked)
  exact (valid.mapped original reached below).2

/-- A successful production expansion combines the ordered ingestion meaning
with meaning-preserving canonical numbering. The final depth guard is still
executed; this statement does not claim success for every resource budget. -/
theorem expand_correct (limits : Limits) (sharing roots : Array Ixon.Expr) (allowShare : Bool)
    (expanded : Expanded) (ran : expand limits sharing roots allowShare = .ok expanded) :
    ∃ resolved rawIds state, TableResult sharing roots allowShare resolved rawIds {} state ∧
      Result state.interner.nodes rawIds expanded.dag expanded.roots := by
  unfold expand at ran
  obtain ⟨⟨⟨resolved, rawIds⟩, state⟩, ingested, tail⟩ := bind_eq_ok ran
  obtain ⟨⟨dag, ids⟩, numbered, finished⟩ := bind_eq_ok tail
  have input := ingestTable_initial limits sharing roots allowShare resolved rawIds state ingested
  have run := ingestTable_run limits sharing roots allowShare resolved rawIds state ingested
  have result := canonicalize_correct state.interner.nodes rawIds run dag ids numbered
  dsimp only at finished
  split at finished
  · change Except.error _ = Except.ok expanded at finished
    cases finished
  · have same : Except.ok ({
        dag, roots := ids, visits := state.visits,
        internedNodes := state.interner.nodes.size } : Expanded) = .ok expanded := finished
    cases Except.ok.inj same
    exact ⟨resolved, rawIds, state, input, result⟩

theorem pairs_compose {first : α → β → Prop} {second : β → γ → Prop} {last : α → γ → Prop}
    (compose : ∀ a b c, first a b → second b c → last a c)
    {left : List α} {middle : List β} {right : List γ}
    (one : List.Forall₂ first left middle) (two : List.Forall₂ second middle right) : List.Forall₂ last left right := by
  induction one generalizing right with
  | nil => cases two; exact .nil
  | cons related _ ih =>
    cases two with
    | cons linked rest => exact .cons (compose _ _ _ related linked) (ih rest)

/-- The actual empty-table route used by the compiler yields canonical roots
that denote exactly its ordered input expressions. All ingestion and
canonicalization premises are discharged from the successful production run. -/
theorem expand_unshared (limits : Limits) (roots : Array Ixon.Expr)
    (expanded : Expanded) (ran : expand limits #[] roots false = .ok expanded) :
    CP expanded.dag.nodes ∧ NodeArity expanded.dag.nodes ∧
      List.Forall₂ (fun source id => id < expanded.dag.nodes.size ∧ termOf expanded.dag.nodes id = source)
        roots.toList expanded.roots.toList := by
  obtain ⟨resolved, rawIds, state, input, result⟩ := expand_correct limits #[] roots false expanded ran
  have originals := input.roots.unshared rfl
  exact ⟨result.cp, result.arity,
    pairs_compose (fun _ _ _ original canonical => ⟨canonical.1, canonical.2.trans original.2⟩) originals result.terms⟩

theorem expand_root_terms (limits : Limits) (roots : Array Ixon.Expr)
    (expanded : Expanded) (ran : expand limits #[] roots false = .ok expanded) :
    expanded.roots.map (termOf expanded.dag.nodes) = roots := by
  have rows := (expand_unshared limits roots expanded ran).2.2
  have terms := pairs_map (pairs_mono (fun _ _ meaning => meaning.2) rows)
  apply Array.toList_inj.mp
  simpa only [Array.toList_map] using terms

theorem pairs_get {relation : α → β → Prop} {left : List α} {right : List β}
    (rows : List.Forall₂ relation left right) : ∀ index (leftBound : index < left.length) (rightBound : index < right.length),
      relation left[index] right[index] := by
  induction rows with
  | nil => intro index impossible; simp at impossible
  | cons related _ ih =>
    intro index leftBound rightBound
    cases index with
    | zero => exact related
    | succ index => exact ih index (by simpa using leftBound) (by simpa using rightBound)

theorem pairs_match_right {first : α → β → Prop} {second : γ → β → Prop} {last : α → γ → Prop}
    (compose : ∀ a b c, first a b → second c b → last a c)
    {left : List α} {ids : List β} {right : List γ}
    (one : List.Forall₂ first left ids) (two : List.Forall₂ second right ids) : List.Forall₂ last left right := by
  induction one generalizing right with
  | nil => cases two; exact .nil
  | cons related _ ih =>
    cases two with
    | cons linked rest => exact .cons (compose _ _ _ related linked) (ih rest)

/-- A shared encoding unfolds to the original ordered roots. Entry equations
and backward references define the substitution; root references stay within
the supplied table. No metadata or compiler success occurs in this predicate. -/
def SharingMeaning (sources sharing roots : Array Ixon.Expr) : Prop :=
  ∃ substitution : Nat → Ixon.Expr,
    (∀ index, index < sharing.size → substitution index = substShares substitution sharing[index]! ∧
      SharesIn (fun slot => slot < index) sharing[index]!) ∧
    (∀ root ∈ roots, SharesIn (fun slot => slot < sharing.size) root) ∧
    roots.map (substShares substitution) = sources

/-- The actual canonical sharing entry preserves the complete ordered input
expressions. This composes source ingestion, canonical renumbering and the
production re-expansion check; no output certificate is a premise. -/
theorem canonicalSharingTiered_meaning (layout : ShareLayout) (limits : Limits) (sources : Array Ixon.Expr)
    (result : TieredSharingResult) (ran : canonicalSharingTiered layout sources limits = .ok result) :
    SharingMeaning sources result.result.sharing result.result.roots := by
  unfold canonicalSharingTiered at ran
  obtain ⟨expanded, expandedRan, sharedRan⟩ := bind_eq_ok ran
  have original := expand_unshared limits sources expanded expandedRan
  obtain ⟨visits, rechecked⟩ := Tiered.canonicalTiered_reexpand sharedRan
  obtain ⟨after, target, _⟩ := reexpand_correct limits expanded.dag result.result.sharing result.result.roots
    original.1 original.2.1 result.result.tableTerms expanded.roots visits rechecked
  let context := rootContext result.result.sharing.size true result.result.roots.size result.result.tableTerms
  let substitution := expansion context after.interner.nodes
  refine ⟨substitution, ?_, ?_, ?_⟩
  · intro index bound
    have refBound : index < result.result.tableTerms.size := by rw [target.tableSize]; exact bound
    have row := pairs_get target.entries index (by simpa using bound) (by simpa using refBound)
    refine ⟨?_, target.backward index bound⟩
    change (match result.result.tableTerms[index]? with
      | some id => termOf after.interner.nodes id | none => default) = substShares substitution result.result.sharing[index]!
    rw [Array.getElem?_eq_getElem refBound]
    simpa only [Array.getElem_toList, getElem!_pos result.result.sharing index bound] using row.2.2
  · intro root member
    obtain ⟨index, bound, same⟩ := Array.mem_iff_getElem.mp member
    subst root
    have refBound : index < expanded.roots.size := by rw [target.rootSize]; exact bound
    have row := pairs_get target.roots index (by simpa using bound) (by simpa using refBound)
    have valid := SharesValid.bounded context _ row.2.1
    simpa only [context, rootContext, target.tableSize, Array.getElem_toList] using valid
  · have roots := pairs_match_right
      (fun source id root sourceMeaning targetMeaning =>
        targetMeaning.2.2.symm.trans ((termOf_retains target.retained id sourceMeaning.1).trans sourceMeaning.2))
      original.2.2 target.roots
    have mapped := pairs_map roots
    apply Array.toList_inj.mp
    simpa only [Array.toList_map] using mapped

end Ix.Sharing.Verify.CanonicalMeaning
