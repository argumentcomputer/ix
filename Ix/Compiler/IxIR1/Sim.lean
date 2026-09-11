import Ix.Compiler.IxIR1.Eval
import Ix.Compiler.IxIR0.Eval

/-!
# IxIR₀ → IxIR₁ memory-simulation foundations

This file separates the four relations needed by the lowering proof:

1. `ValueGraph` realizes a pure IxIR₀ value at an IxIR₁ scalar or live
   heap root. Function-shaped values use an explicit correspondence oracle;
   constructor data is checked recursively.
2. `RootOwnership` states the exact ownership equation for a multiset of
   live roots. Shared refcounts equal incoming roots plus heap edges; unique
   nodes have one incoming owner. Edges and roots remain in one ownership
   world, and pap nodes are shared.
3. `HeapIso` identifies live heaps through a finite partial bijection of
   locations. Dead slots and cost counters are intentionally absent.
4. `StoreGraphExtends` preserves existing node shapes while allowing RC-only
   updates and unrelated allocation, so semantic graphs can survive ordinary
   memory-management steps without demanding full heap isomorphism.

The primitive lemmas below this foundation are the first layer of the formal
IxIR₀ → IxIR₁ simulation. They are kept independent of lowering so the
later compiler induction can reuse them for hand-written and generated code.
-/

namespace Ix.Compiler.IxIR1.Sim

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR0 (Literal)

/-! ## Pure values realized by a heap graph -/

/-- The lowering-specific correspondence for function-shaped values.
`captures` are the pure values stored in the target pap node. Lambda lifting
and known heads will instantiate this oracle in the compiler theorem. -/
abbrev FunctionRel :=
  IxIR0.Value → Address → Nat → List IxIR0.Value → Prop

mutual

  /-- A pure IxIR₀ value realized by an IxIR₁ scalar or live heap node. -/
  inductive ValueGraph (funRel : FunctionRel) (store : Store) :
      IxIR0.Value → RVal → Prop where
    | lit {l : Literal} : ValueGraph funRel store (.lit l) (.lit l)
    | erased : ValueGraph funRel store .erased .erased
    | ctor {adr : Address} {tag : Nat} {args : List IxIR0.Value}
        {loc : Nat} {world : Owned} {rc : Nat} {cid : CtorId}
        {fields : Array RVal} :
        store.get? loc = some ⟨world, rc, .ctorN cid fields⟩ →
        cid.block = adr →
        cid.cidx = tag →
        ValuesGraph funRel store args fields.toList →
        ValueGraph funRel store (.ctor adr tag args) (.loc loc)
    | function {v : IxIR0.Value} {f : Address} {arity : Nat}
        {captures : List IxIR0.Value} {loc rc : Nat} {args : Array RVal} :
        store.get? loc = some ⟨.shared, rc, .papN f arity args⟩ →
        funRel v f arity captures →
        ValuesGraph funRel store captures args.toList →
        ValueGraph funRel store v (.loc loc)

  /-- Pointwise realization of node fields or pap captures. -/
  inductive ValuesGraph (funRel : FunctionRel) (store : Store) :
      List IxIR0.Value → List RVal → Prop where
    | nil : ValuesGraph funRel store [] []
    | cons {v : IxIR0.Value} {rv : RVal}
        {vs : List IxIR0.Value} {rvs : List RVal} :
        ValueGraph funRel store v rv →
        ValuesGraph funRel store vs rvs →
        ValuesGraph funRel store (v :: vs) (rv :: rvs)

end

/-- Pointwise value graphs have equal source and runtime vector lengths. -/
@[simp] theorem ValuesGraph.length {funRel : FunctionRel} {store : Store} :
    ∀ {values : List IxIR0.Value} {runtimeValues : List RVal},
      ValuesGraph funRel store values runtimeValues →
      values.length = runtimeValues.length
  | _, _, .nil => rfl
  | _, _, .cons _ tail => by simp [tail.length]

/-- Pointwise value graphs concatenate in lockstep. -/
theorem ValuesGraph.append {funRel : FunctionRel} {store : Store}
    {sourceLeft sourceRight : List IxIR0.Value}
    {runtimeLeft runtimeRight : List RVal}
    (hleft : ValuesGraph funRel store sourceLeft runtimeLeft)
    (hright : ValuesGraph funRel store sourceRight runtimeRight) :
    ValuesGraph funRel store (sourceLeft ++ sourceRight)
      (runtimeLeft ++ runtimeRight) := by
  induction sourceLeft generalizing runtimeLeft with
  | nil =>
    cases hleft
    simpa using hright
  | cons source sourceLeft ih =>
    cases hleft with
    | cons hhead htail => exact .cons hhead (ih htail)

/-- Pointwise value graphs are insensitive to reversing both vectors. -/
theorem ValuesGraph.reverse {funRel : FunctionRel} {store : Store}
    : ∀ {sourceValues : List IxIR0.Value} {runtimeValues : List RVal},
      ValuesGraph funRel store sourceValues runtimeValues →
      ValuesGraph funRel store sourceValues.reverse runtimeValues.reverse
  | _, _, .nil => .nil
  | _, _, .cons hhead htail => by
      simpa [List.reverse_cons] using
        htail.reverse.append (ValuesGraph.cons hhead ValuesGraph.nil)

/-- Split a pointwise graph at corresponding source/runtime prefixes. -/
theorem ValuesGraph.splitAppend {funRel : FunctionRel} {store : Store}
    {sourceLeft sourceRight : List IxIR0.Value}
    {runtimeLeft runtimeRight : List RVal}
    (hlength : sourceLeft.length = runtimeLeft.length)
    (graph : ValuesGraph funRel store (sourceLeft ++ sourceRight)
      (runtimeLeft ++ runtimeRight)) :
    ValuesGraph funRel store sourceLeft runtimeLeft ∧
      ValuesGraph funRel store sourceRight runtimeRight := by
  induction sourceLeft generalizing runtimeLeft with
  | nil =>
    have hruntime : runtimeLeft = [] :=
      List.length_eq_zero_iff.mp hlength.symm
    subst runtimeLeft
    exact ⟨.nil, by simpa using graph⟩
  | cons source sourceLeft ih =>
    cases runtimeLeft with
    | nil => simp at hlength
    | cons runtime runtimeLeft =>
      simp only [List.length_cons, Nat.succ.injEq] at hlength
      change ValuesGraph funRel store
        (source :: (sourceLeft ++ sourceRight))
        (runtime :: (runtimeLeft ++ runtimeRight)) at graph
      cases graph with
      | cons hhead htail =>
        obtain ⟨hleft, hright⟩ := ih hlength htail
        exact ⟨.cons hhead hleft, hright⟩

/-- Restrict a pointwise graph to equal numeric prefixes. -/
theorem ValuesGraph.take {funRel : FunctionRel} {store : Store}
    {sourceValues : List IxIR0.Value} {runtimeValues : List RVal}
    (graph : ValuesGraph funRel store sourceValues runtimeValues)
    (count : Nat) :
    ValuesGraph funRel store (sourceValues.take count)
      (runtimeValues.take count) := by
  have hsource := List.take_append_drop count sourceValues
  have hruntime := List.take_append_drop count runtimeValues
  have hlength : (sourceValues.take count).length =
      (runtimeValues.take count).length := by
    simp [graph.length]
  have hwhole : ValuesGraph funRel store
      (sourceValues.take count ++ sourceValues.drop count)
      (runtimeValues.take count ++ runtimeValues.drop count) := by
    simpa [hsource, hruntime] using graph
  exact (hwhole.splitAppend hlength).1

/-- Restrict a pointwise graph to corresponding suffixes. -/
theorem ValuesGraph.drop {funRel : FunctionRel} {store : Store}
    {sourceValues : List IxIR0.Value} {runtimeValues : List RVal}
    (graph : ValuesGraph funRel store sourceValues runtimeValues)
    (count : Nat) :
    ValuesGraph funRel store (sourceValues.drop count)
      (runtimeValues.drop count) := by
  have hsource := List.take_append_drop count sourceValues
  have hruntime := List.take_append_drop count runtimeValues
  have hlength : (sourceValues.take count).length =
      (runtimeValues.take count).length := by
    simp [graph.length]
  have hwhole : ValuesGraph funRel store
      (sourceValues.take count ++ sourceValues.drop count)
      (runtimeValues.take count ++ runtimeValues.drop count) := by
    simpa [hsource, hruntime] using graph
  exact (hwhole.splitAppend hlength).2

/-- One-way preservation of live heap shape. Existing live locations keep
their world and node contents, while reference counts may change and the
target store may contain additional live nodes. This is exactly the store
relation under which pure `ValueGraph`s remain valid. -/
def StoreGraphExtends (before after : Store) : Prop :=
  ∀ {loc world rc node},
    before.get? loc = some ⟨world, rc, node⟩ →
    ∃ rc', after.get? loc = some ⟨world, rc', node⟩

/-- Reverse shape inclusion used by destructive operations. Every node still
live afterward existed beforehand with the same world and contents, though
its reference count may differ. Dropped nodes may disappear. -/
def StoreGraphRestricts (before after : Store) : Prop :=
  ∀ {loc world rc node},
    after.get? loc = some ⟨world, rc, node⟩ →
    ∃ rc', before.get? loc = some ⟨world, rc', node⟩

theorem StoreGraphExtends.refl (store : Store) :
    StoreGraphExtends store store := by
  intro loc world rc node hget
  exact ⟨rc, hget⟩

theorem StoreGraphExtends.trans {first middle last : Store}
    (h₁ : StoreGraphExtends first middle)
    (h₂ : StoreGraphExtends middle last) :
    StoreGraphExtends first last := by
  intro loc world rc node hget
  obtain ⟨middleRc, hmiddle⟩ := h₁ hget
  exact h₂ hmiddle

theorem StoreGraphRestricts.refl (store : Store) :
    StoreGraphRestricts store store := by
  intro loc world rc node hget
  exact ⟨rc, hget⟩

theorem StoreGraphRestricts.trans {first middle last : Store}
    (h₁ : StoreGraphRestricts first middle)
    (h₂ : StoreGraphRestricts middle last) :
    StoreGraphRestricts first last := by
  intro loc world rc node hget
  obtain ⟨middleRc, hmiddle⟩ := h₂ hget
  exact h₁ hmiddle

theorem StoreGraphRestricts.rcTick (store : Store) :
    StoreGraphRestricts store store.rcTick := by
  intro loc world rc node hget
  exact ⟨rc, by simpa [Store.rcTick, Store.get?] using hget⟩

/-- Pure value realization ignores refcount changes and survives allocation
of unrelated nodes. The mutual recursor transports constructor fields and pap
captures through the same store relation. -/
theorem ValueGraph.monoStore {funRel : FunctionRel}
    {before after : Store} (hstore : StoreGraphExtends before after)
    {value : IxIR0.Value} {runtimeValue : RVal}
    (graph : ValueGraph funRel before value runtimeValue) :
    ValueGraph funRel after value runtimeValue := by
  refine ValueGraph.rec
    (motive_1 := fun value runtimeValue _ =>
      ValueGraph funRel after value runtimeValue)
    (motive_2 := fun values runtimeValues _ =>
      ValuesGraph funRel after values runtimeValues)
    ?_ ?_ ?_ ?_ ?_ ?_ graph
  · intro literal
    exact .lit
  · exact .erased
  · intro address tag args loc world rc cid fields hget haddress htag
      _ hfields
    obtain ⟨rc', hget'⟩ := hstore hget
    exact .ctor hget' haddress htag hfields
  · intro value address arity captures loc rc args hget hfun _ hcaptures
    obtain ⟨rc', hget'⟩ := hstore hget
    exact .function hget' hfun hcaptures
  · exact .nil
  · intro value runtimeValue values runtimeValues _ _ hvalue hvalues
    exact .cons hvalue hvalues

/-- Pointwise value realization survives the same shape-preserving store
extension as a single value. This companion is especially useful when an
allocation turns an already-related argument vector into node fields. -/
theorem ValuesGraph.monoStore {funRel : FunctionRel}
    {before after : Store} (hstore : StoreGraphExtends before after)
    {values : List IxIR0.Value} {runtimeValues : List RVal}
    (graphs : ValuesGraph funRel before values runtimeValues) :
    ValuesGraph funRel after values runtimeValues := by
  refine ValuesGraph.rec
    (motive_1 := fun value runtimeValue _ =>
      ValueGraph funRel after value runtimeValue)
    (motive_2 := fun values runtimeValues _ =>
      ValuesGraph funRel after values runtimeValues)
    ?_ ?_ ?_ ?_ ?_ ?_ graphs
  · intro literal
    exact .lit
  · exact .erased
  · intro address tag args loc world rc cid fields hget haddress htag
      _ hfields
    obtain ⟨rc', hget'⟩ := hstore hget
    exact .ctor hget' haddress htag hfields
  · intro value address arity captures loc rc args hget hfun _ hcaptures
    obtain ⟨rc', hget'⟩ := hstore hget
    exact .function hget' hfun hcaptures
  · exact .nil
  · intro value runtimeValue values runtimeValues _ _ hvalue hvalues
    exact .cons hvalue hvalues

/-- Pointwise graph lookup: a successful source-list lookup identifies the
runtime value at the same position together with its `ValueGraph`. -/
theorem ValuesGraph.get? {funRel : FunctionRel} {store : Store}
    {sourceValues : List IxIR0.Value} {runtimeValues : List RVal}
    (graphs : ValuesGraph funRel store sourceValues runtimeValues)
    {index : Nat} {sourceValue : IxIR0.Value}
    (hsource : sourceValues[index]? = some sourceValue) :
    ∃ runtimeValue,
      runtimeValues[index]? = some runtimeValue ∧
      ValueGraph funRel store sourceValue runtimeValue := by
  induction index generalizing sourceValues runtimeValues with
  | zero =>
    cases graphs with
    | nil => simp at hsource
    | cons hvalue htail =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hsource
      subst sourceValue
      exact ⟨_, rfl, hvalue⟩
  | succ index ih =>
    cases graphs with
    | nil => simp at hsource
    | cons hvalue htail =>
      rw [List.getElem?_cons_succ] at hsource
      obtain ⟨runtimeValue, hruntime, hvalue⟩ := ih htail hsource
      exact ⟨runtimeValue, by simpa using hruntime, hvalue⟩

/-- Once successful target execution identifies a constructor node, a
constructor-shaped source graph recovers the pointwise field graph. The
extra target-node premise is essential because the abstract `FunctionRel`
may otherwise relate an arbitrary source value to a pap. -/
theorem ValueGraph.ctor_fields_of_get
    {funRel : FunctionRel} {store : Store}
    {address : Address} {tag : Nat} {sourceFields : List IxIR0.Value}
    {loc rc : Nat} {world : Owned} {cid : CtorId}
    {fields : Array RVal}
    (graph : ValueGraph funRel store
      (.ctor address tag sourceFields) (.loc loc))
    (hget : store.get? loc = some ⟨world, rc, .ctorN cid fields⟩) :
    cid.block = address ∧ cid.cidx = tag ∧
      ValuesGraph funRel store sourceFields fields.toList := by
  cases graph with
  | ctor hgraphGet haddress htag hfields =>
    have hbox := Option.some.inj (hgraphGet.symm.trans hget)
    cases hbox
    exact ⟨haddress, htag, hfields⟩
  | function hgraphGet hfun hcaptures =>
    have hbox := Option.some.inj (hgraphGet.symm.trans hget)
    have hnode := congrArg NodeBox.node hbox
    contradiction

/-- Inversion at the erased scalar. Literal graphs carry their literal and
both located graphs produce `.loc`, so a target execution that yields
`RVal.erased` pins the source side exactly. Note the converse fails: the
abstract `FunctionRel` may relate the source erased value to a pap node. -/
theorem ValueGraph.eq_erased_of_erased {funRel : FunctionRel} {store : Store}
    {sourceValue : IxIR0.Value}
    (graph : ValueGraph funRel store sourceValue .erased) :
    sourceValue = .erased := by
  cases graph
  rfl

/-! ## Roots and exact ownership -/

/-- One external heap owner, annotated with the world in which it may be
consumed. Scalars carry no heap ownership but are valid in either world. -/
structure Root where
  world : Owned
  value : RVal
  deriving BEq, Repr

/-- Scalars inhabit either world; a location inhabits the world stored in its
live `NodeBox`. -/
def HasWorld (store : Store) (world : Owned) : RVal → Prop
  | .loc loc => ∃ box, store.get? loc = some box ∧ box.world = world
  | .lit _ | .erased => True

/-- Heap-world evidence is monotone under shape-preserving store extension. -/
theorem HasWorld.monoStore {before after : Store}
    (hstore : StoreGraphExtends before after)
    {world : Owned} {value : RVal}
    (h : HasWorld before world value) : HasWorld after world value := by
  cases value with
  | loc loc =>
    obtain ⟨box, hget, hworld⟩ := h
    cases box with
    | mk boxWorld rc node =>
      obtain ⟨rc', hget'⟩ := hstore hget
      exact ⟨⟨boxWorld, rc', node⟩, hget', hworld⟩
  | lit literal => trivial
  | erased => trivial

/-- The evaluator's executable result-world check is exactly the
propositional world predicate used by the memory simulation. -/
theorem rval_hasWorld_eq_true_iff {store : Store} {world : Owned}
    {value : RVal} :
    RVal.hasWorld store world value = true ↔ HasWorld store world value := by
  cases value with
  | lit l => simp [RVal.hasWorld, HasWorld]
  | erased => simp [RVal.hasWorld, HasWorld]
  | loc loc =>
    simp only [RVal.hasWorld, HasWorld]
    cases hbox : store.get? loc with
    | none => simp
    | some box =>
      simp only [Option.some.injEq, exists_eq_left']
      cases box.world <;> cases world <;> decide

/-- Any successful dynamic result-boundary check returns the same value
and establishes its declared world. -/
theorem checkResultWorld_ok {world : Owned} {out out' : Store × RVal}
    (h : checkResultWorld world out = .ok out') :
    out' = out ∧ HasWorld out.1 world out.2 := by
  simp only [checkResultWorld] at h
  split at h
  next hw =>
    simp only [Except.ok.injEq] at h
    subst out'
    exact ⟨rfl, rval_hasWorld_eq_true_iff.mp hw⟩
  next => contradiction

/-- Successful ownership-aware main execution exposes both its literal body
run and the checked result-world witness.  This is the top-level analogue of
`invoke_fn_result_hasWorld`, with the exact synthetic current function kept
available to structured lowering simulations. -/
theorem runOwnedMain_ok {ctx : Ctx} {world : Owned} {code : Code}
    {fuel : Nat} {out : Store × RVal}
    (run : runOwnedMain ctx world code fuel = .ok out) :
    runCode ctx fuel ⟨0, world, false, code⟩ ({} : Store) [] code =
        .ok out ∧
      HasWorld out.1 world out.2 := by
  unfold runOwnedMain at run
  cases bodyRun :
      runCode ctx fuel ⟨0, world, false, code⟩ ({} : Store) [] code with
  | error error =>
      simp only [bodyRun, bind, Except.bind] at run
      contradiction
  | ok bodyOut =>
      have checked : checkResultWorld world bodyOut = .ok out := by
        simpa only [bodyRun, bind, Except.bind] using run
      obtain ⟨outputEq, resultWorld⟩ := checkResultWorld_ok checked
      subst out
      exact ⟨rfl, resultWorld⟩

/-- A successful call to a function declaration returns a scalar or a
live location in the `FnDef.result` world. This is the first reusable
call-result ownership contract for the compiler simulation. -/
theorem invoke_fn_result_hasWorld {ctx : Ctx} {fuel : Nat}
    {f : Address} {args : List RVal} {store store' : Store}
    {value : RVal} {d : FnDef}
    (hdecl : ctx.decls f = some (.fn d))
    (hinvoke : invoke ctx fuel f args store = .ok (store', value)) :
    HasWorld store' d.result value := by
  cases fuel with
  | zero => simp [invoke] at hinvoke
  | succ fuel =>
    simp only [invoke, hdecl] at hinvoke
    split at hinvoke
    · contradiction
    · cases hrun : runCode ctx fuel d store args.reverse d.body with
      | error e =>
        rw [hrun] at hinvoke
        change (.error e : Except Err (Store × RVal)) =
          .ok (store', value) at hinvoke
        contradiction
      | ok out =>
        rw [hrun] at hinvoke
        change checkResultWorld d.result out = .ok (store', value) at hinvoke
        obtain ⟨hpair, hw⟩ := checkResultWorld_ok hinvoke
        subst out
        exact hw

/-- Every successful invocation supplied exactly the declaration arity,
independently of whether the target is a function or scalar extern. -/
theorem invoke_success_length {ctx : Ctx} {fuel : Nat} {f : Address}
    {args : List RVal} {store store' : Store} {value : RVal} {d : Decl}
    (hdecl : ctx.decls f = some d)
    (hinvoke : invoke ctx fuel f args store = .ok (store', value)) :
    args.length = declArity d := by
  cases fuel with
  | zero => simp [invoke] at hinvoke
  | succ fuel =>
    cases d <;> simp only [invoke, hdecl] at hinvoke
    all_goals
      split at hinvoke
      next hne => contradiction
      next heq => simpa [declArity] using heq

/-- Source values with ownership demands, realized by target roots. -/
inductive RootsGraph (funRel : FunctionRel) (store : Store) :
    List (Owned × IxIR0.Value) → List Root → Prop where
  | nil : RootsGraph funRel store [] []
  | cons {world : Owned} {v : IxIR0.Value} {root : Root}
      {vs : List (Owned × IxIR0.Value)} {roots : List Root} :
      root.world = world →
      HasWorld store world root.value →
      ValueGraph funRel store v root.value →
      RootsGraph funRel store vs roots →
      RootsGraph funRel store ((world, v) :: vs) (root :: roots)

@[simp] theorem RootsGraph.lengths {funRel : FunctionRel} {store : Store}
    {sourceRoots : List (Owned × IxIR0.Value)} {roots : List Root}
    (graph : RootsGraph funRel store sourceRoots roots) :
    sourceRoots.length = roots.length := by
  induction graph <;> simp_all

/-- Concatenate two independently related root frames. -/
theorem RootsGraph.append {funRel : FunctionRel} {store : Store}
    {sourceLeft sourceRight : List (Owned × IxIR0.Value)}
    {left right : List Root}
    (hleft : RootsGraph funRel store sourceLeft left)
    (hright : RootsGraph funRel store sourceRight right) :
    RootsGraph funRel store (sourceLeft ++ sourceRight) (left ++ right) := by
  induction hleft with
  | nil => simpa using hright
  | cons hrootWorld hworld hvalue _ ih =>
    exact .cons hrootWorld hworld hvalue ih

/-- Split a related concatenated frame at a prefix whose source/runtime
lengths agree. The length premise prevents an arbitrary mismatched cut from
dividing the two lockstep lists at different positions. -/
theorem RootsGraph.splitAppend {funRel : FunctionRel} {store : Store}
    {sourceLeft sourceRight : List (Owned × IxIR0.Value)}
    {left right : List Root}
    (hlength : sourceLeft.length = left.length)
    (graph : RootsGraph funRel store
      (sourceLeft ++ sourceRight) (left ++ right)) :
    RootsGraph funRel store sourceLeft left ∧
      RootsGraph funRel store sourceRight right := by
  induction sourceLeft generalizing left with
  | nil =>
    have hleft : left = [] := List.length_eq_zero_iff.mp hlength.symm
    subst left
    exact ⟨.nil, by simpa using graph⟩
  | cons source sourceLeft ih =>
    cases left with
    | nil => simp at hlength
    | cons root left =>
      rcases source with ⟨world, value⟩
      simp only [List.length_cons, Nat.succ.injEq] at hlength
      change RootsGraph funRel store
        ((world, value) :: (sourceLeft ++ sourceRight))
        (root :: (left ++ right)) at graph
      cases graph with
      | cons hrootWorld hworld hvalue htail =>
        obtain ⟨hprefix, hsuffix⟩ := ih hlength htail
        exact ⟨.cons hrootWorld hworld hvalue hprefix, hsuffix⟩

/-- Root-list realization is monotone under the same heap-shape extension as
individual values. Root worlds and runtime values remain unchanged. -/
theorem RootsGraph.monoStore {funRel : FunctionRel}
    {before after : Store} (hstore : StoreGraphExtends before after)
    {values : List (Owned × IxIR0.Value)} {roots : List Root}
    (graph : RootsGraph funRel before values roots) :
    RootsGraph funRel after values roots := by
  induction graph with
  | nil => exact .nil
  | cons hworld hhasWorld hvalue _ ih =>
    exact .cons hworld (hhasWorld.monoStore hstore)
      (hvalue.monoStore hstore) ih

/-- The child references owned by a live node. -/
def nodeChildren : Node → List RVal
  | .ctorN _ fields => fields.toList
  | .papN _ _ args => args.toList

/-- Extract a location reference, ignoring scalars. -/
def rvalLocation? : RVal → Option Nat
  | .loc loc => some loc
  | .lit _ | .erased => none

def rootLocation? (root : Root) : Option Nat := rvalLocation? root.value

/-- Location-owning edges contributed by one store slot. -/
def slotEdgeLocations : Option NodeBox → List Nat
  | none => []
  | some box => (nodeChildren box.node).filterMap rvalLocation?

/-- All location-owning edges of live heap nodes. Dead slots contribute no
owners. Multiplicity is retained. -/
def edgeLocations (store : Store) : List Nat :=
  store.nodes.toList.flatMap slotEdgeLocations

/-- Incoming ownership multiplicity at `loc`: external roots plus live heap
edges. -/
def incoming (store : Store) (roots : List Root) (loc : Nat) : Nat :=
  ((roots.filterMap rootLocation?) ++ edgeLocations store).count loc

/-- Exact root/edge ownership invariant. Cost counters and dead slots do not
participate in it. -/
structure RootOwnership (store : Store) (roots : List Root) : Prop where
  roots_world : ∀ root ∈ roots, HasWorld store root.world root.value
  edges_world : ∀ {loc box}, store.get? loc = some box →
    ∀ child ∈ nodeChildren box.node, HasWorld store box.world child
  pap_shared : ∀ {loc box f arity args},
    store.get? loc = some box → box.node = .papN f arity args →
    box.world = .shared
  counts : ∀ {loc box}, store.get? loc = some box →
    match box.world with
    | .shared => box.rc = incoming store roots loc
    | .unique => box.rc = 1 ∧ incoming store roots loc = 1

/-- Exact ownership depends on the root multiset, not its presentation order.
Compiler environments use an ordered list, so moving an arbitrary source
entry to the distinguished result position relies on this bridge. -/
theorem RootOwnership.perm {store : Store} {roots roots' : List Root}
    (h : RootOwnership store roots) (hp : roots.Perm roots') :
    RootOwnership store roots' := by
  refine ⟨?_, h.edges_world, h.pap_shared, ?_⟩
  · intro root hroot
    exact h.roots_world root (hp.mem_iff.mpr hroot)
  · intro loc box hbox
    have hcount := ((hp.filterMap rootLocation?).append_right
      (edgeLocations store)).count_eq loc
    have hincoming : incoming store roots loc = incoming store roots' loc := by
      simpa [incoming] using hcount
    rw [← hincoming]
    exact h.counts hbox

/-- A graph rooted at a value that remains live after a destructive store
restriction can be rebuilt in the post-state. Exact post-state ownership
supplies liveness for every recursive node edge. -/
theorem ValueGraph.ofRestricts {funRel : FunctionRel}
    {before after : Store} (hstore : StoreGraphRestricts before after)
    {roots : List Root} (hown : RootOwnership after roots)
    {value : IxIR0.Value} {runtimeValue : RVal} {world : Owned}
    (hworld : HasWorld after world runtimeValue)
    (graph : ValueGraph funRel before value runtimeValue) :
    ValueGraph funRel after value runtimeValue := by
  refine ValueGraph.rec
    (motive_1 := fun source runtime _ => ∀ {supportWorld : Owned},
      HasWorld after supportWorld runtime →
      ValueGraph funRel after source runtime)
    (motive_2 := fun sources runtimes _ => ∀ {supportWorld : Owned},
      (∀ runtime, runtime ∈ runtimes →
        HasWorld after supportWorld runtime) →
      ValuesGraph funRel after sources runtimes)
    ?_ ?_ ?_ ?_ ?_ ?_ graph hworld
  · intro literal supportWorld _
    exact .lit
  · intro supportWorld _
    exact .erased
  · intro address tag args loc nodeWorld rc cid fields hget haddress htag
      _ hfields supportWorld hlive
    obtain ⟨afterBox, hafter, hafterWorld⟩ := hlive
    rcases afterBox with ⟨afterWorld, afterRc, afterNode⟩
    change afterWorld = supportWorld at hafterWorld
    subst supportWorld
    obtain ⟨beforeRc, hbefore⟩ := hstore hafter
    have hboxEq :
        (⟨afterWorld, beforeRc, afterNode⟩ : NodeBox) =
          ⟨nodeWorld, rc, .ctorN cid fields⟩ :=
      Option.some.inj (hbefore.symm.trans hget)
    cases hboxEq
    apply ValueGraph.ctor hafter haddress htag
    apply hfields
    intro child hchild
    exact hown.edges_world hafter child
      (by simpa [nodeChildren] using hchild)
  · intro source address arity captures loc rc args hget hfun
      _ hcaptures supportWorld hlive
    obtain ⟨afterBox, hafter, hafterWorld⟩ := hlive
    rcases afterBox with ⟨afterWorld, afterRc, afterNode⟩
    change afterWorld = supportWorld at hafterWorld
    subst supportWorld
    obtain ⟨beforeRc, hbefore⟩ := hstore hafter
    have hboxEq :
        (⟨afterWorld, beforeRc, afterNode⟩ : NodeBox) =
          ⟨.shared, rc, .papN address arity args⟩ :=
      Option.some.inj (hbefore.symm.trans hget)
    cases hboxEq
    apply ValueGraph.function hafter hfun
    apply hcaptures
    intro child hchild
    exact hown.edges_world hafter child
      (by simpa [nodeChildren] using hchild)
  · intro supportWorld _
    exact .nil
  · intro source runtime sources runtimes _ _ hsource hsources
      supportWorld hall
    exact .cons
      (hsource (hall runtime (by simp)))
      (hsources (fun child hchild => hall child (by simp [hchild])))

private theorem rootsGraph_ofRestrictsSubset {funRel : FunctionRel}
    {before after : Store} (hstore : StoreGraphRestricts before after)
    {allRoots : List Root} (hown : RootOwnership after allRoots)
    {sourceRoots : List (Owned × IxIR0.Value)} {roots : List Root}
    (graphs : RootsGraph funRel before sourceRoots roots) :
    (∀ root, root ∈ roots → root ∈ allRoots) →
      RootsGraph funRel after sourceRoots roots := by
  induction graphs with
  | nil =>
    intro _
    exact .nil
  | @cons world value root sourceTail rootTail hrootWorld _ hvalue
      htail ih =>
    intro hsubset
    have hrootLive : HasWorld after world root.value := by
      have hrootWorld' := hown.roots_world root
        (hsubset root (by simp))
      simpa [hrootWorld] using hrootWorld'
    exact .cons hrootWorld hrootLive
      (hvalue.ofRestricts hstore hown hrootLive)
      (ih (fun candidate hmember =>
        hsubset candidate (by simp [hmember])))

theorem RootsGraph.ofRestrictsIn {funRel : FunctionRel}
    {before after : Store} (hstore : StoreGraphRestricts before after)
    {allRoots : List Root} (hown : RootOwnership after allRoots)
    {sourceRoots : List (Owned × IxIR0.Value)} {roots : List Root}
    (hsubset : ∀ root, root ∈ roots → root ∈ allRoots)
    (graphs : RootsGraph funRel before sourceRoots roots) :
    RootsGraph funRel after sourceRoots roots :=
  rootsGraph_ofRestrictsSubset hstore hown graphs hsubset

/-- Every semantically related root in a surviving root list keeps its graph
under a destructive shape restriction. -/
theorem RootsGraph.ofRestricts {funRel : FunctionRel}
    {before after : Store} (hstore : StoreGraphRestricts before after)
    {sourceRoots : List (Owned × IxIR0.Value)} {roots : List Root}
    (hown : RootOwnership after roots)
    (graphs : RootsGraph funRel before sourceRoots roots) :
    RootsGraph funRel after sourceRoots roots :=
  graphs.ofRestrictsIn hstore hown (fun _ => id)

/-- Pointwise source values survive a destructive restriction whenever each
runtime value is still represented by some root in the post-state ownership
set. The supporting root's world is existential because `ValuesGraph` itself
is intentionally world-agnostic. -/
theorem ValuesGraph.ofRestrictsIn {funRel : FunctionRel}
    {before after : Store} (hstore : StoreGraphRestricts before after)
    {allRoots : List Root} (hown : RootOwnership after allRoots)
    {sourceValues : List IxIR0.Value} {runtimeValues : List RVal}
    (hsupport : ∀ runtime, runtime ∈ runtimeValues →
      ∃ world, (⟨world, runtime⟩ : Root) ∈ allRoots)
    (graphs : ValuesGraph funRel before sourceValues runtimeValues) :
    ValuesGraph funRel after sourceValues runtimeValues := by
  refine ValuesGraph.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun sources runtimes _ =>
      (∀ runtime, runtime ∈ runtimes →
        ∃ world, (⟨world, runtime⟩ : Root) ∈ allRoots) →
      ValuesGraph funRel after sources runtimes)
    ?_ ?_ ?_ ?_ ?_ ?_ graphs hsupport
  · intro _
    trivial
  · trivial
  · simp
  · simp
  · intro _
    exact .nil
  · intro source runtime sources runtimes hvalue _ _ htail
    intro hremaining
    obtain ⟨world, hroot⟩ := hremaining runtime (by simp)
    exact .cons
      (hvalue.ofRestricts hstore hown
        (hown.roots_world ⟨world, runtime⟩ hroot))
      (htail (fun child hchild =>
        hremaining child (by simp [hchild])))

theorem RootOwnership.empty : RootOwnership ({} : Store) [] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · intro loc box hbox
    simp [Store.get?] at hbox
  · intro loc box f arity args hbox
    simp [Store.get?] at hbox
  · intro loc box hbox
    simp [Store.get?] at hbox

/-- Every heap edge points to a live node. This is separated from exact owner
counts so graph closure can also be used by location isomorphism. -/
def LiveRVal (store : Store) : RVal → Prop
  | .loc loc => ∃ box, store.get? loc = some box
  | .lit _ | .erased => True

def StoreClosed (store : Store) : Prop :=
  ∀ {loc box}, store.get? loc = some box →
    ∀ child ∈ nodeChildren box.node, LiveRVal store child

theorem RootOwnership.storeClosed {store : Store} {roots : List Root}
    (h : RootOwnership store roots) : StoreClosed store := by
  intro loc box hbox child hchild
  have hw := h.edges_world hbox child hchild
  cases child with
  | loc childLoc =>
    obtain ⟨childBox, hlive, _⟩ := hw
    exact ⟨childBox, hlive⟩
  | lit l => trivial
  | erased => trivial

/-- Roots consumed as the fields/captures of one freshly allocated node. -/
def rootsFor (world : Owned) (values : List RVal) : List Root :=
  values.map fun value => ⟨world, value⟩

/-- Roots for a heterogeneous function telescope. The arity equality in
`FnOwnershipContract` rules out the truncating mismatch cases. -/
def rootsForWorlds : List Owned → List RVal → List Root
  | world :: worlds, value :: values =>
      ⟨world, value⟩ :: rootsForWorlds worlds values
  | _, _ => []

/-- Turn a pointwise value graph into a homogeneous root frame once every
runtime value is known live in the chosen ownership world. -/
theorem ValuesGraph.rootsGraph {funRel : FunctionRel} {store : Store}
    {sourceValues : List IxIR0.Value} {runtimeValues : List RVal}
    (world : Owned)
    (graphs : ValuesGraph funRel store sourceValues runtimeValues)
    (hworld : ∀ runtime, runtime ∈ runtimeValues →
      HasWorld store world runtime) :
    RootsGraph funRel store
      (sourceValues.map fun value => (world, value))
      (rootsFor world runtimeValues) := by
  induction sourceValues generalizing runtimeValues with
  | nil =>
    cases graphs
    exact .nil
  | cons source sources ih =>
    cases graphs with
    | cons hvalue hvalues =>
      simp only [List.map_cons, rootsFor]
      exact RootsGraph.cons rfl
        (hworld _ (by simp)) hvalue
        (ih hvalues (fun candidate hmember =>
          hworld candidate (by simp [hmember])))

/-- Forget the homogeneous ownership annotations of a root frame, recovering
the underlying pointwise value graph. -/
theorem RootsGraph.valuesGraph {funRel : FunctionRel} {store : Store}
    {sourceValues : List IxIR0.Value} {runtimeValues : List RVal}
    {world : Owned}
    (graphs : RootsGraph funRel store
      (sourceValues.map fun value => (world, value))
      (rootsFor world runtimeValues)) :
    ValuesGraph funRel store sourceValues runtimeValues := by
  induction sourceValues generalizing runtimeValues with
  | nil =>
    cases runtimeValues with
    | nil => exact .nil
    | cons runtime runtimes => cases graphs
  | cons source sources ih =>
    cases runtimeValues with
    | nil => cases graphs
    | cons runtime runtimes =>
      simp only [List.map_cons, rootsFor] at graphs
      cases graphs with
      | cons _ _ hvalue htail => exact .cons hvalue (ih htail)

/-- With matching telescope lengths, every runtime value occurs in the
heterogeneous root list at the world paired with one of its positions. -/
theorem exists_root_mem_rootsForWorlds
    {worlds : List Owned} {values : List RVal}
    (hlength : worlds.length = values.length)
    {value : RVal} (hvalue : value ∈ values) :
    ∃ world, (⟨world, value⟩ : Root) ∈
      rootsForWorlds worlds values := by
  induction values generalizing worlds with
  | nil => simp at hvalue
  | cons head tail ih =>
    cases worlds with
    | nil => simp at hlength
    | cons world worlds =>
      simp only [List.length_cons, Nat.succ.injEq] at hlength
      rcases List.mem_cons.mp hvalue with rfl | htail
      · exact ⟨world, by simp [rootsForWorlds]⟩
      · obtain ⟨foundWorld, hfound⟩ := ih hlength htail
        exact ⟨foundWorld, by simp [rootsForWorlds, hfound]⟩

@[simp] theorem rootsForWorlds_cons (world : Owned) (worlds : List Owned)
    (value : RVal) (values : List RVal) :
    rootsForWorlds (world :: worlds) (value :: values) =
      ⟨world, value⟩ :: rootsForWorlds worlds values := rfl

/-- The semantic ownership obligation attached to one lowered function.
The argument worlds come from the corresponding IxIR₀ lambda telescope;
`FnDef` stores only the arity and result world. A future whole-program
compiler theorem will construct one contract per lowered declaration. -/
structure FnOwnershipContract (ctx : Ctx) (d : FnDef)
    (argWorlds : List Owned) : Prop where
  arity_eq : argWorlds.length = d.arity
  preserves : ∀ {fuel : Nat} {store store' : Store} {args : List RVal}
      {value : RVal} {rest : List Root},
    args.length = argWorlds.length →
    RootOwnership store (rootsForWorlds argWorlds args ++ rest) →
    runCode ctx fuel d store args.reverse d.body = .ok (store', value) →
    RootOwnership store' (⟨d.result, value⟩ :: rest)

/-- Exact ownership preservation for one evaluator-fuel index. Separating
the fuel index from `FnOwnershipContract` makes recursive self calls
well-founded: a successful `callSelf` always enters the same body at a
strictly smaller index. -/
def FnOwnershipPreservesAt (ctx : Ctx) (d : FnDef)
    (argWorlds : List Owned) (fuel : Nat) : Prop :=
  ∀ {store store' : Store} {args : List RVal} {value : RVal}
      {rest : List Root},
    args.length = argWorlds.length →
    RootOwnership store (rootsForWorlds argWorlds args ++ rest) →
    runCode ctx fuel d store args.reverse d.body = .ok (store', value) →
    RootOwnership store' (⟨d.result, value⟩ :: rest)

/-- A function contract available only below `limit`. This is the induction
hypothesis consumed while proving a recursive function at the exact index
`limit`; it deliberately cannot justify a same-index recursive call. -/
structure FnOwnershipContractBelow (ctx : Ctx) (d : FnDef)
    (argWorlds : List Owned) (limit : Nat) : Prop where
  arity_eq : argWorlds.length = d.arity
  preserves : ∀ {fuel : Nat}, fuel < limit →
    FnOwnershipPreservesAt ctx d argWorlds fuel

/-- An ordinary function contract can be restricted to any fuel prefix. -/
theorem FnOwnershipContract.below {ctx : Ctx} {d : FnDef}
    {argWorlds : List Owned}
    (hcontract : FnOwnershipContract ctx d argWorlds) (limit : Nat) :
    FnOwnershipContractBelow ctx d argWorlds limit := by
  refine ⟨hcontract.arity_eq, ?_⟩
  intro fuel _
  exact hcontract.preserves

/-- Fuel-prefix contracts are contravariant in their bound. -/
theorem FnOwnershipContractBelow.mono {ctx : Ctx} {d : FnDef}
    {argWorlds : List Owned} {smaller larger : Nat}
    (hcontract : FnOwnershipContractBelow ctx d argWorlds larger)
    (hbound : smaller ≤ larger) :
    FnOwnershipContractBelow ctx d argWorlds smaller := by
  refine ⟨hcontract.arity_eq, ?_⟩
  intro fuel hfuel
  exact hcontract.preserves (Nat.lt_of_lt_of_le hfuel hbound)

/-- Seal a contractive, one-fuel-step body proof into the public unbounded
function contract. At index `limit`, the producer receives ownership
preservation only for strictly smaller self invocations. Strong induction
then supplies every index without assuming the theorem being constructed. -/
theorem fnOwnershipContract_of_below_step {ctx : Ctx} {d : FnDef}
    {argWorlds : List Owned}
    (harity : argWorlds.length = d.arity)
    (hstep : ∀ limit,
      FnOwnershipContractBelow ctx d argWorlds limit →
      FnOwnershipPreservesAt ctx d argWorlds limit) :
    FnOwnershipContract ctx d argWorlds := by
  refine ⟨harity, ?_⟩
  intro fuel store store' args value rest hlength hown hrun
  have hall : ∀ index,
      FnOwnershipPreservesAt ctx d argWorlds index := by
    intro index
    induction index using Nat.strongRecOn with
    | ind index ih =>
      apply hstep index
      refine ⟨harity, ?_⟩
      intro prior hprior
      exact ih prior hprior
  exact hall fuel hlength hown hrun

/-- Exact ownership contract for one case alternative. `entryRoots` describes
the roots consumed by the branch from the enclosing environment and exposed
field values; `rest` is an arbitrary caller continuation. Constructor fields
are borrows at dispatch, so their world evidence is supplied separately and
the alternative must explicitly retain any field it keeps. -/
structure AltOwnershipContract (ctx : Ctx) (cur : FnDef) (alt : Alt)
    (fieldWorld : Owned)
    (entryValid : List RVal → Array RVal → Prop)
    (entryRoots : List RVal → Array RVal → List Root) : Prop where
  preserves : match alt with
    | .mk _ fieldCount body =>
      ∀ {fuel : Nat} {store store' : Store} {env : List RVal}
          {fields : Array RVal} {value : RVal} {rest : List Root},
        fields.size = fieldCount →
        entryValid env fields →
        RootOwnership store (entryRoots env fields ++ rest) →
        (∀ field ∈ fields.toList, HasWorld store fieldWorld field) →
        runCode ctx fuel cur store
            (fields.foldl (fun branchEnv field => field :: branchEnv) env)
            body = .ok (store', value) →
        RootOwnership store' (⟨cur.result, value⟩ :: rest)

/-- A case-alternative ownership contract restricted to evaluator indices
below `limit`. Recursive rule bodies use this form while their enclosing
recursor contract is being sealed. -/
structure AltOwnershipContractBelow (ctx : Ctx) (cur : FnDef) (alt : Alt)
    (fieldWorld : Owned)
    (entryValid : List RVal → Array RVal → Prop)
    (entryRoots : List RVal → Array RVal → List Root)
    (limit : Nat) : Prop where
  preserves : match alt with
    | .mk _ fieldCount body =>
      ∀ {fuel : Nat} {store store' : Store} {env : List RVal}
          {fields : Array RVal} {value : RVal} {rest : List Root},
        fuel < limit →
        fields.size = fieldCount →
        entryValid env fields →
        RootOwnership store (entryRoots env fields ++ rest) →
        (∀ field ∈ fields.toList, HasWorld store fieldWorld field) →
        runCode ctx fuel cur store
            (fields.foldl (fun branchEnv field => field :: branchEnv) env)
            body = .ok (store', value) →
        RootOwnership store' (⟨cur.result, value⟩ :: rest)

/-- Restrict a completed alternative contract to a fuel prefix. -/
theorem AltOwnershipContract.below {ctx : Ctx} {cur : FnDef} {alt : Alt}
    {fieldWorld : Owned}
    {entryValid : List RVal → Array RVal → Prop}
    {entryRoots : List RVal → Array RVal → List Root}
    (hcontract : AltOwnershipContract ctx cur alt fieldWorld
      entryValid entryRoots) (limit : Nat) :
    AltOwnershipContractBelow ctx cur alt fieldWorld
      entryValid entryRoots limit := by
  cases alt with
  | mk tag fieldCount body =>
    refine ⟨?_⟩
    intro fuel store store' env fields value rest _ hsize hvalid hown
      hfields hrun
    exact hcontract.preserves hsize hvalid hown hfields hrun

/-- Fuel-prefix alternative contracts are contravariant in their bound. -/
theorem AltOwnershipContractBelow.mono {ctx : Ctx} {cur : FnDef}
    {alt : Alt} {fieldWorld : Owned}
    {entryValid : List RVal → Array RVal → Prop}
    {entryRoots : List RVal → Array RVal → List Root}
    {smaller larger : Nat}
    (hcontract : AltOwnershipContractBelow ctx cur alt fieldWorld
      entryValid entryRoots larger)
    (hbound : smaller ≤ larger) :
    AltOwnershipContractBelow ctx cur alt fieldWorld
      entryValid entryRoots smaller := by
  cases alt with
  | mk tag fieldCount body =>
    refine ⟨?_⟩
    intro fuel store store' env fields value rest hfuel
    exact hcontract.preserves (Nat.lt_of_lt_of_le hfuel hbound)

/-- Whole-context higher-order ownership obligation. Shared paps consume one
function root and all supplied shared argument roots; every successful
partial, saturated, or over-applied `applyGo` returns one shared root while
preserving the unrelated continuation. Constructing this contract from all
lowered declarations and pap producers is the callable half of the eventual
whole-program compiler theorem. -/
structure ApplyOwnershipContract (ctx : Ctx) : Prop where
  preserves : ∀ {fuel : Nat} {store store' : Store} {function : RVal}
      {args : List RVal} {value : RVal} {rest : List Root},
    RootOwnership store
      (⟨.shared, function⟩ :: rootsFor .shared args ++ rest) →
    applyGo ctx fuel store function args = .ok (store', value) →
    RootOwnership store' (⟨.shared, value⟩ :: rest)

/-- Exact ownership preservation for `applyGo` at one evaluator-fuel index. -/
def ApplyOwnershipPreservesAt (ctx : Ctx) (fuel : Nat) : Prop :=
  ∀ {store store' : Store} {function : RVal} {args : List RVal}
      {value : RVal} {rest : List Root},
    RootOwnership store
      (⟨.shared, function⟩ :: rootsFor .shared args ++ rest) →
    applyGo ctx fuel store function args = .ok (store', value) →
    RootOwnership store' (⟨.shared, value⟩ :: rest)

/-- Ownership preservation for one evaluator-fuel index and one fixed input
heap. Reachability-sensitive simulations use this boundary when their
compiler contract is valid on certified heap images rather than arbitrary
synthetic heaps. -/
def ApplyOwnershipPreservesFrom (ctx : Ctx) (fuel : Nat)
    (store : Store) : Prop :=
  ∀ {store' : Store} {function : RVal} {args : List RVal}
      {value : RVal} {rest : List Root},
    RootOwnership store
      (⟨.shared, function⟩ :: rootsFor .shared args ++ rest) →
    applyGo ctx fuel store function args = .ok (store', value) →
    RootOwnership store' (⟨.shared, value⟩ :: rest)

/-- A whole-context application contract specializes to every fixed input
heap. -/
theorem ApplyOwnershipContract.preservesFrom {ctx : Ctx}
    (contract : ApplyOwnershipContract ctx) (fuel : Nat) (store : Store) :
    ApplyOwnershipPreservesFrom ctx fuel store := by
  intro store' function args value rest ownership run
  exact contract.preserves ownership run

/-- Higher-order application ownership restricted to indices below
`limit`. Saturating and over-applied paps invoke declarations at smaller
fuel, so this contract belongs in the same mutual fuel induction. -/
structure ApplyOwnershipContractBelow (ctx : Ctx) (limit : Nat) : Prop where
  preserves : ∀ {fuel : Nat}, fuel < limit →
    ApplyOwnershipPreservesAt ctx fuel

/-- Every function declaration marked safe for shared PAP entry has an
all-shared signature and preserves ownership below the supplied evaluator-fuel
bound. Externs need no stored contract because their successful ABI is
scalar-only. -/
structure PapSafeDeclContractsBelow (ctx : Ctx) (limit : Nat) : Prop where
  fn : ∀ {address d}, ctx.decls address = some (.fn d) →
    d.papSafe = true →
    d.result = .shared ∧
      FnOwnershipContractBelow ctx d
        (List.replicate d.arity .shared) limit

/-- Unbounded ownership contracts for every PAP-safe function declaration in
a target context. -/
structure PapSafeDeclContracts (ctx : Ctx) : Prop where
  fn : ∀ {address d}, ctx.decls address = some (.fn d) →
    d.papSafe = true →
    d.result = .shared ∧
      FnOwnershipContract ctx d (List.replicate d.arity .shared)

/-- Restrict a completed application contract to a fuel prefix. -/
theorem ApplyOwnershipContract.below {ctx : Ctx}
    (hcontract : ApplyOwnershipContract ctx) (limit : Nat) :
    ApplyOwnershipContractBelow ctx limit := by
  refine ⟨?_⟩
  intro fuel _
  exact hcontract.preserves

/-- Fuel-prefix application contracts are contravariant in the bound. -/
theorem ApplyOwnershipContractBelow.mono {ctx : Ctx}
    {smaller larger : Nat}
    (hcontract : ApplyOwnershipContractBelow ctx larger)
    (hbound : smaller ≤ larger) :
    ApplyOwnershipContractBelow ctx smaller := by
  refine ⟨?_⟩
  intro fuel hfuel
  exact hcontract.preserves (Nat.lt_of_lt_of_le hfuel hbound)

theorem PapSafeDeclContractsBelow.mono {ctx : Ctx}
    {smaller larger : Nat}
    (hdecls : PapSafeDeclContractsBelow ctx larger)
    (hbound : smaller ≤ larger) :
    PapSafeDeclContractsBelow ctx smaller := by
  refine ⟨?_⟩
  intro address d hdecl hpapsafe
  obtain ⟨hresult, hcontract⟩ := hdecls.fn hdecl hpapsafe
  exact ⟨hresult, hcontract.mono hbound⟩

theorem PapSafeDeclContracts.below {ctx : Ctx}
    (hdecls : PapSafeDeclContracts ctx) (limit : Nat) :
    PapSafeDeclContractsBelow ctx limit := by
  refine ⟨?_⟩
  intro address d hdecl hpapsafe
  obtain ⟨hresult, hcontract⟩ := hdecls.fn hdecl hpapsafe
  exact ⟨hresult, hcontract.below limit⟩

/-- Seal a contractive exact-fuel application proof into the public
unbounded `ApplyOwnershipContract`. -/
theorem applyOwnershipContract_of_below_step {ctx : Ctx}
    (hstep : ∀ limit,
      ApplyOwnershipContractBelow ctx limit →
      ApplyOwnershipPreservesAt ctx limit) :
    ApplyOwnershipContract ctx := by
  refine ⟨?_⟩
  intro fuel store store' function args value rest hown hrun
  have hall : ∀ index, ApplyOwnershipPreservesAt ctx index := by
    intro index
    induction index using Nat.strongRecOn with
    | ind index ih =>
      apply hstep index
      refine ⟨?_⟩
      intro prior hprior
      exact ih prior hprior
  exact hall fuel hown hrun

@[simp] theorem filterMap_rootLocation?_rootsFor (world : Owned)
    (values : List RVal) :
    (rootsFor world values).filterMap rootLocation? =
      values.filterMap rvalLocation? := by
  rw [rootsFor, List.filterMap_map]
  have hfun :
      (rootLocation? ∘ fun value => (Root.mk world value)) =
        rvalLocation? := by
    funext value
    cases value <;> rfl
  rw [hfun]

theorem RootOwnership.incoming_eq_zero_of_dead {store : Store}
    {roots : List Root} (h : RootOwnership store roots) {loc : Nat}
    (hdead : store.get? loc = none) : incoming store roots loc = 0 := by
  rw [incoming, List.count_eq_zero]
  intro hmem
  rcases List.mem_append.mp hmem with hroot | hedge
  · rw [List.mem_filterMap] at hroot
    obtain ⟨root, hroot, hloc⟩ := hroot
    have hworld := h.roots_world root hroot
    cases root with
    | mk world value =>
      cases value with
      | loc rootLoc =>
        simp [rootLocation?, rvalLocation?] at hloc
        subst rootLoc
        obtain ⟨box, hlive, _⟩ := hworld
        rw [hdead] at hlive
        contradiction
      | lit l => simp [rootLocation?, rvalLocation?] at hloc
      | erased => simp [rootLocation?, rvalLocation?] at hloc
  · rw [edgeLocations, List.mem_flatMap] at hedge
    obtain ⟨slot, hslot, hedge⟩ := hedge
    cases slot with
    | none => simp [slotEdgeLocations] at hedge
    | some parentBox =>
      have harray : some parentBox ∈ store.nodes := by simpa using hslot
      obtain ⟨parentLoc, hparentArray⟩ :=
        (Array.mem_iff_getElem?).mp harray
      have hparent : store.get? parentLoc = some parentBox := by
        rw [Store.get?, hparentArray]
        rfl
      change loc ∈ (nodeChildren parentBox.node).filterMap rvalLocation?
        at hedge
      rw [List.mem_filterMap] at hedge
      obtain ⟨child, hchild, hloc⟩ := hedge
      have hworld := h.edges_world hparent child hchild
      cases child with
      | loc childLoc =>
        simp [rvalLocation?] at hloc
        subst childLoc
        obtain ⟨box, hlive, _⟩ := hworld
        rw [hdead] at hlive
        contradiction
      | lit l => simp [rvalLocation?] at hloc
      | erased => simp [rvalLocation?] at hloc

/-! ## Location renaming -/

/-- Runtime values agree modulo a location relation. -/
inductive RValIso (locRel : Nat → Nat → Prop) : RVal → RVal → Prop where
  | loc {left right : Nat} : locRel left right →
      RValIso locRel (.loc left) (.loc right)
  | lit {l : Literal} : RValIso locRel (.lit l) (.lit l)
  | erased : RValIso locRel .erased .erased

/-- Pointwise runtime-value isomorphism. -/
inductive RValsIso (locRel : Nat → Nat → Prop) :
    List RVal → List RVal → Prop where
  | nil : RValsIso locRel [] []
  | cons {left right : RVal} {lefts rights : List RVal} :
      RValIso locRel left right →
      RValsIso locRel lefts rights →
      RValsIso locRel (left :: lefts) (right :: rights)

/-- Heap nodes agree in identity/arity and pointwise modulo locations. -/
inductive NodeIso (locRel : Nat → Nat → Prop) : Node → Node → Prop where
  | ctor {cid : CtorId} {left right : Array RVal} :
      RValsIso locRel left.toList right.toList →
      NodeIso locRel (.ctorN cid left) (.ctorN cid right)
  | pap {f : Address} {arity : Nat} {left right : Array RVal} :
      RValsIso locRel left.toList right.toList →
      NodeIso locRel (.papN f arity left) (.papN f arity right)

/-- Live boxes agree semantically. Refcounts are semantic ownership state;
cost counters are not. -/
structure NodeBoxIso (locRel : Nat → Nat → Prop)
    (left right : NodeBox) : Prop where
  world : left.world = right.world
  rc : left.rc = right.rc
  node : NodeIso locRel left.node right.node

/-- A finite partial bijection covering exactly the live locations of two
heaps. The relation itself is finite because both stores have finite arrays;
`related_live` forbids mappings outside their live supports. -/
structure HeapIso (left right : Store) where
  locRel : Nat → Nat → Prop
  left_unique : ∀ {l r₁ r₂}, locRel l r₁ → locRel l r₂ → r₁ = r₂
  right_unique : ∀ {l₁ l₂ r}, locRel l₁ r → locRel l₂ r → l₁ = l₂
  left_total : ∀ {loc box}, left.get? loc = some box →
    ∃ rightLoc, locRel loc rightLoc
  right_total : ∀ {loc box}, right.get? loc = some box →
    ∃ leftLoc, locRel leftLoc loc
  related_live : ∀ {leftLoc rightLoc}, locRel leftLoc rightLoc →
    ∃ leftBox rightBox,
      left.get? leftLoc = some leftBox ∧
      right.get? rightLoc = some rightBox ∧
      NodeBoxIso locRel leftBox rightBox

namespace RValIso

theorem eq_of_location_eq {left right : RVal}
    (h : RValIso (fun l r => l = r) left right) : left = right := by
  cases h with
  | loc related => cases related; rfl
  | lit => rfl
  | erased => rfl

theorem mono {r₁ r₂ : Nat → Nat → Prop}
    (hmono : ∀ {l r}, r₁ l r → r₂ l r) {v₁ v₂ : RVal}
    (h : RValIso r₁ v₁ v₂) : RValIso r₂ v₁ v₂ := by
  cases h with
  | loc h => exact .loc (hmono h)
  | lit => exact .lit
  | erased => exact .erased

theorem refl (v : RVal) : RValIso (fun l r => l = r) v v := by
  cases v with
  | loc l => exact .loc rfl
  | lit l => exact .lit
  | erased => exact .erased

theorem symm {r : Nat → Nat → Prop} {v₁ v₂ : RVal}
    (h : RValIso r v₁ v₂) : RValIso (fun x y => r y x) v₂ v₁ := by
  cases h with
  | loc h => exact .loc h
  | lit => exact .lit
  | erased => exact .erased

theorem trans {r₁ r₂ : Nat → Nat → Prop} {v₁ v₂ v₃ : RVal}
    (h₁ : RValIso r₁ v₁ v₂) (h₂ : RValIso r₂ v₂ v₃) :
    RValIso (fun x z => ∃ y, r₁ x y ∧ r₂ y z) v₁ v₃ := by
  cases h₁ <;> cases h₂
  · exact .loc ⟨_, ‹_›, ‹_›⟩
  · exact .lit
  · exact .erased

end RValIso

/-- Every runtime value vector is related to itself by location equality. -/
theorem RValsIso.refl : ∀ values : List RVal,
    RValsIso (fun l r => l = r) values values
  | [] => .nil
  | v :: rest => .cons (RValIso.refl v) (RValsIso.refl rest)

theorem RValsIso.eq_of_location_eq {left right : List RVal}
    (h : RValsIso (fun l r => l = r) left right) : left = right := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
      rw [head.eq_of_location_eq, ih]

private theorem rvalsIso_symm {r : Nat → Nat → Prop} :
    ∀ {left right : List RVal}, RValsIso r left right →
      RValsIso (fun x y => r y x) right left
  | _, _, .nil => .nil
  | _, _, .cons hv hvs => .cons hv.symm (rvalsIso_symm hvs)

private theorem rvalsIso_mono {r₁ r₂ : Nat → Nat → Prop}
    (hmono : ∀ {l r}, r₁ l r → r₂ l r) :
    ∀ {left right : List RVal}, RValsIso r₁ left right →
      RValsIso r₂ left right
  | _, _, .nil => .nil
  | _, _, .cons hv hvs =>
    .cons (hv.mono hmono) (rvalsIso_mono hmono hvs)

private theorem rvalsIso_trans {r₁ r₂ : Nat → Nat → Prop} :
    ∀ {left middle right : List RVal},
      RValsIso r₁ left middle → RValsIso r₂ middle right →
      RValsIso (fun x z => ∃ y, r₁ x y ∧ r₂ y z) left right
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ hs₁, .cons h₂ hs₂ =>
    .cons (h₁.trans h₂) (rvalsIso_trans hs₁ hs₂)

namespace NodeIso

theorem mono {r₁ r₂ : Nat → Nat → Prop}
    (hmono : ∀ {l r}, r₁ l r → r₂ l r) {left right : Node}
    (h : NodeIso r₁ left right) : NodeIso r₂ left right := by
  cases h with
  | ctor h => exact .ctor (rvalsIso_mono hmono h)
  | pap h => exact .pap (rvalsIso_mono hmono h)

theorem refl (node : Node) : NodeIso (fun l r => l = r) node node := by
  cases node with
  | ctorN cid fields => exact .ctor (RValsIso.refl fields.toList)
  | papN f arity args => exact .pap (RValsIso.refl args.toList)

theorem symm {r : Nat → Nat → Prop} {left right : Node}
    (h : NodeIso r left right) : NodeIso (fun x y => r y x) right left := by
  cases h with
  | ctor h => exact .ctor (rvalsIso_symm h)
  | pap h => exact .pap (rvalsIso_symm h)

theorem trans {r₁ r₂ : Nat → Nat → Prop} {left middle right : Node}
    (h₁ : NodeIso r₁ left middle) (h₂ : NodeIso r₂ middle right) :
    NodeIso (fun x z => ∃ y, r₁ x y ∧ r₂ y z) left right := by
  cases h₁ <;> cases h₂
  · exact .ctor (rvalsIso_trans ‹_› ‹_›)
  · exact .pap (rvalsIso_trans ‹_› ‹_›)

end NodeIso

namespace NodeBoxIso

theorem mono {r₁ r₂ : Nat → Nat → Prop}
    (hmono : ∀ {l r}, r₁ l r → r₂ l r)
    {left right : NodeBox} (h : NodeBoxIso r₁ left right) :
    NodeBoxIso r₂ left right :=
  ⟨h.world, h.rc, h.node.mono hmono⟩

theorem refl (box : NodeBox) :
    NodeBoxIso (fun l r => l = r) box box :=
  ⟨rfl, rfl, NodeIso.refl box.node⟩

theorem symm {r : Nat → Nat → Prop} {left right : NodeBox}
    (h : NodeBoxIso r left right) :
    NodeBoxIso (fun x y => r y x) right left :=
  ⟨h.world.symm, h.rc.symm, h.node.symm⟩

theorem trans {r₁ r₂ : Nat → Nat → Prop}
    {left middle right : NodeBox} (h₁ : NodeBoxIso r₁ left middle)
    (h₂ : NodeBoxIso r₂ middle right) :
    NodeBoxIso (fun x z => ∃ y, r₁ x y ∧ r₂ y z) left right :=
  ⟨h₁.world.trans h₂.world, h₁.rc.trans h₂.rc, h₁.node.trans h₂.node⟩

end NodeBoxIso

private def liveEq (store : Store) (left right : Nat) : Prop :=
  left = right ∧ ∃ box, store.get? left = some box

private theorem rvalIso_live_refl (store : Store) {v : RVal}
    (h : LiveRVal store v) : RValIso (liveEq store) v v := by
  cases v with
  | loc loc => exact .loc ⟨rfl, h⟩
  | lit l => exact .lit
  | erased => exact .erased

private theorem rvalsIso_live_refl (store : Store) :
    ∀ {values : List RVal},
      (∀ v ∈ values, LiveRVal store v) →
      RValsIso (liveEq store) values values
  | [], _ => .nil
  | v :: rest, h =>
    .cons (rvalIso_live_refl store (h v (by simp)))
      (rvalsIso_live_refl store (fun x hx => h x (by simp [hx])))

private theorem nodeBoxIso_live_refl {store : Store} (closed : StoreClosed store)
    {loc : Nat} {box : NodeBox} (hbox : store.get? loc = some box) :
    NodeBoxIso (liveEq store) box box := by
  refine ⟨rfl, rfl, ?_⟩
  cases hnode : box.node with
  | ctorN cid fields =>
    exact .ctor (rvalsIso_live_refl store
      (fun v hv => closed hbox v (by simpa [nodeChildren, hnode] using hv)))
  | papN f arity args =>
    exact .pap (rvalsIso_live_refl store
      (fun v hv => closed hbox v (by simpa [nodeChildren, hnode] using hv)))

namespace HeapIso

@[simp] theorem get?_fresh (store : Store) :
    store.get? store.nodes.size = none := by
  simp [Store.get?]

@[simp] theorem get?_allocNode_new (store : Store) (world : Owned)
    (node : Node) :
    (store.allocNode world node).1.get? (store.allocNode world node).2 =
      some ⟨world, 1, node⟩ := by
  simp [Store.allocNode, Store.get?]

theorem get?_allocNode_old {store : Store} {world : Owned} {node : Node}
    {loc : Nat} {box : NodeBox} (h : store.get? loc = some box) :
    (store.allocNode world node).1.get? loc = some box := by
  have hne : loc ≠ store.nodes.size := by
    intro heq
    subst loc
    rw [get?_fresh] at h
    contradiction
  simpa [Store.allocNode, Store.get?, Array.getElem?_push, hne] using h

theorem get?_of_allocNode_old {store : Store} {world : Owned} {node : Node}
    {loc : Nat} {box : NodeBox} (hne : loc ≠ store.nodes.size)
    (h : (store.allocNode world node).1.get? loc = some box) :
    store.get? loc = some box := by
  simpa [Store.allocNode, Store.get?, Array.getElem?_push, hne] using h

/-- Every heap is isomorphic to itself on live locations. -/
def refl (store : Store) (closed : StoreClosed store) : HeapIso store store where
  locRel := liveEq store
  left_unique h₁ h₂ := h₁.1.symm.trans h₂.1
  right_unique h₁ h₂ := h₁.1.trans h₂.1.symm
  left_total := by intro loc box h; exact ⟨loc, rfl, box, h⟩
  right_total := by intro loc box h; exact ⟨loc, rfl, box, h⟩
  related_live := by
    intro leftLoc rightLoc h
    obtain ⟨rfl, box, hbox⟩ := h
    exact ⟨box, box, hbox, hbox, nodeBoxIso_live_refl closed hbox⟩

/-- Heap isomorphism is symmetric. -/
def symm {left right : Store} (iso : HeapIso left right) :
    HeapIso right left where
  locRel := fun r l => iso.locRel l r
  left_unique := iso.right_unique
  right_unique := iso.left_unique
  left_total := iso.right_total
  right_total := iso.left_total
  related_live := by
    intro rightLoc leftLoc h
    obtain ⟨leftBox, rightBox, hl, hr, hb⟩ := iso.related_live h
    exact ⟨rightBox, leftBox, hr, hl, hb.symm⟩

/-- Composition of finite live-location bijections. -/
def trans {left middle right : Store} (first : HeapIso left middle)
    (second : HeapIso middle right) : HeapIso left right where
  locRel := fun l r => ∃ m, first.locRel l m ∧ second.locRel m r
  left_unique := by
    intro l r₁ r₂ h₁ h₂
    obtain ⟨m₁, hl₁, hr₁⟩ := h₁
    obtain ⟨m₂, hl₂, hr₂⟩ := h₂
    have hm : m₁ = m₂ := first.left_unique hl₁ hl₂
    subst m₂
    exact second.left_unique hr₁ hr₂
  right_unique := by
    intro l₁ l₂ r h₁ h₂
    obtain ⟨m₁, hl₁, hr₁⟩ := h₁
    obtain ⟨m₂, hl₂, hr₂⟩ := h₂
    have hm : m₁ = m₂ := second.right_unique hr₁ hr₂
    subst m₂
    exact first.right_unique hl₁ hl₂
  left_total := by
    intro loc box hbox
    obtain ⟨mid, hmid⟩ := first.left_total hbox
    obtain ⟨leftBox, midBox, _, hmidLive, _⟩ :=
      first.related_live hmid
    obtain ⟨rightLoc, hright⟩ := second.left_total hmidLive
    exact ⟨rightLoc, mid, hmid, hright⟩
  right_total := by
    intro loc box hbox
    obtain ⟨mid, hmid⟩ := second.right_total hbox
    obtain ⟨midBox, rightBox, hmidLive, _, _⟩ :=
      second.related_live hmid
    obtain ⟨leftLoc, hleft⟩ := first.right_total hmidLive
    exact ⟨leftLoc, mid, hleft, hmid⟩
  related_live := by
    intro leftLoc rightLoc hrel
    obtain ⟨midLoc, hleftRel, hrightRel⟩ := hrel
    obtain ⟨leftBox, midBox₁, hleft, hmid₁, hbox₁⟩ :=
      first.related_live hleftRel
    obtain ⟨midBox₂, rightBox, hmid₂, hright, hbox₂⟩ :=
      second.related_live hrightRel
    have hm : midBox₁ = midBox₂ := Option.some.inj (hmid₁.symm.trans hmid₂)
    subst midBox₂
    exact ⟨leftBox, rightBox, hleft, hright, hbox₁.trans hbox₂⟩

/-- Corresponding allocations extend the finite live-location bijection with
the two fresh append locations. -/
def alloc {left right : Store} (iso : HeapIso left right)
    {world : Owned} {leftNode rightNode : Node}
    (hnode : NodeIso iso.locRel leftNode rightNode) :
    HeapIso (left.allocNode world leftNode).1
      (right.allocNode world rightNode).1 := by
  let leftLoc := left.nodes.size
  let rightLoc := right.nodes.size
  let extended : Nat → Nat → Prop := fun l r =>
    (l = leftLoc ∧ r = rightLoc) ∨ iso.locRel l r
  have leftFresh : ∀ r, ¬ iso.locRel leftLoc r := by
    intro r hrel
    obtain ⟨leftBox, rightBox, hl, _, _⟩ := iso.related_live hrel
    have : left.get? leftLoc = none := by
      simp [leftLoc]
    rw [this] at hl
    contradiction
  have rightFresh : ∀ l, ¬ iso.locRel l rightLoc := by
    intro l hrel
    obtain ⟨leftBox, rightBox, _, hr, _⟩ := iso.related_live hrel
    have : right.get? rightLoc = none := by
      simp [rightLoc]
    rw [this] at hr
    contradiction
  refine
    { locRel := extended
      left_unique := ?_
      right_unique := ?_
      left_total := ?_
      right_total := ?_
      related_live := ?_ }
  · intro l r₁ r₂ h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact h₁.2.trans h₂.2.symm
    · rw [h₁.1] at h₂
      exact False.elim (leftFresh r₂ h₂)
    · rw [h₂.1] at h₁
      exact False.elim (leftFresh r₁ h₁)
    · exact iso.left_unique h₁ h₂
  · intro l₁ l₂ r h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact h₁.1.trans h₂.1.symm
    · rw [h₁.2] at h₂
      exact False.elim (rightFresh l₂ h₂)
    · rw [h₂.2] at h₁
      exact False.elim (rightFresh l₁ h₁)
    · exact iso.right_unique h₁ h₂
  · intro loc box hbox
    by_cases hnew : loc = leftLoc
    · exact ⟨rightLoc, .inl ⟨hnew, rfl⟩⟩
    · have hold : left.get? loc = some box := by
        apply get?_of_allocNode_old (by simpa [leftLoc] using hnew) hbox
      obtain ⟨r, hr⟩ := iso.left_total hold
      exact ⟨r, .inr hr⟩
  · intro loc box hbox
    by_cases hnew : loc = rightLoc
    · exact ⟨leftLoc, .inl ⟨rfl, hnew⟩⟩
    · have hold : right.get? loc = some box := by
        apply get?_of_allocNode_old (by simpa [rightLoc] using hnew) hbox
      obtain ⟨l, hl⟩ := iso.right_total hold
      exact ⟨l, .inr hl⟩
  · intro l r hrel
    rcases hrel with hnew | hold
    · obtain ⟨rfl, rfl⟩ := hnew
      refine ⟨⟨world, 1, leftNode⟩, ⟨world, 1, rightNode⟩, ?_, ?_, ?_⟩
      · exact get?_allocNode_new left world leftNode
      · exact get?_allocNode_new right world rightNode
      · exact ⟨rfl, rfl, hnode.mono (fun h => .inr h)⟩
    · obtain ⟨leftBox, rightBox, hl, hr, hb⟩ := iso.related_live hold
      refine ⟨leftBox, rightBox, get?_allocNode_old hl,
        get?_allocNode_old hr, hb.mono (fun h => .inr h)⟩

end HeapIso

/-! ## Exact ownership under heap isomorphism -/

private theorem sum_map_eq_of_bijective_rel
    {α β : Type} (rel : α → β → Prop) (leftValue : α → Nat)
    (rightValue : β → Nat) :
    ∀ (left : List α) (right : List β),
      left.Nodup → right.Nodup →
      (∀ x ∈ left, ∃ y ∈ right, rel x y) →
      (∀ y ∈ right, ∃ x ∈ left, rel x y) →
      (∀ {x y₁ y₂}, rel x y₁ → rel x y₂ → y₁ = y₂) →
      (∀ {x₁ x₂ y}, rel x₁ y → rel x₂ y → x₁ = x₂) →
      (∀ {x y}, rel x y → leftValue x = rightValue y) →
      (left.map leftValue).sum = (right.map rightValue).sum := by
  intro left
  induction left with
  | nil =>
      intro right _ _ _ rightTotal _ _ _
      cases right with
      | nil => rfl
      | cons y ys =>
          obtain ⟨x, member, _⟩ := rightTotal y (by simp)
          simp at member
  | cons x xs ih =>
      intro right leftNodup rightNodup leftTotal rightTotal
        leftFunctional rightFunctional values
      have xNotMem : x ∉ xs := (List.nodup_cons.mp leftNodup).1
      have xsNodup : xs.Nodup := (List.nodup_cons.mp leftNodup).2
      obtain ⟨y, yMember, related⟩ := leftTotal x (by simp)
      obtain ⟨before, after, rightEq⟩ := List.mem_iff_append.mp yMember
      subst right
      let rightRest := before ++ after
      have rearranged : (before ++ y :: after).Perm (y :: rightRest) := by
        exact List.perm_middle
      have rearrangedNodup : (y :: rightRest).Nodup :=
        rearranged.nodup rightNodup
      have yNotMem : y ∉ rightRest :=
        (List.nodup_cons.mp rearrangedNodup).1
      have rightRestNodup : rightRest.Nodup :=
        (List.nodup_cons.mp rearrangedNodup).2
      have tailLeftTotal : ∀ candidate ∈ xs,
          ∃ target ∈ rightRest, rel candidate target := by
        intro candidate candidateMember
        obtain ⟨target, targetMember, candidateRelated⟩ :=
          leftTotal candidate (by simp [candidateMember])
        have targetNe : target ≠ y := by
          intro equal
          subst target
          have candidateEq : candidate = x :=
            rightFunctional candidateRelated related
          subst candidate
          exact xNotMem candidateMember
        refine ⟨target, ?_, candidateRelated⟩
        change target ∈ before ++ after
        rw [List.mem_append]
        simp only [List.mem_append, List.mem_cons] at targetMember
        rcases targetMember with inBefore | targetMember
        · exact Or.inl inBefore
        · rcases targetMember with equal | inAfter
          · exact False.elim (targetNe equal)
          · exact Or.inr inAfter
      have tailRightTotal : ∀ target ∈ rightRest,
          ∃ candidate ∈ xs, rel candidate target := by
        intro target targetMember
        have targetMemberOriginal : target ∈ before ++ y :: after := by
          change target ∈ before ++ after at targetMember
          rw [List.mem_append] at targetMember
          rcases targetMember with inBefore | inAfter
          · exact List.mem_append.mpr (Or.inl inBefore)
          · exact List.mem_append.mpr
              (Or.inr (List.mem_cons.mpr (Or.inr inAfter)))
        obtain ⟨candidate, candidateMember, candidateRelated⟩ :=
          rightTotal target targetMemberOriginal
        have candidateNe : candidate ≠ x := by
          intro equal
          subst candidate
          have targetEq : target = y :=
            leftFunctional candidateRelated related
          subst target
          exact yNotMem targetMember
        refine ⟨candidate, ?_, candidateRelated⟩
        exact List.mem_of_ne_of_mem candidateNe candidateMember
      have tailSums := ih rightRest xsNodup rightRestNodup tailLeftTotal
        tailRightTotal leftFunctional rightFunctional values
      simp only [List.map_cons, List.sum_cons]
      rw [values related, tailSums]
      simp [rightRest, List.map_append, List.sum_append, Nat.add_left_comm]

private def indexedBoxes : List (Option NodeBox) → Nat →
    List (Nat × NodeBox)
  | [], _ => []
  | none :: rest, start => indexedBoxes rest (start + 1)
  | some box :: rest, start =>
      (start, box) :: indexedBoxes rest (start + 1)

private theorem indexedBoxes_eq_zipIdx_filterMap
    (entries : List (Option NodeBox)) (start : Nat) :
    indexedBoxes entries start =
      (entries.zipIdx start).filterMap fun (slot, location) =>
        slot.map fun box => (location, box) := by
  induction entries generalizing start with
  | nil => rfl
  | cons head tail ih =>
      cases head <;> simp [indexedBoxes, ih]

private def liveBoxes (store : Store) : List (Nat × NodeBox) :=
  indexedBoxes store.nodes.toList 0

private theorem mem_liveBoxes_iff {store : Store} {location : Nat}
    {box : NodeBox} :
    (location, box) ∈ liveBoxes store ↔ store.get? location = some box := by
  constructor
  · intro member
    rw [liveBoxes, indexedBoxes_eq_zipIdx_filterMap,
      List.mem_filterMap] at member
    obtain ⟨entry, entryMember, mapped⟩ := member
    rcases entry with ⟨slot, index⟩
    cases slot with
    | none => simp at mapped
    | some entryBox =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at mapped
        obtain ⟨locationEq, boxEq⟩ := mapped
        subst index
        subst entryBox
        have indexed := List.mem_zipIdx entryMember
        obtain ⟨_lower, upper, slotEq⟩ := indexed
        have listAt : store.nodes.toList[location]? = some (some box) := by
          rw [List.getElem?_eq_getElem (by simpa using upper)]
          exact congrArg some slotEq.symm
        have arrayAt : store.nodes[location]? = some (some box) := by
          simpa using listAt
        simp [Store.get?, arrayAt]
  · intro found
    have arrayAt : store.nodes[location]? = some (some box) := by
      cases slot : store.nodes[location]? with
      | none => simp [Store.get?, slot] at found
      | some entry =>
          cases entry with
          | none => simp [Store.get?, slot] at found
          | some entryBox =>
              have boxEq : entryBox = box := by
                simpa [Store.get?, slot] using found
              subst entryBox
              rfl
    have listAt : store.nodes.toList[location]? = some (some box) := by
      simpa using arrayAt
    have zippedAt : store.nodes.toList.zipIdx[location]? =
        some (some box, location) := by
      rw [List.getElem?_zipIdx]
      simpa using listAt
    have zippedMember : (some box, location) ∈
        store.nodes.toList.zipIdx := List.mem_of_getElem? zippedAt
    rw [liveBoxes, indexedBoxes_eq_zipIdx_filterMap,
      List.mem_filterMap]
    exact ⟨(some box, location), zippedMember, by simp⟩

private theorem indexedBoxes_location_ge
    {entries : List (Option NodeBox)} {start location : Nat}
    {box : NodeBox} (member : (location, box) ∈ indexedBoxes entries start) :
    start ≤ location := by
  induction entries generalizing start with
  | nil => simp [indexedBoxes] at member
  | cons head tail ih =>
      cases head with
      | none =>
          exact Nat.le_trans (Nat.le_add_right start 1)
            (ih (start := start + 1) member)
      | some headBox =>
          simp only [indexedBoxes, List.mem_cons] at member
          rcases member with equal | member
          · exact Nat.le_of_eq (congrArg Prod.fst equal).symm
          · exact Nat.le_trans (Nat.le_add_right start 1)
              (ih (start := start + 1) member)

private theorem indexedBoxes_nodup (entries : List (Option NodeBox)) :
    ∀ start, (indexedBoxes entries start).Nodup := by
  induction entries with
  | nil => simp [indexedBoxes]
  | cons head tail ih =>
      intro start
      cases head with
      | none => exact ih (start + 1)
      | some box =>
          rw [indexedBoxes, List.nodup_cons]
          refine ⟨?_, ih (start + 1)⟩
          intro member
          have bound := indexedBoxes_location_ge member
          omega

private theorem liveBoxes_nodup (store : Store) :
    (liveBoxes store).Nodup := by
  exact indexedBoxes_nodup store.nodes.toList 0

private def boxEdgeCount (needle : Nat) (entry : Nat × NodeBox) : Nat :=
  ((nodeChildren entry.2.node).filterMap rvalLocation?).count needle

private theorem edgeCount_indexedBoxes
    (entries : List (Option NodeBox)) (start needle : Nat) :
    (entries.flatMap slotEdgeLocations).count needle =
      ((indexedBoxes entries start).map (boxEdgeCount needle)).sum := by
  induction entries generalizing start with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | none => simpa [indexedBoxes, slotEdgeLocations] using ih (start + 1)
      | some box =>
          simp [indexedBoxes, slotEdgeLocations, boxEdgeCount,
            List.count_append, ih (start + 1)]

private theorem edgeLocations_count_eq_liveBoxes_sum
    (store : Store) (needle : Nat) :
    (edgeLocations store).count needle =
      ((liveBoxes store).map (boxEdgeCount needle)).sum := by
  exact edgeCount_indexedBoxes store.nodes.toList 0 needle

private theorem RValsIso.locationCount_eq
    {left right : Store} (iso : HeapIso left right)
    {leftLoc rightLoc : Nat} (locations : iso.locRel leftLoc rightLoc) :
    ∀ {leftValues rightValues : List RVal},
      RValsIso iso.locRel leftValues rightValues →
      (leftValues.filterMap rvalLocation?).count leftLoc =
        (rightValues.filterMap rvalLocation?).count rightLoc
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      have tailEq := RValsIso.locationCount_eq iso locations tail
      cases head with
      | @loc headLeft headRight related =>
          have iff : headLeft = leftLoc ↔ headRight = rightLoc := by
            constructor
            · intro equal
              subst_vars
              exact iso.left_unique related locations
            · intro equal
              subst_vars
              exact iso.right_unique related locations
          by_cases leftEqual : headLeft = leftLoc
          · have rightEqual := iff.mp leftEqual
            simp [rvalLocation?, leftEqual, rightEqual, tailEq]
          · have rightNe : headRight ≠ rightLoc := fun rightEqual =>
              leftEqual (iff.mpr rightEqual)
            simp [rvalLocation?, leftEqual, rightNe, tailEq]
      | lit => simpa [rvalLocation?, tailEq]
      | erased => simpa [rvalLocation?, tailEq]

private theorem NodeIso.edgeCount_eq
    {left right : Store} (iso : HeapIso left right)
    {leftLoc rightLoc : Nat} (locations : iso.locRel leftLoc rightLoc)
    {leftNode rightNode : Node} (nodes : NodeIso iso.locRel leftNode rightNode) :
    ((nodeChildren leftNode).filterMap rvalLocation?).count leftLoc =
      ((nodeChildren rightNode).filterMap rvalLocation?).count rightLoc := by
  cases nodes with
  | ctor fields =>
      exact RValsIso.locationCount_eq iso locations fields
  | pap args =>
      exact RValsIso.locationCount_eq iso locations args

private def liveBoxRel {left right : Store} (iso : HeapIso left right)
    (leftEntry rightEntry : Nat × NodeBox) : Prop :=
  iso.locRel leftEntry.1 rightEntry.1 ∧
    left.get? leftEntry.1 = some leftEntry.2 ∧
    right.get? rightEntry.1 = some rightEntry.2

private theorem HeapIso.edgeLocations_count_eq
    {left right : Store} (iso : HeapIso left right)
    {leftLoc rightLoc : Nat} (locations : iso.locRel leftLoc rightLoc) :
    (edgeLocations left).count leftLoc =
      (edgeLocations right).count rightLoc := by
  rw [edgeLocations_count_eq_liveBoxes_sum,
    edgeLocations_count_eq_liveBoxes_sum]
  apply sum_map_eq_of_bijective_rel (liveBoxRel iso)
    (boxEdgeCount leftLoc) (boxEdgeCount rightLoc)
    (liveBoxes left) (liveBoxes right)
  · exact liveBoxes_nodup left
  · exact liveBoxes_nodup right
  · intro leftEntry leftMember
    rcases leftEntry with ⟨entryLoc, entryBox⟩
    have leftLive := mem_liveBoxes_iff.mp leftMember
    obtain ⟨rightEntryLoc, related⟩ := iso.left_total leftLive
    obtain ⟨relatedLeftBox, rightEntryBox, relatedLeftLive,
      rightLive, _⟩ := iso.related_live related
    have leftBoxEq : relatedLeftBox = entryBox :=
      Option.some.inj (relatedLeftLive.symm.trans leftLive)
    subst relatedLeftBox
    exact ⟨(rightEntryLoc, rightEntryBox),
      mem_liveBoxes_iff.mpr rightLive, related, leftLive, rightLive⟩
  · intro rightEntry rightMember
    rcases rightEntry with ⟨entryLoc, entryBox⟩
    have rightLive := mem_liveBoxes_iff.mp rightMember
    obtain ⟨leftEntryLoc, related⟩ := iso.right_total rightLive
    obtain ⟨leftEntryBox, relatedRightBox, leftLive,
      relatedRightLive, _⟩ := iso.related_live related
    have rightBoxEq : relatedRightBox = entryBox :=
      Option.some.inj (relatedRightLive.symm.trans rightLive)
    subst relatedRightBox
    exact ⟨(leftEntryLoc, leftEntryBox),
      mem_liveBoxes_iff.mpr leftLive, related, leftLive, rightLive⟩
  · intro leftEntry rightEntry₁ rightEntry₂ first second
    rcases leftEntry with ⟨leftEntryLoc, leftEntryBox⟩
    rcases rightEntry₁ with ⟨rightEntryLoc₁, rightEntryBox₁⟩
    rcases rightEntry₂ with ⟨rightEntryLoc₂, rightEntryBox₂⟩
    have locationEq : rightEntryLoc₁ = rightEntryLoc₂ :=
      iso.left_unique first.1 second.1
    subst rightEntryLoc₂
    have boxEq : rightEntryBox₁ = rightEntryBox₂ :=
      Option.some.inj (first.2.2.symm.trans second.2.2)
    subst rightEntryBox₂
    rfl
  · intro leftEntry₁ leftEntry₂ rightEntry first second
    rcases leftEntry₁ with ⟨leftEntryLoc₁, leftEntryBox₁⟩
    rcases leftEntry₂ with ⟨leftEntryLoc₂, leftEntryBox₂⟩
    rcases rightEntry with ⟨rightEntryLoc, rightEntryBox⟩
    have locationEq : leftEntryLoc₁ = leftEntryLoc₂ :=
      iso.right_unique first.1 second.1
    subst leftEntryLoc₂
    have boxEq : leftEntryBox₁ = leftEntryBox₂ :=
      Option.some.inj (first.2.1.symm.trans second.2.1)
    subst leftEntryBox₂
    rfl
  · intro leftEntry rightEntry related
    rcases leftEntry with ⟨leftEntryLoc, leftEntryBox⟩
    rcases rightEntry with ⟨rightEntryLoc, rightEntryBox⟩
    obtain ⟨relatedLeftBox, relatedRightBox, leftLive, rightLive,
      boxes⟩ := iso.related_live related.1
    have leftBoxEq : relatedLeftBox = leftEntryBox :=
      Option.some.inj (leftLive.symm.trans related.2.1)
    have rightBoxEq : relatedRightBox = rightEntryBox :=
      Option.some.inj (rightLive.symm.trans related.2.2)
    subst relatedLeftBox
    subst relatedRightBox
    exact boxes.node.edgeCount_eq iso locations

/-- External roots agree in ownership world and runtime value modulo a
location relation. -/
structure RootIso (locRel : Nat → Nat → Prop) (left right : Root) : Prop where
  world : left.world = right.world
  value : RValIso locRel left.value right.value

/-- Pointwise root-list agreement modulo a location relation. -/
inductive RootsIso (locRel : Nat → Nat → Prop) :
    List Root → List Root → Prop where
  | nil : RootsIso locRel [] []
  | cons {left right : Root} {lefts rights : List Root} :
      RootIso locRel left right →
      RootsIso locRel lefts rights →
      RootsIso locRel (left :: lefts) (right :: rights)

namespace RootIso

theorem mono {first second : Nat → Nat → Prop}
    (lift : ∀ {left right}, first left right → second left right)
    {left right : Root} (root : RootIso first left right) :
    RootIso second left right :=
  ⟨root.world, root.value.mono lift⟩

theorem symm {locRel : Nat → Nat → Prop} {left right : Root}
    (root : RootIso locRel left right) :
    RootIso (fun rightLoc leftLoc => locRel leftLoc rightLoc) right left :=
  ⟨root.world.symm, root.value.symm⟩

/-- A heap isomorphism determines at most one root preimage for a fixed
target root. -/
theorem left_eq_of_right {leftStore rightStore : Store}
    (iso : HeapIso leftStore rightStore)
    {left₁ left₂ right : Root}
    (first : RootIso iso.locRel left₁ right)
    (second : RootIso iso.locRel left₂ right) : left₁ = left₂ := by
  rcases left₁ with ⟨leftWorld₁, leftValue₁⟩
  rcases left₂ with ⟨leftWorld₂, leftValue₂⟩
  rcases right with ⟨rightWorld, rightValue⟩
  have worldEq : leftWorld₁ = leftWorld₂ :=
    first.world.trans second.world.symm
  subst leftWorld₂
  congr 1
  cases first.value with
  | loc firstRelated =>
      cases second.value with
      | loc secondRelated =>
          exact congrArg RVal.loc
            (iso.right_unique firstRelated secondRelated)
  | lit => cases second.value; rfl
  | erased => cases second.value; rfl

end RootIso

namespace HeapIso

/-- Heap-world evidence follows a related runtime value across a heap
isomorphism. -/
theorem hasWorld {left right : Store} (iso : HeapIso left right)
    {leftValue rightValue : RVal}
    (value : RValIso iso.locRel leftValue rightValue)
    {world : Ix.Compiler.Ixon.Owned}
    (hasWorld : HasWorld left world leftValue) :
    HasWorld right world rightValue := by
  cases value with
  | loc related =>
      obtain ⟨sourceBox, sourceLive, sourceWorld⟩ := hasWorld
      obtain ⟨relatedSourceBox, targetBox, relatedSourceLive, targetLive,
        boxes⟩ := iso.related_live related
      have boxEq : sourceBox = relatedSourceBox :=
        Option.some.inj (sourceLive.symm.trans relatedSourceLive)
      subst sourceBox
      exact ⟨targetBox, targetLive, boxes.world.symm.trans sourceWorld⟩
  | lit => trivial
  | erased => trivial

end HeapIso

namespace RootsIso

theorem mono {first second : Nat → Nat → Prop}
    (lift : ∀ {left right}, first left right → second left right) :
    ∀ {left right : List Root}, RootsIso first left right →
      RootsIso second left right
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (head.mono lift) (tail.mono lift)

theorem symm {locRel : Nat → Nat → Prop} :
    ∀ {left right : List Root}, RootsIso locRel left right →
      RootsIso (fun rightLoc leftLoc => locRel leftLoc rightLoc) right left
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons head.symm tail.symm

/-- Homogeneous root framing preserves a pointwise runtime-value
isomorphism. -/
theorem rootsFor {locRel : Nat → Nat → Prop}
    (world : Ix.Compiler.Ixon.Owned) :
    ∀ {left right : List RVal}, RValsIso locRel left right →
      RootsIso locRel (rootsFor world left) (rootsFor world right)
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons ⟨rfl, head⟩ (rootsFor world tail)

/-- Pointwise root isomorphisms concatenate. -/
theorem append {locRel : Nat → Nat → Prop}
    {leftPrefix rightPrefix leftSuffix rightSuffix : List Root}
    (first : RootsIso locRel leftPrefix rightPrefix)
    (suffix : RootsIso locRel leftSuffix rightSuffix) :
    RootsIso locRel (leftPrefix ++ leftSuffix)
      (rightPrefix ++ rightSuffix) := by
  induction first with
  | nil => exact suffix
  | cons head tail ih => exact .cons head ih

theorem tail {locRel : Nat → Nat → Prop} {left right : Root}
    {lefts rights : List Root}
    (roots : RootsIso locRel (left :: lefts) (right :: rights)) :
    RootsIso locRel lefts rights := by
  cases roots with
  | cons head tail => exact tail

/-- Dropping equal pointwise prefixes preserves root-list isomorphism. -/
theorem drop {locRel : Nat → Nat → Prop} :
    ∀ {left right : List Root}, RootsIso locRel left right →
      ∀ count, RootsIso locRel (left.drop count) (right.drop count)
  | _, _, .nil, count => by cases count <;> exact .nil
  | _, _, .cons head tail, 0 => .cons head tail
  | _, _, .cons head tail, count + 1 => tail.drop count

theorem left_of_right_mem {locRel : Nat → Nat → Prop} :
    ∀ {left right : List Root}, RootsIso locRel left right →
      ∀ {rightRoot}, rightRoot ∈ right →
        ∃ leftRoot, leftRoot ∈ left ∧ RootIso locRel leftRoot rightRoot
  | _, _, .nil, _, member => by simp at member
  | _, _, .cons head tail, rightRoot, member => by
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst rightRoot
        exact ⟨_, by simp, head⟩
      · obtain ⟨leftRoot, leftMember, related⟩ :=
          tail.left_of_right_mem member
        exact ⟨leftRoot, by simp [leftMember], related⟩

/-- Pointwise root preimages of the same target list are unique. -/
theorem left_eq_of_right {leftStore rightStore : Store}
    (iso : HeapIso leftStore rightStore) :
    ∀ {left₁ left₂ right : List Root},
      RootsIso iso.locRel left₁ right →
      RootsIso iso.locRel left₂ right →
      left₁ = left₂
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons firstHead firstTail, .cons secondHead secondTail => by
      have headEq := RootIso.left_eq_of_right iso firstHead secondHead
      have tailEq := RootsIso.left_eq_of_right iso firstTail secondTail
      rw [headEq, tailEq]

/-- Reorder the target presentation of a pointwise root isomorphism while
applying the same permutation to its source presentation. -/
theorem permuteRight {locRel : Nat → Nat → Prop}
    {left right right' : List Root}
    (roots : RootsIso locRel left right) (permutation : right.Perm right') :
    ∃ left', left.Perm left' ∧ RootsIso locRel left' right' := by
  induction permutation generalizing left with
  | nil =>
      cases roots
      exact ⟨[], .refl [], .nil⟩
  | cons root permutation ih =>
      cases roots with
      | cons head tail =>
          obtain ⟨leftTail, tailPermutation, tailRoots⟩ := ih tail
          exact ⟨_ :: leftTail, tailPermutation.cons _, .cons head tailRoots⟩
  | swap first second rest =>
      cases roots with
      | cons firstRoot roots =>
          cases roots with
          | cons secondRoot tail =>
              exact ⟨_, .swap _ _ _, .cons secondRoot (.cons firstRoot tail)⟩
  | trans first second firstIh secondIh =>
      obtain ⟨middleLeft, firstPerm, middleRoots⟩ := firstIh roots
      obtain ⟨rightLeft, secondPerm, rightRoots⟩ := secondIh middleRoots
      exact ⟨rightLeft, firstPerm.trans secondPerm, rightRoots⟩

private theorem values {locRel : Nat → Nat → Prop} :
    ∀ {left right : List Root}, RootsIso locRel left right →
      RValsIso locRel (left.map Root.value) (right.map Root.value)
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons head.value tail.values

private theorem right_hasWorld {left right : Store} (iso : HeapIso left right)
    {leftRoots rightRoots : List Root}
    (roots : RootsIso iso.locRel leftRoots rightRoots)
    (leftWorlds : ∀ root ∈ leftRoots,
      HasWorld left root.world root.value) :
    ∀ root ∈ rightRoots, HasWorld right root.world root.value := by
  induction roots with
  | nil => intro root member; simp at member
  | @cons leftRoot rightRoot leftRoots rightRoots head tail ih =>
    intro root member
    have tailWorlds : ∀ candidate ∈ leftRoots,
        HasWorld left candidate.world candidate.value := by
      intro candidate candidateMember
      exact leftWorlds candidate (by simp [candidateMember])
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst root
      have leftWorld := leftWorlds leftRoot (by simp)
      have rightWorld := iso.hasWorld head.value leftWorld
      simpa [head.world] using rightWorld
    · exact ih tailWorlds root member

private theorem locationCount_eq {left right : Store} (iso : HeapIso left right)
    {leftLoc rightLoc : Nat} (locations : iso.locRel leftLoc rightLoc)
    {leftRoots rightRoots : List Root}
    (roots : RootsIso iso.locRel leftRoots rightRoots) :
    (leftRoots.filterMap rootLocation?).count leftLoc =
      (rightRoots.filterMap rootLocation?).count rightLoc := by
  have values := RValsIso.locationCount_eq iso locations roots.values
  have locationFunction :
      (rvalLocation? ∘ Root.value) = rootLocation? := by
    funext root
    rfl
  simpa only [List.filterMap_map, locationFunction] using values

end RootsIso

namespace HeapIso

/-- Incoming ownership multiplicity is invariant under corresponding heap
and root-list renamings. -/
theorem incoming_eq {left right : Store} (iso : HeapIso left right)
    {leftRoots rightRoots : List Root}
    (roots : RootsIso iso.locRel leftRoots rightRoots)
    {leftLoc rightLoc : Nat} (locations : iso.locRel leftLoc rightLoc) :
    incoming left leftRoots leftLoc = incoming right rightRoots rightLoc := by
  unfold incoming
  rw [List.count_append, List.count_append,
    roots.locationCount_eq iso locations,
    iso.edgeLocations_count_eq locations]

end HeapIso

private theorem RValsIso.left_of_right_mem {locRel : Nat → Nat → Prop} :
    ∀ {left right : List RVal}, RValsIso locRel left right →
      ∀ {rightValue}, rightValue ∈ right →
        ∃ leftValue, leftValue ∈ left ∧
          RValIso locRel leftValue rightValue
  | _, _, .nil, _, member => by simp at member
  | _, _, .cons head tail, rightValue, member => by
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst rightValue
        exact ⟨_, by simp, head⟩
      · obtain ⟨leftValue, leftMember, related⟩ :=
          tail.left_of_right_mem member
        exact ⟨leftValue, by simp [leftMember], related⟩

private theorem NodeIso.children {locRel : Nat → Nat → Prop}
    {left right : Node} (nodes : NodeIso locRel left right) :
    RValsIso locRel (nodeChildren left) (nodeChildren right) := by
  cases nodes with
  | ctor fields => exact fields
  | pap args => exact args

private theorem NodeIso.left_pap_of_right {locRel : Nat → Nat → Prop}
    {left : Node} {f : Ix.Compiler.Ixon.Address} {arity : Nat}
    {rightArgs : Array RVal}
    (nodes : NodeIso locRel left (.papN f arity rightArgs)) :
    ∃ leftArgs, left = .papN f arity leftArgs := by
  cases nodes with
  | pap fields => exact ⟨_, rfl⟩

namespace HeapIso

/-- Exact ownership is invariant under a heap isomorphism when the external
root list is renamed pointwise by the same location relation. -/
theorem rootOwnership {left right : Store} (iso : HeapIso left right)
    {leftRoots rightRoots : List Root}
    (roots : RootsIso iso.locRel leftRoots rightRoots)
    (owned : RootOwnership left leftRoots) :
    RootOwnership right rightRoots := by
  refine ⟨roots.right_hasWorld iso owned.roots_world, ?_, ?_, ?_⟩
  · intro rightLoc rightBox rightLive child childMember
    obtain ⟨leftLoc, related⟩ := iso.right_total rightLive
    obtain ⟨leftBox, relatedRightBox, leftLive, relatedRightLive,
      boxes⟩ := iso.related_live related
    have rightBoxEq : relatedRightBox = rightBox :=
      Option.some.inj (relatedRightLive.symm.trans rightLive)
    subst relatedRightBox
    obtain ⟨leftChild, leftMember, children⟩ :=
      boxes.node.children.left_of_right_mem childMember
    have leftWorld := owned.edges_world leftLive leftChild leftMember
    have rightWorld := iso.hasWorld children leftWorld
    simpa [boxes.world] using rightWorld
  · intro rightLoc rightBox f arity args rightLive rightNode
    obtain ⟨leftLoc, related⟩ := iso.right_total rightLive
    obtain ⟨leftBox, relatedRightBox, leftLive, relatedRightLive,
      boxes⟩ := iso.related_live related
    have rightBoxEq : relatedRightBox = rightBox :=
      Option.some.inj (relatedRightLive.symm.trans rightLive)
    subst relatedRightBox
    have nodes : NodeIso iso.locRel leftBox.node (.papN f arity args) := by
      simpa [rightNode] using boxes.node
    obtain ⟨leftArgs, leftNode⟩ := nodes.left_pap_of_right
    have leftShared := owned.pap_shared leftLive leftNode
    exact boxes.world ▸ leftShared
  · intro rightLoc rightBox rightLive
    obtain ⟨leftLoc, related⟩ := iso.right_total rightLive
    obtain ⟨leftBox, relatedRightBox, leftLive, relatedRightLive,
      boxes⟩ := iso.related_live related
    have rightBoxEq : relatedRightBox = rightBox :=
      Option.some.inj (relatedRightLive.symm.trans rightLive)
    subst relatedRightBox
    have leftCounts := owned.counts leftLive
    have incomingEq := iso.incoming_eq roots related
    rw [← boxes.world, ← boxes.rc, ← incomingEq]
    exact leftCounts

private theorem preimageRoot {left right : Store} (iso : HeapIso left right)
    (root : Root) (world : HasWorld right root.world root.value) :
    ∃ leftRoot, RootIso iso.locRel leftRoot root := by
  rcases root with ⟨rootWorld, value⟩
  cases value with
  | loc rightLoc =>
      obtain ⟨rightBox, rightLive, _rightWorld⟩ := world
      obtain ⟨leftLoc, related⟩ := iso.right_total rightLive
      exact ⟨⟨rootWorld, .loc leftLoc⟩, rfl, .loc related⟩
  | lit literal =>
      exact ⟨⟨rootWorld, .lit literal⟩, rfl, .lit⟩
  | erased =>
      exact ⟨⟨rootWorld, .erased⟩, rfl, .erased⟩

private theorem rootsIsoPreimage {left right : Store}
    (iso : HeapIso left right) :
    ∀ (rightRoots : List Root),
      (∀ root ∈ rightRoots, HasWorld right root.world root.value) →
      ∃ leftRoots, RootsIso iso.locRel leftRoots rightRoots
  | [], _ => ⟨[], .nil⟩
  | root :: rest, worlds => by
      obtain ⟨leftRoot, head⟩ := iso.preimageRoot root
        (worlds root (by simp))
      obtain ⟨leftRest, tail⟩ := iso.rootsIsoPreimage rest
        (fun candidate member => worlds candidate (by simp [member]))
      exact ⟨leftRoot :: leftRest, .cons head tail⟩

/-- Pull an exact external-root presentation backward through a heap
isomorphism. The returned list preserves root order and worlds while replacing
each live location by its unique preimage. -/
theorem rootOwnershipPreimage {left right : Store} (iso : HeapIso left right)
    {rightRoots : List Root} (owned : RootOwnership right rightRoots) :
    ∃ leftRoots,
      RootsIso iso.locRel leftRoots rightRoots ∧
        RootOwnership left leftRoots := by
  obtain ⟨leftRoots, roots⟩ :=
    iso.rootsIsoPreimage rightRoots owned.roots_world
  exact ⟨leftRoots, roots, iso.symm.rootOwnership roots.symm owned⟩

/-- Pull a cons-root ownership presentation backward while fixing a known
preimage for its distinguished head. -/
theorem rootOwnershipPreimageCons {left right : Store}
    (iso : HeapIso left right) {leftRoot rightRoot : Root}
    {rightRest : List Root} (head : RootIso iso.locRel leftRoot rightRoot)
    (owned : RootOwnership right (rightRoot :: rightRest)) :
    ∃ leftRest,
      RootsIso iso.locRel (leftRoot :: leftRest) (rightRoot :: rightRest) ∧
        RootOwnership left (leftRoot :: leftRest) := by
  obtain ⟨leftRest, tail⟩ := iso.rootsIsoPreimage rightRest
    (fun root member => owned.roots_world root (by simp [member]))
  let roots : RootsIso iso.locRel (leftRoot :: leftRest)
      (rightRoot :: rightRest) := .cons head tail
  exact ⟨leftRest, roots, iso.symm.rootOwnership roots.symm owned⟩

/-- Pull an ownership presentation backward while fixing any pointwise-related
root prefix and choosing only the ambient preimage tail. -/
theorem rootOwnershipPreimageAppend {left right : Store}
    (iso : HeapIso left right)
    {leftPrefix rightPrefix rightRest : List Root}
    (first : RootsIso iso.locRel leftPrefix rightPrefix)
    (owned : RootOwnership right (rightPrefix ++ rightRest)) :
    ∃ leftRest,
      RootsIso iso.locRel (leftPrefix ++ leftRest)
          (rightPrefix ++ rightRest) ∧
        RootOwnership left (leftPrefix ++ leftRest) := by
  obtain ⟨leftRest, tail⟩ := iso.rootsIsoPreimage rightRest
    (fun root member => owned.roots_world root
      (List.mem_append_right rightPrefix member))
  let roots := first.append tail
  exact ⟨leftRest, roots, iso.symm.rootOwnership roots.symm owned⟩

end HeapIso

/-- Appending a fresh heap node preserves every existing live node shape. -/
theorem StoreGraphExtends.allocNode (store : Store) (world : Owned)
    (node : Node) :
    StoreGraphExtends store (store.allocNode world node).1 := by
  intro loc boxWorld rc oldNode hget
  exact ⟨rc, HeapIso.get?_allocNode_old hget⟩

/-! ## Allocation and exact ownership -/

private theorem flatMap_set_eq_self {α β : Type} (f : α → List β) :
    ∀ {values : List α} {idx : Nat} {old new : α},
      values[idx]? = some old → f new = f old →
      (values.set idx new).flatMap f = values.flatMap f
  | [], idx, old, new, hget, _ => by simp at hget
  | value :: rest, 0, old, new, hget, hsame => by
    simp at hget
    subst old
    simp [hsame]
  | value :: rest, idx + 1, old, new, hget, hsame => by
    simp only [List.getElem?_cons_succ] at hget
    simp [flatMap_set_eq_self f hget hsame]

theorem nodes_get?_of_get? {store : Store} {loc : Nat} {box : NodeBox}
    (h : store.get? loc = some box) :
    store.nodes[loc]? = some (some box) := by
  rw [Store.get?, Option.bind_eq_some_iff] at h
  obtain ⟨slot, hslot, hid⟩ := h
  change slot = some box at hid
  subst slot
  exact hslot

theorem get?_setBox_same {store : Store} {loc : Nat} {old new : NodeBox}
    (h : store.get? loc = some old) :
    (store.setBox loc new).get? loc = some new := by
  have hnodes := nodes_get?_of_get? h
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnodes
  simp [Store.setBox, Store.get?, Array.set!_eq_setIfInBounds, hlt]

theorem get?_setBox_other {store : Store} {loc other : Nat}
    {old new box : NodeBox} (hne : loc ≠ other)
    (hlive : store.get? loc = some old) (h : store.get? other = some box) :
    (store.setBox loc new).get? other = some box := by
  have hnodes := nodes_get?_of_get? hlive
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnodes
  simpa [Store.setBox, Store.get?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, hlt, hne] using h

theorem get?_of_setBox_other {store : Store} {loc other : Nat}
    {old new box : NodeBox} (hne : loc ≠ other)
    (hlive : store.get? loc = some old)
    (h : (store.setBox loc new).get? other = some box) :
    store.get? other = some box := by
  have hnodes := nodes_get?_of_get? hlive
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnodes
  simpa [Store.setBox, Store.get?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, hlt, hne] using h

private theorem count_flatMap_set_remove {α β : Type} [BEq β]
    (f : α → List β) (needle : β) :
    ∀ {values : List α} {idx : Nat} {old new : α},
      values[idx]? = some old → f new = [] →
      List.count needle ((values.set idx new).flatMap f) +
          List.count needle (f old) =
        List.count needle (values.flatMap f)
  | [], idx, old, new, hget, _ => by simp at hget
  | value :: rest, 0, old, new, hget, hempty => by
    simp at hget
    subst old
    simp [hempty, List.count_append, Nat.add_comm]
  | value :: rest, idx + 1, old, new, hget, hempty => by
    simp only [List.getElem?_cons_succ] at hget
    simp only [List.set, List.flatMap_cons, List.count_append]
    have ih := count_flatMap_set_remove f needle hget hempty
    omega

private theorem count_flatMap_set_add {α β : Type} [BEq β]
    (f : α → List β) (needle : β) :
    ∀ {values : List α} {idx : Nat} {old new : α},
      values[idx]? = some old → f old = [] →
      List.count needle ((values.set idx new).flatMap f) =
        List.count needle (values.flatMap f) +
          List.count needle (f new)
  | [], idx, old, new, hget, _ => by simp at hget
  | value :: rest, 0, old, new, hget, hempty => by
    simp at hget
    subst old
    simp [hempty, List.count_append, Nat.add_comm]
  | value :: rest, idx + 1, old, new, hget, hempty => by
    simp only [List.getElem?_cons_succ] at hget
    simp only [List.set, List.flatMap_cons, List.count_append]
    have ih := count_flatMap_set_add f needle (new := new) hget hempty
    omega

theorem get?_kill_same {store : Store} {loc : Nat} {box : NodeBox}
    (h : store.get? loc = some box) : (store.kill loc).get? loc = none := by
  have hnodes := nodes_get?_of_get? h
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnodes
  simp [Store.kill, Store.get?, Array.set!_eq_setIfInBounds, hlt]

theorem get?_kill_other {store : Store} {loc other : Nat} {box otherBox}
    (hne : loc ≠ other) (hlive : store.get? loc = some box)
    (h : store.get? other = some otherBox) :
    (store.kill loc).get? other = some otherBox := by
  have hnodes := nodes_get?_of_get? hlive
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnodes
  simpa [Store.kill, Store.get?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, hlt, hne] using h

theorem get?_of_kill_other {store : Store} {loc other : Nat} {box otherBox}
    (hne : loc ≠ other) (hlive : store.get? loc = some box)
    (h : (store.kill loc).get? other = some otherBox) :
    store.get? other = some otherBox := by
  have hnodes := nodes_get?_of_get? hlive
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnodes
  simpa [Store.kill, Store.get?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, hlt, hne] using h

/-- Killing one live node leaves every surviving node's shape unchanged. -/
theorem StoreGraphRestricts.kill {store : Store} {loc : Nat} {box : NodeBox}
    (hlive : store.get? loc = some box) :
    StoreGraphRestricts store (store.kill loc) := by
  intro other world rc node hafter
  by_cases heq : loc = other
  · subst other
    rw [get?_kill_same hlive] at hafter
    contradiction
  · exact ⟨rc, get?_of_kill_other heq hlive hafter⟩

theorem count_edgeLocations_kill {store : Store} {loc : Nat}
    {box : NodeBox} (needle : Nat) (h : store.get? loc = some box) :
    List.count needle (edgeLocations (store.kill loc)) +
        List.count needle ((nodeChildren box.node).filterMap rvalLocation?) =
      List.count needle (edgeLocations store) := by
  have hnodes := nodes_get?_of_get? h
  have hlist : store.nodes.toList[loc]? = some (some box) := by
    simpa using hnodes
  rw [edgeLocations, edgeLocations, Store.kill, Array.toList_set!]
  apply count_flatMap_set_remove slotEdgeLocations needle hlist
  rfl

theorem incoming_kill_one (store : Store) (loc : Nat) (world : Owned)
    (node : Node) (rest : List Root) (needle : Nat)
    (hget : store.get? loc = some ⟨world, 1, node⟩) :
    incoming (store.kill loc) (rootsFor world (nodeChildren node) ++ rest)
          needle + (if loc == needle then 1 else 0) =
      incoming store (⟨world, .loc loc⟩ :: rest) needle := by
  have hedge := count_edgeLocations_kill needle hget
  by_cases heq : loc = needle
  · subst needle
    simp [incoming, List.filterMap_append, List.count_append,
      rootLocation?, rvalLocation?] at hedge ⊢
    omega
  · simp [incoming, List.filterMap_append, List.count_append,
      rootLocation?, rvalLocation?, heq] at hedge ⊢
    omega

theorem incoming_kill_shared_one (store : Store) (loc : Nat) (node : Node)
    (rest : List Root) (needle : Nat)
    (hget : store.get? loc = some ⟨.shared, 1, node⟩) :
    incoming (store.kill loc) (rootsFor .shared (nodeChildren node) ++ rest)
          needle + (if loc == needle then 1 else 0) =
      incoming store (⟨.shared, .loc loc⟩ :: rest) needle :=
  incoming_kill_one store loc .shared node rest needle hget

theorem incoming_kill_unique_one (store : Store) (loc : Nat) (node : Node)
    (rest : List Root) (needle : Nat)
    (hget : store.get? loc = some ⟨.unique, 1, node⟩) :
    incoming (store.kill loc) (rootsFor .unique (nodeChildren node) ++ rest)
          needle + (if loc == needle then 1 else 0) =
      incoming store (⟨.unique, .loc loc⟩ :: rest) needle :=
  incoming_kill_one store loc .unique node rest needle hget

private theorem sole_incoming_free_of_one {store : Store} {loc : Nat}
    {world : Owned} {rest : List Root}
    (hcount : 1 = incoming store (⟨world, .loc loc⟩ :: rest) loc) :
    loc ∉ rest.filterMap rootLocation? ++ edgeLocations store := by
  rw [incoming] at hcount
  simp [rootLocation?, rvalLocation?, List.count] at hcount
  intro hmem
  rcases List.mem_append.mp hmem with hroot | hedge
  · rw [List.mem_filterMap] at hroot
    obtain ⟨root, hroot, hmap⟩ := hroot
    exact hcount.1 loc root hroot hmap rfl
  · exact hcount.2 loc hedge rfl

/-- When a shared node has reference count one and its consuming root is
listed first, no root in the tail and no heap edge can also point to it. -/
theorem RootOwnership.sole_incoming_free {store : Store} {loc : Nat}
    {node : Node} {rest : List Root}
    (hget : store.get? loc = some ⟨.shared, 1, node⟩)
    (h : RootOwnership store (⟨.shared, .loc loc⟩ :: rest)) :
    loc ∉ rest.filterMap rootLocation? ++ edgeLocations store := by
  exact sole_incoming_free_of_one (h.counts hget)

/-- A unique node's exact-one incoming equation excludes every other root or
heap edge from its consuming root. -/
theorem RootOwnership.sole_incoming_free_unique {store : Store} {loc : Nat}
    {node : Node} {rest : List Root}
    (hget : store.get? loc = some ⟨.unique, 1, node⟩)
    (h : RootOwnership store (⟨.unique, .loc loc⟩ :: rest)) :
    loc ∉ rest.filterMap rootLocation? ++ edgeLocations store := by
  have hcount := h.counts hget
  exact sole_incoming_free_of_one hcount.2.symm

theorem RootOwnership.sole_root_ne {store : Store} {loc : Nat}
    {node : Node} {rest : List Root}
    (hget : store.get? loc = some ⟨.shared, 1, node⟩)
    (h : RootOwnership store (⟨.shared, .loc loc⟩ :: rest))
    {root : Root} (hroot : root ∈ rest) : root.value ≠ .loc loc := by
  intro heq
  have hfree := h.sole_incoming_free hget
  apply hfree
  apply List.mem_append_left
  rw [List.mem_filterMap]
  exact ⟨root, hroot, by simp [rootLocation?, heq, rvalLocation?]⟩

theorem child_location_mem_edgeLocations {store : Store} {parent : Nat}
    {box : NodeBox} {childLoc : Nat}
    (hparent : store.get? parent = some box)
    (hchild : RVal.loc childLoc ∈ nodeChildren box.node) :
    childLoc ∈ edgeLocations store := by
  have harray : some box ∈ store.nodes :=
    (Array.mem_iff_getElem?).2 ⟨parent, nodes_get?_of_get? hparent⟩
  have hslot : some box ∈ store.nodes.toList := by simpa using harray
  rw [edgeLocations, List.mem_flatMap]
  refine ⟨some box, hslot, ?_⟩
  change childLoc ∈ (nodeChildren box.node).filterMap rvalLocation?
  rw [List.mem_filterMap]
  exact ⟨.loc childLoc, hchild, rfl⟩

theorem RootOwnership.sole_child_ne {store : Store} {loc : Nat}
    {node : Node} {rest : List Root}
    (hget : store.get? loc = some ⟨.shared, 1, node⟩)
    (h : RootOwnership store (⟨.shared, .loc loc⟩ :: rest))
    {parent : Nat} {box : NodeBox} {child : RVal}
    (hparent : store.get? parent = some box)
    (hchild : child ∈ nodeChildren box.node) : child ≠ .loc loc := by
  intro heq
  subst child
  have hfree := h.sole_incoming_free hget
  apply hfree
  apply List.mem_append_right
  exact child_location_mem_edgeLocations hparent hchild

theorem RootOwnership.sole_root_ne_unique {store : Store} {loc : Nat}
    {node : Node} {rest : List Root}
    (hget : store.get? loc = some ⟨.unique, 1, node⟩)
    (h : RootOwnership store (⟨.unique, .loc loc⟩ :: rest))
    {root : Root} (hroot : root ∈ rest) : root.value ≠ .loc loc := by
  intro heq
  have hfree := h.sole_incoming_free_unique hget
  apply hfree
  apply List.mem_append_left
  rw [List.mem_filterMap]
  exact ⟨root, hroot, by simp [rootLocation?, heq, rvalLocation?]⟩

theorem RootOwnership.sole_child_ne_unique {store : Store} {loc : Nat}
    {node : Node} {rest : List Root}
    (hget : store.get? loc = some ⟨.unique, 1, node⟩)
    (h : RootOwnership store (⟨.unique, .loc loc⟩ :: rest))
    {parent : Nat} {box : NodeBox} {child : RVal}
    (hparent : store.get? parent = some box)
    (hchild : child ∈ nodeChildren box.node) : child ≠ .loc loc := by
  intro heq
  subst child
  have hfree := h.sole_incoming_free_unique hget
  apply hfree
  apply List.mem_append_right
  exact child_location_mem_edgeLocations hparent hchild

/-- Killing one live slot preserves the world of every value which does not
name that slot. -/
theorem HasWorld.kill {store : Store} {loc : Nat} {box : NodeBox}
    {world : Owned} {value : RVal}
    (hlive : store.get? loc = some box) (hne : value ≠ .loc loc)
    (h : HasWorld store world value) :
    HasWorld (store.kill loc) world value := by
  cases value with
  | loc valueLoc =>
    obtain ⟨valueBox, hvalue, hworld⟩ := h
    have hloc : loc ≠ valueLoc := by
      intro heq
      subst valueLoc
      exact hne rfl
    exact ⟨valueBox, get?_kill_other hloc hlive hvalue, hworld⟩
  | lit l => trivial
  | erased => trivial

/-- Ownership-facing form of in-place unique reuse. It kills and revives the
same slot, then restores the evaluator's counter behavior: one reuse and no
free. Its node array is extensionally the evaluator's direct overwrite. -/
def reuseNodeStore (store : Store) (loc : Nat) (node : Node) : Store :=
  let revived := (store.kill loc).setBox loc ⟨.unique, 1, node⟩
  { revived with frees := store.frees, reuses := store.reuses + 1 }

theorem reuseNodeStore_eq_direct (store : Store) (loc : Nat) (node : Node) :
    reuseNodeStore store loc node =
      let updated := store.setBox loc ⟨.unique, 1, node⟩
      { updated with reuses := updated.reuses + 1 } := by
  cases store
  simp [reuseNodeStore, Store.kill, Store.setBox,
    Array.set!_eq_setIfInBounds]

theorem get?_reuseNodeStore_same {store : Store} {loc : Nat}
    {oldBox : NodeBox} {node : Node}
    (hget : store.get? loc = some oldBox) :
    (reuseNodeStore store loc node).get? loc =
      some ⟨.unique, 1, node⟩ := by
  have hnodes := nodes_get?_of_get? hget
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnodes
  simp [reuseNodeStore, Store.kill, Store.setBox, Store.get?,
    Array.set!_eq_setIfInBounds, hlt]

theorem get?_reuseNodeStore_other {store : Store} {loc other : Nat}
    {oldBox otherBox : NodeBox} {node : Node} (hne : loc ≠ other)
    (hlive : store.get? loc = some oldBox)
    (hget : store.get? other = some otherBox) :
    (reuseNodeStore store loc node).get? other = some otherBox := by
  have hnodes := nodes_get?_of_get? hlive
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnodes
  simpa [reuseNodeStore, Store.kill, Store.setBox, Store.get?,
    Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hlt, hne]
    using hget

theorem get?_of_reuseNodeStore_other {store : Store} {loc other : Nat}
    {oldBox otherBox : NodeBox} {node : Node} (hne : loc ≠ other)
    (hlive : store.get? loc = some oldBox)
    (hget : (reuseNodeStore store loc node).get? other = some otherBox) :
    store.get? other = some otherBox := by
  have hnodes := nodes_get?_of_get? hlive
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnodes
  simpa [reuseNodeStore, Store.kill, Store.setBox, Store.get?,
    Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hlt, hne]
    using hget

theorem count_edgeLocations_reuseNodeStore {store : Store} {loc : Nat}
    {oldBox : NodeBox} {node : Node} (needle : Nat)
    (hget : store.get? loc = some oldBox) :
    List.count needle (edgeLocations (reuseNodeStore store loc node)) =
      List.count needle (edgeLocations (store.kill loc)) +
        List.count needle ((nodeChildren node).filterMap rvalLocation?) := by
  have hnodes := nodes_get?_of_get? hget
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnodes
  have hslot : (store.kill loc).nodes.toList[loc]? = some none := by
    simp [Store.kill, Array.set!_eq_setIfInBounds, hlt]
  rw [edgeLocations, edgeLocations, reuseNodeStore, Store.setBox,
    Array.toList_set!]
  apply count_flatMap_set_add slotEdgeLocations needle hslot
  rfl

theorem incoming_reuseNodeStore_same (store : Store) (loc : Nat)
    (oldBox : NodeBox) (node : Node) (rest : List Root)
    (hget : store.get? loc = some oldBox) :
    incoming (reuseNodeStore store loc node)
        (⟨.unique, .loc loc⟩ :: rest) loc =
      incoming (store.kill loc)
        (rootsFor .unique (nodeChildren node) ++ rest) loc + 1 := by
  have hedge :=
    count_edgeLocations_reuseNodeStore (node := node) loc hget
  simp [incoming, List.filterMap_append,
    rootLocation?, rvalLocation?, List.count] at hedge ⊢
  omega

theorem incoming_reuseNodeStore_other (store : Store) (loc : Nat)
    (oldBox : NodeBox) (node : Node) (rest : List Root) {other : Nat}
    (hne : loc ≠ other) (hget : store.get? loc = some oldBox) :
    incoming (reuseNodeStore store loc node)
        (⟨.unique, .loc loc⟩ :: rest) other =
      incoming (store.kill loc)
        (rootsFor .unique (nodeChildren node) ++ rest) other := by
  have hedge :=
    count_edgeLocations_reuseNodeStore (node := node) other hget
  simp [incoming, List.filterMap_append, List.count_append,
    rootLocation?, rvalLocation?, hne] at hedge ⊢
  omega

theorem HasWorld.reuseNodeStore {store : Store} {loc : Nat}
    {oldBox : NodeBox} {node : Node} {world : Owned} {value : RVal}
    (hget : store.get? loc = some oldBox)
    (h : HasWorld (store.kill loc) world value) :
    HasWorld (reuseNodeStore store loc node) world value := by
  cases value with
  | loc valueLoc =>
    obtain ⟨valueBox, hvalue, hworld⟩ := h
    have hne : loc ≠ valueLoc := by
      intro heq
      subst valueLoc
      rw [get?_kill_same hget] at hvalue
      contradiction
    have hold : store.get? valueLoc = some valueBox :=
      get?_of_kill_other hne hget hvalue
    exact ⟨valueBox, get?_reuseNodeStore_other hne hget hold, hworld⟩
  | lit literal => trivial
  | erased => trivial

/-- Ownership-facing form of in-place shared reuse.  As for unique reuse,
the slot is killed and revived to expose the ownership transition while the
observable allocator counters are restored to the evaluator's direct
overwrite behavior: one reuse and no free. -/
def reuseSharedNodeStore (store : Store) (loc : Nat) (node : Node) : Store :=
  let revived := (store.kill loc).setBox loc ⟨.shared, 1, node⟩
  { revived with frees := store.frees, reuses := store.reuses + 1 }

theorem reuseSharedNodeStore_eq_direct (store : Store) (loc : Nat)
    (node : Node) :
    reuseSharedNodeStore store loc node =
      let updated := store.setBox loc ⟨.shared, 1, node⟩
      { updated with reuses := updated.reuses + 1 } := by
  cases store
  simp [reuseSharedNodeStore, Store.kill, Store.setBox,
    Array.set!_eq_setIfInBounds]

theorem get?_reuseSharedNodeStore_same {store : Store} {loc : Nat}
    {oldBox : NodeBox} {node : Node}
    (hget : store.get? loc = some oldBox) :
    (reuseSharedNodeStore store loc node).get? loc =
      some ⟨.shared, 1, node⟩ := by
  have hnodes := nodes_get?_of_get? hget
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnodes
  simp [reuseSharedNodeStore, Store.kill, Store.setBox, Store.get?,
    Array.set!_eq_setIfInBounds, hlt]

theorem get?_reuseSharedNodeStore_other {store : Store} {loc other : Nat}
    {oldBox otherBox : NodeBox} {node : Node} (hne : loc ≠ other)
    (hlive : store.get? loc = some oldBox)
    (hget : store.get? other = some otherBox) :
    (reuseSharedNodeStore store loc node).get? other = some otherBox := by
  have hnodes := nodes_get?_of_get? hlive
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnodes
  simpa [reuseSharedNodeStore, Store.kill, Store.setBox, Store.get?,
    Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hlt, hne]
    using hget

theorem get?_of_reuseSharedNodeStore_other {store : Store}
    {loc other : Nat} {oldBox otherBox : NodeBox} {node : Node}
    (hne : loc ≠ other) (hlive : store.get? loc = some oldBox)
    (hget : (reuseSharedNodeStore store loc node).get? other =
      some otherBox) :
    store.get? other = some otherBox := by
  have hnodes := nodes_get?_of_get? hlive
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnodes
  simpa [reuseSharedNodeStore, Store.kill, Store.setBox, Store.get?,
    Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hlt, hne]
    using hget

theorem count_edgeLocations_reuseSharedNodeStore {store : Store}
    {loc : Nat} {oldBox : NodeBox} {node : Node} (needle : Nat)
    (hget : store.get? loc = some oldBox) :
    List.count needle (edgeLocations (reuseSharedNodeStore store loc node)) =
      List.count needle (edgeLocations (store.kill loc)) +
        List.count needle ((nodeChildren node).filterMap rvalLocation?) := by
  have hnodes := nodes_get?_of_get? hget
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnodes
  have hslot : (store.kill loc).nodes.toList[loc]? = some none := by
    simp [Store.kill, Array.set!_eq_setIfInBounds, hlt]
  rw [edgeLocations, edgeLocations, reuseSharedNodeStore, Store.setBox,
    Array.toList_set!]
  apply count_flatMap_set_add slotEdgeLocations needle hslot
  rfl

theorem incoming_reuseSharedNodeStore_same (store : Store) (loc : Nat)
    (oldBox : NodeBox) (node : Node) (rest : List Root)
    (hget : store.get? loc = some oldBox) :
    incoming (reuseSharedNodeStore store loc node)
        (⟨.shared, .loc loc⟩ :: rest) loc =
      incoming (store.kill loc)
        (rootsFor .shared (nodeChildren node) ++ rest) loc + 1 := by
  have hedge :=
    count_edgeLocations_reuseSharedNodeStore (node := node) loc hget
  simp [incoming, List.filterMap_append,
    rootLocation?, rvalLocation?, List.count] at hedge ⊢
  omega

theorem incoming_reuseSharedNodeStore_other (store : Store) (loc : Nat)
    (oldBox : NodeBox) (node : Node) (rest : List Root) {other : Nat}
    (hne : loc ≠ other) (hget : store.get? loc = some oldBox) :
    incoming (reuseSharedNodeStore store loc node)
        (⟨.shared, .loc loc⟩ :: rest) other =
      incoming (store.kill loc)
        (rootsFor .shared (nodeChildren node) ++ rest) other := by
  have hedge :=
    count_edgeLocations_reuseSharedNodeStore (node := node) other hget
  simp [incoming, List.filterMap_append, List.count_append,
    rootLocation?, rvalLocation?, hne] at hedge ⊢
  omega

theorem HasWorld.reuseSharedNodeStore {store : Store} {loc : Nat}
    {oldBox : NodeBox} {node : Node} {world : Owned} {value : RVal}
    (hget : store.get? loc = some oldBox)
    (h : HasWorld (store.kill loc) world value) :
    HasWorld (reuseSharedNodeStore store loc node) world value := by
  cases value with
  | loc valueLoc =>
    obtain ⟨valueBox, hvalue, hworld⟩ := h
    have hne : loc ≠ valueLoc := by
      intro heq
      subst valueLoc
      rw [get?_kill_same hget] at hvalue
      contradiction
    have hold : store.get? valueLoc = some valueBox :=
      get?_of_kill_other hne hget hvalue
    exact ⟨valueBox, get?_reuseSharedNodeStore_other hne hget hold,
      hworld⟩
  | lit literal => trivial
  | erased => trivial

/-- Store transition performed by a successful `dup` on a shared location. -/
def incRcStore (store : Store) (loc : Nat) (box : NodeBox) : Store :=
  (store.setBox loc { box with rc := box.rc + 1 }).rcTick

@[simp] theorem get?_rcTick (store : Store) (loc : Nat) :
    store.rcTick.get? loc = store.get? loc := rfl

/-- Reference-count instrumentation changes no ownership-relevant store
state. -/
theorem RootOwnership.rcTick {store : Store} {roots : List Root}
    (h : RootOwnership store roots) : RootOwnership store.rcTick roots := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro root hroot
    simpa [HasWorld, Store.rcTick, Store.get?] using
      h.roots_world root hroot
  · intro loc box hbox child hchild
    have hold : store.get? loc = some box := by simpa using hbox
    simpa [HasWorld, Store.rcTick, Store.get?] using
      h.edges_world hold child hchild
  · intro loc box f arity args hbox hnode
    apply h.pap_shared (loc := loc) (box := box) (f := f)
      (arity := arity) (args := args)
    · simpa using hbox
    · exact hnode
  · intro loc box hbox
    have hold : store.get? loc = some box := by simpa using hbox
    simpa [incoming, edgeLocations, Store.rcTick] using h.counts hold

/-- Inverse allocation for the final shared owner: remove the node and turn
each outgoing field/capture edge into a temporary root for recursive drop. -/
theorem RootOwnership.killSharedOne {store : Store} {loc : Nat}
    {node : Node} {rest : List Root}
    (hget : store.get? loc = some ⟨.shared, 1, node⟩)
    (h : RootOwnership store (⟨.shared, .loc loc⟩ :: rest)) :
    RootOwnership (store.kill loc)
      (rootsFor .shared (nodeChildren node) ++ rest) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro root hroot
    rcases List.mem_append.mp hroot with hchildRoot | hrest
    · rw [rootsFor, List.mem_map] at hchildRoot
      obtain ⟨child, hchild, rfl⟩ := hchildRoot
      apply HasWorld.kill hget (h.sole_child_ne hget hget hchild)
      exact h.edges_world hget child hchild
    · apply HasWorld.kill hget (h.sole_root_ne hget hrest)
      apply h.roots_world root
      exact List.mem_cons_of_mem _ hrest
  · intro parent parentBox hparent child hchild
    have hne : loc ≠ parent := by
      intro heq
      subst parent
      rw [get?_kill_same hget] at hparent
      contradiction
    have hold : store.get? parent = some parentBox :=
      get?_of_kill_other hne hget hparent
    apply HasWorld.kill hget (h.sole_child_ne hget hold hchild)
    exact h.edges_world hold child hchild
  · intro parent parentBox f arity args hparent hnode
    have hne : loc ≠ parent := by
      intro heq
      subst parent
      rw [get?_kill_same hget] at hparent
      contradiction
    have hold : store.get? parent = some parentBox :=
      get?_of_kill_other hne hget hparent
    exact h.pap_shared hold hnode
  · intro parent parentBox hparent
    have hne : loc ≠ parent := by
      intro heq
      subst parent
      rw [get?_kill_same hget] at hparent
      contradiction
    have hold : store.get? parent = some parentBox :=
      get?_of_kill_other hne hget hparent
    have hincoming :=
      incoming_kill_shared_one store loc node rest parent hget
    have hincoming' :
        incoming (store.kill loc)
            (rootsFor .shared (nodeChildren node) ++ rest) parent =
          incoming store (⟨.shared, .loc loc⟩ :: rest) parent := by
      simpa [hne] using hincoming
    rw [hincoming']
    exact h.counts hold

/-- Inverse allocation for a unique node: remove its sole-owned slot and turn
each outgoing field edge into a temporary unique root for recursive `dropU`. -/
theorem RootOwnership.killUniqueOne {store : Store} {loc : Nat}
    {node : Node} {rest : List Root}
    (hget : store.get? loc = some ⟨.unique, 1, node⟩)
    (h : RootOwnership store (⟨.unique, .loc loc⟩ :: rest)) :
    RootOwnership (store.kill loc)
      (rootsFor .unique (nodeChildren node) ++ rest) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro root hroot
    rcases List.mem_append.mp hroot with hchildRoot | hrest
    · rw [rootsFor, List.mem_map] at hchildRoot
      obtain ⟨child, hchild, rfl⟩ := hchildRoot
      apply HasWorld.kill hget
        (h.sole_child_ne_unique hget hget hchild)
      exact h.edges_world hget child hchild
    · apply HasWorld.kill hget (h.sole_root_ne_unique hget hrest)
      apply h.roots_world root
      exact List.mem_cons_of_mem _ hrest
  · intro parent parentBox hparent child hchild
    have hne : loc ≠ parent := by
      intro heq
      subst parent
      rw [get?_kill_same hget] at hparent
      contradiction
    have hold : store.get? parent = some parentBox :=
      get?_of_kill_other hne hget hparent
    apply HasWorld.kill hget
      (h.sole_child_ne_unique hget hold hchild)
    exact h.edges_world hold child hchild
  · intro parent parentBox f arity args hparent hnode
    have hne : loc ≠ parent := by
      intro heq
      subst parent
      rw [get?_kill_same hget] at hparent
      contradiction
    have hold : store.get? parent = some parentBox :=
      get?_of_kill_other hne hget hparent
    exact h.pap_shared hold hnode
  · intro parent parentBox hparent
    have hne : loc ≠ parent := by
      intro heq
      subst parent
      rw [get?_kill_same hget] at hparent
      contradiction
    have hold : store.get? parent = some parentBox :=
      get?_of_kill_other hne hget hparent
    have hincoming :=
      incoming_kill_unique_one store loc node rest parent hget
    have hincoming' :
        incoming (store.kill loc)
            (rootsFor .unique (nodeChildren node) ++ rest) parent =
          incoming store (⟨.unique, .loc loc⟩ :: rest) parent := by
      simpa [hne] using hincoming
    rw [hincoming']
    exact h.counts hold

/-- Constructor nodes may inhabit either world; pap nodes are always shared. -/
def NodeWorld (world : Owned) : Node → Prop
  | .ctorN _ _ => True
  | .papN _ _ _ => world = .shared

/-- Fill the just-killed slot with a unique node. This is allocation into a
known dead in-bounds slot: child roots become edges and a fresh root for the
revived location is produced. -/
theorem RootOwnership.reviveUnique {store : Store} {loc : Nat}
    {oldBox : NodeBox} {node : Node} {rest : List Root}
    (hget : store.get? loc = some oldBox)
    (h : RootOwnership (store.kill loc)
      (rootsFor .unique (nodeChildren node) ++ rest))
    (hworld : NodeWorld .unique node) :
    RootOwnership (reuseNodeStore store loc node)
      (⟨.unique, .loc loc⟩ :: rest) := by
  let updated : NodeBox := ⟨.unique, 1, node⟩
  have hupdated : (reuseNodeStore store loc node).get? loc =
      some updated := get?_reuseNodeStore_same hget
  have targetWorld :
      HasWorld (reuseNodeStore store loc node) .unique (.loc loc) :=
    ⟨updated, hupdated, rfl⟩
  have childWorld : ∀ child ∈ nodeChildren node,
      HasWorld (store.kill loc) .unique child := by
    intro child hchild
    apply h.roots_world ⟨.unique, child⟩
    apply List.mem_append_left rest
    simp [rootsFor, hchild]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro root hroot
    simp only [List.mem_cons] at hroot
    rcases hroot with rfl | hrest
    · exact targetWorld
    · apply HasWorld.reuseNodeStore hget
      apply h.roots_world root
      exact List.mem_append_right _ hrest
  · intro parent parentBox hparent child hchild
    by_cases heq : loc = parent
    · subst parent
      have hboxeq : parentBox = updated := by
        exact Option.some.inj (hparent.symm.trans hupdated)
      subst parentBox
      exact HasWorld.reuseNodeStore hget (childWorld child hchild)
    · have hold : store.get? parent = some parentBox :=
        get?_of_reuseNodeStore_other heq hget hparent
      have hkilled : (store.kill loc).get? parent = some parentBox :=
        get?_kill_other heq hget hold
      exact HasWorld.reuseNodeStore hget
        (h.edges_world hkilled child hchild)
  · intro parent parentBox f arity args hparent hnode
    by_cases heq : loc = parent
    · subst parent
      have hboxeq : parentBox = updated := by
        exact Option.some.inj (hparent.symm.trans hupdated)
      subst parentBox
      change node = .papN f arity args at hnode
      cases node <;> simp_all [NodeWorld]
    · have hold : store.get? parent = some parentBox :=
        get?_of_reuseNodeStore_other heq hget hparent
      have hkilled : (store.kill loc).get? parent = some parentBox :=
        get?_kill_other heq hget hold
      exact h.pap_shared hkilled hnode
  · intro parent parentBox hparent
    by_cases heq : loc = parent
    · subst parent
      have hboxeq : parentBox = updated := by
        exact Option.some.inj (hparent.symm.trans hupdated)
      subst parentBox
      have hzero := h.incoming_eq_zero_of_dead (get?_kill_same hget)
      have hcount :=
        incoming_reuseNodeStore_same store loc oldBox node rest hget
      rw [hzero] at hcount
      exact ⟨rfl, hcount⟩
    · have hold : store.get? parent = some parentBox :=
        get?_of_reuseNodeStore_other heq hget hparent
      have hkilled : (store.kill loc).get? parent = some parentBox :=
        get?_kill_other heq hget hold
      have hcount := h.counts hkilled
      rw [incoming_reuseNodeStore_other store loc oldBox node rest heq hget]
      exact hcount

/-- In-place unique reuse consumes the old node root and the selected new
field roots, then produces the same location as a root. `hpartition` is the
ownership-level free/allocate pairing: the old fields plus ambient roots are
the new fields plus the roots that remain outside the node, **as
multisets** (`List.Perm`). Permutation rather than list equality is what
same-arity field replacement produces — reusing `Cons(x, xs)` as
`Cons(x, acc)` moves `acc` out of the ambient roots and `xs` into them,
with no split making the two sides equal as lists. -/
theorem RootOwnership.reuseNode {store : Store} {loc : Nat}
    {oldNode newNode : Node} {before after : List Root}
    (hget : store.get? loc = some ⟨.unique, 1, oldNode⟩)
    (h : RootOwnership store (⟨.unique, .loc loc⟩ :: before))
    (hpartition :
      (rootsFor .unique (nodeChildren oldNode) ++ before).Perm
        (rootsFor .unique (nodeChildren newNode) ++ after))
    (hworld : NodeWorld .unique newNode) :
    RootOwnership (reuseNodeStore store loc newNode)
      (⟨.unique, .loc loc⟩ :: after) := by
  have hready := (h.killUniqueOne hget).perm hpartition
  exact hready.reviveUnique hget hworld

/-- Fill a just-killed slot with a shared node.  The proof is the shared
counterpart of `reviveUnique`: the replacement root has refcount one, and
the children supplied as temporary roots become the replacement's outgoing
shared edges. -/
theorem RootOwnership.reviveShared {store : Store} {loc : Nat}
    {oldBox : NodeBox} {node : Node} {rest : List Root}
    (hget : store.get? loc = some oldBox)
    (h : RootOwnership (store.kill loc)
      (rootsFor .shared (nodeChildren node) ++ rest))
    (_hworld : NodeWorld .shared node) :
    RootOwnership (reuseSharedNodeStore store loc node)
      (⟨.shared, .loc loc⟩ :: rest) := by
  let updated : NodeBox := ⟨.shared, 1, node⟩
  have hupdated : (reuseSharedNodeStore store loc node).get? loc =
      some updated := get?_reuseSharedNodeStore_same hget
  have targetWorld :
      HasWorld (reuseSharedNodeStore store loc node) .shared (.loc loc) :=
    ⟨updated, hupdated, rfl⟩
  have childWorld : ∀ child ∈ nodeChildren node,
      HasWorld (store.kill loc) .shared child := by
    intro child hchild
    apply h.roots_world ⟨.shared, child⟩
    apply List.mem_append_left rest
    simp [rootsFor, hchild]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro root hroot
    simp only [List.mem_cons] at hroot
    rcases hroot with rfl | hrest
    · exact targetWorld
    · apply HasWorld.reuseSharedNodeStore hget
      apply h.roots_world root
      exact List.mem_append_right _ hrest
  · intro parent parentBox hparent child hchild
    by_cases heq : loc = parent
    · subst parent
      have hboxeq : parentBox = updated := by
        exact Option.some.inj (hparent.symm.trans hupdated)
      subst parentBox
      exact HasWorld.reuseSharedNodeStore hget (childWorld child hchild)
    · have hold : store.get? parent = some parentBox :=
        get?_of_reuseSharedNodeStore_other heq hget hparent
      have hkilled : (store.kill loc).get? parent = some parentBox :=
        get?_kill_other heq hget hold
      exact HasWorld.reuseSharedNodeStore hget
        (h.edges_world hkilled child hchild)
  · intro parent parentBox f arity args hparent hnode
    by_cases heq : loc = parent
    · subst parent
      have hboxeq : parentBox = updated := by
        exact Option.some.inj (hparent.symm.trans hupdated)
      subst parentBox
      rfl
    · have hold : store.get? parent = some parentBox :=
        get?_of_reuseSharedNodeStore_other heq hget hparent
      have hkilled : (store.kill loc).get? parent = some parentBox :=
        get?_kill_other heq hget hold
      exact h.pap_shared hkilled hnode
  · intro parent parentBox hparent
    by_cases heq : loc = parent
    · subst parent
      have hboxeq : parentBox = updated := by
        exact Option.some.inj (hparent.symm.trans hupdated)
      subst parentBox
      have hzero := h.incoming_eq_zero_of_dead (get?_kill_same hget)
      have hcount :=
        incoming_reuseSharedNodeStore_same store loc oldBox node rest hget
      rw [hzero] at hcount
      exact hcount.symm
    · have hold : store.get? parent = some parentBox :=
        get?_of_reuseSharedNodeStore_other heq hget hparent
      have hkilled : (store.kill loc).get? parent = some parentBox :=
        get?_kill_other heq hget hold
      have hcount := h.counts hkilled
      rw [incoming_reuseSharedNodeStore_other store loc oldBox node rest
        heq hget]
      exact hcount

/-- In-place shared reuse consumes the unit-refcount parent root and the
selected replacement-field roots, then produces the reused location as a
shared root.  As in unique reuse, the field/ambient accounting is stated as
a root-multiset permutation. -/
theorem RootOwnership.reuseSharedNode {store : Store} {loc : Nat}
    {oldNode newNode : Node} {before after : List Root}
    (hget : store.get? loc = some ⟨.shared, 1, oldNode⟩)
    (h : RootOwnership store (⟨.shared, .loc loc⟩ :: before))
    (hpartition :
      (rootsFor .shared (nodeChildren oldNode) ++ before).Perm
        (rootsFor .shared (nodeChildren newNode) ++ after))
    (hworld : NodeWorld .shared newNode) :
    RootOwnership (reuseSharedNodeStore store loc newNode)
      (⟨.shared, .loc loc⟩ :: after) := by
  have hready := (h.killSharedOne hget).perm hpartition
  exact hready.reviveShared hget hworld

/-- Consuming a scalar root changes no heap ownership. -/
theorem RootOwnership.dropNoLocation {store : Store} {world : Owned}
    {value : RVal} {rest : List Root}
    (hnone : rvalLocation? value = none)
    (h : RootOwnership store (⟨world, value⟩ :: rest)) :
    RootOwnership store rest := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro root hroot
    exact h.roots_world root (List.mem_cons_of_mem _ hroot)
  · exact h.edges_world
  · exact h.pap_shared
  · intro loc box hbox
    simpa [incoming, rootLocation?, hnone] using h.counts hbox

/-- Scalars may be added as roots without changing heap ownership. -/
theorem RootOwnership.addNoLocation {store : Store} {world : Owned}
    {value : RVal} {rest : List Root}
    (hnone : rvalLocation? value = none)
    (h : RootOwnership store rest) :
    RootOwnership store (⟨world, value⟩ :: rest) := by
  have hscalar : HasWorld store world value := by
    cases value <;> simp_all [rvalLocation?, HasWorld]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro root hroot
    simp only [List.mem_cons] at hroot
    rcases hroot with rfl | hrest
    · exact hscalar
    · exact h.roots_world root hrest
  · exact h.edges_world
  · exact h.pap_shared
  · intro loc box hbox
    simpa [incoming, rootLocation?, hnone] using h.counts hbox

theorem RVal.rvalLocation?_eq_none_of_isScalar {value : RVal}
    (hscalar : value.isScalar = true) : rvalLocation? value = none := by
  cases value <;> simp_all [RVal.isScalar, rvalLocation?]

/-- A scalar-only argument vector contributes no heap owners, so consuming
all of its logical roots leaves the ambient ownership state unchanged. -/
theorem RootOwnership.dropScalars {store : Store} {world : Owned}
    {rest : List Root} :
    ∀ {values : List RVal}, values.all RVal.isScalar = true →
      RootOwnership store (rootsFor world values ++ rest) →
      RootOwnership store rest := by
  intro values hscalar hown
  induction values with
  | nil => simpa [rootsFor] using hown
  | cons value values ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hscalar
    have hcons : RootOwnership store
        (⟨world, value⟩ :: (rootsFor world values ++ rest)) := by
      simpa [rootsFor] using hown
    exact ih hscalar.2
      (hcons.dropNoLocation
        (RVal.rvalLocation?_eq_none_of_isScalar hscalar.1))

/-- Successful use of the v1 extern boundary certifies both sides of the
call as scalar-only. -/
theorem callScalarOracle_ok {ctx : Ctx} {f : Address}
    {args : List RVal} {value : RVal}
    (hcall : callScalarOracle ctx f args = .ok value) :
    args.all RVal.isScalar = true ∧ value.isScalar = true := by
  cases hargs : args.all RVal.isScalar with
  | false => simp [callScalarOracle, hargs] at hcall
  | true =>
    cases horacle : ctx.oracle f args with
    | none => simp [callScalarOracle, hargs, horacle] at hcall
    | some result =>
      cases hresult : result.isScalar with
      | false => simp [callScalarOracle, hargs, horacle, hresult] at hcall
      | true =>
        simp [callScalarOracle, hargs, horacle, hresult] at hcall
        subst value
        exact ⟨rfl, hresult⟩

theorem RootOwnership.shared_rc_pos {store : Store} {loc rc : Nat}
    {node : Node} {rest : List Root}
    (hget : store.get? loc = some ⟨.shared, rc, node⟩)
    (h : RootOwnership store (⟨.shared, .loc loc⟩ :: rest)) : 0 < rc := by
  have hcount := h.counts hget
  change rc = incoming store (⟨.shared, .loc loc⟩ :: rest) loc at hcount
  rw [hcount, incoming]
  simp [rootLocation?, rvalLocation?, List.count]

theorem get?_incRcStore_same {store : Store} {loc : Nat} {box : NodeBox}
    (h : store.get? loc = some box) :
    (incRcStore store loc box).get? loc =
      some { box with rc := box.rc + 1 } := by
  rw [incRcStore, get?_rcTick]
  exact get?_setBox_same (new := { box with rc := box.rc + 1 }) h

theorem get?_incRcStore_other {store : Store} {loc other : Nat}
    {box otherBox : NodeBox} (hne : loc ≠ other)
    (hlive : store.get? loc = some box)
    (h : store.get? other = some otherBox) :
    (incRcStore store loc box).get? other = some otherBox := by
  rw [incRcStore, get?_rcTick]
  exact get?_setBox_other (new := { box with rc := box.rc + 1 })
    hne hlive h

theorem get?_of_incRcStore_other {store : Store} {loc other : Nat}
    {box otherBox : NodeBox} (hne : loc ≠ other)
    (hlive : store.get? loc = some box)
    (h : (incRcStore store loc box).get? other = some otherBox) :
    store.get? other = some otherBox := by
  apply get?_of_setBox_other (new := { box with rc := box.rc + 1 })
    hne hlive
  rw [incRcStore, get?_rcTick] at h
  exact h

/-- Incrementing one shared refcount preserves every live node's semantic
shape; only the selected node's count changes. -/
theorem StoreGraphExtends.incRcStore {store : Store} {loc rc : Nat}
    {node : Node}
    (hget : store.get? loc = some ⟨.shared, rc, node⟩) :
    StoreGraphExtends store
      (incRcStore store loc ⟨.shared, rc, node⟩) := by
  intro other world otherRc otherNode hother
  by_cases heq : loc = other
  · subst other
    have hbox : (⟨world, otherRc, otherNode⟩ : NodeBox) =
        ⟨.shared, rc, node⟩ :=
      Option.some.inj (hother.symm.trans hget)
    cases hbox
    exact ⟨rc + 1, get?_incRcStore_same hget⟩
  · exact ⟨otherRc, get?_incRcStore_other heq hget hother⟩

/-- Incrementing one shared refcount also preserves every resulting live
node's prior semantic shape.  This is the reverse inclusion counterpart of
`StoreGraphExtends.incRcStore`. -/
theorem StoreGraphRestricts.incRcStore {store : Store} {loc rc : Nat}
    {node : Node}
    (hget : store.get? loc = some ⟨.shared, rc, node⟩) :
    StoreGraphRestricts store
      (incRcStore store loc ⟨.shared, rc, node⟩) := by
  intro other world otherRc otherNode hother
  by_cases heq : loc = other
  · subst other
    have hupdated := get?_incRcStore_same hget
    have hbox : (⟨world, otherRc, otherNode⟩ : NodeBox) =
        ⟨.shared, rc + 1, node⟩ :=
      Option.some.inj (hother.symm.trans hupdated)
    cases hbox
    exact ⟨rc, hget⟩
  · exact ⟨otherRc, get?_of_incRcStore_other heq hget hother⟩

theorem edgeLocations_incRcStore {store : Store} {loc : Nat} {box : NodeBox}
    (h : store.get? loc = some box) :
    edgeLocations (incRcStore store loc box) = edgeLocations store := by
  have hnodes := nodes_get?_of_get? h
  have hlist : store.nodes.toList[loc]? = some (some box) := by
    simpa using hnodes
  rw [edgeLocations, incRcStore, Store.rcTick, Store.setBox,
    Array.toList_set!]
  apply flatMap_set_eq_self slotEdgeLocations hlist
  rfl

theorem incoming_incRcStore_same (store : Store) (loc rc : Nat)
    (node : Node) (rest : List Root)
    (hget : store.get? loc = some ⟨.shared, rc, node⟩) :
    incoming (incRcStore store loc ⟨.shared, rc, node⟩)
        (⟨.shared, .loc loc⟩ :: ⟨.shared, .loc loc⟩ :: rest) loc =
      incoming store (⟨.shared, .loc loc⟩ :: rest) loc + 1 := by
  rw [incoming, incoming, edgeLocations_incRcStore hget]
  simp [rootLocation?, rvalLocation?, List.count_append]

theorem incoming_incRcStore_other (store : Store) (loc rc : Nat)
    (node : Node) (rest : List Root) {other : Nat} (hne : loc ≠ other)
    (hget : store.get? loc = some ⟨.shared, rc, node⟩) :
    incoming (incRcStore store loc ⟨.shared, rc, node⟩)
        (⟨.shared, .loc loc⟩ :: ⟨.shared, .loc loc⟩ :: rest) other =
      incoming store (⟨.shared, .loc loc⟩ :: rest) other := by
  rw [incoming, incoming, edgeLocations_incRcStore hget]
  simp [rootLocation?, rvalLocation?, List.count_append, hne]

theorem incoming_incRcStore_retain_same (store : Store) (loc rc : Nat)
    (node : Node) (rest : List Root)
    (hget : store.get? loc = some ⟨.shared, rc, node⟩) :
    incoming (incRcStore store loc ⟨.shared, rc, node⟩)
        (⟨.shared, .loc loc⟩ :: rest) loc =
      incoming store rest loc + 1 := by
  rw [incoming, incoming, edgeLocations_incRcStore hget]
  simp [rootLocation?, rvalLocation?, List.count_append, Nat.add_comm]

theorem incoming_incRcStore_retain_other (store : Store) (loc rc : Nat)
    (node : Node) (rest : List Root) {other : Nat} (hne : loc ≠ other)
    (hget : store.get? loc = some ⟨.shared, rc, node⟩) :
    incoming (incRcStore store loc ⟨.shared, rc, node⟩)
        (⟨.shared, .loc loc⟩ :: rest) other =
      incoming store rest other := by
  rw [incoming, incoming, edgeLocations_incRcStore hget]
  simp [rootLocation?, rvalLocation?, List.count_append, hne]

theorem HasWorld.incRcStore {store : Store} {loc rc : Nat} {node : Node}
    {world : Owned} {value : RVal}
    (hget : store.get? loc = some ⟨.shared, rc, node⟩)
    (h : HasWorld store world value) :
    HasWorld (incRcStore store loc ⟨.shared, rc, node⟩) world value := by
  cases value with
  | loc valueLoc =>
    obtain ⟨box, hbox, hworld⟩ := h
    by_cases heq : loc = valueLoc
    · subst valueLoc
      have hboxeq : box = ⟨.shared, rc, node⟩ := by
        exact Option.some.inj (hbox.symm.trans hget)
      subst box
      exact ⟨⟨.shared, rc + 1, node⟩,
        get?_incRcStore_same hget, hworld⟩
    · exact ⟨box, get?_incRcStore_other heq hget hbox, hworld⟩
  | lit l => trivial
  | erased => trivial

/-- A successful shared `dup` retains the old root, returns a second root,
and increments exactly the corresponding reference count. -/
theorem RootOwnership.dup {store : Store} {loc rc : Nat} {node : Node}
    {rest : List Root}
    (hget : store.get? loc = some ⟨.shared, rc, node⟩)
    (h : RootOwnership store (⟨.shared, .loc loc⟩ :: rest)) :
    RootOwnership (incRcStore store loc ⟨.shared, rc, node⟩)
      (⟨.shared, .loc loc⟩ :: ⟨.shared, .loc loc⟩ :: rest) := by
  let updated : NodeBox := ⟨.shared, rc + 1, node⟩
  have hupdated :
      (incRcStore store loc ⟨.shared, rc, node⟩).get? loc =
        some updated := by
    exact get?_incRcStore_same hget
  have targetWorld :
      HasWorld (incRcStore store loc ⟨.shared, rc, node⟩)
        .shared (.loc loc) := ⟨updated, hupdated, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro root hroot
    simp only [List.mem_cons] at hroot
    rcases hroot with rfl | rfl | hrest
    · exact targetWorld
    · exact targetWorld
    · apply HasWorld.incRcStore hget
      apply h.roots_world root
      exact .tail _ hrest
  · intro parent parentBox hparent child hchild
    by_cases heq : loc = parent
    · subst parent
      have hboxeq : parentBox = updated := by
        exact Option.some.inj (hparent.symm.trans hupdated)
      subst parentBox
      apply HasWorld.incRcStore hget
      exact h.edges_world hget child hchild
    · have hold : store.get? parent = some parentBox :=
        get?_of_incRcStore_other heq hget hparent
      exact HasWorld.incRcStore hget (h.edges_world hold child hchild)
  · intro parent parentBox f arity args hparent hnode
    by_cases heq : loc = parent
    · subst parent
      have hboxeq : parentBox = updated := by
        exact Option.some.inj (hparent.symm.trans hupdated)
      subst parentBox
      change node = .papN f arity args at hnode
      exact h.pap_shared (loc := loc)
        (box := (⟨.shared, rc, node⟩ : NodeBox)) hget hnode
    · have hold : store.get? parent = some parentBox :=
        get?_of_incRcStore_other heq hget hparent
      exact h.pap_shared hold hnode
  · intro parent parentBox hparent
    by_cases heq : loc = parent
    · subst parent
      have hboxeq : parentBox = updated := by
        exact Option.some.inj (hparent.symm.trans hupdated)
      subst parentBox
      have hcount := h.counts hget
      change rc = incoming store (⟨.shared, .loc loc⟩ :: rest) loc
        at hcount
      change rc + 1 = incoming
        (incRcStore store loc ⟨.shared, rc, node⟩)
          (⟨.shared, .loc loc⟩ :: ⟨.shared, .loc loc⟩ :: rest) loc
      rw [incoming_incRcStore_same store loc rc node rest hget, hcount]
    · have hold : store.get? parent = some parentBox :=
        get?_of_incRcStore_other heq hget hparent
      have hcount := h.counts hold
      rw [incoming_incRcStore_other store loc rc node rest heq hget]
      exact hcount

/-- Retain a borrowed shared value as a new external root. Unlike `dup`, the
borrow itself is an edge rather than an existing root, so this adds exactly
one root and increments the refcount once. -/
theorem RootOwnership.retainShared {store : Store} {loc rc : Nat}
    {node : Node} {rest : List Root}
    (hget : store.get? loc = some ⟨.shared, rc, node⟩)
    (h : RootOwnership store rest) :
    RootOwnership (incRcStore store loc ⟨.shared, rc, node⟩)
      (⟨.shared, .loc loc⟩ :: rest) := by
  let updated : NodeBox := ⟨.shared, rc + 1, node⟩
  have hupdated :
      (incRcStore store loc ⟨.shared, rc, node⟩).get? loc =
        some updated := get?_incRcStore_same hget
  have targetWorld :
      HasWorld (incRcStore store loc ⟨.shared, rc, node⟩)
        .shared (.loc loc) := ⟨updated, hupdated, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro root hroot
    simp only [List.mem_cons] at hroot
    rcases hroot with rfl | hrest
    · exact targetWorld
    · exact HasWorld.incRcStore hget (h.roots_world root hrest)
  · intro parent parentBox hparent child hchild
    by_cases heq : loc = parent
    · subst parent
      have hboxeq : parentBox = updated := by
        exact Option.some.inj (hparent.symm.trans hupdated)
      subst parentBox
      exact HasWorld.incRcStore hget (h.edges_world hget child hchild)
    · have hold : store.get? parent = some parentBox :=
        get?_of_incRcStore_other heq hget hparent
      exact HasWorld.incRcStore hget (h.edges_world hold child hchild)
  · intro parent parentBox f arity args hparent hnode
    by_cases heq : loc = parent
    · subst parent
      have hboxeq : parentBox = updated := by
        exact Option.some.inj (hparent.symm.trans hupdated)
      subst parentBox
      change node = .papN f arity args at hnode
      exact h.pap_shared (loc := loc)
        (box := (⟨.shared, rc, node⟩ : NodeBox)) hget hnode
    · have hold : store.get? parent = some parentBox :=
        get?_of_incRcStore_other heq hget hparent
      exact h.pap_shared hold hnode
  · intro parent parentBox hparent
    by_cases heq : loc = parent
    · subst parent
      have hboxeq : parentBox = updated := by
        exact Option.some.inj (hparent.symm.trans hupdated)
      subst parentBox
      have hcount := h.counts hget
      change rc = incoming store rest loc at hcount
      change rc + 1 = incoming
        (incRcStore store loc ⟨.shared, rc, node⟩)
          (⟨.shared, .loc loc⟩ :: rest) loc
      rw [incoming_incRcStore_retain_same store loc rc node rest hget,
        hcount]
    · have hold : store.get? parent = some parentBox :=
        get?_of_incRcStore_other heq hget hparent
      have hcount := h.counts hold
      rw [incoming_incRcStore_retain_other store loc rc node rest heq hget]
      exact hcount

/-- Store transition performed by a non-final shared `drop`. -/
def decRcStore (store : Store) (loc : Nat) (box : NodeBox) : Store :=
  store.rcTick.setBox loc { box with rc := box.rc - 1 }

theorem get?_decRcStore_same {store : Store} {loc : Nat} {box : NodeBox}
    (h : store.get? loc = some box) :
    (decRcStore store loc box).get? loc =
      some { box with rc := box.rc - 1 } := by
  apply get?_setBox_same
  simpa using h

theorem get?_decRcStore_other {store : Store} {loc other : Nat}
    {box otherBox : NodeBox} (hne : loc ≠ other)
    (hlive : store.get? loc = some box)
    (h : store.get? other = some otherBox) :
    (decRcStore store loc box).get? other = some otherBox := by
  apply get?_setBox_other hne
  · simpa using hlive
  · simpa using h

theorem get?_of_decRcStore_other {store : Store} {loc other : Nat}
    {box otherBox : NodeBox} (hne : loc ≠ other)
    (hlive : store.get? loc = some box)
    (h : (decRcStore store loc box).get? other = some otherBox) :
    store.get? other = some otherBox := by
  have h' : store.rcTick.get? other = some otherBox := by
    apply get?_of_setBox_other hne
    · simpa using hlive
    · exact h
  simpa using h'

/-- Decrementing a shared node's refcount preserves every live node shape. -/
theorem StoreGraphRestricts.decRcStore {store : Store} {loc : Nat}
    {box : NodeBox} (hlive : store.get? loc = some box) :
    StoreGraphRestricts store (decRcStore store loc box) := by
  intro other world rc node hafter
  by_cases heq : loc = other
  · subst other
    have hupdated := get?_decRcStore_same hlive
    have hboxEq :
        ({ box with rc := box.rc - 1 } : NodeBox) = ⟨world, rc, node⟩ :=
      Option.some.inj (hupdated.symm.trans hafter)
    cases box with
    | mk boxWorld boxRc boxNode =>
      simp only at hboxEq
      cases hboxEq
      exact ⟨boxRc, hlive⟩
  · exact ⟨rc, get?_of_decRcStore_other heq hlive hafter⟩

theorem edgeLocations_decRcStore {store : Store} {loc : Nat} {box : NodeBox}
    (h : store.get? loc = some box) :
    edgeLocations (decRcStore store loc box) = edgeLocations store := by
  have hnodes := nodes_get?_of_get? h
  have hlist : store.nodes.toList[loc]? = some (some box) := by
    simpa using hnodes
  rw [edgeLocations, decRcStore, Store.setBox, Store.rcTick,
    Array.toList_set!]
  apply flatMap_set_eq_self slotEdgeLocations hlist
  rfl

theorem incoming_decRcStore_same (store : Store) (loc rc : Nat)
    (node : Node) (rest : List Root)
    (hget : store.get? loc = some ⟨.shared, rc, node⟩) :
    incoming (decRcStore store loc ⟨.shared, rc, node⟩) rest loc + 1 =
      incoming store (⟨.shared, .loc loc⟩ :: rest) loc := by
  rw [incoming, incoming, edgeLocations_decRcStore hget]
  simp [rootLocation?, rvalLocation?, List.count_append]

theorem incoming_decRcStore_other (store : Store) (loc rc : Nat)
    (node : Node) (rest : List Root) {other : Nat} (hne : loc ≠ other)
    (hget : store.get? loc = some ⟨.shared, rc, node⟩) :
    incoming (decRcStore store loc ⟨.shared, rc, node⟩) rest other =
      incoming store (⟨.shared, .loc loc⟩ :: rest) other := by
  rw [incoming, incoming, edgeLocations_decRcStore hget]
  simp [rootLocation?, rvalLocation?, List.count_append, hne]

theorem HasWorld.decRcStore {store : Store} {loc rc : Nat} {node : Node}
    {world : Owned} {value : RVal}
    (hget : store.get? loc = some ⟨.shared, rc, node⟩)
    (h : HasWorld store world value) :
    HasWorld (decRcStore store loc ⟨.shared, rc, node⟩) world value := by
  cases value with
  | loc valueLoc =>
    obtain ⟨box, hbox, hworld⟩ := h
    by_cases heq : loc = valueLoc
    · subst valueLoc
      have hboxeq : box = ⟨.shared, rc, node⟩ := by
        exact Option.some.inj (hbox.symm.trans hget)
      subst box
      exact ⟨⟨.shared, rc - 1, node⟩,
        get?_decRcStore_same hget, hworld⟩
    · exact ⟨box, get?_decRcStore_other heq hget hbox, hworld⟩
  | lit l => trivial
  | erased => trivial

/-- A non-final shared `drop` consumes one root and decrements its positive
refcount. `dropVal_preserves` below combines this local branch with final-owner
reclamation through a mutual induction over the executable deep drop. -/
theorem RootOwnership.dropSharedMany {store : Store} {loc rc : Nat}
    {node : Node} {rest : List Root} (hrc : 1 < rc)
    (hget : store.get? loc = some ⟨.shared, rc, node⟩)
    (h : RootOwnership store (⟨.shared, .loc loc⟩ :: rest)) :
    RootOwnership (decRcStore store loc ⟨.shared, rc, node⟩) rest := by
  let updated : NodeBox := ⟨.shared, rc - 1, node⟩
  have hupdated :
      (decRcStore store loc ⟨.shared, rc, node⟩).get? loc =
        some updated := get?_decRcStore_same hget
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro root hroot
    apply HasWorld.decRcStore hget
    apply h.roots_world root
    exact List.mem_cons_of_mem _ hroot
  · intro parent parentBox hparent child hchild
    by_cases heq : loc = parent
    · subst parent
      have hboxeq : parentBox = updated := by
        exact Option.some.inj (hparent.symm.trans hupdated)
      subst parentBox
      apply HasWorld.decRcStore hget
      exact h.edges_world hget child hchild
    · have hold : store.get? parent = some parentBox :=
        get?_of_decRcStore_other heq hget hparent
      exact HasWorld.decRcStore hget (h.edges_world hold child hchild)
  · intro parent parentBox f arity args hparent hnode
    by_cases heq : loc = parent
    · subst parent
      have hboxeq : parentBox = updated := by
        exact Option.some.inj (hparent.symm.trans hupdated)
      subst parentBox
      change node = .papN f arity args at hnode
      exact h.pap_shared (loc := loc)
        (box := (⟨.shared, rc, node⟩ : NodeBox)) hget hnode
    · have hold : store.get? parent = some parentBox :=
        get?_of_decRcStore_other heq hget hparent
      exact h.pap_shared hold hnode
  · intro parent parentBox hparent
    by_cases heq : loc = parent
    · subst parent
      have hboxeq : parentBox = updated := by
        exact Option.some.inj (hparent.symm.trans hupdated)
      subst parentBox
      have holdCount := h.counts hget
      change rc = incoming store (⟨.shared, .loc loc⟩ :: rest) loc
        at holdCount
      change rc - 1 = incoming
        (decRcStore store loc ⟨.shared, rc, node⟩) rest loc
      have hdelta := incoming_decRcStore_same store loc rc node rest hget
      omega
    · have hold : store.get? parent = some parentBox :=
        get?_of_decRcStore_other heq hget hparent
      have hcount := h.counts hold
      rw [incoming_decRcStore_other store loc rc node rest heq hget]
      exact hcount

/-! The abstract store transitions above are definitionally the successful
branches of the executable evaluator. -/

private theorem bindOk {error α β : Type} (value : α)
    (next : α → Except error β) :
    (Except.ok value >>= next) = next value := rfl

private theorem bindErr {error α β : Type} (err : error)
    (next : α → Except error β) :
    ((Except.error err : Except error α) >>= next) = .error err := rfl

/-! A `case` dispatch borrows its scrutinee and fields: selecting a branch
does not mutate the store or add roots. The selected branch is responsible
for every retain/release operation. -/

theorem RootOwnership.caseFieldsBorrowed {store : Store} {roots : List Root}
    {loc rc : Nat} {world : Owned} {cid : CtorId} {fields : Array RVal}
    (hget : store.get? loc = some ⟨world, rc, .ctorN cid fields⟩)
    (hown : RootOwnership store roots) :
    ∀ field ∈ fields.toList, HasWorld store world field := by
  intro field hfield
  exact hown.edges_world hget field (by simpa [nodeChildren] using hfield)

/-- Constructor-case dispatch is definitionally just entry into the selected
alternative with borrowed fields prepended to the environment. -/
theorem runCode_case_ctor {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {scrut : Atom} {peelNat : Bool}
    {alts : Array Alt} {loc rc : Nat} {world : Owned} {cid : CtorId}
    {fields : Array RVal} {tag nf : Nat} {body : Code}
    (hresolve : resolveAtom env scrut = .ok (.loc loc))
    (hget : store.get? loc = some ⟨world, rc, .ctorN cid fields⟩)
    (halt : alts.find? (fun alt => alt.cidx == cid.cidx) =
      some (.mk tag nf body))
    (hsize : fields.size = nf) :
    runCode ctx (fuel + 1) cur store env (.case scrut peelNat alts) =
      runCode ctx fuel cur store
        (fields.foldl (fun e field => field :: e) env) body := by
  rw [runCode.eq_def]
  dsimp only
  rw [hresolve, bindOk]
  dsimp only
  rw [hget]
  dsimp only
  rw [halt]
  simp [hsize]

/-- Exact constructor-case interface. The dispatcher preserves the incoming
root invariant and exposes only borrowed fields; a branch proof performs the
actual ownership transformation. -/
theorem runCode_case_ctor_owned {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {scrut : Atom}
    {peelNat : Bool} {alts : Array Alt} {loc rc : Nat} {world : Owned}
    {cid : CtorId} {fields : Array RVal} {tag nf : Nat} {body : Code}
    {value : RVal} {roots : List Root} {rest : List Root}
    (hresolve : resolveAtom env scrut = .ok (.loc loc))
    (hget : store.get? loc = some ⟨world, rc, .ctorN cid fields⟩)
    (halt : alts.find? (fun alt => alt.cidx == cid.cidx) =
      some (.mk tag nf body))
    (hsize : fields.size = nf)
    (hown : RootOwnership store roots)
    (hbranch : RootOwnership store roots →
      (∀ field ∈ fields.toList, HasWorld store world field) →
      runCode ctx fuel cur store
          (fields.foldl (fun e field => field :: e) env) body =
        .ok (store', value) →
      RootOwnership store' (⟨cur.result, value⟩ :: rest))
    (hrun : runCode ctx (fuel + 1) cur store env
      (.case scrut peelNat alts) = .ok (store', value)) :
    RootOwnership store' (⟨cur.result, value⟩ :: rest) := by
  rw [runCode_case_ctor hresolve hget halt hsize] at hrun
  exact hbranch hown (hown.caseFieldsBorrowed hget) hrun

/-- Constructor dispatch through a reusable alternative contract. The case
instruction supplies the field borrows; the selected alternative accounts
for every retain/release and preserves the caller continuation. -/
theorem runCode_case_ctor_contract_owned {ctx : Ctx} {fuel : Nat}
    {cur : FnDef} {store store' : Store} {env : List RVal}
    {scrut : Atom} {peelNat : Bool} {alts : Array Alt} {loc rc : Nat}
    {world : Owned} {cid : CtorId} {fields : Array RVal} {tag nf : Nat}
    {body : Code} {value : RVal} {rest : List Root}
    {entryValid : List RVal → Array RVal → Prop}
    {entryRoots : List RVal → Array RVal → List Root}
    (hresolve : resolveAtom env scrut = .ok (.loc loc))
    (hget : store.get? loc = some ⟨world, rc, .ctorN cid fields⟩)
    (halt : alts.find? (fun alt => alt.cidx == cid.cidx) =
      some (.mk tag nf body))
    (hsize : fields.size = nf)
    (hcontract : AltOwnershipContract ctx cur (.mk tag nf body)
      world entryValid entryRoots)
    (hvalid : entryValid env fields)
    (hown : RootOwnership store (entryRoots env fields ++ rest))
    (hrun : runCode ctx (fuel + 1) cur store env
      (.case scrut peelNat alts) = .ok (store', value)) :
    RootOwnership store' (⟨cur.result, value⟩ :: rest) := by
  rw [runCode_case_ctor hresolve hget halt hsize] at hrun
  exact hcontract.preserves hsize hvalid hown
    (hown.caseFieldsBorrowed hget) hrun

/-- A peeled zero literal enters the nullary alternative without changing
the store, environment, or roots. -/
theorem runCode_case_nat_zero {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {scrut : Atom} {alts : Array Alt}
    {tag : Nat} {body : Code}
    (hresolve : resolveAtom env scrut = .ok (.lit (.nat 0)))
    (halt : alts.find? (fun alt => alt.cidx == 0) =
      some (.mk tag 0 body)) :
    runCode ctx (fuel + 1) cur store env (.case scrut true alts) =
      runCode ctx fuel cur store env body := by
  rw [runCode.eq_def]
  dsimp only
  rw [hresolve, bindOk]
  dsimp only
  rw [halt]
  simp

/-- A peeled successor literal exposes its predecessor as an ownership-inert
literal binding. -/
theorem runCode_case_nat_succ {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {scrut : Atom} {alts : Array Alt}
    {n tag : Nat} {body : Code}
    (hresolve : resolveAtom env scrut = .ok (.lit (.nat (n + 1))))
    (halt : alts.find? (fun alt => alt.cidx == 1) =
      some (.mk tag 1 body)) :
    runCode ctx (fuel + 1) cur store env (.case scrut true alts) =
      runCode ctx fuel cur store (.lit (.nat n) :: env) body := by
  rw [runCode.eq_def]
  dsimp only
  rw [hresolve, bindOk]
  dsimp only
  rw [halt]
  simp

/-- Exact root preservation wrapper for a peeled zero branch. -/
theorem runCode_case_nat_zero_owned {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {scrut : Atom}
    {alts : Array Alt} {tag : Nat} {body : Code} {value : RVal}
    {roots rest : List Root}
    (hresolve : resolveAtom env scrut = .ok (.lit (.nat 0)))
    (halt : alts.find? (fun alt => alt.cidx == 0) =
      some (.mk tag 0 body))
    (hown : RootOwnership store roots)
    (hbranch : RootOwnership store roots →
      runCode ctx fuel cur store env body = .ok (store', value) →
      RootOwnership store' (⟨cur.result, value⟩ :: rest))
    (hrun : runCode ctx (fuel + 1) cur store env
      (.case scrut true alts) = .ok (store', value)) :
    RootOwnership store' (⟨cur.result, value⟩ :: rest) := by
  rw [runCode_case_nat_zero hresolve halt] at hrun
  exact hbranch hown hrun

/-- Exact root preservation wrapper for a peeled successor branch. -/
theorem runCode_case_nat_succ_owned {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {scrut : Atom}
    {alts : Array Alt} {n tag : Nat} {body : Code} {value : RVal}
    {roots rest : List Root}
    (hresolve : resolveAtom env scrut = .ok (.lit (.nat (n + 1))))
    (halt : alts.find? (fun alt => alt.cidx == 1) =
      some (.mk tag 1 body))
    (hown : RootOwnership store roots)
    (hbranch : RootOwnership store roots →
      runCode ctx fuel cur store (.lit (.nat n) :: env) body =
        .ok (store', value) →
      RootOwnership store' (⟨cur.result, value⟩ :: rest))
    (hrun : runCode ctx (fuel + 1) cur store env
      (.case scrut true alts) = .ok (store', value)) :
    RootOwnership store' (⟨cur.result, value⟩ :: rest) := by
  rw [runCode_case_nat_succ hresolve halt] at hrun
  exact hbranch hown hrun

/-- Peeled zero dispatch through the same alternative-contract interface as
constructor cases. Its exposed field array is empty. -/
theorem runCode_case_nat_zero_contract_owned {ctx : Ctx} {fuel : Nat}
    {cur : FnDef} {store store' : Store} {env : List RVal}
    {scrut : Atom} {alts : Array Alt} {tag : Nat} {body : Code}
    {value : RVal} {rest : List Root} {fieldWorld : Owned}
    {entryValid : List RVal → Array RVal → Prop}
    {entryRoots : List RVal → Array RVal → List Root}
    (hresolve : resolveAtom env scrut = .ok (.lit (.nat 0)))
    (halt : alts.find? (fun alt => alt.cidx == 0) =
      some (.mk tag 0 body))
    (hcontract : AltOwnershipContract ctx cur (.mk tag 0 body)
      fieldWorld entryValid entryRoots)
    (hvalid : entryValid env #[])
    (hown : RootOwnership store (entryRoots env #[] ++ rest))
    (hrun : runCode ctx (fuel + 1) cur store env
      (.case scrut true alts) = .ok (store', value)) :
    RootOwnership store' (⟨cur.result, value⟩ :: rest) := by
  rw [runCode_case_nat_zero hresolve halt] at hrun
  apply hcontract.preserves (fields := #[]) (by simp) hvalid hown
  · simp
  · simpa using hrun

/-- Peeled successor dispatch exposes its scalar predecessor as a borrowed
unary field and then applies the selected alternative contract. -/
theorem runCode_case_nat_succ_contract_owned {ctx : Ctx} {fuel : Nat}
    {cur : FnDef} {store store' : Store} {env : List RVal}
    {scrut : Atom} {alts : Array Alt} {n tag : Nat} {body : Code}
    {value : RVal} {rest : List Root} {fieldWorld : Owned}
    {entryValid : List RVal → Array RVal → Prop}
    {entryRoots : List RVal → Array RVal → List Root}
    (hresolve : resolveAtom env scrut = .ok (.lit (.nat (n + 1))))
    (halt : alts.find? (fun alt => alt.cidx == 1) =
      some (.mk tag 1 body))
    (hcontract : AltOwnershipContract ctx cur (.mk tag 1 body)
      fieldWorld entryValid entryRoots)
    (hvalid : entryValid env #[.lit (.nat n)])
    (hown : RootOwnership store
      (entryRoots env #[.lit (.nat n)] ++ rest))
    (hrun : runCode ctx (fuel + 1) cur store env
      (.case scrut true alts) = .ok (store', value)) :
    RootOwnership store' (⟨cur.result, value⟩ :: rest) := by
  rw [runCode_case_nat_succ hresolve halt] at hrun
  apply hcontract.preserves (fields := #[.lit (.nat n)]) (by simp)
    hvalid hown
  · intro field hfield
    have : field = .lit (.nat n) := by simpa using hfield
    subst field
    trivial
  · simpa using hrun

/-- Constructor dispatch through an alternative contract available below
the enclosing case fuel. -/
theorem runCode_case_ctor_contract_owned_below {ctx : Ctx} {fuel : Nat}
    {cur : FnDef} {store store' : Store} {env : List RVal}
    {scrut : Atom} {peelNat : Bool} {alts : Array Alt} {loc rc : Nat}
    {world : Owned} {cid : CtorId} {fields : Array RVal} {tag nf : Nat}
    {body : Code} {value : RVal} {rest : List Root}
    {entryValid : List RVal → Array RVal → Prop}
    {entryRoots : List RVal → Array RVal → List Root}
    (hresolve : resolveAtom env scrut = .ok (.loc loc))
    (hget : store.get? loc = some ⟨world, rc, .ctorN cid fields⟩)
    (halt : alts.find? (fun alt => alt.cidx == cid.cidx) =
      some (.mk tag nf body))
    (hsize : fields.size = nf)
    (hcontract : AltOwnershipContractBelow ctx cur (.mk tag nf body)
      world entryValid entryRoots (fuel + 1))
    (hvalid : entryValid env fields)
    (hown : RootOwnership store (entryRoots env fields ++ rest))
    (hrun : runCode ctx (fuel + 1) cur store env
      (.case scrut peelNat alts) = .ok (store', value)) :
    RootOwnership store' (⟨cur.result, value⟩ :: rest) := by
  rw [runCode_case_ctor hresolve hget halt hsize] at hrun
  exact hcontract.preserves (Nat.lt_succ_self fuel) hsize hvalid hown
    (hown.caseFieldsBorrowed hget) hrun

/-- Peeled-zero dispatch through a bounded nullary alternative contract. -/
theorem runCode_case_nat_zero_contract_owned_below
    {ctx : Ctx} {fuel : Nat} {cur : FnDef} {store store' : Store}
    {env : List RVal} {scrut : Atom} {alts : Array Alt} {tag : Nat}
    {body : Code} {value : RVal} {rest : List Root}
    {fieldWorld : Owned}
    {entryValid : List RVal → Array RVal → Prop}
    {entryRoots : List RVal → Array RVal → List Root}
    (hresolve : resolveAtom env scrut = .ok (.lit (.nat 0)))
    (halt : alts.find? (fun alt => alt.cidx == 0) =
      some (.mk tag 0 body))
    (hcontract : AltOwnershipContractBelow ctx cur (.mk tag 0 body)
      fieldWorld entryValid entryRoots (fuel + 1))
    (hvalid : entryValid env #[])
    (hown : RootOwnership store (entryRoots env #[] ++ rest))
    (hrun : runCode ctx (fuel + 1) cur store env
      (.case scrut true alts) = .ok (store', value)) :
    RootOwnership store' (⟨cur.result, value⟩ :: rest) := by
  rw [runCode_case_nat_zero hresolve halt] at hrun
  apply hcontract.preserves (fields := #[]) (Nat.lt_succ_self fuel)
    (by simp) hvalid hown
  · simp
  · simpa using hrun

/-- Peeled-successor dispatch through a bounded unary alternative
contract. -/
theorem runCode_case_nat_succ_contract_owned_below
    {ctx : Ctx} {fuel : Nat} {cur : FnDef} {store store' : Store}
    {env : List RVal} {scrut : Atom} {alts : Array Alt} {n tag : Nat}
    {body : Code} {value : RVal} {rest : List Root}
    {fieldWorld : Owned}
    {entryValid : List RVal → Array RVal → Prop}
    {entryRoots : List RVal → Array RVal → List Root}
    (hresolve : resolveAtom env scrut = .ok (.lit (.nat (n + 1))))
    (halt : alts.find? (fun alt => alt.cidx == 1) =
      some (.mk tag 1 body))
    (hcontract : AltOwnershipContractBelow ctx cur (.mk tag 1 body)
      fieldWorld entryValid entryRoots (fuel + 1))
    (hvalid : entryValid env #[.lit (.nat n)])
    (hown : RootOwnership store
      (entryRoots env #[.lit (.nat n)] ++ rest))
    (hrun : runCode ctx (fuel + 1) cur store env
      (.case scrut true alts) = .ok (store', value)) :
    RootOwnership store' (⟨cur.result, value⟩ :: rest) := by
  rw [runCode_case_nat_succ hresolve halt] at hrun
  apply hcontract.preserves (fields := #[.lit (.nat n)])
    (Nat.lt_succ_self fuel) (by simp) hvalid hown
  · intro field hfield
    have : field = .lit (.nat n) := by simpa using hfield
    subst field
    trivial
  · simpa using hrun

theorem dupVals_single {store : Store} {loc rc : Nat} {node : Node}
    (hget : store.get? loc = some ⟨.shared, rc, node⟩) :
    dupVals store [.loc loc] =
      .ok (incRcStore store loc ⟨.shared, rc, node⟩) := by
  simp [dupVals, hget, incRcStore]

/-- `dupVals` turns one borrowed shared value into one owned root. Locations
increment once; scalar roots are ownership-inert. -/
theorem dupVals_borrowed_preserves {store store' : Store}
    {value : RVal} {roots : List Root}
    (hown : RootOwnership store roots)
    (hworld : HasWorld store .shared value)
    (heval : dupVals store [value] = .ok store') :
    RootOwnership store' (⟨.shared, value⟩ :: roots) := by
  cases value with
  | lit literal =>
    simp [dupVals] at heval
    subst store'
    exact hown.addNoLocation rfl
  | erased =>
    simp [dupVals] at heval
    subst store'
    exact hown.addNoLocation rfl
  | loc loc =>
    obtain ⟨box, hget, hboxWorld⟩ := hworld
    cases box with
    | mk world rc node =>
      change world = .shared at hboxWorld
      subst world
      rw [dupVals_single hget] at heval
      injection heval with hstore
      subst store'
      exact hown.retainShared hget

/-- Duplicating shared values cannot invalidate the world of any value that
was live beforehand. -/
private theorem dupVals_hasWorld {store store' : Store}
    {values : List RVal}
    (heval : dupVals store values = .ok store') :
    ∀ {world value}, HasWorld store world value →
      HasWorld store' world value := by
  induction values generalizing store with
  | nil =>
    change (.ok store : Except Err Store) = .ok store' at heval
    injection heval with hstore
    subst store'
    exact fun h => h
  | cons head tail ih =>
    cases head with
    | lit literal =>
      simp only [dupVals, List.foldlM_cons] at heval
      exact ih heval
    | erased =>
      simp only [dupVals, List.foldlM_cons] at heval
      exact ih heval
    | loc loc =>
      simp only [dupVals, List.foldlM_cons] at heval
      cases hget : store.get? loc with
      | none => simp [hget, bindErr] at heval
      | some box =>
        cases box with
        | mk boxWorld rc node =>
          cases boxWorld with
          | unique => simp [hget, bindErr] at heval
          | shared =>
            simp only [hget] at heval
            exact ih heval ∘ HasWorld.incRcStore hget

private theorem dupVals_cons_ok_inv {store store' : Store}
    {head : RVal} {tail : List RVal}
    (heval : dupVals store (head :: tail) = .ok store') :
    ∃ middle, dupVals store [head] = .ok middle ∧
      dupVals middle tail = .ok store' := by
  rw [show head :: tail = [head] ++ tail by rfl, dupVals,
    List.foldlM_append] at heval
  change (dupVals store [head] >>= fun middle => dupVals middle tail) =
    .ok store' at heval
  cases hmiddle : dupVals store [head] with
  | error err =>
    rw [hmiddle, bindErr] at heval
    contradiction
  | ok middle =>
    refine ⟨middle, rfl, ?_⟩
    rw [hmiddle, bindOk] at heval
    exact heval

/-- Retaining one shared value changes at most a refcount and therefore
preserves every pre-existing live node shape. -/
private theorem dupVals_single_extends {store store' : Store}
    {value : RVal} (heval : dupVals store [value] = .ok store') :
    StoreGraphExtends store store' := by
  cases value with
  | lit literal =>
    simp [dupVals] at heval
    subst store'
    exact StoreGraphExtends.refl store
  | erased =>
    simp [dupVals] at heval
    subst store'
    exact StoreGraphExtends.refl store
  | loc loc =>
    cases hget : store.get? loc with
    | none => simp [dupVals, hget] at heval
    | some box =>
      cases box with
      | mk world rc node =>
        cases world with
        | unique => simp [dupVals, hget] at heval
        | shared =>
          have hresult :
              (store.setBox loc
                ⟨.shared, rc + 1, node⟩).rcTick = store' := by
            simpa [dupVals, hget] using heval
          subst store'
          intro other otherWorld otherRc otherNode hother
          exact (StoreGraphExtends.incRcStore hget) hother

/-- `dupVals` is a sequence of refcount-only extensions. -/
theorem dupVals_extends {store store' : Store} {values : List RVal}
    (heval : dupVals store values = .ok store') :
    StoreGraphExtends store store' := by
  induction values generalizing store with
  | nil =>
    change (.ok store : Except Err Store) = .ok store' at heval
    injection heval with hstore
    subst store'
    exact StoreGraphExtends.refl store
  | cons head tail ih =>
    obtain ⟨middle, hhead, htail⟩ := dupVals_cons_ok_inv heval
    exact StoreGraphExtends.trans (dupVals_single_extends hhead)
      (ih htail)

/-- `dupVals` turns a list of borrowed shared values into owned roots. -/
theorem dupVals_borrowedMany_preserves {store store' : Store}
    {values : List RVal} {roots : List Root}
    (hown : RootOwnership store roots)
    (hworld : ∀ value ∈ values, HasWorld store .shared value)
    (heval : dupVals store values = .ok store') :
    RootOwnership store' (rootsFor .shared values ++ roots) := by
  induction values generalizing store roots with
  | nil =>
    change (.ok store : Except Err Store) = .ok store' at heval
    injection heval with hstore
    subst store'
    simpa [rootsFor] using hown
  | cons head tail ih =>
    obtain ⟨middle, hheadEval, htailEval⟩ := dupVals_cons_ok_inv heval
    have hheadWorld : HasWorld store .shared head :=
      hworld head (by simp)
    have hmiddle : RootOwnership middle (⟨.shared, head⟩ :: roots) :=
      dupVals_borrowed_preserves hown hheadWorld hheadEval
    have htailWorld : ∀ value ∈ tail,
        HasWorld middle .shared value := by
      intro value hvalue
      exact dupVals_hasWorld hheadEval (hworld value (by simp [hvalue]))
    have htail := ih hmiddle htailWorld htailEval
    apply htail.perm
    simpa [rootsFor, List.append_assoc] using
      (List.perm_append_comm (l₁ := rootsFor .shared tail)
        (l₂ := [(⟨.shared, head⟩ : Root)])).append_right roots

theorem runOp_dup {ctx : Ctx} {fuel : Nat} {cur : FnDef} {store : Store}
    {env : List RVal} {target : Atom} {loc rc : Nat} {node : Node}
    (hresolve : resolveAtom env target = .ok (.loc loc))
    (hget : store.get? loc = some ⟨.shared, rc, node⟩) :
    runOp ctx (fuel + 1) cur store env (.dup target) =
      .ok (incRcStore store loc ⟨.shared, rc, node⟩, .loc loc) := by
  rw [runOp.eq_def]
  dsimp only
  rw [hresolve]
  rw [bindOk]
  simp only
  rw [hget]
  rfl

/-- Executing `dup` on a borrowed shared value retains it as one owned root.
This is the operation-level interface used immediately after `fetch`. -/
theorem runOp_retain_borrowed {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {target : Atom} {value : RVal}
    {roots : List Root}
    (hresolve : resolveAtom env target = .ok value)
    (hworld : HasWorld store .shared value)
    (hown : RootOwnership store roots) :
    ∃ store',
      runOp ctx (fuel + 1) cur store env (.dup target) =
          .ok (store', value) ∧
        RootOwnership store' (⟨.shared, value⟩ :: roots) := by
  cases value with
  | lit literal =>
    refine ⟨store, ?_, hown.addNoLocation rfl⟩
    rw [runOp.eq_def]
    dsimp only
    rw [hresolve, bindOk]
  | erased =>
    refine ⟨store, ?_, hown.addNoLocation rfl⟩
    rw [runOp.eq_def]
    dsimp only
    rw [hresolve, bindOk]
  | loc loc =>
    obtain ⟨box, hget, hboxWorld⟩ := hworld
    cases box with
    | mk world rc node =>
      change world = .shared at hboxWorld
      subst world
      refine ⟨incRcStore store loc ⟨.shared, rc, node⟩,
        runOp_dup hresolve hget, hown.retainShared hget⟩

/-- Semantic strengthening of `runOp_retain_borrowed`: refcount-only store
updates preserve the pure value graph for the retained result. -/
theorem runOp_retain_borrowed_valueGraph
    {funRel : FunctionRel} {sourceValue : IxIR0.Value}
    {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {target : Atom} {value : RVal}
    {roots : List Root}
    (hresolve : resolveAtom env target = .ok value)
    (hworld : HasWorld store .shared value)
    (hgraph : ValueGraph funRel store sourceValue value)
    (hown : RootOwnership store roots) :
    ∃ store',
      runOp ctx (fuel + 1) cur store env (.dup target) =
          .ok (store', value) ∧
      StoreGraphExtends store store' ∧
      ValueGraph funRel store' sourceValue value ∧
      RootOwnership store' (⟨.shared, value⟩ :: roots) := by
  cases value with
  | lit literal =>
    refine ⟨store, ?_, StoreGraphExtends.refl store, hgraph,
      hown.addNoLocation rfl⟩
    rw [runOp.eq_def]
    dsimp only
    rw [hresolve, bindOk]
  | erased =>
    refine ⟨store, ?_, StoreGraphExtends.refl store, hgraph,
      hown.addNoLocation rfl⟩
    rw [runOp.eq_def]
    dsimp only
    rw [hresolve, bindOk]
  | loc loc =>
    obtain ⟨box, hget, hboxWorld⟩ := hworld
    cases box with
    | mk world rc node =>
      change world = .shared at hboxWorld
      subst world
      let store' := incRcStore store loc ⟨.shared, rc, node⟩
      have hstore : StoreGraphExtends store store' :=
        StoreGraphExtends.incRcStore hget
      refine ⟨store', runOp_dup hresolve hget, hstore,
        hgraph.monoStore hstore, hown.retainShared hget⟩

/-- Retaining one borrowed field preserves shared-world evidence for every
other field that a later step may retain. Locations transport through the
single RC update; scalar evidence is unchanged. -/
theorem runOp_retain_borrowed_preserves_hasWorlds
    {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {target : Atom} {value : RVal}
    {roots : List Root} {borrowed : List RVal}
    (hresolve : resolveAtom env target = .ok value)
    (hworld : HasWorld store .shared value)
    (hown : RootOwnership store roots)
    (hborrowed : ∀ candidate ∈ borrowed,
      HasWorld store .shared candidate) :
    ∃ store',
      runOp ctx (fuel + 1) cur store env (.dup target) =
          .ok (store', value) ∧
        RootOwnership store' (⟨.shared, value⟩ :: roots) ∧
        ∀ candidate ∈ borrowed,
          HasWorld store' .shared candidate := by
  cases value with
  | lit literal =>
    refine ⟨store, ?_, hown.addNoLocation rfl, hborrowed⟩
    rw [runOp.eq_def]
    dsimp only
    rw [hresolve, bindOk]
  | erased =>
    refine ⟨store, ?_, hown.addNoLocation rfl, hborrowed⟩
    rw [runOp.eq_def]
    dsimp only
    rw [hresolve, bindOk]
  | loc loc =>
    obtain ⟨box, hget, hboxWorld⟩ := hworld
    cases box with
    | mk world rc node =>
      change world = .shared at hboxWorld
      subst world
      refine ⟨incRcStore store loc ⟨.shared, rc, node⟩,
        runOp_dup hresolve hget, hown.retainShared hget, ?_⟩
      intro candidate hmem
      exact HasWorld.incRcStore hget (hborrowed candidate hmem)

theorem runOp_reuse {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {target : Atom} {cid : CtorId}
    {args : Array Atom} {values : List RVal} {loc rc : Nat}
    {oldNode : Node}
    (hargs : resolveAtoms env args = .ok values)
    (hresolve : resolveAtom env target = .ok (.loc loc))
    (hget : store.get? loc = some ⟨.unique, rc, oldNode⟩) :
    runOp ctx (fuel + 1) cur store env (.reuse target cid args) =
      .ok (reuseNodeStore store loc (.ctorN cid values.toArray), .loc loc) := by
  rw [runOp.eq_def]
  dsimp only
  rw [hargs, bindOk]
  rw [hresolve, bindOk]
  dsimp only
  rw [hget]
  dsimp only
  rw [reuseNodeStore_eq_direct]

/-- Exact ownership transfer across a direct invocation from a contract
available below the invocation fuel. A successful invocation at `fuel + 1`
runs the callee body at `fuel`, so the bound is strict exactly where the
mutual declaration induction needs it. -/
theorem invoke_fn_owned_below {ctx : Ctx} {fuel : Nat} {f : Address}
    {argWorlds : List Owned} {args : List RVal} {store store' : Store}
    {value : RVal} {rest : List Root} {d : FnDef}
    (hdecl : ctx.decls f = some (.fn d))
    (hcontract : FnOwnershipContractBelow ctx d argWorlds fuel)
    (hown : RootOwnership store
      (rootsForWorlds argWorlds args ++ rest))
    (hinvoke : invoke ctx fuel f args store = .ok (store', value)) :
    RootOwnership store' (⟨d.result, value⟩ :: rest) := by
  cases fuel with
  | zero => simp [invoke] at hinvoke
  | succ fuel =>
    simp only [invoke, hdecl] at hinvoke
    split at hinvoke
    · contradiction
    next hlen =>
      have hargsLength : args.length = argWorlds.length := by
        have hd : args.length = d.arity := by simpa using hlen
        exact hd.trans hcontract.arity_eq.symm
      cases hrun : runCode ctx fuel d store args.reverse d.body with
      | error e =>
        rw [hrun] at hinvoke
        change (.error e : Except Err (Store × RVal)) =
          .ok (store', value) at hinvoke
        contradiction
      | ok out =>
        rw [hrun] at hinvoke
        change checkResultWorld d.result out = .ok (store', value) at hinvoke
        obtain ⟨hpair, _⟩ := checkResultWorld_ok hinvoke
        subst out
        exact hcontract.preserves (Nat.lt_succ_self fuel)
          hargsLength hown hrun

/-- Exact ownership transfer across a successful direct invocation: the
callee consumes its argument roots and returns one root in its declared
world, while every unrelated continuation root is preserved. -/
theorem invoke_fn_owned {ctx : Ctx} {fuel : Nat} {f : Address}
    {argWorlds : List Owned} {args : List RVal} {store store' : Store}
    {value : RVal} {rest : List Root} {d : FnDef}
    (hdecl : ctx.decls f = some (.fn d))
    (hcontract : FnOwnershipContract ctx d argWorlds)
    (hown : RootOwnership store
      (rootsForWorlds argWorlds args ++ rest))
    (hinvoke : invoke ctx fuel f args store = .ok (store', value)) :
    RootOwnership store' (⟨d.result, value⟩ :: rest) := by
  exact invoke_fn_owned_below hdecl (hcontract.below fuel) hown hinvoke

private theorem rootsForWorlds_replicate_eq_rootsFor_apply (world : Owned) :
    ∀ {values : List RVal} {count : Nat}, values.length = count →
      rootsForWorlds (List.replicate count world) values =
        rootsFor world values := by
  intro values count hlength
  induction values generalizing count with
  | nil =>
    cases count <;> simp_all [rootsFor, rootsForWorlds]
  | cons value values ih =>
    cases count with
    | zero => simp at hlength
    | succ count =>
      simp only [List.length_cons, Nat.succ.injEq] at hlength
      simp [List.replicate_succ, rootsFor, ih hlength]

/-- Invocation through a declaration approved for shared PAP entry consumes
shared argument roots and returns one shared root. Successful extern calls are
covered by their scalar-only ABI. -/
theorem invoke_papSafe_owned_below {ctx : Ctx} {fuel : Nat}
    (hdecls : PapSafeDeclContractsBelow ctx fuel)
    {address : Address} {d : Decl} {args : List RVal}
    {store store' : Store} {value : RVal} {rest : List Root}
    (hdecl : ctx.decls address = some d)
    (hpapSafe : declPapSafe d = true)
    (hown : RootOwnership store (rootsFor .shared args ++ rest))
    (hrun : invoke ctx fuel address args store = .ok (store', value)) :
    RootOwnership store' (⟨.shared, value⟩ :: rest) := by
  cases d with
  | fn fnDef =>
    obtain ⟨hresult, hcontract⟩ := hdecls.fn hdecl hpapSafe
    have hworlds : rootsForWorlds
        (List.replicate fnDef.arity .shared) args =
          rootsFor .shared args := by
      have hlength : args.length = fnDef.arity := by
        cases fuel with
        | zero => simp [invoke] at hrun
        | succ innerFuel =>
          simp only [invoke, hdecl] at hrun
          split at hrun
          next hne => contradiction
          next heq => simpa using heq
      exact rootsForWorlds_replicate_eq_rootsFor_apply .shared hlength
    have howned : RootOwnership store
        (rootsForWorlds (List.replicate fnDef.arity .shared) args ++ rest) := by
      rwa [hworlds]
    have hout := invoke_fn_owned_below hdecl hcontract howned hrun
    rwa [hresult] at hout
  | extern arity =>
    cases fuel with
    | zero => simp [invoke] at hrun
    | succ innerFuel =>
      simp only [invoke, hdecl] at hrun
      split at hrun
      next hne => contradiction
      next heq =>
        cases hcall : callScalarOracle ctx address args with
        | error err =>
          rw [hcall] at hrun
          contradiction
        | ok result =>
          rw [hcall] at hrun
          simp only at hrun
          injection hrun with hpair
          cases hpair
          have hscalar := callScalarOracle_ok hcall
          exact (hown.dropScalars hscalar.1).addNoLocation
            (RVal.rvalLocation?_eq_none_of_isScalar hscalar.2)

/-- The evaluator-level interface for a lowered direct call: resolving the
argument atoms and successfully invoking a function establishes the declared
world of the returned value. Exact root conservation is the next call proof. -/
theorem runOp_call_result_hasWorld {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {f : Address}
    {args : Array Atom} {values : List RVal} {value : RVal} {d : FnDef}
    (hargs : resolveAtoms env args = .ok values)
    (hdecl : ctx.decls f = some (.fn d))
    (hrun : runOp ctx (fuel + 1) cur store env (.call f args) =
      .ok (store', value)) :
    HasWorld store' d.result value := by
  rw [runOp.eq_def] at hrun
  dsimp only at hrun
  rw [hargs, bindOk] at hrun
  exact invoke_fn_result_hasWorld hdecl hrun

/-- Exact operation-level direct-call interface under the bounded contract
environment used by the mutual compiler induction. -/
theorem runOp_call_owned_below {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {f : Address}
    {atoms : Array Atom} {args : List RVal} {value : RVal} {d : FnDef}
    {argWorlds : List Owned} {rest : List Root}
    (hargs : resolveAtoms env atoms = .ok args)
    (hdecl : ctx.decls f = some (.fn d))
    (hcontract : FnOwnershipContractBelow ctx d argWorlds fuel)
    (hown : RootOwnership store
      (rootsForWorlds argWorlds args ++ rest))
    (hrun : runOp ctx (fuel + 1) cur store env (.call f atoms) =
      .ok (store', value)) :
    RootOwnership store' (⟨d.result, value⟩ :: rest) := by
  rw [runOp.eq_def] at hrun
  dsimp only at hrun
  rw [hargs, bindOk] at hrun
  exact invoke_fn_owned_below hdecl hcontract hown hrun

/-- Exact operation-level direct-call interface used by completed compiler
contracts. -/
theorem runOp_call_owned {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {f : Address}
    {atoms : Array Atom} {args : List RVal} {value : RVal} {d : FnDef}
    {argWorlds : List Owned} {rest : List Root}
    (hargs : resolveAtoms env atoms = .ok args)
    (hdecl : ctx.decls f = some (.fn d))
    (hcontract : FnOwnershipContract ctx d argWorlds)
    (hown : RootOwnership store
      (rootsForWorlds argWorlds args ++ rest))
    (hrun : runOp ctx (fuel + 1) cur store env (.call f atoms) =
      .ok (store', value)) :
    RootOwnership store' (⟨d.result, value⟩ :: rest) := by
  exact runOp_call_owned_below hargs hdecl (hcontract.below fuel) hown hrun

/-- Exact operation-level interface for unknown higher-order application
under the bounded contract used by the mutual fuel induction. -/
theorem runOp_apply_owned_below {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {functionAtom : Atom}
    {function : RVal} {atoms : Array Atom} {args : List RVal}
    {value : RVal} {rest : List Root}
    (hfunction : resolveAtom env functionAtom = .ok function)
    (hargs : resolveAtoms env atoms = .ok args)
    (hcontract : ApplyOwnershipContractBelow ctx (fuel + 1))
    (hown : RootOwnership store
      (⟨.shared, function⟩ :: rootsFor .shared args ++ rest))
    (hrun : runOp ctx (fuel + 1) cur store env
      (.apply functionAtom atoms) = .ok (store', value)) :
    RootOwnership store' (⟨.shared, value⟩ :: rest) := by
  rw [runOp.eq_def] at hrun
  dsimp only at hrun
  rw [hfunction, bindOk, hargs, bindOk] at hrun
  exact hcontract.preserves (Nat.lt_succ_self fuel) hown hrun

/-- Exact operation-level interface for unknown higher-order application.
The context contract hides pap saturation/over-application recursion while
retaining the ownership boundary required by `applyRest`. -/
theorem runOp_apply_owned {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {functionAtom : Atom}
    {function : RVal} {atoms : Array Atom} {args : List RVal}
    {value : RVal} {rest : List Root}
    (hfunction : resolveAtom env functionAtom = .ok function)
    (hargs : resolveAtoms env atoms = .ok args)
    (hcontract : ApplyOwnershipContract ctx)
    (hown : RootOwnership store
      (⟨.shared, function⟩ :: rootsFor .shared args ++ rest))
    (hrun : runOp ctx (fuel + 1) cur store env
      (.apply functionAtom atoms) = .ok (store', value)) :
    RootOwnership store' (⟨.shared, value⟩ :: rest) := by
  exact runOp_apply_owned_below hfunction hargs
    (hcontract.below (fuel + 1)) hown hrun

/-- `callSelf` enforces the same result-world contract from the current
function frame. -/
theorem runOp_callSelf_result_hasWorld {ctx : Ctx} {fuel : Nat}
    {cur : FnDef} {store store' : Store} {env : List RVal}
    {args : Array Atom} {values : List RVal} {value : RVal}
    (hargs : resolveAtoms env args = .ok values)
    (hrun : runOp ctx (fuel + 1) cur store env (.callSelf args) =
      .ok (store', value)) :
    HasWorld store' cur.result value := by
  rw [runOp.eq_def] at hrun
  dsimp only at hrun
  rw [hargs, bindOk] at hrun
  split at hrun
  · contradiction
  · cases hcode : runCode ctx fuel cur store values.reverse cur.body with
    | error e =>
      rw [hcode] at hrun
      change (.error e : Except Err (Store × RVal)) =
        .ok (store', value) at hrun
      contradiction
    | ok out =>
      rw [hcode] at hrun
      change checkResultWorld cur.result out = .ok (store', value) at hrun
      obtain ⟨hpair, hw⟩ := checkResultWorld_ok hrun
      subst out
      exact hw

/-- Exact ownership transfer for a recursive self call from a contract
available below the operation's fuel bound. The evaluator enters `cur.body`
at `fuel`, strictly below `fuel + 1`; this is the operational decrease used
by the mutual declaration-contract seal. -/
theorem runOp_callSelf_owned_below {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {atoms : Array Atom}
    {args : List RVal} {value : RVal} {argWorlds : List Owned}
    {rest : List Root}
    (hargs : resolveAtoms env atoms = .ok args)
    (hcontract : FnOwnershipContractBelow ctx cur argWorlds (fuel + 1))
    (hown : RootOwnership store
      (rootsForWorlds argWorlds args ++ rest))
    (hrun : runOp ctx (fuel + 1) cur store env (.callSelf atoms) =
      .ok (store', value)) :
    RootOwnership store' (⟨cur.result, value⟩ :: rest) := by
  rw [runOp.eq_def] at hrun
  dsimp only at hrun
  rw [hargs, bindOk] at hrun
  split at hrun
  · contradiction
  next hlen =>
    have hargsLength : args.length = argWorlds.length := by
      have hd : args.length = cur.arity := by simpa using hlen
      exact hd.trans hcontract.arity_eq.symm
    cases hcode : runCode ctx fuel cur store args.reverse cur.body with
    | error e =>
      rw [hcode] at hrun
      change (.error e : Except Err (Store × RVal)) =
        .ok (store', value) at hrun
      contradiction
    | ok out =>
      rw [hcode] at hrun
      change checkResultWorld cur.result out = .ok (store', value) at hrun
      obtain ⟨hpair, _⟩ := checkResultWorld_ok hrun
      subst out
      exact hcontract.preserves (Nat.lt_succ_self fuel)
        hargsLength hown hcode

/-- Exact ownership transfer for recursive self calls, under the current
function's public semantic contract. -/
theorem runOp_callSelf_owned {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {atoms : Array Atom}
    {args : List RVal} {value : RVal} {argWorlds : List Owned}
    {rest : List Root}
    (hargs : resolveAtoms env atoms = .ok args)
    (hcontract : FnOwnershipContract ctx cur argWorlds)
    (hown : RootOwnership store
      (rootsForWorlds argWorlds args ++ rest))
    (hrun : runOp ctx (fuel + 1) cur store env (.callSelf atoms) =
      .ok (store', value)) :
    RootOwnership store' (⟨cur.result, value⟩ :: rest) := by
  exact runOp_callSelf_owned_below hargs (hcontract.below (fuel + 1))
    hown hrun

/-- Exact ownership transfer across the scalar-only extern ABI. Successful
evaluation proves every argument and the result scalar, so argument roots
are ownership-inert, the store is unchanged, and the result may be recorded
in either demanded world. -/
theorem runOp_extern_owned {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {f : Address}
    {atoms : Array Atom} {args : List RVal} {value : RVal}
    {resultWorld : Owned} {rest : List Root}
    (hargs : resolveAtoms env atoms = .ok args)
    (hown : RootOwnership store (rootsFor .shared args ++ rest))
    (hrun : runOp ctx (fuel + 1) cur store env (.extern f atoms) =
      .ok (store', value)) :
    RootOwnership store' (⟨resultWorld, value⟩ :: rest) := by
  rw [runOp.eq_def] at hrun
  dsimp only at hrun
  rw [hargs, bindOk] at hrun
  cases horacle : callScalarOracle ctx f args with
  | error err =>
    rw [horacle] at hrun
    change (Except.error err : Except Err (Store × RVal)) =
      .ok (store', value) at hrun
    contradiction
  | ok result =>
    rw [horacle] at hrun
    change (Except.ok (store, result) : Except Err (Store × RVal)) =
      .ok (store', value) at hrun
    have hpair : (store, result) = (store', value) := Except.ok.inj hrun
    cases hpair
    have hscalar := callScalarOracle_ok horacle
    exact (hown.dropScalars hscalar.1).addNoLocation
      (RVal.rvalLocation?_eq_none_of_isScalar hscalar.2)

theorem runOp_pure {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {target : Atom} {value : RVal}
    (hresolve : resolveAtom env target = .ok value) :
    runOp ctx (fuel + 1) cur store env (.pure target) =
      .ok (store, value) := by
  rw [runOp.eq_def]
  dsimp only
  rw [hresolve, bindOk]

/-- The lowering emits `pure` for scalar constants. Binding that result adds
an ownership-inert root in whichever world the continuation demands. -/
theorem runOp_pure_scalar_owned {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {target : Atom} {value : RVal}
    {world : Owned} {roots : List Root}
    (hresolve : resolveAtom env target = .ok value)
    (hnone : rvalLocation? value = none)
    (hown : RootOwnership store roots) :
    runOp ctx (fuel + 1) cur store env (.pure target) =
        .ok (store, value) ∧
      RootOwnership store (⟨world, value⟩ :: roots) :=
  ⟨runOp_pure hresolve, hown.addNoLocation hnone⟩

theorem runOp_alloc {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {world : Owned} {cid : CtorId}
    {args : Array Atom} {values : List RVal}
    (hresolve : resolveAtoms env args = .ok values) :
    runOp ctx (fuel + 1) cur store env (.alloc world cid args) =
      .ok ((store.allocNode world (.ctorN cid values.toArray)).1,
        .loc (store.allocNode world (.ctorN cid values.toArray)).2) := by
  rw [runOp.eq_def]
  dsimp only
  rw [hresolve, bindOk]

theorem runOp_free {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {target : Atom} {loc rc : Nat}
    {node : Node}
    (hresolve : resolveAtom env target = .ok (.loc loc))
    (hget : store.get? loc = some ⟨.unique, rc, node⟩) :
    runOp ctx (fuel + 1) cur store env (.free target) =
      .ok (store.kill loc, .erased) := by
  rw [runOp.eq_def]
  dsimp only
  rw [hresolve, bindOk]
  dsimp only
  rw [hget]

/-- The shallow-free evaluator branch consumes the unique parent root and
exposes its fields as unique roots, ready for reuse, transfer, or deep drop. -/
theorem runOp_free_owned {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {target : Atom} {loc : Nat}
    {node : Node} {rest : List Root}
    (hresolve : resolveAtom env target = .ok (.loc loc))
    (hget : store.get? loc = some ⟨.unique, 1, node⟩)
    (hown : RootOwnership store (⟨.unique, .loc loc⟩ :: rest)) :
    runOp ctx (fuel + 1) cur store env (.free target) =
        .ok (store.kill loc, .erased) ∧
      RootOwnership (store.kill loc)
        (rootsFor .unique (nodeChildren node) ++ rest) :=
  ⟨runOp_free hresolve hget, hown.killUniqueOne hget⟩

theorem runOp_fetch {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {target : Atom} {loc rc i : Nat}
    {world : Owned} {cid : CtorId} {fields : Array RVal} {value : RVal}
    (hresolve : resolveAtom env target = .ok (.loc loc))
    (hget : store.get? loc = some ⟨world, rc, .ctorN cid fields⟩)
    (hfield : fields[i]? = some value) :
    runOp ctx (fuel + 1) cur store env (.fetch target i) =
      .ok (store, value) := by
  rw [runOp.eq_def]
  dsimp only
  rw [hresolve, bindOk]
  dsimp only
  rw [hget]
  dsimp only
  rw [hfield]

/-- A successful fetch returns an existing node edge as a borrow: the store
and root multiset are unchanged, while the returned value is known to inhabit
the parent's world. -/
theorem RootOwnership.fetchBorrowed {store : Store} {roots : List Root}
    {loc rc i : Nat} {world : Owned} {cid : CtorId}
    {fields : Array RVal} {value : RVal}
    (hget : store.get? loc = some ⟨world, rc, .ctorN cid fields⟩)
    (hfield : fields[i]? = some value)
    (h : RootOwnership store roots) : HasWorld store world value := by
  have harray : value ∈ fields :=
    (Array.mem_iff_getElem?).2 ⟨i, hfield⟩
  have hlist : value ∈ fields.toList := by simpa using harray
  exact h.edges_world hget value (by simpa [nodeChildren] using hlist)

theorem runOp_fetch_borrowed {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {target : Atom} {roots : List Root}
    {loc rc i : Nat} {cid : CtorId} {fields : Array RVal} {value : RVal}
    (hresolve : resolveAtom env target = .ok (.loc loc))
    (hget : store.get? loc = some ⟨.shared, rc, .ctorN cid fields⟩)
    (hfield : fields[i]? = some value)
    (hown : RootOwnership store roots) :
    runOp ctx (fuel + 1) cur store env (.fetch target i) =
        .ok (store, value) ∧
      HasWorld store .shared value :=
  ⟨runOp_fetch hresolve hget hfield, hown.fetchBorrowed hget hfield⟩

/-- Fetch followed by the lowering's retain step produces one owned shared
field root while retaining every pre-existing root. -/
theorem fetch_dupVals_preserves {store store' : Store} {roots : List Root}
    {loc rc i : Nat} {cid : CtorId} {fields : Array RVal} {value : RVal}
    (hget : store.get? loc = some ⟨.shared, rc, .ctorN cid fields⟩)
    (hfield : fields[i]? = some value)
    (hown : RootOwnership store roots)
    (heval : dupVals store [value] = .ok store') :
    RootOwnership store' (⟨.shared, value⟩ :: roots) :=
  dupVals_borrowed_preserves hown (hown.fetchBorrowed hget hfield) heval

theorem runOp_drop {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {target : Atom} {loc : Nat}
    (hresolve : resolveAtom env target = .ok (.loc loc))
    (heval : dropVal ctx fuel store (.loc loc) = .ok store') :
    runOp ctx (fuel + 1) cur store env (.drop target) =
      .ok (store', .erased) := by
  rw [runOp.eq_def]
  dsimp only
  rw [hresolve, bindOk]
  dsimp only
  rw [heval, bindOk]

theorem runOp_dropU {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {target : Atom} {loc : Nat}
    (hresolve : resolveAtom env target = .ok (.loc loc))
    (heval : dropUVal ctx fuel store (.loc loc) = .ok store') :
    runOp ctx (fuel + 1) cur store env (.dropU target) =
      .ok (store', .erased) := by
  rw [runOp.eq_def]
  dsimp only
  rw [hresolve, bindOk]
  dsimp only
  rw [heval, bindOk]

theorem dropVal_shared_many {ctx : Ctx} {fuel loc rc : Nat} {store : Store}
    {node : Node} (hrc : 1 < rc)
    (hget : store.get? loc = some ⟨.shared, rc, node⟩) :
    dropVal ctx (fuel + 1) store (.loc loc) =
      .ok (decRcStore store loc ⟨.shared, rc, node⟩) := by
  rw [dropVal.eq_def]
  dsimp only
  rw [hget]
  dsimp only
  have hne : (rc == 1) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  rw [hne]
  rfl

private def DropPreservesAt (ctx : Ctx) (fuel : Nat) : Prop :=
  (∀ (store : Store) (value : RVal) (rest : List Root) (store' : Store),
    RootOwnership store (⟨.shared, value⟩ :: rest) →
    dropVal ctx fuel store value = .ok store' →
    RootOwnership store' rest) ∧
  (∀ (store : Store) (values : List RVal) (rest : List Root)
      (store' : Store),
    RootOwnership store (rootsFor .shared values ++ rest) →
    dropMany ctx fuel store values = .ok store' →
    RootOwnership store' rest)

private theorem dropPreservesAt (ctx : Ctx) : ∀ fuel, DropPreservesAt ctx fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro store value rest store' hown heval
      rw [dropVal.eq_def] at heval
      simp at heval
    · intro store values rest store' hown heval
      rw [dropMany.eq_def] at heval
      simp at heval
  | succ fuel ih =>
    obtain ⟨ihVal, ihMany⟩ := ih
    refine ⟨?_, ?_⟩
    · intro store value rest store' hown heval
      cases value with
      | lit literal =>
        rw [dropVal.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        exact hown.dropNoLocation rfl
      | erased =>
        rw [dropVal.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        exact hown.dropNoLocation rfl
      | loc loc =>
        rw [dropVal.eq_def] at heval
        dsimp only at heval
        cases hget : store.get? loc with
        | none =>
          rw [hget] at heval
          simp at heval
        | some box =>
          rw [hget] at heval
          cases box with
          | mk world rc node =>
            cases world with
            | unique => simp at heval
            | shared =>
              dsimp only at heval
              by_cases hrc : rc = 1
              · subst rc
                have hbeq : ((1 : Nat) == 1) = true := by decide
                rw [hbeq] at heval
                have htickGet :
                    store.rcTick.get? loc = some ⟨.shared, 1, node⟩ := by
                  simpa using hget
                have hkill := (hown.rcTick).killSharedOne htickGet
                cases node with
                | ctorN cid fields =>
                  exact ihMany _ fields.toList rest store' hkill heval
                | papN fn arity args =>
                  exact ihMany _ args.toList rest store' hkill heval
              · have hbeq : (rc == 1) = false := by simp [hrc]
                rw [hbeq] at heval
                have hrcPos : 0 < rc := hown.shared_rc_pos hget
                have hrcMany : 1 < rc := by omega
                injection heval with hstore
                subst store'
                exact hown.dropSharedMany hrcMany hget
    · intro store values rest store' hown heval
      cases values with
      | nil =>
        rw [dropMany.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        simpa [rootsFor] using hown
      | cons value values =>
        rw [dropMany.eq_def] at heval
        dsimp only at heval
        cases hfirst : dropVal ctx fuel store value with
        | error err =>
          rw [hfirst, bindErr] at heval
          simp at heval
        | ok middle =>
          rw [hfirst, bindOk] at heval
          have hfirstOwn :
              RootOwnership store
                (⟨.shared, value⟩ ::
                  (rootsFor .shared values ++ rest)) := by
            simpa [rootsFor] using hown
          have hmiddle :
              RootOwnership middle (rootsFor .shared values ++ rest) :=
            ihVal store value _ middle hfirstOwn hfirst
          exact ihMany middle values rest store' hmiddle heval

/-- Every successful shared drop consumes exactly its input root while
preserving the exact ownership invariant, including recursive rc-zero
reclamation. -/
theorem dropVal_preserves {ctx : Ctx} {fuel : Nat} {store store' : Store}
    {value : RVal} {rest : List Root}
    (hown : RootOwnership store (⟨.shared, value⟩ :: rest))
    (heval : dropVal ctx fuel store value = .ok store') :
    RootOwnership store' rest :=
  (dropPreservesAt ctx fuel).1 store value rest store' hown heval

/-- Successful sequential shared drops consume precisely the corresponding
temporary roots. -/
theorem dropMany_preserves {ctx : Ctx} {fuel : Nat} {store store' : Store}
    {values : List RVal} {rest : List Root}
    (hown : RootOwnership store (rootsFor .shared values ++ rest))
    (heval : dropMany ctx fuel store values = .ok store') :
    RootOwnership store' rest :=
  (dropPreservesAt ctx fuel).2 store values rest store' hown heval

private def DropRestrictsAt (ctx : Ctx) (fuel : Nat) : Prop :=
  (∀ (store : Store) (value : RVal) (store' : Store),
    dropVal ctx fuel store value = .ok store' →
    StoreGraphRestricts store store') ∧
  (∀ (store : Store) (values : List RVal) (store' : Store),
    dropMany ctx fuel store values = .ok store' →
    StoreGraphRestricts store store')

/-- Shared deep drop never changes the world or contents of a node that
survives it. The mutual induction follows the evaluator's recursive child
drop exactly; RC-only and kill steps compose through `StoreGraphRestricts`. -/
private theorem dropRestrictsAt (ctx : Ctx) :
    ∀ fuel, DropRestrictsAt ctx fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro store value store' heval
      rw [dropVal.eq_def] at heval
      simp at heval
    · intro store values store' heval
      rw [dropMany.eq_def] at heval
      simp at heval
  | succ fuel ih =>
    obtain ⟨ihVal, ihMany⟩ := ih
    refine ⟨?_, ?_⟩
    · intro store value store' heval
      cases value with
      | lit literal =>
        rw [dropVal.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        exact StoreGraphRestricts.refl store
      | erased =>
        rw [dropVal.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        exact StoreGraphRestricts.refl store
      | loc loc =>
        rw [dropVal.eq_def] at heval
        dsimp only at heval
        cases hget : store.get? loc with
        | none =>
          rw [hget] at heval
          simp at heval
        | some box =>
          rw [hget] at heval
          cases box with
          | mk world rc node =>
            cases world with
            | unique => simp at heval
            | shared =>
              dsimp only at heval
              by_cases hrc : rc = 1
              · subst rc
                have hbeq : ((1 : Nat) == 1) = true := by decide
                rw [hbeq] at heval
                have htickGet :
                    store.rcTick.get? loc = some ⟨.shared, 1, node⟩ := by
                  simpa using hget
                have hprefix : StoreGraphRestricts store
                    (store.rcTick.kill loc) :=
                  StoreGraphRestricts.trans
                    (StoreGraphRestricts.rcTick store)
                    (StoreGraphRestricts.kill htickGet)
                cases node with
                | ctorN cid fields =>
                  exact StoreGraphRestricts.trans hprefix
                    (ihMany _ fields.toList _ heval)
                | papN fn arity args =>
                  exact StoreGraphRestricts.trans hprefix
                    (ihMany _ args.toList _ heval)
              · have hbeq : (rc == 1) = false := by simp [hrc]
                rw [hbeq] at heval
                injection heval with hstore
                subst store'
                exact StoreGraphRestricts.decRcStore hget
    · intro store values store' heval
      cases values with
      | nil =>
        rw [dropMany.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        exact StoreGraphRestricts.refl store
      | cons value values =>
        rw [dropMany.eq_def] at heval
        dsimp only at heval
        cases hfirst : dropVal ctx fuel store value with
        | error err =>
          rw [hfirst, bindErr] at heval
          simp at heval
        | ok middle =>
          rw [hfirst, bindOk] at heval
          exact StoreGraphRestricts.trans
            (ihVal store value middle hfirst)
            (ihMany middle values store' heval)

theorem dropVal_restricts {ctx : Ctx} {fuel : Nat}
    {store store' : Store} {value : RVal}
    (heval : dropVal ctx fuel store value = .ok store') :
    StoreGraphRestricts store store' :=
  (dropRestrictsAt ctx fuel).1 store value store' heval

theorem dropMany_restricts {ctx : Ctx} {fuel : Nat}
    {store store' : Store} {values : List RVal}
    (heval : dropMany ctx fuel store values = .ok store') :
    StoreGraphRestricts store store' :=
  (dropRestrictsAt ctx fuel).2 store values store' heval

/-- The common prefix of every successful pap application: retain each
stored capture, consume the pap root, and expose the stored and newly supplied
arguments as one owned shared vector. -/
theorem applyGo_preparePap_owned {ctx : Ctx} {fuel : Nat}
    {store dupStore readyStore : Store} {loc rc : Nat}
    {f : Address} {arity : Nat} {got : Array RVal}
    {args : List RVal} {rest : List Root}
    (hget : store.get? loc = some
      ⟨.shared, rc, .papN f arity got⟩)
    (hown : RootOwnership store
      (⟨.shared, .loc loc⟩ :: rootsFor .shared args ++ rest))
    (hdup : dupVals store got.toList = .ok dupStore)
    (hdrop : dropVal ctx fuel dupStore (.loc loc) = .ok readyStore) :
    RootOwnership readyStore
      (rootsFor .shared (got.toList ++ args) ++ rest) := by
  have hgotWorld : ∀ value ∈ got.toList,
      HasWorld store .shared value := by
    intro value hvalue
    exact hown.edges_world hget value (by simpa [nodeChildren] using hvalue)
  have hduped : RootOwnership dupStore
      (rootsFor .shared got.toList ++
        ⟨.shared, .loc loc⟩ :: rootsFor .shared args ++ rest) := by
    simpa [List.append_assoc] using
      dupVals_borrowedMany_preserves hown hgotWorld hdup
  have hpapFirst : RootOwnership dupStore
      (⟨.shared, .loc loc⟩ ::
        rootsFor .shared got.toList ++ rootsFor .shared args ++ rest) := by
    apply hduped.perm
    simpa [List.append_assoc] using
      (List.perm_append_comm
        (l₁ := rootsFor .shared got.toList)
        (l₂ := [(⟨.shared, .loc loc⟩ : Root)])).append_right
          (rootsFor .shared args ++ rest)
  have hready := dropVal_preserves hpapFirst hdrop
  simpa [rootsFor, List.append_assoc] using hready

private def DropUPreservesAt (ctx : Ctx) (fuel : Nat) : Prop :=
  (∀ (store : Store) (value : RVal) (rest : List Root) (store' : Store),
    RootOwnership store (⟨.unique, value⟩ :: rest) →
    dropUVal ctx fuel store value = .ok store' →
    RootOwnership store' rest) ∧
  (∀ (store : Store) (values : List RVal) (rest : List Root)
      (store' : Store),
    RootOwnership store (rootsFor .unique values ++ rest) →
    dropManyU ctx fuel store values = .ok store' →
    RootOwnership store' rest)

private theorem dropUPreservesAt (ctx : Ctx) :
    ∀ fuel, DropUPreservesAt ctx fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro store value rest store' hown heval
      rw [dropUVal.eq_def] at heval
      simp at heval
    · intro store values rest store' hown heval
      rw [dropManyU.eq_def] at heval
      simp at heval
  | succ fuel ih =>
    obtain ⟨ihVal, ihMany⟩ := ih
    refine ⟨?_, ?_⟩
    · intro store value rest store' hown heval
      cases value with
      | lit literal =>
        rw [dropUVal.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        exact hown.dropNoLocation rfl
      | erased =>
        rw [dropUVal.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        exact hown.dropNoLocation rfl
      | loc loc =>
        rw [dropUVal.eq_def] at heval
        dsimp only at heval
        cases hget : store.get? loc with
        | none =>
          rw [hget] at heval
          simp at heval
        | some box =>
          rw [hget] at heval
          cases box with
          | mk world rc node =>
            cases world with
            | shared => simp at heval
            | unique =>
              have hrc : rc = 1 := (hown.counts hget).1
              subst rc
              cases node with
              | ctorN cid fields =>
                have hkill := hown.killUniqueOne hget
                exact ihMany _ fields.toList rest store' hkill heval
              | papN fn arity args => simp at heval
    · intro store values rest store' hown heval
      cases values with
      | nil =>
        rw [dropManyU.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        simpa [rootsFor] using hown
      | cons value values =>
        rw [dropManyU.eq_def] at heval
        dsimp only at heval
        cases hfirst : dropUVal ctx fuel store value with
        | error err =>
          rw [hfirst, bindErr] at heval
          simp at heval
        | ok middle =>
          rw [hfirst, bindOk] at heval
          have hfirstOwn :
              RootOwnership store
                (⟨.unique, value⟩ ::
                  (rootsFor .unique values ++ rest)) := by
            simpa [rootsFor] using hown
          have hmiddle :
              RootOwnership middle (rootsFor .unique values ++ rest) :=
            ihVal store value _ middle hfirstOwn hfirst
          exact ihMany middle values rest store' hmiddle heval

/-- Every successful unique deep drop consumes exactly its affine root and
recursively reclaims its constructor tree without touching refcounts. -/
theorem dropUVal_preserves {ctx : Ctx} {fuel : Nat} {store store' : Store}
    {value : RVal} {rest : List Root}
    (hown : RootOwnership store (⟨.unique, value⟩ :: rest))
    (heval : dropUVal ctx fuel store value = .ok store') :
    RootOwnership store' rest :=
  (dropUPreservesAt ctx fuel).1 store value rest store' hown heval

/-- Successful sequential unique drops consume precisely their temporary
child roots. -/
theorem dropManyU_preserves {ctx : Ctx} {fuel : Nat} {store store' : Store}
    {values : List RVal} {rest : List Root}
    (hown : RootOwnership store (rootsFor .unique values ++ rest))
    (heval : dropManyU ctx fuel store values = .ok store') :
    RootOwnership store' rest :=
  (dropUPreservesAt ctx fuel).2 store values rest store' hown heval

private def DropURestrictsAt (ctx : Ctx) (fuel : Nat) : Prop :=
  (∀ (store : Store) (value : RVal) (store' : Store),
    dropUVal ctx fuel store value = .ok store' →
    StoreGraphRestricts store store') ∧
  (∀ (store : Store) (values : List RVal) (store' : Store),
    dropManyU ctx fuel store values = .ok store' →
    StoreGraphRestricts store store')

/-- Unique deep free likewise only removes nodes; all surviving locations
retain their worlds and node contents. -/
private theorem dropURestrictsAt (ctx : Ctx) :
    ∀ fuel, DropURestrictsAt ctx fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro store value store' heval
      rw [dropUVal.eq_def] at heval
      simp at heval
    · intro store values store' heval
      rw [dropManyU.eq_def] at heval
      simp at heval
  | succ fuel ih =>
    obtain ⟨ihVal, ihMany⟩ := ih
    refine ⟨?_, ?_⟩
    · intro store value store' heval
      cases value with
      | lit literal =>
        rw [dropUVal.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        exact StoreGraphRestricts.refl store
      | erased =>
        rw [dropUVal.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        exact StoreGraphRestricts.refl store
      | loc loc =>
        rw [dropUVal.eq_def] at heval
        dsimp only at heval
        cases hget : store.get? loc with
        | none =>
          rw [hget] at heval
          simp at heval
        | some box =>
          rw [hget] at heval
          cases box with
          | mk world rc node =>
            cases world with
            | shared => simp at heval
            | unique =>
              cases node with
              | ctorN cid fields =>
                have hprefix : StoreGraphRestricts store
                    (store.kill loc) :=
                  StoreGraphRestricts.kill hget
                have htail : StoreGraphRestricts (store.kill loc) store' :=
                  ihMany (store.kill loc) fields.toList store' heval
                intro other survivingWorld survivingRc survivingNode hafter
                obtain ⟨middleRc, hmiddle⟩ := htail hafter
                exact hprefix hmiddle
              | papN fn arity args => simp at heval
    · intro store values store' heval
      cases values with
      | nil =>
        rw [dropManyU.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        exact StoreGraphRestricts.refl store
      | cons value values =>
        rw [dropManyU.eq_def] at heval
        dsimp only at heval
        cases hfirst : dropUVal ctx fuel store value with
        | error err =>
          rw [hfirst, bindErr] at heval
          simp at heval
        | ok middle =>
          rw [hfirst, bindOk] at heval
          exact StoreGraphRestricts.trans
            (ihVal store value middle hfirst)
            (ihMany middle values store' heval)

theorem dropUVal_restricts {ctx : Ctx} {fuel : Nat}
    {store store' : Store} {value : RVal}
    (heval : dropUVal ctx fuel store value = .ok store') :
    StoreGraphRestricts store store' :=
  (dropURestrictsAt ctx fuel).1 store value store' heval

theorem dropManyU_restricts {ctx : Ctx} {fuel : Nat}
    {store store' : Store} {values : List RVal}
    (heval : dropManyU ctx fuel store values = .ok store') :
    StoreGraphRestricts store store' :=
  (dropURestrictsAt ctx fuel).2 store values store' heval

@[simp] theorem edgeLocations_allocNode (store : Store) (world : Owned)
    (node : Node) :
    edgeLocations (store.allocNode world node).1 =
      edgeLocations store ++ (nodeChildren node).filterMap rvalLocation? := by
  simp [edgeLocations, slotEdgeLocations, Store.allocNode, Array.toList_push,
    nodeChildren]

theorem incoming_allocNode_old (store : Store) (world : Owned) (node : Node)
    (rest : List Root) {loc : Nat} (hne : loc ≠ store.nodes.size) :
    incoming (store.allocNode world node).1
        (⟨world, .loc store.nodes.size⟩ :: rest) loc =
      incoming store (rootsFor world (nodeChildren node) ++ rest) loc := by
  simp [incoming, List.filterMap_append, List.count_append,
    rootLocation?, rvalLocation?, Ne.symm hne, Nat.add_assoc, Nat.add_comm]

theorem incoming_allocNode_new (store : Store) (world : Owned) (node : Node)
    (rest : List Root) :
    incoming (store.allocNode world node).1
        (⟨world, .loc store.nodes.size⟩ :: rest) store.nodes.size =
      incoming store (rootsFor world (nodeChildren node) ++ rest)
        store.nodes.size + 1 := by
  simp [incoming, List.filterMap_append, List.count_append,
    rootLocation?, rvalLocation?, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

theorem HasWorld.allocNode {store : Store} {world node rootWorld value}
    (h : HasWorld store rootWorld value) :
    HasWorld (store.allocNode world node).1 rootWorld value := by
  cases value with
  | loc loc =>
    obtain ⟨box, hbox, hworld⟩ := h
    exact ⟨box, HeapIso.get?_allocNode_old hbox, hworld⟩
  | lit l => trivial
  | erased => trivial

theorem HasWorld.allocNode_new (store : Store) (world : Owned) (node : Node) :
    HasWorld (store.allocNode world node).1 world
      (.loc store.nodes.size) := by
  exact ⟨⟨world, 1, node⟩, HeapIso.get?_allocNode_new store world node,
    rfl⟩

/-- Allocation consumes one root for every node child and produces one root
for the fresh node. The exact incoming-owner/refcount equation is preserved. -/
theorem RootOwnership.allocNode {store : Store} {world : Owned} {node : Node}
    {rest : List Root}
    (h : RootOwnership store (rootsFor world (nodeChildren node) ++ rest))
    (hworld : NodeWorld world node) :
    RootOwnership (store.allocNode world node).1
      (⟨world, .loc store.nodes.size⟩ :: rest) := by
  have childWorld : ∀ child ∈ nodeChildren node,
      HasWorld store world child := by
    intro child hchild
    apply h.roots_world ⟨world, child⟩
    apply List.mem_append_left rest
    simp [rootsFor, hchild]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro root hroot
    simp only [List.mem_cons] at hroot
    rcases hroot with rfl | hrest
    · exact HasWorld.allocNode_new store world node
    · apply HasWorld.allocNode
      apply h.roots_world root
      exact List.mem_append_right _ hrest
  · intro loc box hbox child hchild
    by_cases hnew : loc = store.nodes.size
    · subst loc
      have hboxeq : box = ⟨world, 1, node⟩ := by
        exact Option.some.inj
          (hbox.symm.trans (HeapIso.get?_allocNode_new store world node))
      subst box
      exact HasWorld.allocNode (childWorld child hchild)
    · have hold : store.get? loc = some box :=
        HeapIso.get?_of_allocNode_old hnew hbox
      exact HasWorld.allocNode (h.edges_world hold child hchild)
  · intro loc box f arity args hbox hnode
    by_cases hnew : loc = store.nodes.size
    · subst loc
      have hboxeq : box = ⟨world, 1, node⟩ := by
        exact Option.some.inj
          (hbox.symm.trans (HeapIso.get?_allocNode_new store world node))
      subst box
      change node = .papN f arity args at hnode
      cases node <;> simp_all [NodeWorld]
    · have hold : store.get? loc = some box :=
        HeapIso.get?_of_allocNode_old hnew hbox
      exact h.pap_shared hold hnode
  · intro loc box hbox
    by_cases hnew : loc = store.nodes.size
    · subst loc
      have hboxeq : box = ⟨world, 1, node⟩ := by
        exact Option.some.inj
          (hbox.symm.trans (HeapIso.get?_allocNode_new store world node))
      subst box
      have hzero := h.incoming_eq_zero_of_dead (HeapIso.get?_fresh store)
      have hcount := incoming_allocNode_new store world node rest
      rw [hzero] at hcount
      cases world <;> simp_all
    · have hold : store.get? loc = some box :=
        HeapIso.get?_of_allocNode_old hnew hbox
      have hcount := h.counts hold
      rw [incoming_allocNode_old store world node rest hnew]
      exact hcount

/-- The reference meaning of unique reuse: shallow-free the old node, then
append-allocate the replacement. -/
theorem RootOwnership.freeAllocNode {store : Store} {loc : Nat}
    {oldNode newNode : Node} {before after : List Root}
    (hget : store.get? loc = some ⟨.unique, 1, oldNode⟩)
    (h : RootOwnership store (⟨.unique, .loc loc⟩ :: before))
    (hpartition :
      (rootsFor .unique (nodeChildren oldNode) ++ before).Perm
        (rootsFor .unique (nodeChildren newNode) ++ after))
    (hworld : NodeWorld .unique newNode) :
    RootOwnership ((store.kill loc).allocNode .unique newNode).1
      (⟨.unique,
        .loc ((store.kill loc).allocNode .unique newNode).2⟩ :: after) := by
  have hready := (h.killUniqueOne hget).perm hpartition
  exact hready.allocNode hworld

/-- Reference meaning of hot shared reuse: consume the final parent owner,
shallow-free the old node, and freshly allocate the replacement. -/
theorem RootOwnership.freeAllocSharedNode {store : Store} {loc : Nat}
    {oldNode newNode : Node} {before after : List Root}
    (hget : store.get? loc = some ⟨.shared, 1, oldNode⟩)
    (h : RootOwnership store (⟨.shared, .loc loc⟩ :: before))
    (hpartition :
      (rootsFor .shared (nodeChildren oldNode) ++ before).Perm
        (rootsFor .shared (nodeChildren newNode) ++ after))
    (hworld : NodeWorld .shared newNode) :
    RootOwnership ((store.kill loc).allocNode .shared newNode).1
      (⟨.shared,
        .loc ((store.kill loc).allocNode .shared newNode).2⟩ :: after) := by
  have hready := (h.killSharedOne hget).perm hpartition
  exact hready.allocNode hworld

/-- Allocation consumes the resolved field roots and returns ownership of the
fresh constructor root. -/
theorem runOp_alloc_owned {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {world : Owned} {cid : CtorId}
    {args : Array Atom} {values : List RVal} {rest : List Root}
    (hresolve : resolveAtoms env args = .ok values)
    (hown : RootOwnership store (rootsFor world values ++ rest)) :
    runOp ctx (fuel + 1) cur store env (.alloc world cid args) =
        .ok ((store.allocNode world (.ctorN cid values.toArray)).1,
          .loc (store.allocNode world (.ctorN cid values.toArray)).2) ∧
      RootOwnership (store.allocNode world (.ctorN cid values.toArray)).1
        (⟨world,
          .loc (store.allocNode world (.ctorN cid values.toArray)).2⟩ ::
            rest) := by
  refine ⟨runOp_alloc hresolve, ?_⟩
  apply RootOwnership.allocNode
  · simpa [nodeChildren] using hown
  · trivial

/-- Semantic strengthening of constructor allocation. Existing argument
graphs survive the fresh allocation and become the fields of the newly
related constructor root. -/
theorem runOp_alloc_owned_valueGraph
    {funRel : FunctionRel} {sourceValues : List IxIR0.Value}
    {sourceAddress : Address} {sourceTag : Nat}
    {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {world : Owned} {cid : CtorId}
    {args : Array Atom} {values : List RVal} {rest : List Root}
    (hresolve : resolveAtoms env args = .ok values)
    (haddress : cid.block = sourceAddress)
    (htag : cid.cidx = sourceTag)
    (hvalues : ValuesGraph funRel store sourceValues values)
    (hown : RootOwnership store (rootsFor world values ++ rest)) :
    let allocated := store.allocNode world (.ctorN cid values.toArray)
    runOp ctx (fuel + 1) cur store env (.alloc world cid args) =
        .ok (allocated.1, .loc allocated.2) ∧
      StoreGraphExtends store allocated.1 ∧
      ValueGraph funRel allocated.1
        (.ctor sourceAddress sourceTag sourceValues) (.loc allocated.2) ∧
      RootOwnership allocated.1
        (⟨world, .loc allocated.2⟩ :: rest) := by
  dsimp only
  have hop := runOp_alloc_owned (ctx := ctx) (cur := cur)
    (fuel := fuel) (cid := cid) (args := args) (values := values)
    (rest := rest) hresolve hown
  let allocated := store.allocNode world (.ctorN cid values.toArray)
  have hstore : StoreGraphExtends store allocated.1 :=
    StoreGraphExtends.allocNode store world (.ctorN cid values.toArray)
  refine ⟨hop.1, hstore, ?_, hop.2⟩
  apply ValueGraph.ctor
  · exact HeapIso.get?_allocNode_new store world
      (.ctorN cid values.toArray)
  · exact haddress
  · exact htag
  · simpa using hvalues.monoStore hstore

/-- Partial application consumes its shared captured-argument roots and
stores them as the edges of one fresh shared pap node. -/
theorem runOp_papp_owned {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {f : Address} {d : Decl}
    {atoms : Array Atom} {values : List RVal} {rest : List Root}
    (hargs : resolveAtoms env atoms = .ok values)
    (hdecl : ctx.decls f = some d)
    (hunder : values.length < declArity d)
    (hown : RootOwnership store (rootsFor .shared values ++ rest)) :
    runOp ctx (fuel + 1) cur store env (.papp f atoms) =
        .ok ((store.allocNode .shared
          (.papN f (declArity d) values.toArray)).1,
          .loc (store.allocNode .shared
            (.papN f (declArity d) values.toArray)).2) ∧
      RootOwnership
        (store.allocNode .shared
          (.papN f (declArity d) values.toArray)).1
        (⟨.shared, .loc (store.allocNode .shared
          (.papN f (declArity d) values.toArray)).2⟩ :: rest) := by
  constructor
  · rw [runOp.eq_def]
    dsimp only
    rw [hargs, bindOk, hdecl]
    dsimp only
    rw [if_pos hunder]
  · apply RootOwnership.allocNode
    · simpa [nodeChildren] using hown
    · rfl

/-- Semantic strengthening of partial-application allocation. The stored
argument prefix remains graph-related after the fresh allocation, and the
new pap root realizes the supplied source function value through `funRel`. -/
theorem runOp_papp_owned_valueGraph
    {funRel : FunctionRel} {sourceValue : IxIR0.Value}
    {sourceValues : List IxIR0.Value}
    {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {f : Address} {d : Decl}
    {atoms : Array Atom} {values : List RVal} {rest : List Root}
    (hargs : resolveAtoms env atoms = .ok values)
    (hdecl : ctx.decls f = some d)
    (hunder : values.length < declArity d)
    (hfun : funRel sourceValue f (declArity d) sourceValues)
    (hvalues : ValuesGraph funRel store sourceValues values)
    (hown : RootOwnership store (rootsFor .shared values ++ rest)) :
    let allocated := store.allocNode .shared
      (.papN f (declArity d) values.toArray)
    runOp ctx (fuel + 1) cur store env (.papp f atoms) =
        .ok (allocated.1, .loc allocated.2) ∧
      StoreGraphExtends store allocated.1 ∧
      ValueGraph funRel allocated.1 sourceValue (.loc allocated.2) ∧
      RootOwnership allocated.1
        (⟨.shared, .loc allocated.2⟩ :: rest) := by
  dsimp only
  have hop := runOp_papp_owned (ctx := ctx) (cur := cur)
    (fuel := fuel) hargs hdecl hunder hown
  let allocated := store.allocNode .shared
    (.papN f (declArity d) values.toArray)
  have hstore : StoreGraphExtends store allocated.1 :=
    StoreGraphExtends.allocNode store .shared
      (.papN f (declArity d) values.toArray)
  refine ⟨hop.1, hstore, ?_, hop.2⟩
  apply ValueGraph.function
  · exact HeapIso.get?_allocNode_new store .shared
      (.papN f (declArity d) values.toArray)
  · exact hfun
  · simpa using hvalues.monoStore hstore

/-- Exact ownership preservation for one `applyGo` index, assuming all
function declarations and recursive application indices below it are already
available. The proof covers pap under-fill, saturation, and over-application. -/
theorem applyOwnershipPreservesAt_of_papSafeDeclsBelow
    {ctx : Ctx} {limit : Nat}
    (hdecls : PapSafeDeclContractsBelow ctx limit)
    (happly : ApplyOwnershipContractBelow ctx limit) :
    ApplyOwnershipPreservesAt ctx limit := by
  intro store store' function args value rest hown hrun
  cases limit with
  | zero => simp [applyGo] at hrun
  | succ fuel =>
    cases function with
    | lit literal => simp [applyGo] at hrun
    | erased =>
      have hargsOwn : RootOwnership store
          (rootsFor .shared args ++ rest) :=
        hown.dropNoLocation rfl
      simp only [applyGo] at hrun
      cases hdrop : dropMany ctx fuel store args with
      | error err =>
        rw [hdrop, bindErr] at hrun
        contradiction
      | ok dropped =>
        rw [hdrop, bindOk] at hrun
        injection hrun with hpair
        cases hpair
        exact (dropMany_preserves hargsOwn hdrop).addNoLocation rfl
    | loc loc =>
      cases hget : store.get? loc with
      | none => simp [applyGo, hget] at hrun
      | some box =>
        cases box with
        | mk boxWorld rc node =>
          cases node with
          | ctorN cid fields => simp [applyGo, hget] at hrun
          | papN address arity got =>
            have hboxWorld : boxWorld = .shared :=
              hown.pap_shared hget rfl
            subst boxWorld
            simp only [applyGo] at hrun
            rw [hget] at hrun
            dsimp only at hrun
            cases hdup : dupVals store got.toList with
            | error err =>
              rw [hdup, bindErr] at hrun
              contradiction
            | ok dupStore =>
              rw [hdup, bindOk] at hrun
              cases hdrop : dropVal ctx fuel dupStore (.loc loc) with
              | error err =>
                rw [hdrop, bindErr] at hrun
                contradiction
              | ok readyStore =>
                rw [hdrop, bindOk] at hrun
                let total := got.toList ++ args
                have hready : RootOwnership readyStore
                    (rootsFor .shared total ++ rest) := by
                  exact applyGo_preparePap_owned hget hown hdup hdrop
                split at hrun
                next hunder =>
                  injection hrun with hpair
                  cases hpair
                  exact hready.allocNode rfl
                next hnotUnder =>
                  split at hrun
                  next hexact =>
                    cases hdecl : ctx.decls address with
                    | none => simp [hdecl] at hrun
                    | some decl =>
                      cases hpapsafe : declPapSafe decl with
                      | false => simp [hdecl, hpapsafe] at hrun
                      | true =>
                        have hinvoke : invoke ctx fuel address total
                            readyStore = .ok (store', value) := by
                          simpa [hdecl, hpapsafe] using hrun
                        have hsmallDecls :=
                          hdecls.mono (Nat.le_succ fuel)
                        exact invoke_papSafe_owned_below hsmallDecls hdecl
                          hpapsafe hready hinvoke
                  next hover =>
                    cases hdecl : ctx.decls address with
                    | none => simp [hdecl] at hrun
                    | some decl =>
                      cases hpapsafe : declPapSafe decl with
                      | false => simp [hdecl, hpapsafe] at hrun
                      | true =>
                        simp only [hdecl, hpapsafe, if_true] at hrun
                        cases hinvoke : invoke ctx fuel address
                            (total.take arity) readyStore with
                        | error err =>
                          rw [hinvoke, bindErr] at hrun
                          contradiction
                        | ok called =>
                          rcases called with ⟨calledStore, result⟩
                          rw [hinvoke, bindOk] at hrun
                          have hpartition : RootOwnership readyStore
                              (rootsFor .shared (total.take arity) ++
                                (rootsFor .shared (total.drop arity) ++ rest)) := by
                            have hsplit := hready
                            have hrootsSplit : rootsFor .shared total =
                                rootsFor .shared (total.take arity) ++
                                  rootsFor .shared (total.drop arity) := by
                              unfold rootsFor
                              rw [← List.map_append]
                              exact congrArg _
                                (List.take_append_drop arity total).symm
                            rw [hrootsSplit] at hsplit
                            simpa only [List.append_assoc] using hsplit
                          have hsmallDecls := hdecls.mono (Nat.le_succ fuel)
                          have hcalled := invoke_papSafe_owned_below hsmallDecls
                            hdecl hpapsafe hpartition hinvoke
                          exact happly.preserves (Nat.lt_succ_self fuel)
                            hcalled hrun

/-- PAP-safe declaration contracts validate every successful shared PAP entry;
unsafe dynamic targets fail before invocation, while direct calls are
unaffected. -/
theorem applyOwnershipContract_of_papSafeDecls {ctx : Ctx}
    (hdecls : PapSafeDeclContracts ctx) :
    ApplyOwnershipContract ctx := by
  apply applyOwnershipContract_of_below_step
  intro limit happly
  exact applyOwnershipPreservesAt_of_papSafeDeclsBelow
    (hdecls.below limit) happly

theorem runOp_drop_owned {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {target : Atom} {loc : Nat}
    {rest : List Root}
    (hresolve : resolveAtom env target = .ok (.loc loc))
    (heval : dropVal ctx fuel store (.loc loc) = .ok store')
    (hown : RootOwnership store (⟨.shared, .loc loc⟩ :: rest)) :
    runOp ctx (fuel + 1) cur store env (.drop target) =
        .ok (store', .erased) ∧
      RootOwnership store' rest :=
  ⟨runOp_drop hresolve heval, dropVal_preserves hown heval⟩

theorem runOp_dropU_owned {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {target : Atom} {loc : Nat}
    {rest : List Root}
    (hresolve : resolveAtom env target = .ok (.loc loc))
    (heval : dropUVal ctx fuel store (.loc loc) = .ok store')
    (hown : RootOwnership store (⟨.unique, .loc loc⟩ :: rest)) :
    runOp ctx (fuel + 1) cur store env (.dropU target) =
        .ok (store', .erased) ∧
      RootOwnership store' rest :=
  ⟨runOp_dropU hresolve heval, dropUVal_preserves hown heval⟩

/-- A successful shared release of an arbitrary runtime value exposes both
the exact surviving ownership and the reverse heap-shape relation needed to
transport semantic graphs. Scalars leave the store unchanged; locations use
the corresponding deep-drop theorems. -/
theorem runOp_drop_value_owned_restricts {ctx : Ctx} {fuel : Nat}
    {cur : FnDef} {store store' : Store} {env : List RVal}
    {target : Atom} {value result : RVal} {rest : List Root}
    (hresolve : resolveAtom env target = .ok value)
    (hown : RootOwnership store (⟨.shared, value⟩ :: rest))
    (hrun : runOp ctx (fuel + 1) cur store env (.drop target) =
      .ok (store', result)) :
    result = .erased ∧ StoreGraphRestricts store store' ∧
      RootOwnership store' rest := by
  rw [runOp.eq_def] at hrun
  dsimp only at hrun
  rw [hresolve, bindOk] at hrun
  cases value with
  | lit literal =>
    change (Except.ok (store, RVal.erased) :
      Except Err (Store × RVal)) = .ok (store', result) at hrun
    have hpair : (store, RVal.erased) = (store', result) :=
      Except.ok.inj hrun
    cases hpair
    exact ⟨rfl, StoreGraphRestricts.refl store,
      hown.dropNoLocation rfl⟩
  | erased =>
    change (Except.ok (store, RVal.erased) :
      Except Err (Store × RVal)) = .ok (store', result) at hrun
    have hpair : (store, RVal.erased) = (store', result) :=
      Except.ok.inj hrun
    cases hpair
    exact ⟨rfl, StoreGraphRestricts.refl store,
      hown.dropNoLocation rfl⟩
  | loc loc =>
    dsimp only at hrun
    cases hdrop : dropVal ctx fuel store (.loc loc) with
    | error err =>
      rw [hdrop] at hrun
      change (Except.error err : Except Err (Store × RVal)) =
        .ok (store', result) at hrun
      contradiction
    | ok dropped =>
      rw [hdrop] at hrun
      change (Except.ok (dropped, RVal.erased) :
        Except Err (Store × RVal)) = .ok (store', result) at hrun
      have hpair : (dropped, RVal.erased) = (store', result) :=
        Except.ok.inj hrun
      cases hpair
      exact ⟨rfl, dropVal_restricts hdrop,
        dropVal_preserves hown hdrop⟩

/-- Affine destruction has the same semantic store interface as shared
release: it consumes one unique root and only removes heap nodes. -/
theorem runOp_dropU_value_owned_restricts {ctx : Ctx} {fuel : Nat}
    {cur : FnDef} {store store' : Store} {env : List RVal}
    {target : Atom} {value result : RVal} {rest : List Root}
    (hresolve : resolveAtom env target = .ok value)
    (hown : RootOwnership store (⟨.unique, value⟩ :: rest))
    (hrun : runOp ctx (fuel + 1) cur store env (.dropU target) =
      .ok (store', result)) :
    result = .erased ∧ StoreGraphRestricts store store' ∧
      RootOwnership store' rest := by
  rw [runOp.eq_def] at hrun
  dsimp only at hrun
  rw [hresolve, bindOk] at hrun
  cases value with
  | lit literal =>
    change (Except.ok (store, RVal.erased) :
      Except Err (Store × RVal)) = .ok (store', result) at hrun
    have hpair : (store, RVal.erased) = (store', result) :=
      Except.ok.inj hrun
    cases hpair
    exact ⟨rfl, StoreGraphRestricts.refl store,
      hown.dropNoLocation rfl⟩
  | erased =>
    change (Except.ok (store, RVal.erased) :
      Except Err (Store × RVal)) = .ok (store', result) at hrun
    have hpair : (store, RVal.erased) = (store', result) :=
      Except.ok.inj hrun
    cases hpair
    exact ⟨rfl, StoreGraphRestricts.refl store,
      hown.dropNoLocation rfl⟩
  | loc loc =>
    dsimp only at hrun
    cases hdrop : dropUVal ctx fuel store (.loc loc) with
    | error err =>
      rw [hdrop] at hrun
      change (Except.error err : Except Err (Store × RVal)) =
        .ok (store', result) at hrun
      contradiction
    | ok dropped =>
      rw [hdrop] at hrun
      change (Except.ok (dropped, RVal.erased) :
        Except Err (Store × RVal)) = .ok (store', result) at hrun
      have hpair : (dropped, RVal.erased) = (store', result) :=
        Except.ok.inj hrun
      cases hpair
      exact ⟨rfl, dropUVal_restricts hdrop,
        dropUVal_preserves hown hdrop⟩

/-- The live-location bijection used by reuse soundness. The reused target
slot corresponds to the specification's fresh append location; every other
live old location corresponds to itself. -/
def reuseRel (store : Store) (target : Nat) (left right : Nat) : Prop :=
  (left = target ∧ right = store.nodes.size) ∨
  (left = right ∧ left ≠ target ∧
    ∃ box, store.get? left = some box)

private theorem rvalsIso_refl_of_mem {rel : Nat → Nat → Prop} :
    ∀ {values : List RVal},
      (∀ value ∈ values, RValIso rel value value) →
      RValsIso rel values values
  | [], _ => .nil
  | value :: rest, h =>
    .cons (h value (by simp))
      (rvalsIso_refl_of_mem fun child hchild =>
        h child (by simp [hchild]))

/-- In-place reuse and its shallow-free-plus-append-allocation specification
are isomorphic. Exact ownership supplies the critical fact that no surviving
edge can point to the consumed target slot. -/
def HeapIso.reuse {store : Store} {target : Nat} {oldBox : NodeBox}
    {newNode : Node} {rest : List Root}
    (hget : store.get? target = some oldBox)
    (hown : RootOwnership (reuseNodeStore store target newNode)
      (⟨.unique, .loc target⟩ :: rest)) :
    HeapIso (reuseNodeStore store target newNode)
      ((store.kill target).allocNode .unique newNode).1 := by
  let left := reuseNodeStore store target newNode
  let right := ((store.kill target).allocNode .unique newNode).1
  let fresh := store.nodes.size
  have hnew : left.get? target = some ⟨.unique, 1, newNode⟩ := by
    exact get?_reuseNodeStore_same hget
  have nodeSelfIso : ∀ {parent box}, left.get? parent = some box →
      NodeIso (reuseRel store target) box.node box.node := by
    intro parent box hparent
    have childIso : ∀ child ∈ nodeChildren box.node,
        RValIso (reuseRel store target) child child := by
      intro child hchild
      have hworld := hown.edges_world hparent child hchild
      have hneValue := hown.sole_child_ne_unique hnew hparent hchild
      cases child with
      | loc childLoc =>
        obtain ⟨childBox, hchildLive, _⟩ := hworld
        have hne : childLoc ≠ target := by
          intro heq
          subst childLoc
          exact hneValue rfl
        have hold : store.get? childLoc = some childBox :=
          get?_of_reuseNodeStore_other (Ne.symm hne) hget hchildLive
        exact .loc (.inr ⟨rfl, hne, childBox, hold⟩)
      | lit literal => exact .lit
      | erased => exact .erased
    cases hnode : box.node with
    | ctorN cid fields =>
      apply NodeIso.ctor
      apply rvalsIso_refl_of_mem
      intro child hchild
      apply childIso child
      simpa [nodeChildren, hnode] using hchild
    | papN fn arity args =>
      apply NodeIso.pap
      apply rvalsIso_refl_of_mem
      intro child hchild
      apply childIso child
      simpa [nodeChildren, hnode] using hchild
  refine
    { locRel := reuseRel store target
      left_unique := ?_
      right_unique := ?_
      left_total := ?_
      right_total := ?_
      related_live := ?_ }
  · intro loc right₁ right₂ h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact h₁.2.trans h₂.2.symm
    · exact False.elim (h₂.2.1 h₁.1)
    · exact False.elim (h₁.2.1 h₂.1)
    · exact h₁.1.symm.trans h₂.1
  · intro left₁ left₂ loc h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact h₁.1.trans h₂.1.symm
    · obtain ⟨box, hbox⟩ := h₂.2.2
      have heq : left₂ = store.nodes.size := h₂.1.trans h₁.2
      subst left₂
      rw [HeapIso.get?_fresh] at hbox
      contradiction
    · obtain ⟨box, hbox⟩ := h₁.2.2
      have heq : left₁ = store.nodes.size := h₁.1.trans h₂.2
      subst left₁
      rw [HeapIso.get?_fresh] at hbox
      contradiction
    · exact h₁.1.trans h₂.1.symm
  · intro loc box hbox
    by_cases heq : loc = target
    · exact ⟨fresh, .inl ⟨heq, rfl⟩⟩
    · have hold : store.get? loc = some box :=
        get?_of_reuseNodeStore_other (Ne.symm heq) hget hbox
      exact ⟨loc, .inr ⟨rfl, heq, box, hold⟩⟩
  · intro loc box hbox
    by_cases heq : loc = fresh
    · exact ⟨target, .inl ⟨rfl, heq⟩⟩
    · have hnotFresh : loc ≠ (store.kill target).nodes.size := by
        simpa [fresh, Store.kill] using heq
      have hkilled : (store.kill target).get? loc = some box :=
        HeapIso.get?_of_allocNode_old hnotFresh hbox
      have hne : target ≠ loc := by
        intro htarget
        subst loc
        rw [get?_kill_same hget] at hkilled
        contradiction
      have hold : store.get? loc = some box :=
        get?_of_kill_other hne hget hkilled
      exact ⟨loc, .inr ⟨rfl, Ne.symm hne, box, hold⟩⟩
  · intro leftLoc rightLoc hrel
    rcases hrel with hnewRel | holdRel
    · obtain ⟨hleftLoc, hrightLoc⟩ := hnewRel
      subst leftLoc
      subst rightLoc
      refine ⟨⟨.unique, 1, newNode⟩, ⟨.unique, 1, newNode⟩,
        hnew, ?_, ?_⟩
      · have hrightNew := HeapIso.get?_allocNode_new
          (store.kill target) .unique newNode
        change ((store.kill target).allocNode .unique newNode).1.get?
          (store.kill target).nodes.size =
            some ⟨.unique, 1, newNode⟩ at hrightNew
        have hsize : (store.kill target).nodes.size = store.nodes.size := by
          simp [Store.kill]
        rw [hsize] at hrightNew
        exact hrightNew
      · exact ⟨rfl, rfl, nodeSelfIso hnew⟩
    · obtain ⟨rfl, hne, oldLiveBox, hold⟩ := holdRel
      have hleft : left.get? leftLoc = some oldLiveBox :=
        get?_reuseNodeStore_other (Ne.symm hne) hget hold
      have hkilled : (store.kill target).get? leftLoc = some oldLiveBox :=
        get?_kill_other (Ne.symm hne) hget hold
      have hright : right.get? leftLoc = some oldLiveBox :=
        HeapIso.get?_allocNode_old hkilled
      exact ⟨oldLiveBox, oldLiveBox, hleft, hright,
        ⟨rfl, rfl, nodeSelfIso hleft⟩⟩

/-- In-place shared reuse and its shallow-free-plus-append-allocation
specification are isomorphic.  Unit shared ownership excludes every
surviving root and heap edge from the consumed slot, so the reused location
can correspond solely to the specification's fresh location. -/
def HeapIso.reuseShared {store : Store} {target : Nat} {oldBox : NodeBox}
    {newNode : Node} {rest : List Root}
    (hget : store.get? target = some oldBox)
    (hown : RootOwnership (reuseSharedNodeStore store target newNode)
      (⟨.shared, .loc target⟩ :: rest)) :
    HeapIso (reuseSharedNodeStore store target newNode)
      ((store.kill target).allocNode .shared newNode).1 := by
  let left := reuseSharedNodeStore store target newNode
  let right := ((store.kill target).allocNode .shared newNode).1
  let fresh := store.nodes.size
  have hnew : left.get? target = some ⟨.shared, 1, newNode⟩ := by
    exact get?_reuseSharedNodeStore_same hget
  have nodeSelfIso : ∀ {parent box}, left.get? parent = some box →
      NodeIso (reuseRel store target) box.node box.node := by
    intro parent box hparent
    have childIso : ∀ child ∈ nodeChildren box.node,
        RValIso (reuseRel store target) child child := by
      intro child hchild
      have hworld := hown.edges_world hparent child hchild
      have hneValue := hown.sole_child_ne hnew hparent hchild
      cases child with
      | loc childLoc =>
        obtain ⟨childBox, hchildLive, _⟩ := hworld
        have hne : childLoc ≠ target := by
          intro heq
          subst childLoc
          exact hneValue rfl
        have hold : store.get? childLoc = some childBox :=
          get?_of_reuseSharedNodeStore_other (Ne.symm hne) hget hchildLive
        exact .loc (.inr ⟨rfl, hne, childBox, hold⟩)
      | lit literal => exact .lit
      | erased => exact .erased
    cases hnode : box.node with
    | ctorN cid fields =>
      apply NodeIso.ctor
      apply rvalsIso_refl_of_mem
      intro child hchild
      apply childIso child
      simpa [nodeChildren, hnode] using hchild
    | papN fn arity args =>
      apply NodeIso.pap
      apply rvalsIso_refl_of_mem
      intro child hchild
      apply childIso child
      simpa [nodeChildren, hnode] using hchild
  refine
    { locRel := reuseRel store target
      left_unique := ?_
      right_unique := ?_
      left_total := ?_
      right_total := ?_
      related_live := ?_ }
  · intro loc right₁ right₂ h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact h₁.2.trans h₂.2.symm
    · exact False.elim (h₂.2.1 h₁.1)
    · exact False.elim (h₁.2.1 h₂.1)
    · exact h₁.1.symm.trans h₂.1
  · intro left₁ left₂ loc h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact h₁.1.trans h₂.1.symm
    · obtain ⟨box, hbox⟩ := h₂.2.2
      have heq : left₂ = store.nodes.size := h₂.1.trans h₁.2
      subst left₂
      rw [HeapIso.get?_fresh] at hbox
      contradiction
    · obtain ⟨box, hbox⟩ := h₁.2.2
      have heq : left₁ = store.nodes.size := h₁.1.trans h₂.2
      subst left₁
      rw [HeapIso.get?_fresh] at hbox
      contradiction
    · exact h₁.1.trans h₂.1.symm
  · intro loc box hbox
    by_cases heq : loc = target
    · exact ⟨fresh, .inl ⟨heq, rfl⟩⟩
    · have hold : store.get? loc = some box :=
        get?_of_reuseSharedNodeStore_other (Ne.symm heq) hget hbox
      exact ⟨loc, .inr ⟨rfl, heq, box, hold⟩⟩
  · intro loc box hbox
    by_cases heq : loc = fresh
    · exact ⟨target, .inl ⟨rfl, heq⟩⟩
    · have hnotFresh : loc ≠ (store.kill target).nodes.size := by
        simpa [fresh, Store.kill] using heq
      have hkilled : (store.kill target).get? loc = some box :=
        HeapIso.get?_of_allocNode_old hnotFresh hbox
      have hne : target ≠ loc := by
        intro htarget
        subst loc
        rw [get?_kill_same hget] at hkilled
        contradiction
      have hold : store.get? loc = some box :=
        get?_of_kill_other hne hget hkilled
      exact ⟨loc, .inr ⟨rfl, Ne.symm hne, box, hold⟩⟩
  · intro leftLoc rightLoc hrel
    rcases hrel with hnewRel | holdRel
    · obtain ⟨hleftLoc, hrightLoc⟩ := hnewRel
      subst leftLoc
      subst rightLoc
      refine ⟨⟨.shared, 1, newNode⟩, ⟨.shared, 1, newNode⟩,
        hnew, ?_, ?_⟩
      · have hrightNew := HeapIso.get?_allocNode_new
          (store.kill target) .shared newNode
        change ((store.kill target).allocNode .shared newNode).1.get?
          (store.kill target).nodes.size =
            some ⟨.shared, 1, newNode⟩ at hrightNew
        have hsize : (store.kill target).nodes.size = store.nodes.size := by
          simp [Store.kill]
        rw [hsize] at hrightNew
        exact hrightNew
      · exact ⟨rfl, rfl, nodeSelfIso hnew⟩
    · obtain ⟨rfl, hne, oldLiveBox, hold⟩ := holdRel
      have hleft : left.get? leftLoc = some oldLiveBox :=
        get?_reuseSharedNodeStore_other (Ne.symm hne) hget hold
      have hkilled : (store.kill target).get? leftLoc = some oldLiveBox :=
        get?_kill_other (Ne.symm hne) hget hold
      have hright : right.get? leftLoc = some oldLiveBox :=
        HeapIso.get?_allocNode_old hkilled
      exact ⟨oldLiveBox, oldLiveBox, hleft, hright,
        ⟨rfl, rfl, nodeSelfIso hleft⟩⟩

/-- Full unique-reuse soundness. The in-place evaluator transition and the
shallow-free-plus-append-allocation specification both preserve exact
ownership, and their result roots correspond under a live-heap isomorphism.
The partition premise is a root-multiset equation (`List.Perm`): canonical
same-arity FBIP reuse permutes the roots without any common list split. -/
theorem reuse_sound {store : Store} {target : Nat} {oldNode newNode : Node}
    {before after : List Root}
    (hget : store.get? target = some ⟨.unique, 1, oldNode⟩)
    (hown : RootOwnership store (⟨.unique, .loc target⟩ :: before))
    (hpartition :
      (rootsFor .unique (nodeChildren oldNode) ++ before).Perm
        (rootsFor .unique (nodeChildren newNode) ++ after))
    (hworld : NodeWorld .unique newNode) :
    ∃ iso : HeapIso (reuseNodeStore store target newNode)
        ((store.kill target).allocNode .unique newNode).1,
      RootOwnership (reuseNodeStore store target newNode)
          (⟨.unique, .loc target⟩ :: after) ∧
      RootOwnership ((store.kill target).allocNode .unique newNode).1
          (⟨.unique,
            .loc ((store.kill target).allocNode .unique newNode).2⟩ :: after) ∧
      iso.locRel target
        ((store.kill target).allocNode .unique newNode).2 := by
  have hinPlace := hown.reuseNode hget hpartition hworld
  have hreference := hown.freeAllocNode hget hpartition hworld
  let iso := HeapIso.reuse hget hinPlace
  refine ⟨iso, hinPlace, hreference, ?_⟩
  change reuseRel store target target
    ((store.kill target).allocNode .unique newNode).2
  exact .inl ⟨rfl, by simp [Store.kill, Store.allocNode]⟩

/-- Full hot shared-reuse soundness.  Physical in-place replacement and the
logical shallow-free-plus-fresh-allocation path preserve exact ownership,
their result roots correspond, and their live heaps differ only by the
reused-slot/fresh-slot renaming. -/
theorem reuse_shared_sound {store : Store} {target : Nat}
    {oldNode newNode : Node} {before after : List Root}
    (hget : store.get? target = some ⟨.shared, 1, oldNode⟩)
    (hown : RootOwnership store (⟨.shared, .loc target⟩ :: before))
    (hpartition :
      (rootsFor .shared (nodeChildren oldNode) ++ before).Perm
        (rootsFor .shared (nodeChildren newNode) ++ after))
    (hworld : NodeWorld .shared newNode) :
    ∃ iso : HeapIso (reuseSharedNodeStore store target newNode)
        ((store.kill target).allocNode .shared newNode).1,
      RootOwnership (reuseSharedNodeStore store target newNode)
          (⟨.shared, .loc target⟩ :: after) ∧
      RootOwnership ((store.kill target).allocNode .shared newNode).1
          (⟨.shared,
            .loc ((store.kill target).allocNode .shared newNode).2⟩ :: after) ∧
      iso.locRel target
        ((store.kill target).allocNode .shared newNode).2 := by
  have hinPlace := hown.reuseSharedNode hget hpartition hworld
  have hreference := hown.freeAllocSharedNode hget hpartition hworld
  let iso := HeapIso.reuseShared hget hinPlace
  refine ⟨iso, hinPlace, hreference, ?_⟩
  change reuseRel store target target
    ((store.kill target).allocNode .shared newNode).2
  exact .inl ⟨rfl, by simp [Store.kill, Store.allocNode]⟩

/-- The shared-reuse isomorphism self-relates every surviving external root.
This stronger interface lets a caller transport continuations containing old
live locations while mapping only the replaced result to its fresh logical
location. -/
theorem reuse_shared_sound_with_survivors {store : Store} {target : Nat}
    {oldNode newNode : Node} {before after : List Root}
    (hget : store.get? target = some ⟨.shared, 1, oldNode⟩)
    (hown : RootOwnership store (⟨.shared, .loc target⟩ :: before))
    (hpartition :
      (rootsFor .shared (nodeChildren oldNode) ++ before).Perm
        (rootsFor .shared (nodeChildren newNode) ++ after))
    (hworld : NodeWorld .shared newNode) :
    ∃ iso : HeapIso (reuseSharedNodeStore store target newNode)
        ((store.kill target).allocNode .shared newNode).1,
      RootOwnership (reuseSharedNodeStore store target newNode)
          (⟨.shared, .loc target⟩ :: after) ∧
      RootOwnership ((store.kill target).allocNode .shared newNode).1
          (⟨.shared,
            .loc ((store.kill target).allocNode .shared newNode).2⟩ :: after) ∧
      iso.locRel target
        ((store.kill target).allocNode .shared newNode).2 ∧
      ∀ root ∈ after, RValIso iso.locRel root.value root.value := by
  have hinPlace := hown.reuseSharedNode hget hpartition hworld
  have hreference := hown.freeAllocSharedNode hget hpartition hworld
  let iso := HeapIso.reuseShared hget hinPlace
  refine ⟨iso, hinPlace, hreference, ?_, ?_⟩
  · change reuseRel store target target
      ((store.kill target).allocNode .shared newNode).2
    exact .inl ⟨rfl, by simp [Store.kill, Store.allocNode]⟩
  · intro root member
    cases root with
    | mk world value =>
        cases value with
        | lit literal => exact .lit
        | erased => exact .erased
        | loc location =>
            have different : location ≠ target := by
              intro same
              apply hinPlace.sole_root_ne
                (get?_reuseSharedNodeStore_same hget) member
              simp [same]
            obtain ⟨box, live, _⟩ :=
              hinPlace.roots_world ⟨world, .loc location⟩ (by simp [member])
            have oldLive : store.get? location = some box :=
              get?_of_reuseSharedNodeStore_other (Ne.symm different) hget
                live
            apply RValIso.loc
            exact .inr ⟨rfl, different, box, oldLive⟩

/-! Value realization is insensitive to the concrete numbering of live heap
locations. The generated mutual induction principles let these two theorems
recurse through constructor fields and pap captures without adding a depth
index to the semantic relation. -/

theorem ValueGraph.transport {funRel : FunctionRel} {left right : Store}
    (iso : HeapIso left right) {v : IxIR0.Value} {leftVal rightVal : RVal}
    (graph : ValueGraph funRel left v leftVal)
    (valueIso : RValIso iso.locRel leftVal rightVal) :
    ValueGraph funRel right v rightVal := by
  refine ValueGraph.rec
    (motive_1 := fun v leftVal _ => ∀ {rightVal},
      RValIso iso.locRel leftVal rightVal →
      ValueGraph funRel right v rightVal)
    (motive_2 := fun values leftVals _ => ∀ {rightVals},
      RValsIso iso.locRel leftVals rightVals →
      ValuesGraph funRel right values rightVals)
    ?_ ?_ ?_ ?_ ?_ ?_ graph valueIso
  · intro l rightVal hval
    cases hval
    exact .lit
  · intro rightVal hval
    cases hval
    exact .erased
  · intro adr tag args loc world rc cid fields hget hadr htag
      hfields ihFields rightVal hval
    cases hval with
    | loc hloc =>
      obtain ⟨leftBox, rightBox, hleft, hright, hboxes⟩ :=
        iso.related_live hloc
      have hlbox : leftBox = ⟨world, rc, .ctorN cid fields⟩ := by
        exact Option.some.inj (hleft.symm.trans hget)
      subst leftBox
      cases rightBox with
      | mk rightWorld rightRc rightNode =>
        obtain ⟨hworld, hrc, hnode⟩ := hboxes
        change world = rightWorld at hworld
        change rc = rightRc at hrc
        change NodeIso iso.locRel (.ctorN cid fields) rightNode at hnode
        subst rightWorld
        subst rightRc
        cases hnode with
        | ctor hfieldIso =>
          exact .ctor hright hadr htag (ihFields hfieldIso)
  · intro v f arity captures loc rc args hget hfun hargs ihArgs
      rightVal hval
    cases hval with
    | loc hloc =>
      obtain ⟨leftBox, rightBox, hleft, hright, hboxes⟩ :=
        iso.related_live hloc
      have hlbox : leftBox = ⟨.shared, rc, .papN f arity args⟩ := by
        exact Option.some.inj (hleft.symm.trans hget)
      subst leftBox
      cases rightBox with
      | mk rightWorld rightRc rightNode =>
        obtain ⟨hworld, hrc, hnode⟩ := hboxes
        change Owned.shared = rightWorld at hworld
        change rc = rightRc at hrc
        change NodeIso iso.locRel (.papN f arity args) rightNode at hnode
        subst rightWorld
        subst rightRc
        cases hnode with
        | pap hargIso =>
          exact .function hright hfun (ihArgs hargIso)
  · intro rightVals hvals
    cases hvals
    exact .nil
  · intro v rv vs rvs hgraph hgraphs ihGraph ihGraphs rightVals hvals
    cases hvals with
    | cons hval hvals => exact .cons (ihGraph hval) (ihGraphs hvals)

theorem ValuesGraph.transport {funRel : FunctionRel} {left right : Store}
    (iso : HeapIso left right) {values : List IxIR0.Value}
    {leftVals rightVals : List RVal}
    (graphs : ValuesGraph funRel left values leftVals)
    (valuesIso : RValsIso iso.locRel leftVals rightVals) :
    ValuesGraph funRel right values rightVals := by
  refine ValuesGraph.rec
    (motive_1 := fun v leftVal _ => ∀ {rightVal},
      RValIso iso.locRel leftVal rightVal →
      ValueGraph funRel right v rightVal)
    (motive_2 := fun values leftVals _ => ∀ {rightVals},
      RValsIso iso.locRel leftVals rightVals →
      ValuesGraph funRel right values rightVals)
    ?_ ?_ ?_ ?_ ?_ ?_ graphs valuesIso
  · intro l rightVal hval
    cases hval
    exact .lit
  · intro rightVal hval
    cases hval
    exact .erased
  · intro adr tag args loc world rc cid fields hget hadr htag
      hfields ihFields rightVal hval
    cases hval with
    | loc hloc =>
      obtain ⟨leftBox, rightBox, hleft, hright, hboxes⟩ :=
        iso.related_live hloc
      have hlbox : leftBox = ⟨world, rc, .ctorN cid fields⟩ := by
        exact Option.some.inj (hleft.symm.trans hget)
      subst leftBox
      cases rightBox with
      | mk rightWorld rightRc rightNode =>
        obtain ⟨hworld, hrc, hnode⟩ := hboxes
        change world = rightWorld at hworld
        change rc = rightRc at hrc
        change NodeIso iso.locRel (.ctorN cid fields) rightNode at hnode
        subst rightWorld
        subst rightRc
        cases hnode with
        | ctor hfieldIso =>
          exact .ctor hright hadr htag (ihFields hfieldIso)
  · intro v f arity captures loc rc args hget hfun hargs ihArgs
      rightVal hval
    cases hval with
    | loc hloc =>
      obtain ⟨leftBox, rightBox, hleft, hright, hboxes⟩ :=
        iso.related_live hloc
      have hlbox : leftBox = ⟨.shared, rc, .papN f arity args⟩ := by
        exact Option.some.inj (hleft.symm.trans hget)
      subst leftBox
      cases rightBox with
      | mk rightWorld rightRc rightNode =>
        obtain ⟨hworld, hrc, hnode⟩ := hboxes
        change Owned.shared = rightWorld at hworld
        change rc = rightRc at hrc
        change NodeIso iso.locRel (.papN f arity args) rightNode at hnode
        subst rightWorld
        subst rightRc
        cases hnode with
        | pap hargIso =>
          exact .function hright hfun (ihArgs hargIso)
  · intro rightVals hvals
    cases hvals
    exact .nil
  · intro v rv vs rvs hgraph hgraphs ihGraph ihGraphs rightVals hvals
    cases hvals with
    | cons hval hvals => exact .cons (ihGraph hval) (ihGraphs hvals)

/-! ## Primitive proof fixtures

These derivations exercise the theorem API, rather than merely executing the
interpreter. They cover shared alias decrement/reclamation, zero-RC unique
deep-free, and in-place reuse versus a free-plus-allocation heap whose result
location is deliberately different, plus shallow-free and borrow/retain fetch
accounting. -/

private def fixtureNode : Node := .ctorN default #[]

private def fixtureStore : Store :=
  (({} : Store).allocNode .shared fixtureNode).1

private def fixtureLoc : Nat := (({} : Store).allocNode .shared fixtureNode).2

theorem fixture_alloc_owned :
    RootOwnership fixtureStore [⟨.shared, .loc fixtureLoc⟩] := by
  apply RootOwnership.allocNode (store := ({} : Store))
    (world := .shared) (node := fixtureNode) (rest := [])
    RootOwnership.empty
  trivial

theorem fixture_dup_owned :
    RootOwnership
      (incRcStore fixtureStore fixtureLoc ⟨.shared, 1, fixtureNode⟩)
      [⟨.shared, .loc fixtureLoc⟩, ⟨.shared, .loc fixtureLoc⟩] := by
  apply RootOwnership.dup
  · exact HeapIso.get?_allocNode_new ({} : Store) .shared fixtureNode
  · exact fixture_alloc_owned

theorem fixture_drop_owned :
    RootOwnership
      (decRcStore
        (incRcStore fixtureStore fixtureLoc ⟨.shared, 1, fixtureNode⟩)
        fixtureLoc ⟨.shared, 2, fixtureNode⟩)
      [⟨.shared, .loc fixtureLoc⟩] := by
  apply RootOwnership.dropSharedMany (rc := 2) (by omega)
  · exact get?_incRcStore_same
      (HeapIso.get?_allocNode_new ({} : Store) .shared fixtureNode)
  · exact fixture_dup_owned

private def fixtureDupStore : Store :=
  incRcStore fixtureStore fixtureLoc ⟨.shared, 1, fixtureNode⟩

private def fixtureAliasedNode : Node :=
  .ctorN default #[.loc fixtureLoc, .loc fixtureLoc]

private def fixtureAliasedStore : Store :=
  (fixtureDupStore.allocNode .shared fixtureAliasedNode).1

private def fixtureAliasedLoc : Nat :=
  (fixtureDupStore.allocNode .shared fixtureAliasedNode).2

theorem fixture_aliased_alloc_owned :
    RootOwnership fixtureAliasedStore
      [⟨.shared, .loc fixtureAliasedLoc⟩] := by
  unfold fixtureAliasedStore fixtureAliasedLoc
  apply RootOwnership.allocNode (store := fixtureDupStore)
    (world := .shared) (node := fixtureAliasedNode) (rest := [])
  · simpa [fixtureDupStore, fixtureAliasedNode, nodeChildren, rootsFor]
      using fixture_dup_owned
  · trivial

private def fixtureAliasedAfterParent : Store :=
  fixtureAliasedStore.rcTick.kill fixtureAliasedLoc

private def fixtureAliasedAfterFirstChild : Store :=
  decRcStore fixtureAliasedAfterParent fixtureLoc
    ⟨.shared, 2, fixtureNode⟩

private def fixtureAliasedDroppedStore : Store :=
  fixtureAliasedAfterFirstChild.rcTick.kill fixtureLoc

private def fixtureCtx : Ctx := { decls := Env.empty }

private theorem fixture_aliased_parent_get :
    fixtureAliasedStore.get? fixtureAliasedLoc =
      some ⟨.shared, 1, fixtureAliasedNode⟩ := by
  simp [fixtureAliasedStore, fixtureAliasedLoc]

private theorem fixture_aliased_child_after_parent_get :
    fixtureAliasedAfterParent.get? fixtureLoc =
      some ⟨.shared, 2, fixtureNode⟩ := by
  have hleaf : fixtureStore.get? fixtureLoc =
      some ⟨.shared, 1, fixtureNode⟩ :=
    HeapIso.get?_allocNode_new ({} : Store) .shared fixtureNode
  have hdup : fixtureDupStore.get? fixtureLoc =
      some ⟨.shared, 2, fixtureNode⟩ := by
    exact get?_incRcStore_same hleaf
  have hchild : fixtureAliasedStore.get? fixtureLoc =
      some ⟨.shared, 2, fixtureNode⟩ := by
    exact HeapIso.get?_allocNode_old hdup
  have hne : fixtureAliasedLoc ≠ fixtureLoc := by decide
  unfold fixtureAliasedAfterParent
  apply get?_kill_other hne
  · simpa using fixture_aliased_parent_get
  · simpa using hchild

private theorem fixture_aliased_child_after_first_get :
    fixtureAliasedAfterFirstChild.get? fixtureLoc =
      some ⟨.shared, 1, fixtureNode⟩ := by
  exact get?_decRcStore_same fixture_aliased_child_after_parent_get

theorem fixture_aliased_drop_eval :
    dropVal fixtureCtx 8 fixtureAliasedStore (.loc fixtureAliasedLoc) =
      .ok fixtureAliasedDroppedStore := by
  rw [dropVal.eq_def]
  dsimp only
  rw [fixture_aliased_parent_get]
  dsimp only
  have hone : ((1 : Nat) == 1) = true := by decide
  rw [hone]
  change dropMany fixtureCtx 7 fixtureAliasedAfterParent
      [.loc fixtureLoc, .loc fixtureLoc] = .ok fixtureAliasedDroppedStore
  rw [dropMany.eq_def]
  dsimp only
  rw [dropVal.eq_def]
  dsimp only
  rw [fixture_aliased_child_after_parent_get]
  dsimp only
  have htwo : ((2 : Nat) == 1) = false := by decide
  rw [htwo]
  simp only [Bool.false_eq_true, if_false, Nat.reduceSub, bindOk]
  change dropMany fixtureCtx 6 fixtureAliasedAfterFirstChild
      [.loc fixtureLoc] = .ok fixtureAliasedDroppedStore
  rw [dropMany.eq_def]
  dsimp only
  rw [dropVal.eq_def]
  dsimp only
  rw [fixture_aliased_child_after_first_get]
  dsimp only
  rw [hone]
  simp only [if_true, fixtureNode]
  rw [dropMany.eq_def]
  rw [bindOk]
  rw [dropMany.eq_def]
  rfl

theorem fixture_aliased_drop_owned :
    RootOwnership fixtureAliasedDroppedStore [] :=
  dropVal_preserves fixture_aliased_alloc_owned fixture_aliased_drop_eval

theorem fixture_aliased_drop_live_zero :
    fixtureAliasedDroppedStore.live = 0 := by
  rfl

theorem fixture_aliased_drop_counters :
    fixtureAliasedDroppedStore.frees = 2 ∧
      fixtureAliasedDroppedStore.rcops = 4 := by
  constructor <;> rfl

private def fixtureUniqueLeafStore : Store :=
  (({} : Store).allocNode .unique fixtureNode).1

private def fixtureUniqueLeafLoc : Nat :=
  (({} : Store).allocNode .unique fixtureNode).2

theorem fixture_unique_leaf_owned :
    RootOwnership fixtureUniqueLeafStore
      [⟨.unique, .loc fixtureUniqueLeafLoc⟩] := by
  apply RootOwnership.allocNode (store := ({} : Store))
    (world := .unique) (node := fixtureNode) (rest := [])
  · exact RootOwnership.empty
  · trivial

private def fixtureUniqueParentNode : Node :=
  .ctorN default #[.loc fixtureUniqueLeafLoc]

private def fixtureUniqueStore : Store :=
  (fixtureUniqueLeafStore.allocNode .unique fixtureUniqueParentNode).1

private def fixtureUniqueLoc : Nat :=
  (fixtureUniqueLeafStore.allocNode .unique fixtureUniqueParentNode).2

theorem fixture_unique_alloc_owned :
    RootOwnership fixtureUniqueStore
      [⟨.unique, .loc fixtureUniqueLoc⟩] := by
  unfold fixtureUniqueStore fixtureUniqueLoc
  apply RootOwnership.allocNode (store := fixtureUniqueLeafStore)
    (world := .unique) (node := fixtureUniqueParentNode) (rest := [])
  · simpa [fixtureUniqueParentNode, nodeChildren, rootsFor]
      using fixture_unique_leaf_owned
  · trivial

private def fixtureUniqueAfterParent : Store :=
  fixtureUniqueStore.kill fixtureUniqueLoc

private def fixtureUniqueDroppedStore : Store :=
  fixtureUniqueAfterParent.kill fixtureUniqueLeafLoc

private theorem fixture_unique_parent_get :
    fixtureUniqueStore.get? fixtureUniqueLoc =
      some ⟨.unique, 1, fixtureUniqueParentNode⟩ := by
  simp [fixtureUniqueStore, fixtureUniqueLoc]

private theorem fixture_unique_child_after_parent_get :
    fixtureUniqueAfterParent.get? fixtureUniqueLeafLoc =
      some ⟨.unique, 1, fixtureNode⟩ := by
  have hleaf : fixtureUniqueLeafStore.get? fixtureUniqueLeafLoc =
      some ⟨.unique, 1, fixtureNode⟩ := by
    simp [fixtureUniqueLeafStore, fixtureUniqueLeafLoc]
  have hchild : fixtureUniqueStore.get? fixtureUniqueLeafLoc =
      some ⟨.unique, 1, fixtureNode⟩ :=
    HeapIso.get?_allocNode_old hleaf
  have hne : fixtureUniqueLoc ≠ fixtureUniqueLeafLoc := by decide
  unfold fixtureUniqueAfterParent
  exact get?_kill_other hne fixture_unique_parent_get hchild

theorem fixture_unique_drop_eval :
    dropUVal fixtureCtx 6 fixtureUniqueStore (.loc fixtureUniqueLoc) =
      .ok fixtureUniqueDroppedStore := by
  rw [dropUVal.eq_def]
  dsimp only
  rw [fixture_unique_parent_get]
  change dropManyU fixtureCtx 5 fixtureUniqueAfterParent
      [.loc fixtureUniqueLeafLoc] = .ok fixtureUniqueDroppedStore
  rw [dropManyU.eq_def]
  dsimp only
  rw [dropUVal.eq_def]
  dsimp only
  rw [fixture_unique_child_after_parent_get]
  simp only [fixtureNode]
  rw [dropManyU.eq_def]
  rw [bindOk]
  rw [dropManyU.eq_def]
  rfl

theorem fixture_unique_drop_owned :
    RootOwnership fixtureUniqueDroppedStore [] :=
  dropUVal_preserves fixture_unique_alloc_owned fixture_unique_drop_eval

theorem fixture_unique_drop_live_zero :
    fixtureUniqueDroppedStore.live = 0 := by
  rfl

theorem fixture_unique_drop_counters :
    fixtureUniqueDroppedStore.frees = 2 ∧
      fixtureUniqueDroppedStore.rcops = 0 := by
  constructor <;> rfl

private def fixtureReuseCid : CtorId :=
  { block := default, indIdx := 0, cidx := 1 }

private def fixtureReuseNode : Node :=
  .ctorN fixtureReuseCid #[.loc fixtureUniqueLeafLoc]

private def fixtureReuseStore : Store :=
  reuseNodeStore fixtureUniqueStore fixtureUniqueLoc fixtureReuseNode

private def fixtureReuseSpec : Store :=
  ((fixtureUniqueStore.kill fixtureUniqueLoc).allocNode
    .unique fixtureReuseNode).1

private def fixtureReuseFresh : Nat :=
  ((fixtureUniqueStore.kill fixtureUniqueLoc).allocNode
    .unique fixtureReuseNode).2

theorem fixture_reuse_sound :
    ∃ iso : HeapIso fixtureReuseStore fixtureReuseSpec,
      RootOwnership fixtureReuseStore
          [⟨.unique, .loc fixtureUniqueLoc⟩] ∧
      RootOwnership fixtureReuseSpec
          [⟨.unique, .loc fixtureReuseFresh⟩] ∧
      iso.locRel fixtureUniqueLoc fixtureReuseFresh := by
  simpa [fixtureReuseStore, fixtureReuseSpec, fixtureReuseFresh] using
    (reuse_sound
      (hget := fixture_unique_parent_get)
      (hown := fixture_unique_alloc_owned)
      (hpartition := .of_eq (by rfl))
      (hworld := by
        trivial)
      (newNode := fixtureReuseNode)
      (before := []) (after := []))

theorem fixture_reuse_locations_differ :
    fixtureUniqueLoc ≠ fixtureReuseFresh := by
  decide

theorem fixture_reuse_costs_excluded_from_iso :
    fixtureReuseStore.allocs = 2 ∧
      fixtureReuseStore.reuses = 1 ∧
      fixtureReuseStore.frees = 0 ∧
      fixtureReuseSpec.allocs = 3 ∧
      fixtureReuseSpec.reuses = 0 ∧
      fixtureReuseSpec.frees = 1 := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

/-! Same-arity field-replacement reuse — the list-reverse shape.
`Cons(x, xs)` is reused in place as `Cons(x, acc)`: the consumed roots are
the old fields `{x, xs}` plus the ambient accumulator root `acc`, and the
supplied roots are the new fields `{x, acc}` plus the leftover `xs`. The
partition is a genuine non-identity permutation — the `#guard`s below check
executably that the two root lists are unequal yet multiset-equal, so the
old equality-shaped premise was uninstantiable here. -/

private def fixtureSwapAccStore : Store :=
  (({} : Store).allocNode .unique fixtureNode).1

private def fixtureSwapAccLoc : Nat :=
  (({} : Store).allocNode .unique fixtureNode).2

private def fixtureSwapXsStore : Store :=
  (fixtureSwapAccStore.allocNode .unique fixtureNode).1

private def fixtureSwapXsLoc : Nat :=
  (fixtureSwapAccStore.allocNode .unique fixtureNode).2

private def fixtureSwapXStore : Store :=
  (fixtureSwapXsStore.allocNode .unique fixtureNode).1

private def fixtureSwapXLoc : Nat :=
  (fixtureSwapXsStore.allocNode .unique fixtureNode).2

/-- The reused cell `Cons(x, xs)`. -/
private def fixtureSwapOldNode : Node :=
  .ctorN fixtureReuseCid #[.loc fixtureSwapXLoc, .loc fixtureSwapXsLoc]

/-- Its replacement `Cons(x, acc)` — same arity, second field swapped. -/
private def fixtureSwapNewNode : Node :=
  .ctorN fixtureReuseCid #[.loc fixtureSwapXLoc, .loc fixtureSwapAccLoc]

private def fixtureSwapStore : Store :=
  (fixtureSwapXStore.allocNode .unique fixtureSwapOldNode).1

private def fixtureSwapLoc : Nat :=
  (fixtureSwapXStore.allocNode .unique fixtureSwapOldNode).2

private def fixtureSwapBefore : List Root :=
  [⟨.unique, .loc fixtureSwapAccLoc⟩]

private def fixtureSwapAfter : List Root :=
  [⟨.unique, .loc fixtureSwapXsLoc⟩]

-- Unequal as lists (no before/after split can equate them)…
#guard ((rootsFor .unique (nodeChildren fixtureSwapOldNode) ++
    fixtureSwapBefore) ==
  (rootsFor .unique (nodeChildren fixtureSwapNewNode) ++
    fixtureSwapAfter)) == false

-- …but equal as root multisets: exactly the permutation premise.
#guard (rootsFor .unique (nodeChildren fixtureSwapOldNode) ++
    fixtureSwapBefore).isPerm
  (rootsFor .unique (nodeChildren fixtureSwapNewNode) ++
    fixtureSwapAfter)

private theorem fixture_swap_acc_owned :
    RootOwnership fixtureSwapAccStore
      [⟨.unique, .loc fixtureSwapAccLoc⟩] := by
  unfold fixtureSwapAccStore fixtureSwapAccLoc
  apply RootOwnership.allocNode (store := ({} : Store))
    (world := .unique) (node := fixtureNode) (rest := [])
  · exact RootOwnership.empty
  · trivial

private theorem fixture_swap_xs_owned :
    RootOwnership fixtureSwapXsStore
      [⟨.unique, .loc fixtureSwapXsLoc⟩,
       ⟨.unique, .loc fixtureSwapAccLoc⟩] := by
  unfold fixtureSwapXsStore fixtureSwapXsLoc
  apply RootOwnership.allocNode (store := fixtureSwapAccStore)
    (world := .unique) (node := fixtureNode)
    (rest := [⟨.unique, .loc fixtureSwapAccLoc⟩])
  · simpa [fixtureNode, nodeChildren, rootsFor] using fixture_swap_acc_owned
  · trivial

private theorem fixture_swap_x_owned :
    RootOwnership fixtureSwapXStore
      [⟨.unique, .loc fixtureSwapXLoc⟩,
       ⟨.unique, .loc fixtureSwapXsLoc⟩,
       ⟨.unique, .loc fixtureSwapAccLoc⟩] := by
  unfold fixtureSwapXStore fixtureSwapXLoc
  apply RootOwnership.allocNode (store := fixtureSwapXsStore)
    (world := .unique) (node := fixtureNode)
    (rest := [⟨.unique, .loc fixtureSwapXsLoc⟩,
              ⟨.unique, .loc fixtureSwapAccLoc⟩])
  · simpa [fixtureNode, nodeChildren, rootsFor] using fixture_swap_xs_owned
  · trivial

private theorem fixture_swap_alloc_owned :
    RootOwnership fixtureSwapStore
      (⟨.unique, .loc fixtureSwapLoc⟩ :: fixtureSwapBefore) := by
  unfold fixtureSwapStore fixtureSwapLoc fixtureSwapBefore
  apply RootOwnership.allocNode (store := fixtureSwapXStore)
    (world := .unique) (node := fixtureSwapOldNode)
    (rest := [⟨.unique, .loc fixtureSwapAccLoc⟩])
  · simpa [fixtureSwapOldNode, nodeChildren, rootsFor] using
      fixture_swap_x_owned
  · trivial

private theorem fixture_swap_parent_get :
    fixtureSwapStore.get? fixtureSwapLoc =
      some ⟨.unique, 1, fixtureSwapOldNode⟩ :=
  HeapIso.get?_allocNode_new fixtureSwapXStore .unique fixtureSwapOldNode

/-- The old field roots plus `acc` permute (cons of a transposition —
not an equality) to the new field roots plus `xs`. -/
private theorem fixture_swap_partition :
    (rootsFor .unique (nodeChildren fixtureSwapOldNode) ++
        fixtureSwapBefore).Perm
      (rootsFor .unique (nodeChildren fixtureSwapNewNode) ++
        fixtureSwapAfter) := by
  show List.Perm
    ([⟨.unique, .loc fixtureSwapXLoc⟩, ⟨.unique, .loc fixtureSwapXsLoc⟩,
      ⟨.unique, .loc fixtureSwapAccLoc⟩] : List Root)
    ([⟨.unique, .loc fixtureSwapXLoc⟩, ⟨.unique, .loc fixtureSwapAccLoc⟩,
      ⟨.unique, .loc fixtureSwapXsLoc⟩] : List Root)
  exact .cons _ (.swap _ _ _)

private def fixtureSwapReuseStore : Store :=
  reuseNodeStore fixtureSwapStore fixtureSwapLoc fixtureSwapNewNode

private def fixtureSwapReuseSpec : Store :=
  ((fixtureSwapStore.kill fixtureSwapLoc).allocNode
    .unique fixtureSwapNewNode).1

private def fixtureSwapReuseFresh : Nat :=
  ((fixtureSwapStore.kill fixtureSwapLoc).allocNode
    .unique fixtureSwapNewNode).2

/-- `reuse_sound` applied across a genuinely permuted partition: in-place
reuse keeps `xs` alive as the leftover root while `acc` becomes the new
second field, and both runs stay exactly owned and isomorphic. -/
theorem fixture_swap_reuse_sound :
    ∃ iso : HeapIso fixtureSwapReuseStore fixtureSwapReuseSpec,
      RootOwnership fixtureSwapReuseStore
          (⟨.unique, .loc fixtureSwapLoc⟩ :: fixtureSwapAfter) ∧
      RootOwnership fixtureSwapReuseSpec
          (⟨.unique, .loc fixtureSwapReuseFresh⟩ :: fixtureSwapAfter) ∧
      iso.locRel fixtureSwapLoc fixtureSwapReuseFresh := by
  simpa [fixtureSwapReuseStore, fixtureSwapReuseSpec,
    fixtureSwapReuseFresh] using
    (reuse_sound
      (hget := fixture_swap_parent_get)
      (hown := fixture_swap_alloc_owned)
      (hpartition := fixture_swap_partition)
      (hworld := by trivial)
      (newNode := fixtureSwapNewNode)
      (before := fixtureSwapBefore) (after := fixtureSwapAfter))

private def fixtureCur : FnDef :=
  { arity := 0, result := .shared, papSafe := false, body := .ret .erased }

private def fixtureIdAddr : Address := default

private def fixtureIdFn : FnDef :=
  { arity := 1, result := .unique, papSafe := false, body := .ret (.var 0) }

private def fixtureIdCtx : Ctx :=
  { decls := fun a =>
      if a = fixtureIdAddr then some (.fn fixtureIdFn) else none }

/-- A one-argument identity demonstrates a non-circular function contract:
the unique argument root becomes the unique result root without changing the
store or unrelated roots. -/
theorem fixture_id_contract :
    FnOwnershipContract fixtureIdCtx fixtureIdFn [.unique] := by
  refine ⟨rfl, ?_⟩
  intro fuel store store' args value rest hlength hown hrun
  cases args with
  | nil => simp at hlength
  | cons arg tail =>
    cases tail with
    | cons arg' tail => simp at hlength
    | nil =>
      cases fuel with
      | zero => simp [runCode] at hrun
      | succ fuel =>
        rw [runCode.eq_def] at hrun
        change (Except.ok (store, arg) : Except Err (Store × RVal)) =
          Except.ok (store', value) at hrun
        have hpair : (store, arg) = (store', value) :=
          Except.ok.inj hrun
        cases hpair
        simpa [fixtureIdFn, rootsForWorlds] using hown

theorem fixture_call_eval :
    runOp fixtureIdCtx 3 fixtureCur fixtureUniqueStore
        [.loc fixtureUniqueLoc] (.call fixtureIdAddr #[.var 0]) =
      .ok (fixtureUniqueStore, .loc fixtureUniqueLoc) := by
  rw [runOp.eq_def]
  dsimp only
  rw [show resolveAtoms [.loc fixtureUniqueLoc] #[.var 0] =
    .ok [.loc fixtureUniqueLoc] by rfl, bindOk]
  rw [invoke.eq_def]
  dsimp only
  rw [show fixtureIdCtx.decls fixtureIdAddr = some (.fn fixtureIdFn) by
    simp [fixtureIdCtx]]
  dsimp only [fixtureIdFn]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
  have harity : ¬ (((1 : Nat) != 1) = true) := by decide
  rw [if_neg harity]
  rw [runCode.eq_def]
  dsimp only
  rw [show resolveAtom [.loc fixtureUniqueLoc].reverse (.var 0) =
    .ok (.loc fixtureUniqueLoc) by rfl, bindOk]
  rw [bindOk]
  unfold checkResultWorld RVal.hasWorld
  dsimp only
  have hworld : ((Owned.unique == Owned.unique) = true) := by decide
  simp [fixture_unique_parent_get, hworld]

theorem fixture_call_owned :
    RootOwnership fixtureUniqueStore
      [⟨.unique, .loc fixtureUniqueLoc⟩] := by
  exact runOp_call_owned
    (ctx := fixtureIdCtx) (fuel := 2) (cur := fixtureCur)
    (store := fixtureUniqueStore) (store' := fixtureUniqueStore)
    (env := [.loc fixtureUniqueLoc]) (f := fixtureIdAddr)
    (atoms := #[.var 0]) (args := [.loc fixtureUniqueLoc])
    (value := .loc fixtureUniqueLoc) (d := fixtureIdFn)
    (argWorlds := [.unique]) (rest := [])
    (by rfl)
    (by simp [fixtureIdCtx])
    fixture_id_contract
    (by simpa [rootsForWorlds] using fixture_unique_alloc_owned)
    fixture_call_eval

theorem fixture_free_eval :
    runOp fixtureCtx 1 fixtureCur fixtureUniqueStore
        [.loc fixtureUniqueLoc] (.free (.var 0)) =
      .ok (fixtureUniqueStore.kill fixtureUniqueLoc, .erased) := by
  apply runOp_free
  · rfl
  · exact fixture_unique_parent_get

theorem fixture_free_owned :
    RootOwnership (fixtureUniqueStore.kill fixtureUniqueLoc)
      [⟨.unique, .loc fixtureUniqueLeafLoc⟩] := by
  have hfree :=
    fixture_unique_alloc_owned.killUniqueOne fixture_unique_parent_get
  simpa [fixtureUniqueParentNode, nodeChildren, rootsFor] using hfree

private def fixtureCaseBody : Code :=
  .letOp (.free (.var 1)) (.ret (.var 1))

private def fixtureCaseAlts : Array Alt :=
  #[.mk 0 1 fixtureCaseBody]

private def fixtureCaseCode : Code :=
  .case (.var 0) false fixtureCaseAlts

private def fixtureCaseCur : FnDef :=
  { arity := 0, result := .unique, papSafe := false, body := fixtureCaseCode }

theorem fixture_case_field_borrowed :
    HasWorld fixtureUniqueStore .unique (.loc fixtureUniqueLeafLoc) := by
  apply fixture_unique_alloc_owned.caseFieldsBorrowed
    (loc := fixtureUniqueLoc) (rc := 1) (cid := default)
    (fields := #[.loc fixtureUniqueLeafLoc])
  · simpa [fixtureUniqueParentNode] using fixture_unique_parent_get
  · simp

/-- The case fixture enters with a borrowed child, shallow-frees the unique
scrutinee, and returns that child as the sole unique root. -/
theorem fixture_case_eval :
    runCode fixtureCtx 3 fixtureCaseCur fixtureUniqueStore
        [.loc fixtureUniqueLoc] fixtureCaseCode =
      .ok (fixtureUniqueStore.kill fixtureUniqueLoc,
        .loc fixtureUniqueLeafLoc) := by
  unfold fixtureCaseCode
  rw [runCode_case_ctor
    (hresolve := by rfl)
    (hget := by
      simpa [fixtureUniqueParentNode] using fixture_unique_parent_get)
    (halt := by rfl) (hsize := by rfl)]
  change runCode fixtureCtx 2 fixtureCaseCur fixtureUniqueStore
    [.loc fixtureUniqueLeafLoc, .loc fixtureUniqueLoc] fixtureCaseBody =
      .ok (fixtureUniqueStore.kill fixtureUniqueLoc,
        .loc fixtureUniqueLeafLoc)
  unfold fixtureCaseBody
  rw [runCode.eq_def]
  dsimp only
  rw [runOp_free (hresolve := by rfl) fixture_unique_parent_get]
  rw [bindOk]
  rw [runCode.eq_def]
  rfl

theorem fixture_case_owned :
    RootOwnership (fixtureUniqueStore.kill fixtureUniqueLoc)
      [⟨.unique, .loc fixtureUniqueLeafLoc⟩] := by
  apply runCode_case_ctor_owned
    (ctx := fixtureCtx) (fuel := 2) (cur := fixtureCaseCur)
    (store := fixtureUniqueStore)
    (store' := fixtureUniqueStore.kill fixtureUniqueLoc)
    (env := [.loc fixtureUniqueLoc]) (scrut := .var 0)
    (peelNat := false) (alts := fixtureCaseAlts)
    (loc := fixtureUniqueLoc) (rc := 1) (world := .unique)
    (cid := default) (fields := #[.loc fixtureUniqueLeafLoc])
    (tag := 0) (nf := 1) (body := fixtureCaseBody)
    (value := .loc fixtureUniqueLeafLoc)
    (roots := [⟨.unique, .loc fixtureUniqueLoc⟩]) (rest := [])
  · rfl
  · simpa [fixtureUniqueParentNode] using fixture_unique_parent_get
  · rfl
  · rfl
  · exact fixture_unique_alloc_owned
  · intro _ _ _
    simpa [fixtureCaseCur] using fixture_free_owned
  · exact fixture_case_eval

private def fixtureNatBody : Code := .ret (.var 0)

private def fixtureNatAlts : Array Alt :=
  #[.mk 0 0 (.ret .erased), .mk 1 1 fixtureNatBody]

private def fixtureNatCode : Code :=
  .case (.var 0) true fixtureNatAlts

private def fixtureNatCur : FnDef :=
  { arity := 0, result := .shared, papSafe := false, body := fixtureNatCode }

theorem fixture_nat_case_eval :
    runCode fixtureCtx 2 fixtureNatCur ({} : Store)
        [.lit (.nat 2)] fixtureNatCode =
      .ok (({} : Store), .lit (.nat 1)) := by
  unfold fixtureNatCode
  rw [runCode_case_nat_succ (n := 1)
    (hresolve := by rfl) (halt := by rfl)]
  unfold fixtureNatBody
  rw [runCode.eq_def]
  rfl

theorem fixture_nat_case_owned :
    RootOwnership ({} : Store) [⟨.shared, .lit (.nat 1)⟩] := by
  apply runCode_case_nat_succ_owned
    (ctx := fixtureCtx) (fuel := 1) (cur := fixtureNatCur)
    (store := ({} : Store)) (store' := ({} : Store))
    (env := [.lit (.nat 2)]) (scrut := .var 0)
    (alts := fixtureNatAlts) (n := 1) (tag := 1)
    (body := fixtureNatBody) (value := .lit (.nat 1))
    (roots := []) (rest := [])
  · rfl
  · rfl
  · exact RootOwnership.empty
  · intro _ _
    exact RootOwnership.empty.addNoLocation (world := .shared) (by rfl)
  · exact fixture_nat_case_eval

private theorem fixture_aliased_child_get :
    fixtureAliasedStore.get? fixtureLoc =
      some ⟨.shared, 2, fixtureNode⟩ := by
  have hleaf : fixtureStore.get? fixtureLoc =
      some ⟨.shared, 1, fixtureNode⟩ :=
    HeapIso.get?_allocNode_new ({} : Store) .shared fixtureNode
  have hdup : fixtureDupStore.get? fixtureLoc =
      some ⟨.shared, 2, fixtureNode⟩ :=
    get?_incRcStore_same hleaf
  exact HeapIso.get?_allocNode_old hdup

theorem fixture_fetch_eval :
    runOp fixtureCtx 1 fixtureCur fixtureAliasedStore
        [.loc fixtureAliasedLoc] (.fetch (.var 0) 0) =
      .ok (fixtureAliasedStore, .loc fixtureLoc) := by
  apply runOp_fetch
  · rfl
  · exact fixture_aliased_parent_get
  · rfl

private def fixtureFetchRetainedStore : Store :=
  incRcStore fixtureAliasedStore fixtureLoc
    ⟨.shared, 2, fixtureNode⟩

theorem fixture_fetch_dup_eval :
    dupVals fixtureAliasedStore [.loc fixtureLoc] =
      .ok fixtureFetchRetainedStore := by
  exact dupVals_single fixture_aliased_child_get

theorem fixture_fetch_dup_owned :
    RootOwnership fixtureFetchRetainedStore
      [⟨.shared, .loc fixtureLoc⟩,
        ⟨.shared, .loc fixtureAliasedLoc⟩] := by
  apply fetch_dupVals_preserves
    (hget := fixture_aliased_parent_get) (i := 0)
  · rfl
  · exact fixture_aliased_alloc_owned
  · exact fixture_fetch_dup_eval

theorem fixture_fetch_dup_rc :
    fixtureFetchRetainedStore.get? fixtureLoc =
      some ⟨.shared, 3, fixtureNode⟩ :=
  get?_incRcStore_same fixture_aliased_child_get

end Ix.Compiler.IxIR1.Sim
