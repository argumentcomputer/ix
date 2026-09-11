import Ix.Compiler.IxIR1.NoReuse
import Ix.Compiler.IxIR2.Eval
import Ix.Compiler.IxIR2.Lower

/-!
# Compositional simulation interface for structured lowering

This file fixes the theorem shape before the proof is scaled over every
instruction. Its foundation packages source allocation order and bounded
roots into a no-reuse-preserved recursive runtime invariant, and uses partial
source-slot maps so ownership-dead
bindings cannot resolve across a CFG edge, discharges scalar and vector
operand resolution, extends or safely forgets related environments across
value and erased bindings, establishes canonical call-entry environments,
derives canonical successor environments from actual generated-edge operand
resolution (including implicit scalar prefixes),
and closes the public small-step cases for IxIR₁ `pure`/IxIR₂ `move`, exact
ordinary constructor allocation, scalar and heap-bearing shared-retain paths,
scalar and fully recursive shared-release paths, scalar unique drop, checked
scalar-leaf unique free, general recursive unique destruction, checked
non-consuming projection, exact function-PAP allocation, direct/self call
entry with exact source call equations, tail entry with its source-shell
equations, constructor/Nat branch composition, under-saturated PAP extension,
exact/over-saturated PAP callee entry, return-time `applyMore` redispatch, and
both resumed and outermost returns.
-/

namespace Ix.Compiler.IxIR2.Lower.Sim

open Ix.Compiler.IxIR2

abbrev RVal := IxIR1.RVal

/-- The structured baseline executes against exactly the IxIR₁ heap and
does not exercise any reset/reuse-credit counters.  Peak-live accounting is a
target-only observation and is intentionally omitted. -/
structure StoreRel (source : IxIR1.Store) (target : Eval.Store) : Prop where
  heap : target.heap = source
  resetAttempts : target.resetAttempts = 0
  hotResets : target.hotResets = 0
  coldResets : target.coldResets = 0
  reusedPayloadUnits : target.reusedPayloadUnits = 0

/-- Fresh source and target stores satisfy the exact baseline relation. -/
theorem StoreRel.initial :
    StoreRel ({} : IxIR1.Store) ({} : Eval.Store) := by
  constructor <;> rfl

/-- Exact baseline heap correspondence transports the source propositional
world predicate to the target evaluator's executable world check. -/
theorem StoreRel.hasWorld_eq_true_iff {source : IxIR1.Store}
    {target : Eval.Store} (relation : StoreRel source target)
    {world : Ix.Compiler.Ixon.Owned} {value : RVal} :
    Eval.RVal.hasWorld target world value = true ↔
      IxIR1.Sim.HasWorld source world value := by
  cases value with
  | lit literal => simp [Eval.RVal.hasWorld, IxIR1.Sim.HasWorld]
  | erased => simp [Eval.RVal.hasWorld, IxIR1.Sim.HasWorld]
  | loc location =>
      simp only [Eval.RVal.hasWorld, Eval.Store.get?, relation.heap,
        IxIR1.Sim.HasWorld]
      cases found : source.get? location with
      | none => simp
      | some box => simp [beq_iff_eq]

/-- Uniform source-world evidence discharges the target allocation check for
the uniform baseline schema carried by the pipeline. -/
theorem StoreRel.fieldWorlds_replicate {source : IxIR1.Store}
    {target : Eval.Store} (relation : StoreRel source target)
    {schema : CtorSchema} {values : Array RVal}
    {world : Ix.Compiler.Ixon.Owned} {count : Nat}
    (schemaFields : schema.fields = Array.replicate count world)
    (valueCount : values.size = count)
    (worlds : ∀ value ∈ values.toList,
      IxIR1.Sim.HasWorld source world value) :
    Eval.FieldWorlds target schema values := by
  apply Eval.FieldWorlds.of_replicate schemaFields valueCount
  intro value member
  exact relation.hasWorld_eq_true_iff.mpr (worlds value member)

/-- Exact source ownership of the values consumed into a constructor is a
direct sufficient premise for the target's uniform-schema field check. -/
theorem StoreRel.fieldWorlds_replicate_of_ownership
    {source : IxIR1.Store} {target : Eval.Store}
    (relation : StoreRel source target)
    {schema : CtorSchema} {values : Array RVal}
    {world : Ix.Compiler.Ixon.Owned} {count : Nat}
    {rest : List IxIR1.Sim.Root}
    (schemaFields : schema.fields = Array.replicate count world)
    (valueCount : values.size = count)
    (ownership : IxIR1.Sim.RootOwnership source
      (IxIR1.Sim.rootsFor world values.toList ++ rest)) :
    Eval.FieldWorlds target schema values := by
  apply relation.fieldWorlds_replicate schemaFields valueCount
  intro value member
  apply ownership.roots_world ⟨world, value⟩
  apply List.mem_append_left
  rw [IxIR1.Sim.rootsFor, List.mem_map]
  exact ⟨value, member, rfl⟩

/-- A checked lowering supplies the exact uniform schema and operand arity at
one retained source allocation. Combined with source root ownership, this
discharges the target evaluator's entire `FieldWorlds` premise. -/
theorem StoreRel.fieldWorlds_of_checked_allocation
    {checked : Lower.Checked} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {world : Ix.Compiler.Ixon.Owned} {identity : CtorId}
    {sourceArguments : Array IxIR1.Atom} {instruction : Instr}
    {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.alloc world identity sourceArguments) index instruction next))
    {sourceStore : IxIR1.Store} {targetStore : Eval.Store}
    (relation : StoreRel sourceStore targetStore)
    {source : List RVal} {values : List RVal} {schema : CtorSchema}
    (resolved : IxIR1.resolveAtoms source sourceArguments = .ok values)
    (schemaAt : checked.artifact.validationContext.schemas world identity =
      some schema)
    {rest : List IxIR1.Sim.Root}
    (ownership : IxIR1.Sim.RootOwnership sourceStore
      (IxIR1.Sim.rootsFor world values ++ rest)) :
    Eval.FieldWorlds targetStore schema values.toArray := by
  apply relation.fieldWorlds_replicate_of_ownership
    (checked.allocationSchemaFields functionMember descendant schemaAt)
  · simpa using IxIR1.resolveAtoms_length resolved
  · exact ownership

/-- Ordinary allocation preserves the exact baseline store relation. -/
theorem StoreRel.alloc {source : IxIR1.Store} {target : Eval.Store}
    (relation : StoreRel source target) (world : Ix.Compiler.Ixon.Owned)
    (node : IxIR1.Node) :
    StoreRel (source.allocNode world node).1
      (target.allocNode world node).1 := by
  constructor
  · rw [Eval.Store.allocNode_heap, relation.heap]
  · change target.resetAttempts = 0
    exact relation.resetAttempts
  · change target.hotResets = 0
    exact relation.hotResets
  · change target.coldResets = 0
    exact relation.coldResets
  · change target.reusedPayloadUnits = 0
    exact relation.reusedPayloadUnits

/-- Related stores choose the same fresh location. -/
theorem StoreRel.alloc_location {source : IxIR1.Store}
    {target : Eval.Store} (relation : StoreRel source target)
    (world : Ix.Compiler.Ixon.Owned) (node : IxIR1.Node) :
    (target.allocNode world node).2 =
      (source.allocNode world node).2 := by
  rw [Eval.Store.allocNode_location, relation.heap]

/-- Updating the same node preserves exact heap correspondence. -/
theorem StoreRel.setBox {source : IxIR1.Store} {target : Eval.Store}
    (relation : StoreRel source target) (location : Nat)
    (box : IxIR1.NodeBox) :
    StoreRel (source.setBox location box) (target.setBox location box) := by
  constructor
  · rw [Eval.Store.setBox_heap, relation.heap]
  · exact relation.resetAttempts
  · exact relation.hotResets
  · exact relation.coldResets
  · exact relation.reusedPayloadUnits

/-- Killing the same location preserves exact heap correspondence. -/
theorem StoreRel.kill {source : IxIR1.Store} {target : Eval.Store}
    (relation : StoreRel source target) (location : Nat) :
    StoreRel (source.kill location) (target.kill location) := by
  constructor
  · rw [Eval.Store.kill_heap, relation.heap]
  · exact relation.resetAttempts
  · exact relation.hotResets
  · exact relation.coldResets
  · exact relation.reusedPayloadUnits

/-- Charging the same RC operation preserves exact store correspondence. -/
theorem StoreRel.rcTick {source : IxIR1.Store} {target : Eval.Store}
    (relation : StoreRel source target) :
    StoreRel source.rcTick target.rcTick := by
  constructor
  · rw [Eval.Store.rcTick_heap, relation.heap]
  · exact relation.resetAttempts
  · exact relation.hotResets
  · exact relation.coldResets
  · exact relation.reusedPayloadUnits

/-! ## Source capability ownership -/

/-- Dynamic interpretation of one producer-retained source capability.
Scalars must really be non-locations; owners and borrows must name a live
value in their static world; consumed bindings impose no pointwise fact. -/
def CapabilityHolds (store : IxIR1.Store) (capability : Lower.BindingCap)
    (value : RVal) : Prop :=
  match capability with
  | .scalar => IxIR1.Sim.rvalLocation? value = none
  | .owned world | .borrowed world _ =>
      IxIR1.Sim.HasWorld store world value
  | .dead => True

/-- Incrementing one shared reference count preserves every pre-existing
capability fact. -/
theorem CapabilityHolds.incRcStore {store : IxIR1.Store} {location rc : Nat}
    {node : IxIR1.Node} {capability : Lower.BindingCap} {value : RVal}
    (found : store.get? location = some ⟨.shared, rc, node⟩)
    (holds : CapabilityHolds store capability value) :
    CapabilityHolds
      (IxIR1.Sim.incRcStore store location ⟨.shared, rc, node⟩)
      capability value := by
  cases capability with
  | scalar => exact holds
  | dead => trivial
  | owned world =>
      exact IxIR1.Sim.HasWorld.incRcStore found holds
  | borrowed world lender =>
      exact IxIR1.Sim.HasWorld.incRcStore found holds

/-- Fresh allocation preserves every capability fact about pre-existing
values. -/
theorem CapabilityHolds.allocNode {store : IxIR1.Store}
    {allocationWorld : Ix.Compiler.Ixon.Owned} {node : IxIR1.Node}
    {capability : Lower.BindingCap} {value : RVal}
    (holds : CapabilityHolds store capability value) :
    CapabilityHolds (store.allocNode allocationWorld node).1 capability
      value := by
  cases capability with
  | scalar => exact holds
  | dead => trivial
  | owned world => exact IxIR1.Sim.HasWorld.allocNode holds
  | borrowed world lender => exact IxIR1.Sim.HasWorld.allocNode holds

/-- Exact external owners selected from a capability vector. Scalars,
borrows, and dead source slots contribute no ownership root. -/
def rootsForCapabilities : List Lower.BindingCap → List RVal →
    List IxIR1.Sim.Root
  | .owned world :: capabilities, value :: values =>
      ⟨world, value⟩ :: rootsForCapabilities capabilities values
  | _ :: capabilities, _ :: values =>
      rootsForCapabilities capabilities values
  | _, _ => []

/-- The world annotation on one external root may be replaced when the same
runtime value is known in the new world. Incoming ownership multiplicity only
depends on the root's location, so all exact count equations are unchanged. -/
theorem RootOwnership_reworldHead
    {store : IxIR1.Store} {oldWorld newWorld : Ix.Compiler.Ixon.Owned}
    {value : RVal} {rest : List IxIR1.Sim.Root}
    (ownership : IxIR1.Sim.RootOwnership store
      (⟨oldWorld, value⟩ :: rest))
    (world : IxIR1.Sim.HasWorld store newWorld value) :
    IxIR1.Sim.RootOwnership store (⟨newWorld, value⟩ :: rest) := by
  refine ⟨?_, ownership.edges_world, ownership.pap_shared, ?_⟩
  · intro root member
    simp only [List.mem_cons] at member
    cases member with
    | inl equal =>
        subst root
        exact world
    | inr member =>
        exact ownership.roots_world root (by simp [member])
  · intro location box found
    have incomingEq : IxIR1.Sim.incoming store
        (⟨oldWorld, value⟩ :: rest) location =
      IxIR1.Sim.incoming store
        (⟨newWorld, value⟩ :: rest) location := rfl
    rw [← incomingEq]
    exact ownership.counts found

/-- A producer borrow is supported by a retained owner when it is the owner
itself or is reachable through zero or more node-child edges.  The relation
retains the exact pre-state heap path so destructive simulation can rebuild
that path in a restricted post-state from the surviving lender root. -/
inductive BorrowSupport (store : IxIR1.Store) (root : RVal) : RVal → Prop where
  | refl : BorrowSupport store root root
  | child {location : Nat} {box : IxIR1.NodeBox} {value : RVal} :
      BorrowSupport store root (.loc location) →
      store.get? location = some box →
      value ∈ IxIR1.Sim.nodeChildren box.node →
      BorrowSupport store root value

namespace BorrowSupport

/-- Exact heap ownership propagates the lender's world along every retained
borrow-support edge. -/
theorem hasWorld {store : IxIR1.Store} {roots : List IxIR1.Sim.Root}
    (ownership : IxIR1.Sim.RootOwnership store roots)
    {root value : RVal} {world : Ix.Compiler.Ixon.Owned}
    (rootWorld : IxIR1.Sim.HasWorld store world root)
    (support : BorrowSupport store root value) :
    IxIR1.Sim.HasWorld store world value := by
  induction support with
  | refl => exact rootWorld
  | @child location box value _ found member ih =>
      obtain ⟨actualBox, actualFound, actualWorld⟩ := ih
      have boxEq : box = actualBox :=
        Option.some.inj (found.symm.trans actualFound)
      subst actualBox
      simpa [actualWorld] using ownership.edges_world found value member

/-- Borrow support survives a shape-preserving store extension such as RC
increment or append allocation. -/
theorem monoStore {before after : IxIR1.Store}
    (extension : IxIR1.Sim.StoreGraphExtends before after)
    {root value : RVal} (support : BorrowSupport before root value) :
    BorrowSupport after root value := by
  induction support with
  | refl => exact .refl
  | @child location box value _ found member ih =>
      cases box with
      | mk world rc node =>
          obtain ⟨afterRc, afterFound⟩ := extension found
          exact .child ih afterFound member

/-- A borrow path rooted at a value that survives a destructive restriction
can be rebuilt in the post-state.  Post-state exact ownership supplies the
liveness of each next child; reverse shape inclusion identifies the same
node contents in the pre-state. -/
theorem ofRestricts {before after : IxIR1.Store}
    (restriction : IxIR1.Sim.StoreGraphRestricts before after)
    {roots : List IxIR1.Sim.Root}
    (ownership : IxIR1.Sim.RootOwnership after roots)
    {root value : RVal} {world : Ix.Compiler.Ixon.Owned}
    (rootWorld : IxIR1.Sim.HasWorld after world root)
    (support : BorrowSupport before root value) :
    BorrowSupport after root value ∧
      IxIR1.Sim.HasWorld after world value := by
  induction support with
  | refl => exact ⟨.refl, rootWorld⟩
  | @child location beforeBox value _ beforeFound member ih =>
      obtain ⟨parentSupport, parentWorld⟩ := ih
      obtain ⟨afterBox, afterFound, afterWorld⟩ := parentWorld
      cases afterBox with
      | mk boxWorld boxRc node =>
          obtain ⟨beforeRc, matchingBefore⟩ := restriction afterFound
          have beforeBoxEq :
              beforeBox = ⟨boxWorld, beforeRc, node⟩ :=
            Option.some.inj (beforeFound.symm.trans matchingBefore)
          subst beforeBox
          have valueWorld :
              IxIR1.Sim.HasWorld after boxWorld value :=
            ownership.edges_world afterFound value member
          have boxWorldEq : boxWorld = world := by
            simpa only using afterWorld
          refine ⟨.child parentSupport afterFound member, ?_⟩
          rw [boxWorldEq] at valueWorld
          exact valueWorld

end BorrowSupport

/-- Rebinding an owned source slot at the de Bruijn head preserves the exact
root multiset: the old occurrence is marked dead and the same root is moved
to the front. -/
theorem rootsForCapabilities_setDead_perm :
    ∀ {capabilities : List Lower.BindingCap} {source : List RVal}
      {index : Nat} {world : Ix.Compiler.Ixon.Owned} {value : RVal},
      capabilities[index]? = some (.owned world) →
      source[index]? = some value →
      ((⟨world, value⟩ : IxIR1.Sim.Root) ::
          rootsForCapabilities (capabilities.set index .dead) source).Perm
        (rootsForCapabilities capabilities source) := by
  intro capabilities source index
  induction index generalizing capabilities source with
  | zero =>
      cases capabilities with
      | nil => simp
      | cons capability capabilities =>
          cases source with
          | nil => simp
          | cons head tail =>
              intro world value capabilityAt sourceAt
              simp only [List.getElem?_cons_zero, Option.some.injEq] at capabilityAt sourceAt
              subst capability
              subst head
              simp [rootsForCapabilities]
  | succ index ih =>
      cases capabilities with
      | nil => simp
      | cons capability capabilities =>
          cases source with
          | nil => simp
          | cons head tail =>
              intro world value capabilityAt sourceAt
              simp only [List.getElem?_cons_succ] at capabilityAt sourceAt
              have tailPerm := ih capabilityAt sourceAt
              cases capability with
              | owned headWorld =>
                  exact (List.Perm.swap _ _ _).trans
                    (List.Perm.cons (⟨headWorld, head⟩ : IxIR1.Sim.Root)
                      tailPerm)
              | scalar | borrowed | dead =>
                  simpa [rootsForCapabilities] using tailPerm

/-- An owned capability contributes its exact source value to the ownership
root list. -/
theorem rootsForCapabilities_owned_mem
    {capabilities : Array Lower.BindingCap} {source : List RVal}
    {index : Nat} {world : Ix.Compiler.Ixon.Owned} {value : RVal}
    (capabilityAt : capabilities[index]? = some (.owned world))
    (sourceAt : source[index]? = some value) :
    (⟨world, value⟩ : IxIR1.Sim.Root) ∈
      rootsForCapabilities capabilities.toList source := by
  have moved := rootsForCapabilities_setDead_perm
    (capabilities := capabilities.toList) (source := source)
    (index := index) (world := world) (value := value)
    (by simpa using capabilityAt) (by simpa using sourceAt)
  exact moved.mem_iff.mp (by simp)

/-- Semantic provenance for one borrowed capability.  A local borrow is
supported by the owned source slot whose retained target atom is its exact
SSA lender.  A caller-rooted borrow is supported by one framed external root
that remains part of whole-machine ownership while the callee is active. -/
def BorrowProvenance (store : IxIR1.Store) (source : List RVal)
    (input : Array (Option Atom))
    (capabilities : Array Lower.BindingCap)
    (frameRoots : List IxIR1.Sim.Root)
    (world : Ix.Compiler.Ixon.Owned) (lender : BorrowLender)
    (value : RVal) : Prop :=
  match lender with
  | .caller =>
      ∃ root, root ∈ frameRoots ∧ root.world = world ∧
        BorrowSupport store root.value value
  | .value lenderId =>
      ∃ (ownerIndex : Nat) (ownerValue : RVal),
        input[ownerIndex]? = some (some (Atom.reg lenderId)) ∧
        capabilities[ownerIndex]? =
          some (Lower.BindingCap.owned world) ∧
        source[ownerIndex]? = some ownerValue ∧
        BorrowSupport store ownerValue value

/-- Every owned source slot names the SSA register that acts as a possible
local borrow lender. -/
def OwnedInputRegisters (input : Array (Option Atom))
    (capabilities : Array Lower.BindingCap) : Prop :=
  ∀ {index : Nat} {world : Ix.Compiler.Ixon.Owned},
    capabilities[index]? = some (.owned world) →
    ∃ id, input[index]? = some (some (.reg id))

/-- Coordinate coherence supplies the owned-register condition used by
semantic lender transport. -/
theorem OwnedInputRegisters.ofCoordinate
    {position : Lower.PositionTrace} {source : Lower.SourceSite}
    {block : BlockId} {target : Lower.TargetPosition}
    {input : Array (Option Atom)}
    (coordinate : position.coordinateMatches source block target input =
      true) :
    OwnedInputRegisters input position.sourceCapabilities := by
  intro index world capabilityAt
  exact position.inputReg_of_owned_coordinateMatch coordinate capabilityAt

namespace BorrowProvenance

/-- Prefixing one result binder transports every pre-existing borrow whose
capability tail is unchanged.  The successor's checked owned-register shape
and proof-map forgetting relation recover the same concrete SSA lender at the
shifted source index. -/
private theorem prependUnchanged
    {before after : IxIR1.Store}
    (extension : IxIR1.Sim.StoreGraphExtends before after)
    {source : List RVal} {input afterInput : Array (Option Atom)}
    {capabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    {headCapability : Lower.BindingCap} {headValue : RVal} {headAtom : Atom}
    (forgets : Lower.InputMap.Forgets afterInput
      (#[some headAtom] ++ input))
    (afterOwners : OwnedInputRegisters afterInput
      (#[headCapability] ++ capabilities))
    {world : Ix.Compiler.Ixon.Owned} {lender : BorrowLender} {value : RVal}
    (provenance : BorrowProvenance before source input capabilities
      frameRoots world lender value) :
    BorrowProvenance after (headValue :: source) afterInput
      (#[headCapability] ++ capabilities) frameRoots world lender value := by
  cases lender with
  | caller =>
      obtain ⟨root, member, rootWorld, support⟩ := provenance
      exact ⟨root, member, rootWorld, support.monoStore extension⟩
  | value lenderId =>
      obtain ⟨ownerIndex, ownerValue, inputAt, capabilityAt, sourceAt,
        support⟩ := provenance
      have shiftedCapability :
          (#[headCapability] ++ capabilities)[ownerIndex + 1]? =
            some (.owned world) := by
        simpa [Array.getElem?_append] using capabilityAt
      obtain ⟨actualId, afterInputAt⟩ :=
        afterOwners shiftedCapability
      have currentInputAt :
          (#[some headAtom] ++ input)[ownerIndex + 1]? =
            some (some (.reg actualId)) :=
        forgets (ownerIndex + 1) (.reg actualId) afterInputAt
      have oldActual : input[ownerIndex]? =
          some (some (.reg actualId)) := by
        simpa [Array.getElem?_append] using currentInputAt
      have actualEq : actualId = lenderId := by
        have atomEq : (Atom.reg actualId) = .reg lenderId :=
          Option.some.inj (Option.some.inj (oldActual.symm.trans inputAt))
        injection atomEq
      subst actualId
      refine ⟨ownerIndex + 1, ownerValue, afterInputAt,
        shiftedCapability, ?_, support.monoStore extension⟩
      simpa using sourceAt

/-- When the new result is not itself borrowed, all successor borrow
provenance comes from the unchanged capability tail. -/
private theorem prependNonBorrowed
    {before after : IxIR1.Store}
    (extension : IxIR1.Sim.StoreGraphExtends before after)
    {source : List RVal} {input afterInput : Array (Option Atom)}
    {capabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (oldBorrows : ∀ {index : Nat} {world : Ix.Compiler.Ixon.Owned}
        {lender : BorrowLender} {value : RVal},
      capabilities[index]? = some (.borrowed world lender) →
      source[index]? = some value →
      BorrowProvenance before source input capabilities frameRoots world
        lender value)
    {headCapability : Lower.BindingCap} {headValue : RVal} {headAtom : Atom}
    (headNotBorrowed : ∀ world lender,
      headCapability ≠ .borrowed world lender)
    (forgets : Lower.InputMap.Forgets afterInput
      (#[some headAtom] ++ input))
    (afterOwners : OwnedInputRegisters afterInput
      (#[headCapability] ++ capabilities)) :
    ∀ {index : Nat} {world : Ix.Compiler.Ixon.Owned}
        {lender : BorrowLender} {value : RVal},
      (#[headCapability] ++ capabilities)[index]? =
          some (.borrowed world lender) →
      (headValue :: source)[index]? = some value →
      BorrowProvenance after (headValue :: source) afterInput
        (#[headCapability] ++ capabilities) frameRoots world lender value := by
  intro index world lender value capabilityAt valueAt
  cases index with
  | zero =>
      simp [Array.getElem?_append] at capabilityAt
      exact (headNotBorrowed world lender capabilityAt).elim
  | succ index =>
      simp [Array.getElem?_append] at capabilityAt valueAt
      exact prependUnchanged extension forgets afterOwners
        (oldBorrows capabilityAt valueAt)

/-- Extending a borrow by one concrete heap edge preserves its recorded
lender while extending the semantic support path. -/
private theorem child
    {store : IxIR1.Store} {source : List RVal}
    {input : Array (Option Atom)}
    {capabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    {world : Ix.Compiler.Ixon.Owned} {lender : BorrowLender}
    {location : Nat} {box : IxIR1.NodeBox} {value : RVal}
    (provenance : BorrowProvenance store source input capabilities frameRoots
      world lender (.loc location))
    (found : store.get? location = some box)
    (member : value ∈ IxIR1.Sim.nodeChildren box.node) :
    BorrowProvenance store source input capabilities frameRoots world lender
      value := by
  cases lender with
  | caller =>
      obtain ⟨root, rootMember, rootWorld, support⟩ := provenance
      exact ⟨root, rootMember, rootWorld, .child support found member⟩
  | value lenderId =>
      obtain ⟨ownerIndex, ownerValue, ownerInput, ownerCapability,
        ownerValueAt, support⟩ := provenance
      exact ⟨ownerIndex, ownerValue, ownerInput, ownerCapability,
        ownerValueAt, .child support found member⟩

/-- Exact ownership turns recorded lender provenance into the dynamic world
fact required by the borrowed capability. -/
theorem hasWorld {store : IxIR1.Store} {source : List RVal}
    {input : Array (Option Atom)}
    {capabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    {world : Ix.Compiler.Ixon.Owned} {lender : BorrowLender}
    {value : RVal}
    (ownership : IxIR1.Sim.RootOwnership store
      (rootsForCapabilities capabilities.toList source ++ frameRoots))
    (provenance : BorrowProvenance store source input capabilities frameRoots
      world lender value) :
    IxIR1.Sim.HasWorld store world value := by
  cases lender with
  | caller =>
      obtain ⟨root, rootMember, rootWorld, support⟩ := provenance
      have rootHas : IxIR1.Sim.HasWorld store world root.value := by
        simpa [rootWorld] using ownership.roots_world root
          (List.mem_append_right _ rootMember)
      exact support.hasWorld ownership rootHas
  | value lenderId =>
      obtain ⟨ownerIndex, ownerValue, ownerInput, ownerCapability,
        ownerValueAt, support⟩ := provenance
      have ownerHas : IxIR1.Sim.HasWorld store world ownerValue :=
        ownership.roots_world ⟨world, ownerValue⟩
          (List.mem_append_left _
            (rootsForCapabilities_owned_mem ownerCapability ownerValueAt))
      exact support.hasWorld ownership ownerHas

/-- Provenance rooted at a surviving owner transports across a destructive
store restriction. -/
theorem ofRestricts {before after : IxIR1.Store} {source : List RVal}
    {input : Array (Option Atom)}
    {capabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (restriction : IxIR1.Sim.StoreGraphRestricts before after)
    (ownership : IxIR1.Sim.RootOwnership after
      (rootsForCapabilities capabilities.toList source ++ frameRoots))
    {world : Ix.Compiler.Ixon.Owned} {lender : BorrowLender}
    {value : RVal}
    (provenance : BorrowProvenance before source input capabilities frameRoots
      world lender value) :
    BorrowProvenance after source input capabilities frameRoots world lender
      value := by
  cases lender with
  | caller =>
      obtain ⟨root, rootMember, rootWorld, support⟩ := provenance
      have rootHas : IxIR1.Sim.HasWorld after world root.value := by
        simpa [rootWorld] using ownership.roots_world root
          (List.mem_append_right _ rootMember)
      exact ⟨root, rootMember, rootWorld,
        (support.ofRestricts restriction ownership rootHas).1⟩
  | value lenderId =>
      obtain ⟨ownerIndex, ownerValue, ownerInput, ownerCapability,
        ownerValueAt, support⟩ := provenance
      have ownerHas : IxIR1.Sim.HasWorld after world ownerValue :=
        ownership.roots_world ⟨world, ownerValue⟩
          (List.mem_append_left _
            (rootsForCapabilities_owned_mem ownerCapability ownerValueAt))
      exact ⟨ownerIndex, ownerValue, ownerInput, ownerCapability,
        ownerValueAt,
        (support.ofRestricts restriction ownership ownerHas).1⟩

end BorrowProvenance

/-- Dynamic source ownership at one producer capability position.  The
pointwise clause supplies world/scalar safety for operand checks; exact root
ownership includes suspended caller roots, and every borrow carries an exact
semantic path from its producer-recorded local or caller lender. -/
structure SourceOwnershipInvariant (store : IxIR1.Store)
    (source : List RVal) (input : Array (Option Atom))
    (capabilities : Array Lower.BindingCap)
    (frameRoots : List IxIR1.Sim.Root) : Prop where
  length : source.length = capabilities.size
  holds : ∀ {index : Nat} {capability : Lower.BindingCap} {value : RVal},
    capabilities[index]? = some capability →
    source[index]? = some value →
    CapabilityHolds store capability value
  ownership : IxIR1.Sim.RootOwnership store
    (rootsForCapabilities capabilities.toList source ++ frameRoots)
  borrows : ∀ {index : Nat} {world : Ix.Compiler.Ixon.Owned}
      {lender : BorrowLender} {value : RVal},
    capabilities[index]? = some (.borrowed world lender) →
    source[index]? = some value →
    BorrowProvenance store source input capabilities frameRoots world lender
      value

/-- Trace-indexed form threaded by the recursive worker.  It is deliberately
generic over the matching flat producer position, so switch children and
instruction continuations can select their own capability vector. -/
def SourceOwnershipAt (positions : List Lower.PositionTrace)
    (trace : Lower.CodeTrace) (store : IxIR1.Store)
    (source : List RVal) (frameRoots : List IxIR1.Sim.Root) : Prop :=
  ∀ position,
    position ∈ positions →
    position.coordinateMatches trace.source trace.sourceBlock
      trace.targetPosition trace.sourceInputMap = true →
    SourceOwnershipInvariant store source trace.sourceInputMap
      position.sourceCapabilities frameRoots

namespace SourceOwnershipAt

private theorem sourceMapOf_zero_for_ownership
    (explicitMap : Array (Option Atom)) :
    Lower.EdgeTrace.sourceMapOf 0 explicitMap = explicitMap := by
  apply Array.ext
  · simp [Lower.EdgeTrace.sourceMapOf]
  · intro index leftBound rightBound
    simp [Lower.EdgeTrace.sourceMapOf]
    cases explicitMap[index] with
    | none => rfl
    | some atom => cases atom <;> rfl

/-- Any empty-input trace begins with the exact empty dynamic ownership
state.  In particular this constructs the invariant at the closed synthetic
main root from the retained zero-arity input map. -/
theorem empty {positions : List Lower.PositionTrace}
    {trace : Lower.CodeTrace}
    (inputEmpty : trace.sourceInputMap.size = 0) :
    SourceOwnershipAt positions trace ({} : IxIR1.Store) [] [] := by
  intro position _ coordinate
  have capabilitySize :=
    position.sourceCapabilities_size_of_coordinateMatch coordinate
  have capabilitiesEmpty : position.sourceCapabilities = #[] :=
    Array.eq_empty_of_size_eq_zero (capabilitySize.trans inputEmpty)
  rw [capabilitiesEmpty]
  have traceInputEmpty : trace.sourceInputMap = #[] :=
    Array.eq_empty_of_size_eq_zero inputEmpty
  rw [traceInputEmpty]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro index capability value capabilityAt
    simp at capabilityAt
  · simpa [rootsForCapabilities] using IxIR1.Sim.RootOwnership.empty
  · intro index world lender value capabilityAt
    simp at capabilityAt

end SourceOwnershipAt

namespace SourceOwnershipInvariant

/-- Empty main entry has no owned roots, framed roots, or scalar obligations. -/
theorem empty :
    SourceOwnershipInvariant ({} : IxIR1.Store) [] #[] #[] [] := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro index capability value capabilityAt
    simp at capabilityAt
  · simpa [rootsForCapabilities] using IxIR1.Sim.RootOwnership.empty
  · intro index world lender value capabilityAt
    simp at capabilityAt

/-- Focus an arbitrary producer owner at the head of the exact root list.
The remaining list still contains every suspended-frame root, which is the
shape needed by physical-reuse stack-avoidance arguments. -/
theorem focusOwned
    {store : IxIR1.Store} {source : List RVal}
    {input : Array (Option Atom)}
    {capabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    {index : Nat} {world : Ix.Compiler.Ixon.Owned} {value : RVal}
    (capabilityAt : capabilities[index]? = some (.owned world))
    (sourceAt : source[index]? = some value) :
    ∃ rest,
      IxIR1.Sim.RootOwnership store (⟨world, value⟩ :: rest) ∧
        ∀ root ∈ frameRoots, root ∈ rest := by
  have rootMember : (⟨world, value⟩ : IxIR1.Sim.Root) ∈
      rootsForCapabilities capabilities.toList source :=
    rootsForCapabilities_owned_mem capabilityAt sourceAt
  obtain ⟨before, after, rootsEq⟩ := List.mem_iff_append.mp rootMember
  let rest := (after ++ frameRoots) ++ before
  refine ⟨rest, ?_, ?_⟩
  · apply invariant.ownership.perm
    rw [rootsEq]
    simpa [rest, List.append_assoc] using
      (List.perm_append_comm
        (l₁ := before)
        (l₂ := (⟨world, value⟩ : IxIR1.Sim.Root) ::
          (after ++ frameRoots)))
  · intro root member
    simp [rest, member]

/-- A capability accepted at an owned boundary dynamically inhabits the
requested world. -/
theorem hasWorld_of_canConsume {store : IxIR1.Store}
    {capability : Lower.BindingCap} {value : RVal}
    {world : Ix.Compiler.Ixon.Owned}
    (holds : CapabilityHolds store capability value)
    (accepted : capability.canConsume world = true) :
    IxIR1.Sim.HasWorld store world value := by
  cases capability <;> cases value <;>
    simp_all [CapabilityHolds, Lower.BindingCap.canConsume,
      IxIR1.Sim.rvalLocation?, IxIR1.Sim.HasWorld, beq_iff_eq]

/-- Resolve one statically accepted source operand to a value in the requested
world. -/
theorem resolveAtom_hasWorld {store : IxIR1.Store} {source : List RVal}
    {input : Array (Option Atom)}
    {capabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    {atom : IxIR1.Atom} {capability : Lower.BindingCap}
    {world : Ix.Compiler.Ixon.Owned} {value : RVal}
    (capabilityAt : Lower.sourceCapability? capabilities atom =
      some capability)
    (accepted : capability.canConsume world = true)
    (resolved : IxIR1.resolveAtom source atom = .ok value) :
    IxIR1.Sim.HasWorld store world value := by
  cases atom with
  | lit literal =>
      have valueEq : (.lit literal : RVal) = value := by
        simpa [IxIR1.resolveAtom] using resolved
      subst value
      trivial
  | erased =>
      have valueEq : (.erased : RVal) = value := by
        simpa [IxIR1.resolveAtom] using resolved
      subst value
      trivial
  | var index =>
      simp only [Lower.sourceCapability?] at capabilityAt
      cases sourceAt : source[index]? with
      | none => simp [IxIR1.resolveAtom, sourceAt] at resolved
      | some found =>
          have valueEq : found = value := by
            simpa [IxIR1.resolveAtom, sourceAt] using resolved
          subst found
          exact hasWorld_of_canConsume
            (invariant.holds capabilityAt sourceAt) accepted

/-- Retiring loans rooted at one SSA lender preserves every surviving
pointwise capability fact. -/
private theorem retireLenderCapabilities_holds
    {store : IxIR1.Store} {source : List RVal}
    {capabilities : Array Lower.BindingCap} {lender : ValueId}
    (holds : ∀ {index : Nat} {capability : Lower.BindingCap} {value : RVal},
      capabilities[index]? = some capability →
      source[index]? = some value →
      CapabilityHolds store capability value) :
    ∀ {index : Nat} {capability : Lower.BindingCap} {value : RVal},
      (Lower.retireLenderCapabilities capabilities lender)[index]? =
          some capability →
      source[index]? = some value →
      CapabilityHolds store capability value := by
  intro index capability value capabilityAt valueAt
  rw [Lower.retireLenderCapabilities, Array.getElem?_map] at capabilityAt
  cases oldAt : capabilities[index]? with
  | none => simp [oldAt] at capabilityAt
  | some oldCapability =>
      have oldHolds := holds oldAt valueAt
      simp only [oldAt, Option.map_some, Option.some.injEq] at capabilityAt
      cases oldCapability with
      | scalar | owned | dead =>
          subst capability
          exact oldHolds
      | borrowed world oldLender =>
          cases oldLender with
          | caller =>
              subst capability
              exact oldHolds
          | value actual =>
              by_cases same : actual = lender
              · simp [Lower.BindingCap.retireLender, same] at capabilityAt
                subst capability
                trivial
              · simp [Lower.BindingCap.retireLender, same] at capabilityAt
                subst capability
                exact oldHolds

/-- Loan retirement does not change the exact owned-root multiset because
borrowed and dead slots are both ownership-inert. -/
private theorem rootsForCapabilities_retireLenderList
    (lender : ValueId) :
    ∀ (capabilities : List Lower.BindingCap) (source : List RVal),
      rootsForCapabilities
          (capabilities.map (Lower.BindingCap.retireLender lender)) source =
        rootsForCapabilities capabilities source := by
  intro capabilities
  induction capabilities with
  | nil => intro source; simp [rootsForCapabilities]
  | cons capability capabilities ih =>
      intro source
      cases source with
      | nil => simp [rootsForCapabilities]
      | cons value values =>
          cases capability with
          | scalar | owned | dead =>
              simp [Lower.BindingCap.retireLender, rootsForCapabilities, ih]
          | borrowed world oldLender =>
              cases oldLender with
              | caller =>
                  simp [Lower.BindingCap.retireLender,
                    rootsForCapabilities, ih]
              | value actual =>
                  by_cases same : actual = lender <;>
                    simp [Lower.BindingCap.retireLender, same,
                      rootsForCapabilities, ih]

private theorem rootsForCapabilities_retireLenderCapabilities
    (capabilities : Array Lower.BindingCap) (source : List RVal)
    (lender : ValueId) :
    rootsForCapabilities
        (Lower.retireLenderCapabilities capabilities lender).toList source =
      rootsForCapabilities capabilities.toList source := by
  simpa [Lower.retireLenderCapabilities] using
    rootsForCapabilities_retireLenderList lender capabilities.toList source

/-- Retiring one owner and its rooted loans preserves all surviving dynamic
facts and removes exactly that owner's root. -/
private theorem retireOwnerCapabilities_ownership
    {store : IxIR1.Store} {source : List RVal}
    {capabilities remaining : Array Lower.BindingCap}
    {input : Array (Option Atom)} {sourceIndex : Nat}
    {world : Ix.Compiler.Ixon.Owned} {value : RVal}
    (holds : ∀ {index : Nat} {capability : Lower.BindingCap}
        {selected : RVal},
      capabilities[index]? = some capability →
      source[index]? = some selected →
      CapabilityHolds store capability selected)
    (capabilityAt : capabilities[sourceIndex]? =
      some (.owned world))
    (sourceAt : source[sourceIndex]? = some value)
    (retired : Lower.retireOwnerCapabilities? capabilities input sourceIndex =
      some remaining) :
    (∀ {index : Nat} {capability : Lower.BindingCap} {selected : RVal},
        remaining[index]? = some capability →
        source[index]? = some selected →
        CapabilityHolds store capability selected) ∧
      (((⟨world, value⟩ : IxIR1.Sim.Root) ::
          rootsForCapabilities remaining.toList source).Perm
        (rootsForCapabilities capabilities.toList source)) := by
  unfold Lower.retireOwnerCapabilities? at retired
  split at retired <;> try contradiction
  next lender inputAt =>
    injection retired with remainingEq
    subst remaining
    have sourceBound : sourceIndex < capabilities.size :=
      (Array.getElem?_eq_some_iff.mp capabilityAt).1
    let consumed := capabilities.setIfInBounds sourceIndex .dead
    have consumedHolds :
        ∀ {index : Nat} {capability : Lower.BindingCap} {selected : RVal},
          consumed[index]? = some capability →
          source[index]? = some selected →
          CapabilityHolds store capability selected := by
      intro index capability selected capabilityAt' selectedAt
      by_cases same : sourceIndex = index
      · subst index
        simp [consumed, sourceBound] at capabilityAt'
        subst capability
        trivial
      · have oldCapability : capabilities[index]? = some capability := by
          simpa [consumed, Array.getElem?_setIfInBounds, same] using
            capabilityAt'
        exact holds oldCapability selectedAt
    refine ⟨retireLenderCapabilities_holds consumedHolds, ?_⟩
    rw [rootsForCapabilities_retireLenderCapabilities]
    have movedRoot := rootsForCapabilities_setDead_perm
      (capabilities := capabilities.toList) (source := source)
      (index := sourceIndex) (world := world) (value := value)
      (by simpa using capabilityAt) (by simpa using sourceAt)
    simpa [consumed, Array.toList_setIfInBounds] using movedRoot

/-- A borrow surviving exact owner retirement retains valid provenance.  A
local surviving lender cannot be the consumed register (that loan would have
become dead), and its distinct owned source slot is unchanged by both the
point update and lender-retirement map. -/
private theorem retireOwnerCapabilities_borrows
    {store : IxIR1.Store} {source : List RVal}
    {input : Array (Option Atom)}
    {capabilities remaining : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (oldBorrows : ∀ {index : Nat} {world : Ix.Compiler.Ixon.Owned}
        {lender : BorrowLender} {value : RVal},
      capabilities[index]? = some (.borrowed world lender) →
      source[index]? = some value →
      BorrowProvenance store source input capabilities frameRoots world lender
        value)
    {consumedIndex : Nat} {consumedWorld : Ix.Compiler.Ixon.Owned}
    (consumedCapability : capabilities[consumedIndex]? =
      some (.owned consumedWorld))
    (retired : Lower.retireOwnerCapabilities? capabilities input
      consumedIndex = some remaining)
    {index : Nat} {world : Ix.Compiler.Ixon.Owned}
    {lender : BorrowLender} {value : RVal}
    (remainingAt : remaining[index]? = some (.borrowed world lender))
    (valueAt : source[index]? = some value) :
    BorrowProvenance store source input remaining frameRoots world lender
      value := by
  unfold Lower.retireOwnerCapabilities? at retired
  split at retired <;> try contradiction
  next consumedLender consumedInput =>
    injection retired with remainingEq
    subst remaining
    have consumedBound : consumedIndex < capabilities.size :=
      (Array.getElem?_eq_some_iff.mp consumedCapability).1
    by_cases sameIndex : consumedIndex = index
    · subst index
      have killedAt :
          (Lower.retireLenderCapabilities
            (capabilities.setIfInBounds consumedIndex .dead)
            consumedLender)[consumedIndex]? = some .dead := by
        rw [Lower.retireLenderCapabilities, Array.getElem?_map]
        simp [consumedBound, Lower.BindingCap.retireLender]
      rw [killedAt] at remainingAt
      cases remainingAt
    · have setAt :
          (capabilities.setIfInBounds consumedIndex .dead)[index]? =
            capabilities[index]? := by
        simp [sameIndex]
      rw [Lower.retireLenderCapabilities, Array.getElem?_map, setAt] at remainingAt
      cases oldAt : capabilities[index]? with
      | none => simp [oldAt] at remainingAt
      | some oldCapability =>
          cases oldCapability with
          | scalar | owned | dead =>
              simp [oldAt, Lower.BindingCap.retireLender] at remainingAt
          | borrowed oldWorld oldLender =>
              cases oldLender with
              | caller =>
                  simp only [oldAt, Option.map_some,
                    Lower.BindingCap.retireLender,
                    Option.some.injEq] at remainingAt
                  rcases remainingAt with ⟨rfl, rfl⟩
                  obtain ⟨root, rootMember, rootWorld, support⟩ :=
                    oldBorrows oldAt valueAt
                  exact ⟨root, rootMember, rootWorld, support⟩
              | value oldLenderId =>
                  by_cases sameLender : oldLenderId = consumedLender
                  · simp [oldAt, Lower.BindingCap.retireLender,
                      sameLender] at remainingAt
                  · simp [oldAt, Lower.BindingCap.retireLender,
                      sameLender] at remainingAt
                    rcases remainingAt with ⟨rfl, rfl⟩
                    obtain ⟨ownerIndex, ownerValue, ownerInput,
                      ownerCapability, ownerValueAt, support⟩ :=
                      oldBorrows oldAt valueAt
                    have ownerNe : consumedIndex ≠ ownerIndex := by
                      intro equal
                      subst ownerIndex
                      have atomEq :
                          (Atom.reg consumedLender) = .reg oldLenderId :=
                        Option.some.inj
                          (Option.some.inj (consumedInput.symm.trans ownerInput))
                      have lenderEq : consumedLender = oldLenderId := by
                        injection atomEq
                      exact sameLender lenderEq.symm
                    have ownerSetAt :
                        (capabilities.setIfInBounds consumedIndex .dead
                          )[ownerIndex]? = some (.owned oldWorld) := by
                      simpa [Array.getElem?_setIfInBounds, ownerNe] using
                        ownerCapability
                    have remainingOwner :
                        (Lower.retireLenderCapabilities
                          (capabilities.setIfInBounds consumedIndex .dead)
                          consumedLender)[ownerIndex]? =
                            some (.owned oldWorld) := by
                      rw [Lower.retireLenderCapabilities, Array.getElem?_map,
                        ownerSetAt]
                      rfl
                    exact ⟨ownerIndex, ownerValue, ownerInput,
                      remainingOwner, ownerValueAt, support⟩

/-- The exact producer `pure`/`move` capability effect preserves dynamic
source ownership.  Scalars and borrows are copied without changing the root
multiset; an owned value moves its existing root from the consumed slot to the
new head. -/
theorem move {store : IxIR1.Store} {source : List RVal}
    {input afterInput : Array (Option Atom)}
    {capabilities afterCapabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    {headAtom : Atom}
    (forgets : Lower.InputMap.Forgets afterInput (#[some headAtom] ++ input))
    (afterOwners : OwnedInputRegisters afterInput afterCapabilities)
    {atom : IxIR1.Atom} {value : RVal}
    (resolved : IxIR1.resolveAtom source atom = .ok value)
    (transition : Lower.moveCapabilities? capabilities input atom =
      some afterCapabilities) :
    SourceOwnershipInvariant store (value :: source) afterInput
      afterCapabilities frameRoots := by
  cases atom with
  | lit literal =>
      simp only [Lower.moveCapabilities?, Lower.sourceCapability?] at transition
      injection transition with afterEq
      subst afterCapabilities
      have valueEq : value = .lit literal := by
        simpa [IxIR1.resolveAtom] using resolved.symm
      subst value
      refine ⟨by simp [Array.size_append, Nat.add_comm, invariant.length],
        ?_, ?_, ?_⟩
      · intro index capability value capabilityAt valueAt
        cases index with
        | zero =>
            simp [Array.getElem?_append] at capabilityAt valueAt
            subst capability
            subst value
            trivial
        | succ index =>
            simp [Array.getElem?_append] at capabilityAt valueAt
            exact invariant.holds capabilityAt valueAt
      · simpa [rootsForCapabilities] using invariant.ownership
      · intro index world lender selected capabilityAt selectedAt
        cases index with
        | zero => simp [Array.getElem?_append] at capabilityAt
        | succ index =>
            simp [Array.getElem?_append] at capabilityAt selectedAt
            exact BorrowProvenance.prependUnchanged
              (IxIR1.Sim.StoreGraphExtends.refl store) forgets afterOwners
              (invariant.borrows capabilityAt selectedAt)
  | erased =>
      simp only [Lower.moveCapabilities?, Lower.sourceCapability?] at transition
      injection transition with afterEq
      subst afterCapabilities
      have valueEq : value = .erased := by
        simpa [IxIR1.resolveAtom] using resolved.symm
      subst value
      refine ⟨by simp [Array.size_append, Nat.add_comm, invariant.length],
        ?_, ?_, ?_⟩
      · intro index capability value capabilityAt valueAt
        cases index with
        | zero =>
            simp [Array.getElem?_append] at capabilityAt valueAt
            subst capability
            subst value
            trivial
        | succ index =>
            simp [Array.getElem?_append] at capabilityAt valueAt
            exact invariant.holds capabilityAt valueAt
      · simpa [rootsForCapabilities] using invariant.ownership
      · intro index world lender selected capabilityAt selectedAt
        cases index with
        | zero => simp [Array.getElem?_append] at capabilityAt
        | succ index =>
            simp [Array.getElem?_append] at capabilityAt selectedAt
            exact BorrowProvenance.prependUnchanged
              (IxIR1.Sim.StoreGraphExtends.refl store) forgets afterOwners
              (invariant.borrows capabilityAt selectedAt)
  | var sourceIndex =>
      cases sourceAt : source[sourceIndex]? with
      | none => simp [IxIR1.resolveAtom, sourceAt] at resolved
      | some found =>
          have valueEq : found = value := by
            simpa [IxIR1.resolveAtom, sourceAt] using resolved
          subst found
          cases capabilityAt : capabilities[sourceIndex]? with
          | none =>
              simp [Lower.moveCapabilities?, Lower.sourceCapability?,
                capabilityAt] at transition
          | some capability =>
              cases capability with
              | dead =>
                  simp [Lower.moveCapabilities?, Lower.sourceCapability?,
                    capabilityAt] at transition
              | scalar =>
                  simp only [Lower.moveCapabilities?,
                    Lower.sourceCapability?, capabilityAt] at transition
                  injection transition with afterEq
                  subst afterCapabilities
                  refine ⟨by simp [Array.size_append, Nat.add_comm,
                    invariant.length], ?_, ?_, ?_⟩
                  · intro index capability value capabilityAt' valueAt
                    cases index with
                    | zero =>
                        simp [Array.getElem?_append] at capabilityAt' valueAt
                        subst capability
                        subst value
                        exact invariant.holds capabilityAt sourceAt
                    | succ index =>
                        simp [Array.getElem?_append] at capabilityAt' valueAt
                        exact invariant.holds capabilityAt' valueAt
                  · simpa [rootsForCapabilities] using invariant.ownership
                  · intro index world lender selected capabilityAt' selectedAt
                    cases index with
                    | zero => simp [Array.getElem?_append] at capabilityAt'
                    | succ index =>
                        simp [Array.getElem?_append] at capabilityAt' selectedAt
                        exact BorrowProvenance.prependUnchanged
                          (IxIR1.Sim.StoreGraphExtends.refl store) forgets
                          afterOwners
                          (invariant.borrows capabilityAt' selectedAt)
              | borrowed world lender =>
                  simp only [Lower.moveCapabilities?,
                    Lower.sourceCapability?, capabilityAt] at transition
                  injection transition with afterEq
                  subst afterCapabilities
                  refine ⟨by simp [Array.size_append, Nat.add_comm,
                    invariant.length], ?_, ?_, ?_⟩
                  · intro index capability value capabilityAt' valueAt
                    cases index with
                    | zero =>
                        simp [Array.getElem?_append] at capabilityAt' valueAt
                        subst capability
                        subst value
                        exact invariant.holds capabilityAt sourceAt
                    | succ index =>
                        simp [Array.getElem?_append] at capabilityAt' valueAt
                        exact invariant.holds capabilityAt' valueAt
                  · simpa [rootsForCapabilities] using invariant.ownership
                  · intro index actualWorld actualLender selected
                      capabilityAt' selectedAt
                    cases index with
                    | zero =>
                        simp [Array.getElem?_append] at capabilityAt' selectedAt
                        rcases capabilityAt' with ⟨rfl, rfl⟩
                        subst selected
                        exact BorrowProvenance.prependUnchanged
                          (IxIR1.Sim.StoreGraphExtends.refl store) forgets
                          afterOwners
                          (invariant.borrows capabilityAt sourceAt)
                    | succ index =>
                        simp [Array.getElem?_append] at capabilityAt' selectedAt
                        exact BorrowProvenance.prependUnchanged
                          (IxIR1.Sim.StoreGraphExtends.refl store) forgets
                          afterOwners
                          (invariant.borrows capabilityAt' selectedAt)
              | owned world =>
                  simp only [Lower.moveCapabilities?,
                    Lower.sourceCapability?, capabilityAt] at transition
                  cases retiredEq : Lower.retireOwnerCapabilities?
                      capabilities input sourceIndex with
                  | none => simp [retiredEq] at transition
                  | some remaining =>
                      simp only [retiredEq, Option.map_some,
                        Option.some.injEq] at transition
                      subst afterCapabilities
                      obtain ⟨remainingHolds, movedRoot⟩ :=
                        retireOwnerCapabilities_ownership invariant.holds
                          capabilityAt sourceAt retiredEq
                      have remainingSize : remaining.size = capabilities.size :=
                        Lower.retireOwnerCapabilities?_size retiredEq
                      refine ⟨by simp [Array.size_append, remainingSize,
                        invariant.length, Nat.add_comm], ?_, ?_, ?_⟩
                      · intro index capability selected capabilityAt' selectedAt
                        cases index with
                        | zero =>
                            simp [Array.getElem?_append] at capabilityAt' selectedAt
                            subst capability
                            subst selected
                            exact invariant.holds capabilityAt sourceAt
                        | succ index =>
                            simp [Array.getElem?_append] at capabilityAt' selectedAt
                            exact remainingHolds capabilityAt' selectedAt
                      · apply invariant.ownership.perm
                        simpa [rootsForCapabilities, List.append_assoc] using
                          movedRoot.symm.append_right frameRoots
                      · intro index actualWorld lender selected capabilityAt'
                          selectedAt
                        cases index with
                        | zero =>
                            simp [Array.getElem?_append] at capabilityAt'
                        | succ index =>
                            simp [Array.getElem?_append] at capabilityAt' selectedAt
                            have remainingProvenance :=
                              retireOwnerCapabilities_borrows invariant.borrows
                                capabilityAt retiredEq capabilityAt' selectedAt
                            exact BorrowProvenance.prependUnchanged
                              (IxIR1.Sim.StoreGraphExtends.refl store) forgets
                              afterOwners remainingProvenance

/-- The exact producer `dup`/`retainShared` capability effect preserves
dynamic source ownership. A borrowed shared value gains its first external
root; an owned shared value gains a second root; scalars are ownership-inert.
-/
theorem dup {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {sourceCurrent : IxIR1.FnDef} {store outputStore : IxIR1.Store}
    {source : List RVal}
    {input afterInput : Array (Option Atom)}
    {capabilities afterCapabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    {headAtom : Atom}
    (forgets : Lower.InputMap.Forgets afterInput (#[some headAtom] ++ input))
    (afterOwners : OwnedInputRegisters afterInput afterCapabilities)
    {atom : IxIR1.Atom} {value : RVal}
    (resolved : IxIR1.resolveAtom source atom = .ok value)
    (transition : Lower.dupCapabilities? capabilities atom =
      some afterCapabilities)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent store
      source (.dup atom) = .ok (outputStore, value)) :
    SourceOwnershipInvariant outputStore (value :: source) afterInput
      afterCapabilities frameRoots := by
  obtain ⟨selected, selectedResolved, selectedOutput⟩ :=
    IxIR1.runOp_dup_success operationRun
  have selectedEq : selected = value := by
    exact Except.ok.inj (selectedResolved.symm.trans resolved)
  subst selected
  cases atom with
  | lit literal =>
      simp only [Lower.dupCapabilities?, Lower.sourceCapability?] at transition
      injection transition with afterEq
      subst afterCapabilities
      have valueEq : value = .lit literal := by
        simpa [IxIR1.resolveAtom] using resolved.symm
      subst value
      have outputEq : (outputStore, IxIR1.RVal.lit literal) =
          (store, IxIR1.RVal.lit literal) := selectedOutput
      have storeEq : outputStore = store := congrArg Prod.fst outputEq
      subst outputStore
      refine ⟨by simp [Array.size_append, Nat.add_comm, invariant.length],
        ?_, ?_, ?_⟩
      · intro index capability value capabilityAt valueAt
        cases index with
        | zero =>
            simp [Array.getElem?_append] at capabilityAt valueAt
            subst capability
            subst value
            trivial
        | succ index =>
            simp [Array.getElem?_append] at capabilityAt valueAt
            exact invariant.holds capabilityAt valueAt
      · simpa [rootsForCapabilities] using invariant.ownership
      · exact BorrowProvenance.prependNonBorrowed
          (IxIR1.Sim.StoreGraphExtends.refl store) invariant.borrows
          (by intros; simp) forgets afterOwners
  | erased =>
      simp only [Lower.dupCapabilities?, Lower.sourceCapability?] at transition
      injection transition with afterEq
      subst afterCapabilities
      have valueEq : value = .erased := by
        simpa [IxIR1.resolveAtom] using resolved.symm
      subst value
      have outputEq : (outputStore, IxIR1.RVal.erased) =
          (store, IxIR1.RVal.erased) := selectedOutput
      have storeEq : outputStore = store := congrArg Prod.fst outputEq
      subst outputStore
      refine ⟨by simp [Array.size_append, Nat.add_comm, invariant.length],
        ?_, ?_, ?_⟩
      · intro index capability value capabilityAt valueAt
        cases index with
        | zero =>
            simp [Array.getElem?_append] at capabilityAt valueAt
            subst capability
            subst value
            trivial
        | succ index =>
            simp [Array.getElem?_append] at capabilityAt valueAt
            exact invariant.holds capabilityAt valueAt
      · simpa [rootsForCapabilities] using invariant.ownership
      · exact BorrowProvenance.prependNonBorrowed
          (IxIR1.Sim.StoreGraphExtends.refl store) invariant.borrows
          (by intros; simp) forgets afterOwners
  | var sourceIndex =>
      cases sourceAt : source[sourceIndex]? with
      | none => simp [IxIR1.resolveAtom, sourceAt] at resolved
      | some found =>
          have valueEq : found = value := by
            simpa [IxIR1.resolveAtom, sourceAt] using resolved
          subst found
          cases capabilityAt : capabilities[sourceIndex]? with
          | none =>
              simp [Lower.dupCapabilities?, Lower.sourceCapability?,
                capabilityAt] at transition
          | some capability =>
              cases capability with
              | dead =>
                  simp [Lower.dupCapabilities?, Lower.sourceCapability?,
                    capabilityAt] at transition
              | owned world =>
                  cases world with
                  | unique =>
                      simp [Lower.dupCapabilities?, Lower.sourceCapability?,
                        capabilityAt] at transition
                  | shared =>
                      simp only [Lower.dupCapabilities?,
                        Lower.sourceCapability?, capabilityAt] at transition
                      injection transition with afterEq
                      subst afterCapabilities
                      have sourceBound : sourceIndex < capabilities.size :=
                        (Array.getElem?_eq_some_iff.mp capabilityAt).1
                      cases value with
                      | lit literal =>
                          have outputEq : (outputStore, IxIR1.RVal.lit literal) =
                              (store, IxIR1.RVal.lit literal) := selectedOutput
                          have storeEq : outputStore = store :=
                            congrArg Prod.fst outputEq
                          subst outputStore
                          refine ⟨by simp [Array.size_append, Nat.add_comm,
                            invariant.length], ?_, ?_, ?_⟩
                          · intro index capability value capabilityAt' valueAt
                            cases index with
                            | zero =>
                                simp [Array.getElem?_append] at capabilityAt' valueAt
                                subst capability
                                subst value
                                trivial
                            | succ index =>
                                simp [Array.getElem?_append] at capabilityAt' valueAt
                                exact invariant.holds capabilityAt' valueAt
                          · simpa [rootsForCapabilities] using
                              invariant.ownership.addNoLocation rfl
                          · exact BorrowProvenance.prependNonBorrowed
                              (IxIR1.Sim.StoreGraphExtends.refl store)
                              invariant.borrows (by intros; simp) forgets
                              afterOwners
                      | erased =>
                          have outputEq : (outputStore, IxIR1.RVal.erased) =
                              (store, IxIR1.RVal.erased) := selectedOutput
                          have storeEq : outputStore = store :=
                            congrArg Prod.fst outputEq
                          subst outputStore
                          refine ⟨by simp [Array.size_append, Nat.add_comm,
                            invariant.length], ?_, ?_, ?_⟩
                          · intro index capability value capabilityAt' valueAt
                            cases index with
                            | zero =>
                                simp [Array.getElem?_append] at capabilityAt' valueAt
                                subst capability
                                subst value
                                trivial
                            | succ index =>
                                simp [Array.getElem?_append] at capabilityAt' valueAt
                                exact invariant.holds capabilityAt' valueAt
                          · simpa [rootsForCapabilities] using
                              invariant.ownership.addNoLocation rfl
                          · exact BorrowProvenance.prependNonBorrowed
                              (IxIR1.Sim.StoreGraphExtends.refl store)
                              invariant.borrows (by intros; simp) forgets
                              afterOwners
                      | loc location =>
                          obtain ⟨box, foundBox, shared, outputEq⟩ :=
                            selectedOutput
                          cases box with
                          | mk boxWorld rc node =>
                              change boxWorld = .shared at shared
                              subst boxWorld
                              have storeEq : outputStore =
                                  IxIR1.Sim.incRcStore store location
                                    ⟨.shared, rc, node⟩ := by
                                simpa [IxIR1.Sim.incRcStore] using
                                  congrArg Prod.fst outputEq
                              subst outputStore
                              refine ⟨by simp [Array.size_append, Nat.add_comm,
                                invariant.length], ?_, ?_, ?_⟩
                              · intro index capability value capabilityAt' valueAt
                                cases index with
                                | zero =>
                                    simp [Array.getElem?_append] at capabilityAt' valueAt
                                    subst capability
                                    subst value
                                    exact IxIR1.Sim.HasWorld.incRcStore foundBox
                                      (invariant.holds capabilityAt sourceAt)
                                | succ index =>
                                    simp [Array.getElem?_append] at capabilityAt' valueAt
                                    exact (invariant.holds capabilityAt' valueAt).incRcStore
                                      foundBox
                              · have movedRoot := rootsForCapabilities_setDead_perm
                                  (capabilities := capabilities.toList)
                                  (source := source) (index := sourceIndex)
                                      (world := .shared)
                                      (value := IxIR1.RVal.loc location)
                                  (by simpa using capabilityAt)
                                  (by simpa using sourceAt)
                                have oldFirst := invariant.ownership.perm
                                  (by
                                    simpa [Array.toList_setIfInBounds,
                                      rootsForCapabilities,
                                      List.append_assoc] using
                                        movedRoot.symm.append_right frameRoots)
                                have duplicated := oldFirst.dup foundBox
                                apply duplicated.perm
                                simpa [Array.toList_setIfInBounds,
                                  rootsForCapabilities,
                                  List.append_assoc] using
                                    (List.Perm.cons
                                      (⟨.shared, IxIR1.RVal.loc location⟩ : IxIR1.Sim.Root)
                                      movedRoot).append_right frameRoots
                              · exact BorrowProvenance.prependNonBorrowed
                                  (IxIR1.Sim.StoreGraphExtends.incRcStore
                                    foundBox) invariant.borrows
                                  (by intros; simp) forgets afterOwners
              | borrowed world lender =>
                  cases world with
                  | unique =>
                      simp [Lower.dupCapabilities?, Lower.sourceCapability?,
                        capabilityAt] at transition
                  | shared =>
                      simp only [Lower.dupCapabilities?,
                        Lower.sourceCapability?, capabilityAt] at transition
                      injection transition with afterEq
                      subst afterCapabilities
                      cases value with
                      | lit literal =>
                          have outputEq : (outputStore, IxIR1.RVal.lit literal) =
                              (store, IxIR1.RVal.lit literal) := selectedOutput
                          have storeEq : outputStore = store :=
                            congrArg Prod.fst outputEq
                          subst outputStore
                          refine ⟨by simp [Array.size_append, Nat.add_comm,
                            invariant.length], ?_, ?_, ?_⟩
                          · intro index capability value capabilityAt' valueAt
                            cases index with
                            | zero =>
                                simp [Array.getElem?_append] at capabilityAt' valueAt
                                subst capability
                                subst value
                                trivial
                            | succ index =>
                                simp [Array.getElem?_append] at capabilityAt' valueAt
                                exact invariant.holds capabilityAt' valueAt
                          · simpa [rootsForCapabilities] using
                              invariant.ownership.addNoLocation rfl
                          · exact BorrowProvenance.prependNonBorrowed
                              (IxIR1.Sim.StoreGraphExtends.refl store)
                              invariant.borrows (by intros; simp) forgets
                              afterOwners
                      | erased =>
                          have outputEq : (outputStore, IxIR1.RVal.erased) =
                              (store, IxIR1.RVal.erased) := selectedOutput
                          have storeEq : outputStore = store :=
                            congrArg Prod.fst outputEq
                          subst outputStore
                          refine ⟨by simp [Array.size_append, Nat.add_comm,
                            invariant.length], ?_, ?_, ?_⟩
                          · intro index capability value capabilityAt' valueAt
                            cases index with
                            | zero =>
                                simp [Array.getElem?_append] at capabilityAt' valueAt
                                subst capability
                                subst value
                                trivial
                            | succ index =>
                                simp [Array.getElem?_append] at capabilityAt' valueAt
                                exact invariant.holds capabilityAt' valueAt
                          · simpa [rootsForCapabilities] using
                              invariant.ownership.addNoLocation rfl
                          · exact BorrowProvenance.prependNonBorrowed
                              (IxIR1.Sim.StoreGraphExtends.refl store)
                              invariant.borrows (by intros; simp) forgets
                              afterOwners
                      | loc location =>
                          obtain ⟨box, foundBox, shared, outputEq⟩ :=
                            selectedOutput
                          cases box with
                          | mk boxWorld rc node =>
                              change boxWorld = .shared at shared
                              subst boxWorld
                              have storeEq : outputStore =
                                  IxIR1.Sim.incRcStore store location
                                    ⟨.shared, rc, node⟩ := by
                                simpa [IxIR1.Sim.incRcStore] using
                                  congrArg Prod.fst outputEq
                              subst outputStore
                              refine ⟨by simp [Array.size_append, Nat.add_comm,
                                invariant.length], ?_, ?_, ?_⟩
                              · intro index capability value capabilityAt' valueAt
                                cases index with
                                | zero =>
                                    simp [Array.getElem?_append] at capabilityAt' valueAt
                                    subst capability
                                    subst value
                                    exact IxIR1.Sim.HasWorld.incRcStore foundBox
                                      (invariant.holds capabilityAt sourceAt)
                                | succ index =>
                                    simp [Array.getElem?_append] at capabilityAt' valueAt
                                    exact (invariant.holds capabilityAt' valueAt).incRcStore
                                      foundBox
                              · simpa [rootsForCapabilities] using
                                  invariant.ownership.retainShared foundBox
                              · exact BorrowProvenance.prependNonBorrowed
                                  (IxIR1.Sim.StoreGraphExtends.incRcStore
                                    foundBox) invariant.borrows
                                  (by intros; simp) forgets afterOwners
              | scalar =>
                  simp only [Lower.dupCapabilities?, Lower.sourceCapability?,
                    capabilityAt] at transition
                  injection transition with afterEq
                  subst afterCapabilities
                  have scalarHolds := invariant.holds capabilityAt sourceAt
                  cases value with
                  | loc location =>
                      simp [CapabilityHolds, IxIR1.Sim.rvalLocation?] at scalarHolds
                  | lit literal =>
                      have outputEq : (outputStore, IxIR1.RVal.lit literal) =
                          (store, IxIR1.RVal.lit literal) := selectedOutput
                      have storeEq : outputStore = store :=
                        congrArg Prod.fst outputEq
                      subst outputStore
                      refine ⟨by simp [Array.size_append, Nat.add_comm,
                        invariant.length], ?_, ?_, ?_⟩
                      · intro index capability value capabilityAt' valueAt
                        cases index with
                        | zero =>
                            simp [Array.getElem?_append] at capabilityAt' valueAt
                            subst capability
                            subst value
                            exact scalarHolds
                        | succ index =>
                            simp [Array.getElem?_append] at capabilityAt' valueAt
                            exact invariant.holds capabilityAt' valueAt
                      · simpa [rootsForCapabilities] using invariant.ownership
                      · exact BorrowProvenance.prependNonBorrowed
                          (IxIR1.Sim.StoreGraphExtends.refl store)
                          invariant.borrows (by intros; simp) forgets
                          afterOwners
                  | erased =>
                      have outputEq : (outputStore, IxIR1.RVal.erased) =
                          (store, IxIR1.RVal.erased) := selectedOutput
                      have storeEq : outputStore = store :=
                        congrArg Prod.fst outputEq
                      subst outputStore
                      refine ⟨by simp [Array.size_append, Nat.add_comm,
                        invariant.length], ?_, ?_, ?_⟩
                      · intro index capability value capabilityAt' valueAt
                        cases index with
                        | zero =>
                            simp [Array.getElem?_append] at capabilityAt' valueAt
                            subst capability
                            subst value
                            exact scalarHolds
                        | succ index =>
                            simp [Array.getElem?_append] at capabilityAt' valueAt
                            exact invariant.holds capabilityAt' valueAt
                      · simpa [rootsForCapabilities] using invariant.ownership
                      · exact BorrowProvenance.prependNonBorrowed
                          (IxIR1.Sim.StoreGraphExtends.refl store)
                          invariant.borrows (by intros; simp) forgets
                          afterOwners

/-- The baseline-compatible producer `fetch` effect preserves exact dynamic
ownership.  The parent capability proves the selected edge inhabits the
constructor world; the new borrowed head contributes no external root. -/
theorem fetch {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {sourceCurrent : IxIR1.FnDef} {store outputStore : IxIR1.Store}
    {source : List RVal}
    {input afterInput : Array (Option Atom)}
    {capabilities afterCapabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    {headAtom : Atom}
    (forgets : Lower.InputMap.Forgets afterInput (#[some headAtom] ++ input))
    (afterOwners : OwnedInputRegisters afterInput afterCapabilities)
    {sourceAtom : IxIR1.Atom} {sourceField : Nat} {targetAtom : Atom}
    {value : RVal}
    (translated : Lower.InputMap.translateAtom input sourceAtom =
      some targetAtom)
    (transition : Lower.fetchCapabilities? capabilities sourceAtom targetAtom =
      some afterCapabilities)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent
      store source (.fetch sourceAtom sourceField) =
        .ok (outputStore, value)) :
    SourceOwnershipInvariant outputStore (value :: source) afterInput
      afterCapabilities frameRoots := by
  obtain ⟨location, box, identity, fields, runtimeValue, sourceResolved,
      sourceGet, node, fieldAt, outputEq⟩ :=
    IxIR1.runOp_fetch_success operationRun
  have storeEq : outputStore = store := congrArg Prod.fst outputEq
  have valueEq : value = runtimeValue := congrArg Prod.snd outputEq
  subst outputStore
  subst runtimeValue
  have prependBorrowed : ∀ {world lender},
      IxIR1.Sim.HasWorld store world (.loc location) →
      BorrowProvenance store source input capabilities frameRoots world lender
        (.loc location) →
      OwnedInputRegisters afterInput
        (#[.borrowed world lender] ++ capabilities) →
      SourceOwnershipInvariant store (value :: source)
        afterInput (#[.borrowed world lender] ++ capabilities)
        frameRoots := by
    intro world lender parentWorld parentProvenance successorOwners
    obtain ⟨parentBox, parentGet, parentWorldEq⟩ := parentWorld
    have parentBoxEq : parentBox = box :=
      Option.some.inj (parentGet.symm.trans sourceGet)
    subst parentBox
    have resultWorld : IxIR1.Sim.HasWorld store world value := by
      have fieldMember : value ∈ fields :=
        (Array.mem_iff_getElem?).2 ⟨sourceField, fieldAt⟩
      have childMember : value ∈ IxIR1.Sim.nodeChildren box.node := by
        rw [node]
        simpa [IxIR1.Sim.nodeChildren] using fieldMember
      have edgeWorld := invariant.ownership.edges_world sourceGet value
        childMember
      simpa [parentWorldEq] using edgeWorld
    have fieldMember : value ∈ fields :=
      (Array.mem_iff_getElem?).2 ⟨sourceField, fieldAt⟩
    have childMember : value ∈ IxIR1.Sim.nodeChildren box.node := by
      rw [node]
      simpa [IxIR1.Sim.nodeChildren] using fieldMember
    refine ⟨by simp [Array.size_append, Nat.add_comm, invariant.length],
      ?_, ?_, ?_⟩
    · intro index capability selectedValue capabilityAt valueAt
      cases index with
      | zero =>
          simp [Array.getElem?_append] at capabilityAt valueAt
          subst capability
          subst selectedValue
          exact resultWorld
      | succ index =>
          simp [Array.getElem?_append] at capabilityAt valueAt
          exact invariant.holds capabilityAt valueAt
    · simpa [rootsForCapabilities] using invariant.ownership
    · intro index actualWorld actualLender selected capabilityAt selectedAt
      cases index with
      | zero =>
          simp [Array.getElem?_append] at capabilityAt selectedAt
          rcases capabilityAt with ⟨rfl, rfl⟩
          subst selected
          exact BorrowProvenance.prependUnchanged
            (IxIR1.Sim.StoreGraphExtends.refl store) forgets successorOwners
            (BorrowProvenance.child parentProvenance sourceGet childMember)
      | succ index =>
          simp [Array.getElem?_append] at capabilityAt selectedAt
          exact BorrowProvenance.prependUnchanged
            (IxIR1.Sim.StoreGraphExtends.refl store) forgets successorOwners
            (invariant.borrows capabilityAt selectedAt)
  cases sourceAtom with
  | lit literal =>
      simp [IxIR1.resolveAtom] at sourceResolved
  | erased =>
      simp [IxIR1.resolveAtom] at sourceResolved
  | var sourceIndex =>
      cases sourceAt : source[sourceIndex]? with
      | none => simp [IxIR1.resolveAtom, sourceAt] at sourceResolved
      | some found =>
          have foundEq : found = .loc location := by
            simpa [IxIR1.resolveAtom, sourceAt] using sourceResolved
          subst found
          cases capabilityAt : capabilities[sourceIndex]? with
          | none =>
              simp [Lower.fetchCapabilities?, Lower.sourceCapability?,
                capabilityAt] at transition
          | some capability =>
              cases capability with
              | scalar =>
                  simp [Lower.fetchCapabilities?, Lower.sourceCapability?,
                    capabilityAt] at transition
              | dead =>
                  simp [Lower.fetchCapabilities?, Lower.sourceCapability?,
                    capabilityAt] at transition
              | owned world =>
                  cases targetAtom with
                  | lit literal =>
                      simp [Lower.fetchCapabilities?, Lower.sourceCapability?,
                        capabilityAt] at transition
                  | erased =>
                      simp [Lower.fetchCapabilities?, Lower.sourceCapability?,
                        capabilityAt] at transition
                  | reg id =>
                      simp only [Lower.fetchCapabilities?,
                        Lower.sourceCapability?, capabilityAt] at transition
                      injection transition with afterEq
                      subst afterCapabilities
                      have inputAt : input[sourceIndex]? =
                          some (some (.reg id)) := by
                        cases foundInput : input[sourceIndex]? with
                        | none =>
                            simp [Lower.InputMap.translateAtom, foundInput]
                              at translated
                        | some slot =>
                            cases slot with
                            | none =>
                                simp [Lower.InputMap.translateAtom, foundInput]
                                  at translated
                            | some actual =>
                                have actualEq : actual = .reg id := by
                                  simpa [Lower.InputMap.translateAtom,
                                    foundInput] using translated
                                subst actual
                                rfl
                      have parentProvenance : BorrowProvenance store source
                          input capabilities frameRoots world (.value id)
                          (.loc location) :=
                        ⟨sourceIndex, .loc location, inputAt, capabilityAt,
                          sourceAt, .refl⟩
                      exact prependBorrowed
                        (invariant.holds capabilityAt sourceAt)
                        parentProvenance afterOwners
              | borrowed world lender =>
                  simp only [Lower.fetchCapabilities?,
                    Lower.sourceCapability?, capabilityAt] at transition
                  injection transition with afterEq
                  subst afterCapabilities
                  exact prependBorrowed
                    (invariant.holds capabilityAt sourceAt)
                    (invariant.borrows capabilityAt sourceAt) afterOwners

end SourceOwnershipInvariant

namespace SourceOwnershipAt

/-- A checked `pure`/`move` node transports the trace-indexed dynamic
ownership invariant to its exact recursive continuation. -/
theorem pure {checked : Lower.Checked}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.pure sourceAtom) index (.move targetAtom) next))
    {store : IxIR1.Store} {source : List RVal} {value : RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.pure sourceAtom) index (.move targetAtom) next) store source
          frameRoots)
    (resolved : IxIR1.resolveAtom source sourceAtom = .ok value) :
    SourceOwnershipAt checked.artifact.trace.positions next store
      (value :: source) frameRoots := by
  intro after afterMember afterCoordinate
  obtain ⟨before, beforeMember, beforeCoordinate, transitionMatch⟩ :=
    checked.pureTransition functionMember descendant afterMember
      afterCoordinate
  have beforeInvariant := ownership before beforeMember (by
      simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
        Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
          beforeCoordinate)
  change SourceOwnershipInvariant store source input
    before.sourceCapabilities frameRoots at beforeInvariant
  have mapFacts := Lower.CodeTrace.inputMapForgets_of_match
    (functionTrace.descendantInputMapsMatch descendant) (by rfl)
  have letOpMatch := functionTrace.descendantLetOpMatch descendant
  have forgets : Lower.InputMap.Forgets next.sourceInputMap
      (#[some (.reg entryValueCount)] ++ input) := by
    simpa [letOpMatch.1.nextInput] using mapFacts.2.2.1
  have afterOwners : OwnedInputRegisters next.sourceInputMap
      after.sourceCapabilities :=
    OwnedInputRegisters.ofCoordinate afterCoordinate
  unfold Lower.PositionTrace.moveMatches at transitionMatch
  cases transitionEq : Lower.moveCapabilities?
      before.sourceCapabilities input sourceAtom with
  | none => simp [transitionEq] at transitionMatch
  | some expected =>
      have expectedEq : expected = after.sourceCapabilities := by
        simpa [transitionEq, beq_iff_eq] using transitionMatch
      apply beforeInvariant.move forgets afterOwners resolved
      simpa [expectedEq] using transitionEq

/-- A checked `dup`/`retainShared` node transports trace-indexed dynamic
ownership to its exact recursive continuation. -/
theorem dup {checked : Lower.Checked}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.dup sourceAtom) index (.retainShared targetAtom) next))
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {store outputStore : IxIR1.Store} {source : List RVal} {value : RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.dup sourceAtom) index (.retainShared targetAtom) next) store source
          frameRoots)
    (resolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1)
      functionTrace.source store source (.dup sourceAtom) =
        .ok (outputStore, value)) :
    SourceOwnershipAt checked.artifact.trace.positions next outputStore
      (value :: source) frameRoots := by
  intro after afterMember afterCoordinate
  obtain ⟨before, beforeMember, beforeCoordinate, transitionMatch⟩ :=
    checked.dupTransition functionMember descendant afterMember
      afterCoordinate
  have beforeInvariant := ownership before beforeMember (by
      simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
        Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
          beforeCoordinate)
  change SourceOwnershipInvariant store source input
    before.sourceCapabilities frameRoots at beforeInvariant
  have mapFacts := Lower.CodeTrace.inputMapForgets_of_match
    (functionTrace.descendantInputMapsMatch descendant) (by rfl)
  have letOpMatch := functionTrace.descendantLetOpMatch descendant
  have forgets : Lower.InputMap.Forgets next.sourceInputMap
      (#[some (.reg entryValueCount)] ++ input) := by
    simpa [letOpMatch.1.nextInput] using mapFacts.2.2.1
  have afterOwners : OwnedInputRegisters next.sourceInputMap
      after.sourceCapabilities :=
    OwnedInputRegisters.ofCoordinate afterCoordinate
  unfold Lower.PositionTrace.dupMatches at transitionMatch
  cases transitionEq : Lower.dupCapabilities?
      before.sourceCapabilities sourceAtom with
  | none => simp [transitionEq] at transitionMatch
  | some expected =>
      have expectedEq : expected = after.sourceCapabilities := by
        simpa [transitionEq, beq_iff_eq] using transitionMatch
      apply beforeInvariant.dup forgets afterOwners resolved
        (sourceFuel := sourceFuel)
        (operationRun := operationRun)
      simpa [expectedEq] using transitionEq

/-- A checked `fetch` node transports trace-indexed dynamic ownership to its
exact recursive continuation without an external transition premise. -/
theorem fetch {checked : Lower.Checked}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceAtom : IxIR1.Atom} {sourceField : Nat}
    {targetAtom : Atom} {targetCid : IxIR1.CtorId} {targetField : Nat}
    {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
          (.fetch targetAtom targetCid targetField) next))
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {store outputStore : IxIR1.Store} {source : List RVal} {value : RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
          (.fetch targetAtom targetCid targetField) next) store source
            frameRoots)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1)
      functionTrace.source store source (.fetch sourceAtom sourceField) =
        .ok (outputStore, value)) :
    SourceOwnershipAt checked.artifact.trace.positions next outputStore
      (value :: source) frameRoots := by
  intro after afterMember afterCoordinate
  obtain ⟨before, beforeMember, beforeCoordinate, transitionMatch⟩ :=
    checked.fetchTransition functionMember descendant afterMember
      afterCoordinate
  have beforeInvariant := ownership before beforeMember (by
      simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
        Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
          beforeCoordinate)
  change SourceOwnershipInvariant store source input
    before.sourceCapabilities frameRoots at beforeInvariant
  have mapFacts := Lower.CodeTrace.inputMapForgets_of_match
    (functionTrace.descendantInputMapsMatch descendant) (by rfl)
  have letOpMatch := functionTrace.descendantLetOpMatch descendant
  have forgets : Lower.InputMap.Forgets next.sourceInputMap
      (#[some (.reg entryValueCount)] ++ input) := by
    simpa [letOpMatch.1.nextInput] using mapFacts.2.2.1
  have afterOwners : OwnedInputRegisters next.sourceInputMap
      after.sourceCapabilities :=
    OwnedInputRegisters.ofCoordinate afterCoordinate
  have translated :=
    (functionTrace.descendantOperationSyntax descendant).2
  unfold Lower.PositionTrace.fetchMatches at transitionMatch
  cases transitionEq : Lower.fetchCapabilities?
      before.sourceCapabilities sourceAtom targetAtom with
  | none => simp [transitionEq] at transitionMatch
  | some expected =>
      have expectedEq : expected = after.sourceCapabilities := by
        simpa [transitionEq, beq_iff_eq] using transitionMatch
      apply beforeInvariant.fetch forgets afterOwners translated
        (sourceFuel := sourceFuel)
        (operationRun := operationRun)
      simpa [expectedEq] using transitionEq

end SourceOwnershipAt

namespace SourceOwnershipInvariant

private def sourceResolveStep (source : List RVal)
    (values : List RVal) (atom : IxIR1.Atom) :
    Except IxIR1.Err (List RVal) := do
  pure (values ++ [← IxIR1.resolveAtom source atom])

private inductive SourceAtomsResolve (source : List RVal) :
    List IxIR1.Atom → List RVal → Prop where
  | nil : SourceAtomsResolve source [] []
  | cons (head : IxIR1.resolveAtom source atom = .ok value)
      (tail : SourceAtomsResolve source atoms values) :
      SourceAtomsResolve source (atom :: atoms) (value :: values)

namespace SourceAtomsResolve

private theorem ofFoldlM {source : List RVal} :
    ∀ atoms accumulator output,
      atoms.foldlM (sourceResolveStep source) accumulator = .ok output →
      ∃ values, SourceAtomsResolve source atoms values ∧
        output = accumulator ++ values := by
  intro atoms
  induction atoms with
  | nil =>
      intro accumulator output run
      simp only [List.foldlM_nil, pure, Except.pure] at run
      injection run with outputEq
      subst output
      exact ⟨[], .nil, by simp⟩
  | cons atom atoms ih =>
      intro accumulator output run
      simp only [List.foldlM_cons] at run
      cases headRun : IxIR1.resolveAtom source atom with
      | error error =>
          have step : sourceResolveStep source accumulator atom =
              .error error := by
            simp [sourceResolveStep, headRun, bind, Except.bind]
          rw [step] at run
          simp only [bind, Except.bind] at run
          contradiction
      | ok value =>
          have step : sourceResolveStep source accumulator atom =
              .ok (accumulator ++ [value]) := by
            simp [sourceResolveStep, headRun, bind, Except.bind,
              pure, Except.pure]
          rw [step] at run
          simp only [bind, Except.bind] at run
          obtain ⟨values, valuesRun, outputEq⟩ :=
            ih (accumulator ++ [value]) output run
          refine ⟨value :: values, .cons headRun valuesRun, ?_⟩
          rw [outputEq]
          simp [List.append_assoc]

private theorem ofResolveAtoms {source : List RVal}
    {atoms : Array IxIR1.Atom} {values : List RVal}
    (resolved : IxIR1.resolveAtoms source atoms = .ok values) :
    SourceAtomsResolve source atoms.toList values := by
  unfold IxIR1.resolveAtoms at resolved
  rw [← Array.foldlM_toList] at resolved
  change atoms.toList.foldlM (sourceResolveStep source) [] =
    .ok values at resolved
  obtain ⟨found, relation, valuesEq⟩ :=
    ofFoldlM atoms.toList [] values resolved
  simp only [List.nil_append] at valuesEq
  subst found
  exact relation

private theorem length {source : List RVal} {atoms : List IxIR1.Atom}
    {values : List RVal} (resolved : SourceAtomsResolve source atoms values) :
    atoms.length = values.length := by
  induction resolved with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem worlds {store : IxIR1.Store} {source : List RVal}
    {input : Array (Option Atom)}
    {capabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    {world : Ix.Compiler.Ixon.Owned} :
    ∀ {atoms values}, SourceAtomsResolve source atoms values →
      (∀ atom ∈ atoms,
        ∃ capability,
          Lower.sourceCapability? capabilities atom = some capability ∧
            capability.canConsume world = true) →
      ∀ value ∈ values, IxIR1.Sim.HasWorld store world value := by
  intro atoms values relation
  induction relation with
  | nil => simp
  | @cons atom value atoms values head tail ih =>
      intro accepted candidate member
      simp only [List.mem_cons] at member
      cases member with
      | inl equal =>
          subst candidate
          obtain ⟨capability, capabilityAt, canConsume⟩ :=
            accepted atom (by simp)
          exact invariant.resolveAtom_hasWorld capabilityAt canConsume head
      | inr member =>
          apply ih
          · intro tailAtom tailMember
            exact accepted tailAtom (by simp [tailMember])
          · exact member

end SourceAtomsResolve

/-- One exact producer consumption moves the selected ownership token behind
an arbitrary already-consumed prefix. Scalar arguments are admitted as inert
roots; owned variables are removed from their source slot by permutation. -/
private theorem consumeCapability_ownership
    {store : IxIR1.Store} {source : List RVal}
    {capabilities remaining : Array Lower.BindingCap}
    {input : Array (Option Atom)}
    {world : Ix.Compiler.Ixon.Owned} {atom : IxIR1.Atom} {value : RVal}
    {consumedRoots : List IxIR1.Sim.Root}
    {suffixRoots : List IxIR1.Sim.Root}
    (holds : ∀ {index : Nat} {capability : Lower.BindingCap}
        {selected : RVal},
      capabilities[index]? = some capability →
      source[index]? = some selected →
      CapabilityHolds store capability selected)
    (ownership : IxIR1.Sim.RootOwnership store
      (consumedRoots ++ rootsForCapabilities capabilities.toList source ++
        suffixRoots))
    (resolved : IxIR1.resolveAtom source atom = .ok value)
    (consumed : Lower.consumeCapability? capabilities input world atom =
      some remaining) :
    (∀ {index : Nat} {capability : Lower.BindingCap} {selected : RVal},
        remaining[index]? = some capability →
        source[index]? = some selected →
        CapabilityHolds store capability selected) ∧
      IxIR1.Sim.RootOwnership store
        (consumedRoots ++ [(⟨world, value⟩ : IxIR1.Sim.Root)] ++
          rootsForCapabilities remaining.toList source ++ suffixRoots) := by
  have addScalar (scalar : IxIR1.Sim.rvalLocation? value = none) :
      IxIR1.Sim.RootOwnership store
        (consumedRoots ++ [(⟨world, value⟩ : IxIR1.Sim.Root)] ++
          rootsForCapabilities capabilities.toList source ++ suffixRoots) := by
    have added := ownership.addNoLocation (world := world) scalar
    apply added.perm
    simpa [List.append_assoc] using
      (List.perm_append_comm
        (l₁ := [(⟨world, value⟩ : IxIR1.Sim.Root)])
        (l₂ := consumedRoots)).append_right
          (rootsForCapabilities capabilities.toList source ++ suffixRoots)
  cases atom with
  | lit literal =>
      simp only [Lower.consumeCapability?, Lower.sourceCapability?] at consumed
      injection consumed with remainingEq
      subst remaining
      have valueEq : value = .lit literal := by
        simpa [IxIR1.resolveAtom] using resolved.symm
      subst value
      exact ⟨holds, addScalar rfl⟩
  | erased =>
      simp only [Lower.consumeCapability?, Lower.sourceCapability?] at consumed
      injection consumed with remainingEq
      subst remaining
      have valueEq : value = .erased := by
        simpa [IxIR1.resolveAtom] using resolved.symm
      subst value
      exact ⟨holds, addScalar rfl⟩
  | var sourceIndex =>
      cases sourceAt : source[sourceIndex]? with
      | none => simp [IxIR1.resolveAtom, sourceAt] at resolved
      | some found =>
          have foundEq : found = value := by
            simpa [IxIR1.resolveAtom, sourceAt] using resolved
          subst found
          cases capabilityAt : capabilities[sourceIndex]? with
          | none =>
              simp [Lower.consumeCapability?, Lower.sourceCapability?,
                capabilityAt] at consumed
          | some capability =>
              cases capability with
              | borrowed actual lender =>
                  simp [Lower.consumeCapability?, Lower.sourceCapability?,
                    capabilityAt] at consumed
              | dead =>
                  simp [Lower.consumeCapability?, Lower.sourceCapability?,
                    capabilityAt] at consumed
              | scalar =>
                  simp only [Lower.consumeCapability?,
                    Lower.sourceCapability?, capabilityAt] at consumed
                  injection consumed with remainingEq
                  subst remaining
                  have scalarHolds := holds capabilityAt sourceAt
                  exact ⟨holds, addScalar (by
                    simpa [CapabilityHolds] using scalarHolds)⟩
              | owned actual =>
                  simp [Lower.consumeCapability?, Lower.sourceCapability?,
                    capabilityAt] at consumed
                  obtain ⟨actualEq, remainingEq⟩ := consumed
                  subst actual
                  obtain ⟨remainingHolds, movedRoot⟩ :=
                    retireOwnerCapabilities_ownership holds capabilityAt
                      sourceAt remainingEq
                  refine ⟨remainingHolds, ?_⟩
                  apply ownership.perm
                  simpa [List.append_assoc] using
                    (movedRoot.symm.append_left consumedRoots).append_right
                      suffixRoots

/-- One owned-boundary capability update preserves provenance for every
borrow that remains live after the update. -/
private theorem consumeCapability_borrows
    {store : IxIR1.Store} {source : List RVal}
    {input : Array (Option Atom)}
    {capabilities remaining : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (oldBorrows : ∀ {index : Nat} {world : Ix.Compiler.Ixon.Owned}
        {lender : BorrowLender} {value : RVal},
      capabilities[index]? = some (.borrowed world lender) →
      source[index]? = some value →
      BorrowProvenance store source input capabilities frameRoots world lender
        value)
    {world : Ix.Compiler.Ixon.Owned} {atom : IxIR1.Atom}
    (consumed : Lower.consumeCapability? capabilities input world atom =
      some remaining) :
    ∀ {index : Nat} {borrowWorld : Ix.Compiler.Ixon.Owned}
        {lender : BorrowLender} {value : RVal},
      remaining[index]? = some (.borrowed borrowWorld lender) →
      source[index]? = some value →
      BorrowProvenance store source input remaining frameRoots borrowWorld
        lender value := by
  cases atom with
  | lit literal =>
      simp only [Lower.consumeCapability?, Lower.sourceCapability?] at consumed
      injection consumed with remainingEq
      subst remaining
      exact oldBorrows
  | erased =>
      simp only [Lower.consumeCapability?, Lower.sourceCapability?] at consumed
      injection consumed with remainingEq
      subst remaining
      exact oldBorrows
  | var sourceIndex =>
      cases capabilityAt : capabilities[sourceIndex]? with
      | none =>
          simp [Lower.consumeCapability?, Lower.sourceCapability?,
            capabilityAt] at consumed
      | some capability =>
          cases capability with
          | scalar =>
              simp only [Lower.consumeCapability?, Lower.sourceCapability?,
                capabilityAt] at consumed
              injection consumed with remainingEq
              subst remaining
              exact oldBorrows
          | borrowed borrowWorld lender | dead =>
              simp [Lower.consumeCapability?, Lower.sourceCapability?,
                capabilityAt] at consumed
          | owned actual =>
              simp [Lower.consumeCapability?, Lower.sourceCapability?,
                capabilityAt] at consumed
              obtain ⟨actualEq, remainingEq⟩ := consumed
              subst actual
              exact retireOwnerCapabilities_borrows oldBorrows capabilityAt
                remainingEq

/-- Sequential exact producer consumption accumulates the resolved argument
roots in source order ahead of the surviving source-owner roots. -/
private theorem consumeCapabilitiesList_ownership
    {store : IxIR1.Store} {source : List RVal}
    {capabilities remaining : Array Lower.BindingCap}
    {input : Array (Option Atom)}
    {world : Ix.Compiler.Ixon.Owned}
    {atoms : List IxIR1.Atom} {values : List RVal}
    {consumedRoots : List IxIR1.Sim.Root}
    {suffixRoots : List IxIR1.Sim.Root}
    (holds : ∀ {index : Nat} {capability : Lower.BindingCap}
        {selected : RVal},
      capabilities[index]? = some capability →
      source[index]? = some selected →
      CapabilityHolds store capability selected)
    (ownership : IxIR1.Sim.RootOwnership store
      (consumedRoots ++ rootsForCapabilities capabilities.toList source ++
        suffixRoots))
    (resolved : SourceAtomsResolve source atoms values)
    (consumed : Lower.consumeCapabilitiesList? capabilities input world atoms =
      some remaining) :
    (∀ {index : Nat} {capability : Lower.BindingCap} {selected : RVal},
        remaining[index]? = some capability →
        source[index]? = some selected →
        CapabilityHolds store capability selected) ∧
      IxIR1.Sim.RootOwnership store
        (consumedRoots ++ IxIR1.Sim.rootsFor world values ++
          rootsForCapabilities remaining.toList source ++ suffixRoots) := by
  induction resolved generalizing capabilities consumedRoots with
  | nil =>
      simp only [Lower.consumeCapabilitiesList?] at consumed
      injection consumed with remainingEq
      subst remaining
      refine ⟨holds, ?_⟩
      simpa [IxIR1.Sim.rootsFor, List.append_assoc] using ownership
  | @cons atom value atoms values head tail ih =>
      simp only [Lower.consumeCapabilitiesList?] at consumed
      cases step : Lower.consumeCapability? capabilities input world atom with
      | none => simp [step] at consumed
      | some nextCapabilities =>
          simp only [step] at consumed
          obtain ⟨nextHolds, nextOwnership⟩ :=
            consumeCapability_ownership holds ownership head step
          have recursive := ih nextHolds nextOwnership consumed
          refine ⟨recursive.1, ?_⟩
          simpa [IxIR1.Sim.rootsFor, List.append_assoc] using recursive.2

/-- Heterogeneous call-argument consumption accumulates one exact root in
the world of each owned parameter, ahead of the surviving caller roots. -/
private theorem consumeCapabilitiesWorlds_ownership
    {store : IxIR1.Store} {source : List RVal}
    {capabilities remaining : Array Lower.BindingCap}
    {input : Array (Option Atom)}
    {worlds : List Ix.Compiler.Ixon.Owned}
    {atoms : List IxIR1.Atom} {values : List RVal}
    {consumedRoots suffixRoots : List IxIR1.Sim.Root}
    (holds : ∀ {index : Nat} {capability : Lower.BindingCap}
        {selected : RVal},
      capabilities[index]? = some capability →
      source[index]? = some selected →
      CapabilityHolds store capability selected)
    (ownership : IxIR1.Sim.RootOwnership store
      (consumedRoots ++ rootsForCapabilities capabilities.toList source ++
        suffixRoots))
    (resolved : SourceAtomsResolve source atoms values)
    (consumed : Lower.consumeCapabilitiesWorlds? capabilities input worlds
      atoms = some remaining) :
    (∀ {index : Nat} {capability : Lower.BindingCap} {selected : RVal},
        remaining[index]? = some capability →
        source[index]? = some selected →
        CapabilityHolds store capability selected) ∧
      IxIR1.Sim.RootOwnership store
        (consumedRoots ++ IxIR1.Sim.rootsForWorlds worlds values ++
          rootsForCapabilities remaining.toList source ++ suffixRoots) := by
  induction resolved generalizing capabilities worlds consumedRoots with
  | nil =>
      cases worlds with
      | nil =>
          simp only [Lower.consumeCapabilitiesWorlds?] at consumed
          injection consumed with remainingEq
          subst remaining
          exact ⟨holds, by simpa [IxIR1.Sim.rootsForWorlds,
            List.append_assoc] using ownership⟩
      | cons world worlds =>
          simp [Lower.consumeCapabilitiesWorlds?] at consumed
  | @cons atom value atoms values head tail ih =>
      cases worlds with
      | nil => simp [Lower.consumeCapabilitiesWorlds?] at consumed
      | cons world worlds =>
          simp only [Lower.consumeCapabilitiesWorlds?] at consumed
          cases step : Lower.consumeCapability? capabilities input world atom with
          | none => simp [step] at consumed
          | some nextCapabilities =>
              simp only [step] at consumed
              obtain ⟨nextHolds, nextOwnership⟩ :=
                consumeCapability_ownership holds ownership head step
              have recursive := ih nextHolds nextOwnership consumed
              refine ⟨recursive.1, ?_⟩
              simpa [IxIR1.Sim.rootsForWorlds, List.append_assoc] using
                recursive.2

/-- Successful projection of the baseline owned call ABI identifies the
entry capability vector as the reversed parameter-world telescope. -/
private theorem ownedParameterWorlds?_entryCapabilities
    {signature : Signature} {worlds : List Ix.Compiler.Ixon.Owned}
    (projected : Lower.ownedParameterWorlds? signature.params.toList =
      some worlds) :
    (Lower.entryCapabilities signature).toList =
      worlds.reverse.map Lower.BindingCap.owned := by
  unfold Lower.entryCapabilities
  have listShape : ∀ {parameters : List Param}
      {parameterWorlds : List Ix.Compiler.Ixon.Owned},
      Lower.ownedParameterWorlds? parameters = some parameterWorlds →
      parameters.map (fun parameter =>
        match parameter.passing with
        | .owned => Lower.BindingCap.owned parameter.world
        | .borrowed => Lower.BindingCap.borrowed parameter.world .caller) =
        parameterWorlds.map Lower.BindingCap.owned := by
    intro parameters parameterWorlds projection
    induction parameters generalizing parameterWorlds with
    | nil =>
        simp [Lower.ownedParameterWorlds?] at projection
        subst parameterWorlds
        simp
    | cons parameter rest ih =>
        rcases parameter with ⟨world, passing⟩
        cases passing with
        | borrowed =>
            simp [Lower.ownedParameterWorlds?] at projection
        | owned =>
            simp only [Lower.ownedParameterWorlds?, beq_self_eq_true,
              if_true] at projection
            cases restProjection : Lower.ownedParameterWorlds? rest with
            | none => simp [restProjection] at projection
            | some restWorlds =>
                simp only [restProjection, Option.map_some,
                  Option.some.injEq] at projection
                subst parameterWorlds
                simp [ih restProjection]
  change (signature.params.toList.reverse.map (fun parameter =>
      match parameter.passing with
      | .owned => Lower.BindingCap.owned parameter.world
      | .borrowed => Lower.BindingCap.borrowed parameter.world .caller)) =
    worlds.reverse.map Lower.BindingCap.owned
  calc
    _ = (signature.params.toList.map (fun parameter =>
        match parameter.passing with
        | .owned => Lower.BindingCap.owned parameter.world
        | .borrowed => Lower.BindingCap.borrowed parameter.world
            .caller)).reverse := List.map_reverse
    _ = (worlds.map Lower.BindingCap.owned).reverse :=
      congrArg List.reverse (listShape projected)
    _ = _ := List.map_reverse.symm

/-- Owned capabilities and a same-length value vector denote the canonical
heterogeneous root telescope. -/
private theorem rootsForCapabilities_owned
    {worlds : List Ix.Compiler.Ixon.Owned} {values : List RVal}
    (length : worlds.length = values.length) :
    rootsForCapabilities (worlds.map Lower.BindingCap.owned) values =
      IxIR1.Sim.rootsForWorlds worlds values := by
  induction worlds generalizing values with
  | nil =>
      cases values with
      | nil => rfl
      | cons value values => simp at length
  | cons world worlds ih =>
      cases values with
      | nil => simp at length
      | cons value values =>
          simp only [List.length_cons, Nat.succ.injEq] at length
          simp [rootsForCapabilities, IxIR1.Sim.rootsForWorlds, ih length]

/-- Reversing two same-length heterogeneous telescopes reverses their root
list without changing any world/value pairing. -/
private theorem rootsForWorlds_reverse
    {worlds : List Ix.Compiler.Ixon.Owned} {values : List RVal}
    (length : worlds.length = values.length) :
    IxIR1.Sim.rootsForWorlds worlds.reverse values.reverse =
      (IxIR1.Sim.rootsForWorlds worlds values).reverse := by
  induction worlds generalizing values with
  | nil =>
      cases values with
      | nil => rfl
      | cons value values => simp at length
  | cons world worlds ih =>
      cases values with
      | nil => simp at length
      | cons value values =>
          simp only [List.length_cons, Nat.succ.injEq] at length
          rw [List.reverse_cons, List.reverse_cons]
          have appendShape : ∀ {leftWorlds : List Ix.Compiler.Ixon.Owned}
              {leftValues : List RVal},
              leftWorlds.length = leftValues.length →
              IxIR1.Sim.rootsForWorlds (leftWorlds ++ [world])
                  (leftValues ++ [value]) =
                IxIR1.Sim.rootsForWorlds leftWorlds leftValues ++
                  [⟨world, value⟩] := by
            intro leftWorlds leftValues leftLength
            induction leftWorlds generalizing leftValues with
            | nil =>
                cases leftValues with
                | nil => rfl
                | cons head tail => simp at leftLength
            | cons headWorld tailWorlds appendIh =>
                cases leftValues with
                | nil => simp at leftLength
                | cons headValue tailValues =>
                    simp only [List.length_cons, Nat.succ.injEq] at leftLength
                    simp [IxIR1.Sim.rootsForWorlds,
                      appendIh leftLength]
          rw [appendShape (by simpa using length), ih length]
          simp [IxIR1.Sim.rootsForWorlds]

/-- The exact entry roots are a presentation-order permutation of the
source-order call argument roots. -/
private theorem entryRoots_perm
    {signature : Signature} {worlds : List Ix.Compiler.Ixon.Owned}
    {values : List RVal}
    (projected : Lower.ownedParameterWorlds? signature.params.toList =
      some worlds)
    (length : worlds.length = values.length) :
    (rootsForCapabilities (Lower.entryCapabilities signature).toList
      values.reverse).Perm (IxIR1.Sim.rootsForWorlds worlds values) := by
  rw [ownedParameterWorlds?_entryCapabilities projected]
  rw [rootsForCapabilities_owned (by simpa using length)]
  rw [rootsForWorlds_reverse length]
  exact List.reverse_perm _

/-- If the call audit says no local owner survives, the dynamic root
projection of that capability vector is empty for every source environment. -/
private theorem rootsForCapabilities_eq_nil_of_noOwnedRoots
    {capabilities : Array Lower.BindingCap} {source : List RVal}
    (noOwners : Lower.noOwnedRoots capabilities = true) :
    rootsForCapabilities capabilities.toList source = [] := by
  unfold Lower.noOwnedRoots at noOwners
  have listResult : ∀ (caps : List Lower.BindingCap) (values : List RVal),
      caps.all (fun capability => !capability.hasOwnedRoot) = true →
      rootsForCapabilities caps values = [] := by
    intro caps
    induction caps with
    | nil => intro values _; rfl
    | cons capability rest ih =>
        intro values noOwners
        cases values with
        | nil => simp [rootsForCapabilities]
        | cons value values =>
            simp only [List.all_cons, Bool.and_eq_true] at noOwners
            cases capability with
            | owned world =>
                simp [Lower.BindingCap.hasOwnedRoot] at noOwners
            | scalar =>
                simpa [rootsForCapabilities] using ih values noOwners.2
            | borrowed world lender =>
                simpa [rootsForCapabilities] using ih values noOwners.2
            | dead =>
                simpa [rootsForCapabilities] using ih values noOwners.2
  exact listResult capabilities.toList source noOwners

/-- Exact checked call consumption constructs the complete callee-entry
ownership invariant. Surviving caller owners become the suspended frame
suffix; transferred argument owners become the callee's canonical local
roots. -/
theorem callEntryInvariant
    {store : IxIR1.Store} {source : List RVal}
    {input calleeInput : Array (Option Atom)}
    {capabilities remaining : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root} {signature : Signature}
    {arguments : Array IxIR1.Atom} {values : List RVal}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    (resolved : IxIR1.resolveAtoms source arguments = .ok values)
    (consumed : Lower.callRemainingCapabilities? capabilities input signature
      arguments = some remaining) :
    SourceOwnershipInvariant store values.reverse calleeInput
      (Lower.entryCapabilities signature)
      (rootsForCapabilities remaining.toList source ++ frameRoots) := by
  unfold Lower.callRemainingCapabilities? at consumed
  cases projectedEq : Lower.ownedParameterWorlds?
      signature.params.toList with
  | none => simp [projectedEq] at consumed
  | some worlds =>
      simp only [projectedEq, Option.bind_eq_bind, Option.bind_some] at consumed
      have resolvedRelation := SourceAtomsResolve.ofResolveAtoms resolved
      have valueLength : arguments.toList.length = values.length :=
        SourceAtomsResolve.length resolvedRelation
      have worldLength : worlds.length = arguments.toList.length :=
        Lower.consumeCapabilitiesWorlds?_length consumed
      have worldsValuesLength : worlds.length = values.length :=
        worldLength.trans valueLength
      obtain ⟨remainingHolds, readyOwnership⟩ :=
        consumeCapabilitiesWorlds_ownership
          (consumedRoots := []) (suffixRoots := frameRoots)
          invariant.holds (by simpa using invariant.ownership)
          resolvedRelation consumed
      have entryShape := ownedParameterWorlds?_entryCapabilities projectedEq
      have entrySize : (Lower.entryCapabilities signature).size =
          worlds.length := by
        simpa using congrArg List.length entryShape
      have entryPerm := entryRoots_perm projectedEq worldsValuesLength
      have entryOwnership : IxIR1.Sim.RootOwnership store
          (rootsForCapabilities (Lower.entryCapabilities signature).toList
              values.reverse ++
            (rootsForCapabilities remaining.toList source ++ frameRoots)) := by
        apply readyOwnership.perm
        simpa [List.append_assoc] using
          entryPerm.symm.append_right
            (rootsForCapabilities remaining.toList source ++ frameRoots)
      refine ⟨?_, ?_, entryOwnership, ?_⟩
      · simpa using worldsValuesLength.symm.trans entrySize.symm
      · intro index capability selected capabilityAt selectedAt
        have capabilityListAt :
            (Lower.entryCapabilities signature).toList[index]? =
              some capability := by
          simpa using capabilityAt
        have capabilityMember : capability ∈
            (Lower.entryCapabilities signature).toList :=
          List.mem_of_getElem? capabilityListAt
        rw [entryShape] at capabilityMember
        simp only [List.mem_map] at capabilityMember
        obtain ⟨world, _, capabilityEq⟩ := capabilityMember
        subst capability
        have rootMember := rootsForCapabilities_owned_mem capabilityAt
          selectedAt
        exact entryOwnership.roots_world ⟨world, selected⟩
          (List.mem_append_left _ rootMember)
      · intro index world lender selected capabilityAt selectedAt
        have capabilityListAt :
            (Lower.entryCapabilities signature).toList[index]? =
              some (.borrowed world lender) := by
          simpa using capabilityAt
        have capabilityMember : (.borrowed world lender : Lower.BindingCap) ∈
            (Lower.entryCapabilities signature).toList :=
          List.mem_of_getElem? capabilityListAt
        rw [entryShape] at capabilityMember
        simp at capabilityMember

/-- Ordinary-call capability consumption preserves the pointwise semantic
meaning and array shape of every surviving caller slot. This is the exact
fact needed to justify the caller frame while it is suspended. -/
theorem callRemainingHolds
    {store : IxIR1.Store} {source : List RVal}
    {input : Array (Option Atom)}
    {capabilities remaining : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root} {signature : Signature}
    {arguments : Array IxIR1.Atom} {values : List RVal}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    (resolved : IxIR1.resolveAtoms source arguments = .ok values)
    (consumed : Lower.callRemainingCapabilities? capabilities input signature
      arguments = some remaining) :
    remaining.size = capabilities.size ∧
      ∀ {index : Nat} {capability : Lower.BindingCap} {selected : RVal},
        remaining[index]? = some capability →
        source[index]? = some selected →
        CapabilityHolds store capability selected := by
  unfold Lower.callRemainingCapabilities? at consumed
  cases projectedEq : Lower.ownedParameterWorlds?
      signature.params.toList with
  | none => simp [projectedEq] at consumed
  | some worlds =>
      simp only [projectedEq, Option.bind_eq_bind, Option.bind_some] at consumed
      have resolvedRelation := SourceAtomsResolve.ofResolveAtoms resolved
      obtain ⟨remainingHolds, _⟩ :=
        consumeCapabilitiesWorlds_ownership
          (consumedRoots := []) (suffixRoots := frameRoots)
          invariant.holds (by simpa using invariant.ownership)
          resolvedRelation consumed
      exact ⟨Lower.consumeCapabilitiesWorlds?_size consumed, remainingHolds⟩

/-- Dynamic-application capability consumption exposes the exact shared
root multiset consumed by the function and argument operands.  The surviving
capability roots and framed roots remain as an explicit suffix, so evaluator
progress can be reconstructed without assuming a source execution. -/
theorem applyInputOwnership
    {store : IxIR1.Store} {source : List RVal}
    {input : Array (Option Atom)}
    {capabilities afterFunction remaining : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    {function : IxIR1.Atom} {functionValue : RVal}
    {arguments : Array IxIR1.Atom} {values : List RVal}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    (functionResolved : IxIR1.resolveAtom source function = .ok functionValue)
    (argumentsResolved : IxIR1.resolveAtoms source arguments = .ok values)
    (functionConsumed : Lower.consumeCapability? capabilities input .shared
      function = some afterFunction)
    (argumentsConsumed : Lower.consumeCapabilitiesList? afterFunction input
      .shared arguments.toList = some remaining) :
    IxIR1.Sim.RootOwnership store
      (⟨.shared, functionValue⟩ ::
        IxIR1.Sim.rootsFor .shared values ++
          rootsForCapabilities remaining.toList source ++ frameRoots) := by
  obtain ⟨afterFunctionHolds, afterFunctionOwnership⟩ :=
    consumeCapability_ownership (consumedRoots := [])
      (suffixRoots := frameRoots) invariant.holds
      (by simpa using invariant.ownership) functionResolved functionConsumed
  have resolvedRelation := SourceAtomsResolve.ofResolveAtoms
    argumentsResolved
  obtain ⟨_remainingHolds, readyOwnership⟩ :=
    consumeCapabilitiesList_ownership
      (consumedRoots := [(⟨.shared, functionValue⟩ : IxIR1.Sim.Root)])
      (suffixRoots := frameRoots) afterFunctionHolds
      (by simpa using afterFunctionOwnership) resolvedRelation
      argumentsConsumed
  simpa [List.append_assoc] using readyOwnership

/-- Dynamic-application capability consumption preserves the pointwise
semantic meaning and array shape of every surviving caller slot. This is the
shared-function analogue of `callRemainingHolds`, used to justify a caller
frame suspended while a PAP callee executes. -/
theorem applyRemainingHolds
    {store : IxIR1.Store} {source : List RVal}
    {input : Array (Option Atom)}
    {capabilities afterFunction remaining : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    {function : IxIR1.Atom} {functionValue : RVal}
    {arguments : Array IxIR1.Atom} {values : List RVal}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    (functionResolved : IxIR1.resolveAtom source function = .ok functionValue)
    (argumentsResolved : IxIR1.resolveAtoms source arguments = .ok values)
    (functionConsumed : Lower.consumeCapability? capabilities input .shared
      function = some afterFunction)
    (argumentsConsumed : Lower.consumeCapabilitiesList? afterFunction input
      .shared arguments.toList = some remaining) :
    remaining.size = capabilities.size ∧
      ∀ {index : Nat} {capability : Lower.BindingCap} {selected : RVal},
        remaining[index]? = some capability →
        source[index]? = some selected →
        CapabilityHolds store capability selected := by
  obtain ⟨afterFunctionHolds, afterFunctionOwnership⟩ :=
    consumeCapability_ownership (consumedRoots := [])
      (suffixRoots := frameRoots) invariant.holds
      (by simpa using invariant.ownership) functionResolved functionConsumed
  have resolvedRelation := SourceAtomsResolve.ofResolveAtoms argumentsResolved
  obtain ⟨remainingHolds, _⟩ :=
    consumeCapabilitiesList_ownership
      (consumedRoots := [(⟨.shared, functionValue⟩ : IxIR1.Sim.Root)])
      (suffixRoots := frameRoots) afterFunctionHolds
      (by simpa using afterFunctionOwnership) resolvedRelation
      argumentsConsumed
  exact ⟨(Lower.consumeCapabilitiesList?_size argumentsConsumed).trans
    (Lower.consumeCapability?_size functionConsumed), remainingHolds⟩

/-- A capability vector accepted by the ordinary-call suspension audit has
no borrowed slot at any index. -/
private theorem borrowed_impossible_of_noBorrows
    {capabilities : Array Lower.BindingCap}
    (noBorrows : Lower.noBorrows capabilities = true)
    {index : Nat} {world : Ix.Compiler.Ixon.Owned}
    {lender : BorrowLender}
    (capabilityAt : capabilities[index]? = some (.borrowed world lender)) :
    False := by
  have listAt : capabilities.toList[index]? =
      some (.borrowed world lender) := by
    simpa using capabilityAt
  have member : (.borrowed world lender : Lower.BindingCap) ∈
      capabilities.toList := List.mem_of_getElem? listAt
  unfold Lower.noBorrows at noBorrows
  have point := List.all_eq_true.mp noBorrows _ member
  simp [Lower.BindingCap.isBorrowed] at point

/-- Reinstall an ordinary caller after its callee returns. Scalar/dead facts
survive independently of the heap, surviving owners are justified by the
returned framed root ownership, and the call audit rules out suspended
borrows. -/
theorem callResultInvariant
    {beforeStore afterStore : IxIR1.Store} {source : List RVal}
    {input afterInput : Array (Option Atom)}
    {capabilities remaining : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root} {signature : Signature}
    {arguments : Array IxIR1.Atom} {values : List RVal} {value : RVal}
    (invariant : SourceOwnershipInvariant beforeStore source input capabilities
      frameRoots)
    (resolved : IxIR1.resolveAtoms source arguments = .ok values)
    (consumed : Lower.callRemainingCapabilities? capabilities input signature
      arguments = some remaining)
    (noBorrows : Lower.noBorrows remaining = true)
    (resultOwnership : IxIR1.Sim.RootOwnership afterStore
      (⟨signature.result, value⟩ ::
        (rootsForCapabilities remaining.toList source ++ frameRoots))) :
    SourceOwnershipInvariant afterStore (value :: source) afterInput
      (#[.owned signature.result] ++ remaining) frameRoots := by
  unfold Lower.callRemainingCapabilities? at consumed
  cases projectedEq : Lower.ownedParameterWorlds?
      signature.params.toList with
  | none => simp [projectedEq] at consumed
  | some worlds =>
      simp only [projectedEq, Option.bind_eq_bind, Option.bind_some] at consumed
      have resolvedRelation := SourceAtomsResolve.ofResolveAtoms resolved
      obtain ⟨remainingHolds, _⟩ := consumeCapabilitiesWorlds_ownership
        (consumedRoots := []) (suffixRoots := frameRoots) invariant.holds
        (by simpa using invariant.ownership) resolvedRelation consumed
      have remainingSize := Lower.consumeCapabilitiesWorlds?_size consumed
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Array.size_append, remainingSize, invariant.length,
          Nat.add_comm]
      · intro index capability selected capabilityAt selectedAt
        cases index with
        | zero =>
            simp [Array.getElem?_append] at capabilityAt selectedAt
            subst capability
            subst selected
            exact resultOwnership.roots_world
              ⟨signature.result, value⟩ (by simp)
        | succ index =>
            simp [Array.getElem?_append] at capabilityAt selectedAt
            cases capability with
            | scalar =>
                simpa [CapabilityHolds] using
                  remainingHolds capabilityAt selectedAt
            | dead => trivial
            | borrowed world lender =>
                exact False.elim
                  (borrowed_impossible_of_noBorrows noBorrows capabilityAt)
            | owned world =>
                exact resultOwnership.roots_world ⟨world, selected⟩ (by
                  simp [rootsForCapabilities_owned_mem capabilityAt selectedAt])
      · simpa [rootsForCapabilities, List.append_assoc] using resultOwnership
      · intro index world lender selected capabilityAt selectedAt
        cases index with
        | zero => simp [Array.getElem?_append] at capabilityAt
        | succ index =>
            simp [Array.getElem?_append] at capabilityAt selectedAt
            exact False.elim
              (borrowed_impossible_of_noBorrows noBorrows capabilityAt)

/-- Sequential owned-boundary consumption preserves every surviving borrow's
exact lender provenance. -/
private theorem consumeCapabilitiesList_borrows
    {store : IxIR1.Store} {source : List RVal}
    {input : Array (Option Atom)}
    {capabilities remaining : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (oldBorrows : ∀ {index : Nat} {world : Ix.Compiler.Ixon.Owned}
        {lender : BorrowLender} {value : RVal},
      capabilities[index]? = some (.borrowed world lender) →
      source[index]? = some value →
      BorrowProvenance store source input capabilities frameRoots world lender
        value)
    {world : Ix.Compiler.Ixon.Owned} {atoms : List IxIR1.Atom}
    (consumed : Lower.consumeCapabilitiesList? capabilities input world atoms =
      some remaining) :
    ∀ {index : Nat} {borrowWorld : Ix.Compiler.Ixon.Owned}
        {lender : BorrowLender} {value : RVal},
      remaining[index]? = some (.borrowed borrowWorld lender) →
      source[index]? = some value →
      BorrowProvenance store source input remaining frameRoots borrowWorld
        lender value := by
  induction atoms generalizing capabilities with
  | nil =>
      simp only [Lower.consumeCapabilitiesList?] at consumed
      injection consumed with remainingEq
      subst remaining
      exact oldBorrows
  | cons atom atoms ih =>
      simp only [Lower.consumeCapabilitiesList?] at consumed
      cases step : Lower.consumeCapability? capabilities input world atom with
      | none => simp [step] at consumed
      | some nextCapabilities =>
          simp only [step] at consumed
          exact ih (consumeCapability_borrows oldBorrows step) consumed

/-- After one owner has been consumed, a destructive store restriction and
the exact surviving roots suffice to bind the erased scalar result and rebuild
all pointwise capability and borrow facts. -/
private theorem prependScalarAfterRestriction
    {before after : IxIR1.Store} {source : List RVal}
    {input afterInput : Array (Option Atom)}
    {capabilities remaining : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant before source input capabilities
      frameRoots)
    {headAtom : Atom}
    (forgets : Lower.InputMap.Forgets afterInput
      (#[some headAtom] ++ input))
    (afterOwners : OwnedInputRegisters afterInput
      (#[.scalar] ++ remaining))
    {world : Ix.Compiler.Ixon.Owned} {atom : IxIR1.Atom} {value : RVal}
    (resolved : IxIR1.resolveAtom source atom = .ok value)
    (consumed : Lower.consumeCapability? capabilities input world atom =
      some remaining)
    (restriction : IxIR1.Sim.StoreGraphRestricts before after)
    (ownership : IxIR1.Sim.RootOwnership after
      (rootsForCapabilities remaining.toList source ++ frameRoots)) :
    SourceOwnershipInvariant after (.erased :: source) afterInput
      (#[.scalar] ++ remaining) frameRoots := by
  obtain ⟨remainingHolds, _⟩ :=
    consumeCapability_ownership (consumedRoots := [])
      (suffixRoots := frameRoots) invariant.holds
      (by simpa using invariant.ownership) resolved consumed
  have remainingBorrows :
      ∀ {index : Nat} {borrowWorld : Ix.Compiler.Ixon.Owned}
          {lender : BorrowLender} {borrowedValue : RVal},
        remaining[index]? = some (.borrowed borrowWorld lender) →
        source[index]? = some borrowedValue →
        BorrowProvenance before source input remaining frameRoots borrowWorld
          lender borrowedValue :=
    consumeCapability_borrows invariant.borrows consumed
  have postBorrows :
      ∀ {index : Nat} {borrowWorld : Ix.Compiler.Ixon.Owned}
          {lender : BorrowLender} {borrowedValue : RVal},
        remaining[index]? = some (.borrowed borrowWorld lender) →
        source[index]? = some borrowedValue →
        BorrowProvenance after source input remaining frameRoots borrowWorld
          lender borrowedValue := by
    intro index borrowWorld lender borrowedValue capabilityAt valueAt
    exact BorrowProvenance.ofRestricts restriction ownership
      (remainingBorrows capabilityAt valueAt)
  have remainingSize : remaining.size = capabilities.size :=
    Lower.consumeCapability?_size consumed
  refine ⟨by
      simp [Array.size_append, invariant.length, remainingSize, Nat.add_comm],
    ?_, ?_, ?_⟩
  · intro index capability selected capabilityAt selectedAt
    cases index with
    | zero =>
        simp [Array.getElem?_append] at capabilityAt selectedAt
        subst capability
        subst selected
        rfl
    | succ index =>
        simp [Array.getElem?_append] at capabilityAt selectedAt
        cases capability with
        | scalar => exact remainingHolds capabilityAt selectedAt
        | dead => trivial
        | owned actual =>
            exact ownership.roots_world ⟨actual, selected⟩
              (List.mem_append_left _
                (rootsForCapabilities_owned_mem capabilityAt selectedAt))
        | borrowed actual lender =>
            exact (postBorrows capabilityAt selectedAt).hasWorld ownership
  · simpa [rootsForCapabilities] using ownership
  · exact BorrowProvenance.prependNonBorrowed
      (IxIR1.Sim.StoreGraphExtends.refl after) postBorrows
      (by intros; simp) forgets afterOwners

/-- Exact shared destruction consumes its selected shared owner, transports all
surviving lender paths through the restricted heap, and binds the erased
result. -/
theorem drop {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {sourceCurrent : IxIR1.FnDef} {store outputStore : IxIR1.Store}
    {source : List RVal}
    {input afterInput : Array (Option Atom)}
    {capabilities afterCapabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    {headAtom : Atom}
    (forgets : Lower.InputMap.Forgets afterInput
      (#[some headAtom] ++ input))
    (afterOwners : OwnedInputRegisters afterInput afterCapabilities)
    {atom : IxIR1.Atom} {result : RVal}
    (transition : Lower.destructionCapabilities? capabilities input .shared
      atom = some afterCapabilities)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent
      store source (.drop atom) = .ok (outputStore, result)) :
    SourceOwnershipInvariant outputStore (result :: source) afterInput
      afterCapabilities frameRoots := by
  obtain ⟨value, resolved, _⟩ := IxIR1.runOp_drop_success operationRun
  cases consumedEq : Lower.consumeCapability? capabilities input .shared atom with
  | none =>
      simp [Lower.destructionCapabilities?, consumedEq] at transition
  | some remaining =>
      have afterEq : #[.scalar] ++ remaining = afterCapabilities := by
        simpa [Lower.destructionCapabilities?, consumedEq] using transition
      subst afterCapabilities
      obtain ⟨_, readyOwnership⟩ :=
        consumeCapability_ownership (consumedRoots := [])
          (suffixRoots := frameRoots) invariant.holds
          (by simpa using invariant.ownership) resolved consumedEq
      have readyOwnership' : IxIR1.Sim.RootOwnership store
          (⟨.shared, value⟩ ::
            (rootsForCapabilities remaining.toList source ++ frameRoots)) := by
        simpa [List.append_assoc] using readyOwnership
      obtain ⟨resultEq, restriction, postOwnership⟩ :=
        IxIR1.Sim.runOp_drop_value_owned_restricts resolved readyOwnership'
          operationRun
      subst result
      exact prependScalarAfterRestriction invariant forgets afterOwners
        resolved consumedEq restriction postOwnership

/-- Exact unique recursive destruction has the same ownership interface as
shared destruction, specialized to a unique consumed root. -/
theorem dropU {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {sourceCurrent : IxIR1.FnDef} {store outputStore : IxIR1.Store}
    {source : List RVal}
    {input afterInput : Array (Option Atom)}
    {capabilities afterCapabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    {headAtom : Atom}
    (forgets : Lower.InputMap.Forgets afterInput
      (#[some headAtom] ++ input))
    (afterOwners : OwnedInputRegisters afterInput afterCapabilities)
    {atom : IxIR1.Atom} {result : RVal}
    (transition : Lower.destructionCapabilities? capabilities input .unique
      atom = some afterCapabilities)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent
      store source (.dropU atom) = .ok (outputStore, result)) :
    SourceOwnershipInvariant outputStore (result :: source) afterInput
      afterCapabilities frameRoots := by
  obtain ⟨value, resolved, _⟩ := IxIR1.runOp_dropU_success operationRun
  cases consumedEq : Lower.consumeCapability? capabilities input .unique atom with
  | none =>
      simp [Lower.destructionCapabilities?, consumedEq] at transition
  | some remaining =>
      have afterEq : #[.scalar] ++ remaining = afterCapabilities := by
        simpa [Lower.destructionCapabilities?, consumedEq] using transition
      subst afterCapabilities
      obtain ⟨_, readyOwnership⟩ :=
        consumeCapability_ownership (consumedRoots := [])
          (suffixRoots := frameRoots) invariant.holds
          (by simpa using invariant.ownership) resolved consumedEq
      have readyOwnership' : IxIR1.Sim.RootOwnership store
          (⟨.unique, value⟩ ::
            (rootsForCapabilities remaining.toList source ++ frameRoots)) := by
        simpa [List.append_assoc] using readyOwnership
      obtain ⟨resultEq, restriction, postOwnership⟩ :=
        IxIR1.Sim.runOp_dropU_value_owned_restricts resolved readyOwnership'
          operationRun
      subst result
      exact prependScalarAfterRestriction invariant forgets afterOwners
        resolved consumedEq restriction postOwnership

/-- Checked scalar-leaf shallow free consumes the selected unique owner.  The
freed constructor's scalar fields contribute no surviving heap roots, while
all unrelated owners and lender paths transport through the one-node kill. -/
theorem free {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {sourceCurrent : IxIR1.FnDef} {store outputStore : IxIR1.Store}
    {source : List RVal}
    {input afterInput : Array (Option Atom)}
    {capabilities afterCapabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    {headAtom : Atom}
    (forgets : Lower.InputMap.Forgets afterInput
      (#[some headAtom] ++ input))
    (afterOwners : OwnedInputRegisters afterInput afterCapabilities)
    {atom : IxIR1.Atom} {location : Nat} {box : IxIR1.NodeBox}
    {identity : CtorId} {fields : Array RVal} {result : RVal}
    (transition : Lower.destructionCapabilities? capabilities input .unique
      atom = some afterCapabilities)
    (resolved : IxIR1.resolveAtom source atom = .ok (.loc location))
    (sourceGet : store.get? location = some box)
    (unique : box.world = .unique)
    (node : box.node = .ctorN identity fields)
    (scalarFields : fields.all IxIR1.RVal.isScalar = true)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent
      store source (.free atom) = .ok (outputStore, result)) :
    SourceOwnershipInvariant outputStore (result :: source) afterInput
      afterCapabilities frameRoots := by
  cases consumedEq : Lower.consumeCapability? capabilities input .unique atom with
  | none =>
      simp [Lower.destructionCapabilities?, consumedEq] at transition
  | some remaining =>
      have afterEq : #[.scalar] ++ remaining = afterCapabilities := by
        simpa [Lower.destructionCapabilities?, consumedEq] using transition
      subst afterCapabilities
      obtain ⟨_, readyOwnership⟩ :=
        consumeCapability_ownership (consumedRoots := [])
          (suffixRoots := frameRoots) invariant.holds
          (by simpa using invariant.ownership) resolved consumedEq
      have readyOwnership' : IxIR1.Sim.RootOwnership store
          (⟨.unique, (.loc location : RVal)⟩ ::
            (rootsForCapabilities remaining.toList source ++ frameRoots)) := by
        simpa [List.append_assoc] using readyOwnership
      cases box with
      | mk actualWorld rc actualNode =>
          simp only at unique node sourceGet
          subst actualWorld
          have rcOne : rc = 1 := (readyOwnership'.counts sourceGet).1
          subst rc
          have killedOwnership := readyOwnership'.killUniqueOne sourceGet
          have scalarChildren :
              (IxIR1.Sim.nodeChildren actualNode).all IxIR1.RVal.isScalar =
                true := by
            rw [node]
            simpa [IxIR1.Sim.nodeChildren] using scalarFields
          have postOwnership : IxIR1.Sim.RootOwnership
              (store.kill location)
              (rootsForCapabilities remaining.toList source ++ frameRoots) :=
            killedOwnership.dropScalars scalarChildren
          have expectedRun := IxIR1.Sim.runOp_free
            (ctx := sourceContext) (fuel := sourceFuel) (cur := sourceCurrent)
            resolved sourceGet
          have outputEq :
              (store.kill location, (.erased : RVal)) =
                (outputStore, result) :=
            Except.ok.inj (expectedRun.symm.trans operationRun)
          have outputStoreEq : store.kill location = outputStore :=
            congrArg Prod.fst outputEq
          have resultEq : (.erased : RVal) = result :=
            congrArg Prod.snd outputEq
          subst outputStore
          subst result
          exact prependScalarAfterRestriction invariant forgets afterOwners
            resolved consumedEq (IxIR1.Sim.StoreGraphRestricts.kill sourceGet)
              postOwnership

/-- The checked producer capability vector and the dynamic ownership
invariant establish every field world needed by target allocation. -/
theorem resolveAtoms_hasWorld
    {store : IxIR1.Store} {source : List RVal}
    {position : Lower.PositionTrace}
    {site : Lower.SourceSite} {block : BlockId} {index : Nat}
    {input : Array (Option Atom)} {world : Ix.Compiler.Ixon.Owned}
    {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input
      position.sourceCapabilities frameRoots)
    {arguments : Array IxIR1.Atom} {values : List RVal}
    (positionMatch : position.allocationMatches site block index input world
      arguments = true)
    (resolved : IxIR1.resolveAtoms source arguments = .ok values) :
    ∀ value ∈ values, IxIR1.Sim.HasWorld store world value := by
  apply SourceAtomsResolve.worlds invariant
    (SourceAtomsResolve.ofResolveAtoms resolved)
  intro atom member
  exact position.sourceCapability_canConsume_of_allocationMatch
    positionMatch member

/-- Before a checked allocation mutates the store, its sequential capability
consumption already exposes the exact constructor-field roots followed by all
surviving source and suspended-frame roots.  This is the pre-allocation
accounting boundary used by reuse proofs that need a root partition rather
than only the post-allocation invariant. -/
theorem allocationReadyOwnership
    {store : IxIR1.Store} {source values : List RVal}
    {input : Array (Option Atom)}
    {capabilities afterCapabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    {world : Ix.Compiler.Ixon.Owned} {arguments : Array IxIR1.Atom}
    (resolved : IxIR1.resolveAtoms source arguments = .ok values)
    (transition : Lower.allocationCapabilities? capabilities input world
      arguments = some afterCapabilities) :
    ∃ remaining,
      Lower.consumeCapabilitiesList? capabilities input world
          arguments.toList = some remaining ∧
      afterCapabilities = #[.owned world] ++ remaining ∧
      IxIR1.Sim.RootOwnership store
        (IxIR1.Sim.rootsFor world values ++
          rootsForCapabilities remaining.toList source ++ frameRoots) := by
  cases consumeEq : Lower.consumeCapabilitiesList? capabilities input world
      arguments.toList with
  | none =>
      simp [Lower.allocationCapabilities?, consumeEq] at transition
  | some remaining =>
      have afterEq : #[.owned world] ++ remaining = afterCapabilities := by
        simpa [Lower.allocationCapabilities?, consumeEq] using transition
      have resolvedRelation := SourceAtomsResolve.ofResolveAtoms resolved
      obtain ⟨_remainingHolds, readyOwnership⟩ :=
        consumeCapabilitiesList_ownership (consumedRoots := [])
          (suffixRoots := frameRoots) invariant.holds
          (by simpa using invariant.ownership) resolvedRelation consumeEq
      exact ⟨remaining, rfl, afterEq.symm,
        by simpa [List.append_assoc] using readyOwnership⟩

/-- The exact producer ordinary-allocation transition consumes every field
owner into the new constructor and exposes ownership of the fresh result.
All surviving source capability facts transport across the append allocation. -/
theorem alloc {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {sourceCurrent : IxIR1.FnDef} {store outputStore : IxIR1.Store}
    {source : List RVal}
    {input afterInput : Array (Option Atom)}
    {capabilities afterCapabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    {headAtom : Atom}
    (forgets : Lower.InputMap.Forgets afterInput (#[some headAtom] ++ input))
    (afterOwners : OwnedInputRegisters afterInput afterCapabilities)
    {world : Ix.Compiler.Ixon.Owned} {identity : CtorId}
    {arguments : Array IxIR1.Atom} {value : RVal}
    (transition : Lower.allocationCapabilities? capabilities input world
      arguments =
      some afterCapabilities)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent
      store source (.alloc world identity arguments) =
        .ok (outputStore, value)) :
    SourceOwnershipInvariant outputStore (value :: source) afterInput
      afterCapabilities frameRoots := by
  obtain ⟨values, resolved, outputEq⟩ :=
    IxIR1.runOp_alloc_success operationRun
  have outputStoreEq : outputStore =
      (store.allocNode world (.ctorN identity values.toArray)).1 :=
    congrArg Prod.fst outputEq
  have valueEq : value =
      .loc (store.allocNode world (.ctorN identity values.toArray)).2 :=
    congrArg Prod.snd outputEq
  subst outputStore
  subst value
  cases consumeEq : Lower.consumeCapabilitiesList? capabilities input world
      arguments.toList with
  | none =>
      simp [Lower.allocationCapabilities?, consumeEq] at transition
  | some remaining =>
      have afterEq :
          #[.owned world] ++ remaining = afterCapabilities := by
        simpa [Lower.allocationCapabilities?, consumeEq] using transition
      subst afterCapabilities
      have resolvedRelation := SourceAtomsResolve.ofResolveAtoms resolved
      obtain ⟨remainingHolds, readyOwnership⟩ :=
        consumeCapabilitiesList_ownership (consumedRoots := [])
          (suffixRoots := frameRoots)
          invariant.holds (by simpa using invariant.ownership)
            resolvedRelation consumeEq
      have readyOwnership' : IxIR1.Sim.RootOwnership store
          (IxIR1.Sim.rootsFor world values ++
            rootsForCapabilities remaining.toList source ++ frameRoots) := by
        simpa using readyOwnership
      have allocatedOwnership :=
        (IxIR1.Sim.runOp_alloc_owned
          (ctx := sourceContext) (fuel := sourceFuel)
          (cur := sourceCurrent) (cid := identity) (args := arguments)
          resolved
            (by simpa [List.append_assoc] using readyOwnership')).2
      have remainingSize : remaining.size = capabilities.size :=
        Lower.consumeCapabilitiesList?_size consumeEq
      have remainingBorrows :
          ∀ {index : Nat} {borrowWorld : Ix.Compiler.Ixon.Owned}
              {lender : BorrowLender} {borrowedValue : RVal},
            remaining[index]? = some (.borrowed borrowWorld lender) →
            source[index]? = some borrowedValue →
            BorrowProvenance store source input remaining frameRoots
              borrowWorld lender borrowedValue :=
        consumeCapabilitiesList_borrows invariant.borrows consumeEq
      refine ⟨by
          simp [Array.size_append, remainingSize, invariant.length,
            Nat.add_comm], ?_, ?_, ?_⟩
      · intro index capability selected capabilityAt selectedAt
        cases index with
        | zero =>
            simp [Array.getElem?_append] at capabilityAt selectedAt
            subst capability
            subst selected
            exact IxIR1.Sim.HasWorld.allocNode_new store world
              (.ctorN identity values.toArray)
        | succ index =>
            simp [Array.getElem?_append] at capabilityAt selectedAt
            exact (remainingHolds capabilityAt selectedAt).allocNode
      · simpa [rootsForCapabilities] using allocatedOwnership
      · exact BorrowProvenance.prependNonBorrowed
          (IxIR1.Sim.StoreGraphExtends.allocNode store world
            (.ctorN identity values.toArray)) remainingBorrows
          (by intros; simp) forgets afterOwners

/-- Function partial application consumes its shared capture owners into a
fresh shared PAP node and exposes the fresh PAP owner. -/
theorem papp {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {sourceCurrent : IxIR1.FnDef} {store outputStore : IxIR1.Store}
    {source : List RVal}
    {input afterInput : Array (Option Atom)}
    {capabilities afterCapabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    {headAtom : Atom}
    (forgets : Lower.InputMap.Forgets afterInput (#[some headAtom] ++ input))
    (afterOwners : OwnedInputRegisters afterInput afterCapabilities)
    {function : Ix.Compiler.Ixon.Address}
    {arguments : Array IxIR1.Atom} {value : RVal}
    (transition : Lower.allocationCapabilities? capabilities input .shared
      arguments =
      some afterCapabilities)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent
      store source (.papp function arguments) =
        .ok (outputStore, value)) :
    SourceOwnershipInvariant outputStore (value :: source) afterInput
      afterCapabilities frameRoots := by
  obtain ⟨values, declaration, resolved, declarationAt, under, outputEq⟩ :=
    IxIR1.runOp_papp_success operationRun
  have outputStoreEq : outputStore =
      (store.allocNode .shared
        (.papN function (IxIR1.declArity declaration) values.toArray)).1 :=
    congrArg Prod.fst outputEq
  have valueEq : value =
      .loc (store.allocNode .shared
        (.papN function (IxIR1.declArity declaration) values.toArray)).2 :=
    congrArg Prod.snd outputEq
  subst outputStore
  subst value
  cases consumeEq : Lower.consumeCapabilitiesList? capabilities input .shared
      arguments.toList with
  | none =>
      simp [Lower.allocationCapabilities?, consumeEq] at transition
  | some remaining =>
      have afterEq :
          #[.owned .shared] ++ remaining = afterCapabilities := by
        simpa [Lower.allocationCapabilities?, consumeEq] using transition
      subst afterCapabilities
      have resolvedRelation := SourceAtomsResolve.ofResolveAtoms resolved
      obtain ⟨remainingHolds, readyOwnership⟩ :=
        consumeCapabilitiesList_ownership (consumedRoots := [])
          (suffixRoots := frameRoots)
          invariant.holds (by simpa using invariant.ownership)
            resolvedRelation consumeEq
      have readyOwnership' : IxIR1.Sim.RootOwnership store
          (IxIR1.Sim.rootsFor .shared values ++
            rootsForCapabilities remaining.toList source ++ frameRoots) := by
        simpa using readyOwnership
      have allocatedOwnership :=
        (IxIR1.Sim.runOp_papp_owned
          (ctx := sourceContext) (fuel := sourceFuel)
          (cur := sourceCurrent) (f := function) (atoms := arguments)
          resolved declarationAt under
            (by simpa [List.append_assoc] using readyOwnership')).2
      have remainingSize : remaining.size = capabilities.size :=
        Lower.consumeCapabilitiesList?_size consumeEq
      have remainingBorrows :
          ∀ {index : Nat} {borrowWorld : Ix.Compiler.Ixon.Owned}
              {lender : BorrowLender} {borrowedValue : RVal},
            remaining[index]? = some (.borrowed borrowWorld lender) →
            source[index]? = some borrowedValue →
            BorrowProvenance store source input remaining frameRoots
              borrowWorld lender borrowedValue :=
        consumeCapabilitiesList_borrows invariant.borrows consumeEq
      refine ⟨by
          simp [Array.size_append, remainingSize, invariant.length,
            Nat.add_comm], ?_, ?_, ?_⟩
      · intro index capability selected capabilityAt selectedAt
        cases index with
        | zero =>
            simp [Array.getElem?_append] at capabilityAt selectedAt
            subst capability
            subst selected
            exact IxIR1.Sim.HasWorld.allocNode_new store .shared
              (.papN function (IxIR1.declArity declaration) values.toArray)
        | succ index =>
            simp [Array.getElem?_append] at capabilityAt selectedAt
            exact (remainingHolds capabilityAt selectedAt).allocNode
      · simpa [rootsForCapabilities] using allocatedOwnership
      · exact BorrowProvenance.prependNonBorrowed
          (IxIR1.Sim.StoreGraphExtends.allocNode store .shared
            (.papN function (IxIR1.declArity declaration) values.toArray))
          remainingBorrows (by intros; simp) forgets afterOwners

private theorem rootsForCapabilities_replicate_owned
    (world : Ix.Compiler.Ixon.Owned) : ∀ (values : List RVal),
    rootsForCapabilities
        (List.replicate values.length (Lower.BindingCap.owned world)) values =
      IxIR1.Sim.rootsFor world values := by
  intro values
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [List.replicate_succ, rootsForCapabilities,
        IxIR1.Sim.rootsFor, ih]

/-- A same-length all-shared owned capability vector realizes the canonical
reversed source environment at a dynamically selected PAP callee entry. -/
theorem sharedEntry {store : IxIR1.Store} {values : List RVal}
    {input : Array (Option Atom)} {capabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (shape : capabilities =
      Array.replicate values.length (.owned .shared))
    (ownership : IxIR1.Sim.RootOwnership store
      (IxIR1.Sim.rootsFor .shared values ++ frameRoots)) :
    SourceOwnershipInvariant store values.reverse input capabilities
      frameRoots := by
  subst capabilities
  have rootsEq :
      rootsForCapabilities
          (Array.replicate values.length
            (Lower.BindingCap.owned .shared)).toList values.reverse =
        (IxIR1.Sim.rootsFor .shared values).reverse := by
    calc
      _ = IxIR1.Sim.rootsFor .shared values.reverse := by
        simpa using rootsForCapabilities_replicate_owned .shared
          values.reverse
      _ = _ := by simp [IxIR1.Sim.rootsFor, List.map_reverse]
  have entryOwnership : IxIR1.Sim.RootOwnership store
      (rootsForCapabilities
          (Array.replicate values.length
            (Lower.BindingCap.owned .shared)).toList values.reverse ++
        frameRoots) := by
    apply ownership.perm
    rw [rootsEq]
    exact (List.reverse_perm (IxIR1.Sim.rootsFor .shared values)).symm
      |>.append_right frameRoots
  refine ⟨by simp, ?_, entryOwnership, ?_⟩
  · intro index capability selected capabilityAt selectedAt
    have capabilityEq : capability = .owned .shared := by
      simp only [Array.getElem?_replicate] at capabilityAt
      split at capabilityAt
      next bound => exact Option.some.inj capabilityAt |>.symm
      next bound => contradiction
    subst capability
    exact entryOwnership.roots_world ⟨.shared, selected⟩
      (List.mem_append_left _
        (rootsForCapabilities_owned_mem capabilityAt selectedAt))
  · intro index world lender selected capabilityAt selectedAt
    simp only [Array.getElem?_replicate] at capabilityAt
    split at capabilityAt
    next bound => cases capabilityAt
    next bound => contradiction

/-- Consume a dynamic PAP function and its newly supplied arguments, then
replay the PAP retain/release prefix.  The resulting roots are split between
the first callee entry and any residual `applyMore` arguments; surviving
caller owners remain as the final suspended-frame suffix. -/
theorem preparePapEntry {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {store retainedStore readyStore : IxIR1.Store} {source : List RVal}
    {input : Array (Option Atom)}
    {capabilities afterFunction remaining : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    {functionAtom : IxIR1.Atom} {argumentAtoms : Array IxIR1.Atom}
    {location rc : Nat} {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    {captured : Array RVal} {arguments supplied residual : List RVal}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    (functionResolved : IxIR1.resolveAtom source functionAtom =
      .ok (.loc location))
    (argumentsResolved : IxIR1.resolveAtoms source argumentAtoms =
      .ok arguments)
    (functionConsumed : Lower.consumeCapability? capabilities input .shared
      functionAtom = some afterFunction)
    (argumentsConsumed : Lower.consumeCapabilitiesList? afterFunction input
      .shared argumentAtoms.toList = some remaining)
    (papAt : store.get? location =
      some ⟨.shared, rc, .papN address arity captured⟩)
    (retained : IxIR1.dupVals store captured.toList = .ok retainedStore)
    (released : IxIR1.dropVal sourceContext sourceFuel retainedStore
      (.loc location) = .ok readyStore)
    (split : captured.toList ++ arguments = supplied ++ residual) :
    IxIR1.Sim.RootOwnership readyStore
      (IxIR1.Sim.rootsFor .shared supplied ++
        IxIR1.Sim.rootsFor .shared residual ++
        rootsForCapabilities remaining.toList source ++ frameRoots) := by
  obtain ⟨afterFunctionHolds, afterFunctionOwnership⟩ :=
    consumeCapability_ownership (consumedRoots := [])
      (suffixRoots := frameRoots) invariant.holds
      (by simpa using invariant.ownership) functionResolved functionConsumed
  have resolvedRelation := SourceAtomsResolve.ofResolveAtoms argumentsResolved
  obtain ⟨_, readyOwnership⟩ :=
    consumeCapabilitiesList_ownership
      (consumedRoots :=
        [(⟨.shared, .loc location⟩ : IxIR1.Sim.Root)])
      (suffixRoots := frameRoots) afterFunctionHolds
      (by simpa using afterFunctionOwnership) resolvedRelation
      argumentsConsumed
  have papOwnership := IxIR1.Sim.applyGo_preparePap_owned papAt
    (by simpa [List.append_assoc] using readyOwnership) retained released
  rw [split] at papOwnership
  simpa [IxIR1.Sim.rootsFor, List.append_assoc] using papOwnership

/-- Dynamic application consumes the shared function root and every supplied
shared argument root. A preservation law for this exact input heap returns
one shared result root while the checked suspension rule excludes borrows
from the surviving source frame. -/
theorem applyFrom {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {sourceCurrent : IxIR1.FnDef} {store outputStore : IxIR1.Store}
    {source : List RVal}
    {input afterInput : Array (Option Atom)}
    {capabilities afterCapabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    {function : IxIR1.Atom} {arguments : Array IxIR1.Atom} {value : RVal}
    (transition : Lower.applyCapabilities? capabilities input function
      arguments = some afterCapabilities)
    (noBorrows : Lower.noBorrows afterCapabilities = true)
    (preserves : IxIR1.Sim.ApplyOwnershipPreservesFrom sourceContext
      sourceFuel store)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent
      store source (.apply function arguments) = .ok (outputStore, value)) :
    SourceOwnershipInvariant outputStore (value :: source) afterInput
      afterCapabilities frameRoots := by
  obtain ⟨functionValue, values, functionResolved, argumentsResolved,
      applyRun⟩ :=
    IxIR1.runOp_apply_success operationRun
  unfold Lower.applyCapabilities? at transition
  cases functionConsume : Lower.consumeCapability? capabilities input .shared
      function with
  | none => simp [functionConsume] at transition
  | some afterFunction =>
      simp only [functionConsume, Option.bind_eq_bind, Option.bind_some] at transition
      cases argumentsConsume : Lower.consumeCapabilitiesList? afterFunction
          input .shared arguments.toList with
      | none => simp [argumentsConsume] at transition
      | some remaining =>
          have afterEq :
              #[.owned .shared] ++ remaining = afterCapabilities := by
            simpa [argumentsConsume] using transition
          subst afterCapabilities
          obtain ⟨afterFunctionHolds, afterFunctionOwnership⟩ :=
            consumeCapability_ownership (consumedRoots := [])
              (suffixRoots := frameRoots) invariant.holds
              (by simpa using invariant.ownership) functionResolved
              functionConsume
          have resolvedRelation := SourceAtomsResolve.ofResolveAtoms
            argumentsResolved
          obtain ⟨remainingHolds, readyOwnership⟩ :=
            consumeCapabilitiesList_ownership
              (consumedRoots :=
                [(⟨.shared, functionValue⟩ : IxIR1.Sim.Root)])
              (suffixRoots := frameRoots) afterFunctionHolds
              (by simpa using afterFunctionOwnership) resolvedRelation
              argumentsConsume
          have resultOwnership : IxIR1.Sim.RootOwnership outputStore
              (⟨.shared, value⟩ ::
                (rootsForCapabilities remaining.toList source ++
                  frameRoots)) := by
            exact preserves
              (by simpa [List.append_assoc] using readyOwnership) applyRun
          have remainingSize : remaining.size = capabilities.size :=
            (Lower.consumeCapabilitiesList?_size argumentsConsume).trans
              (Lower.consumeCapability?_size functionConsume)
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp [Array.size_append, remainingSize, invariant.length,
              Nat.add_comm]
          · intro index capability selected capabilityAt selectedAt
            cases index with
            | zero =>
                simp [Array.getElem?_append] at capabilityAt selectedAt
                subst capability
                subst selected
                exact resultOwnership.roots_world ⟨.shared, value⟩ (by simp)
            | succ index =>
                simp [Array.getElem?_append] at capabilityAt selectedAt
                cases capability with
                | scalar =>
                    simpa [CapabilityHolds] using
                      remainingHolds capabilityAt selectedAt
                | dead => trivial
                | borrowed world lender =>
                    have fullAt :
                        (#[.owned .shared] ++ remaining)[index + 1]? =
                          some (.borrowed world lender) := by
                      simp [Array.getElem?_append, capabilityAt]
                    exact False.elim
                      (borrowed_impossible_of_noBorrows noBorrows fullAt)
                | owned world =>
                    exact resultOwnership.roots_world ⟨world, selected⟩ (by
                      simp [rootsForCapabilities_owned_mem capabilityAt
                        selectedAt])
          · simpa [rootsForCapabilities, List.append_assoc] using
              resultOwnership
          · intro index world lender selected capabilityAt selectedAt
            exact False.elim
              (borrowed_impossible_of_noBorrows noBorrows capabilityAt)

/-- The traditional whole-context contract specializes the fixed-input rule
used by `applyFrom`. -/
theorem apply {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {sourceCurrent : IxIR1.FnDef} {store outputStore : IxIR1.Store}
    {source : List RVal}
    {input afterInput : Array (Option Atom)}
    {capabilities afterCapabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    {function : IxIR1.Atom} {arguments : Array IxIR1.Atom} {value : RVal}
    (transition : Lower.applyCapabilities? capabilities input function
      arguments = some afterCapabilities)
    (noBorrows : Lower.noBorrows afterCapabilities = true)
    (contract : IxIR1.Sim.ApplyOwnershipContract sourceContext)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent
      store source (.apply function arguments) = .ok (outputStore, value)) :
    SourceOwnershipInvariant outputStore (value :: source) afterInput
      afterCapabilities frameRoots :=
  invariant.applyFrom transition noBorrows
    (contract.preservesFrom sourceFuel store) operationRun

end SourceOwnershipInvariant

namespace SourceOwnershipAt

/-- A checked ordinary allocation transports trace-indexed ownership through
its exact sequential argument consumption and fresh-result binding. -/
theorem alloc {checked : Lower.Checked}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceWorld targetWorld : Ix.Compiler.Ixon.Owned}
    {sourceCid targetCid : CtorId}
    {sourceArguments : Array IxIR1.Atom} {targetArguments : Array Atom}
    {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
          (.alloc targetWorld targetCid targetArguments) next))
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {store outputStore : IxIR1.Store} {source : List RVal} {value : RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
          (.alloc targetWorld targetCid targetArguments) next) store source
            frameRoots)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1)
      functionTrace.source store source
        (.alloc sourceWorld sourceCid sourceArguments) =
          .ok (outputStore, value)) :
    SourceOwnershipAt checked.artifact.trace.positions next outputStore
      (value :: source) frameRoots := by
  intro after afterMember afterCoordinate
  obtain ⟨before, beforeMember, beforeCoordinate, transitionMatch⟩ :=
    checked.allocationTransition functionMember descendant afterMember
      afterCoordinate
  have beforeInvariant := ownership before beforeMember (by
      simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
        Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
          beforeCoordinate)
  change SourceOwnershipInvariant store source input
    before.sourceCapabilities frameRoots at beforeInvariant
  have mapFacts := Lower.CodeTrace.inputMapForgets_of_match
    (functionTrace.descendantInputMapsMatch descendant) (by rfl)
  have letOpMatch := functionTrace.descendantLetOpMatch descendant
  have forgets : Lower.InputMap.Forgets next.sourceInputMap
      (#[some (.reg entryValueCount)] ++ input) := by
    simpa [letOpMatch.1.nextInput] using mapFacts.2.2.1
  have afterOwners : OwnedInputRegisters next.sourceInputMap
      after.sourceCapabilities :=
    OwnedInputRegisters.ofCoordinate afterCoordinate
  unfold Lower.PositionTrace.allocationResultMatches at transitionMatch
  cases transitionEq : Lower.allocationCapabilities?
      before.sourceCapabilities input sourceWorld sourceArguments with
  | none => simp [transitionEq] at transitionMatch
  | some expected =>
      have expectedEq : expected = after.sourceCapabilities := by
        simpa [transitionEq, beq_iff_eq] using transitionMatch
      apply beforeInvariant.alloc forgets afterOwners (sourceFuel := sourceFuel)
        (operationRun := operationRun)
      simpa [expectedEq] using transitionEq

/-- A checked function partial application transports trace-indexed ownership
through shared capture consumption and fresh PAP-owner binding. -/
theorem papp {checked : Lower.Checked}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceAddress targetAddress : Ix.Compiler.Ixon.Address}
    {sourceArguments : Array IxIR1.Atom} {targetArguments : Array Atom}
    {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.papp sourceAddress sourceArguments) index
          (.papp targetAddress targetArguments) next))
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {store outputStore : IxIR1.Store} {source : List RVal} {value : RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.papp sourceAddress sourceArguments) index
          (.papp targetAddress targetArguments) next) store source
            frameRoots)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1)
      functionTrace.source store source
        (.papp sourceAddress sourceArguments) =
          .ok (outputStore, value)) :
    SourceOwnershipAt checked.artifact.trace.positions next outputStore
      (value :: source) frameRoots := by
  intro after afterMember afterCoordinate
  obtain ⟨before, beforeMember, beforeCoordinate, transitionMatch⟩ :=
    checked.pappTransition functionMember descendant afterMember
      afterCoordinate
  have beforeInvariant := ownership before beforeMember (by
      simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
        Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
          beforeCoordinate)
  change SourceOwnershipInvariant store source input
    before.sourceCapabilities frameRoots at beforeInvariant
  have mapFacts := Lower.CodeTrace.inputMapForgets_of_match
    (functionTrace.descendantInputMapsMatch descendant) (by rfl)
  have letOpMatch := functionTrace.descendantLetOpMatch descendant
  have forgets : Lower.InputMap.Forgets next.sourceInputMap
      (#[some (.reg entryValueCount)] ++ input) := by
    simpa [letOpMatch.1.nextInput] using mapFacts.2.2.1
  have afterOwners : OwnedInputRegisters next.sourceInputMap
      after.sourceCapabilities :=
    OwnedInputRegisters.ofCoordinate afterCoordinate
  unfold Lower.PositionTrace.allocationResultMatches at transitionMatch
  cases transitionEq : Lower.allocationCapabilities?
      before.sourceCapabilities input .shared sourceArguments with
  | none => simp [transitionEq] at transitionMatch
  | some expected =>
      have expectedEq : expected = after.sourceCapabilities := by
        simpa [transitionEq, beq_iff_eq] using transitionMatch
      apply beforeInvariant.papp forgets afterOwners (sourceFuel := sourceFuel)
        (operationRun := operationRun)
      simpa [expectedEq] using transitionEq

/-- A checked dynamic application transports trace-indexed ownership through
the shared function/argument boundary using a preservation law for its exact
input heap, then reinstalls the surviving source frame around the returned
shared owner. -/
theorem applyFrom {checked : Lower.Checked}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceFunction : IxIR1.Atom} {sourceArguments : Array IxIR1.Atom}
    {targetFunction : Atom} {targetArguments : Array Atom}
    {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
          (.apply targetFunction targetArguments) next))
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {store outputStore : IxIR1.Store} {source : List RVal} {value : RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
          (.apply targetFunction targetArguments) next)
      store source frameRoots)
    (preserves : IxIR1.Sim.ApplyOwnershipPreservesFrom sourceContext
      sourceFuel store)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1)
      functionTrace.source store source
        (.apply sourceFunction sourceArguments) = .ok (outputStore, value)) :
    SourceOwnershipAt checked.artifact.trace.positions next outputStore
      (value :: source) frameRoots := by
  intro after afterMember afterCoordinate
  obtain ⟨before, beforeMember, beforeCoordinate, transitionMatch⟩ :=
    checked.applyTransition functionMember descendant afterMember
      afterCoordinate
  have beforeInvariant := ownership before beforeMember (by
    simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
      Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
        beforeCoordinate)
  change SourceOwnershipInvariant store source input
    before.sourceCapabilities frameRoots at beforeInvariant
  unfold Lower.PositionTrace.applyResultMatches at transitionMatch
  cases transitionEq : Lower.applyCapabilities?
      before.sourceCapabilities input sourceFunction sourceArguments with
  | none => simp [transitionEq] at transitionMatch
  | some expected =>
      simp only [transitionEq, Bool.and_eq_true, beq_iff_eq] at transitionMatch
      have transition : Lower.applyCapabilities?
          before.sourceCapabilities input sourceFunction sourceArguments =
            some after.sourceCapabilities := by
        simpa [transitionMatch.2] using transitionEq
      have noBorrows : Lower.noBorrows after.sourceCapabilities = true := by
        simpa [transitionMatch.2] using transitionMatch.1
      exact beforeInvariant.applyFrom transition noBorrows preserves operationRun

/-- The whole-context application contract remains a compatibility wrapper
around the reachable-heap `applyFrom` interface. -/
theorem apply {checked : Lower.Checked}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceFunction : IxIR1.Atom} {sourceArguments : Array IxIR1.Atom}
    {targetFunction : Atom} {targetArguments : Array Atom}
    {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
          (.apply targetFunction targetArguments) next))
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {store outputStore : IxIR1.Store} {source : List RVal} {value : RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
          (.apply targetFunction targetArguments) next)
      store source frameRoots)
    (contract : IxIR1.Sim.ApplyOwnershipContract sourceContext)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1)
      functionTrace.source store source
        (.apply sourceFunction sourceArguments) = .ok (outputStore, value)) :
    SourceOwnershipAt checked.artifact.trace.positions next outputStore
      (value :: source) frameRoots :=
  applyFrom functionMember descendant ownership
    (contract.preservesFrom sourceFuel store) operationRun

/-- A checked dynamic PAP application constructs the first callee's exact
entry ownership from the caller's current capability state.  Exact
saturation uses an empty residual list; over-saturation frames the residual
shared arguments ahead of the surviving caller roots for `applyMore`. -/
theorem applyPapEntry {checked : Lower.Checked}
    {callerTrace calleeTrace : Lower.FunctionTrace}
    (callerMember : callerTrace ∈ checked.artifact.trace.functions)
    (calleeMember : calleeTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceFunction : IxIR1.Atom} {sourceArguments : Array IxIR1.Atom}
    {instruction : Instr} {next : Lower.CodeTrace}
    (descendant : callerTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index instruction next))
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {sourceStore retainedStore readyStore : IxIR1.Store}
    {source : List RVal} {location rc : Nat}
    {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    {captured : Array RVal} {arguments supplied residual : List RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index instruction next)
      sourceStore source frameRoots)
    (functionResolved : IxIR1.resolveAtom source sourceFunction =
      .ok (.loc location))
    (argumentsResolved : IxIR1.resolveAtoms source sourceArguments =
      .ok arguments)
    (papAt : sourceStore.get? location =
      some ⟨.shared, rc, .papN address arity captured⟩)
    (retained : IxIR1.dupVals sourceStore captured.toList = .ok retainedStore)
    (released : IxIR1.dropVal sourceContext sourceFuel retainedStore
      (.loc location) = .ok readyStore)
    (split : captured.toList ++ arguments = supplied ++ residual)
    (entryArity : supplied.length =
      calleeTrace.generated.signature.params.size)
    (papSafe : calleeTrace.generated.signature.papSafe = true) :
    ∃ before afterFunction remaining,
      before ∈ checked.artifact.trace.positions ∧
      before.coordinateMatches site blockId (.instruction index) input = true ∧
      Lower.consumeCapability? before.sourceCapabilities input .shared
          sourceFunction = some afterFunction ∧
      Lower.consumeCapabilitiesList? afterFunction input .shared
          sourceArguments.toList = some remaining ∧
      Lower.noBorrows (#[.owned .shared] ++ remaining) = true ∧
      IxIR1.Sim.RootOwnership readyStore
        (IxIR1.Sim.rootsFor .shared supplied ++
          IxIR1.Sim.rootsFor .shared residual ++
          rootsForCapabilities remaining.toList source ++ frameRoots) ∧
      SourceOwnershipAt checked.artifact.trace.positions calleeTrace.root
        readyStore supplied.reverse
        (IxIR1.Sim.rootsFor .shared residual ++
          rootsForCapabilities remaining.toList source ++ frameRoots) := by
  have nextDescendant : callerTrace.root.Descendant next :=
    .step descendant (by simp [Lower.CodeTrace.children])
  obtain ⟨after, afterMember, afterCoordinate⟩ :=
    checked.position callerMember nextDescendant
  obtain ⟨before, beforeMember, beforeCoordinate, transition⟩ :=
    checked.applyTransition callerMember descendant afterMember afterCoordinate
  unfold Lower.PositionTrace.applyResultMatches at transition
  unfold Lower.applyCapabilities? at transition
  cases functionConsumed : Lower.consumeCapability? before.sourceCapabilities
      input .shared sourceFunction with
  | none => simp [functionConsumed] at transition
  | some afterFunction =>
      simp only [functionConsumed, Option.bind_eq_bind, Option.bind_some] at transition
      cases argumentsConsumed : Lower.consumeCapabilitiesList? afterFunction
          input .shared sourceArguments.toList with
      | none => simp [argumentsConsumed] at transition
      | some remaining =>
          simp only [argumentsConsumed, Option.bind_some] at transition
          change (Lower.noBorrows (#[.owned .shared] ++ remaining) &&
            (#[.owned .shared] ++ remaining ==
              after.sourceCapabilities)) = true at transition
          simp only [Bool.and_eq_true, beq_iff_eq] at transition
          have beforeInvariant := ownership before beforeMember (by
            simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
              Lower.CodeTrace.targetPosition,
              Lower.CodeTrace.sourceInputMap] using beforeCoordinate)
          change SourceOwnershipInvariant sourceStore source input
            before.sourceCapabilities frameRoots at beforeInvariant
          have readyOwnership := beforeInvariant.preparePapEntry
            functionResolved argumentsResolved functionConsumed
              argumentsConsumed papAt retained released split
          have entryShape :
              Lower.entryCapabilities calleeTrace.generated.signature =
                Array.replicate supplied.length (.owned .shared) := by
            simpa [entryArity] using
              checked.papSafeEntryCapabilities calleeMember papSafe
          have calleeOwnership : SourceOwnershipAt
              checked.artifact.trace.positions calleeTrace.root readyStore
              supplied.reverse
              (IxIR1.Sim.rootsFor .shared residual ++
                rootsForCapabilities remaining.toList source ++
                  frameRoots) := by
            intro entry entryMember entryCoordinate
            rw [checked.entryCapabilities calleeMember entryMember
              entryCoordinate]
            exact SourceOwnershipInvariant.sharedEntry entryShape
              (by simpa [List.append_assoc] using readyOwnership)
          exact ⟨before, afterFunction, remaining, beforeMember,
            beforeCoordinate, functionConsumed, argumentsConsumed,
            transition.1, readyOwnership, calleeOwnership⟩

/-- A checked scalar-leaf shallow free derives its continuation ownership from
the exact destruction capability transition and the certified concrete leaf. -/
theorem free {checked : Lower.Checked}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {targetCid : CtorId}
    {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.free sourceAtom) index (.freeUnique targetAtom targetCid) next))
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {store outputStore : IxIR1.Store} {source : List RVal} {value : RVal}
    {location : Nat} {box : IxIR1.NodeBox} {identity : CtorId}
    {fields : Array RVal} {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.free sourceAtom) index (.freeUnique targetAtom targetCid) next)
      store source frameRoots)
    (resolved : IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : store.get? location = some box)
    (unique : box.world = .unique)
    (node : box.node = .ctorN identity fields)
    (scalarFields : fields.all IxIR1.RVal.isScalar = true)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1)
      functionTrace.source store source (.free sourceAtom) =
        .ok (outputStore, value)) :
    SourceOwnershipAt checked.artifact.trace.positions next outputStore
      (value :: source) frameRoots := by
  intro after afterMember afterCoordinate
  obtain ⟨before, beforeMember, beforeCoordinate, transitionMatch⟩ :=
    checked.destructionTransition functionMember (by rfl) descendant afterMember
      afterCoordinate
  have beforeInvariant := ownership before beforeMember (by
      simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
        Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
          beforeCoordinate)
  change SourceOwnershipInvariant store source input
    before.sourceCapabilities frameRoots at beforeInvariant
  have mapFacts := Lower.CodeTrace.inputMapForgets_of_match
    (functionTrace.descendantInputMapsMatch descendant) (by rfl)
  have letOpMatch := functionTrace.descendantLetOpMatch descendant
  have forgets : Lower.InputMap.Forgets next.sourceInputMap
      (#[some .erased] ++ input) := by
    simpa [letOpMatch.1.nextInput] using mapFacts.2.2.1
  have afterOwners : OwnedInputRegisters next.sourceInputMap
      after.sourceCapabilities :=
    OwnedInputRegisters.ofCoordinate afterCoordinate
  unfold Lower.PositionTrace.destructionResultMatches at transitionMatch
  cases transitionEq : Lower.destructionCapabilities?
      before.sourceCapabilities input .unique sourceAtom with
  | none => simp [transitionEq] at transitionMatch
  | some expected =>
      have expectedEq : expected = after.sourceCapabilities := by
        simpa [transitionEq, beq_iff_eq] using transitionMatch
      apply beforeInvariant.free forgets afterOwners
        (sourceFuel := sourceFuel) (operationRun := operationRun)
        (resolved := resolved) (sourceGet := sourceGet) (unique := unique)
        (node := node) (scalarFields := scalarFields)
      simpa [expectedEq] using transitionEq

/-- A checked shared destruction derives its dynamic ownership transition from
the producer's exact consume-and-retire capability effect. -/
theorem drop {checked : Lower.Checked}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.drop sourceAtom) index (.releaseShared targetAtom) next))
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {store outputStore : IxIR1.Store} {source : List RVal} {value : RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.drop sourceAtom) index (.releaseShared targetAtom) next) store source
          frameRoots)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1)
      functionTrace.source store source (.drop sourceAtom) =
        .ok (outputStore, value)) :
    SourceOwnershipAt checked.artifact.trace.positions next outputStore
      (value :: source) frameRoots := by
  intro after afterMember afterCoordinate
  obtain ⟨before, beforeMember, beforeCoordinate, transitionMatch⟩ :=
    checked.destructionTransition functionMember (by rfl) descendant afterMember
      afterCoordinate
  have beforeInvariant := ownership before beforeMember (by
      simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
        Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
          beforeCoordinate)
  change SourceOwnershipInvariant store source input
    before.sourceCapabilities frameRoots at beforeInvariant
  have mapFacts := Lower.CodeTrace.inputMapForgets_of_match
    (functionTrace.descendantInputMapsMatch descendant) (by rfl)
  have letOpMatch := functionTrace.descendantLetOpMatch descendant
  have forgets : Lower.InputMap.Forgets next.sourceInputMap
      (#[some .erased] ++ input) := by
    simpa [letOpMatch.1.nextInput] using mapFacts.2.2.1
  have afterOwners : OwnedInputRegisters next.sourceInputMap
      after.sourceCapabilities :=
    OwnedInputRegisters.ofCoordinate afterCoordinate
  unfold Lower.PositionTrace.destructionResultMatches at transitionMatch
  cases transitionEq : Lower.destructionCapabilities?
      before.sourceCapabilities input .shared sourceAtom with
  | none => simp [transitionEq] at transitionMatch
  | some expected =>
      have expectedEq : expected = after.sourceCapabilities := by
        simpa [transitionEq, beq_iff_eq] using transitionMatch
      apply beforeInvariant.drop forgets afterOwners (sourceFuel := sourceFuel)
        (operationRun := operationRun)
      simpa [expectedEq] using transitionEq

/-- A checked unique recursive destruction derives the continuation ownership
invariant without an external semantic-transition premise. -/
theorem dropU {checked : Lower.Checked}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.dropU sourceAtom) index (.dropUnique targetAtom) next))
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {store outputStore : IxIR1.Store} {source : List RVal} {value : RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.dropU sourceAtom) index (.dropUnique targetAtom) next) store source
          frameRoots)
    (operationRun : IxIR1.runOp sourceContext (sourceFuel + 1)
      functionTrace.source store source (.dropU sourceAtom) =
        .ok (outputStore, value)) :
    SourceOwnershipAt checked.artifact.trace.positions next outputStore
      (value :: source) frameRoots := by
  intro after afterMember afterCoordinate
  obtain ⟨before, beforeMember, beforeCoordinate, transitionMatch⟩ :=
    checked.destructionTransition functionMember (by rfl) descendant afterMember
      afterCoordinate
  have beforeInvariant := ownership before beforeMember (by
      simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
        Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
          beforeCoordinate)
  change SourceOwnershipInvariant store source input
    before.sourceCapabilities frameRoots at beforeInvariant
  have mapFacts := Lower.CodeTrace.inputMapForgets_of_match
    (functionTrace.descendantInputMapsMatch descendant) (by rfl)
  have letOpMatch := functionTrace.descendantLetOpMatch descendant
  have forgets : Lower.InputMap.Forgets next.sourceInputMap
      (#[some .erased] ++ input) := by
    simpa [letOpMatch.1.nextInput] using mapFacts.2.2.1
  have afterOwners : OwnedInputRegisters next.sourceInputMap
      after.sourceCapabilities :=
    OwnedInputRegisters.ofCoordinate afterCoordinate
  unfold Lower.PositionTrace.destructionResultMatches at transitionMatch
  cases transitionEq : Lower.destructionCapabilities?
      before.sourceCapabilities input .unique sourceAtom with
  | none => simp [transitionEq] at transitionMatch
  | some expected =>
      have expectedEq : expected = after.sourceCapabilities := by
        simpa [transitionEq, beq_iff_eq] using transitionMatch
      apply beforeInvariant.dropU forgets afterOwners (sourceFuel := sourceFuel)
        (operationRun := operationRun)
      simpa [expectedEq] using transitionEq

/-- A checked addressed call consumes its argument owners and constructs the
callee's canonical entry invariant. The exact surviving caller roots are
returned as the suspended frame suffix. -/
theorem callEntry {checked : Lower.Checked}
    {callerTrace calleeTrace : Lower.FunctionTrace}
    (callerMember : callerTrace ∈ checked.artifact.trace.functions)
    (calleeMember : calleeTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {address : Ix.Compiler.Ixon.Address}
    {sourceArguments : Array IxIR1.Atom} {instruction : Instr}
    {next : Lower.CodeTrace}
    (descendant : callerTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.call address sourceArguments) index instruction next))
    (signatureAt : Lower.targetSignature?
      checked.artifact.program.declarations address =
        some calleeTrace.generated.signature)
    {store : IxIR1.Store} {source values : List RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.call address sourceArguments) index instruction next)
      store source frameRoots)
    (resolved : IxIR1.resolveAtoms source sourceArguments = .ok values) :
    ∃ before remaining,
      before ∈ checked.artifact.trace.positions ∧
      before.coordinateMatches site blockId (.instruction index) input = true ∧
      Lower.callRemainingCapabilities? before.sourceCapabilities input
          calleeTrace.generated.signature sourceArguments = some remaining ∧
      Lower.noBorrows remaining = true ∧
      SourceOwnershipAt checked.artifact.trace.positions calleeTrace.root store
        values.reverse
        (rootsForCapabilities remaining.toList source ++ frameRoots) := by
  obtain ⟨before, beforeMember, beforeCoordinate⟩ :=
    checked.position callerMember descendant
  have beforeCoordinate' : before.coordinateMatches site blockId
      (.instruction index) input = true := by
    simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
      Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
        beforeCoordinate
  have nextDescendant : callerTrace.root.Descendant next :=
    .step descendant (by simp [Lower.CodeTrace.children])
  obtain ⟨after, afterMember, afterCoordinate⟩ :=
    checked.position callerMember nextDescendant
  have transition := checked.callTransition callerMember signatureAt descendant
    beforeMember beforeCoordinate' afterMember afterCoordinate
  unfold Lower.PositionTrace.callResultMatches at transition
  cases consumedEq : Lower.callRemainingCapabilities?
      before.sourceCapabilities input calleeTrace.generated.signature
        sourceArguments with
  | none => simp [consumedEq] at transition
  | some remaining =>
      simp only [consumedEq, Bool.and_eq_true, beq_iff_eq] at transition
      refine ⟨before, remaining, beforeMember, beforeCoordinate', consumedEq,
        transition.1, ?_⟩
      have beforeInvariant := ownership before beforeMember (by
        simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
          Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
            beforeCoordinate)
      change SourceOwnershipInvariant store source input
        before.sourceCapabilities frameRoots at beforeInvariant
      intro entry entryMember entryCoordinate
      have entryEq := checked.entryCapabilities calleeMember entryMember
        entryCoordinate
      rw [entryEq]
      exact beforeInvariant.callEntryInvariant resolved consumedEq

/-- Recursive self-call entry has the same exact ownership transfer, using
the current checked signature as its ABI. -/
theorem callSelfEntry {checked : Lower.Checked}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceArguments : Array IxIR1.Atom} {instruction : Instr}
    {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.callSelf sourceArguments) index instruction next))
    {store : IxIR1.Store} {source values : List RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.callSelf sourceArguments) index instruction next)
      store source frameRoots)
    (resolved : IxIR1.resolveAtoms source sourceArguments = .ok values) :
    ∃ before remaining,
      before ∈ checked.artifact.trace.positions ∧
      before.coordinateMatches site blockId (.instruction index) input = true ∧
      Lower.callRemainingCapabilities? before.sourceCapabilities input
          functionTrace.generated.signature sourceArguments = some remaining ∧
      Lower.noBorrows remaining = true ∧
      SourceOwnershipAt checked.artifact.trace.positions functionTrace.root
        store values.reverse
        (rootsForCapabilities remaining.toList source ++ frameRoots) := by
  obtain ⟨before, beforeMember, beforeCoordinate⟩ :=
    checked.position functionMember descendant
  have beforeCoordinate' : before.coordinateMatches site blockId
      (.instruction index) input = true := by
    simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
      Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
        beforeCoordinate
  have nextDescendant : functionTrace.root.Descendant next :=
    .step descendant (by simp [Lower.CodeTrace.children])
  obtain ⟨after, afterMember, afterCoordinate⟩ :=
    checked.position functionMember nextDescendant
  have transition := checked.callSelfTransition functionMember descendant
    beforeMember beforeCoordinate' afterMember afterCoordinate
  unfold Lower.PositionTrace.callResultMatches at transition
  cases consumedEq : Lower.callRemainingCapabilities?
      before.sourceCapabilities input functionTrace.generated.signature
        sourceArguments with
  | none => simp [consumedEq] at transition
  | some remaining =>
      simp only [consumedEq, Bool.and_eq_true, beq_iff_eq] at transition
      refine ⟨before, remaining, beforeMember, beforeCoordinate', consumedEq,
        transition.1, ?_⟩
      have beforeInvariant := ownership before beforeMember (by
        simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
          Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
            beforeCoordinate)
      change SourceOwnershipInvariant store source input
        before.sourceCapabilities frameRoots at beforeInvariant
      intro entry entryMember entryCoordinate
      have entryEq := checked.entryCapabilities functionMember entryMember
        entryCoordinate
      rw [entryEq]
      exact beforeInvariant.callEntryInvariant resolved consumedEq

/-- A checked addressed tail call transfers every local owner into the
callee, so the enclosing suspended-frame suffix is preserved exactly. -/
theorem tailCallEntry {checked : Lower.Checked}
    {callerTrace calleeTrace : Lower.FunctionTrace}
    (callerMember : callerTrace ∈ checked.artifact.trace.functions)
    (calleeMember : calleeTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {address : Ix.Compiler.Ixon.Address}
    {sourceArguments : Array IxIR1.Atom} {generated : Block}
    (descendant : callerTrace.root.Descendant
      (.tailCall site blockId input entryValueCount address sourceArguments
        generated))
    (signatureAt : Lower.targetSignature?
      checked.artifact.program.declarations address =
        some calleeTrace.generated.signature)
    {store : IxIR1.Store} {source values : List RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.tailCall site blockId input entryValueCount address sourceArguments
        generated) store source frameRoots)
    (resolved : IxIR1.resolveAtoms source sourceArguments = .ok values) :
    SourceOwnershipAt checked.artifact.trace.positions calleeTrace.root store
      values.reverse frameRoots := by
  obtain ⟨before, beforeMember, transition⟩ :=
    checked.tailCallPosition callerMember signatureAt descendant
  unfold Lower.PositionTrace.tailCallMatches at transition
  simp only [Bool.and_eq_true] at transition
  cases consumedEq : Lower.callRemainingCapabilities?
      before.sourceCapabilities input calleeTrace.generated.signature
        sourceArguments with
  | none => simp [consumedEq] at transition
  | some remaining =>
      simp only [consumedEq] at transition
      have noRoots := SourceOwnershipInvariant.rootsForCapabilities_eq_nil_of_noOwnedRoots
        (source := source) transition.2
      have beforeInvariant := ownership before beforeMember (by
        simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
          Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
            transition.1)
      change SourceOwnershipInvariant store source input
        before.sourceCapabilities frameRoots at beforeInvariant
      intro entry entryMember entryCoordinate
      have entryEq := checked.entryCapabilities calleeMember entryMember
        entryCoordinate
      rw [entryEq]
      simpa [noRoots] using
        beforeInvariant.callEntryInvariant (calleeInput := calleeTrace.root.sourceInputMap)
          resolved consumedEq

/-- A checked recursive tail call likewise transfers every local owner and
re-enters the same root with the unchanged enclosing frame suffix. -/
theorem tailCallSelfEntry {checked : Lower.Checked}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {sourceArguments : Array IxIR1.Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.tailCallSelf site blockId input entryValueCount sourceArguments
        generated))
    {store : IxIR1.Store} {source values : List RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.tailCallSelf site blockId input entryValueCount sourceArguments
        generated) store source frameRoots)
    (resolved : IxIR1.resolveAtoms source sourceArguments = .ok values) :
    SourceOwnershipAt checked.artifact.trace.positions functionTrace.root store
      values.reverse frameRoots := by
  obtain ⟨before, beforeMember, transition⟩ :=
    checked.tailCallSelfPosition functionMember descendant
  unfold Lower.PositionTrace.tailCallMatches at transition
  simp only [Bool.and_eq_true] at transition
  cases consumedEq : Lower.callRemainingCapabilities?
      before.sourceCapabilities input functionTrace.generated.signature
        sourceArguments with
  | none => simp [consumedEq] at transition
  | some remaining =>
      simp only [consumedEq] at transition
      have noRoots := SourceOwnershipInvariant.rootsForCapabilities_eq_nil_of_noOwnedRoots
        (source := source) transition.2
      have beforeInvariant := ownership before beforeMember (by
        simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
          Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
            transition.1)
      change SourceOwnershipInvariant store source input
        before.sourceCapabilities frameRoots at beforeInvariant
      intro entry entryMember entryCoordinate
      have entryEq := checked.entryCapabilities functionMember entryMember
        entryCoordinate
      rw [entryEq]
      simpa [noRoots] using
        beforeInvariant.callEntryInvariant
          (calleeInput := functionTrace.root.sourceInputMap) resolved consumedEq

/-- At a checked return, consuming the declared result leaves exactly that
result root followed by the suspended caller-frame roots. -/
theorem returnRoot {checked : Lower.Checked}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.ret site blockId input entryValueCount sourceAtom targetAtom generated))
    {store : IxIR1.Store} {source : List RVal} {value : RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.ret site blockId input entryValueCount sourceAtom targetAtom generated)
      store source frameRoots)
    (resolved : IxIR1.resolveAtom source sourceAtom = .ok value) :
    IxIR1.Sim.RootOwnership store
      (⟨functionTrace.generated.signature.result, value⟩ :: frameRoots) := by
  obtain ⟨position, positionMember, coordinate⟩ :=
    checked.position functionMember descendant
  have coordinate' : position.coordinateMatches site blockId .terminator input =
      true := by
    simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
      Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
        coordinate
  have transition := checked.returnPositionMatch functionMember descendant
    positionMember coordinate'
  unfold Lower.PositionTrace.returnMatches at transition
  simp only [Bool.and_eq_true] at transition
  cases consumedEq : Lower.consumeCapability? position.sourceCapabilities input
      functionTrace.generated.signature.result sourceAtom with
  | none => simp [consumedEq] at transition
  | some remaining =>
      simp only [consumedEq] at transition
      have invariant := ownership position positionMember coordinate
      change SourceOwnershipInvariant store source input
        position.sourceCapabilities frameRoots at invariant
      obtain ⟨_, readyOwnership⟩ :=
        SourceOwnershipInvariant.consumeCapability_ownership
        (consumedRoots := []) (suffixRoots := frameRoots) invariant.holds
        (by simpa using invariant.ownership) resolved consumedEq
      have noRoots :=
        SourceOwnershipInvariant.rootsForCapabilities_eq_nil_of_noOwnedRoots
          (source := source) transition.2
      simpa [noRoots] using readyOwnership

/-- Restore an addressed ordinary-call continuation directly from the
callee's terminal framed ownership, with no caller-supplied post-call
ownership premise. -/
theorem callResult {checked : Lower.Checked}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {address : Ix.Compiler.Ixon.Address} {signature : Signature}
    {sourceArguments : Array IxIR1.Atom} {instruction : Instr}
    {next : Lower.CodeTrace}
    (signatureAt : Lower.targetSignature?
      checked.artifact.program.declarations address = some signature)
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.call address sourceArguments) index instruction next))
    {before : Lower.PositionTrace} {remaining : Array Lower.BindingCap}
    (beforeMember : before ∈ checked.artifact.trace.positions)
    (beforeCoordinate : before.coordinateMatches site blockId
      (.instruction index) input = true)
    {beforeStore afterStore : IxIR1.Store} {source values : List RVal}
    {value : RVal} {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.call address sourceArguments) index instruction next)
      beforeStore source frameRoots)
    (resolved : IxIR1.resolveAtoms source sourceArguments = .ok values)
    (consumed : Lower.callRemainingCapabilities? before.sourceCapabilities input
      signature sourceArguments = some remaining)
    (resultOwnership : IxIR1.Sim.RootOwnership afterStore
      (⟨signature.result, value⟩ ::
        (rootsForCapabilities remaining.toList source ++ frameRoots))) :
    SourceOwnershipAt checked.artifact.trace.positions next afterStore
      (value :: source) frameRoots := by
  have beforeInvariant := ownership before beforeMember (by
    simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
      Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
        beforeCoordinate)
  change SourceOwnershipInvariant beforeStore source input
    before.sourceCapabilities frameRoots at beforeInvariant
  intro after afterMember afterCoordinate
  have transition := checked.callTransition functionMember signatureAt
    descendant beforeMember beforeCoordinate afterMember afterCoordinate
  unfold Lower.PositionTrace.callResultMatches at transition
  simp only [consumed, Bool.and_eq_true, beq_iff_eq] at transition
  rw [← transition.2]
  exact beforeInvariant.callResultInvariant resolved consumed transition.1
    resultOwnership

/-- Restore a recursive ordinary-call continuation from the callee's exact
terminal ownership. -/
theorem callSelfResult {checked : Lower.Checked}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {sourceArguments : Array IxIR1.Atom} {instruction : Instr}
    {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.callSelf sourceArguments) index instruction next))
    {before : Lower.PositionTrace} {remaining : Array Lower.BindingCap}
    (beforeMember : before ∈ checked.artifact.trace.positions)
    (beforeCoordinate : before.coordinateMatches site blockId
      (.instruction index) input = true)
    {beforeStore afterStore : IxIR1.Store} {source values : List RVal}
    {value : RVal} {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.callSelf sourceArguments) index instruction next)
      beforeStore source frameRoots)
    (resolved : IxIR1.resolveAtoms source sourceArguments = .ok values)
    (consumed : Lower.callRemainingCapabilities? before.sourceCapabilities input
      functionTrace.generated.signature sourceArguments = some remaining)
    (resultOwnership : IxIR1.Sim.RootOwnership afterStore
      (⟨functionTrace.generated.signature.result, value⟩ ::
        (rootsForCapabilities remaining.toList source ++ frameRoots))) :
    SourceOwnershipAt checked.artifact.trace.positions next afterStore
      (value :: source) frameRoots := by
  have beforeInvariant := ownership before beforeMember (by
    simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
      Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
        beforeCoordinate)
  change SourceOwnershipInvariant beforeStore source input
    before.sourceCapabilities frameRoots at beforeInvariant
  intro after afterMember afterCoordinate
  have transition := checked.callSelfTransition functionMember descendant
    beforeMember beforeCoordinate afterMember afterCoordinate
  unfold Lower.PositionTrace.callResultMatches at transition
  simp only [consumed, Bool.and_eq_true, beq_iff_eq] at transition
  rw [← transition.2]
  exact beforeInvariant.callResultInvariant resolved consumed transition.1
    resultOwnership

end SourceOwnershipAt

/-- Checked allocation derives its target field-world evidence from the
producer capability position and the dynamic ownership invariant at that
recursive trace node.  No allocation-shaped root list is supplied by the
caller. -/
theorem StoreRel.fieldWorlds_of_checked_allocation_capabilities
    {checked : Lower.Checked} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount index : Nat}
    {world : Ix.Compiler.Ixon.Owned} {identity : CtorId}
    {sourceArguments : Array IxIR1.Atom} {instruction : Instr}
    {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.alloc world identity sourceArguments) index instruction next))
    {sourceStore : IxIR1.Store} {targetStore : Eval.Store}
    (relation : StoreRel sourceStore targetStore)
    {source : List RVal} {values : List RVal} {schema : CtorSchema}
    {frameRoots : List IxIR1.Sim.Root}
    (ownershipAt : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.alloc world identity sourceArguments) index instruction next)
      sourceStore source frameRoots)
    (resolved : IxIR1.resolveAtoms source sourceArguments = .ok values)
    (schemaAt : checked.artifact.validationContext.schemas world identity =
      some schema) :
    Eval.FieldWorlds targetStore schema values.toArray := by
  obtain ⟨position, positionMember, positionMatch⟩ :=
    checked.allocationPosition functionMember descendant
  have coordinate :=
    position.coordinateMatches_of_allocationMatch positionMatch
  have ownership := ownershipAt position positionMember (by
      simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceBlock,
        Lower.CodeTrace.targetPosition, Lower.CodeTrace.sourceInputMap] using
          coordinate)
  change SourceOwnershipInvariant sourceStore source input
    position.sourceCapabilities frameRoots at ownership
  apply relation.fieldWorlds_replicate
    (checked.allocationSchemaFields functionMember descendant schemaAt)
  · simpa using IxIR1.resolveAtoms_length resolved
  · exact ownership.resolveAtoms_hasWorld positionMatch resolved

/-- The exact source-side condition needed to reconcile shared release:
IxIR₁ historically permits decrementing a malformed live node from zero,
whereas IxIR₂ rejects that state.  No allocation-order or ownership-graph
assumption is needed by the recursive work-list correspondence. -/
def PositiveSharedRC (store : IxIR1.Store) : Prop :=
  ∀ {location box}, store.get? location = some box →
    box.world = .shared → 0 < box.rc

/-- The source runtime facts threaded by the recursive structured simulation.
Allocation order supplies the strict live-RC premise required by destructive
IxIR₂ steps, bounded roots prevent stale evaluator bindings from naming
future append locations, and live PAPs retain the source evaluator's strict
under-saturation guarantee. -/
structure SourceRuntimeInvariant (store : IxIR1.Store)
    (roots : List RVal) : Prop where
  order : IxIR1.Reclamation.AllocationOrderInvariant store
  rootsInBounds : IxIR1.Reclamation.ValuesInBounds store roots
  papsUnder : IxIR1.Reclamation.PAPsUnder store

namespace SourceRuntimeInvariant

/-- The empty source machine establishes the recursive runtime invariant. -/
theorem empty : SourceRuntimeInvariant ({} : IxIR1.Store) [] :=
  ⟨IxIR1.Reclamation.AllocationOrderInvariant.empty,
    IxIR1.Reclamation.ValuesInBounds.nil _,
    IxIR1.Reclamation.PAPsUnder.empty⟩

/-- Allocation order is stronger than the shared-only positivity premise used
by the exact destructive-step simulation. -/
theorem positiveSharedRC {store : IxIR1.Store} {roots : List RVal}
    (invariant : SourceRuntimeInvariant store roots) :
    PositiveSharedRC store := by
  intro location box found _
  exact invariant.order.rc_pos found

/-- Heap-world evidence for an owned root implies that its location, when
present, lies within the current append-only node array. -/
private theorem hasWorld_valueInBounds {store : IxIR1.Store}
    {world : Ix.Compiler.Ixon.Owned} {value : RVal}
    (hasWorld : IxIR1.Sim.HasWorld store world value) :
    IxIR1.Reclamation.ValueInBounds store value := by
  cases value with
  | loc location =>
      obtain ⟨box, found, _⟩ := hasWorld
      exact IxIR1.Reclamation.RVal.inBounds_of_get? found
  | lit literal => trivial
  | erased => trivial

/-- Canonical shared callee-entry roots provide the bounded environment half
of the runtime invariant; allocation order is supplied by the PAP
retain/release prefix. -/
theorem sharedEntry {store : IxIR1.Store} {values : List RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (order : IxIR1.Reclamation.AllocationOrderInvariant store)
    (papsUnder : IxIR1.Reclamation.PAPsUnder store)
    (ownership : IxIR1.Sim.RootOwnership store
      (IxIR1.Sim.rootsFor .shared values ++ frameRoots)) :
    SourceRuntimeInvariant store values.reverse := by
  have bounds : IxIR1.Reclamation.ValuesInBounds store values := by
    intro value member
    apply hasWorld_valueInBounds
    apply ownership.roots_world ⟨.shared, value⟩
    exact List.mem_append_left _ (by
      simpa [IxIR1.Sim.rootsFor] using member)
  exact ⟨order, bounds.reverse, papsUnder⟩

/-- Resolving one source atom cannot manufacture a future heap location. -/
theorem resolveAtom {store : IxIR1.Store} {roots : List RVal}
    (invariant : SourceRuntimeInvariant store roots)
    {atom : IxIR1.Atom} {value : RVal}
    (resolved : IxIR1.resolveAtom roots atom = .ok value) :
    IxIR1.Reclamation.ValueInBounds store value :=
  IxIR1.Reclamation.resolveAtom_inBounds invariant.rootsInBounds resolved

/-- A resolved source argument vector is a valid root set in the unchanged
store. -/
theorem resolveAtoms {store : IxIR1.Store} {roots : List RVal}
    (invariant : SourceRuntimeInvariant store roots)
    {atoms : Array IxIR1.Atom} {values : List RVal}
    (resolved : IxIR1.resolveAtoms roots atoms = .ok values) :
    SourceRuntimeInvariant store values :=
  ⟨invariant.order,
    IxIR1.Reclamation.resolveAtoms_inBounds invariant.rootsInBounds resolved,
    invariant.papsUnder⟩

/-- Call entry reverses source arguments into the callee's de Bruijn
environment without changing their boundedness. -/
theorem resolveAtomsReverse {store : IxIR1.Store} {roots : List RVal}
    (invariant : SourceRuntimeInvariant store roots)
    {atoms : Array IxIR1.Atom} {values : List RVal}
    (resolved : IxIR1.resolveAtoms roots atoms = .ok values) :
    SourceRuntimeInvariant store values.reverse :=
  ⟨invariant.order,
    (IxIR1.Reclamation.resolveAtoms_inBounds
      invariant.rootsInBounds resolved).reverse,
    invariant.papsUnder⟩

/-- Constructor dispatch prepends the live node's fields, in the evaluator's
reverse field order, to the child environment. Allocation order proves every
field is already bounded. -/
theorem constructorBranch {store : IxIR1.Store} {roots : List RVal}
    (invariant : SourceRuntimeInvariant store roots)
    {location : Nat} {box : IxIR1.NodeBox} {cid : CtorId}
    {fields : Array RVal}
    (found : store.get? location = some box)
    (node : box.node = .ctorN cid fields) :
    SourceRuntimeInvariant store (fields.toList.reverse ++ roots) := by
  have fieldBounds :
      IxIR1.Reclamation.ValuesInBounds store fields.toList := by
    have children := invariant.order.childrenInBounds found
    simpa [IxIR1.Sim.nodeChildren, node] using children
  exact ⟨invariant.order,
    fieldBounds.reverse.append invariant.rootsInBounds,
    invariant.papsUnder⟩

/-- Peeling a Nat successor adds only a scalar predecessor to the child
environment, so the heap component of the invariant is unchanged. -/
theorem natSuccessor {store : IxIR1.Store} {roots : List RVal}
    (invariant : SourceRuntimeInvariant store roots) (predecessor : Nat) :
    SourceRuntimeInvariant store (.lit (.nat predecessor) :: roots) :=
  ⟨invariant.order,
    IxIR1.Reclamation.ValuesInBounds.cons (by trivial)
      invariant.rootsInBounds,
    invariant.papsUnder⟩

/-- A successful source code run that executes no reuse preserves allocation
order, keeps the old environment bounded, and adds the result as a bounded
root. -/
theorem runCode {ctx : IxIR1.Ctx} {fuel : Nat} {cur : IxIR1.FnDef}
    {store store' : IxIR1.Store} {env : List RVal} {code : IxIR1.Code}
    {value : RVal} (invariant : SourceRuntimeInvariant store env)
    (reuses : store'.reuses = store.reuses)
    (run : IxIR1.runCode ctx fuel cur store env code = .ok (store', value)) :
    SourceRuntimeInvariant store' (value :: env) := by
  have ordered := IxIR1.Reclamation.runCode_order_of_reuses_eq
    invariant.order invariant.rootsInBounds reuses run
  have oldRoots := invariant.rootsInBounds.mono
    (IxIR1.Reclamation.runCode_footprint run).nodes_size
  have papsUnder := IxIR1.Reclamation.runCode_papsUnder_of_reuses_eq
    invariant.order invariant.rootsInBounds invariant.papsUnder reuses run
  exact ⟨ordered.1,
    IxIR1.Reclamation.ValuesInBounds.cons ordered.2 oldRoots,
    papsUnder⟩

/-- Operation-level form of `runCode`; this is the induction rule used at a
generated nonterminal instruction. -/
theorem runOp {ctx : IxIR1.Ctx} {fuel : Nat} {cur : IxIR1.FnDef}
    {store store' : IxIR1.Store} {env : List RVal} {op : IxIR1.Op}
    {value : RVal} (invariant : SourceRuntimeInvariant store env)
    (reuses : store'.reuses = store.reuses)
    (run : IxIR1.runOp ctx fuel cur store env op = .ok (store', value)) :
    SourceRuntimeInvariant store' (value :: env) := by
  have ordered := IxIR1.Reclamation.runOp_order_of_reuses_eq
    invariant.order invariant.rootsInBounds reuses run
  have oldRoots := invariant.rootsInBounds.mono
    (IxIR1.Reclamation.runOp_footprint run).nodes_size
  have papsUnder := IxIR1.Reclamation.runOp_papsUnder_of_reuses_eq
    invariant.order invariant.rootsInBounds invariant.papsUnder reuses run
  exact ⟨ordered.1,
    IxIR1.Reclamation.ValuesInBounds.cons ordered.2 oldRoots,
    papsUnder⟩

/-- A successful declared invocation preserves the invariant on its argument
roots and adds the returned value. -/
theorem invoke {ctx : IxIR1.Ctx} {fuel : Nat} {address : Ixon.Address}
    {args : List RVal} {store store' : IxIR1.Store} {value : RVal}
    (invariant : SourceRuntimeInvariant store args)
    (reuses : store'.reuses = store.reuses)
    (run : IxIR1.invoke ctx fuel address args store = .ok (store', value)) :
    SourceRuntimeInvariant store' (value :: args) := by
  have ordered := IxIR1.Reclamation.invoke_order_of_reuses_eq
    invariant.order invariant.rootsInBounds reuses run
  have oldRoots := invariant.rootsInBounds.mono
    (IxIR1.Reclamation.invoke_footprint run).nodes_size
  have papsUnder := IxIR1.Reclamation.invoke_papsUnder_of_reuses_eq
    invariant.order invariant.rootsInBounds invariant.papsUnder reuses run
  exact ⟨ordered.1,
    IxIR1.Reclamation.ValuesInBounds.cons ordered.2 oldRoots,
    papsUnder⟩

/-- A successful higher-order application preserves the function/argument
root set and adds its result. -/
theorem applyGo {ctx : IxIR1.Ctx} {fuel : Nat}
    {store store' : IxIR1.Store} {function : RVal} {args : List RVal}
    {value : RVal}
    (invariant : SourceRuntimeInvariant store (function :: args))
    (reuses : store'.reuses = store.reuses)
    (run : IxIR1.applyGo ctx fuel store function args = .ok (store', value)) :
    SourceRuntimeInvariant store' (value :: function :: args) := by
  have ordered := IxIR1.Reclamation.applyGo_order_of_reuses_eq
    invariant.order (invariant.rootsInBounds _ (by simp))
    (fun argument member => invariant.rootsInBounds argument (by simp [member]))
    reuses run
  have oldRoots := invariant.rootsInBounds.mono
    (IxIR1.Reclamation.applyGo_footprint run).nodes_size
  have papsUnder := IxIR1.Reclamation.applyGo_papsUnder_of_reuses_eq
    invariant.order (invariant.rootsInBounds _ (by simp))
    (fun argument member => invariant.rootsInBounds argument (by
      simp [member])) invariant.papsUnder reuses run
  exact ⟨ordered.1,
    IxIR1.Reclamation.ValuesInBounds.cons ordered.2 oldRoots,
    papsUnder⟩

/-- Reuse-free syntax discharges the counter premise of `runCode`. -/
theorem runCodeNoReuse {ctx : IxIR1.Ctx} {fuel : Nat} {cur : IxIR1.FnDef}
    {store store' : IxIR1.Store} {env : List RVal} {code : IxIR1.Code}
    {value : RVal} (invariant : SourceRuntimeInvariant store env)
    (hctx : IxIR1.NoReuse.CtxNoReuse ctx)
    (hcur : IxIR1.NoReuse.CodeNoReuse cur.body)
    (hcode : IxIR1.NoReuse.CodeNoReuse code)
    (run : IxIR1.runCode ctx fuel cur store env code = .ok (store', value)) :
    SourceRuntimeInvariant store' (value :: env) :=
  invariant.runCode
    (IxIR1.NoReuse.runCode_reuses_eq hctx hcur hcode run) run

/-- Reuse-free syntax discharges the counter premise of `runOp`. -/
theorem runOpNoReuse {ctx : IxIR1.Ctx} {fuel : Nat} {cur : IxIR1.FnDef}
    {store store' : IxIR1.Store} {env : List RVal} {op : IxIR1.Op}
    {value : RVal} (invariant : SourceRuntimeInvariant store env)
    (hctx : IxIR1.NoReuse.CtxNoReuse ctx)
    (hcur : IxIR1.NoReuse.CodeNoReuse cur.body)
    (hop : IxIR1.NoReuse.OpNoReuse op)
    (run : IxIR1.runOp ctx fuel cur store env op = .ok (store', value)) :
    SourceRuntimeInvariant store' (value :: env) :=
  invariant.runOp
    (IxIR1.NoReuse.runOp_reuses_eq hctx hcur hop run) run

/-- Context no-reuse discharges the counter premise of declared invocation. -/
theorem invokeNoReuse {ctx : IxIR1.Ctx} {fuel : Nat}
    {address : Ixon.Address} {args : List RVal}
    {store store' : IxIR1.Store} {value : RVal}
    (invariant : SourceRuntimeInvariant store args)
    (hctx : IxIR1.NoReuse.CtxNoReuse ctx)
    (run : IxIR1.invoke ctx fuel address args store = .ok (store', value)) :
    SourceRuntimeInvariant store' (value :: args) :=
  invariant.invoke (IxIR1.NoReuse.invoke_reuses_eq hctx run) run

/-- Context no-reuse discharges the counter premise of higher-order
application. -/
theorem applyGoNoReuse {ctx : IxIR1.Ctx} {fuel : Nat}
    {store store' : IxIR1.Store} {function : RVal} {args : List RVal}
    {value : RVal}
    (invariant : SourceRuntimeInvariant store (function :: args))
    (hctx : IxIR1.NoReuse.CtxNoReuse ctx)
    (run : IxIR1.applyGo ctx fuel store function args = .ok (store', value)) :
    SourceRuntimeInvariant store' (value :: function :: args) :=
  invariant.applyGo (IxIR1.NoReuse.applyGo_reuses_eq hctx run) run

end SourceRuntimeInvariant

private theorem sourceNodesGet_of_get {store : IxIR1.Store}
    {location : Nat} {box : IxIR1.NodeBox}
    (found : store.get? location = some box) :
    store.nodes[location]? = some (some box) := by
  rw [IxIR1.Store.get?, Option.bind_eq_some_iff] at found
  obtain ⟨slot, slotAt, equal⟩ := found
  change slot = some box at equal
  subst slot
  exact slotAt

private theorem sourceGet_setBox_same {store : IxIR1.Store}
    {location : Nat} {old new : IxIR1.NodeBox}
    (found : store.get? location = some old) :
    (store.setBox location new).get? location = some new := by
  have nodesAt := sourceNodesGet_of_get found
  obtain ⟨inBounds, _⟩ := Array.getElem?_eq_some_iff.mp nodesAt
  simp [IxIR1.Store.setBox, IxIR1.Store.get?,
    Array.set!_eq_setIfInBounds, inBounds]

private theorem sourceGet_of_setBox_other {store : IxIR1.Store}
    {location other : Nat} {old new box : IxIR1.NodeBox}
    (different : location ≠ other)
    (live : store.get? location = some old)
    (found : (store.setBox location new).get? other = some box) :
    store.get? other = some box := by
  have nodesAt := sourceNodesGet_of_get live
  obtain ⟨inBounds, _⟩ := Array.getElem?_eq_some_iff.mp nodesAt
  simpa [IxIR1.Store.setBox, IxIR1.Store.get?,
    Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
    inBounds, different] using found

private theorem sourceGet_kill_same {store : IxIR1.Store}
    {location : Nat} {box : IxIR1.NodeBox}
    (found : store.get? location = some box) :
    (store.kill location).get? location = none := by
  have nodesAt := sourceNodesGet_of_get found
  obtain ⟨inBounds, _⟩ := Array.getElem?_eq_some_iff.mp nodesAt
  simp [IxIR1.Store.kill, IxIR1.Store.get?,
    Array.set!_eq_setIfInBounds, inBounds]

private theorem sourceGet_of_kill_other {store : IxIR1.Store}
    {location other : Nat} {old box : IxIR1.NodeBox}
    (different : location ≠ other)
    (live : store.get? location = some old)
    (found : (store.kill location).get? other = some box) :
    store.get? other = some box := by
  have nodesAt := sourceNodesGet_of_get live
  obtain ⟨inBounds, _⟩ := Array.getElem?_eq_some_iff.mp nodesAt
  simpa [IxIR1.Store.kill, IxIR1.Store.get?,
    Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
    inBounds, different] using found

theorem PositiveSharedRC.rcTick {store : IxIR1.Store}
    (positive : PositiveSharedRC store) : PositiveSharedRC store.rcTick := by
  intro location box found shared
  exact positive (by
    simpa [IxIR1.Store.rcTick, IxIR1.Store.get?] using found) shared

theorem PositiveSharedRC.setRc {store : IxIR1.Store} {location : Nat}
    {box : IxIR1.NodeBox} {newRC : Nat}
    (positive : PositiveSharedRC store)
    (found : store.get? location = some box) (newPositive : 0 < newRC) :
    PositiveSharedRC (store.setBox location { box with rc := newRC }) := by
  intro other otherBox otherFound otherShared
  by_cases equal : location = other
  · subst other
    have updated := sourceGet_setBox_same
      (new := { box with rc := newRC }) found
    have boxEqual : otherBox = { box with rc := newRC } :=
      Option.some.inj (otherFound.symm.trans updated)
    subst otherBox
    exact newPositive
  · exact positive
      (sourceGet_of_setBox_other equal found otherFound) otherShared

theorem PositiveSharedRC.kill {store : IxIR1.Store} {location : Nat}
    {box : IxIR1.NodeBox} (positive : PositiveSharedRC store)
    (found : store.get? location = some box) :
    PositiveSharedRC (store.kill location) := by
  intro other otherBox otherFound otherShared
  by_cases equal : location = other
  · subst other
    rw [sourceGet_kill_same found] at otherFound
    contradiction
  · exact positive (sourceGet_of_kill_other equal found otherFound)
      otherShared

/-- A proof-side source-slot map. `none` marks a source binding whose ownership
has already been consumed. The target register remains physically present
inside its current SSA block, but no later source operand may resolve through
that slot. -/
abbrev EnvMap := Array (Option Atom)

/-- Translate one live source atom through an explicit source-slot-to-target-
atom map. The executable compiler certificate and runtime simulation share
this single definition; dead entries deliberately fail translation. -/
abbrev translateAtom (mapping : EnvMap) : IxIR1.Atom → Option Atom :=
  Lower.InputMap.translateAtom mapping

/-- Every live source environment slot resolves through its generated target
atom to the same runtime value. Dead ownership slots are deliberately absent
from this semantic premise. -/
def EnvRel (source : List RVal) (target : Array RVal)
    (mapping : EnvMap) : Prop :=
  ∀ (index : Nat) (value : RVal) (atom : Atom),
    source[index]? = some value →
    mapping[index]? = some (some atom) →
    Eval.resolveAtom target atom = .ok value

/-- The empty source environment is related to the empty proof map. -/
theorem EnvRel.empty (target : Array RVal := #[]) :
    EnvRel [] target #[] := by
  intro index value atom sourceGet
  simp at sourceGet

/-- Two live source slots mapped to the same target register contain the same
runtime value. -/
private theorem EnvRel.source_eq_of_same_reg
    {source : List RVal} {target : Array RVal} {input : EnvMap}
    (relation : EnvRel source target input)
    {leftIndex rightIndex register : Nat} {leftValue rightValue : RVal}
    (leftSource : source[leftIndex]? = some leftValue)
    (rightSource : source[rightIndex]? = some rightValue)
    (leftInput : input[leftIndex]? = some (some (.reg register)))
    (rightInput : input[rightIndex]? = some (some (.reg register))) :
    leftValue = rightValue := by
  have leftResolved := relation leftIndex leftValue (.reg register)
    leftSource leftInput
  have rightResolved := relation rightIndex rightValue (.reg register)
    rightSource rightInput
  exact Except.ok.inj (leftResolved.symm.trans rightResolved)

/-- A successful static edge-owner search identifies a live owned source slot
whose predecessor atom is exactly the requested lender register. -/
private theorem edgeOwnerIndex?_facts
    {capabilities : Array Lower.BindingCap} {input : EnvMap}
    {lender ownerIndex : Nat}
    (found : Lower.edgeOwnerIndex? capabilities input lender =
      some ownerIndex) :
    ∃ world,
      capabilities[ownerIndex]? = some (.owned world) ∧
      input[ownerIndex]? = some (some (.reg lender)) := by
  unfold Lower.edgeOwnerIndex? at found
  have member := List.mem_of_find?_eq_some found
  have matched := List.find?_some found
  have bound : ownerIndex < capabilities.size := by
    simpa using (List.mem_range.mp member)
  cases capabilityAt : capabilities[ownerIndex]? with
  | none => simp [capabilityAt] at matched
  | some capability =>
      cases capability with
      | scalar | borrowed | dead => simp [capabilityAt] at matched
      | owned world =>
          cases inputAt : input[ownerIndex]? with
          | none => simp [capabilityAt, inputAt] at matched
          | some slot =>
              cases slot with
              | none => simp [capabilityAt, inputAt] at matched
              | some atom =>
                  cases atom with
                  | lit literal => simp [capabilityAt, inputAt] at matched
                  | erased => simp [capabilityAt, inputAt] at matched
                  | reg actual =>
                      have actualEq : actual = lender :=
                        beq_iff_eq.mp (by
                          simpa [capabilityAt, inputAt] using matched)
                      subst actual
                      exact ⟨world, rfl, rfl⟩

/-- Edge rebasing changes only borrow-lender names (or maps an invalid lender
to `dead`); it preserves every dynamic pointwise capability fact. -/
private theorem CapabilityHolds.rebaseEdge
    {store : IxIR1.Store} {value : RVal}
    {allCapabilities : Array Lower.BindingCap} {input : EnvMap}
    {capability : Lower.BindingCap}
    (holds : CapabilityHolds store capability value) :
    CapabilityHolds store
      ((capability.rebaseEdge? allCapabilities input).getD .dead) value := by
  cases capability with
  | scalar => simpa [Lower.BindingCap.rebaseEdge?, CapabilityHolds] using holds
  | owned world =>
      simpa [Lower.BindingCap.rebaseEdge?, CapabilityHolds] using holds
  | dead => simp [Lower.BindingCap.rebaseEdge?, CapabilityHolds]
  | borrowed world lender =>
      cases lender with
      | caller =>
          simpa [Lower.BindingCap.rebaseEdge?, CapabilityHolds] using holds
      | value lender =>
          cases owner : Lower.edgeOwnerIndex? allCapabilities input lender with
          | none =>
              simp [Lower.BindingCap.rebaseEdge?, owner,
                CapabilityHolds]
          | some ownerIndex =>
              simp only [Lower.BindingCap.rebaseEdge?, owner]
              generalize lookupEq : allCapabilities[ownerIndex]? = lookup
              cases lookup with
              | none => simp [CapabilityHolds]
              | some ownerCapability =>
                  cases ownerCapability with
                  | scalar => simp [CapabilityHolds]
                  | borrowed ownerWorld ownerLender =>
                      simp [CapabilityHolds]
                  | dead => simp [CapabilityHolds]
                  | owned ownerWorld =>
                      by_cases same : ownerWorld = world
                      · simpa [same, CapabilityHolds] using holds
                      · simp [same, CapabilityHolds]

/-- Edge rebasing does not change which source slots contribute ownership
roots. -/
private theorem rootsForCapabilities_rebaseEdge
    (allCapabilities : Array Lower.BindingCap) (input : EnvMap) :
    ∀ (capabilities : List Lower.BindingCap) (source : List RVal),
      rootsForCapabilities
          (capabilities.map fun capability =>
            (capability.rebaseEdge? allCapabilities input).getD .dead)
          source =
        rootsForCapabilities capabilities source := by
  intro capabilities
  induction capabilities with
  | nil => intro source; simp [rootsForCapabilities]
  | cons capability capabilities ih =>
      intro source
      cases source with
      | nil => simp [rootsForCapabilities]
      | cons value values =>
          cases capability with
          | scalar =>
              change rootsForCapabilities
                  (capabilities.map fun capability =>
                    (capability.rebaseEdge? allCapabilities input).getD .dead)
                  values = rootsForCapabilities capabilities values
              exact ih values
          | owned world =>
              change (⟨world, value⟩ : IxIR1.Sim.Root) ::
                    rootsForCapabilities
                      (capabilities.map fun capability =>
                        (capability.rebaseEdge? allCapabilities input).getD
                          .dead)
                      values =
                  ⟨world, value⟩ :: rootsForCapabilities capabilities values
              exact congrArg (List.cons ⟨world, value⟩) (ih values)
          | dead =>
              change rootsForCapabilities
                  (capabilities.map fun capability =>
                    (capability.rebaseEdge? allCapabilities input).getD .dead)
                  values = rootsForCapabilities capabilities values
              exact ih values
          | borrowed world lender =>
              cases lender with
              | caller =>
                  change rootsForCapabilities
                      (capabilities.map fun capability =>
                        (capability.rebaseEdge? allCapabilities input).getD
                          .dead)
                      values = rootsForCapabilities capabilities values
                  exact ih values
              | value lender =>
                  cases owner : Lower.edgeOwnerIndex? allCapabilities input
                      lender with
                  | none =>
                      simpa only [List.map_cons,
                        Lower.BindingCap.rebaseEdge?, owner,
                        Option.getD_none,
                        rootsForCapabilities] using ih values
                  | some ownerIndex =>
                      simp only [List.map_cons,
                        Lower.BindingCap.rebaseEdge?, owner]
                      generalize lookupEq :
                        allCapabilities[ownerIndex]? = lookup
                      cases lookup with
                      | none =>
                          change rootsForCapabilities
                              (capabilities.map fun capability =>
                                (capability.rebaseEdge? allCapabilities
                                  input).getD .dead)
                              values = rootsForCapabilities capabilities values
                          exact ih values
                      | some ownerCapability =>
                          cases ownerCapability with
                          | scalar | borrowed | dead =>
                              change rootsForCapabilities
                                  (capabilities.map fun capability =>
                                    (capability.rebaseEdge? allCapabilities
                                      input).getD .dead)
                                  values = rootsForCapabilities capabilities values
                              exact ih values
                          | owned ownerWorld =>
                              by_cases same : ownerWorld = world
                              · have sameBool :
                                    (ownerWorld == world) = true := by
                                  simpa using same
                                simpa [Lower.BindingCap.rebaseEdge?, sameBool,
                                  rootsForCapabilities] using ih values
                              · have different :
                                    ¬ ((ownerWorld == world) = true) := by
                                  simpa using same
                                simpa [Lower.BindingCap.rebaseEdge?, different,
                                  rootsForCapabilities] using ih values

namespace SourceOwnershipInvariant

/-- Crossing a canonical generated CFG edge preserves exact dynamic source
ownership. Local borrow lenders are renamed from predecessor SSA registers to
the same-index successor parameters selected by the checked edge audit. -/
theorem edge
    {store : IxIR1.Store} {source : List RVal} {target : Array RVal}
    {input : EnvMap} {capabilities afterCapabilities :
      Array Lower.BindingCap} {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    (environments : EnvRel source target input)
    (transition : Lower.edgeCapabilities? capabilities input =
      some afterCapabilities) :
    SourceOwnershipInvariant store source
      (Lower.EdgeTrace.explicitMapOf input) afterCapabilities frameRoots := by
  unfold Lower.edgeCapabilities? at transition
  split at transition <;> try contradiction
  injection transition with afterEq
  subst afterCapabilities
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using invariant.length
  · intro index capability value capabilityAt valueAt
    rw [Array.getElem?_map] at capabilityAt
    cases oldAt : capabilities[index]? with
    | none => simp [oldAt] at capabilityAt
    | some oldCapability =>
        simp only [oldAt, Option.map_some, Option.some.injEq] at capabilityAt
        subst capability
        exact CapabilityHolds.rebaseEdge
          (invariant.holds oldAt valueAt)
  · simpa [Array.toList_map,
      rootsForCapabilities_rebaseEdge] using invariant.ownership
  · intro index world lender value capabilityAt valueAt
    rw [Array.getElem?_map] at capabilityAt
    cases oldAt : capabilities[index]? with
    | none => simp [oldAt] at capabilityAt
    | some oldCapability =>
        simp only [oldAt, Option.map_some, Option.some.injEq] at capabilityAt
        cases oldCapability with
        | scalar =>
            simp [Lower.BindingCap.rebaseEdge?] at capabilityAt
        | owned oldWorld =>
            simp [Lower.BindingCap.rebaseEdge?] at capabilityAt
        | dead =>
            simp [Lower.BindingCap.rebaseEdge?] at capabilityAt
        | borrowed oldWorld oldLender =>
            cases oldLender with
            | caller =>
                have outputEq :
                    Lower.BindingCap.borrowed oldWorld .caller =
                      .borrowed world lender := by
                  simpa [Lower.BindingCap.rebaseEdge?] using capabilityAt
                injection outputEq with worldEq lenderEq
                subst world
                subst lender
                exact invariant.borrows oldAt valueAt
            | value oldLender =>
                cases owner : Lower.edgeOwnerIndex? capabilities input
                    oldLender with
                | none =>
                    simp [Lower.BindingCap.rebaseEdge?, owner] at capabilityAt
                | some ownerIndex =>
                    obtain ⟨ownerWorld, ownerCapability, ownerInput⟩ :=
                      edgeOwnerIndex?_facts owner
                    by_cases sameWorld : ownerWorld = oldWorld
                    · subst ownerWorld
                      have outputEq :
                          Lower.BindingCap.borrowed oldWorld
                              (.value ownerIndex) =
                            .borrowed world lender := by
                        simpa [Lower.BindingCap.rebaseEdge?, owner,
                          ownerCapability] using capabilityAt
                      injection outputEq with worldEq lenderEq
                      subst world
                      subst lender
                      obtain ⟨oldOwnerIndex, oldOwnerValue, oldOwnerInput,
                        oldOwnerCapability, oldOwnerSource, support⟩ :=
                        invariant.borrows oldAt valueAt
                      have ownerBound : ownerIndex < capabilities.size :=
                        (Array.getElem?_eq_some_iff.mp ownerCapability).1
                      have sourceBound : ownerIndex < source.length := by
                        rw [invariant.length]
                        exact ownerBound
                      let ownerValue := source[ownerIndex]
                      have ownerSource :
                          source[ownerIndex]? = some ownerValue :=
                        List.getElem?_eq_some_iff.mpr ⟨sourceBound, rfl⟩
                      have ownerValueEq : ownerValue = oldOwnerValue :=
                        environments.source_eq_of_same_reg ownerSource
                          oldOwnerSource ownerInput oldOwnerInput
                      have successorInput :
                          (Lower.EdgeTrace.explicitMapOf input)[ownerIndex]? =
                            some (some (.reg ownerIndex)) := by
                        unfold Lower.EdgeTrace.explicitMapOf
                        rw [Array.getElem?_mapIdx]
                        simp [ownerInput]
                      have successorCapability :
                          (capabilities.map fun capability =>
                            (capability.rebaseEdge? capabilities input).getD
                              .dead)[ownerIndex]? =
                            some (.owned oldWorld) := by
                        rw [Array.getElem?_map, ownerCapability]
                        rfl
                      refine ⟨ownerIndex, ownerValue, successorInput,
                        successorCapability, ownerSource, ?_⟩
                      simpa [ownerValueEq] using support
                    · simp [Lower.BindingCap.rebaseEdge?, owner,
                        ownerCapability, sameWorld] at capabilityAt

/-- Shifting a local lender register does not change the pointwise meaning of
its capability. -/
private theorem CapabilityHolds.shiftLender
    {store : IxIR1.Store} {value : RVal} {amount : Nat}
    {capability : Lower.BindingCap}
    (holds : CapabilityHolds store capability value) :
    CapabilityHolds store (capability.shiftLender amount) value := by
  cases capability with
  | scalar | owned | dead => exact holds
  | borrowed world lender =>
      cases lender <;> exact holds

/-- Lender-register shifts are ownership-inert. -/
private theorem rootsForCapabilities_shiftLender (amount : Nat) :
    ∀ (capabilities : List Lower.BindingCap) (source : List RVal),
      rootsForCapabilities
          (capabilities.map (Lower.BindingCap.shiftLender amount)) source =
        rootsForCapabilities capabilities source := by
  intro capabilities
  induction capabilities with
  | nil => intro source; simp [rootsForCapabilities]
  | cons capability capabilities ih =>
      intro source
      cases source with
      | nil => simp [rootsForCapabilities]
      | cons value values =>
          cases capability with
          | scalar | owned | dead =>
              simp [Lower.BindingCap.shiftLender, rootsForCapabilities, ih]
          | borrowed world lender =>
              cases lender <;>
                simp [Lower.BindingCap.shiftLender, rootsForCapabilities, ih]

/-- Prefixing one scalar successor parameter and shifting every local lender
by one preserves exact dynamic source ownership. -/
theorem prependScalarShift
    {store : IxIR1.Store} {source : List RVal} {input : EnvMap}
    {capabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root} {scalarValue : RVal}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    (scalar : IxIR1.Sim.rvalLocation? scalarValue = none) :
    SourceOwnershipInvariant store (scalarValue :: source)
      (Lower.EdgeTrace.sourceMapOf 1 input)
      (#[.scalar] ++ capabilities.map (Lower.BindingCap.shiftLender 1))
      frameRoots := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [invariant.length, Array.size_append, Nat.add_comm]
  · intro index capability value capabilityAt valueAt
    cases index with
    | zero =>
        simp [Array.getElem?_append] at capabilityAt valueAt
        subst capability
        subst value
        exact scalar
    | succ index =>
        simp [Array.getElem?_append] at capabilityAt valueAt
        cases oldAt : capabilities[index]? with
        | none => simp [oldAt] at capabilityAt
        | some oldCapability =>
            simp only [oldAt, Option.some.injEq] at capabilityAt
            obtain ⟨candidate, rfl, shifted⟩ := capabilityAt
            subst capability
            exact CapabilityHolds.shiftLender
              (invariant.holds oldAt valueAt)
  · simpa [Array.toList_append, Array.toList_map, rootsForCapabilities,
      rootsForCapabilities_shiftLender] using invariant.ownership
  · intro index world lender value capabilityAt valueAt
    cases index with
    | zero => simp [Array.getElem?_append] at capabilityAt
    | succ index =>
        simp [Array.getElem?_append] at capabilityAt valueAt
        cases oldAt : capabilities[index]? with
        | none => simp [oldAt] at capabilityAt
        | some oldCapability =>
            simp only [oldAt, Option.some.injEq] at capabilityAt
            cases oldCapability with
            | scalar => simp [Lower.BindingCap.shiftLender] at capabilityAt
            | owned oldWorld =>
                simp [Lower.BindingCap.shiftLender] at capabilityAt
            | dead => simp [Lower.BindingCap.shiftLender] at capabilityAt
            | borrowed oldWorld oldLender =>
                cases oldLender with
                | caller =>
                    have outputEq :
                        Lower.BindingCap.borrowed oldWorld .caller =
                          .borrowed world lender := by
                      simpa [Lower.BindingCap.shiftLender] using capabilityAt
                    injection outputEq with worldEq lenderEq
                    subst world
                    subst lender
                    exact invariant.borrows oldAt valueAt
                | value oldLender =>
                    have outputEq :
                        Lower.BindingCap.borrowed oldWorld
                            (.value (oldLender + 1)) =
                          .borrowed world lender := by
                      simpa [Lower.BindingCap.shiftLender] using capabilityAt
                    injection outputEq with worldEq lenderEq
                    subst world
                    subst lender
                    obtain ⟨ownerIndex, ownerValue, ownerInput,
                      ownerCapability, ownerSource, support⟩ :=
                      invariant.borrows oldAt valueAt
                    have successorInput :
                        (Lower.EdgeTrace.sourceMapOf 1 input
                          )[ownerIndex + 1]? =
                            some (some (.reg (oldLender + 1))) := by
                      unfold Lower.EdgeTrace.sourceMapOf
                      simp [Array.getElem?_append, ownerInput,
                        Lower.shiftAtom]
                    have successorCapability :
                        (#[.scalar] ++ capabilities.map
                          (Lower.BindingCap.shiftLender 1))[ownerIndex + 1]? =
                            some (.owned oldWorld) := by
                      simp [Array.getElem?_append, ownerCapability,
                        Lower.BindingCap.shiftLender]
                    have successorSource :
                        (scalarValue :: source)[ownerIndex + 1]? =
                          some ownerValue := by
                      simpa [Nat.add_comm] using ownerSource
                    exact ⟨ownerIndex + 1, ownerValue, successorInput,
                      successorCapability, successorSource, support⟩

/-- A checked Nat-zero edge is exactly the canonical edge transform. -/
theorem natZero
    {store : IxIR1.Store} {source : List RVal} {target : Array RVal}
    {input : EnvMap} {capabilities afterCapabilities :
      Array Lower.BindingCap} {frameRoots : List IxIR1.Sim.Root}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    (environments : EnvRel source target input)
    (transition : Lower.natZeroChildCapabilities? input capabilities =
      some afterCapabilities) :
    SourceOwnershipInvariant store source
      (Lower.EdgeTrace.explicitMapOf input) afterCapabilities frameRoots := by
  exact invariant.edge environments transition

/-- A checked Nat-successor edge rebases predecessor lenders, prefixes the
peeled scalar, and shifts local successor-register lenders exactly once. -/
theorem natSucc
    {store : IxIR1.Store} {source : List RVal} {target : Array RVal}
    {input : EnvMap} {capabilities afterCapabilities :
      Array Lower.BindingCap} {frameRoots : List IxIR1.Sim.Root}
    {predecessor : Nat}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    (environments : EnvRel source target input)
    (transition : Lower.natSuccChildCapabilities? input capabilities =
      some afterCapabilities) :
    SourceOwnershipInvariant store (.lit (.nat predecessor) :: source)
      (Lower.EdgeTrace.sourceMapOf 1
        (Lower.EdgeTrace.explicitMapOf input))
      afterCapabilities frameRoots := by
  unfold Lower.natSuccChildCapabilities? at transition
  cases rebasedEq : Lower.edgeCapabilities? capabilities input with
  | none => simp [rebasedEq] at transition
  | some rebased =>
      simp [rebasedEq] at transition
      subst afterCapabilities
      apply prependScalarShift (invariant.edge environments rebasedEq)
      rfl

/-- Prefixing equally-sized source, input, and capability vectors preserves
the provenance of every borrow in the old suffix. -/
private theorem prependBorrowProvenancePrefix
    {store : IxIR1.Store} {source prefixValues : List RVal}
    {input prefixInput : EnvMap}
    {capabilities prefixCapabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    (inputSize : prefixInput.size = prefixValues.length)
    (capabilitySize : prefixCapabilities.size = prefixValues.length)
    {world : Ix.Compiler.Ixon.Owned} {lender : BorrowLender} {value : RVal}
    (provenance : BorrowProvenance store source input capabilities frameRoots
      world lender value) :
    BorrowProvenance store (prefixValues ++ source) (prefixInput ++ input)
      (prefixCapabilities ++ capabilities) frameRoots world lender value := by
  cases lender with
  | caller => exact provenance
  | value lenderId =>
      obtain ⟨ownerIndex, ownerValue, ownerInput, ownerCapability,
        ownerSource, support⟩ := provenance
      refine ⟨prefixValues.length + ownerIndex, ownerValue, ?_, ?_, ?_,
        support⟩
      · simpa [Array.getElem?_append, inputSize] using ownerInput
      · simpa [Array.getElem?_append, capabilitySize] using ownerCapability
      · rw [List.getElem?_append_right (by omega)]
        simpa using ownerSource

/-- A uniform borrowed capability prefix contributes no ownership roots. -/
private theorem rootsForCapabilities_borrowedPrefix
    (world : Ix.Compiler.Ixon.Owned) (lender : BorrowLender) :
    ∀ (prefixValues : List RVal) (capabilities : List Lower.BindingCap)
        (source : List RVal),
      rootsForCapabilities
          (List.replicate prefixValues.length (.borrowed world lender) ++
            capabilities)
          (prefixValues ++ source) =
        rootsForCapabilities capabilities source := by
  intro prefixValues
  induction prefixValues with
  | nil => intro capabilities source; simp
  | cons value values ih =>
      intro capabilities source
      rw [show (value :: values).length = Nat.succ values.length by rfl,
        List.replicate_succ]
      exact ih capabilities source

/-- Prepending constructor fields as uniform borrows extends one retained
scrutinee-lender path to every fetched field while leaving the exact root
multiset unchanged. -/
theorem constructorFields
    {store : IxIR1.Store} {source : List RVal} {input : EnvMap}
    {capabilities : Array Lower.BindingCap}
    {frameRoots : List IxIR1.Sim.Root}
    {fields : Array RVal} {location : Nat} {box : IxIR1.NodeBox}
    {cid : CtorId} {world : Ix.Compiler.Ixon.Owned}
    {lender : BorrowLender} {parameterCount : Nat}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    (provenance : BorrowProvenance store source input capabilities frameRoots
      world lender (.loc location))
    (found : store.get? location = some box)
    (node : box.node = .ctorN cid fields) :
    SourceOwnershipInvariant store (fields.toList.reverse ++ source)
      (Lower.constructorChildInputMap parameterCount fields.size ++ input)
      (Array.replicate fields.size (.borrowed world lender) ++ capabilities)
      frameRoots := by
  let prefixValues := fields.toList.reverse
  let prefixInput := Lower.constructorChildInputMap parameterCount fields.size
  let prefixCapabilities :=
    Array.replicate fields.size (Lower.BindingCap.borrowed world lender)
  have prefixLength : prefixValues.length = fields.size := by
    simp [prefixValues]
  have inputSize : prefixInput.size = prefixValues.length := by
    simp [prefixInput, Lower.constructorChildInputMap, prefixLength]
  have capabilitySize : prefixCapabilities.size = prefixValues.length := by
    simp [prefixCapabilities, prefixLength]
  have extendField : ∀ {value : RVal}, value ∈ fields.toList →
      BorrowProvenance store (prefixValues ++ source)
        (prefixInput ++ input) (prefixCapabilities ++ capabilities)
        frameRoots world lender value := by
    intro value member
    apply prependBorrowProvenancePrefix inputSize capabilitySize
    apply BorrowProvenance.child provenance found
    simpa [IxIR1.Sim.nodeChildren, node] using member
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [invariant.length]
  · intro index capability value capabilityAt valueAt
    by_cases prefixIndex : index < fields.size
    · have prefixValueAt : prefixValues[index]? = some value := by
        have bound : index < prefixValues.length := by
          simpa [prefixLength] using prefixIndex
        rw [List.getElem?_append_left bound] at valueAt
        exact valueAt
      have fieldMember : value ∈ fields.toList := by
        have reverseMember : value ∈ prefixValues :=
          List.mem_of_getElem? prefixValueAt
        simpa [prefixValues] using reverseMember
      have capabilityEq : capability = .borrowed world lender := by
        have prefixBound : index < prefixCapabilities.size := by
          simpa [prefixCapabilities] using prefixIndex
        rw [Array.getElem?_append, if_pos prefixBound] at capabilityAt
        simpa [prefixCapabilities, prefixIndex] using capabilityAt.symm
      subst capability
      exact BorrowProvenance.hasWorld invariant.ownership
        (BorrowProvenance.child provenance found
          (by simpa [IxIR1.Sim.nodeChildren, node] using fieldMember))
    · let sourceIndex := index - fields.size
      have afterPrefix : fields.size ≤ index := Nat.le_of_not_gt prefixIndex
      have oldValueAt : source[sourceIndex]? = some value := by
        rw [List.getElem?_append_right (by
          simpa [prefixValues, prefixLength] using afterPrefix)] at valueAt
        simpa [sourceIndex, prefixValues, prefixLength] using valueAt
      have oldCapabilityAt : capabilities[sourceIndex]? =
          some capability := by
        rw [Array.getElem?_append] at capabilityAt
        have notPrefix : ¬ index < prefixCapabilities.size := by
          simpa [prefixCapabilities] using prefixIndex
        rw [if_neg notPrefix] at capabilityAt
        simpa [sourceIndex, prefixCapabilities] using capabilityAt
      exact invariant.holds oldCapabilityAt oldValueAt
  · rw [Array.toList_append]
    have roots := rootsForCapabilities_borrowedPrefix world lender
      prefixValues capabilities.toList source
    rw [prefixLength] at roots
    have rootsEq :
        rootsForCapabilities
            (prefixCapabilities.toList ++ capabilities.toList)
            (prefixValues ++ source) =
          rootsForCapabilities capabilities.toList source := by
      simpa [prefixCapabilities] using roots
    rw [rootsEq]
    exact invariant.ownership
  · intro index actualWorld actualLender value capabilityAt valueAt
    by_cases prefixIndex : index < fields.size
    · have prefixValueAt : prefixValues[index]? = some value := by
        have bound : index < prefixValues.length := by
          simpa [prefixLength] using prefixIndex
        rw [List.getElem?_append_left bound] at valueAt
        exact valueAt
      have fieldMember : value ∈ fields.toList := by
        have reverseMember : value ∈ prefixValues :=
          List.mem_of_getElem? prefixValueAt
        simpa [prefixValues] using reverseMember
      have equalities : world = actualWorld ∧ lender = actualLender := by
        have prefixBound : index < prefixCapabilities.size := by
          simpa [prefixCapabilities] using prefixIndex
        rw [Array.getElem?_append, if_pos prefixBound] at capabilityAt
        simpa [prefixCapabilities, prefixIndex] using capabilityAt
      rcases equalities with ⟨rfl, rfl⟩
      exact extendField fieldMember
    · let sourceIndex := index - fields.size
      have afterPrefix : fields.size ≤ index := Nat.le_of_not_gt prefixIndex
      have oldValueAt : source[sourceIndex]? = some value := by
        rw [List.getElem?_append_right (by
          simpa [prefixValues, prefixLength] using afterPrefix)] at valueAt
        simpa [sourceIndex, prefixValues, prefixLength] using valueAt
      have oldCapabilityAt : capabilities[sourceIndex]? =
          some (.borrowed actualWorld actualLender) := by
        rw [Array.getElem?_append] at capabilityAt
        have notPrefix : ¬ index < prefixCapabilities.size := by
          simpa [prefixCapabilities] using prefixIndex
        rw [if_neg notPrefix] at capabilityAt
        simpa [sourceIndex, prefixCapabilities] using capabilityAt
      exact prependBorrowProvenancePrefix inputSize capabilitySize
        (invariant.borrows oldCapabilityAt oldValueAt)

/-- Successful translation of a source variable through the canonical edge
map exposes its exact same-index successor register. -/
private theorem explicitMapOf_at_of_translate_var
    {input : EnvMap} {sourceIndex : Nat} {targetAtom : Atom}
    (translated : Lower.InputMap.translateAtom
      (Lower.EdgeTrace.explicitMapOf input) (.var sourceIndex) =
        some targetAtom) :
    (Lower.EdgeTrace.explicitMapOf input)[sourceIndex]? =
      some (some (.reg sourceIndex)) := by
  unfold Lower.InputMap.translateAtom at translated
  cases mapped : (Lower.EdgeTrace.explicitMapOf input)[sourceIndex]? with
  | none => simp [mapped] at translated
  | some slot =>
      cases slot with
      | none => simp [mapped] at translated
      | some atom =>
          have atomEq : atom = targetAtom := by
            simpa [mapped] using translated
          unfold Lower.EdgeTrace.explicitMapOf at mapped
          rw [Array.getElem?_mapIdx] at mapped
          cases inputAt : input[sourceIndex]? with
          | none => simp [inputAt] at mapped
          | some slot =>
              cases slot with
              | none => simp [inputAt] at mapped
              | some sourceAtom =>
                  have registerEq : atom = .reg sourceIndex := by
                    simpa [inputAt] using mapped.symm
                  simp [registerEq]

/-- The complete checked constructor-child transform: edge rebasing chooses
the scrutinee lender, a uniform schema supplies the borrowed field prefix,
and the runtime constructor supplies the concrete support edges. -/
theorem constructor
    {schemas : Ix.Compiler.Ixon.Owned → CtorId → Option CtorSchema}
    {store : IxIR1.Store} {source : List RVal} {target : Array RVal}
    {input : EnvMap} {capabilities afterCapabilities :
      Array Lower.BindingCap} {frameRoots : List IxIR1.Sim.Root}
    {sourceScrutinee : IxIR1.Atom} {targetScrutinee : Atom}
    {cid : CtorId} {fields : Array RVal} {location : Nat}
    {box : IxIR1.NodeBox} {parameterCount : Nat}
    (invariant : SourceOwnershipInvariant store source input capabilities
      frameRoots)
    (environments : EnvRel source target input)
    (transition : Lower.constructorChildCapabilities? schemas input
      sourceScrutinee cid capabilities = some afterCapabilities)
    (translated : Lower.InputMap.translateAtom
      (Lower.EdgeTrace.explicitMapOf input) sourceScrutinee =
        some targetScrutinee)
    (sourceResolved : IxIR1.resolveAtom source sourceScrutinee =
      .ok (.loc location))
    (found : store.get? location = some box)
    (node : box.node = .ctorN cid fields)
    (schemaFields : ∀ {world schema}, schemas world cid = some schema →
      ∃ count, schema.fields = Array.replicate count world)
    (afterSize : afterCapabilities.size =
      fields.size + capabilities.size) :
    SourceOwnershipInvariant store (fields.toList.reverse ++ source)
      (Lower.constructorChildInputMap parameterCount fields.size ++
        Lower.EdgeTrace.explicitMapOf input)
      afterCapabilities frameRoots := by
  unfold Lower.constructorChildCapabilities? at transition
  cases rebasedEq : Lower.edgeCapabilities? capabilities input with
  | none => simp [rebasedEq] at transition
  | some rebased =>
      have edgeInvariant := invariant.edge environments rebasedEq
      cases sourceScrutinee with
      | lit literal => simp [rebasedEq] at transition
      | erased => simp [rebasedEq] at transition
      | var sourceIndex =>
          have successorInput :=
            explicitMapOf_at_of_translate_var translated
          cases sourceAt : source[sourceIndex]? with
          | none => simp [IxIR1.resolveAtom, sourceAt] at sourceResolved
          | some scrutineeValue =>
              have scrutineeEq : scrutineeValue = .loc location := by
                simpa [IxIR1.resolveAtom, sourceAt] using sourceResolved
              subst scrutineeValue
              cases capabilityAt : rebased[sourceIndex]? with
              | none => simp [rebasedEq, capabilityAt] at transition
              | some capability =>
                  cases capability with
                  | scalar =>
                      simp [rebasedEq, capabilityAt] at transition
                  | dead =>
                      simp [rebasedEq, capabilityAt] at transition
                  | owned world =>
                      cases schemaAt : schemas world cid with
                      | none =>
                          simp [rebasedEq, capabilityAt, schemaAt] at transition
                      | some schema =>
                          simp [rebasedEq, capabilityAt, schemaAt] at transition
                          subst afterCapabilities
                          obtain ⟨count, schemaUniform⟩ :=
                            schemaFields schemaAt
                          have rebasedSize : rebased.size = capabilities.size :=
                            edgeInvariant.length.symm.trans invariant.length
                          have countEq : count = fields.size := by
                            simp [schemaUniform, rebasedSize] at afterSize
                            omega
                          subst count
                          have provenance : BorrowProvenance store source
                              (Lower.EdgeTrace.explicitMapOf input) rebased
                              frameRoots world (.value sourceIndex)
                              (.loc location) :=
                            ⟨sourceIndex, .loc location, successorInput,
                              capabilityAt, sourceAt, .refl⟩
                          have fieldsInvariant := constructorFields
                            edgeInvariant provenance found node
                            (parameterCount := parameterCount)
                          simpa [schemaUniform] using fieldsInvariant
                  | borrowed world lender =>
                      cases schemaAt : schemas world cid with
                      | none =>
                          simp [rebasedEq, capabilityAt, schemaAt] at transition
                      | some schema =>
                          simp [rebasedEq, capabilityAt, schemaAt] at transition
                          subst afterCapabilities
                          obtain ⟨count, schemaUniform⟩ :=
                            schemaFields schemaAt
                          have rebasedSize : rebased.size = capabilities.size :=
                            edgeInvariant.length.symm.trans invariant.length
                          have countEq : count = fields.size := by
                            simp [schemaUniform, rebasedSize] at afterSize
                            omega
                          subst count
                          have provenance :=
                            edgeInvariant.borrows capabilityAt sourceAt
                          have fieldsInvariant := constructorFields
                            edgeInvariant provenance found node
                            (parameterCount := parameterCount)
                          simpa [schemaUniform] using fieldsInvariant

end SourceOwnershipInvariant

namespace SourceOwnershipAt

/-- Checked literal-zero branch selection transports ownership to every
matching position in the exact recursive child. -/
theorem switchNatZero
    (checked : Lower.Checked) {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId} {input : EnvMap}
    {entryValueCount : Nat} {sourceScrutinee : IxIR1.Atom}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List Lower.EdgeTrace}
    {children : List Lower.CodeTrace} {constructors : Array CtorAlt}
    {peel : NatPeel}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children))
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors (some peel))
    (branches : Lower.NatBranchPairMatch site blockId input alternatives
      constructors peel outgoing children)
    {store : IxIR1.Store} {source : List RVal} {target : Array RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children)
      store source frameRoots)
    (environments : EnvRel source target input) :
    SourceOwnershipAt checked.artifact.trace.positions branches.zeroChild
      store source frameRoots := by
  intro after afterMember afterCoordinate
  obtain ⟨before, beforeMember, beforeCoordinate, transition⟩ :=
    checked.natZeroBranchTransition functionMember descendant terminator
      branches.zeroChildAt branches.succChildAt afterMember afterCoordinate
  have current := ownership before beforeMember beforeCoordinate
  have current' : SourceOwnershipInvariant store source input
      before.sourceCapabilities frameRoots := by
    simpa [Lower.CodeTrace.sourceInputMap] using current
  have next := current'.natZero environments transition
  have childInput : branches.zeroChild.sourceInputMap =
      Lower.EdgeTrace.explicitMapOf input := by
    rw [branches.zero.childInput]
    unfold Lower.EdgeTrace.sourceMap
    rw [branches.zero.edgeImplicitScalars, sourceMapOf_zero_for_ownership,
      branches.zero.edgeSourceInput]
  rw [childInput]
  exact next

/-- Checked literal-successor branch selection transports ownership through
the peeled scalar prefix and its one-register lender shift. -/
theorem switchNatSucc
    (checked : Lower.Checked) {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId} {input : EnvMap}
    {entryValueCount : Nat} {sourceScrutinee : IxIR1.Atom}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List Lower.EdgeTrace}
    {children : List Lower.CodeTrace} {constructors : Array CtorAlt}
    {peel : NatPeel}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children))
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors (some peel))
    (branches : Lower.NatBranchPairMatch site blockId input alternatives
      constructors peel outgoing children)
    {store : IxIR1.Store} {source : List RVal} {target : Array RVal}
    {frameRoots : List IxIR1.Sim.Root} {predecessor : Nat}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children)
      store source frameRoots)
    (environments : EnvRel source target input) :
    SourceOwnershipAt checked.artifact.trace.positions branches.succChild
      store (.lit (.nat predecessor) :: source) frameRoots := by
  intro after afterMember afterCoordinate
  obtain ⟨before, beforeMember, beforeCoordinate, transition⟩ :=
    checked.natSuccBranchTransition functionMember descendant terminator
      branches.zeroChildAt branches.succChildAt afterMember afterCoordinate
  have current := ownership before beforeMember beforeCoordinate
  have current' : SourceOwnershipInvariant store source input
      before.sourceCapabilities frameRoots := by
    simpa [Lower.CodeTrace.sourceInputMap] using current
  have next := current'.natSucc
    (predecessor := predecessor) environments transition
  have childInput : branches.succChild.sourceInputMap =
      Lower.EdgeTrace.sourceMapOf 1
        (Lower.EdgeTrace.explicitMapOf input) := by
    rw [branches.succ.childInput]
    unfold Lower.EdgeTrace.sourceMap
    rw [branches.succ.edgeImplicitScalars,
      branches.succ.edgeSourceInput]
  rw [childInput]
  exact next

/-- Checked constructor branch selection transports ownership to every
matching child position. Coordinate sizes force the uniform pipeline schema
arity to equal the concrete runtime field vector. -/
theorem switchCtor
    (checked : Lower.Checked) {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId} {input : EnvMap}
    {entryValueCount : Nat} {sourceScrutinee : IxIR1.Atom}
    {peelNat : Bool} {alternatives : Array IxIR1.Alt}
    {targetScrutinee : Atom} {generated : Block}
    {outgoing : List Lower.EdgeTrace} {children : List Lower.CodeTrace}
    {constructors : Array CtorAlt} {targetPeel : Option NatPeel}
    {index : Nat} {targetBranch : CtorAlt} {edge : Lower.EdgeTrace}
    {child : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children))
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors targetPeel)
    (targetAt : constructors[index]? = some targetBranch)
    (childAt : children[index]? = some child)
    (branch : Lower.ConstructorBranchMatch site blockId input
      sourceScrutinee alternatives targetBranch edge child)
    {store : IxIR1.Store} {source : List RVal} {targetValues : Array RVal}
    {frameRoots : List IxIR1.Sim.Root} {location : Nat}
    {box : IxIR1.NodeBox} {cid : CtorId} {fields : Array RVal}
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children)
      store source frameRoots)
    (environments : EnvRel source targetValues input)
    (sourceResolved : IxIR1.resolveAtom source sourceScrutinee =
      .ok (.loc location))
    (found : store.get? location = some box)
    (node : box.node = .ctorN cid fields)
    (targetCid : targetBranch.cid = cid)
    (fieldArity : fields.size = branch.fieldCount)
    (schemaFields : ∀ {world schema},
      checked.artifact.validationContext.schemas world cid = some schema →
        ∃ count, schema.fields = Array.replicate count world) :
    SourceOwnershipAt checked.artifact.trace.positions child store
      (fields.toList.reverse ++ source) frameRoots := by
  intro after afterMember afterCoordinate
  obtain ⟨before, beforeMember, beforeCoordinate, transition⟩ :=
    checked.constructorBranchTransition functionMember descendant terminator
      targetAt childAt afterMember afterCoordinate
  have current := ownership before beforeMember beforeCoordinate
  have current' : SourceOwnershipInvariant store source input
      before.sourceCapabilities frameRoots := by
    simpa [Lower.CodeTrace.sourceInputMap] using current
  have beforeSize : before.sourceCapabilities.size = input.size :=
    before.sourceCapabilities_size_of_coordinateMatch beforeCoordinate
  have afterCoordinateSize :
      after.sourceCapabilities.size = child.sourceInputMap.size :=
    after.sourceCapabilities_size_of_coordinateMatch afterCoordinate
  have afterSize : after.sourceCapabilities.size =
      fields.size + before.sourceCapabilities.size := by
    calc
      after.sourceCapabilities.size = child.sourceInputMap.size :=
        afterCoordinateSize
      _ = branch.fieldCount + input.size := by
        rw [branch.childInput]
        simp [Lower.constructorChildInputMap,
          Lower.EdgeTrace.explicitMapOf, branch.edgeSourceInput]
      _ = fields.size + before.sourceCapabilities.size := by
        rw [← fieldArity, beforeSize]
  rw [targetCid] at transition
  have next := current'.constructor environments transition
    branch.translatedScrutinee sourceResolved found node schemaFields afterSize
    (parameterCount := edge.targetParams.size)
  have childInput : child.sourceInputMap =
      Lower.constructorChildInputMap edge.targetParams.size fields.size ++
        Lower.EdgeTrace.explicitMapOf input := by
    rw [branch.childInput, ← fieldArity, branch.edgeSourceInput]
  rw [childInput]
  exact next

end SourceOwnershipAt

/-- Runtime frame invariant at one recursive compiler-trace node. This is the
state threaded by the block-compositional semantic induction. -/
structure CodeStateRel (functionTrace : Lower.FunctionTrace)
    (trace : Lower.CodeTrace) (source : List RVal)
    (frame : Eval.Frame) : Prop where
  definition : frame.definition = functionTrace.generated
  block : frame.block = trace.sourceBlock
  pc : frame.pc = trace.entryPc
  valueCount : frame.values.size = trace.entryValueCount
  sourceCount : source.length = trace.sourceInputMap.size
  environments : EnvRel source frame.values trace.sourceInputMap

/-- A source result-world fact is exactly the executable world check required
by a target return from the related generated function. -/
theorem CodeStateRel.resultWorld {functionTrace : Lower.FunctionTrace}
    {trace : Lower.CodeTrace} {source : List RVal} {frame : Eval.Frame}
    (state : CodeStateRel functionTrace trace source frame)
    {sourceStore : IxIR1.Store} {targetStore : Eval.Store}
    (stores : StoreRel sourceStore targetStore) {value : RVal}
    (world : IxIR1.Sim.HasWorld sourceStore functionTrace.source.result value) :
    Eval.RVal.hasWorld targetStore frame.definition.signature.result value =
      true := by
  apply stores.hasWorld_eq_true_iff.mpr
  rw [state.definition, functionTrace.sourceResult]
  exact world

/-- A related frame at a recursive trace descendant executes the exact head
block certified by that function trace. -/
theorem CodeStateRel.blockAt {functionTrace : Lower.FunctionTrace}
    {trace : Lower.CodeTrace} {source : List RVal} {frame : Eval.Frame}
    (state : CodeStateRel functionTrace trace source frame)
    (descendant : functionTrace.root.Descendant trace) :
    frame.definition.blocks[frame.block]? = some trace.headBlock.2 := by
  have matched := functionTrace.descendantInstructionsMatch descendant
  have blockId := Lower.CodeTrace.headBlock_eq_sourceBlock_of_match matched
  have blockAt := functionTrace.descendantHeadBlockAt descendant
  simpa [state.definition, state.block, blockId] using blockAt

/-- A related instruction-node state points at the exact retained instruction
inside the generated function, including the evaluator's strict PC bound. -/
theorem CodeStateRel.instructionAt {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {operation : IxIR1.Op} {instruction : Instr} {next : Lower.CodeTrace}
    {source : List RVal} {frame : Eval.Frame}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next) source frame)
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next)) :
    frame.definition.blocks[frame.block]? = some next.headBlock.2 ∧
      frame.pc < next.headBlock.2.instructions.size ∧
      next.headBlock.2.instructions[frame.pc]? = some instruction := by
  obtain ⟨localMatch, _⟩ := functionTrace.descendantLetOpMatch descendant
  have framePc : frame.pc = index := by
    simpa [Lower.CodeTrace.entryPc] using state.pc
  obtain ⟨indexBound, _⟩ :=
    Array.getElem?_eq_some_iff.mp localMatch.instructionAt
  refine ⟨state.blockAt descendant, ?_, ?_⟩
  · simpa [framePc] using indexBound
  · simpa [framePc] using localMatch.instructionAt

/-- Generic recursive-state hand-off after one retained baseline instruction.
The operation proof supplies only the concrete successor-frame equalities and
environment relation; the checked trace supplies definition, block, PC,
register-count, and proof-map progression to the recursive continuation. -/
theorem CodeStateRel.letOpNext {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {operation : IxIR1.Op} {instruction : Instr} {next : Lower.CodeTrace}
    {source nextSource : List RVal} {frame nextFrame : Eval.Frame}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next) source frame)
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next))
    (definition : nextFrame.definition = frame.definition)
    (block : nextFrame.block = frame.block)
    (pc : nextFrame.pc = frame.pc + 1)
    (valueCount : nextFrame.values.size = frame.values.size +
      (Lower.Instr.baselineValueDelta instruction).getD 0)
    (sourceCount : nextSource.length = source.length + 1)
    (environments : EnvRel nextSource nextFrame.values nextInput) :
    CodeStateRel functionTrace next nextSource nextFrame := by
  obtain ⟨localMatch, _⟩ := functionTrace.descendantLetOpMatch descendant
  have frameBlock : frame.block = blockId := by
    simpa [Lower.CodeTrace.sourceBlock] using state.block
  have framePc : frame.pc = index := by
    simpa [Lower.CodeTrace.entryPc] using state.pc
  constructor
  · exact definition.trans state.definition
  · exact block.trans (frameBlock.trans localMatch.nextBlock.symm)
  · calc
      nextFrame.pc = frame.pc + 1 := pc
      _ = index + 1 := by rw [framePc]
      _ = next.entryPc := localMatch.nextPc.symm
  · calc
      nextFrame.values.size = frame.values.size +
          (Lower.Instr.baselineValueDelta instruction).getD 0 := valueCount
      _ = entryValueCount +
          (Lower.Instr.baselineValueDelta instruction).getD 0 := by
            simpa [Lower.CodeTrace.entryValueCount] using
              congrArg (fun count => count +
                (Lower.Instr.baselineValueDelta instruction).getD 0)
                state.valueCount
      _ = next.entryValueCount := localMatch.nextValueCount.symm
  · have currentSourceCount : source.length = input.size := by
      simpa [Lower.CodeTrace.sourceInputMap] using state.sourceCount
    have mapsMatched := functionTrace.descendantInputMapsMatch descendant
    have mapSize := Lower.CodeTrace.inputMapSize_of_match mapsMatched
    calc
      nextSource.length = source.length + 1 := sourceCount
      _ = input.size + 1 := by rw [currentSourceCount]
      _ = nextInput.size := mapSize.symm
      _ = next.sourceInputMap.size := by rw [localMatch.nextInput]
  · simpa [localMatch.nextInput] using environments

/-- A successor proof map may forget live slots but cannot retarget one. This
is the ownership-consumption step needed between the operation-local lemmas
and the compiler's cursor relation. -/
abbrev EnvMap.Forgets (next current : EnvMap) : Prop :=
  Lower.InputMap.Forgets next current

/-- Forgetting consumed bindings preserves the environment relation. -/
theorem EnvRel.forget {source : List RVal} {target : Array RVal}
    {current next : EnvMap} (relation : EnvRel source target current)
    (forgets : EnvMap.Forgets next current) :
    EnvRel source target next := by
  intro index value atom sourceGet mapped
  exact relation index value atom sourceGet (forgets index atom mapped)

/-- Specialize safe forgetting to one checked recursive instruction node.
The caller supplies the canonical binder-plus-predecessor relation produced by
the operation lemma; the trace certificate converts it to the exact successor
map retained by the compiler. -/
theorem EnvRel.forgetTracedLetOp
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {operation : IxIR1.Op} {instruction : Instr} {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next))
    {source : List RVal} {target : Array RVal} {head : Atom}
    (relation : EnvRel source target (#[some head] ++ input))
    (binder : Lower.Instr.baselineBinderAtom entryValueCount instruction =
      some head) :
    EnvRel source target nextInput := by
  have mapsMatched := functionTrace.descendantInputMapsMatch descendant
  have mapFacts := Lower.CodeTrace.inputMapForgets_of_match mapsMatched binder
  exact relation.forget mapFacts.2.2.1

/-- Value-producing specialization: rewrite the runtime append ordinal to the
compiler-certified entry count before applying checked map forgetting. -/
theorem EnvRel.forgetTracedValue
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {operation : IxIR1.Op} {instruction : Instr} {next : Lower.CodeTrace}
    {source nextSource : List RVal} {frame : Eval.Frame}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next) source frame)
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next))
    {target : Array RVal}
    (relation : EnvRel nextSource target
      (#[some (.reg frame.values.size)] ++ input))
    (binder : Lower.Instr.baselineBinderAtom entryValueCount instruction =
      some (.reg entryValueCount)) :
    EnvRel nextSource target nextInput := by
  have canonical : EnvRel nextSource target
      (#[some (.reg entryValueCount)] ++ input) := by
    simpa [state.valueCount, Lower.CodeTrace.entryValueCount,
      Lower.CodeTrace.sourceInputMap] using relation
  exact canonical.forgetTracedLetOp descendant binder

/-- Effect-only specialization for instructions whose IxIR₁ result binder
maps to the inert erased atom and does not append a target value register. -/
theorem EnvRel.forgetTracedErased
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {operation : IxIR1.Op} {instruction : Instr} {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next))
    {source : List RVal} {target : Array RVal}
    (relation : EnvRel source target (#[some .erased] ++ input))
    (binder : Lower.Instr.baselineBinderAtom entryValueCount instruction =
      some .erased) :
    EnvRel source target nextInput :=
  relation.forgetTracedLetOp descendant binder

/-- The proof map at a function entry reverses source de Bruijn parameter
slots onto target call-order registers. -/
def entryMap (arity : Nat) : EnvMap :=
  Lower.entryInputMap arity

/-- A resolved target argument vector is related to the source callee's
reversed de Bruijn environment by the canonical entry map. -/
theorem EnvRel.entry (values : Array RVal) :
    EnvRel values.toList.reverse values (entryMap values.size) := by
  intro index value atom sourceGet mapped
  obtain ⟨indexBound, _⟩ := List.getElem?_eq_some_iff.mp sourceGet
  have originalBound : index < values.toList.length := by
    simpa using indexBound
  have targetGet :
      values[values.size - 1 - index]? = some value := by
    rw [List.getElem?_reverse (l := values.toList) originalBound]
      at sourceGet
    simpa using sourceGet
  have atomEq : atom = .reg (values.size - 1 - index) := by
    unfold entryMap Lower.entryInputMap at mapped
    rw [Array.getElem?_map, List.getElem?_toArray,
      List.getElem?_range (by simpa using indexBound)] at mapped
    simpa using Option.some.inj mapped.symm
  subst atom
  simp [Eval.resolveAtom, targetGet]

/-- Any retained function trace starts in `CodeStateRel` when its resolved
arguments are installed in call order and the source environment uses the
IxIR₁ reversed de Bruijn convention. -/
theorem functionEntryCodeState (trace : Lower.FunctionTrace)
    (values : Array RVal)
    (arity : values.size = trace.source.arity) :
    CodeStateRel trace trace.root values.toList.reverse
      { definition := trace.generated, values } := by
  constructor
  · rfl
  · simpa using trace.entryBlock.symm
  · simpa using trace.entryPc.symm
  · simpa [trace.entryValueCount] using arity
  · rw [trace.entryInput, ← arity]
    simp [Lower.entryInputMap]
  · rw [trace.entryInput, ← arity]
    exact EnvRel.entry values

/-- Exact target frame used for a lowered artifact's closed main. -/
def initialMainFrame (artifact : Lower.Artifact) : Eval.Frame :=
  { definition := artifact.program.main }

/-- Exact target machine used for a lowered artifact's closed main. -/
def initialMainMachine (artifact : Lower.Artifact) (heapFuel : Nat) :
    Eval.Machine :=
  Eval.initialMachine artifact.program.main #[] heapFuel

/-- All structural and semantic relations needed by the root trace induction
hold at the exact machine state consumed by `runMain`. -/
theorem initialMainState (artifact : Lower.Artifact) (heapFuel : Nat) :
    let frame := initialMainFrame artifact
    let machine := initialMainMachine artifact heapFuel
    machine.control = .running frame [] ∧
      frame.definition = artifact.mainTrace.generated ∧
      frame.block = artifact.mainTrace.root.sourceBlock ∧
      frame.pc = artifact.mainTrace.root.entryPc ∧
      EnvRel [] frame.values artifact.mainTrace.root.sourceInputMap ∧
      StoreRel ({} : IxIR1.Store) machine.store ∧
      frame.definition.blocks[frame.block]? =
        some artifact.mainTrace.root.headBlock.2 := by
  dsimp only
  refine ⟨rfl, artifact.mainGenerated.symm, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [initialMainFrame] using artifact.mainTrace.entryBlock.symm
  · simpa [initialMainFrame] using artifact.mainTrace.entryPc.symm
  · rw [artifact.mainEntryInput]
    exact EnvRel.empty
  · change StoreRel ({} : IxIR1.Store)
      (Eval.initialMachine artifact.program.main #[] heapFuel).store
    rw [Eval.initialMachine_store_empty]
    exact StoreRel.initial
  · simpa [initialMainFrame] using artifact.mainHeadBlockAt

/-- The exact initial main frame satisfies the recursive trace-state
invariant at the artifact's distinguished root. -/
theorem initialMainCodeState (artifact : Lower.Artifact) :
    CodeStateRel artifact.mainTrace artifact.mainTrace.root []
      (initialMainFrame artifact) := by
  constructor
  · exact artifact.mainGenerated.symm
  · simpa [initialMainFrame] using artifact.mainTrace.entryBlock.symm
  · simpa [initialMainFrame] using artifact.mainTrace.entryPc.symm
  · rw [artifact.mainTrace.entryValueCount, artifact.mainSource]
    rfl
  · rw [artifact.mainEntryInput]
    rfl
  · rw [artifact.mainEntryInput]
    exact EnvRel.empty

/-- `runMain` starts from exactly the machine named by `initialMainState`. -/
theorem runMain_eq_initialMainMachine (artifact : Lower.Artifact)
    (context : Eval.Context) (interpretation : Eval.Interpretation)
    (controlFuel heapFuel : Nat) :
    Eval.runMain context interpretation artifact.program controlFuel heapFuel =
      Eval.runMachine context interpretation controlFuel
        (initialMainMachine artifact heapFuel) := by
  exact Eval.runMain_eq_runMachine artifact.mainArity artifact.mainNonempty

/-- Shifting a register operand past a value prefix preserves its resolution
in the suffix register file. -/
theorem resolveAtom_shift {suffix : Array RVal} {atom : Atom} {value : RVal}
    (prefixValues : Array RVal)
    (resolved : Eval.resolveAtom suffix atom = .ok value) :
    Eval.resolveAtom (prefixValues ++ suffix)
      (Lower.shiftAtom prefixValues.size atom) = .ok value := by
  cases atom with
  | reg index =>
      cases found : suffix[index]? with
      | none => simp [Eval.resolveAtom, found] at resolved
      | some candidate =>
        have candidateEq : candidate = value := by
          simpa [Eval.resolveAtom, found] using resolved
        subst candidate
        have notPrefix :
            ¬index + prefixValues.size < prefixValues.size :=
          Nat.not_lt_of_ge (Nat.le_add_left prefixValues.size index)
        have offset :
            index + prefixValues.size - prefixValues.size = index :=
          Nat.add_sub_cancel_right index prefixValues.size
        simp [Lower.shiftAtom, Eval.resolveAtom, Array.getElem?_append,
          notPrefix, offset, found]
  | lit literal => exact resolved
  | erased => exact resolved

/-- Shifting an operand across a zero-width prefix is the identity. -/
@[simp] theorem shiftAtom_zero (atom : Atom) :
    Lower.shiftAtom 0 atom = atom := by
  cases atom <;> simp [Lower.shiftAtom]

/-- A zero-width implicit prefix leaves the explicit successor map
unchanged. -/
theorem sourceMapOf_zero (explicitMap : Array (Option Atom)) :
    Lower.EdgeTrace.sourceMapOf 0 explicitMap = explicitMap := by
  apply Array.ext
  · simp [Lower.EdgeTrace.sourceMapOf]
  · intro index leftBound rightBound
    simp [Lower.EdgeTrace.sourceMapOf]
    cases explicitMap[index] <;> rfl

/-- Prefixing implicit scalar block parameters preserves an explicit
successor environment relation. This is exactly the map shape emitted in an
`EdgeTrace`, including register shifting and absent consumed slots. -/
theorem EnvRel.sourceMapOf {source : List RVal}
    {explicitValues : Array RVal} {explicitMap : EnvMap}
    (relation : EnvRel source explicitValues explicitMap)
    (implicitValues : Array RVal) :
    EnvRel (implicitValues.toList ++ source)
      (implicitValues ++ explicitValues)
      (Lower.EdgeTrace.sourceMapOf implicitValues.size explicitMap) := by
  intro index value atom sourceGet mapped
  by_cases prefixIndex : index < implicitValues.size
  · have valueAt : implicitValues[index]? = some value := by
      have listAt : implicitValues.toList[index]? = some value := by
        simpa [List.getElem?_append_left prefixIndex] using sourceGet
      simpa using listAt
    have atomEq : atom = .reg index := by
      unfold Lower.EdgeTrace.sourceMapOf at mapped
      simp only [Array.getElem?_append, Array.size_map, List.size_toArray,
        List.length_range, prefixIndex, if_pos, Array.getElem?_map,
        List.getElem?_toArray, List.getElem?_range prefixIndex,
        Option.map_some, Option.some.injEq] at mapped
      exact mapped.symm
    subst atom
    simp only [Eval.resolveAtom]
    rw [Array.getElem?_append, if_pos prefixIndex, valueAt]
  · have afterPrefix : implicitValues.size ≤ index :=
      Nat.le_of_not_gt prefixIndex
    let explicitIndex := index - implicitValues.size
    have sourceAt : source[explicitIndex]? = some value := by
      rw [List.getElem?_append_right (by simpa using afterPrefix)] at sourceGet
      simpa [explicitIndex] using sourceGet
    unfold Lower.EdgeTrace.sourceMapOf at mapped
    simp only [Array.getElem?_append, Array.size_map, List.size_toArray,
      List.length_range, prefixIndex, Array.getElem?_map] at mapped
    cases explicitAt : explicitMap[explicitIndex]? with
    | none => simp [explicitIndex, explicitAt] at mapped
    | some slot =>
      cases slot with
      | none => simp [explicitIndex, explicitAt] at mapped
      | some explicitAtom =>
        have mappedAt :
            explicitMap[explicitIndex]? = some (some explicitAtom) := explicitAt
        have atomEq :
            atom = Lower.shiftAtom implicitValues.size explicitAtom := by
          simpa [explicitIndex, explicitAt] using mapped.symm
        subst atom
        exact resolveAtom_shift implicitValues
          (relation explicitIndex value explicitAtom sourceAt mappedAt)

/-- A generated edge trace and the baseline evaluator transfer agree on the
exact successor frame and establish its proof-side source environment. This
is the CFG hand-off used by constructor branches (with no implicit values)
and Nat-successor branches (with the predecessor prefix). -/
theorem simulate_traced_edge_transfer
    {frame : Eval.Frame} {edge : Edge} {trace : Lower.EdgeTrace}
    {block : Block} {source : List RVal} {explicitMap : EnvMap}
    {implicitValues explicitValues : Array RVal}
    (edgeTarget : edge.target = trace.target)
    (edgeValues : edge.values = trace.explicitValues)
    (edgeCredits : edge.credits = #[])
    (traceMap : trace.sourceMap =
      Lower.EdgeTrace.sourceMapOf trace.implicitScalars explicitMap)
    (implicitCount : trace.implicitScalars = implicitValues.size)
    (resolved : Eval.resolveAtoms frame.values trace.explicitValues =
      .ok explicitValues)
    (environments : EnvRel source explicitValues explicitMap)
    (frameCredits : frame.credits = #[])
    (blockAt : frame.definition.blocks[trace.target]? = some block)
    (blockParams : block.valueParams = trace.targetParams)
    (valueArity : (implicitValues ++ explicitValues).size =
      trace.targetParams.size)
    (blockCredits : block.creditParams = #[]) :
    let target : Eval.Frame :=
      { frame with
        block := trace.target
        pc := 0
        values := implicitValues ++ explicitValues
        credits := #[] }
    Eval.EdgeTransfer frame edge implicitValues target ∧
      EnvRel (implicitValues.toList ++ source) target.values trace.sourceMap := by
  dsimp only
  have targetResolved : Eval.resolveAtoms frame.values edge.values =
      .ok explicitValues := by simpa [edgeValues] using resolved
  have targetBlock : frame.definition.blocks[edge.target]? = some block := by
    simpa [edgeTarget] using blockAt
  have targetArity : (implicitValues ++ explicitValues).size =
      block.valueParams.size := by
    rw [blockParams]
    exact valueArity
  constructor
  · simpa [edgeTarget] using Eval.EdgeTransfer.baseline targetResolved
      frameCredits edgeCredits targetBlock targetArity blockCredits
  · simpa [traceMap, implicitCount] using
      environments.sourceMapOf implicitValues

/-- Operand resolution is representation-independent once the generated
environment map is related. This is the common first step of the `move`,
memory-operation, call, return, and switch simulation cases. -/
theorem resolveAtom_of_envRel {source : List RVal} {target : Array RVal}
    {mapping : EnvMap} (relation : EnvRel source target mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (resolved : IxIR1.resolveAtom source sourceAtom = .ok value) :
    Eval.resolveAtom target targetAtom = .ok value := by
  cases sourceAtom with
  | var index =>
      have sourceGet : source[index]? = some value := by
        cases found : source[index]? with
        | none => simp [IxIR1.resolveAtom, found] at resolved
        | some candidate =>
            have equal : candidate = value := by
              simpa [IxIR1.resolveAtom, found] using resolved
            exact congrArg some equal
      cases mappedGet : mapping[index]? with
      | none =>
          simp [Lower.InputMap.translateAtom, mappedGet] at translated
      | some slot =>
          cases slot with
          | none =>
              simp [Lower.InputMap.translateAtom, mappedGet] at translated
          | some mappedAtom =>
              have atomEq : mappedAtom = targetAtom := by
                simpa [Lower.InputMap.translateAtom, mappedGet] using translated
              subst mappedAtom
              exact relation index value targetAtom sourceGet mappedGet
  | lit literal =>
      simp only [Lower.InputMap.translateAtom, Option.some.injEq] at translated
      subst targetAtom
      simp only [IxIR1.resolveAtom, Except.ok.injEq] at resolved
      subst value
      rfl
  | erased =>
      simp only [Lower.InputMap.translateAtom, Option.some.injEq] at translated
      subst targetAtom
      simp only [IxIR1.resolveAtom, Except.ok.injEq] at resolved
      subst value
      rfl

/-- A translated target operand can be reflected back to its source operand
when the checked environment map has the certified source length. -/
theorem resolveAtom_of_envRel_target {source : List IxIR1.RVal}
    {target : Array IxIR1.RVal} {mapping : EnvMap}
    (relation : EnvRel source target mapping)
    (sourceCount : source.length = mapping.size)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : IxIR1.RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (resolved : Eval.resolveAtom target targetAtom = .ok value) :
    IxIR1.resolveAtom source sourceAtom = .ok value := by
  cases sourceAtom with
  | var index =>
      cases mappedGet : mapping[index]? with
      | none =>
          simp [Lower.InputMap.translateAtom, mappedGet] at translated
      | some slot =>
          cases slot with
          | none =>
              simp [Lower.InputMap.translateAtom, mappedGet] at translated
          | some mappedAtom =>
              have atomEq : mappedAtom = targetAtom := by
                simpa [Lower.InputMap.translateAtom, mappedGet] using translated
              subst mappedAtom
              have mapBound : index < mapping.size :=
                (Array.getElem?_eq_some_iff.mp mappedGet).1
              have sourceBound : index < source.length := by
                rw [sourceCount]
                exact mapBound
              let sourceValue := source[index]
              have sourceGet : source[index]? = some sourceValue := by
                simp [sourceValue, sourceBound]
              have targetSource := relation index sourceValue targetAtom
                sourceGet mappedGet
              have valueEq : sourceValue = value :=
                Except.ok.inj (targetSource.symm.trans resolved)
              simp [IxIR1.resolveAtom, sourceGet, valueEq]
  | lit literal =>
      simp only [Lower.InputMap.translateAtom, Option.some.injEq] at translated
      subst targetAtom
      simp only [Eval.resolveAtom, Except.ok.injEq] at resolved
      subst value
      rfl
  | erased =>
      simp only [Lower.InputMap.translateAtom, Option.some.injEq] at translated
      subst targetAtom
      simp only [Eval.resolveAtom, Except.ok.injEq] at resolved
      subst value
      rfl

/-- Appending a new SSA value does not change resolution of any atom that was
already valid in the frame. -/
theorem resolveAtom_push_old {target : Array RVal} {atom : Atom}
    {value extra : RVal}
    (resolved : Eval.resolveAtom target atom = .ok value) :
    Eval.resolveAtom (target.push extra) atom = .ok value := by
  cases atom with
  | lit literal => exact resolved
  | erased => exact resolved
  | reg index =>
      have notEnd : index ≠ target.size := by
        intro equal
        subst index
        simp [Eval.resolveAtom] at resolved
      simpa [Eval.resolveAtom, Array.getElem?_push, notEnd] using resolved

/-- Appending any value suffix preserves resolution of atoms that were valid
in the original register file. -/
theorem resolveAtom_append_old {target suffix : Array RVal} {atom : Atom}
    {value : RVal}
    (resolved : Eval.resolveAtom target atom = .ok value) :
    Eval.resolveAtom (target ++ suffix) atom = .ok value := by
  cases atom with
  | lit literal => exact resolved
  | erased => exact resolved
  | reg index =>
      cases found : target[index]? with
      | none => simp [Eval.resolveAtom, found] at resolved
      | some candidate =>
          have bound : index < target.size :=
            (Array.getElem?_eq_some_iff.mp found).1
          simpa [Eval.resolveAtom, Array.getElem?_append, bound, found] using
            resolved

/-- Result-producing instructions prepend one source de Bruijn binding while
appending one target SSA register. -/
theorem EnvRel.bindValue {source : List RVal} {target : Array RVal}
    {mapping : EnvMap} (relation : EnvRel source target mapping)
    (value : RVal) :
    EnvRel (value :: source) (target.push value)
      (#[some (.reg target.size)] ++ mapping) := by
  intro index candidate atom sourceGet mapped
  cases index with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at sourceGet
      subst candidate
      have atomEq : atom = .reg target.size := by
        simpa [Array.getElem?_append] using mapped.symm
      subst atom
      simp [Eval.resolveAtom]
  | succ index =>
      have oldGet : source[index]? = some candidate := by
        simpa using sourceGet
      have oldMapped : mapping[index]? = some (some atom) := by
        simpa [Array.getElem?_append] using mapped
      exact resolveAtom_push_old
        (relation index candidate atom oldGet oldMapped)

/-- Generic value-producing continuation state.  This is shared by ordinary
one-step operations, direct calls after their callee returns, and dynamic
application after its PAP chain eventually resumes the original caller. -/
theorem CodeStateRel.letOpValueNext
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {operation : IxIR1.Op} {instruction : Instr} {next : Lower.CodeTrace}
    {source : List RVal} {frame : Eval.Frame}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next) source frame)
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next))
    (binder : Lower.Instr.baselineBinderAtom entryValueCount instruction =
      some (.reg entryValueCount))
    (delta : Lower.Instr.baselineValueDelta instruction = some 1)
    (value : RVal) :
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push value }
    CodeStateRel functionTrace next (value :: source) nextFrame := by
  dsimp only
  have canonical := state.environments.bindValue value
  have nextEnvironments := canonical.forgetTracedValue state descendant binder
  exact state.letOpNext descendant rfl rfl rfl
    (by simp [delta]) rfl nextEnvironments

/-- Constructor alternatives prepend source fields in reverse order while
their generated fetch prologue appends target registers in field order. This
is the exact environment shape retained in `constructorChildInputMap`. -/
theorem EnvRel.constructorFields {source : List RVal}
    {target fields : Array RVal} {mapping : EnvMap}
    (relation : EnvRel source target mapping) :
    EnvRel (fields.toList.reverse ++ source) (target ++ fields)
      (Lower.constructorChildInputMap target.size fields.size ++ mapping) := by
  intro index value atom sourceGet mapped
  by_cases prefixIndex : index < fields.size
  · have sourcePrefix : fields.toList.reverse[index]? = some value := by
      have prefixIndex' : index < fields.toList.reverse.length := by
        simpa using prefixIndex
      rw [List.getElem?_append_left prefixIndex'] at sourceGet
      exact sourceGet
    have originalBound : index < fields.toList.length := by
      simpa using prefixIndex
    rw [List.getElem?_reverse (l := fields.toList) originalBound] at sourcePrefix
    let fieldIndex := fields.size - 1 - index
    have fieldAt : fields[fieldIndex]? = some value := by
      simpa [fieldIndex] using sourcePrefix
    have atomEq : atom = .reg (target.size + fieldIndex) := by
      have rangeAt : (List.range fields.size).reverse[index]? =
          some fieldIndex := by
        rw [List.getElem?_reverse (l := List.range fields.size)
          (by simpa using prefixIndex)]
        have fieldIndexBound : fieldIndex < fields.size := by
          dsimp [fieldIndex]
          omega
        have rangeField : (List.range fields.size)[fieldIndex]? =
            some fieldIndex := List.getElem?_range fieldIndexBound
        simpa [fieldIndex] using rangeField
      have mapAt :
          (Lower.constructorChildInputMap target.size fields.size)[index]? =
            some (some (.reg (target.size + fieldIndex))) := by
        unfold Lower.constructorChildInputMap
        rw [Array.getElem?_map, List.getElem?_toArray, rangeAt]
        rfl
      have mapPrefix : index <
          (Lower.constructorChildInputMap target.size fields.size).size := by
        simpa [Lower.constructorChildInputMap] using prefixIndex
      rw [Array.getElem?_append, if_pos mapPrefix, mapAt] at mapped
      simpa using mapped.symm
    subst atom
    have afterTarget : ¬target.size + fieldIndex < target.size := by omega
    simp [Eval.resolveAtom, Array.getElem?_append, afterTarget, fieldAt]
  · have afterPrefix : fields.size ≤ index := Nat.le_of_not_gt prefixIndex
    let sourceIndex := index - fields.size
    have sourceAt : source[sourceIndex]? = some value := by
      rw [List.getElem?_append_right (by simpa using afterPrefix)] at sourceGet
      simpa [sourceIndex] using sourceGet
    unfold Lower.constructorChildInputMap at mapped
    simp only [Array.getElem?_append, Array.size_map, List.size_toArray,
      List.length_reverse, List.length_range, prefixIndex] at mapped
    exact resolveAtom_append_old
      (relation sourceIndex value atom sourceAt
        (by simpa [sourceIndex] using mapped))

/-- Effect-only IxIR₂ instructions append no SSA value; their IxIR₁ result
binder is represented directly by the erased atom. -/
theorem EnvRel.bindErased {source : List RVal} {target : Array RVal}
    {mapping : EnvMap} (relation : EnvRel source target mapping) :
    EnvRel (.erased :: source) target (#[some .erased] ++ mapping) := by
  intro index candidate atom sourceGet mapped
  cases index with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at sourceGet
      subst candidate
      have atomEq : atom = .erased := by
        simpa [Array.getElem?_append] using mapped.symm
      subst atom
      rfl
  | succ index =>
      have oldGet : source[index]? = some candidate := by
        simpa using sourceGet
      have oldMapped : mapping[index]? = some (some atom) := by
        simpa [Array.getElem?_append] using mapped
      exact relation index candidate atom oldGet oldMapped

/-- A target `move` takes exactly one public small step, preserving the store,
stack, and credits while advancing the program counter and appending its
resolved value.  This packages the evaluator reduction needed by the source
`pure` instruction case. -/
theorem step_move {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation} {block : Block}
    {atom : Atom} {value : RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .move atom)
    (resolved : Eval.resolveAtom frame.values atom = .ok value) :
    Eval.Step context interpretation machine
      { machine with
        control := .running
          { frame with
            pc := frame.pc + 1
            values := frame.values.push value }
          stack } := by
  exact Eval.Step.move control blockAt pc instruction resolved

/-- The source `pure`/target `move` boundary preserves operand meaning and the
environment relation needed by the continuation. -/
theorem pure_move_preserves {source : List RVal} {target : Array RVal}
    {mapping : EnvMap} (relation : EnvRel source target mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (resolved : IxIR1.resolveAtom source sourceAtom = .ok value) :
    Eval.resolveAtom target targetAtom = .ok value ∧
      EnvRel (value :: source) (target.push value)
        (#[some (.reg target.size)] ++ mapping) := by
  exact ⟨resolveAtom_of_envRel relation translated resolved,
    relation.bindValue value⟩

/-- First instruction-level simulation case: a related IxIR₁ `pure` operand
drives the generated IxIR₂ `move` step, and the successor environments are
again related. -/
theorem simulate_pure_move {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation} {block : Block}
    {source : List RVal} {mapping : EnvMap}
    (relation : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .move targetAtom) :
    Eval.Step context interpretation machine
        { machine with
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push value }
            stack } ∧
      EnvRel (value :: source) (frame.values.push value)
        (#[some (.reg frame.values.size)] ++ mapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok value :=
    resolveAtom_of_envRel relation translated sourceResolved
  exact ⟨step_move control blockAt pc instruction targetResolved,
    relation.bindValue value⟩

/-- Trace-facing `pure`/`move` case. Recursive-trace membership supplies the
actual generated block, instruction coordinate, and translated target
operand; callers retain only runtime frame alignment and source resolution. -/
theorem simulate_traced_pure_move {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.pure sourceAtom) index (.move targetAtom) next))
    {source : List RVal} {value : RVal}
    (relation : EnvRel source frame.values input)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (definition : frame.definition = functionTrace.generated)
    (frameBlock : frame.block = blockId)
    (framePc : frame.pc = index)
    (entryValues : entryValueCount = frame.values.size)
    (sourceCount : source.length = input.size)
    (control : machine.control = .running frame stack) :
    Eval.Step context interpretation machine
        { machine with
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push value }
            stack } ∧
      EnvRel (value :: source) (frame.values.push value) nextInput := by
  have translated : translateAtom input sourceAtom = some targetAtom := by
    simpa [Lower.OperationSyntax] using
      functionTrace.descendantOperationSyntax descendant
  obtain ⟨localMatch, generatedBlock⟩ :=
    functionTrace.descendantLetOpMatch descendant
  have blockAt :
      frame.definition.blocks[frame.block]? = some next.headBlock.2 := by
    simpa [definition, frameBlock] using generatedBlock
  obtain ⟨indexBound, instructionAt⟩ :=
    Array.getElem?_eq_some_iff.mp localMatch.instructionAt
  have pcBound : frame.pc < next.headBlock.2.instructions.size := by
    simpa [framePc] using indexBound
  have instruction :
      next.headBlock.2.instructions[frame.pc] = .move targetAtom := by
    simpa [framePc] using instructionAt
  have simulated := simulate_pure_move
    (context := context) (interpretation := interpretation)
    relation translated sourceResolved control blockAt pcBound instruction
  exact ⟨simulated.1,
    simulated.2.forgetTracedValue
      (show CodeStateRel functionTrace
        (.letOp site blockId input nextInput entryValueCount
          (.pure sourceAtom) index (.move targetAtom) next) source frame from
        { definition
          block := by simpa [Lower.CodeTrace.sourceBlock] using frameBlock
          pc := by simpa [Lower.CodeTrace.entryPc] using framePc
          valueCount := by
            simpa [Lower.CodeTrace.entryValueCount] using entryValues.symm
          sourceCount := by
            simpa [Lower.CodeTrace.sourceInputMap] using sourceCount
          environments := relation })
      descendant rfl⟩

/-- Recursive-state form of the trace-facing `pure`/`move` case. Besides the
one target step, it establishes the exact `CodeStateRel` expected by the
continuation trace, including compiler-certified block and PC progression. -/
theorem simulate_traced_pure_move_state {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.pure sourceAtom) index (.move targetAtom) next))
    {source : List RVal} {value : RVal}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.pure sourceAtom) index (.move targetAtom) next) source frame)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (control : machine.control = .running frame stack) :
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push value }
    Eval.Step context interpretation machine
        { machine with control := .running nextFrame stack } ∧
      CodeStateRel functionTrace next (value :: source) nextFrame := by
  dsimp only
  have frameBlock : frame.block = blockId := by
    simpa [Lower.CodeTrace.sourceBlock] using state.block
  have framePc : frame.pc = index := by
    simpa [Lower.CodeTrace.entryPc] using state.pc
  have entryValues : entryValueCount = frame.values.size := by
    simpa [Lower.CodeTrace.entryValueCount] using state.valueCount.symm
  have simulated := simulate_traced_pure_move
    (context := context) (interpretation := interpretation)
    descendant state.environments sourceResolved state.definition
      frameBlock framePc entryValues
      (by simpa [Lower.CodeTrace.sourceInputMap] using state.sourceCount)
      control
  refine ⟨simulated.1, state.letOpNext descendant rfl rfl rfl ?_ rfl
    simulated.2⟩
  simp [Lower.Instr.baselineValueDelta]

/-- Successful-run form of the `pure`/`move` induction case.  Source
evaluation is inverted into its exact atom-resolution and continuation run,
while the target takes one step into the recursive trace state.  A later
semantic induction only has to apply its continuation hypothesis to the
returned `runCode` equation and `CodeStateRel`. -/
theorem simulate_traced_pure_move_success_step
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat} {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.pure sourceAtom) index (.move targetAtom) next))
    {sourceStore : IxIR1.Store} {source : List RVal}
    {sourceOutput : IxIR1.Store × RVal}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.pure sourceAtom) index (.move targetAtom) next) source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 2)
      sourceCurrent sourceStore source
        (.letOp (.pure sourceAtom) next.sourceCode) = .ok sourceOutput)
    (control : machine.control = .running frame stack) :
    ∃ value nextFrame,
      nextFrame =
          { frame with
            pc := frame.pc + 1
            values := frame.values.push value } ∧
        IxIR1.resolveAtom source sourceAtom = .ok value ∧
        IxIR1.runCode sourceContext (sourceFuel + 1) sourceCurrent
          sourceStore (value :: source) next.sourceCode = .ok sourceOutput ∧
        Eval.Step context interpretation machine
          { machine with control := .running nextFrame stack } ∧
        StoreRel sourceStore
          ({ machine with control := .running nextFrame stack } :
            Eval.Machine).store ∧
        CodeStateRel functionTrace next (value :: source) nextFrame := by
  dsimp only
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  obtain ⟨value, sourceResolved, operationOutput⟩ :=
    IxIR1.runOp_pure_success operationRun
  have middleStoreEq : middleStore = sourceStore :=
    congrArg Prod.fst operationOutput
  have operationValueEq : operationValue = value :=
    congrArg Prod.snd operationOutput
  subst middleStore
  subst operationValue
  obtain ⟨targetStep, nextState⟩ :=
    simulate_traced_pure_move_state descendant state sourceResolved control
  exact ⟨value,
    { frame with
      pc := frame.pc + 1
      values := frame.values.push value },
    rfl, sourceResolved, continuationRun, targetStep, stores, nextState⟩

/-- Retaining a scalar is operationally inert. -/
theorem retainShared_of_scalar {store : Eval.Store} {value : RVal}
    (scalar : Eval.RVal.isScalar value = true) :
    Eval.retainShared store value = .ok store := by
  cases value <;> simp [Eval.RVal.isScalar, Eval.retainShared] at scalar ⊢

/-- Releasing a scalar leaves the store unchanged and spends exactly the one
heap-traversal unit used to inspect the work-list item. -/
theorem releaseShared_of_scalar {store : Eval.Store} {value : RVal}
    (heapFuel : Nat) (scalar : Eval.RVal.isScalar value = true) :
    Eval.releaseShared (heapFuel + 1) store value = .ok (store, heapFuel) := by
  cases value <;>
    simp [Eval.RVal.isScalar, Eval.releaseShared,
      Eval.releaseSharedWork] at scalar ⊢

/-- Dropping a unique scalar has the same one-item heap-budget behavior as a
shared scalar release. -/
theorem dropUnique_of_scalar {store : Eval.Store} {value : RVal}
    (heapFuel : Nat) (scalar : Eval.RVal.isScalar value = true) :
    Eval.dropUnique (heapFuel + 1) store value = .ok (store, heapFuel) := by
  cases value <;>
    simp [Eval.RVal.isScalar, Eval.dropUnique,
      Eval.dropUniqueWork] at scalar ⊢

/-- IxIR₁ shared dropping is inert on one scalar whenever its recursive fuel
is positive. -/
theorem sourceDropVal_of_scalar {context : IxIR1.Ctx}
    {store : IxIR1.Store} {value : RVal} (fuel : Nat)
    (scalar : Eval.RVal.isScalar value = true) :
    IxIR1.dropVal context (fuel + 1) store value = .ok store := by
  cases value <;>
    simp [Eval.RVal.isScalar, IxIR1.dropVal] at scalar ⊢

/-- IxIR₁ unique dropping is likewise inert on one scalar. -/
theorem sourceDropUVal_of_scalar {context : IxIR1.Ctx}
    {store : IxIR1.Store} {value : RVal} (fuel : Nat)
    (scalar : Eval.RVal.isScalar value = true) :
    IxIR1.dropUVal context (fuel + 1) store value = .ok store := by
  cases value <;>
    simp [Eval.RVal.isScalar, IxIR1.dropUVal] at scalar ⊢

/-- A scalar list needs one more unit of IxIR₁ recursive fuel than its length,
because the source list worker also inspects the empty tail. -/
theorem sourceDropMany_of_scalars {context : IxIR1.Ctx}
    {store : IxIR1.Store} {values : List RVal}
    (scalars : values.all Eval.RVal.isScalar = true) :
    IxIR1.dropMany context (values.length + 1) store values = .ok store := by
  induction values with
  | nil => simp [IxIR1.dropMany]
  | cons value values ih =>
      simp only [List.all_cons, Bool.and_eq_true] at scalars
      have head := sourceDropVal_of_scalar (context := context)
        (store := store) values.length scalars.1
      rw [show (value :: values).length + 1 =
        (values.length + 1) + 1 by simp]
      rw [IxIR1.dropMany.eq_def]
      simp only
      rw [head]
      simp only [bind, Except.bind]
      exact ih scalars.2

/-- The unique source list worker has the same scalar-list fuel equation. -/
theorem sourceDropManyU_of_scalars {context : IxIR1.Ctx}
    {store : IxIR1.Store} {values : List RVal}
    (scalars : values.all Eval.RVal.isScalar = true) :
    IxIR1.dropManyU context (values.length + 1) store values = .ok store := by
  induction values with
  | nil => simp [IxIR1.dropManyU]
  | cons value values ih =>
      simp only [List.all_cons, Bool.and_eq_true] at scalars
      have head := sourceDropUVal_of_scalar (context := context)
        (store := store) values.length scalars.1
      rw [show (value :: values).length + 1 =
        (values.length + 1) + 1 by simp]
      rw [IxIR1.dropManyU.eq_def]
      simp only
      rw [head]
      simp only [bind, Except.bind]
      exact ih scalars.2

/-- IxIR₂ spends exactly one heap unit per scalar shared-release work item. -/
theorem releaseSharedWork_of_scalars {store : Eval.Store}
    {values : List RVal} (heapFuel : Nat)
    (scalars : values.all Eval.RVal.isScalar = true) :
    Eval.releaseSharedWork (heapFuel + values.length) store values =
      .ok (store, heapFuel) := by
  induction values generalizing heapFuel with
  | nil => simp [Eval.releaseSharedWork]
  | cons value values ih =>
      simp only [List.all_cons, Bool.and_eq_true] at scalars
      rw [show heapFuel + (value :: values).length =
        (heapFuel + values.length) + 1 by
          simp only [List.length_cons]
          omega]
      cases value with
      | loc location => simp [Eval.RVal.isScalar] at scalars
      | lit literal =>
          simp only [Eval.releaseSharedWork]
          exact ih heapFuel scalars.2
      | erased =>
          simp only [Eval.releaseSharedWork]
          exact ih heapFuel scalars.2

/-- IxIR₂ unique destruction has the same exact scalar work-list budget. -/
theorem dropUniqueWork_of_scalars {store : Eval.Store}
    {values : List RVal} (heapFuel : Nat)
    (scalars : values.all Eval.RVal.isScalar = true) :
    Eval.dropUniqueWork (heapFuel + values.length) store values =
      .ok (store, heapFuel) := by
  induction values generalizing heapFuel with
  | nil => simp [Eval.dropUniqueWork]
  | cons value values ih =>
      simp only [List.all_cons, Bool.and_eq_true] at scalars
      rw [show heapFuel + (value :: values).length =
        (heapFuel + values.length) + 1 by
          simp only [List.length_cons]
          omega]
      cases value with
      | loc location => simp [Eval.RVal.isScalar] at scalars
      | lit literal =>
          simp only [Eval.dropUniqueWork]
          exact ih heapFuel scalars.2
      | erased =>
          simp only [Eval.dropUniqueWork]
          exact ih heapFuel scalars.2

/-- Exact-budget shared-release work on a prefix composes with an
independently budgeted suffix.  Recursive final-owner expansion stays in the
prefix because the target prepends the released node's children. -/
theorem releaseSharedWork_append {firstFuel secondFuel : Nat}
    {store middle output : Eval.Store} {first second : List RVal}
    {remaining : Nat}
    (firstRun : Eval.releaseSharedWork firstFuel store first =
      .ok (middle, 0))
    (secondRun : Eval.releaseSharedWork secondFuel middle second =
      .ok (output, remaining)) :
    Eval.releaseSharedWork (firstFuel + secondFuel) store (first ++ second) =
      .ok (output, remaining) := by
  induction firstFuel generalizing store first middle with
  | zero =>
      cases first with
      | nil =>
          simp only [Eval.releaseSharedWork, Except.ok.injEq, Prod.mk.injEq]
            at firstRun
          obtain ⟨rfl, _⟩ := firstRun
          simpa [Eval.releaseSharedWork] using secondRun
      | cons value first => simp [Eval.releaseSharedWork] at firstRun
  | succ firstFuel ih =>
      cases first with
      | nil => simp [Eval.releaseSharedWork] at firstRun
      | cons value first =>
          cases value with
          | lit literal =>
              have prefix' :
                  Eval.releaseSharedWork firstFuel store first =
                    .ok (middle, 0) := by
                simpa [Eval.releaseSharedWork] using firstRun
              have combined := ih prefix' secondRun
              simpa [Eval.releaseSharedWork, Nat.succ_add] using combined
          | erased =>
              have prefix' :
                  Eval.releaseSharedWork firstFuel store first =
                    .ok (middle, 0) := by
                simpa [Eval.releaseSharedWork] using firstRun
              have combined := ih prefix' secondRun
              simpa [Eval.releaseSharedWork, Nat.succ_add] using combined
          | loc location =>
              cases boxAt : store.get? location with
              | none => simp [Eval.releaseSharedWork, boxAt] at firstRun
              | some box =>
                  cases world : box.world with
                  | unique =>
                      simp [Eval.releaseSharedWork, boxAt, world] at firstRun
                  | shared =>
                      by_cases zero : box.rc = 0
                      · simp [Eval.releaseSharedWork, boxAt, world, zero]
                          at firstRun
                      · by_cases unit : box.rc = 1
                        · cases node : box.node with
                          | ctorN cid fields =>
                              have prefix' :
                                  Eval.releaseSharedWork firstFuel
                                      (store.rcTick.kill location)
                                      (fields.toList ++ first) =
                                    .ok (middle, 0) := by
                                simpa [Eval.releaseSharedWork, boxAt, world,
                                  zero, unit, node] using firstRun
                              have combined := ih prefix' secondRun
                              simpa [Eval.releaseSharedWork, boxAt, world,
                                zero, unit, node, Nat.succ_add,
                                List.append_assoc] using combined
                          | papN address arity arguments =>
                              have prefix' :
                                  Eval.releaseSharedWork firstFuel
                                      (store.rcTick.kill location)
                                      (arguments.toList ++ first) =
                                    .ok (middle, 0) := by
                                simpa [Eval.releaseSharedWork, boxAt, world,
                                  zero, unit, node] using firstRun
                              have combined := ih prefix' secondRun
                              simpa [Eval.releaseSharedWork, boxAt, world,
                                zero, unit, node, Nat.succ_add,
                                List.append_assoc] using combined
                        · have prefix' :
                              Eval.releaseSharedWork firstFuel
                                  (store.rcTick.setBox location
                                    { box with rc := box.rc - 1 }) first =
                                .ok (middle, 0) := by
                            simpa [Eval.releaseSharedWork, boxAt, world,
                              zero, unit] using firstRun
                          have combined := ih prefix' secondRun
                          simpa [Eval.releaseSharedWork, boxAt, world,
                            zero, unit, Nat.succ_add] using combined

/-- A successful shared-release work list consumes a store/value-determined
amount of heap fuel. Different initial budgets therefore produce the same
store and differ only by their residual suffix. -/
theorem releaseSharedWork_success_unique
    {leftFuel rightFuel : Nat}
    {store leftStore rightStore : Eval.Store}
    {values : List RVal} {leftRemaining rightRemaining : Nat}
    (left : Eval.releaseSharedWork leftFuel store values =
      .ok (leftStore, leftRemaining))
    (right : Eval.releaseSharedWork rightFuel store values =
      .ok (rightStore, rightRemaining)) :
    leftStore = rightStore ∧
      leftFuel + rightRemaining = rightFuel + leftRemaining := by
  induction leftFuel generalizing rightFuel store values leftStore rightStore
      leftRemaining rightRemaining with
  | zero =>
      cases values with
      | nil =>
          simp [Eval.releaseSharedWork] at left right
          obtain ⟨rfl, rfl⟩ := left
          obtain ⟨rfl, rfl⟩ := right
          exact ⟨rfl, by omega⟩
      | cons value values => simp [Eval.releaseSharedWork] at left
  | succ leftFuel ih =>
      cases values with
      | nil =>
          simp [Eval.releaseSharedWork] at left right
          obtain ⟨rfl, rfl⟩ := left
          obtain ⟨rfl, rfl⟩ := right
          exact ⟨rfl, by omega⟩
      | cons value values =>
          cases rightFuel with
          | zero => simp [Eval.releaseSharedWork] at right
          | succ rightFuel =>
              cases value with
              | lit literal =>
                  obtain ⟨storeEq, fuelEq⟩ :=
                    ih (rightFuel := rightFuel) left right
                  exact ⟨storeEq, by omega⟩
              | erased =>
                  obtain ⟨storeEq, fuelEq⟩ :=
                    ih (rightFuel := rightFuel) left right
                  exact ⟨storeEq, by omega⟩
              | loc location =>
                  cases found : store.get? location with
                  | none => simp [Eval.releaseSharedWork, found] at left
                  | some box =>
                      cases world : box.world with
                      | unique =>
                          simp [Eval.releaseSharedWork, found, world] at left
                      | shared =>
                          by_cases zero : box.rc = 0
                          · simp [Eval.releaseSharedWork, found, world, zero]
                              at left
                          · by_cases unit : box.rc = 1
                            · cases node : box.node with
                              | ctorN cid fields =>
                                  obtain ⟨storeEq, fuelEq⟩ :=
                                    ih (rightFuel := rightFuel)
                                    (store := store.rcTick.kill location)
                                    (values := fields.toList ++ values)
                                    (by simpa [Eval.releaseSharedWork, found,
                                      world, zero, unit, node] using left)
                                    (by simpa [Eval.releaseSharedWork, found,
                                      world, zero, unit, node] using right)
                                  exact ⟨storeEq, by omega⟩
                              | papN address arity arguments =>
                                  obtain ⟨storeEq, fuelEq⟩ :=
                                    ih (rightFuel := rightFuel)
                                    (store := store.rcTick.kill location)
                                    (values := arguments.toList ++ values)
                                    (by simpa [Eval.releaseSharedWork, found,
                                      world, zero, unit, node] using left)
                                    (by simpa [Eval.releaseSharedWork, found,
                                      world, zero, unit, node] using right)
                                  exact ⟨storeEq, by omega⟩
                            · obtain ⟨storeEq, fuelEq⟩ :=
                                ih (rightFuel := rightFuel)
                                (store := store.rcTick.setBox location
                                  { box with rc := box.rc - 1 })
                                (values := values)
                                (by simpa [Eval.releaseSharedWork, found,
                                  world, zero, unit] using left)
                                (by simpa [Eval.releaseSharedWork, found,
                                  world, zero, unit] using right)
                              exact ⟨storeEq, by omega⟩

/-- An exact shared-release traversal can carry any independently chosen heap
fuel suffix through unchanged.  This is the backward-budget framing rule used
when a destructive instruction is prefixed to an already funded continuation. -/
theorem releaseSharedWork_add_suffix {localFuel suffix : Nat}
    {store output : Eval.Store} {values : List RVal}
    (run : Eval.releaseSharedWork localFuel store values = .ok (output, 0)) :
    Eval.releaseSharedWork (localFuel + suffix) store values =
      .ok (output, suffix) := by
  have emptyRun : Eval.releaseSharedWork suffix output [] =
      .ok (output, suffix) := by
    simp [Eval.releaseSharedWork]
  simpa using releaseSharedWork_append run emptyRun

/-- Single-value wrapper of `releaseSharedWork_add_suffix`. -/
theorem releaseShared_add_suffix {localFuel suffix : Nat}
    {store output : Eval.Store} {value : RVal}
    (run : Eval.releaseShared localFuel store value = .ok (output, 0)) :
    Eval.releaseShared (localFuel + suffix) store value =
      .ok (output, suffix) := by
  exact releaseSharedWork_add_suffix run

/-- Exact-budget unique work on a prefix composes with an independently
budgeted suffix.  The zero remaining fuel pins the split point unambiguously. -/
theorem dropUniqueWork_append {firstFuel secondFuel : Nat}
    {store middle output : Eval.Store} {first second : List RVal}
    {remaining : Nat}
    (firstRun : Eval.dropUniqueWork firstFuel store first = .ok (middle, 0))
    (secondRun : Eval.dropUniqueWork secondFuel middle second =
      .ok (output, remaining)) :
    Eval.dropUniqueWork (firstFuel + secondFuel) store (first ++ second) =
      .ok (output, remaining) := by
  induction firstFuel generalizing store first middle with
  | zero =>
      cases first with
      | nil =>
          simp only [Eval.dropUniqueWork, Except.ok.injEq, Prod.mk.injEq]
            at firstRun
          obtain ⟨rfl, _⟩ := firstRun
          simpa [Eval.dropUniqueWork] using secondRun
      | cons value first => simp [Eval.dropUniqueWork] at firstRun
  | succ firstFuel ih =>
      cases first with
      | nil => simp [Eval.dropUniqueWork] at firstRun
      | cons value first =>
          cases value with
          | lit literal =>
              have prefix' :
                  Eval.dropUniqueWork firstFuel store first =
                    .ok (middle, 0) := by
                simpa [Eval.dropUniqueWork] using firstRun
              have combined := ih prefix' secondRun
              simpa [Eval.dropUniqueWork, Nat.succ_add] using combined
          | erased =>
              have prefix' :
                  Eval.dropUniqueWork firstFuel store first =
                    .ok (middle, 0) := by
                simpa [Eval.dropUniqueWork] using firstRun
              have combined := ih prefix' secondRun
              simpa [Eval.dropUniqueWork, Nat.succ_add] using combined
          | loc location =>
              cases boxAt : store.get? location with
              | none => simp [Eval.dropUniqueWork, boxAt] at firstRun
              | some box =>
                  cases world : box.world with
                  | shared =>
                      simp [Eval.dropUniqueWork, boxAt, world] at firstRun
                  | unique =>
                      cases node : box.node with
                      | papN address arity arguments =>
                          simp [Eval.dropUniqueWork, boxAt, world, node]
                            at firstRun
                      | ctorN cid fields =>
                          have prefix' :
                              Eval.dropUniqueWork firstFuel
                                  (store.kill location)
                                  (fields.toList ++ first) =
                                .ok (middle, 0) := by
                            simpa [Eval.dropUniqueWork, boxAt, world, node]
                              using firstRun
                          have combined := ih prefix' secondRun
                          simpa [Eval.dropUniqueWork, boxAt, world, node,
                            Nat.succ_add, List.append_assoc] using combined

/-- A successful unique-drop work list consumes a store/value-determined
amount of heap fuel. Different initial budgets therefore produce the same
store and differ only by their residual suffix. -/
theorem dropUniqueWork_success_unique
    {leftFuel rightFuel : Nat}
    {store leftStore rightStore : Eval.Store}
    {values : List RVal} {leftRemaining rightRemaining : Nat}
    (left : Eval.dropUniqueWork leftFuel store values =
      .ok (leftStore, leftRemaining))
    (right : Eval.dropUniqueWork rightFuel store values =
      .ok (rightStore, rightRemaining)) :
    leftStore = rightStore ∧
      leftFuel + rightRemaining = rightFuel + leftRemaining := by
  induction leftFuel generalizing rightFuel store values leftStore rightStore
      leftRemaining rightRemaining with
  | zero =>
      cases values with
      | nil =>
          simp [Eval.dropUniqueWork] at left right
          obtain ⟨rfl, rfl⟩ := left
          obtain ⟨rfl, rfl⟩ := right
          exact ⟨rfl, by omega⟩
      | cons value values => simp [Eval.dropUniqueWork] at left
  | succ leftFuel ih =>
      cases values with
      | nil =>
          simp [Eval.dropUniqueWork] at left right
          obtain ⟨rfl, rfl⟩ := left
          obtain ⟨rfl, rfl⟩ := right
          exact ⟨rfl, by omega⟩
      | cons value values =>
          cases rightFuel with
          | zero => simp [Eval.dropUniqueWork] at right
          | succ rightFuel =>
              cases value with
              | lit literal =>
                  obtain ⟨storeEq, fuelEq⟩ :=
                    ih (rightFuel := rightFuel) left right
                  exact ⟨storeEq, by omega⟩
              | erased =>
                  obtain ⟨storeEq, fuelEq⟩ :=
                    ih (rightFuel := rightFuel) left right
                  exact ⟨storeEq, by omega⟩
              | loc location =>
                  cases found : store.get? location with
                  | none => simp [Eval.dropUniqueWork, found] at left
                  | some box =>
                      cases world : box.world with
                      | shared =>
                          simp [Eval.dropUniqueWork, found, world] at left
                      | unique =>
                          cases node : box.node with
                          | papN address arity arguments =>
                              simp [Eval.dropUniqueWork, found, world, node]
                                at left
                          | ctorN cid fields =>
                              obtain ⟨storeEq, fuelEq⟩ :=
                                ih (rightFuel := rightFuel)
                                  (store := store.kill location)
                                  (values := fields.toList ++ values)
                                  (by simpa [Eval.dropUniqueWork, found,
                                    world, node] using left)
                                  (by simpa [Eval.dropUniqueWork, found,
                                    world, node] using right)
                              exact ⟨storeEq, by omega⟩

/-- An exact unique-drop traversal can carry any independently chosen heap
fuel suffix through unchanged. -/
theorem dropUniqueWork_add_suffix {localFuel suffix : Nat}
    {store output : Eval.Store} {values : List RVal}
    (run : Eval.dropUniqueWork localFuel store values = .ok (output, 0)) :
    Eval.dropUniqueWork (localFuel + suffix) store values =
      .ok (output, suffix) := by
  have emptyRun : Eval.dropUniqueWork suffix output [] =
      .ok (output, suffix) := by
    simp [Eval.dropUniqueWork]
  simpa using dropUniqueWork_append run emptyRun

/-- Single-value wrapper of `dropUniqueWork_add_suffix`. -/
theorem dropUnique_add_suffix {localFuel suffix : Nat}
    {store output : Eval.Store} {value : RVal}
    (run : Eval.dropUnique localFuel store value = .ok (output, 0)) :
    Eval.dropUnique (localFuel + suffix) store value =
      .ok (output, suffix) := by
  exact dropUniqueWork_add_suffix run

/-- At a fixed IxIR₁ recursive fuel, successful shared release of one value
has an exact-store IxIR₂ work-list execution.  Positivity is both the one
extra source premise and a preserved output fact. -/
def SharedValSimAt (context : IxIR1.Ctx) (fuel : Nat) : Prop :=
  ∀ {sourceStore : IxIR1.Store} {targetStore : Eval.Store}
    {value : RVal} {sourceOut : IxIR1.Store},
    PositiveSharedRC sourceStore →
    StoreRel sourceStore targetStore →
    IxIR1.dropVal context fuel sourceStore value = .ok sourceOut →
    ∃ targetFuel targetOut,
      Eval.releaseSharedWork targetFuel targetStore [value] =
          .ok (targetOut, 0) ∧
        StoreRel sourceOut targetOut ∧
        PositiveSharedRC sourceOut

/-- The list half of the mutually recursive shared-release correspondence. -/
def SharedManySimAt (context : IxIR1.Ctx) (fuel : Nat) : Prop :=
  ∀ {sourceStore : IxIR1.Store} {targetStore : Eval.Store}
    {values : List RVal} {sourceOut : IxIR1.Store},
    PositiveSharedRC sourceStore →
    StoreRel sourceStore targetStore →
    IxIR1.dropMany context fuel sourceStore values = .ok sourceOut →
    ∃ targetFuel targetOut,
      Eval.releaseSharedWork targetFuel targetStore values =
          .ok (targetOut, 0) ∧
        StoreRel sourceOut targetOut ∧
        PositiveSharedRC sourceOut

/-- Successful recursive IxIR₁ shared destruction is simulated by the flat
IxIR₂ work list.  The positivity premise excludes exactly IxIR₁'s legacy
zero-refcount decrement case; target fuel remains independently existential. -/
theorem sharedReleaseWork_simulation (context : IxIR1.Ctx) :
    ∀ fuel, SharedValSimAt context fuel ∧ SharedManySimAt context fuel := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · unfold SharedValSimAt
        intro sourceStore targetStore value sourceOut positive stores sourceRun
        simp [IxIR1.dropVal] at sourceRun
      · unfold SharedManySimAt
        intro sourceStore targetStore values sourceOut positive stores sourceRun
        simp [IxIR1.dropMany] at sourceRun
  | succ fuel ih =>
      have valueIH : SharedValSimAt context fuel := ih.1
      have manyIH : SharedManySimAt context fuel := ih.2
      unfold SharedValSimAt at valueIH
      unfold SharedManySimAt at manyIH
      constructor
      · unfold SharedValSimAt
        intro sourceStore targetStore value sourceOut positive stores sourceRun
        cases value with
        | lit literal =>
            simp only [IxIR1.dropVal] at sourceRun
            cases sourceRun
            refine ⟨1, targetStore, ?_, stores, positive⟩
            simp [Eval.releaseSharedWork]
        | erased =>
            simp only [IxIR1.dropVal] at sourceRun
            cases sourceRun
            refine ⟨1, targetStore, ?_, stores, positive⟩
            simp [Eval.releaseSharedWork]
        | loc location =>
            rw [IxIR1.dropVal.eq_def] at sourceRun
            dsimp only at sourceRun
            cases sourceGet : sourceStore.get? location with
            | none => simp [sourceGet] at sourceRun
            | some box =>
                cases world : box.world with
                | unique => simp [sourceGet, world] at sourceRun
                | shared =>
                    have targetGet :
                        targetStore.get? location = some box := by
                      unfold Eval.Store.get?
                      rw [stores.heap]
                      exact sourceGet
                    have countPositive : 0 < box.rc :=
                      positive sourceGet world
                    have nonzero : box.rc ≠ 0 := by omega
                    have tickGet :
                        sourceStore.rcTick.get? location = some box := by
                      simpa [IxIR1.Store.rcTick, IxIR1.Store.get?]
                        using sourceGet
                    by_cases unit : box.rc = 1
                    · cases node : box.node with
                      | ctorN cid fields =>
                          have childRun :
                              IxIR1.dropMany context fuel
                                  (sourceStore.rcTick.kill location)
                                  fields.toList = .ok sourceOut := by
                            simpa [sourceGet, world, unit, node]
                              using sourceRun
                          have prefixPositive :
                              PositiveSharedRC
                                (sourceStore.rcTick.kill location) :=
                            PositiveSharedRC.kill
                              (PositiveSharedRC.rcTick positive) tickGet
                          obtain ⟨targetFuel, targetOut, targetRun,
                              outputStores, outputPositive⟩ :=
                            manyIH prefixPositive
                              ((stores.rcTick).kill location) childRun
                          refine ⟨targetFuel + 1, targetOut, ?_,
                            outputStores, outputPositive⟩
                          simpa [Eval.releaseSharedWork, targetGet, world,
                            nonzero, unit, node] using targetRun
                      | papN address arity arguments =>
                          have childRun :
                              IxIR1.dropMany context fuel
                                  (sourceStore.rcTick.kill location)
                                  arguments.toList = .ok sourceOut := by
                            simpa [sourceGet, world, unit, node]
                              using sourceRun
                          have prefixPositive :
                              PositiveSharedRC
                                (sourceStore.rcTick.kill location) :=
                            PositiveSharedRC.kill
                              (PositiveSharedRC.rcTick positive) tickGet
                          obtain ⟨targetFuel, targetOut, targetRun,
                              outputStores, outputPositive⟩ :=
                            manyIH prefixPositive
                              ((stores.rcTick).kill location) childRun
                          refine ⟨targetFuel + 1, targetOut, ?_,
                            outputStores, outputPositive⟩
                          simpa [Eval.releaseSharedWork, targetGet, world,
                            nonzero, unit, node] using targetRun
                    · have unitTest : (box.rc == 1) = false := by
                        simp [unit]
                      have directRun :
                          (.ok (sourceStore.rcTick.setBox location
                            { box with rc := box.rc - 1 }) :
                              Except IxIR1.Err IxIR1.Store) =
                            .ok sourceOut := by
                        simpa [sourceGet, world, unitTest] using sourceRun
                      injection directRun with outputEqual
                      subst sourceOut
                      have decrementedPositive : 0 < box.rc - 1 := by omega
                      have outputPositive :
                          PositiveSharedRC
                            (sourceStore.rcTick.setBox location
                              { box with rc := box.rc - 1 }) :=
                        PositiveSharedRC.setRc
                          (PositiveSharedRC.rcTick positive) tickGet
                          decrementedPositive
                      refine ⟨1,
                        targetStore.rcTick.setBox location
                          { box with rc := box.rc - 1 }, ?_,
                        (stores.rcTick).setBox location
                          { box with rc := box.rc - 1 }, outputPositive⟩
                      simp [Eval.releaseSharedWork, targetGet, world,
                        nonzero, unit]
      · unfold SharedManySimAt
        intro sourceStore targetStore values sourceOut positive stores sourceRun
        cases values with
        | nil =>
            simp only [IxIR1.dropMany] at sourceRun
            cases sourceRun
            refine ⟨0, targetStore, ?_, stores, positive⟩
            simp [Eval.releaseSharedWork]
        | cons value values =>
            rw [IxIR1.dropMany.eq_def] at sourceRun
            dsimp only at sourceRun
            cases valueRun : IxIR1.dropVal context fuel sourceStore value with
            | error error =>
                simp [valueRun, bind, Except.bind] at sourceRun
            | ok middleStore =>
                simp only [valueRun, bind, Except.bind] at sourceRun
                obtain ⟨valueFuel, targetMiddle, targetValueRun,
                    middleStores, middlePositive⟩ :=
                  valueIH positive stores valueRun
                obtain ⟨valuesFuel, targetOut, targetValuesRun,
                    outputStores, outputPositive⟩ :=
                  manyIH middlePositive middleStores sourceRun
                refine ⟨valueFuel + valuesFuel, targetOut, ?_,
                  outputStores, outputPositive⟩
                simpa using
                  (releaseSharedWork_append targetValueRun targetValuesRun)

/-- Public value projection of the mutual recursive shared-release theorem. -/
theorem dropVal_simulates_releaseSharedWork {context : IxIR1.Ctx}
    {fuel : Nat} {sourceStore : IxIR1.Store} {targetStore : Eval.Store}
    {value : RVal} {sourceOut : IxIR1.Store}
    (positive : PositiveSharedRC sourceStore)
    (stores : StoreRel sourceStore targetStore)
    (sourceRun : IxIR1.dropVal context fuel sourceStore value = .ok sourceOut) :
    ∃ targetFuel targetOut,
      Eval.releaseSharedWork targetFuel targetStore [value] =
          .ok (targetOut, 0) ∧
        StoreRel sourceOut targetOut ∧
        PositiveSharedRC sourceOut :=
  (sharedReleaseWork_simulation context fuel).1 positive stores sourceRun

/-- Public list projection of the mutual recursive shared-release theorem. -/
theorem dropMany_simulates_releaseSharedWork {context : IxIR1.Ctx}
    {fuel : Nat} {sourceStore : IxIR1.Store} {targetStore : Eval.Store}
    {values : List RVal} {sourceOut : IxIR1.Store}
    (positive : PositiveSharedRC sourceStore)
    (stores : StoreRel sourceStore targetStore)
    (sourceRun :
      IxIR1.dropMany context fuel sourceStore values = .ok sourceOut) :
    ∃ targetFuel targetOut,
      Eval.releaseSharedWork targetFuel targetStore values =
          .ok (targetOut, 0) ∧
        StoreRel sourceOut targetOut ∧
        PositiveSharedRC sourceOut :=
  (sharedReleaseWork_simulation context fuel).2 positive stores sourceRun

/-- At a fixed IxIR₁ recursive fuel, one successful unique-value drop has an
exact-store IxIR₂ work-list execution with some exact target budget. -/
def UniqueValSimAt (context : IxIR1.Ctx) (fuel : Nat) : Prop :=
  ∀ {sourceStore : IxIR1.Store} {targetStore : Eval.Store}
    {value : RVal} {sourceOut : IxIR1.Store},
    StoreRel sourceStore targetStore →
    IxIR1.dropUVal context fuel sourceStore value = .ok sourceOut →
    ∃ targetFuel targetOut,
      Eval.dropUniqueWork targetFuel targetStore [value] =
          .ok (targetOut, 0) ∧
        StoreRel sourceOut targetOut

/-- The list half of the mutually recursive unique-drop correspondence. -/
def UniqueManySimAt (context : IxIR1.Ctx) (fuel : Nat) : Prop :=
  ∀ {sourceStore : IxIR1.Store} {targetStore : Eval.Store}
    {values : List RVal} {sourceOut : IxIR1.Store},
    StoreRel sourceStore targetStore →
    IxIR1.dropManyU context fuel sourceStore values = .ok sourceOut →
    ∃ targetFuel targetOut,
      Eval.dropUniqueWork targetFuel targetStore values =
          .ok (targetOut, 0) ∧
        StoreRel sourceOut targetOut

/-- Successful recursive IxIR₁ unique destruction is simulated by the flat
IxIR₂ work list.  Target fuel is existential because the source budgets tree
depth/list recursion while the target counts visited runtime values. -/
theorem uniqueDropWork_simulation (context : IxIR1.Ctx) :
    ∀ fuel, UniqueValSimAt context fuel ∧ UniqueManySimAt context fuel := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · unfold UniqueValSimAt
        intro sourceStore targetStore value sourceOut stores sourceRun
        simp [IxIR1.dropUVal] at sourceRun
      · unfold UniqueManySimAt
        intro sourceStore targetStore values sourceOut stores sourceRun
        simp [IxIR1.dropManyU] at sourceRun
  | succ fuel ih =>
      have valueIH : UniqueValSimAt context fuel := ih.1
      have manyIH : UniqueManySimAt context fuel := ih.2
      unfold UniqueValSimAt at valueIH
      unfold UniqueManySimAt at manyIH
      constructor
      · unfold UniqueValSimAt
        intro sourceStore targetStore value sourceOut stores sourceRun
        cases value with
        | lit literal =>
            simp only [IxIR1.dropUVal] at sourceRun
            cases sourceRun
            refine ⟨1, targetStore, ?_, stores⟩
            simp [Eval.dropUniqueWork]
        | erased =>
            simp only [IxIR1.dropUVal] at sourceRun
            cases sourceRun
            refine ⟨1, targetStore, ?_, stores⟩
            simp [Eval.dropUniqueWork]
        | loc location =>
            rw [IxIR1.dropUVal.eq_def] at sourceRun
            dsimp only at sourceRun
            cases sourceGet : sourceStore.get? location with
            | none => simp [sourceGet] at sourceRun
            | some box =>
                cases world : box.world with
                | shared => simp [sourceGet, world] at sourceRun
                | unique =>
                    cases node : box.node with
                    | papN address arity arguments =>
                        simp [sourceGet, world, node] at sourceRun
                    | ctorN cid fields =>
                        simp only [sourceGet, world, node] at sourceRun
                        have targetGet :
                            targetStore.get? location = some box := by
                          unfold Eval.Store.get?
                          rw [stores.heap]
                          exact sourceGet
                        obtain ⟨targetFuel, targetOut, targetRun, outputStores⟩ :=
                          manyIH (stores.kill location) sourceRun
                        refine ⟨targetFuel + 1, targetOut, ?_, outputStores⟩
                        simpa [Eval.dropUniqueWork, targetGet, world, node]
                          using targetRun
      · unfold UniqueManySimAt
        intro sourceStore targetStore values sourceOut stores sourceRun
        cases values with
        | nil =>
            simp only [IxIR1.dropManyU] at sourceRun
            cases sourceRun
            refine ⟨0, targetStore, ?_, stores⟩
            simp [Eval.dropUniqueWork]
        | cons value values =>
            rw [IxIR1.dropManyU.eq_def] at sourceRun
            dsimp only at sourceRun
            cases valueRun : IxIR1.dropUVal context fuel sourceStore value with
            | error error =>
                simp [valueRun, bind, Except.bind] at sourceRun
            | ok middleStore =>
                simp only [valueRun, bind, Except.bind] at sourceRun
                obtain ⟨valueFuel, targetMiddle, targetValueRun,
                    middleStores⟩ := valueIH stores valueRun
                obtain ⟨valuesFuel, targetOut, targetValuesRun,
                    outputStores⟩ := manyIH middleStores sourceRun
                refine ⟨valueFuel + valuesFuel, targetOut, ?_, outputStores⟩
                simpa using
                  (dropUniqueWork_append targetValueRun targetValuesRun)

/-- Public value projection of the mutual recursive unique-drop theorem. -/
theorem dropUVal_simulates_dropUniqueWork {context : IxIR1.Ctx}
    {fuel : Nat} {sourceStore : IxIR1.Store} {targetStore : Eval.Store}
    {value : RVal} {sourceOut : IxIR1.Store}
    (stores : StoreRel sourceStore targetStore)
    (sourceRun :
      IxIR1.dropUVal context fuel sourceStore value = .ok sourceOut) :
    ∃ targetFuel targetOut,
      Eval.dropUniqueWork targetFuel targetStore [value] =
          .ok (targetOut, 0) ∧
        StoreRel sourceOut targetOut :=
  (uniqueDropWork_simulation context fuel).1 stores sourceRun

/-- Public list projection of the mutual recursive unique-drop theorem. -/
theorem dropManyU_simulates_dropUniqueWork {context : IxIR1.Ctx}
    {fuel : Nat} {sourceStore : IxIR1.Store} {targetStore : Eval.Store}
    {values : List RVal} {sourceOut : IxIR1.Store}
    (stores : StoreRel sourceStore targetStore)
    (sourceRun :
      IxIR1.dropManyU context fuel sourceStore values = .ok sourceOut) :
    ∃ targetFuel targetOut,
      Eval.dropUniqueWork targetFuel targetStore values =
          .ok (targetOut, 0) ∧
        StoreRel sourceOut targetOut :=
  (uniqueDropWork_simulation context fuel).2 stores sourceRun

/-- The scalar branch of IxIR₁ `dup` and IxIR₂ `retainShared` is an
identical store-preserving step. -/
theorem simulate_dup_retain_scalar {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (scalar : Eval.RVal.isScalar value = true)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .retainShared targetAtom) :
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.dup sourceAtom) = .ok (sourceStore, value) ∧
      Eval.Step context interpretation machine
        { machine with
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push value }
            stack } ∧
      StoreRel sourceStore machine.store ∧
      EnvRel (value :: source) (frame.values.push value)
        (#[some (.reg frame.values.size)] ++ mapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok value :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetStep := Eval.Step.retainShared (context := context)
    (interpretation := interpretation) control blockAt pc instruction
    targetResolved (retainShared_of_scalar scalar)
  refine ⟨?_, targetStep, stores, environments.bindValue value⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  cases value with
  | loc location => simp [Eval.RVal.isScalar] at scalar
  | lit literal => rfl
  | erased => rfl

/-- The heap-bearing branch increments the same shared node and RC counter in
both exact stores before binding the retained location. -/
theorem simulate_dup_retain_shared {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {location : Nat} {box : IxIR1.NodeBox}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .retainShared targetAtom) :
    let nextBox := { box with rc := box.rc + 1 }
    let sourceStore' := (sourceStore.setBox location nextBox).rcTick
    let targetStore' := (machine.store.setBox location nextBox).rcTick
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.dup sourceAtom) = .ok (sourceStore', .loc location) ∧
      Eval.Step context interpretation machine
        { machine with
          store := targetStore'
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push (.loc location) }
            stack } ∧
      StoreRel sourceStore' targetStore' ∧
      EnvRel (.loc location :: source)
        (frame.values.push (.loc location))
        (#[some (.reg frame.values.size)] ++ mapping) := by
  dsimp only
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok (.loc location) :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetGet : machine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have retained :
      Eval.retainShared machine.store (.loc location) =
        .ok ((machine.store.setBox location
          { box with rc := box.rc + 1 }).rcTick) := by
    unfold Eval.retainShared
    simp only
    rw [targetGet]
    simp only
    rw [shared]
    rfl
  have targetStep := Eval.Step.retainShared (context := context)
    (interpretation := interpretation) control blockAt pc instruction
    targetResolved retained
  refine ⟨?_, targetStep,
    (stores.setBox location { box with rc := box.rc + 1 }).rcTick,
    environments.bindValue (.loc location)⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  simp only [bind, Except.bind]
  rw [sourceGet]
  simp only
  rw [shared]

/-- Trace-facing scalar retain transition. -/
theorem simulate_traced_dup_retain_scalar_state {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.dup sourceAtom) index (.retainShared targetAtom) next))
    {sourceStore : IxIR1.Store} {source : List RVal} {value : RVal}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.dup sourceAtom) index (.retainShared targetAtom) next) source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (scalar : Eval.RVal.isScalar value = true)
    (control : machine.control = .running frame stack) :
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push value }
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.dup sourceAtom) = .ok (sourceStore, value) ∧
      Eval.Step context interpretation machine
        { machine with control := .running nextFrame stack } ∧
      StoreRel sourceStore machine.store ∧
      CodeStateRel functionTrace next (value :: source) nextFrame := by
  dsimp only
  have translated : translateAtom input sourceAtom = some targetAtom := by
    simpa [Lower.OperationSyntax] using
      functionTrace.descendantOperationSyntax descendant
  obtain ⟨blockAt, pcBound, instructionAt⟩ := state.instructionAt descendant
  have instruction :
      next.headBlock.2.instructions[frame.pc] = .retainShared targetAtom :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  obtain ⟨sourceRun, targetStep, nextStores, canonical⟩ :=
    simulate_dup_retain_scalar stores state.environments translated
      sourceResolved scalar control blockAt pcBound instruction
  have nextEnvironments := canonical.forgetTracedValue state descendant
    (show Lower.Instr.baselineBinderAtom entryValueCount
      (.retainShared targetAtom) = some (.reg entryValueCount) by rfl)
  refine ⟨sourceRun, targetStep, nextStores,
    state.letOpNext descendant rfl rfl rfl ?_ rfl nextEnvironments⟩
  simp [Lower.Instr.baselineValueDelta]

/-- Trace-facing heap-bearing shared retain transition. -/
theorem simulate_traced_dup_retain_shared_state {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.dup sourceAtom) index (.retainShared targetAtom) next))
    {sourceStore : IxIR1.Store} {source : List RVal}
    {location : Nat} {box : IxIR1.NodeBox}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.dup sourceAtom) index (.retainShared targetAtom) next) source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (control : machine.control = .running frame stack) :
    let nextBox := { box with rc := box.rc + 1 }
    let sourceStore' := (sourceStore.setBox location nextBox).rcTick
    let targetStore' := (machine.store.setBox location nextBox).rcTick
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push (.loc location) }
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.dup sourceAtom) = .ok (sourceStore', .loc location) ∧
      Eval.Step context interpretation machine
        { machine with
          store := targetStore'
          control := .running nextFrame stack } ∧
      StoreRel sourceStore' targetStore' ∧
      CodeStateRel functionTrace next (.loc location :: source) nextFrame := by
  dsimp only
  have translated : translateAtom input sourceAtom = some targetAtom := by
    simpa [Lower.OperationSyntax] using
      functionTrace.descendantOperationSyntax descendant
  obtain ⟨blockAt, pcBound, instructionAt⟩ := state.instructionAt descendant
  have instruction :
      next.headBlock.2.instructions[frame.pc] = .retainShared targetAtom :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  obtain ⟨sourceRun, targetStep, nextStores, canonical⟩ :=
    simulate_dup_retain_shared stores state.environments translated
      sourceResolved sourceGet shared control blockAt pcBound instruction
  have nextEnvironments := canonical.forgetTracedValue state descendant
    (show Lower.Instr.baselineBinderAtom entryValueCount
      (.retainShared targetAtom) = some (.reg entryValueCount) by rfl)
  refine ⟨sourceRun, targetStep, nextStores,
    state.letOpNext descendant rfl rfl rfl ?_ rfl nextEnvironments⟩
  simp [Lower.Instr.baselineValueDelta]

/-- A scalar IxIR₁ shared drop and its effect-only IxIR₂ release leave the
exact store and runtime environments unchanged.  The target accounts for the
single scalar work-list visit in its independent heap budget. -/
theorem simulate_drop_release_scalar {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel targetHeapFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (scalar : Eval.RVal.isScalar value = true)
    (heapFuel : machine.heapFuel = targetHeapFuel + 1)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .releaseShared targetAtom) :
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.drop sourceAtom) = .ok (sourceStore, .erased) ∧
      Eval.Step context interpretation machine
        { store := machine.store
          heapFuel := targetHeapFuel
          control := .running { frame with pc := frame.pc + 1 } stack } ∧
      StoreRel sourceStore machine.store ∧
      EnvRel (.erased :: source) frame.values
        (#[some .erased] ++ mapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok value :=
    resolveAtom_of_envRel environments translated sourceResolved
  have released :
      Eval.releaseShared machine.heapFuel machine.store value =
        .ok (machine.store, targetHeapFuel) := by
    rw [heapFuel]
    exact releaseShared_of_scalar targetHeapFuel scalar
  have targetStep := Eval.Step.releaseShared (context := context)
    (interpretation := interpretation) control blockAt pc instruction
    targetResolved released
  refine ⟨?_, targetStep, stores, environments.bindErased⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  cases value with
  | loc location => simp [Eval.RVal.isScalar] at scalar
  | lit literal => rfl
  | erased => rfl

/-- A scalar IxIR₁ unique drop and its effect-only IxIR₂ counterpart preserve
the exact store while spending one target heap-traversal unit. -/
theorem simulate_dropU_dropUnique_scalar {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel targetHeapFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (scalar : Eval.RVal.isScalar value = true)
    (heapFuel : machine.heapFuel = targetHeapFuel + 1)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .dropUnique targetAtom) :
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.dropU sourceAtom) = .ok (sourceStore, .erased) ∧
      Eval.Step context interpretation machine
        { store := machine.store
          heapFuel := targetHeapFuel
          control := .running { frame with pc := frame.pc + 1 } stack } ∧
      StoreRel sourceStore machine.store ∧
      EnvRel (.erased :: source) frame.values
        (#[some .erased] ++ mapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok value :=
    resolveAtom_of_envRel environments translated sourceResolved
  have dropped :
      Eval.dropUnique machine.heapFuel machine.store value =
        .ok (machine.store, targetHeapFuel) := by
    rw [heapFuel]
    exact dropUnique_of_scalar targetHeapFuel scalar
  have targetStep := Eval.Step.dropUnique (context := context)
    (interpretation := interpretation) control blockAt pc instruction
    targetResolved dropped
  refine ⟨?_, targetStep, stores, environments.bindErased⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  cases value with
  | loc location => simp [Eval.RVal.isScalar] at scalar
  | lit literal => rfl
  | erased => rfl

/-- Trace-facing scalar shared-drop transition. -/
theorem simulate_traced_drop_release_scalar_state {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel targetHeapFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.drop sourceAtom) index (.releaseShared targetAtom) next))
    {sourceStore : IxIR1.Store} {source : List RVal} {value : RVal}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.drop sourceAtom) index (.releaseShared targetAtom) next) source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (scalar : Eval.RVal.isScalar value = true)
    (heapFuel : machine.heapFuel = targetHeapFuel + 1)
    (control : machine.control = .running frame stack) :
    let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.drop sourceAtom) = .ok (sourceStore, .erased) ∧
      Eval.Step context interpretation machine
        { store := machine.store
          heapFuel := targetHeapFuel
          control := .running nextFrame stack } ∧
      StoreRel sourceStore machine.store ∧
      CodeStateRel functionTrace next (.erased :: source) nextFrame := by
  dsimp only
  have translated : translateAtom input sourceAtom = some targetAtom := by
    simpa [Lower.OperationSyntax] using
      functionTrace.descendantOperationSyntax descendant
  obtain ⟨blockAt, pcBound, instructionAt⟩ := state.instructionAt descendant
  have instruction :
      next.headBlock.2.instructions[frame.pc] = .releaseShared targetAtom :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  obtain ⟨sourceRun, targetStep, nextStores, canonical⟩ :=
    simulate_drop_release_scalar stores state.environments translated
      sourceResolved scalar heapFuel control blockAt pcBound instruction
  have nextEnvironments := canonical.forgetTracedErased descendant
    (show Lower.Instr.baselineBinderAtom entryValueCount
      (.releaseShared targetAtom) = some .erased by rfl)
  refine ⟨sourceRun, targetStep, nextStores,
    state.letOpNext descendant rfl rfl rfl ?_ rfl nextEnvironments⟩
  simp [Lower.Instr.baselineValueDelta]

/-- Trace-facing scalar unique-drop transition. -/
theorem simulate_traced_dropU_dropUnique_scalar_state
    {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel targetHeapFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.dropU sourceAtom) index (.dropUnique targetAtom) next))
    {sourceStore : IxIR1.Store} {source : List RVal} {value : RVal}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.dropU sourceAtom) index (.dropUnique targetAtom) next) source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (scalar : Eval.RVal.isScalar value = true)
    (heapFuel : machine.heapFuel = targetHeapFuel + 1)
    (control : machine.control = .running frame stack) :
    let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.dropU sourceAtom) = .ok (sourceStore, .erased) ∧
      Eval.Step context interpretation machine
        { store := machine.store
          heapFuel := targetHeapFuel
          control := .running nextFrame stack } ∧
      StoreRel sourceStore machine.store ∧
      CodeStateRel functionTrace next (.erased :: source) nextFrame := by
  dsimp only
  have translated : translateAtom input sourceAtom = some targetAtom := by
    simpa [Lower.OperationSyntax] using
      functionTrace.descendantOperationSyntax descendant
  obtain ⟨blockAt, pcBound, instructionAt⟩ := state.instructionAt descendant
  have instruction :
      next.headBlock.2.instructions[frame.pc] = .dropUnique targetAtom :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  obtain ⟨sourceRun, targetStep, nextStores, canonical⟩ :=
    simulate_dropU_dropUnique_scalar stores state.environments translated
      sourceResolved scalar heapFuel control blockAt pcBound instruction
  have nextEnvironments := canonical.forgetTracedErased descendant
    (show Lower.Instr.baselineBinderAtom entryValueCount
      (.dropUnique targetAtom) = some .erased by rfl)
  refine ⟨sourceRun, targetStep, nextStores,
    state.letOpNext descendant rfl rfl rfl ?_ rfl nextEnvironments⟩
  simp [Lower.Instr.baselineValueDelta]

/-- Every successful recursive IxIR₁ unique-location drop has a sufficient
IxIR₂ heap budget that drives one effect-only `dropUnique` step to the same
exact heap.  The theorem exposes the locally chosen budget explicitly; later
block composition can add slack and combine these finite witnesses. -/
theorem simulate_dropU_dropUnique_recursive
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore sourceStore' : IxIR1.Store} {source : List RVal}
    {mapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {location : Nat}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceDropped :
      IxIR1.dropUVal sourceContext sourceFuel sourceStore (.loc location) =
        .ok sourceStore')
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .dropUnique targetAtom) :
    ∃ targetHeapFuel targetStore,
      IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
            source (.dropU sourceAtom) = .ok (sourceStore', .erased) ∧
        Eval.Step context interpretation
          { machine with heapFuel := targetHeapFuel }
          { store := targetStore
            heapFuel := 0
            control := .running { frame with pc := frame.pc + 1 } stack } ∧
        StoreRel sourceStore' targetStore ∧
        EnvRel (.erased :: source) frame.values
          (#[some .erased] ++ mapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok (.loc location) :=
    resolveAtom_of_envRel environments translated sourceResolved
  obtain ⟨targetHeapFuel, targetStore, targetRun, outputStores⟩ :=
    dropUVal_simulates_dropUniqueWork stores sourceDropped
  have targetDropped :
      Eval.dropUnique targetHeapFuel machine.store (.loc location) =
        .ok (targetStore, 0) := by
    simpa [Eval.dropUnique] using targetRun
  have beforeControl :
      ({ machine with heapFuel := targetHeapFuel } : Eval.Machine).control =
        .running frame stack := by
    simpa using control
  have targetStep := Eval.Step.dropUnique (context := context)
    (interpretation := interpretation) beforeControl blockAt pc instruction
    targetResolved targetDropped
  refine ⟨targetHeapFuel, targetStore, ?_, targetStep, outputStores,
    environments.bindErased⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  simp only [bind, Except.bind]
  rw [sourceDropped]

/-- Every successful recursive IxIR₁ shared-location drop from a positive-RC
heap has a sufficient IxIR₂ budget for one effect-only `releaseShared` step
to the same exact heap.  Positivity is returned for subsequent instructions. -/
theorem simulate_drop_release_recursive
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore sourceStore' : IxIR1.Store} {source : List RVal}
    {mapping : EnvMap}
    (positive : PositiveSharedRC sourceStore)
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {location : Nat}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceDropped :
      IxIR1.dropVal sourceContext sourceFuel sourceStore (.loc location) =
        .ok sourceStore')
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .releaseShared targetAtom) :
    ∃ targetHeapFuel targetStore,
      IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
            source (.drop sourceAtom) = .ok (sourceStore', .erased) ∧
        Eval.Step context interpretation
          { machine with heapFuel := targetHeapFuel }
          { store := targetStore
            heapFuel := 0
            control := .running { frame with pc := frame.pc + 1 } stack } ∧
        StoreRel sourceStore' targetStore ∧
        PositiveSharedRC sourceStore' ∧
        EnvRel (.erased :: source) frame.values
          (#[some .erased] ++ mapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok (.loc location) :=
    resolveAtom_of_envRel environments translated sourceResolved
  obtain ⟨targetHeapFuel, targetStore, targetRun, outputStores,
      outputPositive⟩ :=
    dropVal_simulates_releaseSharedWork positive stores sourceDropped
  have targetReleased :
      Eval.releaseShared targetHeapFuel machine.store (.loc location) =
        .ok (targetStore, 0) := by
    simpa [Eval.releaseShared] using targetRun
  have beforeControl :
      ({ machine with heapFuel := targetHeapFuel } : Eval.Machine).control =
        .running frame stack := by
    simpa using control
  have targetStep := Eval.Step.releaseShared (context := context)
    (interpretation := interpretation) beforeControl blockAt pc instruction
    targetResolved targetReleased
  refine ⟨targetHeapFuel, targetStore, ?_, targetStep, outputStores,
    outputPositive, environments.bindErased⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  simp only [bind, Except.bind]
  rw [sourceDropped]

/-- Trace-facing recursive unique drop. A successful source recursive drop
selects a sufficient target heap budget, while the trace supplies all target
syntax and the exact continuation state. -/
theorem simulate_traced_dropU_dropUnique_recursive_state
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.dropU sourceAtom) index (.dropUnique targetAtom) next))
    {sourceStore sourceStore' : IxIR1.Store} {source : List RVal}
    {location : Nat}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.dropU sourceAtom) index (.dropUnique targetAtom) next) source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceDropped :
      IxIR1.dropUVal sourceContext sourceFuel sourceStore (.loc location) =
        .ok sourceStore')
    (control : machine.control = .running frame stack) :
    ∃ targetHeapFuel targetStore,
      let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
      IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
            source (.dropU sourceAtom) = .ok (sourceStore', .erased) ∧
        Eval.Step context interpretation
          { machine with heapFuel := targetHeapFuel }
          { store := targetStore
            heapFuel := 0
            control := .running nextFrame stack } ∧
        StoreRel sourceStore' targetStore ∧
        CodeStateRel functionTrace next (.erased :: source) nextFrame := by
  have translated : translateAtom input sourceAtom = some targetAtom := by
    simpa [Lower.OperationSyntax] using
      functionTrace.descendantOperationSyntax descendant
  obtain ⟨blockAt, pcBound, instructionAt⟩ := state.instructionAt descendant
  have instruction :
      next.headBlock.2.instructions[frame.pc] = .dropUnique targetAtom :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  obtain ⟨targetHeapFuel, targetStore, sourceRun, targetStep,
      nextStores, canonical⟩ :=
    simulate_dropU_dropUnique_recursive stores state.environments translated
      sourceResolved sourceDropped control blockAt pcBound instruction
  refine ⟨targetHeapFuel, targetStore, ?_⟩
  dsimp only
  have nextEnvironments := canonical.forgetTracedErased descendant
    (show Lower.Instr.baselineBinderAtom entryValueCount
      (.dropUnique targetAtom) = some .erased by rfl)
  refine ⟨sourceRun, targetStep, nextStores,
    state.letOpNext descendant rfl rfl rfl ?_ rfl nextEnvironments⟩
  simp [Lower.Instr.baselineValueDelta]

/-- Trace-facing recursive shared drop, including preservation of the source
positive-reference-count invariant needed by subsequent recursive releases. -/
theorem simulate_traced_drop_release_recursive_state
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.drop sourceAtom) index (.releaseShared targetAtom) next))
    {sourceStore sourceStore' : IxIR1.Store} {source : List RVal}
    {location : Nat}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.drop sourceAtom) index (.releaseShared targetAtom) next) source frame)
    (positive : PositiveSharedRC sourceStore)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceDropped :
      IxIR1.dropVal sourceContext sourceFuel sourceStore (.loc location) =
        .ok sourceStore')
    (control : machine.control = .running frame stack) :
    ∃ targetHeapFuel targetStore,
      let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
      IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
            source (.drop sourceAtom) = .ok (sourceStore', .erased) ∧
        Eval.Step context interpretation
          { machine with heapFuel := targetHeapFuel }
          { store := targetStore
            heapFuel := 0
            control := .running nextFrame stack } ∧
        StoreRel sourceStore' targetStore ∧
        PositiveSharedRC sourceStore' ∧
        CodeStateRel functionTrace next (.erased :: source) nextFrame := by
  have translated : translateAtom input sourceAtom = some targetAtom := by
    simpa [Lower.OperationSyntax] using
      functionTrace.descendantOperationSyntax descendant
  obtain ⟨blockAt, pcBound, instructionAt⟩ := state.instructionAt descendant
  have instruction :
      next.headBlock.2.instructions[frame.pc] = .releaseShared targetAtom :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  obtain ⟨targetHeapFuel, targetStore, sourceRun, targetStep,
      nextStores, nextPositive, canonical⟩ :=
    simulate_drop_release_recursive positive stores state.environments
      translated sourceResolved sourceDropped control blockAt pcBound instruction
  refine ⟨targetHeapFuel, targetStore, ?_⟩
  dsimp only
  have nextEnvironments := canonical.forgetTracedErased descendant
    (show Lower.Instr.baselineBinderAtom entryValueCount
      (.releaseShared targetAtom) = some .erased by rfl)
  refine ⟨sourceRun, targetStep, nextStores, nextPositive,
    state.letOpNext descendant rfl rfl rfl ?_ rfl nextEnvironments⟩
  simp [Lower.Instr.baselineValueDelta]

/-- Releasing a shared node with more than one owner decrements the same
refcount and charges the same RC operation in both exact stores.  This is the
non-recursive heap-bearing branch of deep shared release. -/
theorem simulate_drop_release_shared_nonunit {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef}
    {sourceDropFuel targetHeapFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {location : Nat} {box : IxIR1.NodeBox}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (nonzero : box.rc ≠ 0)
    (nonunit : box.rc ≠ 1)
    (heapFuel : machine.heapFuel = targetHeapFuel + 1)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .releaseShared targetAtom) :
    let nextBox := { box with rc := box.rc - 1 }
    let sourceStore' := sourceStore.rcTick.setBox location nextBox
    let targetStore' := machine.store.rcTick.setBox location nextBox
    IxIR1.runOp sourceContext ((sourceDropFuel + 1) + 1) sourceCurrent
          sourceStore source (.drop sourceAtom) =
        .ok (sourceStore', .erased) ∧
      Eval.Step context interpretation machine
        { store := targetStore'
          heapFuel := targetHeapFuel
          control := .running { frame with pc := frame.pc + 1 } stack } ∧
      StoreRel sourceStore' targetStore' ∧
      EnvRel (.erased :: source) frame.values
        (#[some .erased] ++ mapping) := by
  dsimp only
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok (.loc location) :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetGet : machine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have released :
      Eval.releaseShared machine.heapFuel machine.store (.loc location) =
        .ok (machine.store.rcTick.setBox location
          { box with rc := box.rc - 1 }, targetHeapFuel) := by
    rw [heapFuel]
    simp [Eval.releaseShared, Eval.releaseSharedWork, targetGet, shared,
      nonzero, nonunit]
  have targetStep := Eval.Step.releaseShared (context := context)
    (interpretation := interpretation) control blockAt pc instruction
    targetResolved released
  refine ⟨?_, targetStep, (stores.rcTick).setBox location
    { box with rc := box.rc - 1 }, environments.bindErased⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  simp only [bind, Except.bind]
  rw [IxIR1.dropVal.eq_def]
  simp only
  rw [sourceGet]
  simp [shared, nonunit]

/-- Deep-dropping a unique constructor whose children are all scalar kills the
same node in both stores.  IxIR₂ spends one heap unit on the constructor plus
one per field; IxIR₁ additionally needs fuel to inspect the empty list tail. -/
theorem simulate_dropU_dropUnique_scalar_ctor
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {targetHeapFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {cid : IxIR1.CtorId} {location : Nat}
    {box : IxIR1.NodeBox} {fields : Array RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (unique : box.world = .unique)
    (node : box.node = .ctorN cid fields)
    (scalarFields : fields.toList.all Eval.RVal.isScalar = true)
    (heapFuel : machine.heapFuel =
      (targetHeapFuel + fields.toList.length) + 1)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .dropUnique targetAtom) :
    IxIR1.runOp sourceContext ((fields.toList.length + 2) + 1)
          sourceCurrent sourceStore source (.dropU sourceAtom) =
        .ok (sourceStore.kill location, .erased) ∧
      Eval.Step context interpretation machine
        { store := machine.store.kill location
          heapFuel := targetHeapFuel
          control := .running { frame with pc := frame.pc + 1 } stack } ∧
      StoreRel (sourceStore.kill location)
        (machine.store.kill location) ∧
      EnvRel (.erased :: source) frame.values
        (#[some .erased] ++ mapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok (.loc location) :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetGet : machine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have sourceDropped :
      IxIR1.dropUVal sourceContext (fields.toList.length + 2) sourceStore
          (.loc location) = .ok (sourceStore.kill location) := by
    rw [IxIR1.dropUVal.eq_def]
    simp only
    rw [sourceGet]
    simp only
    rw [unique, node]
    exact sourceDropManyU_of_scalars scalarFields
  have targetDropped :
      Eval.dropUnique machine.heapFuel machine.store (.loc location) =
        .ok (machine.store.kill location, targetHeapFuel) := by
    rw [heapFuel]
    unfold Eval.dropUnique
    simp only [Eval.dropUniqueWork]
    rw [targetGet]
    simp only
    rw [unique, node]
    simpa using (dropUniqueWork_of_scalars
      (store := machine.store.kill location) targetHeapFuel scalarFields)
  have targetStep := Eval.Step.dropUnique (context := context)
    (interpretation := interpretation) control blockAt pc instruction
    targetResolved targetDropped
  refine ⟨?_, targetStep, stores.kill location,
    environments.bindErased⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  simp only [bind, Except.bind]
  rw [sourceDropped]

/-- Releasing the final owner of an all-scalar shared constructor charges one
RC operation, kills that constructor, and traverses only inert scalar fields
in both machines. -/
theorem simulate_drop_release_shared_unit_scalar_ctor
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {targetHeapFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {cid : IxIR1.CtorId} {location : Nat}
    {box : IxIR1.NodeBox} {fields : Array RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (unit : box.rc = 1)
    (node : box.node = .ctorN cid fields)
    (scalarFields : fields.toList.all Eval.RVal.isScalar = true)
    (heapFuel : machine.heapFuel =
      (targetHeapFuel + fields.toList.length) + 1)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .releaseShared targetAtom) :
    IxIR1.runOp sourceContext ((fields.toList.length + 2) + 1)
          sourceCurrent sourceStore source (.drop sourceAtom) =
        .ok (sourceStore.rcTick.kill location, .erased) ∧
      Eval.Step context interpretation machine
        { store := machine.store.rcTick.kill location
          heapFuel := targetHeapFuel
          control := .running { frame with pc := frame.pc + 1 } stack } ∧
      StoreRel (sourceStore.rcTick.kill location)
        (machine.store.rcTick.kill location) ∧
      EnvRel (.erased :: source) frame.values
        (#[some .erased] ++ mapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok (.loc location) :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetGet : machine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have sourceDropped :
      IxIR1.dropVal sourceContext (fields.toList.length + 2) sourceStore
          (.loc location) =
        .ok (sourceStore.rcTick.kill location) := by
    rw [IxIR1.dropVal.eq_def]
    simp only
    rw [sourceGet]
    simp only
    rw [shared, unit, node]
    exact sourceDropMany_of_scalars scalarFields
  have targetReleased :
      Eval.releaseShared machine.heapFuel machine.store (.loc location) =
        .ok (machine.store.rcTick.kill location, targetHeapFuel) := by
    rw [heapFuel]
    unfold Eval.releaseShared
    simp only [Eval.releaseSharedWork]
    rw [targetGet]
    simp only
    rw [shared, unit, node]
    simpa using (releaseSharedWork_of_scalars
      (store := machine.store.rcTick.kill location) targetHeapFuel scalarFields)
  have targetStep := Eval.Step.releaseShared (context := context)
    (interpretation := interpretation) control blockAt pc instruction
    targetResolved targetReleased
  refine ⟨?_, targetStep, (stores.rcTick).kill location,
    environments.bindErased⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  simp only [bind, Except.bind]
  rw [sourceDropped]

/-- A checked scalar-leaf IxIR₁ free and IxIR₂ `freeUnique` kill the same
unique constructor location and bind the source's erased effect result. -/
theorem simulate_free_freeUnique {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {cid : IxIR1.CtorId} {location : Nat}
    {box : IxIR1.NodeBox} {fields : Array RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (unique : box.world = .unique)
    (node : box.node = .ctorN cid fields)
    (scalarFields : fields.all Eval.RVal.isScalar = true)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .freeUnique targetAtom cid) :
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.free sourceAtom) =
        .ok (sourceStore.kill location, .erased) ∧
      Eval.Step context interpretation machine
        { machine with
          store := machine.store.kill location
          control := .running { frame with pc := frame.pc + 1 } stack } ∧
      StoreRel (sourceStore.kill location)
        (machine.store.kill location) ∧
      EnvRel (.erased :: source) frame.values
        (#[some .erased] ++ mapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok (.loc location) :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetGet : machine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have targetStep := Eval.Step.freeUnique (context := context)
    (interpretation := interpretation) control blockAt pc instruction
    targetResolved targetGet unique node scalarFields
  refine ⟨?_, targetStep, stores.kill location, environments.bindErased⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  simp only [bind, Except.bind]
  rw [sourceGet]
  simp only
  rw [unique]

/-- Trace-facing checked shallow free. The trace discharges operand and
instruction-coordinate facts while the exact constructor/scalar-leaf runtime
facts remain the owner-keyed provenance boundary. -/
theorem simulate_traced_free_freeUnique_state {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {targetCid : IxIR1.CtorId}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.free sourceAtom) index (.freeUnique targetAtom targetCid) next))
    {sourceStore : IxIR1.Store} {source : List RVal}
    {location : Nat} {box : IxIR1.NodeBox} {fields : Array RVal}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.free sourceAtom) index (.freeUnique targetAtom targetCid) next)
      source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (unique : box.world = .unique)
    (node : box.node = .ctorN targetCid fields)
    (scalarFields : fields.all Eval.RVal.isScalar = true)
    (control : machine.control = .running frame stack) :
    let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.free sourceAtom) =
        .ok (sourceStore.kill location, .erased) ∧
      Eval.Step context interpretation machine
        { machine with
          store := machine.store.kill location
          control := .running nextFrame stack } ∧
      StoreRel (sourceStore.kill location) (machine.store.kill location) ∧
      CodeStateRel functionTrace next (.erased :: source) nextFrame := by
  dsimp only
  have translated : translateAtom input sourceAtom = some targetAtom := by
    simpa [Lower.OperationSyntax] using
      functionTrace.descendantOperationSyntax descendant
  obtain ⟨blockAt, pcBound, instructionAt⟩ := state.instructionAt descendant
  have instruction :
      next.headBlock.2.instructions[frame.pc] =
        .freeUnique targetAtom targetCid :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  obtain ⟨sourceRun, targetStep, nextStores, canonical⟩ :=
    simulate_free_freeUnique stores state.environments translated
      sourceResolved sourceGet unique node scalarFields control blockAt pcBound
      instruction
  have nextEnvironments := canonical.forgetTracedErased descendant
    (show Lower.Instr.baselineBinderAtom entryValueCount
      (.freeUnique targetAtom targetCid) = some .erased by rfl)
  refine ⟨sourceRun, targetStep, nextStores,
    state.letOpNext descendant rfl rfl rfl ?_ rfl nextEnvironments⟩
  simp [Lower.Instr.baselineValueDelta]

/-- A checked IxIR₂ fetch refines the corresponding non-consuming IxIR₁
projection when the owner's exact constructor sidecar identifies the runtime
node.  Both machines keep the store unchanged and bind the same field value. -/
theorem simulate_fetch {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {cid : IxIR1.CtorId} {field location : Nat}
    {box : IxIR1.NodeBox} {fields : Array RVal} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (node : box.node = .ctorN cid fields)
    (fieldAt : fields[field]? = some value)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .fetch targetAtom cid field) :
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.fetch sourceAtom field) = .ok (sourceStore, value) ∧
      Eval.Step context interpretation machine
        { machine with
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push value }
            stack } ∧
      StoreRel sourceStore machine.store ∧
      EnvRel (value :: source) (frame.values.push value)
        (#[some (.reg frame.values.size)] ++ mapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok (.loc location) :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetGet : machine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have targetStep := Eval.Step.fetch (context := context)
    (interpretation := interpretation) control blockAt pc instruction
    targetResolved targetGet node fieldAt
  refine ⟨?_, targetStep, stores, environments.bindValue value⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  simp only [bind, Except.bind]
  rw [sourceGet]
  simp only
  rw [node]
  simp only
  rw [fieldAt]

/-- Trace-facing non-consuming projection. The checked trace supplies operand,
field, target coordinate, continuation map, and recursive-state progression;
the runtime constructor identity remains the provenance obligation. -/
theorem simulate_traced_fetch_state {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {sourceField targetField : Nat} {targetCid : IxIR1.CtorId}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
        (.fetch targetAtom targetCid targetField) next))
    {sourceStore : IxIR1.Store} {source : List RVal}
    {location : Nat} {box : IxIR1.NodeBox}
    {fields : Array RVal} {value : RVal}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
        (.fetch targetAtom targetCid targetField) next) source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (node : box.node = .ctorN targetCid fields)
    (fieldAt : fields[sourceField]? = some value)
    (control : machine.control = .running frame stack) :
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push value }
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.fetch sourceAtom sourceField) = .ok (sourceStore, value) ∧
      Eval.Step context interpretation machine
        { machine with control := .running nextFrame stack } ∧
      StoreRel sourceStore machine.store ∧
      CodeStateRel functionTrace next (value :: source) nextFrame := by
  dsimp only
  have operationSyntax := functionTrace.descendantOperationSyntax descendant
  change sourceField = targetField ∧
    Lower.InputMap.translateAtom input sourceAtom = some targetAtom at operationSyntax
  obtain ⟨fieldEq, translated⟩ := operationSyntax
  subst targetField
  obtain ⟨blockAt, pcBound, instructionAt⟩ := state.instructionAt descendant
  have instruction :
      next.headBlock.2.instructions[frame.pc] =
        .fetch targetAtom targetCid sourceField :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  obtain ⟨sourceRun, targetStep, nextStores, canonical⟩ := simulate_fetch
    stores state.environments translated sourceResolved sourceGet node fieldAt
      control blockAt pcBound instruction
  have nextEnvironments := canonical.forgetTracedValue state descendant
    (show Lower.Instr.baselineBinderAtom entryValueCount
      (.fetch targetAtom targetCid sourceField) =
        some (.reg entryValueCount) by rfl)
  refine ⟨sourceRun, targetStep, nextStores,
    state.letOpNext descendant rfl rfl rfl ?_ rfl nextEnvironments⟩
  simp [Lower.Instr.baselineValueDelta]

/-- Pointwise translation of an operand vector. Keeping this relation
separate from the executable translators makes it compose directly with
generated instruction equations. -/
inductive AtomsListRel (mapping : EnvMap) :
    List IxIR1.Atom → List Atom → Prop where
  | nil : AtomsListRel mapping [] []
  | cons : translateAtom mapping sourceAtom = some targetAtom →
      AtomsListRel mapping sourceAtoms targetAtoms →
      AtomsListRel mapping (sourceAtom :: sourceAtoms)
        (targetAtom :: targetAtoms)

def AtomsRel (mapping : EnvMap) (source : Array IxIR1.Atom)
    (target : Array Atom) : Prop :=
  AtomsListRel mapping source.toList target.toList

private theorem atomsListRel_of_mapM (mapping : EnvMap) :
    ∀ (source : List IxIR1.Atom) (target : List Atom),
      source.mapM (translateAtom mapping) = some target →
      AtomsListRel mapping source target
  | [], target, translated => by
      simp at translated
      subst target
      exact .nil
  | sourceAtom :: sourceAtoms, target, translated => by
      cases atomEq : translateAtom mapping sourceAtom with
      | none => simp [List.mapM_cons, atomEq] at translated
      | some targetAtom =>
          cases restEq : sourceAtoms.mapM (translateAtom mapping) with
          | none => simp [List.mapM_cons, atomEq, restEq] at translated
          | some targetAtoms =>
              have targetEq : target = targetAtom :: targetAtoms := by
                simpa [List.mapM_cons, atomEq, restEq] using translated.symm
              subst target
              exact .cons atomEq
                (atomsListRel_of_mapM mapping sourceAtoms targetAtoms restEq)

/-- Reflect the producer's executable vector translation into the
pointwise relation consumed by the semantic operand-resolution lemmas. -/
theorem atomsRel_of_translateAtoms {mapping : EnvMap}
    {source : Array IxIR1.Atom} {target : Array Atom}
    (translated : Lower.InputMap.translateAtoms mapping source = some target) :
    AtomsRel mapping source target := by
  unfold Lower.InputMap.translateAtoms at translated
  cases mapped : source.toList.mapM (translateAtom mapping) with
  | none => simp [mapped] at translated
  | some targetAtoms =>
      have targetEq : target = targetAtoms.toArray := by
        simpa [mapped] using translated.symm
      subst target
      unfold AtomsRel
      simpa using atomsListRel_of_mapM mapping source.toList targetAtoms mapped

private theorem except_bind_eq_ok {ε α β : Type} {input : Except ε α}
    {next : α → Except ε β} {output : β}
    (bound : input.bind next = .ok output) :
    ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input with
  | error error => cases bound
  | ok value => exact ⟨value, rfl, bound⟩

/-- Pointwise account of a successful target operand-vector resolution. -/
inductive ResolvedAtomsList (target : Array RVal) :
    List Atom → List RVal → Prop where
  | nil : ResolvedAtomsList target [] []
  | cons : Eval.resolveAtom target atom = .ok value →
      ResolvedAtomsList target atoms values →
      ResolvedAtomsList target (atom :: atoms) (value :: values)

def ResolvedAtoms (target : Array RVal) (atoms : Array Atom)
    (values : Array RVal) : Prop :=
  ResolvedAtomsList target atoms.toList values.toList

private theorem resolveFold_rel {target : Array RVal} :
    ∀ (atoms : List Atom) (accumulator output : Array RVal),
      List.foldlM
          (fun values atom => do
            return values.push (← Eval.resolveAtom target atom))
          accumulator atoms = .ok output →
      ∃ values, ResolvedAtomsList target atoms values ∧
        output = accumulator ++ values.toArray := by
  intro atoms
  induction atoms with
  | nil =>
      intro accumulator output resolved
      simp only [List.foldlM_nil] at resolved
      change Except.ok accumulator = Except.ok output at resolved
      have outputEqual : accumulator = output := Except.ok.inj resolved
      subst output
      exact ⟨[], .nil, by simp⟩
  | cons atom atoms ih =>
      intro accumulator output resolved
      simp only [List.foldlM_cons] at resolved
      obtain ⟨nextAccumulator, headResolved, tailResolved⟩ :=
        except_bind_eq_ok resolved
      obtain ⟨value, atomResolved, pushed⟩ :=
        except_bind_eq_ok headResolved
      have nextEqual : nextAccumulator = accumulator.push value := by
        simpa using Except.ok.inj pushed.symm
      subst nextAccumulator
      obtain ⟨values, valuesResolved, outputEqual⟩ :=
        ih (accumulator.push value) output tailResolved
      refine ⟨value :: values, .cons atomResolved valuesResolved, ?_⟩
      rw [outputEqual]
      apply Array.ext'
      simp

/-- `resolveAtoms` retains the exact input/output order pointwise. -/
theorem resolvedAtoms_of_resolveAtoms {target : Array RVal}
    {atoms : Array Atom} {values : Array RVal}
    (resolved : Eval.resolveAtoms target atoms = .ok values) :
    ResolvedAtoms target atoms values := by
  unfold Eval.resolveAtoms at resolved
  rw [← Array.foldlM_toList] at resolved
  obtain ⟨resolvedValues, pointwise, outputEqual⟩ :=
    resolveFold_rel atoms.toList #[] values resolved
  have valuesEqual : values = resolvedValues.toArray := by
    simpa using outputEqual
  subst values
  simpa [ResolvedAtoms] using pointwise

theorem ResolvedAtomsList.getElem? {target : Array RVal}
    {atoms : List Atom} {values : List RVal}
    (relation : ResolvedAtomsList target atoms values)
    {index : Nat} {atom : Atom} (found : atoms[index]? = some atom) :
    ∃ value, values[index]? = some value ∧
      Eval.resolveAtom target atom = .ok value := by
  induction relation generalizing index atom with
  | nil => simp at found
  | @cons headAtom headValue tailAtoms tailValues head tail ih =>
      cases index with
      | zero =>
          have atomEqual : headAtom = atom := by simpa using found
          subst atom
          exact ⟨headValue, by simp, head⟩
      | succ index =>
          obtain ⟨value, valueAt, resolved⟩ := ih (by simpa using found)
          exact ⟨value, by simpa using valueAt, resolved⟩

private def sourceResolveTargetStep (source : List IxIR1.RVal)
    (output : List IxIR1.RVal) (atom : IxIR1.Atom) :
    Except IxIR1.Err (List IxIR1.RVal) := do
  return output ++ [← IxIR1.resolveAtom source atom]

private theorem resolveSourceFold_of_envRel_target
    {source : List IxIR1.RVal} {target : Array IxIR1.RVal}
    {mapping : EnvMap} (relation : EnvRel source target mapping)
    (sourceCount : source.length = mapping.size) :
    {sourceAtoms : List IxIR1.Atom} → {targetAtoms : List Atom} →
      {values : List IxIR1.RVal} →
      AtomsListRel mapping sourceAtoms targetAtoms →
      ResolvedAtomsList target targetAtoms values →
      ∀ accumulator,
        List.foldlM (sourceResolveTargetStep source) accumulator sourceAtoms =
          (Except.ok (accumulator ++ values) :
            Except IxIR1.Err (List IxIR1.RVal)) := by
  intro sourceAtoms targetAtoms values atoms resolved
  induction atoms generalizing values with
  | nil =>
      cases resolved
      intro accumulator
      simp only [List.foldlM_nil, List.append_nil]
      rfl
  | @cons sourceAtom targetAtom sourceAtoms targetAtoms translated tail ih =>
      cases resolved with
      | @cons _ value _ values targetResolved tailResolved =>
          intro accumulator
          have sourceResolved := resolveAtom_of_envRel_target relation
            sourceCount translated targetResolved
          simp only [List.foldlM_cons]
          simp only [sourceResolveTargetStep, sourceResolved]
          change List.foldlM (sourceResolveTargetStep source)
              (accumulator ++ [value]) sourceAtoms =
            .ok (accumulator ++ (value :: values))
          simpa [List.append_assoc] using
            ih tailResolved (accumulator ++ [value])

/-- Successful resolution of a translated target operand vector reflects to
the exact source vector and preserves result order. -/
theorem resolveAtoms_of_envRel_target {source : List IxIR1.RVal}
    {target : Array IxIR1.RVal} {mapping : EnvMap}
    (relation : EnvRel source target mapping)
    (sourceCount : source.length = mapping.size)
    {sourceAtoms : Array IxIR1.Atom} {targetAtoms : Array Atom}
    (atoms : AtomsRel mapping sourceAtoms targetAtoms)
    {values : Array IxIR1.RVal}
    (resolved : Eval.resolveAtoms target targetAtoms = .ok values) :
    IxIR1.resolveAtoms source sourceAtoms = .ok values.toList := by
  have pointwise := resolvedAtoms_of_resolveAtoms resolved
  unfold IxIR1.resolveAtoms
  rw [← Array.foldlM_toList]
  change List.foldlM (sourceResolveTargetStep source) [] sourceAtoms.toList =
    .ok values.toList
  simpa using resolveSourceFold_of_envRel_target relation sourceCount atoms
    pointwise []

/-- Structural relation emitted by `edgeView`: each live source slot becomes
the same-position successor register and carries its current target operand;
dead slots impose no resolution premise. -/
def EdgeArgsRel (currentMap explicitMap : EnvMap)
    (arguments : Array Atom) : Prop :=
  ∀ (index : Nat) (successorAtom : Atom),
    explicitMap[index]? = some (some successorAtom) →
    ∃ argument,
      successorAtom = .reg index ∧
      currentMap[index]? = some (some argument) ∧
      arguments[index]? = some argument

/-- The three edge tables derived from one retained predecessor map satisfy
`EdgeArgsRel` by construction. -/
theorem EdgeArgsRel.canonical (sourceInputMap : EnvMap) :
    EdgeArgsRel sourceInputMap
      (Lower.EdgeTrace.explicitMapOf sourceInputMap)
      (Lower.EdgeTrace.explicitValuesOf sourceInputMap) := by
  intro index successorAtom mapped
  unfold Lower.EdgeTrace.explicitMapOf at mapped
  rw [Array.getElem?_mapIdx] at mapped
  cases inputAt : sourceInputMap[index]? with
  | none => simp [inputAt] at mapped
  | some slot =>
      cases slot with
      | none => simp [inputAt] at mapped
      | some argument =>
          have successorEqual : successorAtom = .reg index := by
            simpa [inputAt] using mapped.symm
          refine ⟨argument, successorEqual, rfl, ?_⟩
          unfold Lower.EdgeTrace.explicitValuesOf
          rw [Array.getElem?_map]
          simp [inputAt]

/-- Resolving a generated edge's explicit arguments converts the parent
environment relation into the successor's same-position register relation.
Consumed slots remain absent and therefore require no source lookup. -/
theorem EnvRel.of_edge_arguments {source : List RVal}
    {target values : Array RVal} {currentMap explicitMap : EnvMap}
    {arguments : Array Atom}
    (environments : EnvRel source target currentMap)
    (edgeArguments : EdgeArgsRel currentMap explicitMap arguments)
    (resolved : Eval.resolveAtoms target arguments = .ok values) :
    EnvRel source values explicitMap := by
  have pointwise := resolvedAtoms_of_resolveAtoms resolved
  intro index value successorAtom sourceAt mapped
  obtain ⟨argument, successorEqual, currentAt, argumentAt⟩ :=
    edgeArguments index successorAtom mapped
  have argumentResolved : Eval.resolveAtom target argument = .ok value :=
    environments index value argument sourceAt currentAt
  have argumentAtList : arguments.toList[index]? = some argument := by
    simpa using argumentAt
  obtain ⟨resolvedValue, valueAtList, resolvedValueEq⟩ :=
    pointwise.getElem? argumentAtList
  have resolvedValueEqual : resolvedValue = value := by
    rw [argumentResolved] at resolvedValueEq
    exact (Except.ok.inj resolvedValueEq).symm
  subst resolvedValue
  have valueAt : values[index]? = some value := by
    simpa using valueAtList
  subst successorAtom
  simp [Eval.resolveAtom, valueAt]

/-- Parent-facing form of `simulate_traced_edge_transfer`. The compiler need
only prove the structural `EdgeArgsRel`; actual operand resolution derives the
explicit successor relation before implicit parameters are prefixed. -/
theorem simulate_traced_edge_transfer_from_parent
    {frame : Eval.Frame} {edge : Edge} {trace : Lower.EdgeTrace}
    {block : Block} {source : List RVal}
    {currentMap explicitMap : EnvMap}
    {implicitValues explicitValues : Array RVal}
    (edgeTarget : edge.target = trace.target)
    (edgeValues : edge.values = trace.explicitValues)
    (edgeCredits : edge.credits = #[])
    (traceMap : trace.sourceMap =
      Lower.EdgeTrace.sourceMapOf trace.implicitScalars explicitMap)
    (implicitCount : trace.implicitScalars = implicitValues.size)
    (environments : EnvRel source frame.values currentMap)
    (edgeArguments :
      EdgeArgsRel currentMap explicitMap trace.explicitValues)
    (resolved : Eval.resolveAtoms frame.values trace.explicitValues =
      .ok explicitValues)
    (frameCredits : frame.credits = #[])
    (blockAt : frame.definition.blocks[trace.target]? = some block)
    (blockParams : block.valueParams = trace.targetParams)
    (valueArity : (implicitValues ++ explicitValues).size =
      trace.targetParams.size)
    (blockCredits : block.creditParams = #[]) :
    let target : Eval.Frame :=
      { frame with
        block := trace.target
        pc := 0
        values := implicitValues ++ explicitValues
        credits := #[] }
    Eval.EdgeTransfer frame edge implicitValues target ∧
      EnvRel (implicitValues.toList ++ source) target.values trace.sourceMap := by
  apply simulate_traced_edge_transfer edgeTarget edgeValues edgeCredits
    traceMap implicitCount resolved
  · exact environments.of_edge_arguments edgeArguments resolved
  · exact frameCredits
  · exact blockAt
  · exact blockParams
  · exact valueArity
  · exact blockCredits

/-- Canonical generated-edge hand-off. Both the explicit argument vector and
the successor source map are computed projections of the trace's retained
parent map, so the recursive compiler proof supplies only its current
environment invariant. -/
theorem simulate_generated_edge_transfer
    {frame : Eval.Frame} {edge : Edge} {trace : Lower.EdgeTrace}
    {block : Block} {source : List RVal}
    {implicitValues explicitValues : Array RVal}
    (edgeTarget : edge.target = trace.target)
    (edgeValues : edge.values = trace.explicitValues)
    (edgeCredits : edge.credits = #[])
    (implicitCount : trace.implicitScalars = implicitValues.size)
    (environments : EnvRel source frame.values trace.sourceInputMap)
    (resolved : Eval.resolveAtoms frame.values trace.explicitValues =
      .ok explicitValues)
    (frameCredits : frame.credits = #[])
    (blockAt : frame.definition.blocks[trace.target]? = some block)
    (blockParams : block.valueParams = trace.targetParams)
    (valueArity : (implicitValues ++ explicitValues).size =
      trace.targetParams.size)
    (blockCredits : block.creditParams = #[]) :
    let target : Eval.Frame :=
      { frame with
        block := trace.target
        pc := 0
        values := implicitValues ++ explicitValues
        credits := #[] }
    Eval.EdgeTransfer frame edge implicitValues target ∧
      EnvRel (implicitValues.toList ++ source) target.values trace.sourceMap := by
  have edgeArguments : EdgeArgsRel trace.sourceInputMap
      (Lower.EdgeTrace.explicitMapOf trace.sourceInputMap)
      trace.explicitValues := by
    simpa [Lower.EdgeTrace.explicitValues] using
      EdgeArgsRel.canonical trace.sourceInputMap
  apply simulate_traced_edge_transfer_from_parent edgeTarget edgeValues
    edgeCredits (by rfl) implicitCount environments edgeArguments resolved
      frameCredits blockAt blockParams valueArity blockCredits

/-- Runtime readiness of one generated baseline edge. Operand resolution and
the implicit/explicit value-count equation are the only dynamic facts not
already fixed by `EdgeTrace`. -/
def EdgeRuntimeReady (frame : Eval.Frame) (trace : Lower.EdgeTrace) : Prop :=
  ∃ values,
    Eval.resolveAtoms frame.values trace.explicitValues = .ok values ∧
      trace.implicitScalars + values.size = trace.targetParams.size

private theorem resolveFold_exists_of_pointwise (target : Array RVal) :
    ∀ (atoms : List Atom) (accumulator : Array RVal),
      (∀ (index : Nat) (atom : Atom), atoms[index]? = some atom →
        ∃ value, Eval.resolveAtom target atom = .ok value) →
      ∃ output,
        List.foldlM
            (fun values atom => do
              return values.push (← Eval.resolveAtom target atom))
            accumulator atoms = .ok output ∧
          output.size = accumulator.size + atoms.length
  | [], accumulator, _ => ⟨accumulator, rfl, by simp⟩
  | atom :: atoms, accumulator, pointwise => by
      obtain ⟨value, resolved⟩ := pointwise 0 atom (by rfl)
      have tailPointwise : ∀ (index : Nat) (tailAtom : Atom),
          atoms[index]? = some tailAtom →
            ∃ value, Eval.resolveAtom target tailAtom = .ok value := by
        intro index tailAtom found
        exact pointwise (index + 1) tailAtom (by simpa using found)
      obtain ⟨output, folded, outputSize⟩ :=
        resolveFold_exists_of_pointwise target atoms
          (accumulator.push value) tailPointwise
      refine ⟨output, ?_, ?_⟩
      · rw [List.foldlM_cons]
        rw [resolved]
        exact folded
      · simp only [Array.size_push, List.length_cons] at outputSize ⊢
        omega

/-- A finite operand vector resolves whenever each indexed operand does. -/
theorem resolveAtoms_exists_of_pointwise {target : Array RVal}
    {atoms : Array Atom}
    (pointwise : ∀ (index : Nat) (atom : Atom),
      atoms[index]? = some atom →
      ∃ value, Eval.resolveAtom target atom = .ok value) :
    ∃ values,
      Eval.resolveAtoms target atoms = .ok values ∧
        values.size = atoms.size := by
  have listPointwise : ∀ (index : Nat) (atom : Atom),
      atoms.toList[index]? = some atom →
      ∃ value, Eval.resolveAtom target atom = .ok value := by
    intro index atom found
    exact pointwise index atom (by simpa using found)
  obtain ⟨values, resolved, valueCount⟩ :=
    resolveFold_exists_of_pointwise target atoms.toList #[] listPointwise
  refine ⟨values, ?_, ?_⟩
  · unfold Eval.resolveAtoms
    rw [← Array.foldlM_toList]
    exact resolved
  · simpa using valueCount

/-- The canonical explicit operand vector of a generated edge is dynamically
ready whenever its complete source environment is related. The retained edge
arity equation supplies the implicit-prefix count. -/
theorem edgeRuntimeReady_of_envRel {source : List RVal}
    {frame : Eval.Frame} {trace : Lower.EdgeTrace}
    (environments : EnvRel source frame.values trace.sourceInputMap)
    (sourceCount : source.length = trace.sourceInputMap.size)
    (parameterCount : trace.targetParams.size =
      trace.implicitScalars + trace.sourceInputMap.size) :
    EdgeRuntimeReady frame trace := by
  obtain ⟨values, resolved, valueCount⟩ :=
    resolveAtoms_exists_of_pointwise
      (target := frame.values) (atoms := trace.explicitValues) (by
        intro index atom found
        unfold Lower.EdgeTrace.explicitValues
          Lower.EdgeTrace.explicitValuesOf at found
        rw [Array.getElem?_map] at found
        cases slotAt : trace.sourceInputMap[index]? with
        | none => simp [slotAt] at found
        | some slot =>
            cases slot with
            | none =>
                have atomEq : atom = .erased := by
                  simpa [slotAt] using found.symm
                subst atom
                exact ⟨.erased, rfl⟩
            | some mappedAtom =>
                have atomEq : atom = mappedAtom := by
                  simpa [slotAt] using found.symm
                subst atom
                have mapBound : index < trace.sourceInputMap.size :=
                  (Array.getElem?_eq_some_iff.mp slotAt).1
                have sourceBound : index < source.length := by
                  rw [sourceCount]
                  exact mapBound
                let value := source[index]
                have sourceAt : source[index]? = some value :=
                  List.getElem?_eq_some_iff.mpr ⟨sourceBound, rfl⟩
                exact ⟨value,
                  environments index value mappedAtom sourceAt slotAt⟩)
  refine ⟨values, resolved, ?_⟩
  calc
    trace.implicitScalars + values.size =
        trace.implicitScalars + trace.sourceInputMap.size := by
          rw [valueCount]
          simp [Lower.EdgeTrace.explicitValues,
            Lower.EdgeTrace.explicitValuesOf]
    _ = trace.targetParams.size := parameterCount.symm

private theorem array_eq_empty_of_isEmpty {values : Array α}
    (empty : values.isEmpty = true) : values = #[] := by
  apply Array.ext'
  simpa [Array.isEmpty] using empty

/-- Frame after executing the first `count` generated constructor-field
fetches. -/
def fetchPrefixFrame (frame : Eval.Frame) (fields : Array RVal)
    (count : Nat) : Eval.Frame :=
  { frame with
    pc := count
    values := frame.values ++ fields.extract 0 count }

/-- Internal induction for the constructor fetch prologue. -/
private theorem simulate_fetch_prologue_from
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {atom : Atom} {cid : CtorId} {location : Nat}
    {box : IxIR1.NodeBox} {fields : Array RVal}
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (prologue : Lower.fetchPrologueMatches block.instructions atom cid
      fields.size = true)
    (resolved : Eval.resolveAtom frame.values atom = .ok (.loc location))
    (boxAt : machine.store.get? location = some box)
    (node : box.node = .ctorN cid fields) :
    ∀ (remaining index : Nat), index + remaining = fields.size →
      Eval.Steps context interpretation remaining
        { machine with
          control := .running (fetchPrefixFrame frame fields index) stack }
        { machine with
          control := .running (fetchPrefixFrame frame fields fields.size) stack } := by
  intro remaining
  induction remaining with
  | zero =>
      intro index total
      have indexEq : index = fields.size := by omega
      subst index
      exact .refl _
  | succ remaining ih =>
      intro index total
      have indexBound : index < fields.size := by omega
      have instructionAt := Lower.fetchPrologueAt_of_match prologue indexBound
      obtain ⟨pcBound, instruction⟩ :=
        Array.getElem?_eq_some_iff.mp instructionAt
      have fieldAt : fields[index]? = some fields[index] :=
        Array.getElem?_eq_some_iff.mpr ⟨indexBound, rfl⟩
      have currentResolved :
          Eval.resolveAtom (fetchPrefixFrame frame fields index).values atom =
            .ok (.loc location) := by
        simpa [fetchPrefixFrame] using
          resolveAtom_append_old
            (suffix := fields.extract 0 index) resolved
      have currentBlockAt :
          (fetchPrefixFrame frame fields index).definition.blocks[(fetchPrefixFrame
            frame fields index).block]? = some block := by
        simpa [fetchPrefixFrame] using blockAt
      have currentPc :
          (fetchPrefixFrame frame fields index).pc < block.instructions.size := by
        simpa [fetchPrefixFrame] using pcBound
      have currentInstruction :
          block.instructions[(fetchPrefixFrame frame fields index).pc] =
            .fetch atom cid index := by
        simpa [fetchPrefixFrame] using instruction
      have headRaw := Eval.Step.fetch
        (context := context) (interpretation := interpretation)
        (machine := { machine with
          control := .running (fetchPrefixFrame frame fields index) stack })
        (frame := fetchPrefixFrame frame fields index)
        (value := fields[index]) rfl currentBlockAt currentPc
          currentInstruction currentResolved boxAt node fieldAt
      have extractSucc : fields.extract 0 (index + 1) =
          (fields.extract 0 index).push fields[index] :=
        Array.extract_succ_right (by omega) indexBound
      have nextFrame :
          { fetchPrefixFrame frame fields index with
            pc := (fetchPrefixFrame frame fields index).pc + 1
            values := (fetchPrefixFrame frame fields index).values.push
              fields[index] } =
            fetchPrefixFrame frame fields (index + 1) := by
        cases frame
        unfold fetchPrefixFrame
        rw [extractSucc, Array.push_append]
      have head : Eval.Step context interpretation
          { machine with
            control := .running (fetchPrefixFrame frame fields index) stack }
          { machine with
            control := .running (fetchPrefixFrame frame fields (index + 1)) stack } := by
        rw [nextFrame] at headRaw
        exact headRaw
      have tail := ih (index + 1) (by omega)
      exact .cons rfl head tail

/-- Execute a complete certified constructor fetch prologue. The target takes
exactly one control step per field and ends with all fields appended in source
constructor order. -/
theorem simulate_fetch_prologue
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {atom : Atom} {cid : CtorId} {location : Nat}
    {box : IxIR1.NodeBox} {fields : Array RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (startPc : frame.pc = 0)
    (prologue : Lower.fetchPrologueMatches block.instructions atom cid
      fields.size = true)
    (resolved : Eval.resolveAtom frame.values atom = .ok (.loc location))
    (boxAt : machine.store.get? location = some box)
    (node : box.node = .ctorN cid fields) :
    let finalFrame : Eval.Frame :=
      { frame with
        pc := fields.size
        values := frame.values ++ fields }
    Eval.Steps context interpretation fields.size machine
      { machine with control := .running finalFrame stack } := by
  dsimp only
  have steps := simulate_fetch_prologue_from
    (context := context) (interpretation := interpretation)
    (stack := stack)
    blockAt prologue resolved boxAt node fields.size 0 (by simp)
  have startFrame : fetchPrefixFrame frame fields 0 = frame := by
    cases frame
    simp_all [fetchPrefixFrame]
  have startMachine :
      { machine with control := .running frame stack } = machine := by
    cases machine
    simp_all
  rw [startFrame, startMachine] at steps
  simpa [fetchPrefixFrame] using steps

/-- A certified constructor switch, generated edge transfer, and exact field
fetch prologue compose into the recursive constructor child's `CodeStateRel`.
The result also retains the parent runtime facts, exact edge-entry frame, and
certified child prologue needed by downstream rewrite-aware simulation. The
only non-trace premises are the runtime node, source alternative selected by
that node, and its field arity. Generated-edge operand readiness follows from
the complete source environment invariant. -/
theorem simulate_traced_switch_ctor_state
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List Lower.EdgeTrace}
    {children : List Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children))
    {sourceStore : IxIR1.Store} {source : List RVal}
    {location : Nat} {box : IxIR1.NodeBox} {cid : CtorId}
    {fields : Array RVal}
    (state : CodeStateRel functionTrace
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children) source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved : IxIR1.resolveAtom source sourceScrutinee =
      .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (node : box.node = .ctorN cid fields)
    {tag fieldCount alternativeIndex : Nat} {body : IxIR1.Code}
    (sourceAlternative : Lower.sourceAlternativeAtTag? alternatives cid.cidx =
      some (.mk tag fieldCount body, alternativeIndex))
    (fieldArity : fields.size = fieldCount)
    {constructors : Array CtorAlt} {targetPeel : Option NatPeel}
    {index : Nat} {target : CtorAlt} {edge : Lower.EdgeTrace}
    {child : Lower.CodeTrace}
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors targetPeel)
    (targetAt : constructors[index]? = some target)
    (targetAlternative : constructors.find? (fun candidate =>
      candidate.cid == cid) = some target)
    (edgeAt : outgoing[index]? = some edge)
    (childAt : children[index]? = some child)
    (control : machine.control = .running frame stack)
    (frameCredits : frame.credits = #[]) :
    ∃ finalFrame edgeFrame childScrutinee,
      child.source = site.alternative alternativeIndex ∧
        child.sourceCode = body ∧
        Eval.Steps context interpretation (1 + fields.size) machine
          { machine with control := .running finalFrame stack } ∧
        (∀ heapFuel,
          Eval.Steps context interpretation (1 + fields.size)
            { machine with heapFuel }
            { { machine with control := .running finalFrame stack } with
              heapFuel }) ∧
        finalFrame.credits = #[] ∧
        StoreRel sourceStore machine.store ∧
        CodeStateRel functionTrace child
          (fields.toList.reverse ++ source) finalFrame ∧
        frame.definition.blocks[frame.block]? = some generated ∧
        frame.pc = generated.instructions.size ∧
        Eval.resolveAtom frame.values targetScrutinee =
          .ok (.loc location) ∧
        machine.store.get? location = some box ∧
        Eval.EdgeTransfer frame target.edge #[] edgeFrame ∧
        Eval.Step context interpretation machine
          { machine with control := .running edgeFrame stack } ∧
        edgeFrame.definition.blocks[edgeFrame.block]? =
          some child.headBlock.2 ∧
        edgeFrame.pc = 0 ∧
        Eval.resolveAtom edgeFrame.values childScrutinee =
          .ok (.loc location) ∧
        Lower.fetchPrologueMatches child.headBlock.2.instructions
          childScrutinee cid fields.size = true ∧
        finalFrame = { edgeFrame with
          pc := fields.size
          values := edgeFrame.values ++ fields } := by
  have recursiveMatched :=
    functionTrace.descendantSwitchBranchesMatch descendant
  have localMatched :=
    Lower.CodeTrace.switchNodeBranchesMatch_of_match recursiveMatched
  have branch := Lower.constructorBranchMatchAt_of_switch_match
    localMatched terminator targetAt edgeAt childAt
  have targetCid : target.cid = cid := by
    have matched : (target.cid == cid) = true := Array.find?_some
      (p := fun candidate : CtorAlt => candidate.cid == cid)
      (a := target) (xs := constructors) targetAlternative
    exact beq_iff_eq.mp matched
  have branchAlternative := branch.sourceAlternative
  rw [targetCid, sourceAlternative] at branchAlternative
  have alternativeEqual := Option.some.inj branchAlternative
  have sourceTag : branch.tag = tag := by
    exact (congrArg (fun alternative : IxIR1.Alt × Nat =>
      match alternative.1 with | .mk tag _ _ => tag) alternativeEqual).symm
  have sourceFieldCount : branch.fieldCount = fieldCount := by
    exact (congrArg (fun alternative : IxIR1.Alt × Nat =>
      match alternative.1 with | .mk _ fields _ => fields) alternativeEqual).symm
  have sourceBody : branch.body = body := by
    exact (congrArg (fun alternative : IxIR1.Alt × Nat =>
      match alternative.1 with | .mk _ _ body => body) alternativeEqual).symm
  have sourceAlternativeIndex : branch.alternativeIndex = alternativeIndex :=
    (congrArg Prod.snd alternativeEqual).symm
  have edgeMember : edge ∈ outgoing := List.mem_of_getElem? edgeAt
  have childMember : child ∈ children := List.mem_of_getElem? childAt
  have childDescendant : functionTrace.root.Descendant child :=
    .step descendant childMember
  have ready : EdgeRuntimeReady frame edge :=
    edgeRuntimeReady_of_envRel
      (by simpa [Lower.CodeTrace.sourceInputMap, branch.edgeSourceInput]
        using state.environments)
      (by simpa [Lower.CodeTrace.sourceInputMap, branch.edgeSourceInput]
        using state.sourceCount)
      branch.edgeParameterCount
  obtain ⟨explicitValues, edgeResolved, edgeArity⟩ := ready
  let edgeFrame : Eval.Frame :=
    { frame with
      block := edge.target
      pc := 0
      values := #[] ++ explicitValues
      credits := #[] }
  let finalFrame : Eval.Frame :=
    { edgeFrame with
      pc := fields.size
      values := edgeFrame.values ++ fields }
  have edgeCredits : target.edge.credits = #[] :=
    array_eq_empty_of_isEmpty branch.edgeCredits
  have blockCredits : child.headBlock.2.creditParams = #[] :=
    array_eq_empty_of_isEmpty branch.childCredits
  have childBlockAt :
      frame.definition.blocks[edge.target]? = some child.headBlock.2 := by
    have found := functionTrace.descendantHeadBlockAt childDescendant
    rw [state.definition]
    simpa [branch.childHeadBlock] using found
  have parentEnvironments : EnvRel source frame.values edge.sourceInputMap := by
    have current : EnvRel source frame.values input := by
      simpa [Lower.CodeTrace.sourceInputMap] using state.environments
    simpa [branch.edgeSourceInput] using current
  have valueArity : (#[] ++ explicitValues).size = edge.targetParams.size := by
    simpa [branch.edgeImplicitScalars] using edgeArity
  obtain ⟨transferred, edgeEnvironments⟩ :=
    simulate_generated_edge_transfer branch.edgeTarget.symm branch.edgeValues
      edgeCredits (by simpa using branch.edgeImplicitScalars)
      parentEnvironments edgeResolved frameCredits childBlockAt
      branch.childParams valueArity blockCredits
  have parentBlockAt :
      frame.definition.blocks[frame.block]? = some generated := by
    simpa [Lower.CodeTrace.headBlock] using state.blockAt descendant
  have parentPc : frame.pc = generated.instructions.size := by
    simpa [Lower.CodeTrace.entryPc] using state.pc
  have syntaxMatched := functionTrace.descendantSyntaxMatches descendant
  obtain ⟨_, _, translated, _⟩ :=
    Lower.CodeTrace.switchSyntax_of_match syntaxMatched
  have targetResolved : Eval.resolveAtom frame.values targetScrutinee =
      .ok (.loc location) :=
    resolveAtom_of_envRel state.environments translated sourceResolved
  have targetGet : machine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have switchStep : Eval.Step context interpretation machine
      { machine with control := .running edgeFrame stack } := by
    apply Eval.Step.switchCtor control parentBlockAt parentPc terminator
      targetResolved targetGet node targetAlternative
    simpa [edgeFrame] using transferred
  have explicitEnvironments : EnvRel source edgeFrame.values
      (Lower.EdgeTrace.explicitMapOf edge.sourceInputMap) := by
    have sourceMapZero : edge.sourceMap =
        Lower.EdgeTrace.explicitMapOf edge.sourceInputMap := by
      unfold Lower.EdgeTrace.sourceMap
      rw [branch.edgeImplicitScalars]
      exact sourceMapOf_zero _
    rw [sourceMapZero] at edgeEnvironments
    simpa [edgeFrame] using edgeEnvironments
  have childTranslated :
      Lower.InputMap.translateAtom
        (Lower.EdgeTrace.explicitMapOf edge.sourceInputMap) sourceScrutinee =
          some branch.childScrutinee := by
    simpa [branch.edgeSourceInput] using branch.translatedScrutinee
  have childResolved : Eval.resolveAtom edgeFrame.values
      branch.childScrutinee = .ok (.loc location) :=
    resolveAtom_of_envRel explicitEnvironments childTranslated sourceResolved
  have prologue : Lower.fetchPrologueMatches child.headBlock.2.instructions
      branch.childScrutinee cid fields.size = true := by
    simpa [targetCid, sourceFieldCount, fieldArity] using branch.fetchPrologue
  have prologueSteps : Eval.Steps context interpretation fields.size
      { machine with control := .running edgeFrame stack }
      { machine with control := .running finalFrame stack } := by
    apply simulate_fetch_prologue
      (machine := { machine with control := .running edgeFrame stack })
      (frame := edgeFrame) (stack := stack) rfl
      (show edgeFrame.definition.blocks[edgeFrame.block]? =
        some child.headBlock.2 by simpa [edgeFrame] using childBlockAt)
      (by rfl) prologue childResolved targetGet node
  have targetSteps : Eval.Steps context interpretation (1 + fields.size)
      machine { machine with control := .running finalFrame stack } :=
    (switchStep.toSteps control).trans prologueSteps
  have targetStepsPreserving : ∀ heapFuel,
      Eval.Steps context interpretation (1 + fields.size)
        { machine with heapFuel }
        { { machine with control := .running finalFrame stack } with
          heapFuel } := by
    intro heapFuel
    let fundedMachine : Eval.Machine := { machine with heapFuel }
    have fundedControl : fundedMachine.control = .running frame stack := by
      simpa [fundedMachine] using control
    have fundedGet : fundedMachine.store.get? location = some box := by
      simpa [fundedMachine] using targetGet
    have fundedSwitch : Eval.Step context interpretation fundedMachine
        { fundedMachine with control := .running edgeFrame stack } := by
      apply Eval.Step.switchCtor fundedControl parentBlockAt parentPc terminator
        targetResolved fundedGet node targetAlternative
      simpa [edgeFrame] using transferred
    have fundedPrologue : Eval.Steps context interpretation fields.size
        { fundedMachine with control := .running edgeFrame stack }
        { fundedMachine with control := .running finalFrame stack } := by
      apply simulate_fetch_prologue
        (machine := { fundedMachine with
          control := .running edgeFrame stack })
        (frame := edgeFrame) (stack := stack) rfl
        (show edgeFrame.definition.blocks[edgeFrame.block]? =
          some child.headBlock.2 by simpa [edgeFrame] using childBlockAt)
        (by rfl) prologue childResolved fundedGet node
    have fundedSteps := (fundedSwitch.toSteps fundedControl).trans
      fundedPrologue
    simpa [fundedMachine] using fundedSteps
  have finalEnvironments : EnvRel (fields.toList.reverse ++ source)
      finalFrame.values child.sourceInputMap := by
    have extended := explicitEnvironments.constructorFields (fields := fields)
    have edgeValueCount : edgeFrame.values.size = edge.targetParams.size := by
      simpa [edgeFrame] using valueArity
    simpa [finalFrame, branch.childInput, edgeValueCount, sourceFieldCount,
      fieldArity] using extended
  have explicitValueCount : explicitValues.size = edge.targetParams.size := by
    simpa using valueArity
  have childState : CodeStateRel functionTrace child
      (fields.toList.reverse ++ source) finalFrame := by
    constructor
    · simpa [finalFrame, edgeFrame] using state.definition
    · simpa [finalFrame, edgeFrame] using branch.childBlock.symm
    · simpa [finalFrame, sourceFieldCount, fieldArity] using branch.childPc.symm
    · calc
        finalFrame.values.size = edge.targetParams.size + fields.size := by
          simp [finalFrame, edgeFrame, explicitValueCount]
        _ = edge.targetParams.size + branch.fieldCount := by
          rw [sourceFieldCount, fieldArity]
        _ = child.entryValueCount := branch.childValueCount.symm
    · rw [branch.childInput]
      have currentCount : source.length = input.size := by
        simpa [Lower.CodeTrace.sourceInputMap] using state.sourceCount
      simp [Lower.constructorChildInputMap, fieldArity,
        Lower.EdgeTrace.explicitMapOf, sourceFieldCount,
        branch.edgeSourceInput, currentCount]
    · exact finalEnvironments
  exact ⟨finalFrame, edgeFrame, branch.childScrutinee,
    branch.childSource.trans
      (congrArg (fun index => site.alternative index)
        sourceAlternativeIndex),
    branch.childCode.trans sourceBody,
    targetSteps, targetStepsPreserving, rfl, stores, childState,
    parentBlockAt, parentPc, targetResolved, targetGet, transferred, switchStep,
    by simpa [edgeFrame] using childBlockAt, rfl, childResolved, prologue, rfl⟩

/-- A certified literal-zero switch step enters the exact recursive child
state. All branch/edge/body coordinates, generated-edge operand readiness,
and the successor proof map follow from the retained trace invariant. -/
theorem simulate_traced_switch_nat_zero_state
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {targetScrutinee : Atom} {generated : Block}
    {outgoing : List Lower.EdgeTrace} {children : List Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children))
    {source : List RVal}
    (state : CodeStateRel functionTrace
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children) source frame)
    (sourceResolved : IxIR1.resolveAtom source sourceScrutinee =
      .ok (.lit (.nat 0)))
    (control : machine.control = .running frame stack)
    (frameCredits : frame.credits = #[]) :
    ∃ (constructors : Array CtorAlt) (peel : NatPeel)
        (branches : Lower.NatBranchPairMatch site blockId input alternatives
          constructors peel outgoing children) (childFrame : Eval.Frame),
      generated.terminator =
          .switchValue targetScrutinee constructors (some peel) ∧
        branches.zeroEdge ∈ outgoing ∧
        branches.zeroChild ∈ children ∧
        Lower.sourceAlternativeAtTag? alternatives 0 =
          some (.mk 0 0 branches.zero.body,
            branches.zero.alternativeIndex) ∧
        branches.zeroChild.source =
          site.alternative branches.zero.alternativeIndex ∧
        branches.zeroChild.sourceCode = branches.zero.body ∧
        Eval.Step context interpretation machine
          { machine with control := .running childFrame stack } ∧
        (∀ heapFuel,
          Eval.Step context interpretation { machine with heapFuel }
            { { machine with control := .running childFrame stack } with
              heapFuel }) ∧
        childFrame.credits = #[] ∧
        CodeStateRel functionTrace branches.zeroChild source childFrame := by
  have recursiveMatched :=
    functionTrace.descendantSwitchBranchesMatch descendant
  have localMatched :=
    Lower.CodeTrace.switchNodeBranchesMatch_of_match recursiveMatched
  have syntaxMatched := functionTrace.descendantSyntaxMatches descendant
  obtain ⟨constructors, natPeel, translated, terminator⟩ :=
    Lower.CodeTrace.switchSyntax_of_match syntaxMatched
  cases natPeel with
  | none =>
      simp [Lower.switchNodeBranchesMatch, terminator] at localMatched
  | some peel =>
      let branches := Lower.natBranchPairMatch_of_switch_match
        localMatched terminator
      have edgeMember : branches.zeroEdge ∈ outgoing :=
        List.mem_of_getElem? branches.zeroEdgeAt
      have childMember : branches.zeroChild ∈ children :=
        List.mem_of_getElem? branches.zeroChildAt
      have childDescendant :
          functionTrace.root.Descendant branches.zeroChild :=
        .step descendant childMember
      have ready : EdgeRuntimeReady frame branches.zeroEdge :=
        edgeRuntimeReady_of_envRel
          (by simpa [Lower.CodeTrace.sourceInputMap,
              branches.zero.edgeSourceInput] using state.environments)
          (by simpa [Lower.CodeTrace.sourceInputMap,
              branches.zero.edgeSourceInput] using state.sourceCount)
          branches.zero.edgeParameterCount
      obtain ⟨explicitValues, edgeResolved, edgeArity⟩ := ready
      let childFrame : Eval.Frame :=
        { frame with
          block := branches.zeroEdge.target
          pc := 0
          values := #[] ++ explicitValues
          credits := #[] }
      have edgeCredits : peel.zero.credits = #[] :=
        array_eq_empty_of_isEmpty branches.zero.edgeCredits
      have blockCredits :
          branches.zeroChild.headBlock.2.creditParams = #[] :=
        array_eq_empty_of_isEmpty branches.zero.childCredits
      have childBlockAt :
          frame.definition.blocks[branches.zeroEdge.target]? =
            some branches.zeroChild.headBlock.2 := by
        have found := functionTrace.descendantHeadBlockAt childDescendant
        rw [state.definition]
        simpa [branches.zero.childHeadBlock] using found
      have parentEnvironments : EnvRel source frame.values
          branches.zeroEdge.sourceInputMap := by
        have current : EnvRel source frame.values input := by
          simpa [Lower.CodeTrace.sourceInputMap] using state.environments
        simpa [branches.zero.edgeSourceInput] using current
      have valueArity : (#[] ++ explicitValues).size =
          branches.zeroEdge.targetParams.size := by
        simpa [branches.zero.edgeImplicitScalars] using edgeArity
      obtain ⟨transferred, childEnvironments⟩ :=
        simulate_generated_edge_transfer
          branches.zero.edgeTarget.symm branches.zero.edgeValues edgeCredits
          (by simpa using branches.zero.edgeImplicitScalars)
          parentEnvironments edgeResolved frameCredits childBlockAt
          branches.zero.childParams valueArity blockCredits
      have parentBlockAt :
          frame.definition.blocks[frame.block]? = some generated := by
        simpa [Lower.CodeTrace.headBlock] using state.blockAt descendant
      have parentPc : frame.pc = generated.instructions.size := by
        simpa [Lower.CodeTrace.entryPc] using state.pc
      have targetResolved : Eval.resolveAtom frame.values targetScrutinee =
          .ok (.lit (.nat 0)) :=
        resolveAtom_of_envRel state.environments translated sourceResolved
      have targetStep : Eval.Step context interpretation machine
          { machine with control := .running childFrame stack } := by
        apply Eval.Step.switchNatZero control parentBlockAt parentPc terminator
          targetResolved
        simpa [childFrame] using transferred
      have targetStepPreserving : ∀ heapFuel,
          Eval.Step context interpretation { machine with heapFuel }
            { { machine with control := .running childFrame stack } with
              heapFuel } := by
        intro heapFuel
        let fundedMachine : Eval.Machine := { machine with heapFuel }
        have fundedControl : fundedMachine.control =
            .running frame stack := by
          simpa [fundedMachine] using control
        have fundedStep : Eval.Step context interpretation fundedMachine
            { fundedMachine with control := .running childFrame stack } := by
          apply Eval.Step.switchNatZero fundedControl parentBlockAt parentPc
            terminator targetResolved
          simpa [childFrame] using transferred
        simpa [fundedMachine] using fundedStep
      have childState : CodeStateRel functionTrace branches.zeroChild source
          childFrame := by
        constructor
        · simpa [childFrame] using state.definition
        · simpa [childFrame] using branches.zero.childBlock.symm
        · simpa [childFrame] using branches.zero.childPc.symm
        · calc
            childFrame.values.size = branches.zeroEdge.targetParams.size := by
              simpa [childFrame] using valueArity
            _ = branches.zeroChild.entryValueCount :=
              branches.zero.childValueCount.symm
        · rw [branches.zero.childInput]
          simpa [Lower.EdgeTrace.sourceMap, Lower.EdgeTrace.sourceMapOf,
            Lower.EdgeTrace.explicitMapOf,
            branches.zero.edgeImplicitScalars,
            branches.zero.edgeSourceInput, Lower.CodeTrace.sourceInputMap]
            using state.sourceCount
        · simpa [childFrame, branches.zero.childInput] using
            childEnvironments
      exact ⟨constructors, peel, branches, childFrame, terminator, edgeMember,
        childMember, branches.zero.sourceAlternative,
        branches.zero.childSource, branches.zero.childCode, targetStep,
        targetStepPreserving, rfl, childState⟩

/-- A certified literal-successor switch step preserves the peeled
predecessor as the child environment's implicit leading scalar and enters the
exact recursive child state. -/
theorem simulate_traced_switch_nat_succ_state
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {targetScrutinee : Atom} {generated : Block}
    {outgoing : List Lower.EdgeTrace} {children : List Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children))
    {source : List RVal} {predecessor : Nat}
    (state : CodeStateRel functionTrace
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children) source frame)
    (sourceResolved : IxIR1.resolveAtom source sourceScrutinee =
      .ok (.lit (.nat (predecessor + 1))))
    (control : machine.control = .running frame stack)
    (frameCredits : frame.credits = #[]) :
    ∃ (constructors : Array CtorAlt) (peel : NatPeel)
        (branches : Lower.NatBranchPairMatch site blockId input alternatives
          constructors peel outgoing children) (childFrame : Eval.Frame),
      generated.terminator =
          .switchValue targetScrutinee constructors (some peel) ∧
        branches.succEdge ∈ outgoing ∧
        branches.succChild ∈ children ∧
        Lower.sourceAlternativeAtTag? alternatives 1 =
          some (.mk 1 1 branches.succ.body,
            branches.succ.alternativeIndex) ∧
        branches.succChild.source =
          site.alternative branches.succ.alternativeIndex ∧
        branches.succChild.sourceCode = branches.succ.body ∧
        Eval.Step context interpretation machine
          { machine with control := .running childFrame stack } ∧
        (∀ heapFuel,
          Eval.Step context interpretation { machine with heapFuel }
            { { machine with control := .running childFrame stack } with
              heapFuel }) ∧
        childFrame.credits = #[] ∧
        CodeStateRel functionTrace branches.succChild
          (.lit (.nat predecessor) :: source) childFrame := by
  have recursiveMatched :=
    functionTrace.descendantSwitchBranchesMatch descendant
  have localMatched :=
    Lower.CodeTrace.switchNodeBranchesMatch_of_match recursiveMatched
  have syntaxMatched := functionTrace.descendantSyntaxMatches descendant
  obtain ⟨constructors, natPeel, translated, terminator⟩ :=
    Lower.CodeTrace.switchSyntax_of_match syntaxMatched
  cases natPeel with
  | none =>
      simp [Lower.switchNodeBranchesMatch, terminator] at localMatched
  | some peel =>
      let branches := Lower.natBranchPairMatch_of_switch_match
        localMatched terminator
      have edgeMember : branches.succEdge ∈ outgoing :=
        List.mem_of_getElem? branches.succEdgeAt
      have childMember : branches.succChild ∈ children :=
        List.mem_of_getElem? branches.succChildAt
      have childDescendant :
          functionTrace.root.Descendant branches.succChild :=
        .step descendant childMember
      have ready : EdgeRuntimeReady frame branches.succEdge :=
        edgeRuntimeReady_of_envRel
          (by simpa [Lower.CodeTrace.sourceInputMap,
              branches.succ.edgeSourceInput] using state.environments)
          (by simpa [Lower.CodeTrace.sourceInputMap,
              branches.succ.edgeSourceInput] using state.sourceCount)
          branches.succ.edgeParameterCount
      obtain ⟨explicitValues, edgeResolved, edgeArity⟩ := ready
      let implicitValues : Array RVal := #[.lit (.nat predecessor)]
      let childFrame : Eval.Frame :=
        { frame with
          block := branches.succEdge.target
          pc := 0
          values := implicitValues ++ explicitValues
          credits := #[] }
      have edgeCredits : peel.succ.credits = #[] :=
        array_eq_empty_of_isEmpty branches.succ.edgeCredits
      have blockCredits :
          branches.succChild.headBlock.2.creditParams = #[] :=
        array_eq_empty_of_isEmpty branches.succ.childCredits
      have childBlockAt :
          frame.definition.blocks[branches.succEdge.target]? =
            some branches.succChild.headBlock.2 := by
        have found := functionTrace.descendantHeadBlockAt childDescendant
        rw [state.definition]
        simpa [branches.succ.childHeadBlock] using found
      have parentEnvironments : EnvRel source frame.values
          branches.succEdge.sourceInputMap := by
        have current : EnvRel source frame.values input := by
          simpa [Lower.CodeTrace.sourceInputMap] using state.environments
        simpa [branches.succ.edgeSourceInput] using current
      have valueArity : (implicitValues ++ explicitValues).size =
          branches.succEdge.targetParams.size := by
        simpa [implicitValues, branches.succ.edgeImplicitScalars] using
          edgeArity
      obtain ⟨transferred, childEnvironments⟩ :=
        simulate_generated_edge_transfer
          branches.succ.edgeTarget.symm branches.succ.edgeValues edgeCredits
          (by simpa [implicitValues] using branches.succ.edgeImplicitScalars)
          parentEnvironments edgeResolved frameCredits childBlockAt
          branches.succ.childParams valueArity blockCredits
      have parentBlockAt :
          frame.definition.blocks[frame.block]? = some generated := by
        simpa [Lower.CodeTrace.headBlock] using state.blockAt descendant
      have parentPc : frame.pc = generated.instructions.size := by
        simpa [Lower.CodeTrace.entryPc] using state.pc
      have targetResolved : Eval.resolveAtom frame.values targetScrutinee =
          .ok (.lit (.nat (predecessor + 1))) :=
        resolveAtom_of_envRel state.environments translated sourceResolved
      have targetStep : Eval.Step context interpretation machine
          { machine with control := .running childFrame stack } := by
        apply Eval.Step.switchNatSucc control parentBlockAt parentPc terminator
          targetResolved
        simpa [childFrame, implicitValues] using transferred
      have targetStepPreserving : ∀ heapFuel,
          Eval.Step context interpretation { machine with heapFuel }
            { { machine with control := .running childFrame stack } with
              heapFuel } := by
        intro heapFuel
        let fundedMachine : Eval.Machine := { machine with heapFuel }
        have fundedControl : fundedMachine.control =
            .running frame stack := by
          simpa [fundedMachine] using control
        have fundedStep : Eval.Step context interpretation fundedMachine
            { fundedMachine with control := .running childFrame stack } := by
          apply Eval.Step.switchNatSucc fundedControl parentBlockAt parentPc
            terminator targetResolved
          simpa [childFrame, implicitValues] using transferred
        simpa [fundedMachine] using fundedStep
      have childState : CodeStateRel functionTrace branches.succChild
          (.lit (.nat predecessor) :: source) childFrame := by
        constructor
        · simpa [childFrame] using state.definition
        · simpa [childFrame] using branches.succ.childBlock.symm
        · simpa [childFrame] using branches.succ.childPc.symm
        · calc
            childFrame.values.size = branches.succEdge.targetParams.size := by
              simpa [childFrame] using valueArity
            _ = branches.succChild.entryValueCount :=
              branches.succ.childValueCount.symm
        · rw [branches.succ.childInput]
          have currentCount : source.length = input.size := by
            simpa [Lower.CodeTrace.sourceInputMap] using state.sourceCount
          simp [Lower.EdgeTrace.sourceMap, Lower.EdgeTrace.sourceMapOf,
            Lower.EdgeTrace.explicitMapOf,
            branches.succ.edgeImplicitScalars,
            branches.succ.edgeSourceInput, currentCount, Nat.add_comm]
        · simpa [childFrame, implicitValues, branches.succ.childInput] using
            childEnvironments
      exact ⟨constructors, peel, branches, childFrame, terminator, edgeMember,
        childMember, branches.succ.sourceAlternative,
        branches.succ.childSource, branches.succ.childCode, targetStep,
        targetStepPreserving, rfl, childState⟩

private theorem resolveFold_of_envRel {source : List RVal}
    {target : Array RVal} {mapping : EnvMap}
    (relation : EnvRel source target mapping)
    {sourceAtoms : List IxIR1.Atom} {targetAtoms : List Atom}
    (atoms : AtomsListRel mapping sourceAtoms targetAtoms) :
    ∀ (accumulator output : List RVal),
      List.foldlM
          (fun values atom => do
            return values ++ [← IxIR1.resolveAtom source atom])
          accumulator sourceAtoms = .ok output →
      List.foldlM
          (fun values atom => do
            return values.push (← Eval.resolveAtom target atom))
          accumulator.toArray targetAtoms = .ok output.toArray := by
  induction atoms with
  | nil =>
      intro accumulator output resolved
      simp only [List.foldlM_nil] at resolved ⊢
      cases resolved
      rfl
  | @cons sourceAtom targetAtom sourceAtoms targetAtoms translated _ ih =>
      intro accumulator output resolved
      simp only [List.foldlM_cons] at resolved ⊢
      obtain ⟨nextAccumulator, headResolved, tailResolved⟩ :=
        except_bind_eq_ok resolved
      obtain ⟨value, sourceResolved, nextResolved⟩ :=
        except_bind_eq_ok headResolved
      have nextEqual : nextAccumulator = accumulator ++ [value] := by
        simpa using Except.ok.inj nextResolved.symm
      subst nextAccumulator
      have targetResolved :
          Eval.resolveAtom target targetAtom = .ok value :=
        resolveAtom_of_envRel relation translated sourceResolved
      rw [targetResolved]
      have appendArray :
          (accumulator ++ [value]).toArray = accumulator.toArray.push value := by
        apply Array.ext'
        simp
      change List.foldlM
          (fun values atom => do
            return values.push (← Eval.resolveAtom target atom))
          (accumulator.toArray.push value) targetAtoms = .ok output.toArray
      rw [← appendArray]
      exact ih (accumulator ++ [value]) output tailResolved

/-- Operand-vector resolution agrees pointwise, including result order. -/
theorem resolveAtoms_of_envRel {source : List RVal} {target : Array RVal}
    {mapping : EnvMap} (relation : EnvRel source target mapping)
    {sourceAtoms : Array IxIR1.Atom} {targetAtoms : Array Atom}
    (atoms : AtomsRel mapping sourceAtoms targetAtoms)
    {values : List RVal}
    (resolved : IxIR1.resolveAtoms source sourceAtoms = .ok values) :
    Eval.resolveAtoms target targetAtoms = .ok values.toArray := by
  unfold Eval.resolveAtoms
  rw [← Array.foldlM_toList]
  apply resolveFold_of_envRel relation atoms [] values
  simpa only [IxIR1.resolveAtoms, Array.foldlM_toList] using resolved

/-- Ordinary allocation is the first heap-changing instruction case. The
source and target allocate the same constructor at the same fresh location
under either interpretation, preserve the exact baseline store relation, and
bind related result slots. -/
theorem simulate_alloc {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {world : Ix.Compiler.Ixon.Owned} {cid : IxIR1.CtorId}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom} {schema : CtorSchema}
    {values : List RVal}
    (arguments : AtomsRel mapping sourceArguments targetArguments)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (fields : Eval.FieldWorlds machine.store schema values.toArray)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .alloc world cid targetArguments)
    (schemaAt : context.schemas world cid = some schema) :
    let node := IxIR1.Node.ctorN cid values.toArray
    let sourceAllocation := sourceStore.allocNode world node
    let targetAllocation := machine.store.allocNode world node
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.alloc world cid sourceArguments) =
        .ok (sourceAllocation.1, .loc sourceAllocation.2) ∧
      Eval.Step context interpretation machine
        { machine with
          store := targetAllocation.1
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push (.loc sourceAllocation.2) }
            stack } ∧
      StoreRel sourceAllocation.1 targetAllocation.1 ∧
      EnvRel (.loc sourceAllocation.2 :: source)
        (frame.values.push (.loc sourceAllocation.2))
        (#[some (.reg frame.values.size)] ++ mapping) := by
  dsimp only
  have targetResolved :
      Eval.resolveAtoms frame.values targetArguments = .ok values.toArray :=
    resolveAtoms_of_envRel environments arguments sourceResolved
  have locationEq :
      (machine.store.allocNode world (.ctorN cid values.toArray)).2 =
        (sourceStore.allocNode world (.ctorN cid values.toArray)).2 :=
    stores.alloc_location world (.ctorN cid values.toArray)
  have targetStep := Eval.Step.alloc (interpretation := interpretation)
    control blockAt pc instruction schemaAt targetResolved fields
  dsimp only at targetStep
  rw [locationEq] at targetStep
  refine ⟨?_, targetStep,
    stores.alloc world (.ctorN cid values.toArray), ?_⟩
  · unfold IxIR1.runOp
    simp only
    rw [sourceResolved]
    rfl
  · exact environments.bindValue
      (.loc (sourceStore.allocNode world (.ctorN cid values.toArray)).2)

/-- Trace-facing allocation transition. Checked operation syntax supplies the
world, constructor, and target operand vector; recursive-state helpers supply
the instruction coordinate and exact continuation state. -/
theorem simulate_traced_alloc_state {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceWorld targetWorld : Ix.Compiler.Ixon.Owned}
    {sourceCid targetCid : IxIR1.CtorId}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next))
    {sourceStore : IxIR1.Store} {source : List RVal}
    {schema : CtorSchema} {values : List RVal}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next) source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (fields : Eval.FieldWorlds machine.store schema values.toArray)
    (control : machine.control = .running frame stack)
    (schemaAt : context.schemas sourceWorld sourceCid = some schema) :
    let node := IxIR1.Node.ctorN sourceCid values.toArray
    let sourceAllocation := sourceStore.allocNode sourceWorld node
    let targetAllocation := machine.store.allocNode sourceWorld node
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push (.loc sourceAllocation.2) }
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.alloc sourceWorld sourceCid sourceArguments) =
        .ok (sourceAllocation.1, .loc sourceAllocation.2) ∧
      Eval.Step context interpretation machine
        { machine with
          store := targetAllocation.1
          control := .running nextFrame stack } ∧
      StoreRel sourceAllocation.1 targetAllocation.1 ∧
      CodeStateRel functionTrace next
        (.loc sourceAllocation.2 :: source) nextFrame := by
  dsimp only
  have operationSyntax := functionTrace.descendantOperationSyntax descendant
  change sourceWorld = targetWorld ∧ sourceCid = targetCid ∧
    Lower.InputMap.translateAtoms input sourceArguments =
      some targetArguments at operationSyntax
  obtain ⟨worldEq, cidEq, translated⟩ := operationSyntax
  subst targetWorld
  subst targetCid
  have arguments : AtomsRel input sourceArguments targetArguments :=
    atomsRel_of_translateAtoms translated
  obtain ⟨blockAt, pcBound, instructionAt⟩ := state.instructionAt descendant
  have instruction :
      next.headBlock.2.instructions[frame.pc] =
        .alloc sourceWorld sourceCid targetArguments :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  obtain ⟨sourceRun, targetStep, nextStores, canonical⟩ := simulate_alloc
    stores state.environments arguments sourceResolved fields control blockAt
      pcBound instruction schemaAt
  have nextEnvironments := canonical.forgetTracedValue state descendant
    (show Lower.Instr.baselineBinderAtom entryValueCount
      (.alloc sourceWorld sourceCid targetArguments) =
        some (.reg entryValueCount) by rfl)
  refine ⟨sourceRun, targetStep, nextStores,
    state.letOpNext descendant rfl rfl rfl ?_ rfl nextEnvironments⟩
  simp [Lower.Instr.baselineValueDelta]

/-- Checked-artifact allocation transition. The retained schema and producer
capability certificates select the dynamic source ownership invariant, so
recursive simulation callers supply neither a target-only `FieldWorlds`
witness nor an allocation-shaped root list. -/
theorem simulate_traced_alloc_checked_state
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat} {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation}
    {checked : Lower.Checked} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    (contextSchemas : context.schemas =
      checked.artifact.validationContext.schemas)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceWorld targetWorld : Ix.Compiler.Ixon.Owned}
    {sourceCid targetCid : IxIR1.CtorId}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next))
    {sourceStore : IxIR1.Store} {source : List RVal}
    {schema : CtorSchema} {values : List RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next) source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (control : machine.control = .running frame stack)
    (schemaAt : context.schemas sourceWorld sourceCid = some schema)
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next)
      sourceStore source frameRoots) :
    let node := IxIR1.Node.ctorN sourceCid values.toArray
    let sourceAllocation := sourceStore.allocNode sourceWorld node
    let targetAllocation := machine.store.allocNode sourceWorld node
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push (.loc sourceAllocation.2) }
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.alloc sourceWorld sourceCid sourceArguments) =
        .ok (sourceAllocation.1, .loc sourceAllocation.2) ∧
      Eval.Step context interpretation machine
        { machine with
          store := targetAllocation.1
          control := .running nextFrame stack } ∧
      StoreRel sourceAllocation.1 targetAllocation.1 ∧
      CodeStateRel functionTrace next
        (.loc sourceAllocation.2 :: source) nextFrame := by
  have checkedSchemaAt : checked.artifact.validationContext.schemas
      sourceWorld sourceCid = some schema := by
    rw [← contextSchemas]
    exact schemaAt
  have fields := stores.fieldWorlds_of_checked_allocation_capabilities
    functionMember descendant ownership sourceResolved checkedSchemaAt
  exact simulate_traced_alloc_state descendant state stores sourceResolved
    fields control schemaAt

/-- Successful-run form of checked ordinary allocation. Source evaluation
determines the field vector and exact fresh location; the checked schema,
producer capabilities, and trace-indexed ownership invariant discharge
`FieldWorlds`. -/
theorem simulate_traced_alloc_checked_success_step
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat} {context : Eval.Context} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation}
    {checked : Lower.Checked} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    (contextSchemas : context.schemas =
      checked.artifact.validationContext.schemas)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceWorld targetWorld : Ix.Compiler.Ixon.Owned}
    {sourceCid targetCid : IxIR1.CtorId}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next))
    {sourceStore : IxIR1.Store} {source : List RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput : IxIR1.Store × RVal}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next) source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 2)
      sourceCurrent sourceStore source
        (.letOp (.alloc sourceWorld sourceCid sourceArguments)
          next.sourceCode) = .ok sourceOutput)
    (control : machine.control = .running frame stack)
    {schema : CtorSchema}
    (schemaAt : context.schemas sourceWorld sourceCid = some schema)
    (ownership : SourceOwnershipAt checked.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next)
      sourceStore source frameRoots) :
    ∃ values sourceAllocation targetAllocation nextFrame,
      sourceAllocation = sourceStore.allocNode sourceWorld
          (.ctorN sourceCid values.toArray) ∧
        targetAllocation = machine.store.allocNode sourceWorld
          (.ctorN sourceCid values.toArray) ∧
        IxIR1.resolveAtoms source sourceArguments = .ok values ∧
        IxIR1.runCode sourceContext (sourceFuel + 1) sourceCurrent
          sourceAllocation.1 (.loc sourceAllocation.2 :: source)
          next.sourceCode = .ok sourceOutput ∧
        nextFrame =
          { frame with
            pc := frame.pc + 1
            values := frame.values.push (.loc sourceAllocation.2) } ∧
        Eval.Step context .logical machine
          { machine with
            store := targetAllocation.1
            control := .running nextFrame stack } ∧
        StoreRel sourceAllocation.1 targetAllocation.1 ∧
        CodeStateRel functionTrace next
          (.loc sourceAllocation.2 :: source) nextFrame := by
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  obtain ⟨values, sourceResolved, operationOutput⟩ :=
    IxIR1.runOp_alloc_success operationRun
  have middleStoreEq : middleStore =
      (sourceStore.allocNode sourceWorld
        (.ctorN sourceCid values.toArray)).1 :=
    congrArg Prod.fst operationOutput
  have operationValueEq : operationValue =
      .loc (sourceStore.allocNode sourceWorld
        (.ctorN sourceCid values.toArray)).2 :=
    congrArg Prod.snd operationOutput
  subst middleStore
  subst operationValue
  obtain ⟨_, targetStep, nextStores, nextState⟩ :=
    simulate_traced_alloc_checked_state
      (sourceContext := sourceContext) (sourceCurrent := sourceCurrent)
      (sourceFuel := sourceFuel) functionMember contextSchemas descendant state
      stores sourceResolved control schemaAt ownership
  exact ⟨values,
    sourceStore.allocNode sourceWorld (.ctorN sourceCid values.toArray),
    machine.store.allocNode sourceWorld (.ctorN sourceCid values.toArray),
    { frame with
      pc := frame.pc + 1
      values := frame.values.push
        (.loc (sourceStore.allocNode sourceWorld
          (.ctorN sourceCid values.toArray)).2) },
    rfl, rfl, sourceResolved, continuationRun, rfl, targetStep, nextStores,
    nextState⟩

/-- Strictly under-saturated partial application allocates the same shared PAP
node in IxIR₁ and IxIR₂.  The declaration premises are the function-level
context correspondence that the later whole-program induction will supply. -/
theorem simulate_papp_fn {sourceContext : IxIR1.Ctx}
    {sourceCurrent sourceDefinition : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {targetDefinition : Function}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {address : Ix.Compiler.Ixon.Address}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom} {values : List RVal}
    (arguments : AtomsRel mapping sourceArguments targetArguments)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceDeclaration :
      sourceContext.decls address = some (.fn sourceDefinition))
    (targetDeclaration :
      context.declarations address = some (.fn targetDefinition))
    (arity :
      targetDefinition.signature.params.size = sourceDefinition.arity)
    (papSafe : targetDefinition.signature.papSafe = true)
    (under : values.length < sourceDefinition.arity)
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .papp address targetArguments) :
    let node := IxIR1.Node.papN address sourceDefinition.arity values.toArray
    let sourceAllocation := sourceStore.allocNode .shared node
    let targetAllocation := machine.store.allocNode .shared node
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.papp address sourceArguments) =
        .ok (sourceAllocation.1, .loc sourceAllocation.2) ∧
      Eval.Step context interpretation machine
        { machine with
          store := targetAllocation.1
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push (.loc sourceAllocation.2) }
            stack } ∧
      StoreRel sourceAllocation.1 targetAllocation.1 ∧
      EnvRel (.loc sourceAllocation.2 :: source)
        (frame.values.push (.loc sourceAllocation.2))
        (#[some (.reg frame.values.size)] ++ mapping) := by
  dsimp only
  have targetResolved :
      Eval.resolveAtoms frame.values targetArguments = .ok values.toArray :=
    resolveAtoms_of_envRel environments arguments sourceResolved
  have targetUnder :
      values.toArray.size < targetDefinition.signature.params.size := by
    simpa [arity] using under
  have targetStep := Eval.Step.pappFn (interpretation := interpretation)
    control blockAt pc instruction noCredits targetDeclaration papSafe
    targetResolved targetUnder
  rw [arity] at targetStep
  dsimp only at targetStep
  have locationEq :
      (machine.store.allocNode .shared
        (.papN address sourceDefinition.arity values.toArray)).2 =
      (sourceStore.allocNode .shared
        (.papN address sourceDefinition.arity values.toArray)).2 :=
    stores.alloc_location .shared
      (.papN address sourceDefinition.arity values.toArray)
  rw [locationEq] at targetStep
  refine ⟨?_, targetStep,
    stores.alloc .shared
      (.papN address sourceDefinition.arity values.toArray),
    environments.bindValue
      (.loc (sourceStore.allocNode .shared
        (.papN address sourceDefinition.arity values.toArray)).2)⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  simp only [bind, Except.bind]
  rw [sourceDeclaration]
  unfold IxIR1.declArity
  simp only
  rw [if_pos under]

/-- Trace-facing function partial application. Address/argument syntax,
instruction coordinates, successor map, and recursive state are all recovered
from the checked derivation. -/
theorem simulate_traced_papp_fn_state {sourceContext : IxIR1.Ctx}
    {sourceCurrent sourceDefinition : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {targetDefinition : Function}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAddress targetAddress : Ix.Compiler.Ixon.Address}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.papp sourceAddress sourceArguments) index
        (.papp targetAddress targetArguments) next))
    {sourceStore : IxIR1.Store} {source : List RVal}
    {values : List RVal}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.papp sourceAddress sourceArguments) index
        (.papp targetAddress targetArguments) next) source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceDeclaration :
      sourceContext.decls sourceAddress = some (.fn sourceDefinition))
    (targetDeclaration :
      context.declarations sourceAddress = some (.fn targetDefinition))
    (arity : targetDefinition.signature.params.size = sourceDefinition.arity)
    (papSafe : targetDefinition.signature.papSafe = true)
    (under : values.length < sourceDefinition.arity)
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let node := IxIR1.Node.papN sourceAddress sourceDefinition.arity
      values.toArray
    let sourceAllocation := sourceStore.allocNode .shared node
    let targetAllocation := machine.store.allocNode .shared node
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push (.loc sourceAllocation.2) }
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.papp sourceAddress sourceArguments) =
        .ok (sourceAllocation.1, .loc sourceAllocation.2) ∧
      Eval.Step context interpretation machine
        { machine with
          store := targetAllocation.1
          control := .running nextFrame stack } ∧
      StoreRel sourceAllocation.1 targetAllocation.1 ∧
      CodeStateRel functionTrace next
        (.loc sourceAllocation.2 :: source) nextFrame := by
  dsimp only
  have operationSyntax := functionTrace.descendantOperationSyntax descendant
  change sourceAddress = targetAddress ∧
    Lower.InputMap.translateAtoms input sourceArguments =
      some targetArguments at operationSyntax
  obtain ⟨addressEq, translated⟩ := operationSyntax
  subst targetAddress
  have arguments : AtomsRel input sourceArguments targetArguments :=
    atomsRel_of_translateAtoms translated
  obtain ⟨blockAt, pcBound, instructionAt⟩ := state.instructionAt descendant
  have instruction :
      next.headBlock.2.instructions[frame.pc] =
        .papp sourceAddress targetArguments :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  obtain ⟨sourceRun, targetStep, nextStores, canonical⟩ := simulate_papp_fn
    stores state.environments arguments sourceResolved sourceDeclaration
      targetDeclaration arity papSafe under noCredits control blockAt pcBound
      instruction
  have nextEnvironments := canonical.forgetTracedValue state descendant
    (show Lower.Instr.baselineBinderAtom entryValueCount
      (.papp sourceAddress targetArguments) = some (.reg entryValueCount) by rfl)
  refine ⟨sourceRun, targetStep, nextStores,
    state.letOpNext descendant rfl rfl rfl ?_ rfl nextEnvironments⟩
  simp [Lower.Instr.baselineValueDelta]

/-- One captured PAP value is retained identically by the IxIR₁ and IxIR₂
heap primitives. -/
private theorem dupVals_single_simulates_retainShared
    {sourceStore sourceOut : IxIR1.Store}
    {targetStore : Eval.Store} {value : RVal}
    (stores : StoreRel sourceStore targetStore)
    (sourceRun : IxIR1.dupVals sourceStore [value] = .ok sourceOut) :
    ∃ targetOut,
      Eval.retainShared targetStore value = .ok targetOut ∧
        StoreRel sourceOut targetOut := by
  cases value with
  | lit literal =>
      simp [IxIR1.dupVals] at sourceRun
      subst sourceOut
      exact ⟨targetStore, by simp [Eval.retainShared], stores⟩
  | erased =>
      simp [IxIR1.dupVals] at sourceRun
      subst sourceOut
      exact ⟨targetStore, by simp [Eval.retainShared], stores⟩
  | loc location =>
      cases sourceGet : sourceStore.get? location with
      | none => simp [IxIR1.dupVals, sourceGet] at sourceRun
      | some box =>
          cases box with
          | mk world rc node =>
              cases world with
              | unique => simp [IxIR1.dupVals, sourceGet] at sourceRun
              | shared =>
                  have targetGet : targetStore.get? location =
                      some ⟨.shared, rc, node⟩ := by
                    unfold Eval.Store.get?
                    rw [stores.heap]
                    exact sourceGet
                  have sourceEq :
                      sourceOut =
                        (sourceStore.setBox location
                          ⟨.shared, rc + 1, node⟩).rcTick := by
                    simpa [IxIR1.dupVals, sourceGet] using sourceRun.symm
                  subst sourceOut
                  refine ⟨(targetStore.setBox location
                    ⟨.shared, rc + 1, node⟩).rcTick, ?_,
                    (stores.setBox location
                      ⟨.shared, rc + 1, node⟩).rcTick⟩
                  simp [Eval.retainShared, targetGet]

private theorem dupVals_cons_ok_inv {store store' : IxIR1.Store}
    {head : RVal} {tail : List RVal}
    (run : IxIR1.dupVals store (head :: tail) = .ok store') :
    ∃ middle,
      IxIR1.dupVals store [head] = .ok middle ∧
        IxIR1.dupVals middle tail = .ok store' := by
  rw [show head :: tail = [head] ++ tail by rfl, IxIR1.dupVals,
    List.foldlM_append] at run
  change (IxIR1.dupVals store [head] >>= fun middle =>
    IxIR1.dupVals middle tail) = .ok store' at run
  cases middleRun : IxIR1.dupVals store [head] with
  | error error =>
      rw [middleRun] at run
      simp only [bind, Except.bind] at run
      contradiction
  | ok middle =>
      refine ⟨middle, rfl, ?_⟩
      rw [middleRun] at run
      simp only [bind, Except.bind] at run
      exact run

/-- IxIR₁'s PAP-capture duplication loop and IxIR₂'s retain loop produce
exactly related stores for the same ordered value vector. -/
theorem dupVals_simulates_retainSharedMany
    {sourceStore sourceOut : IxIR1.Store}
    {targetStore : Eval.Store} (values : List RVal)
    (stores : StoreRel sourceStore targetStore)
    (sourceRun : IxIR1.dupVals sourceStore values = .ok sourceOut) :
    ∃ targetOut,
      Eval.RetainSharedMany targetStore values.toArray targetOut ∧
        StoreRel sourceOut targetOut := by
  induction values generalizing sourceStore targetStore with
  | nil =>
      change (.ok sourceStore : Except IxIR1.Err IxIR1.Store) =
        .ok sourceOut at sourceRun
      injection sourceRun with sourceEq
      subst sourceOut
      exact ⟨targetStore, Eval.RetainSharedMany.empty targetStore, stores⟩
  | cons value values ih =>
      obtain ⟨sourceMiddle, sourceFirst, sourceRest⟩ :=
        dupVals_cons_ok_inv sourceRun
      obtain ⟨targetMiddle, targetFirst, middleStores⟩ :=
        dupVals_single_simulates_retainShared stores sourceFirst
      obtain ⟨targetOut, targetRest, outStores⟩ :=
        ih middleStores sourceRest
      exact ⟨targetOut,
        Eval.RetainSharedMany.cons targetFirst targetRest, outStores⟩

private theorem PositiveSharedRC.dupValsSingle
    {store out : IxIR1.Store} {value : RVal}
    (positive : PositiveSharedRC store)
    (run : IxIR1.dupVals store [value] = .ok out) :
    PositiveSharedRC out := by
  cases value with
  | lit literal =>
      simp [IxIR1.dupVals] at run
      subst out
      exact positive
  | erased =>
      simp [IxIR1.dupVals] at run
      subst out
      exact positive
  | loc location =>
      cases found : store.get? location with
      | none => simp [IxIR1.dupVals, found] at run
      | some box =>
          cases box with
          | mk world rc node =>
              cases world with
              | unique => simp [IxIR1.dupVals, found] at run
              | shared =>
                  have outEq : out =
                      (store.setBox location
                        ⟨.shared, rc + 1, node⟩).rcTick := by
                    simpa [IxIR1.dupVals, found] using run.symm
                  subst out
                  have updated : PositiveSharedRC
                      (store.setBox location
                        ⟨.shared, rc + 1, node⟩) := by
                    intro other otherBox otherFound otherShared
                    exact positive.setRc
                      (location := location)
                      (box := (⟨.shared, rc, node⟩ : IxIR1.NodeBox))
                      (newRC := rc + 1) found (Nat.zero_lt_succ rc)
                      otherFound otherShared
                  intro other otherBox otherFound otherShared
                  exact PositiveSharedRC.rcTick updated otherFound otherShared

/-- Retaining a finite PAP capture preserves positive refcounts for every
live shared node. -/
theorem PositiveSharedRC.dupVals {store out : IxIR1.Store}
    (positive : PositiveSharedRC store) (values : List RVal)
    (run : IxIR1.dupVals store values = .ok out) :
    PositiveSharedRC out := by
  induction values generalizing store with
  | nil =>
      change (.ok store : Except IxIR1.Err IxIR1.Store) = .ok out at run
      injection run with equal
      subst out
      exact positive
  | cons value values ih =>
      obtain ⟨middle, first, rest⟩ := dupVals_cons_ok_inv run
      exact ih (positive.dupValsSingle first) rest

/-- The heap preparation common to every shared-PAP application branch.
IxIR₁'s ordered capture duplication and consuming PAP drop determine an exact
IxIR₂ retain loop, sufficient heap budget, release result, and both
intermediate store relations. -/
theorem simulate_apply_pap_prepare
    {sourceContext : IxIR1.Ctx} {sourceFuel location : Nat}
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {targetStore : Eval.Store} {captured : Array RVal}
    (stores : StoreRel sourceStore targetStore)
    (positive : PositiveSharedRC sourceStore)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext sourceFuel sourceRetained
      (.loc location) = .ok sourceReleased) :
    ∃ (targetRetained targetReleased : Eval.Store) (targetHeapFuel : Nat),
      Eval.RetainSharedMany targetStore captured targetRetained ∧
        StoreRel sourceRetained targetRetained ∧
        Eval.releaseSharedWork targetHeapFuel targetRetained [.loc location] =
          .ok (targetReleased, 0) ∧
        StoreRel sourceReleased targetReleased := by
  obtain ⟨targetRetained, targetRetain, retainedStores⟩ :=
    dupVals_simulates_retainSharedMany captured.toList stores sourceRetain
  have targetRetain' :
      Eval.RetainSharedMany targetStore captured targetRetained := by
    simpa using targetRetain
  have retainedPositive : PositiveSharedRC sourceRetained := by
    intro retainedLocation retainedBox retainedGet retainedShared
    exact positive.dupVals captured.toList sourceRetain retainedGet
      retainedShared
  obtain ⟨targetHeapFuel, targetReleased, targetRelease, releasedStores,
      _⟩ :=
    dropVal_simulates_releaseSharedWork retainedPositive retainedStores
      sourceRelease
  exact ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain',
    retainedStores, targetRelease, releasedStores⟩

/-- Direct simulation of the erased `applyGo` branch used after an
`applyMore` return.  Releasing the residual source arguments determines an
exact target release budget and immediate erased resumption. -/
theorem simulate_applyGo_erased
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {sourceStore sourceReleased : IxIR1.Store}
    {targetStore : Eval.Store} {values : List RVal}
    {resume : Eval.Frame} {stack : List Eval.Continuation}
    (positive : PositiveSharedRC sourceStore)
    (stores : StoreRel sourceStore targetStore)
    (sourceRelease : IxIR1.dropMany sourceContext sourceFuel sourceStore
      values = .ok sourceReleased) :
    ∃ (targetHeapFuel : Nat) (targetReleased : Eval.Store),
      IxIR1.applyGo sourceContext (sourceFuel + 1) sourceStore .erased values =
          .ok (sourceReleased, .erased) ∧
        Eval.ApplyTransfer context interpretation targetStore targetHeapFuel
          .erased values.toArray resume stack
          { store := targetReleased
            heapFuel := 0
            control := .running
              { resume with values := resume.values.push .erased } stack } ∧
        StoreRel sourceReleased targetReleased ∧
        PositiveSharedRC sourceReleased := by
  obtain ⟨targetHeapFuel, targetReleased, targetRelease, releasedStores,
      releasedPositive⟩ :=
    dropMany_simulates_releaseSharedWork positive stores sourceRelease
  have transferred := Eval.ApplyTransfer.erased
    (context := context) (interpretation := interpretation)
    (resume := resume) (stack := stack) (by simpa using targetRelease)
  refine ⟨targetHeapFuel, targetReleased, ?_, transferred, releasedStores,
    releasedPositive⟩
  rw [IxIR1.applyGo.eq_def]
  dsimp only
  rw [sourceRelease]
  rfl

/-- Direct simulation of the under-saturated PAP `applyGo` branch.  This is
the return-time counterpart of `simulate_apply_pap_under`: it starts from an
already resolved function value and residual value list, as supplied by an
`applyMore` continuation. -/
theorem simulate_applyGo_pap_under
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {targetStore : Eval.Store} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    {captured : Array RVal} {values : List RVal}
    {resume : Eval.Frame} {stack : List Eval.Continuation}
    (stores : StoreRel sourceStore targetStore)
    (positive : PositiveSharedRC sourceStore)
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext sourceFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalUnder : (captured.toList ++ values).length < arity) :
    let pap := IxIR1.Node.papN address arity (captured ++ values.toArray)
    let sourceAllocation := sourceReleased.allocNode .shared pap
    ∃ (targetRetained targetReleased : Eval.Store) (targetHeapFuel : Nat),
      Eval.RetainSharedMany targetStore captured targetRetained ∧
        StoreRel sourceRetained targetRetained ∧
        Eval.releaseSharedWork targetHeapFuel targetRetained [.loc location] =
          .ok (targetReleased, 0) ∧
        StoreRel sourceReleased targetReleased ∧
        let targetAllocation := targetReleased.allocNode .shared pap
        IxIR1.applyGo sourceContext (sourceFuel + 1) sourceStore
            (.loc location) values =
            .ok (sourceAllocation.1, .loc sourceAllocation.2) ∧
          Eval.ApplyTransfer context interpretation targetStore targetHeapFuel
            (.loc location) values.toArray resume stack
            { store := targetAllocation.1
              heapFuel := 0
              control := .running
                { resume with
                  values := resume.values.push (.loc sourceAllocation.2) }
                stack } ∧
          StoreRel sourceAllocation.1 targetAllocation.1 := by
  dsimp only
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      retainedStores, targetRelease, releasedStores⟩ :=
    simulate_apply_pap_prepare stores positive sourceRetain sourceRelease
  have targetGet : targetStore.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have targetUnder : (captured ++ values.toArray).size < arity := by
    simpa using totalUnder
  have transferred := Eval.ApplyTransfer.papUnder
    (context := context) (interpretation := interpretation)
    (resume := resume) (stack := stack) targetGet shared node capturedUnder
      targetRetain targetRelease targetUnder
  let pap := IxIR1.Node.papN address arity (captured ++ values.toArray)
  let sourceAllocation := sourceReleased.allocNode .shared pap
  let targetAllocation := targetReleased.allocNode .shared pap
  have locationEq : targetAllocation.2 = sourceAllocation.2 := by
    exact releasedStores.alloc_location .shared pap
  dsimp only at transferred
  dsimp only [targetAllocation, sourceAllocation, pap] at locationEq
  rw [locationEq] at transferred
  have sourceRun :
      IxIR1.applyGo sourceContext (sourceFuel + 1) sourceStore
          (.loc location) values =
          .ok (sourceAllocation.1, .loc sourceAllocation.2) := by
    rw [IxIR1.applyGo.eq_def]
    dsimp only
    rw [sourceGet]
    simp only
    rw [node]
    simp only
    rw [sourceRetain]
    simp only [bind, Except.bind]
    rw [sourceRelease]
    simp only
    rw [if_pos totalUnder]
    have payloadEq :
        (captured.toList ++ values).toArray = captured ++ values.toArray := by
      apply Array.toList_inj.mp
      simp
    rw [payloadEq]
  exact ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
    retainedStores, targetRelease, releasedStores, sourceRun,
    by simpa [targetAllocation, sourceAllocation, pap] using transferred,
    releasedStores.alloc .shared pap⟩

/-- Direct exact-saturation simulation for a resolved `applyGo`.  It enters
the matched callee under an ordinary resume continuation and exposes the
literal source invocation equation used by recursive `applyMore` simulation. -/
theorem simulate_applyGo_pap_saturated_enter
    {sourceContext : IxIR1.Ctx} {sourceDefinition : IxIR1.FnDef}
    {sourceFuel : Nat} {context : Eval.Context}
    {interpretation : Eval.Interpretation}
    {targetDefinition : Function} {calleeTrace : Lower.FunctionTrace}
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {targetStore : Eval.Store} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {captured : Array RVal} {values : List RVal}
    {resume : Eval.Frame} {stack : List Eval.Continuation}
    (stores : StoreRel sourceStore targetStore)
    (positive : PositiveSharedRC sourceStore)
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext sourceFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalExact : (captured.toList ++ values).length = arity)
    (papArity : arity = sourceDefinition.arity)
    (sourceDeclaration :
      sourceContext.decls address = some (.fn sourceDefinition))
    (sourcePapSafe : sourceDefinition.papSafe = true)
    (targetDeclaration :
      context.declarations address = some (.fn targetDefinition)) :
    let sourceTotal := captured.toList ++ values
    let targetTotal := captured ++ values.toArray
    let calleeFrame : Eval.Frame :=
      { definition := targetDefinition, values := targetTotal }
    ∃ (targetRetained targetReleased : Eval.Store) (targetHeapFuel : Nat),
      Eval.RetainSharedMany targetStore captured targetRetained ∧
        StoreRel sourceRetained targetRetained ∧
        Eval.releaseSharedWork targetHeapFuel targetRetained [.loc location] =
          .ok (targetReleased, 0) ∧
        StoreRel sourceReleased targetReleased ∧
        IxIR1.applyGo sourceContext (sourceFuel + 1) sourceStore
            (.loc location) values =
          IxIR1.invoke sourceContext sourceFuel address sourceTotal
            sourceReleased ∧
        Eval.ApplyTransfer context interpretation targetStore targetHeapFuel
          (.loc location) values.toArray resume stack
          { store := targetReleased
            heapFuel := 0
            control := .running calleeFrame (.resume resume :: stack) } ∧
        CodeStateRel calleeTrace calleeTrace.root sourceTotal.reverse
          calleeFrame := by
  dsimp only
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      retainedStores, targetRelease, releasedStores⟩ :=
    simulate_apply_pap_prepare stores positive sourceRetain sourceRelease
  have targetGet : targetStore.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  let sourceTotal := captured.toList ++ values
  let targetTotal := captured ++ values.toArray
  have totalArrayEq : sourceTotal.toArray = targetTotal := by
    apply Array.toList_inj.mp
    simp [sourceTotal, targetTotal]
  have targetSize : targetTotal.size = arity := by
    simpa [sourceTotal, targetTotal] using totalExact
  have targetPapSafe : targetDefinition.signature.papSafe = true := by
    calc
      targetDefinition.signature.papSafe =
          calleeTrace.generated.signature.papSafe := by
            rw [calleeMatch.generated]
      _ = calleeTrace.source.papSafe := calleeTrace.sourcePapSafe
      _ = sourceDefinition.papSafe := congrArg IxIR1.FnDef.papSafe
        calleeMatch.source
      _ = true := sourcePapSafe
  have targetParamArity :
      targetDefinition.signature.params.size = arity := by
    calc
      targetDefinition.signature.params.size =
          calleeTrace.generated.signature.params.size := by
            rw [calleeMatch.generated]
      _ = calleeTrace.source.arity := calleeTrace.sourceArity
      _ = sourceDefinition.arity := congrArg IxIR1.FnDef.arity
        calleeMatch.source
      _ = arity := papArity.symm
  have suppliedEq : targetTotal.extract 0 arity = targetTotal := by
    rw [← targetSize]
    exact Array.extract_size
  have suppliedArity :
      (targetTotal.extract 0 arity).size =
        targetDefinition.signature.params.size := by
    rw [suppliedEq, targetSize, targetParamArity]
  have targetNonempty : targetDefinition.blocks.isEmpty = false := by
    simpa [calleeMatch.generated] using calleeTrace.generatedNonempty
  have transferred := Eval.ApplyTransfer.papFn
    (context := context) (interpretation := interpretation)
    (resume := resume) (stack := stack) targetGet shared node capturedUnder
      targetRetain targetRelease
      (by simpa [targetTotal] using Nat.le_of_eq targetSize.symm)
      targetDeclaration targetPapSafe suppliedArity targetNonempty
  dsimp only at transferred
  have remainingEmpty :
      (targetTotal.extract arity targetTotal.size).isEmpty = true := by
    simp [Array.isEmpty, Array.size_extract]
    omega
  rw [suppliedEq, remainingEmpty] at transferred
  simp only [if_true] at transferred
  have sourceRun :
      IxIR1.applyGo sourceContext (sourceFuel + 1) sourceStore
          (.loc location) values =
        IxIR1.invoke sourceContext sourceFuel address sourceTotal
          sourceReleased := by
    rw [IxIR1.applyGo.eq_def]
    dsimp only
    rw [sourceGet]
    simp only
    rw [node]
    simp only
    rw [sourceRetain]
    simp only [bind, Except.bind]
    rw [sourceRelease]
    simp only
    rw [if_neg (by omega)]
    rw [if_pos (beq_iff_eq.mpr (by
      simpa [sourceTotal] using totalExact))]
    rw [sourceDeclaration]
    simp [IxIR1.declPapSafe, sourcePapSafe, sourceTotal]
  have entryArity : targetTotal.size = calleeTrace.source.arity := by
    calc
      targetTotal.size = arity := targetSize
      _ = sourceDefinition.arity := papArity
      _ = calleeTrace.source.arity := by rw [calleeMatch.source]
  have calleeState := functionEntryCodeState calleeTrace targetTotal entryArity
  have sourceEnvironment : targetTotal.toList.reverse = sourceTotal.reverse := by
    rw [← totalArrayEq]
  rw [sourceEnvironment] at calleeState
  exact ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
    retainedStores, targetRelease, releasedStores, sourceRun,
    by simpa [targetTotal] using transferred,
    by simpa [calleeMatch.generated, sourceTotal, targetTotal] using calleeState⟩

/-- Direct over-saturation simulation for a resolved `applyGo`.  It enters
the first matched callee under a new `applyMore` continuation and proves that
the retained target suffix is exactly the source residual argument list. -/
theorem simulate_applyGo_pap_over_enter
    {sourceContext : IxIR1.Ctx} {sourceDefinition : IxIR1.FnDef}
    {sourceFuel : Nat} {context : Eval.Context}
    {interpretation : Eval.Interpretation}
    {targetDefinition : Function} {calleeTrace : Lower.FunctionTrace}
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {targetStore : Eval.Store} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {captured : Array RVal} {values : List RVal}
    {resume : Eval.Frame} {stack : List Eval.Continuation}
    (stores : StoreRel sourceStore targetStore)
    (positive : PositiveSharedRC sourceStore)
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext sourceFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalOver : arity < (captured.toList ++ values).length)
    (papArity : arity = sourceDefinition.arity)
    (sourceDeclaration :
      sourceContext.decls address = some (.fn sourceDefinition))
    (sourcePapSafe : sourceDefinition.papSafe = true)
    (targetDeclaration :
      context.declarations address = some (.fn targetDefinition)) :
    let sourceTotal := captured.toList ++ values
    let sourceSupplied := sourceTotal.take arity
    let sourceRemaining := sourceTotal.drop arity
    let targetTotal := captured ++ values.toArray
    let targetSupplied := targetTotal.extract 0 arity
    let targetRemaining := targetTotal.extract arity targetTotal.size
    let calleeFrame : Eval.Frame :=
      { definition := targetDefinition, values := targetSupplied }
    ∃ (targetRetained targetReleased : Eval.Store) (targetHeapFuel : Nat),
      Eval.RetainSharedMany targetStore captured targetRetained ∧
        StoreRel sourceRetained targetRetained ∧
        Eval.releaseSharedWork targetHeapFuel targetRetained [.loc location] =
          .ok (targetReleased, 0) ∧
        StoreRel sourceReleased targetReleased ∧
        IxIR1.applyGo sourceContext (sourceFuel + 1) sourceStore
            (.loc location) values =
          (do
            let (nextStore, result) ←
              IxIR1.invoke sourceContext sourceFuel address sourceSupplied
                sourceReleased
            IxIR1.applyGo sourceContext sourceFuel nextStore result
              sourceRemaining) ∧
        Eval.ApplyTransfer context interpretation targetStore targetHeapFuel
          (.loc location) values.toArray resume stack
          { store := targetReleased
            heapFuel := 0
            control := .running calleeFrame
              (.applyMore targetRemaining resume :: stack) } ∧
        targetRemaining.toList = sourceRemaining ∧
        CodeStateRel calleeTrace calleeTrace.root sourceSupplied.reverse
          calleeFrame := by
  dsimp only
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      retainedStores, targetRelease, releasedStores⟩ :=
    simulate_apply_pap_prepare stores positive sourceRetain sourceRelease
  have targetGet : targetStore.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  let sourceTotal := captured.toList ++ values
  let sourceSupplied := sourceTotal.take arity
  let sourceRemaining := sourceTotal.drop arity
  let targetTotal := captured ++ values.toArray
  let targetSupplied := targetTotal.extract 0 arity
  let targetRemaining := targetTotal.extract arity targetTotal.size
  have totalArrayEq : sourceTotal.toArray = targetTotal := by
    apply Array.toList_inj.mp
    simp [sourceTotal, targetTotal]
  have targetOver : arity < targetTotal.size := by
    simpa [sourceTotal, targetTotal] using totalOver
  have suppliedArrayEq : targetSupplied = sourceSupplied.toArray := by
    calc
      targetSupplied = targetTotal.take arity := Array.take_eq_extract.symm
      _ = sourceTotal.toArray.take arity := by rw [totalArrayEq]
      _ = sourceSupplied.toArray := List.take_toArray
  have remainingArrayEq : targetRemaining = sourceRemaining.toArray := by
    calc
      targetRemaining = targetTotal.extract arity := rfl
      _ = sourceTotal.toArray.extract arity := by rw [totalArrayEq]
      _ = sourceRemaining.toArray := List.toArray_drop.symm
  have remainingListEq : targetRemaining.toList = sourceRemaining := by
    rw [remainingArrayEq]
  have targetPapSafe : targetDefinition.signature.papSafe = true := by
    calc
      targetDefinition.signature.papSafe =
          calleeTrace.generated.signature.papSafe := by
            rw [calleeMatch.generated]
      _ = calleeTrace.source.papSafe := calleeTrace.sourcePapSafe
      _ = sourceDefinition.papSafe := congrArg IxIR1.FnDef.papSafe
        calleeMatch.source
      _ = true := sourcePapSafe
  have targetParamArity :
      targetDefinition.signature.params.size = arity := by
    calc
      targetDefinition.signature.params.size =
          calleeTrace.generated.signature.params.size := by
            rw [calleeMatch.generated]
      _ = calleeTrace.source.arity := calleeTrace.sourceArity
      _ = sourceDefinition.arity := congrArg IxIR1.FnDef.arity
        calleeMatch.source
      _ = arity := papArity.symm
  have suppliedSize : targetSupplied.size = arity := by
    simp [targetSupplied, Array.size_extract]
    omega
  have suppliedArity :
      targetSupplied.size = targetDefinition.signature.params.size := by
    rw [suppliedSize, targetParamArity]
  have targetNonempty : targetDefinition.blocks.isEmpty = false := by
    simpa [calleeMatch.generated] using calleeTrace.generatedNonempty
  have transferred := Eval.ApplyTransfer.papFn
    (context := context) (interpretation := interpretation)
    (resume := resume) (stack := stack) targetGet shared node capturedUnder
      targetRetain targetRelease (Nat.le_of_lt targetOver) targetDeclaration
      targetPapSafe suppliedArity targetNonempty
  dsimp only at transferred
  have remainingNonempty : targetRemaining.isEmpty = false := by
    simp [Array.isEmpty, targetRemaining, Array.size_extract]
    omega
  rw [remainingNonempty] at transferred
  have sourceRun :
      IxIR1.applyGo sourceContext (sourceFuel + 1) sourceStore
          (.loc location) values =
        (do
          let (nextStore, result) ←
            IxIR1.invoke sourceContext sourceFuel address sourceSupplied
              sourceReleased
          IxIR1.applyGo sourceContext sourceFuel nextStore result
            sourceRemaining) := by
    rw [IxIR1.applyGo.eq_def]
    dsimp only
    rw [sourceGet]
    simp only
    rw [node]
    simp only
    rw [sourceRetain]
    simp only [bind, Except.bind]
    rw [sourceRelease]
    simp only
    rw [if_neg (by omega)]
    rw [if_neg (by
      intro exactGuard
      have exactEq := beq_iff_eq.mp exactGuard
      omega)]
    rw [sourceDeclaration]
    simp [IxIR1.declPapSafe, sourcePapSafe, sourceTotal, sourceSupplied,
      sourceRemaining]
  have entryArity : targetSupplied.size = calleeTrace.source.arity := by
    calc
      targetSupplied.size = arity := suppliedSize
      _ = sourceDefinition.arity := papArity
      _ = calleeTrace.source.arity := by rw [calleeMatch.source]
  have calleeState := functionEntryCodeState calleeTrace targetSupplied
    entryArity
  have sourceEnvironment :
      targetSupplied.toList.reverse = sourceSupplied.reverse := by
    rw [suppliedArrayEq]
  rw [sourceEnvironment] at calleeState
  have calleeState' : CodeStateRel calleeTrace calleeTrace.root
      sourceSupplied.reverse
      { definition := targetDefinition, values := targetSupplied } := by
    simpa only [calleeMatch.generated] using calleeState
  exact ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
    retainedStores, targetRelease, releasedStores, sourceRun,
    by simpa [targetTotal, targetSupplied, targetRemaining] using transferred,
    remainingListEq, calleeState'⟩

/-- The under-saturated dynamic-application branch is simulated without an
opaque target heap witness.  IxIR₁'s capture duplication and PAP release
derive the exact IxIR₂ retain/release work, after which both sides allocate
the same longer PAP at the same fresh location. -/
theorem simulate_apply_pap_under
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat} {context : Eval.Context}
    {interpretation : Eval.Interpretation}
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {targetStore : Eval.Store} {source : List RVal}
    {sourceFunction : IxIR1.Atom}
    {sourceArguments : Array IxIR1.Atom}
    {location : Nat} {box : IxIR1.NodeBox}
    {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    {captured : Array RVal} {values : List RVal}
    {resume : Eval.Frame} {stack : List Eval.Continuation}
    (stores : StoreRel sourceStore targetStore)
    (positive : PositiveSharedRC sourceStore)
    (functionResolved :
      IxIR1.resolveAtom source sourceFunction = .ok (.loc location))
    (argumentsResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext sourceFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalUnder : (captured.toList ++ values).length < arity) :
    let pap := IxIR1.Node.papN address arity (captured ++ values.toArray)
    let sourceAllocation := sourceReleased.allocNode .shared pap
    ∃ (targetRetained targetReleased : Eval.Store) (targetHeapFuel : Nat),
      Eval.RetainSharedMany targetStore captured targetRetained ∧
        StoreRel sourceRetained targetRetained ∧
        Eval.releaseSharedWork targetHeapFuel targetRetained [.loc location] =
          .ok (targetReleased, 0) ∧
        StoreRel sourceReleased targetReleased ∧
        let targetAllocation := targetReleased.allocNode .shared pap
        IxIR1.runOp sourceContext (sourceFuel + 2) sourceCurrent sourceStore
            source (.apply sourceFunction sourceArguments) =
            .ok (sourceAllocation.1, .loc sourceAllocation.2) ∧
          Eval.ApplyTransfer context interpretation targetStore targetHeapFuel
            (.loc location) values.toArray resume stack
            { store := targetAllocation.1
              heapFuel := 0
              control := .running
                { resume with
                  values := resume.values.push (.loc sourceAllocation.2) }
                stack } ∧
          StoreRel sourceAllocation.1 targetAllocation.1 := by
  dsimp only
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain',
      retainedStores, targetRelease, releasedStores⟩ :=
    simulate_apply_pap_prepare stores positive sourceRetain sourceRelease
  have targetGet : targetStore.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have targetUnder : (captured ++ values.toArray).size < arity := by
    simpa using totalUnder
  have transferred := Eval.ApplyTransfer.papUnder
    (context := context) (interpretation := interpretation)
    (resume := resume) (stack := stack)
    targetGet shared node capturedUnder targetRetain' targetRelease targetUnder
  let pap := IxIR1.Node.papN address arity (captured ++ values.toArray)
  let sourceAllocation := sourceReleased.allocNode .shared pap
  let targetAllocation := targetReleased.allocNode .shared pap
  have locationEq : targetAllocation.2 = sourceAllocation.2 := by
    exact releasedStores.alloc_location .shared pap
  dsimp only at transferred
  dsimp only [targetAllocation, sourceAllocation, pap] at locationEq
  rw [locationEq] at transferred
  have sourceRun :
      IxIR1.runOp sourceContext (sourceFuel + 2) sourceCurrent sourceStore
          source (.apply sourceFunction sourceArguments) =
          .ok (sourceAllocation.1, .loc sourceAllocation.2) := by
    rw [IxIR1.runOp.eq_def]
    dsimp only
    rw [functionResolved]
    simp only [bind, Except.bind]
    rw [argumentsResolved]
    simp only
    rw [IxIR1.applyGo.eq_def]
    dsimp only
    rw [sourceGet]
    simp only
    rw [node]
    simp only
    rw [sourceRetain]
    simp only [bind, Except.bind]
    rw [sourceRelease]
    simp only
    rw [if_pos totalUnder]
    have payloadEq :
        (captured.toList ++ values).toArray = captured ++ values.toArray := by
      apply Array.toList_inj.mp
      simp
    rw [payloadEq]
  exact ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain',
    retainedStores, targetRelease, releasedStores, sourceRun,
    by simpa [targetAllocation, sourceAllocation, pap] using transferred,
    releasedStores.alloc .shared pap⟩

/-- Exact saturation exposes the literal IxIR₁ invocation equation while the
IxIR₂ dispatcher enters the matched callee root under an ordinary resume
continuation.  PAP capture retains and the consuming old-PAP release are
derived from the source heap operations rather than supplied as target
witnesses. -/
theorem simulate_apply_pap_saturated_enter
    {sourceContext : IxIR1.Ctx}
    {sourceCurrent sourceDefinition : IxIR1.FnDef}
    {sourceFuel : Nat} {context : Eval.Context}
    {interpretation : Eval.Interpretation}
    {targetDefinition : Function} {calleeTrace : Lower.FunctionTrace}
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {targetStore : Eval.Store} {source : List RVal}
    {sourceFunction : IxIR1.Atom}
    {sourceArguments : Array IxIR1.Atom}
    {location : Nat} {box : IxIR1.NodeBox}
    {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {captured : Array RVal} {values : List RVal}
    {resume : Eval.Frame} {stack : List Eval.Continuation}
    (stores : StoreRel sourceStore targetStore)
    (positive : PositiveSharedRC sourceStore)
    (functionResolved :
      IxIR1.resolveAtom source sourceFunction = .ok (.loc location))
    (argumentsResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext sourceFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalExact : (captured.toList ++ values).length = arity)
    (papArity : arity = sourceDefinition.arity)
    (sourceDeclaration :
      sourceContext.decls address = some (.fn sourceDefinition))
    (sourcePapSafe : sourceDefinition.papSafe = true)
    (targetDeclaration :
      context.declarations address = some (.fn targetDefinition)) :
    let sourceTotal := captured.toList ++ values
    let targetTotal := captured ++ values.toArray
    let calleeFrame : Eval.Frame :=
      { definition := targetDefinition, values := targetTotal }
    ∃ (targetRetained targetReleased : Eval.Store) (targetHeapFuel : Nat),
      Eval.RetainSharedMany targetStore captured targetRetained ∧
        StoreRel sourceRetained targetRetained ∧
        Eval.releaseSharedWork targetHeapFuel targetRetained [.loc location] =
          .ok (targetReleased, 0) ∧
        StoreRel sourceReleased targetReleased ∧
        IxIR1.runOp sourceContext (sourceFuel + 2) sourceCurrent sourceStore
            source (.apply sourceFunction sourceArguments) =
          IxIR1.invoke sourceContext sourceFuel address sourceTotal
            sourceReleased ∧
        Eval.ApplyTransfer context interpretation targetStore targetHeapFuel
          (.loc location) values.toArray resume stack
          { store := targetReleased
            heapFuel := 0
            control := .running calleeFrame (.resume resume :: stack) } ∧
        CodeStateRel calleeTrace calleeTrace.root sourceTotal.reverse
          calleeFrame := by
  dsimp only
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      retainedStores, targetRelease, releasedStores⟩ :=
    simulate_apply_pap_prepare stores positive sourceRetain sourceRelease
  have targetGet : targetStore.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  let sourceTotal := captured.toList ++ values
  let targetTotal := captured ++ values.toArray
  have totalArrayEq : sourceTotal.toArray = targetTotal := by
    apply Array.toList_inj.mp
    simp [sourceTotal, targetTotal]
  have targetSize : targetTotal.size = arity := by
    simpa [sourceTotal, targetTotal] using totalExact
  have targetPapSafe : targetDefinition.signature.papSafe = true := by
    calc
      targetDefinition.signature.papSafe =
          calleeTrace.generated.signature.papSafe := by
            rw [calleeMatch.generated]
      _ = calleeTrace.source.papSafe := calleeTrace.sourcePapSafe
      _ = sourceDefinition.papSafe := congrArg IxIR1.FnDef.papSafe
        calleeMatch.source
      _ = true := sourcePapSafe
  have targetParamArity :
      targetDefinition.signature.params.size = arity := by
    calc
      targetDefinition.signature.params.size =
          calleeTrace.generated.signature.params.size := by
            rw [calleeMatch.generated]
      _ = calleeTrace.source.arity := calleeTrace.sourceArity
      _ = sourceDefinition.arity := congrArg IxIR1.FnDef.arity
        calleeMatch.source
      _ = arity := papArity.symm
  have suppliedEq : targetTotal.extract 0 arity = targetTotal := by
    rw [← targetSize]
    exact Array.extract_size
  have suppliedArity :
      (targetTotal.extract 0 arity).size =
        targetDefinition.signature.params.size := by
    rw [suppliedEq, targetSize, targetParamArity]
  have targetNonempty : targetDefinition.blocks.isEmpty = false := by
    simpa [calleeMatch.generated] using calleeTrace.generatedNonempty
  have transferred := Eval.ApplyTransfer.papFn
    (context := context) (interpretation := interpretation)
    (resume := resume) (stack := stack)
    targetGet shared node capturedUnder targetRetain targetRelease
      (by simpa [targetTotal] using Nat.le_of_eq targetSize.symm)
      targetDeclaration targetPapSafe suppliedArity
      targetNonempty
  dsimp only at transferred
  have remainingEmpty :
      (targetTotal.extract arity targetTotal.size).isEmpty = true := by
    simp [Array.isEmpty, Array.size_extract]
    omega
  rw [suppliedEq, remainingEmpty] at transferred
  simp only [if_true] at transferred
  have sourceRun :
      IxIR1.runOp sourceContext (sourceFuel + 2) sourceCurrent sourceStore
          source (.apply sourceFunction sourceArguments) =
        IxIR1.invoke sourceContext sourceFuel address sourceTotal
          sourceReleased := by
    rw [IxIR1.runOp.eq_def]
    dsimp only
    rw [functionResolved]
    simp only [bind, Except.bind]
    rw [argumentsResolved]
    simp only
    rw [IxIR1.applyGo.eq_def]
    dsimp only
    rw [sourceGet]
    simp only
    rw [node]
    simp only
    rw [sourceRetain]
    simp only [bind, Except.bind]
    rw [sourceRelease]
    simp only
    rw [if_neg (by omega)]
    rw [if_pos (beq_iff_eq.mpr (by simpa [sourceTotal] using totalExact))]
    rw [sourceDeclaration]
    simp [IxIR1.declPapSafe, sourcePapSafe, sourceTotal]
  have entryArity : targetTotal.size = calleeTrace.source.arity := by
    calc
      targetTotal.size = arity := targetSize
      _ = sourceDefinition.arity := papArity
      _ = calleeTrace.source.arity := by rw [calleeMatch.source]
  have calleeState := functionEntryCodeState calleeTrace targetTotal entryArity
  have sourceEnvironment : targetTotal.toList.reverse = sourceTotal.reverse := by
    rw [← totalArrayEq]
  rw [sourceEnvironment] at calleeState
  exact ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
    retainedStores, targetRelease, releasedStores, sourceRun,
    by simpa [targetTotal] using transferred,
    by simpa [calleeMatch.generated, sourceTotal, targetTotal] using calleeState⟩

/-- Over-application exposes the IxIR₁ invoke-then-apply equation and enters
the same matched target callee under an explicit `applyMore` continuation.
The residual target vector is proved to be exactly the source `drop` suffix,
which is the induction hand-off when the callee later returns. -/
theorem simulate_apply_pap_over_enter
    {sourceContext : IxIR1.Ctx}
    {sourceCurrent sourceDefinition : IxIR1.FnDef}
    {sourceFuel : Nat} {context : Eval.Context}
    {interpretation : Eval.Interpretation}
    {targetDefinition : Function} {calleeTrace : Lower.FunctionTrace}
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {targetStore : Eval.Store} {source : List RVal}
    {sourceFunction : IxIR1.Atom}
    {sourceArguments : Array IxIR1.Atom}
    {location : Nat} {box : IxIR1.NodeBox}
    {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {captured : Array RVal} {values : List RVal}
    {resume : Eval.Frame} {stack : List Eval.Continuation}
    (stores : StoreRel sourceStore targetStore)
    (positive : PositiveSharedRC sourceStore)
    (functionResolved :
      IxIR1.resolveAtom source sourceFunction = .ok (.loc location))
    (argumentsResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext sourceFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalOver : arity < (captured.toList ++ values).length)
    (papArity : arity = sourceDefinition.arity)
    (sourceDeclaration :
      sourceContext.decls address = some (.fn sourceDefinition))
    (sourcePapSafe : sourceDefinition.papSafe = true)
    (targetDeclaration :
      context.declarations address = some (.fn targetDefinition)) :
    let sourceTotal := captured.toList ++ values
    let sourceSupplied := sourceTotal.take arity
    let sourceRemaining := sourceTotal.drop arity
    let targetTotal := captured ++ values.toArray
    let targetSupplied := targetTotal.extract 0 arity
    let targetRemaining := targetTotal.extract arity targetTotal.size
    let calleeFrame : Eval.Frame :=
      { definition := targetDefinition, values := targetSupplied }
    ∃ (targetRetained targetReleased : Eval.Store) (targetHeapFuel : Nat),
      Eval.RetainSharedMany targetStore captured targetRetained ∧
        StoreRel sourceRetained targetRetained ∧
        Eval.releaseSharedWork targetHeapFuel targetRetained [.loc location] =
          .ok (targetReleased, 0) ∧
        StoreRel sourceReleased targetReleased ∧
        IxIR1.runOp sourceContext (sourceFuel + 2) sourceCurrent sourceStore
            source (.apply sourceFunction sourceArguments) =
          (do
            let (nextStore, result) ←
              IxIR1.invoke sourceContext sourceFuel address sourceSupplied
                sourceReleased
            IxIR1.applyGo sourceContext sourceFuel nextStore result
              sourceRemaining) ∧
        Eval.ApplyTransfer context interpretation targetStore targetHeapFuel
          (.loc location) values.toArray resume stack
          { store := targetReleased
            heapFuel := 0
            control := .running calleeFrame
              (.applyMore targetRemaining resume :: stack) } ∧
        targetRemaining.toList = sourceRemaining ∧
        CodeStateRel calleeTrace calleeTrace.root sourceSupplied.reverse
          calleeFrame := by
  dsimp only
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      retainedStores, targetRelease, releasedStores⟩ :=
    simulate_apply_pap_prepare stores positive sourceRetain sourceRelease
  have targetGet : targetStore.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  let sourceTotal := captured.toList ++ values
  let sourceSupplied := sourceTotal.take arity
  let sourceRemaining := sourceTotal.drop arity
  let targetTotal := captured ++ values.toArray
  let targetSupplied := targetTotal.extract 0 arity
  let targetRemaining := targetTotal.extract arity targetTotal.size
  have totalArrayEq : sourceTotal.toArray = targetTotal := by
    apply Array.toList_inj.mp
    simp [sourceTotal, targetTotal]
  have targetOver : arity < targetTotal.size := by
    simpa [sourceTotal, targetTotal] using totalOver
  have suppliedArrayEq : targetSupplied = sourceSupplied.toArray := by
    calc
      targetSupplied = targetTotal.take arity := Array.take_eq_extract.symm
      _ = sourceTotal.toArray.take arity := by rw [totalArrayEq]
      _ = sourceSupplied.toArray := List.take_toArray
  have remainingArrayEq : targetRemaining = sourceRemaining.toArray := by
    calc
      targetRemaining = targetTotal.extract arity := rfl
      _ = sourceTotal.toArray.extract arity := by rw [totalArrayEq]
      _ = sourceRemaining.toArray := List.toArray_drop.symm
  have remainingListEq : targetRemaining.toList = sourceRemaining := by
    rw [remainingArrayEq]
  have targetPapSafe : targetDefinition.signature.papSafe = true := by
    calc
      targetDefinition.signature.papSafe =
          calleeTrace.generated.signature.papSafe := by
            rw [calleeMatch.generated]
      _ = calleeTrace.source.papSafe := calleeTrace.sourcePapSafe
      _ = sourceDefinition.papSafe := congrArg IxIR1.FnDef.papSafe
        calleeMatch.source
      _ = true := sourcePapSafe
  have targetParamArity :
      targetDefinition.signature.params.size = arity := by
    calc
      targetDefinition.signature.params.size =
          calleeTrace.generated.signature.params.size := by
            rw [calleeMatch.generated]
      _ = calleeTrace.source.arity := calleeTrace.sourceArity
      _ = sourceDefinition.arity := congrArg IxIR1.FnDef.arity
        calleeMatch.source
      _ = arity := papArity.symm
  have suppliedSize : targetSupplied.size = arity := by
    simp [targetSupplied, Array.size_extract]
    omega
  have suppliedArity :
      targetSupplied.size = targetDefinition.signature.params.size := by
    rw [suppliedSize, targetParamArity]
  have targetNonempty : targetDefinition.blocks.isEmpty = false := by
    simpa [calleeMatch.generated] using calleeTrace.generatedNonempty
  have transferred := Eval.ApplyTransfer.papFn
    (context := context) (interpretation := interpretation)
    (resume := resume) (stack := stack)
    targetGet shared node capturedUnder targetRetain targetRelease
      (Nat.le_of_lt targetOver) targetDeclaration targetPapSafe suppliedArity
      targetNonempty
  dsimp only at transferred
  have remainingNonempty : targetRemaining.isEmpty = false := by
    simp [Array.isEmpty, targetRemaining, Array.size_extract]
    omega
  rw [remainingNonempty] at transferred
  have sourceRun :
      IxIR1.runOp sourceContext (sourceFuel + 2) sourceCurrent sourceStore
          source (.apply sourceFunction sourceArguments) =
        (do
          let (nextStore, result) ←
            IxIR1.invoke sourceContext sourceFuel address sourceSupplied
              sourceReleased
          IxIR1.applyGo sourceContext sourceFuel nextStore result
            sourceRemaining) := by
    rw [IxIR1.runOp.eq_def]
    dsimp only
    rw [functionResolved]
    simp only [bind, Except.bind]
    rw [argumentsResolved]
    simp only
    rw [IxIR1.applyGo.eq_def]
    dsimp only
    rw [sourceGet]
    simp only
    rw [node]
    simp only
    rw [sourceRetain]
    simp only [bind, Except.bind]
    rw [sourceRelease]
    simp only
    rw [if_neg (by omega)]
    rw [if_neg (by
      intro exactGuard
      have exactEq := beq_iff_eq.mp exactGuard
      omega)]
    rw [sourceDeclaration]
    simp [IxIR1.declPapSafe, sourcePapSafe, sourceTotal, sourceSupplied,
      sourceRemaining]
  have entryArity : targetSupplied.size = calleeTrace.source.arity := by
    calc
      targetSupplied.size = arity := suppliedSize
      _ = sourceDefinition.arity := papArity
      _ = calleeTrace.source.arity := by rw [calleeMatch.source]
  have calleeState := functionEntryCodeState calleeTrace targetSupplied
    entryArity
  have sourceEnvironment :
      targetSupplied.toList.reverse = sourceSupplied.reverse := by
    rw [suppliedArrayEq]
  rw [sourceEnvironment] at calleeState
  have calleeState' : CodeStateRel calleeTrace calleeTrace.root
      sourceSupplied.reverse
      { definition := targetDefinition, values := targetSupplied } := by
    simpa only [calleeMatch.generated] using calleeState
  exact ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
    retainedStores, targetRelease, releasedStores, sourceRun,
    by simpa [targetTotal, targetSupplied, targetRemaining] using transferred,
    remainingListEq,
    calleeState'⟩

/-- Trace-facing dynamic-application dispatch.  The checked derivation
supplies both translated operand families and the exact instruction
coordinate.  `ApplyTransfer` then selects the evaluator's immediate, exact
call, or over-application path while the second conclusion retains the exact
caller continuation state established whenever that path ultimately resumes
with a value. -/
theorem simulate_traced_apply_transfer_state
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine target : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceFunction : IxIR1.Atom} {targetFunction : Atom}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next))
    {source : List RVal} {function : RVal} {values : List RVal}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next) source frame)
    (sourceFunctionResolved :
      IxIR1.resolveAtom source sourceFunction = .ok function)
    (sourceArgumentsResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack)
    (transferred : Eval.ApplyTransfer context interpretation machine.store
      machine.heapFuel function values.toArray
      { frame with pc := frame.pc + 1 } stack target) :
    Eval.Step context interpretation machine target ∧
      ∀ value,
        CodeStateRel functionTrace next (value :: source)
          { frame with
            pc := frame.pc + 1
            values := frame.values.push value } := by
  have operationSyntax := functionTrace.descendantOperationSyntax descendant
  change Lower.InputMap.translateAtom input sourceFunction =
      some targetFunction ∧
    Lower.InputMap.translateAtoms input sourceArguments =
      some targetArguments at operationSyntax
  obtain ⟨functionTranslated, argumentsTranslated⟩ := operationSyntax
  have arguments : AtomsRel input sourceArguments targetArguments :=
    atomsRel_of_translateAtoms argumentsTranslated
  have targetFunctionResolved :
      Eval.resolveAtom frame.values targetFunction = .ok function :=
    resolveAtom_of_envRel state.environments functionTranslated
      sourceFunctionResolved
  have targetArgumentsResolved :
      Eval.resolveAtoms frame.values targetArguments = .ok values.toArray :=
    resolveAtoms_of_envRel state.environments arguments
      sourceArgumentsResolved
  obtain ⟨blockAt, pcBound, instructionAt⟩ := state.instructionAt descendant
  have instruction :
      next.headBlock.2.instructions[frame.pc] =
        .apply targetFunction targetArguments :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  constructor
  · exact Eval.Step.apply control blockAt pcBound instruction noCredits
      targetFunctionResolved targetArgumentsResolved transferred
  · intro value
    exact state.letOpValueNext descendant rfl rfl value

/-- Trace-facing exact saturation combines the source invocation equation,
derived PAP heap preparation, the emitted `apply` step, exact callee-root
state, and the caller state that an ordinary resumed return must establish. -/
theorem simulate_traced_apply_pap_saturated_enter_state
    {sourceContext : IxIR1.Ctx}
    {sourceCurrent sourceDefinition : IxIR1.FnDef}
    {sourceFuel : Nat} {context : Eval.Context}
    {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {callerTrace calleeTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceFunction : IxIR1.Atom} {targetFunction : Atom}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : callerTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next))
    {targetDefinition : Function}
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {source : List RVal} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {captured : Array RVal} {values : List RVal}
    (state : CodeStateRel callerTrace
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next) source frame)
    (stores : StoreRel sourceStore machine.store)
    (positive : PositiveSharedRC sourceStore)
    (functionResolved :
      IxIR1.resolveAtom source sourceFunction = .ok (.loc location))
    (argumentsResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext sourceFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalExact : (captured.toList ++ values).length = arity)
    (papArity : arity = sourceDefinition.arity)
    (sourceDeclaration :
      sourceContext.decls address = some (.fn sourceDefinition))
    (sourcePapSafe : sourceDefinition.papSafe = true)
    (targetDeclaration :
      context.declarations address = some (.fn targetDefinition))
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let sourceTotal := captured.toList ++ values
    let targetTotal := captured ++ values.toArray
    let resume : Eval.Frame := { frame with pc := frame.pc + 1 }
    let calleeFrame : Eval.Frame :=
      { definition := targetDefinition, values := targetTotal }
    let targetMachine : Eval.Machine :=
      { store := machine.store
        heapFuel := 0
        control := .running calleeFrame (.resume resume :: stack) }
    ∃ (targetRetained targetReleased : Eval.Store) (targetHeapFuel : Nat),
      Eval.RetainSharedMany machine.store captured targetRetained ∧
        StoreRel sourceRetained targetRetained ∧
        Eval.releaseSharedWork targetHeapFuel targetRetained [.loc location] =
          .ok (targetReleased, 0) ∧
        StoreRel sourceReleased targetReleased ∧
        IxIR1.runOp sourceContext (sourceFuel + 2) sourceCurrent sourceStore
            source (.apply sourceFunction sourceArguments) =
          IxIR1.invoke sourceContext sourceFuel address sourceTotal
            sourceReleased ∧
        Eval.Step context interpretation
          { machine with heapFuel := targetHeapFuel }
          { targetMachine with store := targetReleased } ∧
        CodeStateRel calleeTrace calleeTrace.root sourceTotal.reverse
          calleeFrame ∧
        ∀ value,
          CodeStateRel callerTrace next (value :: source)
            { frame with
              pc := frame.pc + 1
              values := frame.values.push value } := by
  dsimp only
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      retainedStores, targetRelease, releasedStores, sourceRun, transferred,
      calleeState⟩ :=
    simulate_apply_pap_saturated_enter
      (resume := { frame with pc := frame.pc + 1 }) calleeMatch stores positive
      functionResolved argumentsResolved sourceGet shared node capturedUnder
      sourceRetain sourceRelease totalExact papArity sourceDeclaration
      sourcePapSafe targetDeclaration
  have beforeControl :
      ({ machine with heapFuel := targetHeapFuel } : Eval.Machine).control =
        .running frame stack := by
    simpa using control
  obtain ⟨targetStep, callerState⟩ :=
    simulate_traced_apply_transfer_state descendant state functionResolved
      argumentsResolved noCredits beforeControl transferred
  exact ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
    retainedStores, targetRelease, releasedStores, sourceRun, targetStep,
    calleeState, callerState⟩

/-- Trace-facing over-application combines the source invoke-then-apply
equation with the emitted entry step, exact callee-root state, and residual
argument identity needed by the later `retApplyMore` transition. -/
theorem simulate_traced_apply_pap_over_enter_state
    {sourceContext : IxIR1.Ctx}
    {sourceCurrent sourceDefinition : IxIR1.FnDef}
    {sourceFuel : Nat} {context : Eval.Context}
    {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {callerTrace calleeTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceFunction : IxIR1.Atom} {targetFunction : Atom}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : callerTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next))
    {targetDefinition : Function}
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {source : List RVal} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {captured : Array RVal} {values : List RVal}
    (state : CodeStateRel callerTrace
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next) source frame)
    (stores : StoreRel sourceStore machine.store)
    (positive : PositiveSharedRC sourceStore)
    (functionResolved :
      IxIR1.resolveAtom source sourceFunction = .ok (.loc location))
    (argumentsResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext sourceFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalOver : arity < (captured.toList ++ values).length)
    (papArity : arity = sourceDefinition.arity)
    (sourceDeclaration :
      sourceContext.decls address = some (.fn sourceDefinition))
    (sourcePapSafe : sourceDefinition.papSafe = true)
    (targetDeclaration :
      context.declarations address = some (.fn targetDefinition))
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let sourceTotal := captured.toList ++ values
    let sourceSupplied := sourceTotal.take arity
    let sourceRemaining := sourceTotal.drop arity
    let targetTotal := captured ++ values.toArray
    let targetSupplied := targetTotal.extract 0 arity
    let targetRemaining := targetTotal.extract arity targetTotal.size
    let resume : Eval.Frame := { frame with pc := frame.pc + 1 }
    let calleeFrame : Eval.Frame :=
      { definition := targetDefinition, values := targetSupplied }
    let targetMachine : Eval.Machine :=
      { store := machine.store
        heapFuel := 0
        control := .running calleeFrame
          (.applyMore targetRemaining resume :: stack) }
    ∃ (targetRetained targetReleased : Eval.Store) (targetHeapFuel : Nat),
      Eval.RetainSharedMany machine.store captured targetRetained ∧
        StoreRel sourceRetained targetRetained ∧
        Eval.releaseSharedWork targetHeapFuel targetRetained [.loc location] =
          .ok (targetReleased, 0) ∧
        StoreRel sourceReleased targetReleased ∧
        IxIR1.runOp sourceContext (sourceFuel + 2) sourceCurrent sourceStore
            source (.apply sourceFunction sourceArguments) =
          (do
            let (nextStore, result) ←
              IxIR1.invoke sourceContext sourceFuel address sourceSupplied
                sourceReleased
            IxIR1.applyGo sourceContext sourceFuel nextStore result
              sourceRemaining) ∧
        Eval.Step context interpretation
          { machine with heapFuel := targetHeapFuel }
          { targetMachine with store := targetReleased } ∧
        targetRemaining.toList = sourceRemaining ∧
        CodeStateRel calleeTrace calleeTrace.root sourceSupplied.reverse
          calleeFrame ∧
        ∀ value,
          CodeStateRel callerTrace next (value :: source)
            { frame with
              pc := frame.pc + 1
              values := frame.values.push value } := by
  dsimp only
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      retainedStores, targetRelease, releasedStores, sourceRun, transferred,
      remainingEq, calleeState⟩ :=
    simulate_apply_pap_over_enter
      (resume := { frame with pc := frame.pc + 1 }) calleeMatch stores positive
      functionResolved argumentsResolved sourceGet shared node capturedUnder
      sourceRetain sourceRelease totalOver papArity sourceDeclaration
      sourcePapSafe targetDeclaration
  have beforeControl :
      ({ machine with heapFuel := targetHeapFuel } : Eval.Machine).control =
        .running frame stack := by
    simpa using control
  obtain ⟨targetStep, callerState⟩ :=
    simulate_traced_apply_transfer_state descendant state functionResolved
      argumentsResolved noCredits beforeControl transferred
  exact ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
    retainedStores, targetRelease, releasedStores, sourceRun, targetStep,
    remainingEq, calleeState, callerState⟩

/-- A saturated addressed source call reduces to argument resolution followed
by `invoke`. Exposing this equation keeps the recursive simulation from
unfolding `runOp` at every call site. -/
theorem source_runOp_call_eq
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat} {sourceStore : IxIR1.Store}
    {source : List RVal} {address : Ix.Compiler.Ixon.Address}
    {sourceArguments : Array IxIR1.Atom} {values : List RVal}
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values) :
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
        source (.call address sourceArguments) =
      IxIR1.invoke sourceContext sourceFuel address values sourceStore := by
  rw [IxIR1.runOp.eq_def]
  simp only
  rw [sourceResolved]
  rfl

/-- A saturated source self-call reduces to the current body and its dynamic
result-world check. -/
theorem source_runOp_callSelf_eq
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat} {sourceStore : IxIR1.Store}
    {source : List RVal}
    {sourceArguments : Array IxIR1.Atom} {values : List RVal}
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : sourceCurrent.arity = values.length) :
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
        source (.callSelf sourceArguments) = (do
      let out ← IxIR1.runCode sourceContext sourceFuel sourceCurrent
        sourceStore values.reverse sourceCurrent.body
      IxIR1.checkResultWorld sourceCurrent.result out) := by
  rw [IxIR1.runOp.eq_def]
  simp only
  rw [sourceResolved]
  simp only [bind, Except.bind]
  rw [argumentArity]
  simp

/-- The compiler-recognized tail-call shell is observationally just the
addressed invocation; its trailing `ret (.var 0)` contributes no result
change and consumes the second source fuel layer. -/
theorem source_runCode_tail_call_eq
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat} {sourceStore : IxIR1.Store}
    {source : List RVal} {address : Ix.Compiler.Ixon.Address}
    {sourceArguments : Array IxIR1.Atom} {values : List RVal}
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values) :
    IxIR1.runCode sourceContext (sourceFuel + 2) sourceCurrent sourceStore
        source (.letOp (.call address sourceArguments) (.ret (.var 0))) =
      IxIR1.invoke sourceContext sourceFuel address values sourceStore := by
  rw [IxIR1.runCode.eq_def]
  simp only
  rw [source_runOp_call_eq sourceResolved]
  cases invokeRun :
      IxIR1.invoke sourceContext sourceFuel address values sourceStore with
  | error error => rfl
  | ok output =>
      rcases output with ⟨nextStore, value⟩
      simp only [bind, Except.bind]
      rw [IxIR1.runCode.eq_def]
      rfl

/-- The self-tail-call shell likewise reduces to the current function body
and its result-world check without retaining an extra source continuation. -/
theorem source_runCode_tail_callSelf_eq
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat} {sourceStore : IxIR1.Store}
    {source : List RVal}
    {sourceArguments : Array IxIR1.Atom} {values : List RVal}
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : sourceCurrent.arity = values.length) :
    IxIR1.runCode sourceContext (sourceFuel + 2) sourceCurrent sourceStore
        source (.letOp (.callSelf sourceArguments) (.ret (.var 0))) = (do
      let out ← IxIR1.runCode sourceContext sourceFuel sourceCurrent
        sourceStore values.reverse sourceCurrent.body
      IxIR1.checkResultWorld sourceCurrent.result out) := by
  rw [IxIR1.runCode.eq_def]
  simp only
  rw [source_runOp_callSelf_eq sourceResolved argumentArity]
  cases callRun : (do
      let out ← IxIR1.runCode sourceContext sourceFuel sourceCurrent
        sourceStore values.reverse sourceCurrent.body
      IxIR1.checkResultWorld sourceCurrent.result out) with
  | error error => rfl
  | ok output =>
      rcases output with ⟨nextStore, value⟩
      simp only [bind, Except.bind]
      rw [IxIR1.runCode.eq_def]
      rfl

/-- A direct-call instruction resolves the same argument vector, enters the
addressed target function in one step, and establishes its canonical reversed
source-parameter environment. The function-body induction supplies the
subsequent execution under the pushed continuation. -/
theorem simulate_call_fn_enter {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation} {block : Block}
    {source : List RVal} {mapping : EnvMap}
    (environments : EnvRel source frame.values mapping)
    {address : Ix.Compiler.Ixon.Address}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom} {values : List RVal}
    {definition : Function}
    (arguments : AtomsRel mapping sourceArguments targetArguments)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (declaration : context.declarations address = some (.fn definition))
    (arity : definition.signature.params.size = values.length)
    (nonempty : definition.blocks.isEmpty = false)
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .call address targetArguments) :
    Eval.Step context interpretation machine
        { machine with
          control := .running
            { definition, values := values.toArray }
            (.resume { frame with pc := frame.pc + 1 } :: stack) } ∧
      EnvRel values.reverse values.toArray (entryMap values.length) := by
  have targetResolved :
      Eval.resolveAtoms frame.values targetArguments = .ok values.toArray :=
    resolveAtoms_of_envRel environments arguments sourceResolved
  have targetArity :
      values.toArray.size = definition.signature.params.size := by
    simp [arity]
  exact ⟨Eval.Step.callFn control blockAt pc instruction noCredits
      targetResolved declaration targetArity nonempty,
    EnvRel.entry values.toArray⟩

/-- A recursive self-call has the same entry relation as an addressed call. -/
theorem simulate_call_self_enter {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation} {block : Block}
    {source : List RVal} {mapping : EnvMap}
    (environments : EnvRel source frame.values mapping)
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom} {values : List RVal}
    (arguments : AtomsRel mapping sourceArguments targetArguments)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (arity : frame.definition.signature.params.size = values.length)
    (nonempty : frame.definition.blocks.isEmpty = false)
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .callSelf targetArguments) :
    Eval.Step context interpretation machine
        { machine with
          control := .running
            { definition := frame.definition, values := values.toArray }
            (.resume { frame with pc := frame.pc + 1 } :: stack) } ∧
      EnvRel values.reverse values.toArray (entryMap values.length) := by
  have targetResolved :
      Eval.resolveAtoms frame.values targetArguments = .ok values.toArray :=
    resolveAtoms_of_envRel environments arguments sourceResolved
  have targetArity :
      values.toArray.size = frame.definition.signature.params.size := by
    simp [arity]
  exact ⟨Eval.Step.callSelf control blockAt pc instruction noCredits
      targetResolved targetArity nonempty,
    EnvRel.entry values.toArray⟩

/-- Trace-facing addressed call entry. The caller trace supplies emitted call
syntax and coordinates; an exact callee `FunctionTraceMatch` turns the target
entry frame into the callee root `CodeStateRel`. -/
theorem simulate_traced_call_fn_enter_state {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation}
    {functionTrace calleeTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAddress targetAddress : Ix.Compiler.Ixon.Address}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.call sourceAddress sourceArguments) index
        (.call targetAddress targetArguments) next))
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration sourceAddress) sourceDefinition targetDefinition)
    {source : List RVal} {values : List RVal}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.call sourceAddress sourceArguments) index
        (.call targetAddress targetArguments) next) source frame)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : sourceDefinition.arity = values.length)
    (declaration :
      context.declarations sourceAddress = some (.fn targetDefinition))
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let calleeFrame : Eval.Frame :=
      { definition := targetDefinition, values := values.toArray }
    Eval.Step context interpretation machine
        { machine with
          control := .running calleeFrame
            (.resume { frame with pc := frame.pc + 1 } :: stack) } ∧
      CodeStateRel calleeTrace calleeTrace.root values.reverse calleeFrame := by
  dsimp only
  have operationSyntax := functionTrace.descendantOperationSyntax descendant
  change sourceAddress = targetAddress ∧
    Lower.InputMap.translateAtoms input sourceArguments =
      some targetArguments at operationSyntax
  obtain ⟨addressEq, translated⟩ := operationSyntax
  subst targetAddress
  have arguments : AtomsRel input sourceArguments targetArguments :=
    atomsRel_of_translateAtoms translated
  have targetArity :
      targetDefinition.signature.params.size = values.length := by
    calc
      targetDefinition.signature.params.size =
          calleeTrace.generated.signature.params.size := by
            rw [calleeMatch.generated]
      _ = calleeTrace.source.arity := calleeTrace.sourceArity
      _ = sourceDefinition.arity := congrArg IxIR1.FnDef.arity calleeMatch.source
      _ = values.length := argumentArity
  have targetNonempty : targetDefinition.blocks.isEmpty = false := by
    simpa [calleeMatch.generated] using calleeTrace.generatedNonempty
  obtain ⟨blockAt, pcBound, instructionAt⟩ := state.instructionAt descendant
  have instruction :
      next.headBlock.2.instructions[frame.pc] =
        .call sourceAddress targetArguments :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  have entered := simulate_call_fn_enter
    (context := context) (interpretation := interpretation)
    state.environments arguments
    sourceResolved declaration targetArity targetNonempty noCredits control
      blockAt pcBound instruction
  have entryArity : values.toArray.size = calleeTrace.source.arity := by
    simpa [calleeMatch.source] using argumentArity.symm
  have calleeState := functionEntryCodeState calleeTrace values.toArray entryArity
  exact ⟨entered.1, by
    simpa [calleeMatch.generated] using calleeState⟩

/-- Trace-facing recursive self-call entry into the same function-trace root. -/
theorem simulate_traced_call_self_enter_state {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.callSelf sourceArguments) index (.callSelf targetArguments) next))
    {source : List RVal} {values : List RVal}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.callSelf sourceArguments) index (.callSelf targetArguments) next)
      source frame)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : functionTrace.source.arity = values.length)
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let calleeFrame : Eval.Frame :=
      { definition := frame.definition, values := values.toArray }
    Eval.Step context interpretation machine
        { machine with
          control := .running calleeFrame
            (.resume { frame with pc := frame.pc + 1 } :: stack) } ∧
      CodeStateRel functionTrace functionTrace.root values.reverse calleeFrame := by
  dsimp only
  have translated : Lower.InputMap.translateAtoms input sourceArguments =
      some targetArguments := by
    simpa [Lower.OperationSyntax] using
      functionTrace.descendantOperationSyntax descendant
  have arguments : AtomsRel input sourceArguments targetArguments :=
    atomsRel_of_translateAtoms translated
  have targetArity :
      frame.definition.signature.params.size = values.length := by
    calc
      frame.definition.signature.params.size =
          functionTrace.generated.signature.params.size := by
            rw [state.definition]
      _ = functionTrace.source.arity := functionTrace.sourceArity
      _ = values.length := argumentArity
  have targetNonempty : frame.definition.blocks.isEmpty = false := by
    simpa [state.definition] using functionTrace.generatedNonempty
  obtain ⟨blockAt, pcBound, instructionAt⟩ := state.instructionAt descendant
  have instruction :
      next.headBlock.2.instructions[frame.pc] =
        .callSelf targetArguments :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  have entered := simulate_call_self_enter
    (context := context) (interpretation := interpretation)
    state.environments arguments
    sourceResolved targetArity targetNonempty noCredits control blockAt pcBound
      instruction
  have entryArity : values.toArray.size = functionTrace.source.arity := by
    simpa using argumentArity.symm
  have calleeState := functionEntryCodeState functionTrace values.toArray
    entryArity
  exact ⟨entered.1, by simpa [state.definition] using calleeState⟩

/-- Tail calls enter the addressed callee without growing the continuation
stack while preserving the same canonical entry relation. -/
theorem simulate_tail_call_fn_enter {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation} {block : Block}
    {source : List RVal} {mapping : EnvMap}
    (environments : EnvRel source frame.values mapping)
    {address : Ix.Compiler.Ixon.Address}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom} {values : List RVal}
    {definition : Function}
    (arguments : AtomsRel mapping sourceArguments targetArguments)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (declaration : context.declarations address = some (.fn definition))
    (arity : definition.signature.params.size = values.length)
    (nonempty : definition.blocks.isEmpty = false)
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .tailCall address targetArguments) :
    Eval.Step context interpretation machine
        { machine with
          control := .running
            { definition, values := values.toArray } stack } ∧
      EnvRel values.reverse values.toArray (entryMap values.length) := by
  have targetResolved :
      Eval.resolveAtoms frame.values targetArguments = .ok values.toArray :=
    resolveAtoms_of_envRel environments arguments sourceResolved
  have targetArity :
      values.toArray.size = definition.signature.params.size := by
    simp [arity]
  exact ⟨Eval.Step.tailCallFn control blockAt pc terminator noCredits
      targetResolved declaration targetArity nonempty,
    EnvRel.entry values.toArray⟩

/-- Tail-recursive self entry likewise preserves the continuation stack. -/
theorem simulate_tail_call_self_enter {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation} {block : Block}
    {source : List RVal} {mapping : EnvMap}
    (environments : EnvRel source frame.values mapping)
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom} {values : List RVal}
    (arguments : AtomsRel mapping sourceArguments targetArguments)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (arity : frame.definition.signature.params.size = values.length)
    (nonempty : frame.definition.blocks.isEmpty = false)
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .tailCallSelf targetArguments) :
    Eval.Step context interpretation machine
        { machine with
          control := .running
            { definition := frame.definition, values := values.toArray }
            stack } ∧
      EnvRel values.reverse values.toArray (entryMap values.length) := by
  have targetResolved :
      Eval.resolveAtoms frame.values targetArguments = .ok values.toArray :=
    resolveAtoms_of_envRel environments arguments sourceResolved
  have targetArity :
      values.toArray.size = frame.definition.signature.params.size := by
    simp [arity]
  exact ⟨Eval.Step.tailCallSelf control blockAt pc terminator noCredits
      targetResolved targetArity nonempty,
    EnvRel.entry values.toArray⟩

/-- Trace-facing addressed tail-call entry. The checked terminal trace
provides the target argument vector, executable block, PC, and terminator. -/
theorem simulate_traced_tail_call_fn_enter_state {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation}
    {functionTrace calleeTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : EnvMap} {entryValueCount : Nat}
    {address : Ix.Compiler.Ixon.Address}
    {sourceArguments : Array IxIR1.Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.tailCall site blockId input entryValueCount address sourceArguments
        generated))
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {source : List RVal} {values : List RVal}
    (state : CodeStateRel functionTrace
      (.tailCall site blockId input entryValueCount address sourceArguments
        generated) source frame)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : sourceDefinition.arity = values.length)
    (declaration : context.declarations address = some (.fn targetDefinition))
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let calleeFrame : Eval.Frame :=
      { definition := targetDefinition, values := values.toArray }
    Eval.Step context interpretation machine
        { machine with
          control := .running calleeFrame stack } ∧
      CodeStateRel calleeTrace calleeTrace.root values.reverse calleeFrame := by
  dsimp only
  have syntaxMatched := functionTrace.descendantSyntaxMatches descendant
  obtain ⟨targetArguments, translated, terminator⟩ :=
    Lower.CodeTrace.tailCallSyntax_of_match syntaxMatched
  have arguments : AtomsRel input sourceArguments targetArguments :=
    atomsRel_of_translateAtoms translated
  have blockAt :
      frame.definition.blocks[frame.block]? = some generated := by
    simpa [Lower.CodeTrace.headBlock] using state.blockAt descendant
  have pc : frame.pc = generated.instructions.size := by
    simpa [Lower.CodeTrace.entryPc] using state.pc
  have targetArity :
      targetDefinition.signature.params.size = values.length := by
    calc
      targetDefinition.signature.params.size =
          calleeTrace.generated.signature.params.size := by
            rw [calleeMatch.generated]
      _ = calleeTrace.source.arity := calleeTrace.sourceArity
      _ = sourceDefinition.arity := congrArg IxIR1.FnDef.arity calleeMatch.source
      _ = values.length := argumentArity
  have targetNonempty : targetDefinition.blocks.isEmpty = false := by
    simpa [calleeMatch.generated] using calleeTrace.generatedNonempty
  have entered := simulate_tail_call_fn_enter
    (context := context) (interpretation := interpretation)
    state.environments arguments sourceResolved declaration targetArity
      targetNonempty noCredits control blockAt pc terminator
  have entryArity : values.toArray.size = calleeTrace.source.arity := by
    simpa [calleeMatch.source] using argumentArity.symm
  have calleeState := functionEntryCodeState calleeTrace values.toArray entryArity
  exact ⟨entered.1, by
    simpa [calleeMatch.generated] using calleeState⟩

/-- Trace-facing self-tail-call entry. All generated syntax and coordinates
come from the checked recursive derivation. -/
theorem simulate_traced_tail_call_self_enter_state {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : EnvMap} {entryValueCount : Nat}
    {sourceArguments : Array IxIR1.Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.tailCallSelf site blockId input entryValueCount sourceArguments
        generated))
    {source : List RVal} {values : List RVal}
    (state : CodeStateRel functionTrace
      (.tailCallSelf site blockId input entryValueCount sourceArguments
        generated) source frame)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : functionTrace.source.arity = values.length)
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let calleeFrame : Eval.Frame :=
      { definition := frame.definition, values := values.toArray }
    Eval.Step context interpretation machine
        { machine with
          control := .running calleeFrame stack } ∧
      CodeStateRel functionTrace functionTrace.root values.reverse
        calleeFrame := by
  dsimp only
  have syntaxMatched := functionTrace.descendantSyntaxMatches descendant
  obtain ⟨targetArguments, translated, terminator⟩ :=
    Lower.CodeTrace.tailCallSelfSyntax_of_match syntaxMatched
  have arguments : AtomsRel input sourceArguments targetArguments :=
    atomsRel_of_translateAtoms translated
  have blockAt :
      frame.definition.blocks[frame.block]? = some generated := by
    simpa [Lower.CodeTrace.headBlock] using state.blockAt descendant
  have pc : frame.pc = generated.instructions.size := by
    simpa [Lower.CodeTrace.entryPc] using state.pc
  have targetArity :
      frame.definition.signature.params.size = values.length := by
    calc
      frame.definition.signature.params.size =
          functionTrace.generated.signature.params.size := by
            rw [state.definition]
      _ = functionTrace.source.arity := functionTrace.sourceArity
      _ = values.length := argumentArity
  have targetNonempty : frame.definition.blocks.isEmpty = false := by
    simpa [state.definition] using functionTrace.generatedNonempty
  have entered := simulate_tail_call_self_enter
    (context := context) (interpretation := interpretation)
    state.environments arguments sourceResolved targetArity targetNonempty
      noCredits control blockAt pc terminator
  have entryArity : values.toArray.size = functionTrace.source.arity := by
    simpa using argumentArity.symm
  have calleeState := functionEntryCodeState functionTrace values.toArray
    entryArity
  exact ⟨entered.1, by simpa [state.definition] using calleeState⟩

/-- Trace-facing addressed calls now expose both sides of the recursive
induction seam: the exact IxIR₁ `invoke` equation and the genuine target entry
step into the matched callee root. The heap relation is unchanged by entry. -/
theorem simulate_traced_call_fn_enter_source_state
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace calleeTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAddress targetAddress : Ix.Compiler.Ixon.Address}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.call sourceAddress sourceArguments) index
        (.call targetAddress targetArguments) next))
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration sourceAddress) sourceDefinition targetDefinition)
    {sourceStore : IxIR1.Store} {source : List RVal}
    {values : List RVal}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.call sourceAddress sourceArguments) index
        (.call targetAddress targetArguments) next) source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : sourceDefinition.arity = values.length)
    (declaration :
      context.declarations sourceAddress = some (.fn targetDefinition))
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let calleeFrame : Eval.Frame :=
      { definition := targetDefinition, values := values.toArray }
    IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source
          sourceStore source (.call sourceAddress sourceArguments) =
        IxIR1.invoke sourceContext sourceFuel sourceAddress values sourceStore ∧
      Eval.Step context interpretation machine
        { machine with
          control := .running calleeFrame
            (.resume { frame with pc := frame.pc + 1 } :: stack) } ∧
      StoreRel sourceStore machine.store ∧
      CodeStateRel calleeTrace calleeTrace.root values.reverse calleeFrame := by
  dsimp only
  obtain ⟨targetStep, calleeState⟩ :=
    simulate_traced_call_fn_enter_state
      (context := context) (interpretation := interpretation)
      descendant calleeMatch state sourceResolved argumentArity declaration
        noCredits control
  exact ⟨source_runOp_call_eq sourceResolved, targetStep, stores, calleeState⟩

/-- Recursive self-call entry has the same paired source/target seam, with
the source equation naming the current function body and result-world check. -/
theorem simulate_traced_call_self_enter_source_state
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.callSelf sourceArguments) index (.callSelf targetArguments) next))
    {sourceStore : IxIR1.Store} {source : List RVal}
    {values : List RVal}
    (state : CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.callSelf sourceArguments) index (.callSelf targetArguments) next)
      source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : functionTrace.source.arity = values.length)
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let calleeFrame : Eval.Frame :=
      { definition := frame.definition, values := values.toArray }
    IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source
          sourceStore source (.callSelf sourceArguments) = (do
        let out ← IxIR1.runCode sourceContext sourceFuel functionTrace.source
          sourceStore values.reverse functionTrace.source.body
        IxIR1.checkResultWorld functionTrace.source.result out) ∧
      Eval.Step context interpretation machine
        { machine with
          control := .running calleeFrame
            (.resume { frame with pc := frame.pc + 1 } :: stack) } ∧
      StoreRel sourceStore machine.store ∧
      CodeStateRel functionTrace functionTrace.root values.reverse
        calleeFrame := by
  dsimp only
  obtain ⟨targetStep, calleeState⟩ :=
    simulate_traced_call_self_enter_state
      (context := context) (interpretation := interpretation)
      descendant state sourceResolved argumentArity noCredits control
  exact ⟨source_runOp_callSelf_eq sourceResolved argumentArity,
    targetStep, stores, calleeState⟩

/-- A traced addressed tail call discards both source and target caller
continuations: the compiler-recognized source shell is exactly `invoke`, and
the target enters the same matched callee root with the existing stack. -/
theorem simulate_traced_tail_call_fn_enter_source_state
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace calleeTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : EnvMap} {entryValueCount : Nat}
    {address : Ix.Compiler.Ixon.Address}
    {sourceArguments : Array IxIR1.Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.tailCall site blockId input entryValueCount address sourceArguments
        generated))
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {sourceStore : IxIR1.Store} {source : List RVal}
    {values : List RVal}
    (state : CodeStateRel functionTrace
      (.tailCall site blockId input entryValueCount address sourceArguments
        generated) source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : sourceDefinition.arity = values.length)
    (declaration : context.declarations address = some (.fn targetDefinition))
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let calleeFrame : Eval.Frame :=
      { definition := targetDefinition, values := values.toArray }
    IxIR1.runCode sourceContext (sourceFuel + 2) functionTrace.source
          sourceStore source
          (.letOp (.call address sourceArguments) (.ret (.var 0))) =
        IxIR1.invoke sourceContext sourceFuel address values sourceStore ∧
      Eval.Step context interpretation machine
        { machine with control := .running calleeFrame stack } ∧
      StoreRel sourceStore machine.store ∧
      CodeStateRel calleeTrace calleeTrace.root values.reverse calleeFrame := by
  dsimp only
  obtain ⟨targetStep, calleeState⟩ :=
    simulate_traced_tail_call_fn_enter_state
      (context := context) (interpretation := interpretation)
      descendant calleeMatch state sourceResolved argumentArity declaration
        noCredits control
  exact ⟨source_runCode_tail_call_eq sourceResolved,
    targetStep, stores, calleeState⟩

/-- Self-tail calls expose the analogous current-body source equation and
enter the same trace root without growing either continuation stack. -/
theorem simulate_traced_tail_call_self_enter_source_state
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : EnvMap} {entryValueCount : Nat}
    {sourceArguments : Array IxIR1.Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.tailCallSelf site blockId input entryValueCount sourceArguments
        generated))
    {sourceStore : IxIR1.Store} {source : List RVal}
    {values : List RVal}
    (state : CodeStateRel functionTrace
      (.tailCallSelf site blockId input entryValueCount sourceArguments
        generated) source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : functionTrace.source.arity = values.length)
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let calleeFrame : Eval.Frame :=
      { definition := frame.definition, values := values.toArray }
    IxIR1.runCode sourceContext (sourceFuel + 2) functionTrace.source
          sourceStore source
          (.letOp (.callSelf sourceArguments) (.ret (.var 0))) = (do
        let out ← IxIR1.runCode sourceContext sourceFuel functionTrace.source
          sourceStore values.reverse functionTrace.source.body
        IxIR1.checkResultWorld functionTrace.source.result out) ∧
      Eval.Step context interpretation machine
        { machine with control := .running calleeFrame stack } ∧
      StoreRel sourceStore machine.store ∧
      CodeStateRel functionTrace functionTrace.root values.reverse
        calleeFrame := by
  dsimp only
  obtain ⟨targetStep, calleeState⟩ :=
    simulate_traced_tail_call_self_enter_state
      (context := context) (interpretation := interpretation)
      descendant state sourceResolved argumentArity noCredits control
  exact ⟨source_runCode_tail_callSelf_eq sourceResolved argumentArity,
    targetStep, stores, calleeState⟩

/-- Generic instruction/continuation composition for the code induction.
Once an operation-local theorem supplies one target step and the continuation
hypothesis starts from its successor state, exact finite executions compose
without equating source fuel to target control steps. -/
theorem simulate_letOp_continuation {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine middle targetOut : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation}
    {sourceStore middleStore outStore : IxIR1.Store}
    {source : List RVal} {operation : IxIR1.Op} {rest : IxIR1.Code}
    {value outValue : RVal} {continuationCount : Nat}
    (running : machine.control = .running frame stack)
    (sourceOperation : IxIR1.runOp sourceContext sourceFuel sourceCurrent
      sourceStore source operation = .ok (middleStore, value))
    (targetOperation :
      Eval.Step context interpretation machine middle)
    (sourceContinuation : IxIR1.runCode sourceContext sourceFuel
      sourceCurrent middleStore (value :: source) rest =
        .ok (outStore, outValue))
    (targetContinuation : Eval.Steps context interpretation
      continuationCount middle targetOut) :
    IxIR1.runCode sourceContext (sourceFuel + 1) sourceCurrent sourceStore
        source (.letOp operation rest) = .ok (outStore, outValue) ∧
      Eval.Steps context interpretation (Nat.succ continuationCount)
        machine targetOut := by
  constructor
  · rw [IxIR1.runCode.eq_def]
    simp only
    rw [sourceOperation]
    exact sourceContinuation
  · exact .cons running targetOperation targetContinuation

/-- Constructor-case composition: source dispatch selects the same branch as
the target's full-constructor switch, whose one control step composes directly
with the branch induction hypothesis. The branch execution starts after the
generated edge transfer (and any constructor-field fetch prologue). -/
theorem simulate_case_ctor_branch {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine targetOut : Eval.Machine} {frame target : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore sourceOut : IxIR1.Store} {source : List RVal}
    {mapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceScrutinee : IxIR1.Atom} {targetScrutinee : Atom}
    {location : Nat} {box : IxIR1.NodeBox} {cid : IxIR1.CtorId}
    {fields : Array RVal} {sourceAlternatives : Array IxIR1.Alt}
    {sourcePeelNat : Bool} {tag fieldCount : Nat} {body : IxIR1.Code}
    {value : RVal}
    {constructors : Array CtorAlt} {targetPeelNat : Option NatPeel}
    {alternative : CtorAlt} {branchCount : Nat}
    (translated :
      translateAtom mapping sourceScrutinee = some targetScrutinee)
    (sourceResolved :
      IxIR1.resolveAtom source sourceScrutinee = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (node : box.node = .ctorN cid fields)
    (sourceAlternative : sourceAlternatives.find? (fun candidate =>
      candidate.cidx == cid.cidx) =
        some (.mk tag fieldCount body))
    (fieldArity : fields.size = fieldCount)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator =
      .switchValue targetScrutinee constructors targetPeelNat)
    (targetAlternative : constructors.find? (fun candidate =>
      candidate.cid == cid) = some alternative)
    (transferred : Eval.EdgeTransfer frame alternative.edge #[] target)
    (sourceBranch : IxIR1.runCode sourceContext sourceFuel sourceCurrent
      sourceStore (fields.toList.reverse ++ source) body =
        .ok (sourceOut, value))
    (targetBranch : Eval.Steps context interpretation branchCount
      { machine with control := .running target stack } targetOut) :
    IxIR1.runCode sourceContext (sourceFuel + 1) sourceCurrent sourceStore
        source (.case sourceScrutinee sourcePeelNat sourceAlternatives) =
          .ok (sourceOut, value) ∧
      Eval.Steps context interpretation (Nat.succ branchCount)
        machine targetOut := by
  have targetResolved :
      Eval.resolveAtom frame.values targetScrutinee = .ok (.loc location) :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetGet : machine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have targetStep := Eval.Step.switchCtor (context := context)
    (interpretation := interpretation) control blockAt pc terminator
      targetResolved targetGet node targetAlternative transferred
  constructor
  · rw [IxIR1.runCode.eq_def]
    simp only
    rw [sourceResolved]
    simp only [bind, Except.bind]
    rw [sourceGet]
    simp only
    rw [node]
    simp only
    rw [sourceAlternative]
    simp [fieldArity, sourceBranch]
  · exact .cons control targetStep targetBranch

/-- Literal-Nat zero dispatch composes one target switch step with the zero
branch induction hypothesis. -/
theorem simulate_case_nat_zero_branch {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine targetOut : Eval.Machine} {frame target : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore sourceOut : IxIR1.Store} {source : List RVal}
    {mapping : EnvMap}
    (environments : EnvRel source frame.values mapping)
    {sourceScrutinee : IxIR1.Atom} {targetScrutinee : Atom}
    {sourceAlternatives : Array IxIR1.Alt} {body : IxIR1.Code}
    {value : RVal}
    {constructors : Array CtorAlt} {peel : NatPeel}
    {branchCount : Nat}
    (translated :
      translateAtom mapping sourceScrutinee = some targetScrutinee)
    (sourceResolved :
      IxIR1.resolveAtom source sourceScrutinee = .ok (.lit (.nat 0)))
    (sourceAlternative : sourceAlternatives.find? (fun candidate =>
      candidate.cidx == 0) =
        some (.mk 0 0 body))
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator =
      .switchValue targetScrutinee constructors (some peel))
    (transferred : Eval.EdgeTransfer frame peel.zero #[] target)
    (sourceBranch : IxIR1.runCode sourceContext sourceFuel sourceCurrent
      sourceStore source body = .ok (sourceOut, value))
    (targetBranch : Eval.Steps context interpretation branchCount
      { machine with control := .running target stack } targetOut) :
    IxIR1.runCode sourceContext (sourceFuel + 1) sourceCurrent sourceStore
        source (.case sourceScrutinee true sourceAlternatives) =
          .ok (sourceOut, value) ∧
      Eval.Steps context interpretation (Nat.succ branchCount)
        machine targetOut := by
  have targetResolved :
      Eval.resolveAtom frame.values targetScrutinee = .ok (.lit (.nat 0)) :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetStep := Eval.Step.switchNatZero (context := context)
    (interpretation := interpretation) control blockAt pc terminator
      targetResolved transferred
  constructor
  · rw [IxIR1.runCode.eq_def]
    simp only
    rw [sourceResolved]
    simp only [bind, Except.bind]
    rw [sourceAlternative]
    exact sourceBranch
  · exact .cons control targetStep targetBranch

/-- Literal-Nat successor dispatch preserves the peeled predecessor and
composes one target switch step with the successor-branch induction
hypothesis. -/
theorem simulate_case_nat_succ_branch {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel predecessor : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine targetOut : Eval.Machine} {frame target : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore sourceOut : IxIR1.Store} {source : List RVal}
    {mapping : EnvMap}
    (environments : EnvRel source frame.values mapping)
    {sourceScrutinee : IxIR1.Atom} {targetScrutinee : Atom}
    {sourceAlternatives : Array IxIR1.Alt} {body : IxIR1.Code}
    {value : RVal}
    {constructors : Array CtorAlt} {peel : NatPeel}
    {branchCount : Nat}
    (translated :
      translateAtom mapping sourceScrutinee = some targetScrutinee)
    (sourceResolved : IxIR1.resolveAtom source sourceScrutinee =
      .ok (.lit (.nat (predecessor + 1))))
    (sourceAlternative : sourceAlternatives.find? (fun candidate =>
      candidate.cidx == 1) =
        some (.mk 1 1 body))
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator =
      .switchValue targetScrutinee constructors (some peel))
    (transferred : Eval.EdgeTransfer frame peel.succ
      #[.lit (.nat predecessor)] target)
    (sourceBranch : IxIR1.runCode sourceContext sourceFuel sourceCurrent
      sourceStore (.lit (.nat predecessor) :: source) body =
        .ok (sourceOut, value))
    (targetBranch : Eval.Steps context interpretation branchCount
      { machine with control := .running target stack } targetOut) :
    IxIR1.runCode sourceContext (sourceFuel + 1) sourceCurrent sourceStore
        source (.case sourceScrutinee true sourceAlternatives) =
          .ok (sourceOut, value) ∧
      Eval.Steps context interpretation (Nat.succ branchCount)
        machine targetOut := by
  have targetResolved : Eval.resolveAtom frame.values targetScrutinee =
      .ok (.lit (.nat (predecessor + 1))) :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetStep := Eval.Step.switchNatSucc (context := context)
    (interpretation := interpretation) control blockAt pc terminator
      targetResolved transferred
  constructor
  · rw [IxIR1.runCode.eq_def]
    simp only
    rw [sourceResolved]
    simp only [bind, Except.bind]
    rw [sourceAlternative]
    exact sourceBranch
  · exact .cons control targetStep targetBranch

/-- A callee return under an over-application continuation performs the same
return-value resolution as an ordinary return, then dispatches that value and
the retained residual vector through the shared `ApplyTransfer` boundary. -/
theorem simulate_ret_apply_more {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine target : Eval.Machine} {frame caller : Eval.Frame}
    {arguments : Array RVal} {rest : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal} {mapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (control : machine.control =
      .running frame (.applyMore arguments caller :: rest))
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .ret targetAtom)
    (noCredits : frame.credits = #[])
    (world : Eval.RVal.hasWorld machine.store
      frame.definition.signature.result value = true)
    (transferred : Eval.ApplyTransfer context interpretation machine.store
      machine.heapFuel value arguments caller rest target) :
    IxIR1.runCode sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.ret sourceAtom) = .ok (sourceStore, value) ∧
      Eval.Steps context interpretation 1 machine target ∧
      StoreRel sourceStore machine.store := by
  have targetResolved : Eval.resolveAtom frame.values targetAtom = .ok value :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetStep := Eval.Step.retApplyMore (context := context)
    (interpretation := interpretation) control blockAt pc terminator
      targetResolved noCredits world transferred
  refine ⟨?_, targetStep.toSteps control, stores⟩
  unfold IxIR1.runCode
  simp only
  rw [sourceResolved]
  rfl

/-- Trace-facing over-application return. The retained callee derivation
supplies its exact return syntax and coordinate; the caller supplies only the
next dynamic `ApplyTransfer` result for the already-certified residual vector. -/
theorem simulate_traced_ret_apply_more_state
    {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine target : Eval.Machine} {frame caller : Eval.Frame}
    {arguments : Array RVal} {rest : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : EnvMap} {entryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.ret site blockId input entryValueCount sourceAtom targetAtom generated))
    {sourceStore : IxIR1.Store} {source : List RVal} {value : RVal}
    (state : CodeStateRel functionTrace
      (.ret site blockId input entryValueCount sourceAtom targetAtom generated)
      source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (control : machine.control =
      .running frame (.applyMore arguments caller :: rest))
    (noCredits : frame.credits = #[])
    (world : Eval.RVal.hasWorld machine.store
      frame.definition.signature.result value = true)
    (transferred : Eval.ApplyTransfer context interpretation machine.store
      machine.heapFuel value arguments caller rest target) :
    IxIR1.runCode sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.ret sourceAtom) = .ok (sourceStore, value) ∧
      Eval.Steps context interpretation 1 machine target ∧
      StoreRel sourceStore machine.store := by
  have syntaxMatched := functionTrace.descendantSyntaxMatches descendant
  obtain ⟨translated, terminator⟩ :=
    Lower.CodeTrace.retSyntax_of_match syntaxMatched
  have blockAt : frame.definition.blocks[frame.block]? = some generated := by
    simpa [Lower.CodeTrace.headBlock] using state.blockAt descendant
  have pc : frame.pc = generated.instructions.size := by
    simpa [Lower.CodeTrace.entryPc] using state.pc
  exact simulate_ret_apply_more stores state.environments translated
    sourceResolved control blockAt pc terminator noCredits world transferred

/-- The non-outer return base case resumes the suspended target caller and
establishes the source result binding relation needed by its continuation. -/
theorem simulate_ret_resume {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame caller : Eval.Frame}
    {rest : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source callerSource : List RVal}
    {mapping callerMapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    (callerEnvironments :
      EnvRel callerSource caller.values callerMapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (control : machine.control =
      .running frame (.resume caller :: rest))
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .ret targetAtom)
    (noCredits : frame.credits = #[])
    (world : Eval.RVal.hasWorld machine.store
      frame.definition.signature.result value = true) :
    IxIR1.runCode sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.ret sourceAtom) = .ok (sourceStore, value) ∧
      Eval.Steps context interpretation 1 machine
        { machine with
          control := .running
            { caller with values := caller.values.push value } rest } ∧
      StoreRel sourceStore machine.store ∧
      EnvRel (value :: callerSource) (caller.values.push value)
        (#[some (.reg caller.values.size)] ++ callerMapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok value :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetStep := Eval.Step.retResume (context := context)
    (interpretation := interpretation) control blockAt pc terminator
      targetResolved noCredits world
  refine ⟨?_, targetStep.toSteps control, stores,
    callerEnvironments.bindValue value⟩
  unfold IxIR1.runCode
  simp only
  rw [sourceResolved]
  rfl

/-- Trace-facing resumed return. As in the outermost case, recursive trace
membership supplies the executable block, terminal PC, translated operand,
and return terminator; the caller relation is extended with the result. -/
theorem simulate_traced_ret_resume_state {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame caller : Eval.Frame}
    {rest : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : EnvMap} {entryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.ret site blockId input entryValueCount sourceAtom targetAtom generated))
    {sourceStore : IxIR1.Store} {source callerSource : List RVal}
    {callerMapping : EnvMap} {value : RVal}
    (state : CodeStateRel functionTrace
      (.ret site blockId input entryValueCount sourceAtom targetAtom generated)
      source frame)
    (stores : StoreRel sourceStore machine.store)
    (callerEnvironments :
      EnvRel callerSource caller.values callerMapping)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (control : machine.control =
      .running frame (.resume caller :: rest))
    (noCredits : frame.credits = #[])
    (world : Eval.RVal.hasWorld machine.store
      frame.definition.signature.result value = true) :
    IxIR1.runCode sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.ret sourceAtom) = .ok (sourceStore, value) ∧
      Eval.Steps context interpretation 1 machine
        { machine with
          control := .running
            { caller with values := caller.values.push value } rest } ∧
      StoreRel sourceStore machine.store ∧
      EnvRel (value :: callerSource) (caller.values.push value)
        (#[some (.reg caller.values.size)] ++ callerMapping) := by
  have syntaxMatched := functionTrace.descendantSyntaxMatches descendant
  obtain ⟨translated, terminator⟩ :=
    Lower.CodeTrace.retSyntax_of_match syntaxMatched
  have blockAt :
      frame.definition.blocks[frame.block]? = some generated := by
    simpa [Lower.CodeTrace.headBlock] using state.blockAt descendant
  have pc : frame.pc = generated.instructions.size := by
    simpa [Lower.CodeTrace.entryPc] using state.pc
  exact simulate_ret_resume stores state.environments callerEnvironments
    translated sourceResolved control blockAt pc terminator noCredits world

/-- Complete a traced value-producing caller instruction when a traced callee
returns. This is the call-stack hand-off needed by recursive function
induction: the callee return step, checked caller map forgetting, and caller
PC/register progression produce the caller continuation's `CodeStateRel`. -/
theorem simulate_traced_return_to_letOp_state
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {calleeFrame callerFrame : Eval.Frame}
    {rest : List Eval.Continuation}
    {callerTrace calleeTrace : Lower.FunctionTrace}
    {callSite : Lower.SourceSite} {callBlock : BlockId}
    {callInput nextInput : EnvMap} {callEntryValueCount callIndex : Nat}
    {operation : IxIR1.Op} {instruction : Instr} {next : Lower.CodeTrace}
    (callerDescendant : callerTrace.root.Descendant
      (.letOp callSite callBlock callInput nextInput callEntryValueCount
        operation callIndex instruction next))
    {returnSite : Lower.SourceSite} {returnBlock : BlockId}
    {returnInput : EnvMap} {returnEntryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {generated : Block}
    (calleeDescendant : calleeTrace.root.Descendant
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom generated))
    {sourceStore : IxIR1.Store} {calleeSource callerSource : List RVal}
    {value : RVal}
    (callerState : CodeStateRel callerTrace
      (.letOp callSite callBlock callInput nextInput callEntryValueCount
        operation callIndex instruction next) callerSource callerFrame)
    (calleeState : CodeStateRel calleeTrace
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom generated) calleeSource calleeFrame)
    (binder : Lower.Instr.baselineBinderAtom callEntryValueCount instruction =
      some (.reg callEntryValueCount))
    (delta : Lower.Instr.baselineValueDelta instruction = some 1)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtom calleeSource sourceAtom = .ok value)
    (control : machine.control = .running calleeFrame
      (.resume { callerFrame with pc := callerFrame.pc + 1 } :: rest))
    (noCredits : calleeFrame.credits = #[])
    (world : Eval.RVal.hasWorld machine.store
      calleeFrame.definition.signature.result value = true) :
    let nextCallerFrame : Eval.Frame :=
      { callerFrame with
        pc := callerFrame.pc + 1
        values := callerFrame.values.push value }
    IxIR1.runCode sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          calleeSource (.ret sourceAtom) = .ok (sourceStore, value) ∧
      Eval.Steps context interpretation 1 machine
        { machine with control := .running nextCallerFrame rest } ∧
      StoreRel sourceStore machine.store ∧
      CodeStateRel callerTrace next (value :: callerSource)
        nextCallerFrame := by
  dsimp only
  have callerEnvironments : EnvRel callerSource
      ({ callerFrame with pc := callerFrame.pc + 1 } : Eval.Frame).values
      callInput := by
    simpa [Lower.CodeTrace.sourceInputMap] using callerState.environments
  obtain ⟨sourceRun, targetSteps, nextStores, canonical⟩ :=
    simulate_traced_ret_resume_state calleeDescendant calleeState stores
      callerEnvironments sourceResolved control noCredits world
  have canonical' : EnvRel (value :: callerSource)
      (callerFrame.values.push value)
      (#[some (.reg callerFrame.values.size)] ++ callInput) := by
    simpa using canonical
  have nextEnvironments := canonical'.forgetTracedValue callerState
    callerDescendant binder
  refine ⟨sourceRun, ?_, nextStores,
    callerState.letOpNext callerDescendant rfl rfl rfl ?_ rfl
      nextEnvironments⟩
  · simpa using targetSteps
  · simp [delta]

/-- Baseline logical execution preserves the exact IxIR₁ heap and value.
Later credit insertion weakens this to heap isomorphism; keeping the stronger
baseline relation makes that proof boundary explicit. -/
structure OutcomeRel (source : IxIR1.Store × RVal)
    (target : Eval.Result) extends StoreRel source.1 target.store where
  value : target.value = source.2

/-- The terminal block case: a related source return and outermost target
return take one genuine control step to the same value and preserve the exact
baseline store relation. -/
theorem simulate_ret_halt {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal} {mapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (control : machine.control = .running frame [])
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .ret targetAtom)
    (noCredits : frame.credits = #[])
    (world : Eval.RVal.hasWorld machine.store
      frame.definition.signature.result value = true) :
    IxIR1.runCode sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.ret sourceAtom) = .ok (sourceStore, value) ∧
      Eval.Steps context interpretation 1 machine
        { machine with control := .halted value } ∧
      StoreRel sourceStore machine.store := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok value :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetStep := Eval.Step.retHalt (context := context)
    (interpretation := interpretation) control blockAt pc terminator
    targetResolved noCredits world
  refine ⟨?_, targetStep.toSteps control, stores⟩
  unfold IxIR1.runCode
  simp only
  rw [sourceResolved]
  rfl

/-- Trace-facing outermost return case. The recursive derivation supplies the
exact executable block, terminal PC, translated operand, and retained return
terminator, leaving only source resolution and runtime side conditions. -/
theorem simulate_traced_ret_halt_state {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : EnvMap} {entryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.ret site blockId input entryValueCount sourceAtom targetAtom generated))
    {sourceStore : IxIR1.Store} {source : List RVal} {value : RVal}
    (state : CodeStateRel functionTrace
      (.ret site blockId input entryValueCount sourceAtom targetAtom generated)
      source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (control : machine.control = .running frame [])
    (noCredits : frame.credits = #[])
    (world : Eval.RVal.hasWorld machine.store
      frame.definition.signature.result value = true) :
    IxIR1.runCode sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.ret sourceAtom) = .ok (sourceStore, value) ∧
      Eval.Steps context interpretation 1 machine
        { machine with control := .halted value } ∧
      StoreRel sourceStore machine.store := by
  have syntaxMatched := functionTrace.descendantSyntaxMatches descendant
  obtain ⟨translated, terminator⟩ :=
    Lower.CodeTrace.retSyntax_of_match syntaxMatched
  have blockAt :
      frame.definition.blocks[frame.block]? = some generated := by
    simpa [Lower.CodeTrace.headBlock] using state.blockAt descendant
  have pc : frame.pc = generated.instructions.size := by
    simpa [Lower.CodeTrace.entryPc] using state.pc
  exact simulate_ret_halt stores state.environments translated sourceResolved
    control blockAt pc terminator noCredits world

/-- Successful-run terminal case for the recursive semantic induction.
Inverting source success supplies atom resolution and the unchanged store;
the source result contract is then transported through `CodeStateRel` to
discharge the target evaluator's executable return-world check. -/
theorem simulate_traced_ret_halt_success
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat} {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : EnvMap} {entryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.ret site blockId input entryValueCount sourceAtom targetAtom generated))
    {sourceStore : IxIR1.Store} {source : List RVal}
    {sourceOutput : IxIR1.Store × RVal}
    (state : CodeStateRel functionTrace
      (.ret site blockId input entryValueCount sourceAtom targetAtom generated)
      source frame)
    (stores : StoreRel sourceStore machine.store)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 1)
      sourceCurrent sourceStore source (.ret sourceAtom) = .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame [])
    (noCredits : frame.credits = #[]) :
    ∃ value,
      sourceOutput = (sourceStore, value) ∧
        Eval.Steps context interpretation 1 machine
          { machine with control := .halted value } ∧
        StoreRel sourceStore machine.store := by
  obtain ⟨value, sourceResolved, outputEq⟩ :=
    IxIR1.runCode_ret_success sourceRun
  subst sourceOutput
  have targetWorld := state.resultWorld stores resultWorld
  obtain ⟨_, targetSteps, nextStores⟩ :=
    simulate_traced_ret_halt_state
      (sourceContext := sourceContext) (sourceCurrent := sourceCurrent)
      (sourceFuel := sourceFuel) descendant state stores sourceResolved control
      noCredits targetWorld
  exact ⟨value, rfl, targetSteps, nextStores⟩

/-- Runner-facing form of the terminal block case. The exact one-step witness
selects a control budget of one and produces the public baseline outcome. -/
theorem simulate_ret_halt_runMachine {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal} {mapping : EnvMap}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (control : machine.control = .running frame [])
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .ret targetAtom)
    (noCredits : frame.credits = #[])
    (world : Eval.RVal.hasWorld machine.store
      frame.definition.signature.result value = true) :
    let targetOut : Eval.Result :=
      { store := machine.store
        value
        controlRemaining := 0
        heapRemaining := machine.heapFuel }
    IxIR1.runCode sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.ret sourceAtom) = .ok (sourceStore, value) ∧
      Eval.runMachine context interpretation 1 machine = .ok targetOut ∧
      OutcomeRel (sourceStore, value) targetOut := by
  dsimp only
  obtain ⟨sourceRun, targetSteps, _⟩ := simulate_ret_halt
    stores environments translated sourceResolved control blockAt pc
      terminator noCredits world
  refine ⟨sourceRun, targetSteps.runMachine_halted, ?_⟩
  exact { stores with value := rfl }

/-- The block-compositional proof's public whole-main endpoint. Fuel is not
equated: source success existentially obtains independent target control and
heap-traversal budgets. -/
def SuccessfulMainSimulation (sourceContext : IxIR1.Ctx)
    (targetContext : Eval.Context) (sourceMain : IxIR1.Code)
    (sourceResult : Ix.Compiler.Ixon.Owned) (targetProgram : Program) : Prop :=
  ∀ {sourceFuel sourceOut},
    IxIR1.runOwnedMain sourceContext sourceResult sourceMain sourceFuel =
        .ok sourceOut →
    ∃ controlFuel heapFuel targetOut,
      Eval.runMain targetContext .logical targetProgram controlFuel heapFuel =
          .ok targetOut ∧
        OutcomeRel sourceOut targetOut

end Ix.Compiler.IxIR2.Lower.Sim
