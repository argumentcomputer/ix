/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.LogicalPolicy

/-! A certified claim bundle is an ordered dependency DAG. Aggregation checks
each conditional leaf, matches its complete deferred headers, and replays its
admission in one growing interface. Set subtraction alone grants no meaning.
The checked result extends every compatible interpretation of its remaining
frontier and constructs a model when that frontier is empty. -/

namespace Ix.Theory.Certified

open Model Model.SetTheory

universe u v
variable {β : Type u} [DecidableEq β]

structure ClaimNode (β : Type u) where
  subjects : List (ConstRef β)
  frontier : List (FrontierWitness β)
  declarations : List (DeclarationWitness β)
  deriving Inhabited

structure CheckedNode (fuel : Nat) (signature : PrimitiveSignature β) (store : Store β) where
  input : ClaimNode β
  receipt : ConditionalStore.{u,v} signature store input.subjects
  validation : checkConditionalStore? fuel signature store input.frontier input.subjects
    input.declarations = some receipt

def checkNode? (fuel : Nat) (signature : PrimitiveSignature β) (store : Store β)
    (node : ClaimNode β) : Option (CheckedNode.{u,v} fuel signature store) :=
  match h : checkConditionalStore?.{u,v} fuel signature store node.frontier node.subjects node.declarations with
  | none => none
  | some receipt => some ⟨node, receipt, h⟩

theorem checkNode?_input {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    {node : ClaimNode β} {result : CheckedNode.{u,v} fuel signature store}
    (h : checkNode? fuel signature store node = some result) : result.input = node := by
  unfold checkNode? at h
  split at h
  · cases h
  · cases Option.some.inj h; rfl

theorem CheckedNode.frontier_refs {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    (node : CheckedNode.{u,v} fuel signature store) :
    node.receipt.frontier.refs = node.input.frontier.map (·.ref) :=
  checkFrontier?_refs (checkConditionalStore?_frontier node.validation)

def nodeSubjects {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    (nodes : List (CheckedNode.{u,v} fuel signature store)) : List (ConstRef β) :=
  nodes.flatMap (·.input.subjects)

def nodeFrontiers {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    (nodes : List (CheckedNode.{u,v} fuel signature store)) : List (ConstRef β) :=
  nodes.flatMap (·.receipt.frontier.refs)

def outstanding {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    (nodes : List (CheckedNode.{u,v} fuel signature store)) : List (ConstRef β) :=
  (nodeFrontiers nodes).filter (fun ref => !(nodeSubjects nodes).contains ref) |>.eraseDups

/-- Dependencies refer to the external frontier or to subjects of earlier
nodes. Internal recursion stays inside one atomic declaration producer. -/
inductive DependencyOrder {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β} :
    List (ConstRef β) → List (CheckedNode.{u,v} fuel signature store) → Prop where
  | nil (known) : DependencyOrder known []
  | cons {known node rest}
      (available : ∀ ref ∈ node.receipt.frontier.refs, ref ∈ known)
      (tail : DependencyOrder (known ++ node.input.subjects) rest) :
      DependencyOrder known (node :: rest)

omit [DecidableEq β] in
theorem HeaderPresent.extend {signature : PrimitiveSignature β} {a b : Environment β}
    (extension : Extends.{u,v} signature a b) {header : Signature.Header β}
    (h : HeaderPresent a header) : HeaderPresent b header := by
  obtain ⟨entry, he, hu, ht⟩ := h.entry
  simp only [HeaderPresent, extension.lookup _ _ he]
  exact ⟨hu, ht⟩

structure ReplayResult {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    (state : CheckedInterface signature) (known : List (ConstRef β))
    (nodes : List (CheckedNode.{u,v} fuel signature store)) where
  checked : CheckedExtension.{u,v} signature store state
  order : DependencyOrder known nodes
  subjects : ∀ ref ∈ nodeSubjects nodes, (checked.result.entries ref).isSome = true
  frontiers : ∀ node ∈ nodes, ∀ header ∈ node.receipt.frontier.headers,
    HeaderPresent checked.result.entries header

def Ordinary.BlockWitness.outputs (witness : Ordinary.BlockWitness β) : List (ConstRef β) :=
  [.member witness.source 0, .member witness.recursor 0] ++
    (List.range witness.shape.shape.constructors.length).map (.ctor witness.source 0 ·)

def DeclarationWitness.outputs : DeclarationWitness β → List (ConstRef β)
  | .definition witness => [witness.ref]
  | .ordinary witness | .natural witness => witness.outputs
  | .standard witness => [witness.ref]
  | .quotient witness => Quotient.kinds.map witness.refs.ref
  | .structure witness => witness.facts.block.outputs
  | .modeled witness => witness.companions.map (·.header.ref)

/-- Reusing an already available declaration grants no additional equation,
body or fact: the interface is unchanged. Every other declaration undergoes
the full admission check. This permits shared, independently checked closures
without replacing any chosen interpretation. -/
def replayDeclarations? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : CheckedInterface signature) : List (DeclarationWitness β) →
      Option (CheckedExtension.{u,v} signature store state)
  | [] => some (CheckedExtension.refl state)
  | witness :: rest => do
    let step ← if witness.outputs.all (fun ref => (state.entries ref).isSome) then
        some (CheckedExtension.refl state)
      else checkDeclarationExtension?.{u,v} fuel (store := store) state witness
    let rest ← replayDeclarations? fuel step.result rest
    return step.trans rest

/-- All semantic checks run again in the shared prefix. This constructs
compatibility of separately checked leaves instead of selecting unrelated
models and presuming they agree. Only published subjects discharge frontiers. -/
def replayNodes? {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    (state : CheckedInterface signature) (known : List (ConstRef β)) :
    (nodes : List (CheckedNode.{u,v} fuel signature store)) →
      Option (ReplayResult state known nodes)
  | [] => some ⟨CheckedExtension.refl state, .nil known, by simp [nodeSubjects], by simp⟩
  | node :: nodes =>
    if available : node.receipt.frontier.refs.all (known.contains ·) = true then
      if aligned : node.receipt.frontier.headers.all (fun h => decide (HeaderPresent state.entries h)) = true then
        do
          let step ← replayDeclarations?.{u,v} fuel (store := store) state node.input.declarations
          if present : node.input.subjects.all (fun ref => (step.result.entries ref).isSome) = true then do
            let tail ← replayNodes? step.result (known ++ node.input.subjects) nodes
            return {
              checked := step.trans tail.checked
              order := .cons (by simpa using List.all_eq_true.mp available) tail.order
              subjects := by
                intro ref hr
                rcases List.mem_append.mp hr with hhead | htail
                · have hp := List.all_eq_true.mp present ref hhead
                  obtain ⟨entry, he⟩ := Option.isSome_iff_exists.mp hp
                  exact Option.isSome_iff_exists.mpr ⟨entry, tail.checked.extension.lookup _ _ he⟩
                · exact tail.subjects ref htail
              frontiers := by
                intro other hm header hh
                rcases List.mem_cons.mp hm with rfl | hm
                · have h : HeaderPresent state.entries header := of_decide_eq_true
                    (List.all_eq_true.mp aligned header hh)
                  exact (h.extend step.extension).extend tail.checked.extension
                · exact tail.frontiers other hm header hh
            }
          else none
      else none
    else none

structure CheckedBatch (fuel : Nat) (signature : PrimitiveSignature β) (store : Store β)
    (inputs : List (ClaimNode β)) where
  nodes : List (CheckedNode.{u,v} fuel signature store)
  exactNodes : nodes.map (·.input) = inputs
  receipt : ConditionalStore.{u,v} signature store (nodeSubjects nodes)
  exactFrontier : ∀ ref, ref ∈ receipt.frontier.refs ↔ ref ∈ outstanding nodes
  order : DependencyOrder
    (receipt.frontier.refs ++ [signature.falseType, signature.falseElim]) nodes
  frontiers : ∀ node ∈ nodes, ∀ header ∈ node.receipt.frontier.headers,
    HeaderPresent receipt.checked.result.entries header

def checkBatch? (fuel : Nat) (signature : PrimitiveSignature β) (store : Store β)
    (frontier : List (FrontierWitness β)) (inputs : List (ClaimNode β)) :
    Option (CheckedBatch.{u,v} fuel signature store inputs) :=
  if inputs.length > fuel then none else
  match hn : inputs.mapM (checkNode?.{u,v} fuel signature store) with
  | none => none
  | some nodes => do
    let dependencies ← checkFrontier?.{u,v} fuel signature store frontier
    if exactFrontier : dependencies.refs.all (outstanding nodes |>.contains ·) = true ∧
        (outstanding nodes).all (dependencies.refs.contains ·) = true then
      if fresh : (nodeSubjects nodes).all (fun ref => (dependencies.interface.entries ref).isNone) = true then do
          let replay ← replayNodes? dependencies.interface
            (dependencies.refs ++ [signature.falseType, signature.falseElim]) nodes
          return {
            nodes
            exactNodes := by
              have h := mapM_projection (checkNode?.{u,v} fuel signature store) (·.input) id
                (fun _ _ h => checkNode?_input h) hn
              simpa using h
            receipt := ⟨dependencies, replay.checked, fun r hr => Option.isNone_iff_eq_none.mp
              (List.all_eq_true.mp fresh r hr), replay.subjects⟩
            exactFrontier := by
              intro ref
              constructor
              · intro hr; simpa using List.all_eq_true.mp exactFrontier.1 ref hr
              · intro hr; simpa using List.all_eq_true.mp exactFrontier.2 ref hr
            order := replay.order
            frontiers := replay.frontiers
          }
      else none
    else none

def acceptsBatch (fuel : Nat) (signature : PrimitiveSignature β) (store : Store β)
    (frontier : List (FrontierWitness β)) (inputs : List (ClaimNode β)) : Bool :=
  (checkBatch?.{u,v} fuel signature store frontier inputs).isSome

/-- Every leaf's deferred interface is interpreted by the same final model. -/
theorem CheckedBatch.compatible_leaves {fuel : Nat} {signature : PrimitiveSignature β}
    {store : Store β} {inputs : List (ClaimNode β)}
    (batch : CheckedBatch.{u,v} fuel signature store inputs)
    (V : Type v) [SetTheory V] (constants : Assignment β V)
    (hM : signature.Compatible batch.receipt.checked.result.entries constants)
    {node : CheckedNode.{u,v} fuel signature store} (hn : node ∈ batch.nodes) :
    signature.Compatible node.receipt.frontier.interface.entries constants :=
  node.receipt.frontier.compatible batch.receipt.checked.result
    (batch.frontiers node hn) V constants hM

theorem CheckedFrontier.empty_interface {signature : PrimitiveSignature β} {store : Store β}
    (frontier : CheckedFrontier.{u,v} signature store) (h : frontier.refs = []) :
    frontier.interface.entries = signature.environment := by
  have hh : frontier.headers = [] := List.map_eq_nil_iff.mp h
  simp [CheckedFrontier.interface, hh, Signature.environment]

/-- A closed aggregate constructs its model from the pinned prelude. No
realization of a private assumption set is a hypothesis of this theorem. -/
theorem CheckedBatch.closed_has_model {fuel : Nat} {signature : PrimitiveSignature β}
    {store : Store β} {inputs : List (ClaimNode β)}
    (batch : CheckedBatch.{u,v} fuel signature store inputs)
    (closed : batch.receipt.frontier.refs = []) (V : Type v) [SetTheory V] :
    ∃ constants : Assignment β V,
      signature.Compatible batch.receipt.checked.result.entries constants ∧
      ∀ ref ∈ nodeSubjects batch.nodes, ∃ entry,
        batch.receipt.checked.result.entries ref = some entry ∧
        SourceHeader store ref entry ∧
        ∀ levels, levels.length = entry.universes → ∀ env,
          constants ref levels ∈ˢ interp constants levels env entry.type := by
  have initial : signature.Compatible batch.receipt.frontier.interface.entries
      (signature.assignment (V := V)) := by
    rw [batch.receipt.frontier.empty_interface closed]
    exact signature.compatible_assignment
  obtain ⟨constants, hM, _, subjects⟩ := batch.receipt.subject_sound V signature.assignment initial
  refine ⟨constants, hM, ?_⟩
  intro ref hr
  obtain ⟨entry, he, _, hs, hm⟩ := subjects ref hr
  exact ⟨entry, he, hs, fun levels hl env => (hm levels hl env).2⟩

end Ix.Theory.Certified
