import Ix.Compiler.IxIR2.Validate
import Ix.Compiler.IxIR2.CreditFree

/-!
# Structured IxIR₁ to IxIR₂ lowering

IxIR₁ deliberately erases two facts that IxIR₂ must check: function-parameter
worlds and the full constructor identity at `fetch`, `free`, and case sites.
The lowering context supplies exactly those owner-sensitive facts.  Everything
else here is producer-computed: blocks, SSA ordinals, capability transfer,
edge parameters, scalar-leaf facts, and the proof-facing validation equation.

The baseline is intentionally conservative.  Function parameters use the
owned IxIR₁ calling convention, raw `reuse` is rejected, and every live source
environment slot is transferred at a join.  Parameter reduction, borrowing,
and reset/reuse insertion are later checked transformations over this output.

Successful lowering also retains a recursive `CodeTrace` mirroring the exact
source-code derivation.  Its checked block order and instruction coordinates
let semantic proofs recover generated CFG facts from trace membership instead
of accepting those coordinates as caller-supplied premises.
-/

namespace Ix.Compiler.IxIR2.Lower

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR2

/-- A stable source-code coordinate. `branches` records alternative indices
from outermost to innermost; `offset` counts `letOp`s in the current arm. -/
structure SourceSite where
  owner : Validate.Owner
  branches : List Nat := []
  offset : Nat := 0
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def SourceSite.next (site : SourceSite) : SourceSite :=
  { site with offset := site.offset + 1 }

def SourceSite.alternative (site : SourceSite) (index : Nat) : SourceSite :=
  { site with branches := site.branches ++ [index], offset := 0 }

/-- Facts retained from validated IxIR₀/IxIR₁ production. Missing facts
fail closed at the operation that needs them. -/
structure Context where
  /-- Parameter worlds in call order for each addressed IxIR₁ function. -/
  parameterWorlds : Address → Option (Array Owned) := fun _ => none
  schemas : Owned → CtorId → Option CtorSchema := fun _ _ => none
  /-- Exact constructor at one IxIR₁ projection. -/
  fetchCtor : SourceSite → Option CtorId := fun _ => none
  /-- Checked all-scalar constructor at one IxIR₁ shallow free. -/
  scalarFreeCtor : SourceSite → Option CtorId := fun _ => none
  /-- Full constructor identities for an IxIR₁ alternative. More than one
  identity is permitted because IxIR₁ dispatch retains only tag/arity;
  checked lowering emits one IxIR₂ edge for every producer-admitted full
  identity. An empty list permits a Nat-only alternative. -/
  caseCtors : SourceSite → Nat → List CtorId := fun _ _ => []
  /-- Generic tooling may preserve scalar externs. The certified pipeline
  leaves this false. -/
  allowExtern : Bool := false
  /-- Structural recursion budget for one source-code path. -/
  maxDepth : Nat := 100000

structure Input where
  declarations : List (Address × IxIR1.Decl)
  main : IxIR1.Code
  mainResult : Owned

/-- View the source main as a closed synthetic function, matching the target
machine's uniform function/frame representation. -/
def Input.mainDefinition (input : Input) : IxIR1.FnDef :=
  { arity := 0
    result := input.mainResult
    papSafe := false
    body := input.main }

inductive Error where
  | duplicateDeclaration (address : Address)
  | missingParameterWorlds (address : Address)
  | signature (owner : Validate.Owner) (detail : String)
  | source (site : SourceSite) (detail : String)
  | ownership (site : SourceSite) (detail : String)
  | schema (site : SourceSite) (detail : String)
  | unsupported (site : SourceSite) (detail : String)
  | resources (site : SourceSite)
  | internal (detail : String)
  | validation (error : Validate.Error)
  deriving BEq, Repr

inductive TargetPosition where
  | instruction (index : Nat)
  | terminator
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Capability tracked for one source de Bruijn binding while constructing
an SSA block.  Retaining this producer-computed state in the flat position
trace lets semantic clients recover ownership worlds without replaying the
private lowering monad. -/
inductive BindingCap where
  | scalar
  | owned (world : Owned)
  | borrowed (world : Owned) (lender : BorrowLender)
  | dead
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- One source position's producer-computed target coordinate. A source arm
may occur more than once when the same IxIR₁ alternative serves both a
constructor and a literal-Nat path. -/
structure PositionTrace where
  source : SourceSite
  block : BlockId
  target : TargetPosition
  /-- Source-slot capabilities immediately before this source operation or
  terminator.  The checked trace audits their live/dead shape against the
  recursive code trace before exposing them to simulation. -/
  sourceCapabilities : Array BindingCap
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Exact environment-to-parameter transfer generated at one edge. -/
structure EdgeTrace where
  source : SourceSite
  sourceBlock : BlockId
  target : BlockId
  /-- Source-slot map at the end of the predecessor block. Live slots name
  operands in that frame; consumed slots are absent. -/
  sourceInputMap : Array (Option Atom)
  targetParams : Array ValueCap
  implicitScalars : Nat := 0
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Shift register operands across a prefix of implicit block parameters.
Literals and erased operands are independent of the register file. -/
def shiftAtom (amount : Nat) : Atom → Atom
  | .reg id => .reg (id + amount)
  | .lit literal => .lit literal
  | .erased => .erased

/-- The proof-side successor map generated for a CFG edge. Implicit scalar
parameters occupy the prefix; every live explicit source slot is shifted past
that prefix while a consumed slot remains absent. -/
def EdgeTrace.sourceMapOf (implicitScalars : Nat)
    (explicitMap : Array (Option Atom)) : Array (Option Atom) :=
  let implicitMap := (List.range implicitScalars).toArray.map fun index =>
    some (.reg index)
  implicitMap ++ explicitMap.map fun
    | none => none
    | some atom => some (shiftAtom implicitScalars atom)

/-- Explicit edge operands derived from a predecessor source map. A consumed
slot is represented by the inert erased value so block-parameter ordinals
remain aligned with source de Bruijn slots. -/
def EdgeTrace.explicitValuesOf
    (sourceInputMap : Array (Option Atom)) : Array Atom :=
  sourceInputMap.map fun
    | none => .erased
    | some atom => atom

/-- Before any implicit prefix is added, every live successor source slot is
the same-position block parameter. -/
def EdgeTrace.explicitMapOf
    (sourceInputMap : Array (Option Atom)) : Array (Option Atom) :=
  sourceInputMap.mapIdx fun index slot =>
    match slot with
    | none => none
    | some _ => some (.reg index)

/-- Explicit operands carried by this exact generated edge. -/
def EdgeTrace.explicitValues (trace : EdgeTrace) : Array Atom :=
  EdgeTrace.explicitValuesOf trace.sourceInputMap

/-- Proof-side map for the source environment visible on entry to the
successor. Live slots name successor block-local registers; consumed slots
are absent. Implicit scalar values (currently Nat predecessors) occupy the
prefix. -/
def EdgeTrace.sourceMap (trace : EdgeTrace) : Array (Option Atom) :=
  EdgeTrace.sourceMapOf trace.implicitScalars
    (EdgeTrace.explicitMapOf trace.sourceInputMap)

namespace InputMap

/-- Translate one source atom through a partial source-slot map. -/
def translateAtom (mapping : Array (Option Atom)) : IxIR1.Atom → Option Atom
  | .var index => (mapping[index]?).bind id
  | .lit literal => some (.lit literal)
  | .erased => some .erased

/-- Translate a source operand vector pointwise and in order. -/
def translateAtoms (mapping : Array (Option Atom))
    (atoms : Array IxIR1.Atom) : Option (Array Atom) := do
  let translated ← atoms.toList.mapM (translateAtom mapping)
  return translated.toArray

/-- A successor proof map may forget live slots but cannot retarget one. -/
def Forgets (next current : Array (Option Atom)) : Prop :=
  ∀ (index : Nat) (atom : Atom),
    next[index]? = some (some atom) →
    current[index]? = some (some atom)

/-- Finite executable check for `Forgets`. -/
def checksForgets (next current : Array (Option Atom)) : Bool :=
  (List.range next.size).all fun index =>
    match next[index]? with
    | some (some atom) => current[index]? == some (some atom)
    | _ => true

/-- Reflect the finite forgetting check into its proof-facing relation. -/
theorem forgets_of_check {next current : Array (Option Atom)}
    (checked : checksForgets next current = true) :
    Forgets next current := by
  intro index atom nextAt
  have bound : index < next.size :=
    (Array.getElem?_eq_some_iff.mp nextAt).1
  have member : index ∈ List.range next.size := List.mem_range.mpr bound
  have point := List.all_eq_true.mp checked index member
  simp [nextAt] at point
  exact point

end InputMap

/-- Derivation-shaped output of one successful `compileCode` call.  Unlike
the flat position and edge indexes below, this tree preserves the exact
recursive structure on which the block-compositional simulation proceeds.
Terminal nodes retain the installed block; instruction nodes retain the
pre/post source maps and recursive continuation; switch nodes retain their
locally generated edges and recursive child runs in production order. -/
inductive CodeTrace where
  | ret (source : SourceSite) (sourceBlock : BlockId)
      (sourceInputMap : Array (Option Atom))
      (entryValueCount : Nat)
      (sourceAtom : IxIR1.Atom) (targetAtom : Atom) (generated : Block)
  | tailCall (source : SourceSite) (sourceBlock : BlockId)
      (sourceInputMap : Array (Option Atom)) (entryValueCount : Nat)
      (address : Address)
      (arguments : Array IxIR1.Atom) (generated : Block)
  | tailCallSelf (source : SourceSite) (sourceBlock : BlockId)
      (sourceInputMap : Array (Option Atom)) (entryValueCount : Nat)
      (arguments : Array IxIR1.Atom) (generated : Block)
  | letOp (source : SourceSite) (sourceBlock : BlockId)
      (sourceInputMap nextInputMap : Array (Option Atom))
      (entryValueCount : Nat)
      (operation : IxIR1.Op) (targetIndex : Nat)
      (targetInstruction : Instr) (next : CodeTrace)
  | switchValue (source : SourceSite) (sourceBlock : BlockId)
      (sourceInputMap : Array (Option Atom)) (entryValueCount : Nat)
      (sourceScrutinee : IxIR1.Atom) (peelNat : Bool)
      (alternatives : Array IxIR1.Alt) (targetScrutinee : Atom)
      (generated : Block) (outgoing : List EdgeTrace)
      (children : List CodeTrace)

/-- Root source coordinate of one recursive compiler run. -/
def CodeTrace.source : CodeTrace → SourceSite
  | .ret source .. | .tailCall source .. | .tailCallSelf source ..
  | .letOp source .. | .switchValue source .. => source

/-- Block in which one recursive compiler run begins. -/
def CodeTrace.sourceBlock : CodeTrace → BlockId
  | .ret _ block .. | .tailCall _ block .. | .tailCallSelf _ block ..
  | .letOp _ block .. | .switchValue _ block .. => block

/-- Proof map visible at the beginning of one recursive compiler run. -/
def CodeTrace.sourceInputMap : CodeTrace → Array (Option Atom)
  | .ret _ _ input .. | .tailCall _ _ input ..
  | .tailCallSelf _ _ input .. | .letOp _ _ input ..
  | .switchValue _ _ input .. => input

/-- Number of target value registers present when this recursive compiler
run begins. -/
def CodeTrace.entryValueCount : CodeTrace → Nat
  | .ret _ _ _ count .. | .tailCall _ _ _ count ..
  | .tailCallSelf _ _ _ count .. | .letOp _ _ _ _ count ..
  | .switchValue _ _ _ count .. => count

/-- Exact IxIR₁ code consumed by one recursive compiler call.  The source
syntax is reconstructed from constructor payloads, so instruction
continuations recurse through the same tree used by the semantic proof. -/
def CodeTrace.sourceCode : CodeTrace → IxIR1.Code
  | .ret _ _ _ _ source _ _ => .ret source
  | .tailCall _ _ _ _ address arguments _ =>
      .letOp (.call address arguments) (.ret (.var 0))
  | .tailCallSelf _ _ _ _ arguments _ =>
      .letOp (.callSelf arguments) (.ret (.var 0))
  | .letOp _ _ _ _ _ operation _ _ next =>
      .letOp operation next.sourceCode
  | .switchValue _ _ _ _ scrutinee peelNat alternatives _ _ _ _ =>
      .case scrutinee peelNat alternatives

/-- Installed blocks in reservation/production order.  A `letOp` remains in
its continuation's block, while a switch owns its terminal block and then the
blocks recursively produced for its children. -/
def CodeTrace.blocks : CodeTrace → List (BlockId × Block)
  | .ret _ block _ _ _ _ generated
  | .tailCall _ block _ _ _ _ generated
  | .tailCallSelf _ block _ _ _ generated => [(block, generated)]
  | .letOp _ _ _ _ _ _ _ _ next => next.blocks
  | .switchValue _ block _ _ _ _ _ _ generated _ children =>
      (block, generated) :: children.flatMap CodeTrace.blocks

/-- The block completed by a compiler call before descending into any switch
children.  Leading instruction nodes share their continuation's block. -/
def CodeTrace.headBlock : CodeTrace → BlockId × Block
  | .ret _ block _ _ _ _ generated
  | .tailCall _ block _ _ _ _ generated
  | .tailCallSelf _ block _ _ _ generated
  | .switchValue _ block _ _ _ _ _ _ generated _ _ => (block, generated)
  | .letOp _ _ _ _ _ _ _ _ next => next.headBlock

/-- Target program counter at which this recursive compiler call begins.
Terminal/switch nodes begin at their completed instruction-array length;
instruction nodes begin at their retained instruction coordinate. -/
def CodeTrace.entryPc : CodeTrace → Nat
  | .ret _ _ _ _ _ _ generated
  | .tailCall _ _ _ _ _ _ generated
  | .tailCallSelf _ _ _ _ _ generated
  | .switchValue _ _ _ _ _ _ _ _ generated _ _ =>
      generated.instructions.size
  | .letOp _ _ _ _ _ _ index _ _ => index

/-- Flat producer position corresponding to the beginning of this recursive
trace node. -/
def CodeTrace.targetPosition : CodeTrace → TargetPosition
  | .letOp _ _ _ _ _ _ index _ _ => .instruction index
  | .ret .. | .tailCall .. | .tailCallSelf .. | .switchValue .. =>
      .terminator

/-- The completed head block is always present in the recursive block list. -/
theorem CodeTrace.headBlock_mem_blocks :
    ∀ trace : CodeTrace, trace.headBlock ∈ trace.blocks
  | .ret .. => by simp [CodeTrace.headBlock, CodeTrace.blocks]
  | .tailCall .. => by simp [CodeTrace.headBlock, CodeTrace.blocks]
  | .tailCallSelf .. => by simp [CodeTrace.headBlock, CodeTrace.blocks]
  | .letOp _ _ _ _ _ _ _ _ next => by
      simpa [CodeTrace.headBlock, CodeTrace.blocks] using
        CodeTrace.headBlock_mem_blocks next
  | .switchValue .. => by simp [CodeTrace.headBlock, CodeTrace.blocks]

/-- Immediate recursive compiler calls.  Instruction nodes have one
continuation; switch nodes expose every constructor/Nat child in production
order; terminal nodes have none. -/
def CodeTrace.children : CodeTrace → List CodeTrace
  | .letOp _ _ _ _ _ _ _ _ next => [next]
  | .switchValue _ _ _ _ _ _ _ _ _ _ children => children
  | _ => []

/-- Local block-entry ABI check for one recursive compiler node. Nodes that
begin after an already emitted instruction do not introduce a target block
entry and therefore impose no parameter-count condition. -/
def CodeTrace.entryValueCountMatches (trace : CodeTrace) : Bool :=
  if trace.entryPc == 0 then
    trace.entryValueCount == trace.headBlock.2.valueParams.size
  else
    true

mutual

/-- Executable recursive audit that every compiler node beginning at target
PC zero has exactly the value-register count declared by its completed head
block's parameter ABI. -/
def CodeTrace.entryValueCountsMatch : CodeTrace → Bool
  | trace@(.ret ..) | trace@(.tailCall ..) | trace@(.tailCallSelf ..) =>
      trace.entryValueCountMatches
  | trace@(.letOp _ _ _ _ _ _ _ _ next) =>
      trace.entryValueCountMatches && next.entryValueCountsMatch
  | trace@(.switchValue _ _ _ _ _ _ _ _ _ _ children) =>
      trace.entryValueCountMatches &&
        codeTraceListEntryValueCountsMatch children

private def codeTraceListEntryValueCountsMatch : List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.entryValueCountsMatch &&
        codeTraceListEntryValueCountsMatch rest

end

/-- Reflexive/transitive reachability through the exact recursive compiler
call tree. -/
inductive CodeTrace.Descendant (root : CodeTrace) : CodeTrace → Prop where
  | refl : Descendant root root
  | step {parent child : CodeTrace} :
      Descendant root parent → child ∈ parent.children →
      Descendant root child

/-- Blocks produced by an immediate recursive call remain in the parent's
flattened canonical block list. -/
theorem CodeTrace.blocks_subset_of_child {parent child : CodeTrace}
    (childMem : child ∈ parent.children) :
    ∀ {entry : BlockId × Block}, entry ∈ child.blocks →
      entry ∈ parent.blocks := by
  cases parent with
  | ret _ _ _ _ _ _ _ =>
      simp [CodeTrace.children] at childMem
  | tailCall _ _ _ _ _ _ _ =>
      simp [CodeTrace.children] at childMem
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at childMem
  | letOp _ _ _ _ _ _ _ _ next =>
      simp [CodeTrace.children] at childMem
      subst child
      intro entry member
      simpa [CodeTrace.blocks] using member
  | switchValue source block input entryValueCount sourceScrutinee peel alternatives
      targetScrutinee generated outgoing children =>
      intro entry member
      simp only [CodeTrace.children] at childMem
      simp only [CodeTrace.blocks, List.mem_cons]
      right
      exact List.mem_flatMap.mpr ⟨child, childMem, member⟩

/-- Every descendant's blocks remain blocks of the root compiler run. -/
theorem CodeTrace.Descendant.blocks_subset {root child : CodeTrace}
    (descendant : Descendant root child) :
    ∀ {entry : BlockId × Block}, entry ∈ child.blocks →
      entry ∈ root.blocks := by
  induction descendant with
  | refl => exact fun member => member
  | @step parent child parentDescendant childMem ih =>
      intro entry member
      exact ih (CodeTrace.blocks_subset_of_child childMem member)

namespace CodeTrace

/-- Extract the local block-entry ABI check from the recursive certificate. -/
theorem entryValueCountMatches_of_match {trace : CodeTrace}
    (matched : trace.entryValueCountsMatch = true) :
    trace.entryValueCountMatches = true := by
  cases trace with
  | ret source block input entryValueCount sourceAtom targetAtom generated =>
      simpa [CodeTrace.entryValueCountsMatch] using matched
  | tailCall source block input entryValueCount address arguments generated =>
      simpa [CodeTrace.entryValueCountsMatch] using matched
  | tailCallSelf source block input entryValueCount arguments generated =>
      simpa [CodeTrace.entryValueCountsMatch] using matched
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      simp only [CodeTrace.entryValueCountsMatch, Bool.and_eq_true] at matched
      exact matched.1
  | switchValue source block input entryValueCount sourceScrutinee peel
      alternatives targetScrutinee generated outgoing children =>
      simp only [CodeTrace.entryValueCountsMatch, Bool.and_eq_true] at matched
      exact matched.1

/-- At a checked target block entry, the retained target value count is
exactly the completed head block's value-parameter count. -/
theorem entryValueCount_eq_headParams_of_match
    {trace : CodeTrace} (matched : trace.entryValueCountsMatch = true)
    (pc : trace.entryPc = 0) :
    trace.entryValueCount = trace.headBlock.2.valueParams.size := by
  have localMatch := CodeTrace.entryValueCountMatches_of_match matched
  change (if trace.entryPc == 0 then
      trace.entryValueCount == trace.headBlock.2.valueParams.size
    else true) = true at localMatch
  rw [if_pos (beq_iff_eq.mpr pc)] at localMatch
  exact beq_iff_eq.mp localMatch

private theorem codeTraceListEntryValueCountsMatch_of_mem
    {traces : List CodeTrace} {child : CodeTrace}
    (matched : codeTraceListEntryValueCountsMatch traces = true)
    (member : child ∈ traces) : child.entryValueCountsMatch = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListEntryValueCountsMatch, Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- The recursive block-entry ABI audit is inherited by every immediate
compiler continuation or switch child. -/
theorem entryValueCountsMatch_of_child {parent child : CodeTrace}
    (matched : parent.entryValueCountsMatch = true)
    (member : child ∈ parent.children) :
    child.entryValueCountsMatch = true := by
  cases parent with
  | ret source block input entryValueCount sourceAtom targetAtom generated =>
      simp [CodeTrace.children] at member
  | tailCall source block input entryValueCount address arguments generated =>
      simp [CodeTrace.children] at member
  | tailCallSelf source block input entryValueCount arguments generated =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      simp [CodeTrace.children] at member
      subst child
      simp only [CodeTrace.entryValueCountsMatch, Bool.and_eq_true] at matched
      exact matched.2
  | switchValue source block input entryValueCount sourceScrutinee peel
      alternatives targetScrutinee generated outgoing children =>
      simp only [CodeTrace.entryValueCountsMatch, Bool.and_eq_true] at matched
      exact codeTraceListEntryValueCountsMatch_of_mem
        matched.2 member

/-- Every recursive descendant inherits the checked block-entry target-value
ABI certificate. -/
theorem Descendant.entryValueCountsMatch {root child : CodeTrace}
    (descendant : Descendant root child)
    (matched : root.entryValueCountsMatch = true) :
    child.entryValueCountsMatch = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.entryValueCountsMatch_of_child ih childMem

section InductTree

variable (motive : CodeTrace → Prop)
  (retCase : ∀ source block input entryValueCount sourceAtom targetAtom generated,
    motive (.ret source block input entryValueCount sourceAtom targetAtom generated))
  (tailCallCase : ∀ source block input entryValueCount address arguments generated,
    motive (.tailCall source block input entryValueCount address arguments generated))
  (tailCallSelfCase : ∀ source block input entryValueCount arguments generated,
    motive (.tailCallSelf source block input entryValueCount arguments generated))
  (letOpCase : ∀ source block input nextInput entryValueCount operation targetIndex
      targetInstruction next,
    motive next →
    motive (.letOp source block input nextInput entryValueCount operation targetIndex
      targetInstruction next))
  (switchCase : ∀ source block input entryValueCount sourceScrutinee peel alternatives
      targetScrutinee generated outgoing children,
    (∀ child, child ∈ children → motive child) →
    motive (.switchValue source block input entryValueCount sourceScrutinee peel alternatives
      targetScrutinee generated outgoing children))

include retCase tailCallCase tailCallSelfCase letOpCase switchCase

mutual

private theorem inductTreeCore : (trace : CodeTrace) → motive trace
  | .ret source block input entryValueCount sourceAtom targetAtom generated =>
      retCase source block input entryValueCount sourceAtom targetAtom generated
  | .tailCall source block input entryValueCount address arguments generated =>
      tailCallCase source block input entryValueCount address arguments generated
  | .tailCallSelf source block input entryValueCount arguments generated =>
      tailCallSelfCase source block input entryValueCount arguments generated
  | .letOp source block input nextInput entryValueCount operation targetIndex
      targetInstruction next =>
      letOpCase source block input nextInput entryValueCount operation targetIndex
        targetInstruction next (inductTreeCore next)
  | .switchValue source block input entryValueCount sourceScrutinee peel alternatives
      targetScrutinee generated outgoing children =>
      switchCase source block input entryValueCount sourceScrutinee peel alternatives
        targetScrutinee generated outgoing children
          (inductTreeListCore children)

private theorem inductTreeListCore :
    (traces : List CodeTrace) → ∀ child, child ∈ traces → motive child
  | [], child, member => by
      let _ := retCase
      let _ := tailCallCase
      let _ := tailCallSelfCase
      let _ := letOpCase
      let _ := switchCase
      simp at member
  | head :: tail, child, member => by
      simp only [List.mem_cons] at member
      cases member with
      | inl equal =>
          subst child
          exact inductTreeCore head
      | inr member => exact inductTreeListCore tail child member

end

/-- Tree induction that exposes hypotheses for every switch child nested in
the list.  This is the proof principle used by the semantic simulation; it
avoids rebuilding recursion from the flat position/edge indexes. -/
theorem inductTree (trace : CodeTrace) : motive trace :=
  inductTreeCore motive retCase tailCallCase tailCallSelfCase letOpCase
    switchCase trace

end InductTree

end CodeTrace

/-- Exact source-operation/target-instruction syntax correspondence for the
baseline lowering subset. Constructor identities erased by IxIR₁ are checked
elsewhere; all retained operands, addresses, fields, and worlds agree here. -/
def operationMatches (input : Array (Option Atom)) : IxIR1.Op → Instr → Bool
  | .pure source, .move target =>
      InputMap.translateAtom input source == some target
  | .alloc sourceWorld sourceCtor sourceArgs,
      .alloc targetWorld targetCtor targetArgs =>
      sourceWorld == targetWorld && sourceCtor == targetCtor &&
        InputMap.translateAtoms input sourceArgs == some targetArgs
  | .free source, .freeUnique target _
  | .dup source, .retainShared target
  | .drop source, .releaseShared target
  | .dropU source, .dropUnique target =>
      InputMap.translateAtom input source == some target
  | .fetch source sourceField, .fetch target _ targetField =>
      sourceField == targetField &&
        InputMap.translateAtom input source == some target
  | .call sourceAddress sourceArgs, .call targetAddress targetArgs
  | .papp sourceAddress sourceArgs, .papp targetAddress targetArgs
  | .extern sourceAddress sourceArgs, .extern targetAddress targetArgs =>
      sourceAddress == targetAddress &&
        InputMap.translateAtoms input sourceArgs == some targetArgs
  | .callSelf sourceArgs, .callSelf targetArgs =>
      InputMap.translateAtoms input sourceArgs == some targetArgs
  | .apply sourceFunction sourceArgs, .apply targetFunction targetArgs =>
      InputMap.translateAtom input sourceFunction == some targetFunction &&
        InputMap.translateAtoms input sourceArgs == some targetArgs
  | _, _ => false

/-- Proof-facing form of `operationMatches`. It exposes exactly the retained
operand/address/field syntax while intentionally leaving erased constructor
identity at fetch/free sites to the owner-keyed provenance sidecars. -/
def OperationSyntax (input : Array (Option Atom)) : IxIR1.Op → Instr → Prop
  | .pure source, .move target =>
      InputMap.translateAtom input source = some target
  | .alloc sourceWorld sourceCtor sourceArgs,
      .alloc targetWorld targetCtor targetArgs =>
      sourceWorld = targetWorld ∧ sourceCtor = targetCtor ∧
        InputMap.translateAtoms input sourceArgs = some targetArgs
  | .free source, .freeUnique target _
  | .dup source, .retainShared target
  | .drop source, .releaseShared target
  | .dropU source, .dropUnique target =>
      InputMap.translateAtom input source = some target
  | .fetch source sourceField, .fetch target _ targetField =>
      sourceField = targetField ∧
        InputMap.translateAtom input source = some target
  | .call sourceAddress sourceArgs, .call targetAddress targetArgs
  | .papp sourceAddress sourceArgs, .papp targetAddress targetArgs
  | .extern sourceAddress sourceArgs, .extern targetAddress targetArgs =>
      sourceAddress = targetAddress ∧
        InputMap.translateAtoms input sourceArgs = some targetArgs
  | .callSelf sourceArgs, .callSelf targetArgs =>
      InputMap.translateAtoms input sourceArgs = some targetArgs
  | .apply sourceFunction sourceArgs, .apply targetFunction targetArgs =>
      InputMap.translateAtom input sourceFunction = some targetFunction ∧
        InputMap.translateAtoms input sourceArgs = some targetArgs
  | _, _ => False

/-- Reflect executable operation syntax checking into its proof-facing form. -/
theorem operationSyntax_of_match {input : Array (Option Atom)}
    {source : IxIR1.Op} {target : Instr}
    (matched : operationMatches input source target = true) :
    OperationSyntax input source target := by
  cases source <;> cases target <;>
    simp_all [operationMatches, OperationSyntax, Bool.and_eq_true]

mutual

/-- Executable syntax/terminator coherence for the recursive compiler trace. -/
def CodeTrace.syntaxMatches : CodeTrace → Bool
  | .ret _ _ input _ sourceAtom targetAtom generated =>
      (InputMap.translateAtom input sourceAtom == some targetAtom) &&
        (generated.terminator == .ret targetAtom)
  | .tailCall _ _ input _ sourceAddress sourceArgs generated =>
      match generated.terminator with
      | .tailCall targetAddress targetArgs =>
          sourceAddress == targetAddress &&
            (InputMap.translateAtoms input sourceArgs == some targetArgs)
      | _ => false
  | .tailCallSelf _ _ input _ sourceArgs generated =>
      match generated.terminator with
      | .tailCallSelf targetArgs =>
          InputMap.translateAtoms input sourceArgs == some targetArgs
      | _ => false
  | .letOp _ _ input _ _ operation _ instruction next =>
      operationMatches input operation instruction && next.syntaxMatches
  | .switchValue _ _ input _ sourceScrutinee _ _ targetScrutinee generated
      _ children =>
      (InputMap.translateAtom input sourceScrutinee == some targetScrutinee) &&
        (match generated.terminator with
        | .switchValue actual _ _ => actual == targetScrutinee
        | _ => false) &&
        codeTraceListSyntaxMatches children

private def codeTraceListSyntaxMatches : List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.syntaxMatches && codeTraceListSyntaxMatches rest

end

/-- Local syntax facts at an instruction trace node. -/
theorem CodeTrace.letOpSyntax_of_match
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {operation : IxIR1.Op} {index : Nat} {instruction : Instr}
    {next : CodeTrace}
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      operation index instruction next).syntaxMatches = true) :
    operationMatches input operation instruction = true ∧
      next.syntaxMatches = true := by
  simpa [CodeTrace.syntaxMatches, Bool.and_eq_true] using matched

/-- Proof-facing source/target operation syntax at one checked instruction
trace node. -/
theorem CodeTrace.letOpOperationSyntax_of_match
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {operation : IxIR1.Op} {index : Nat} {instruction : Instr}
    {next : CodeTrace}
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      operation index instruction next).syntaxMatches = true) :
    OperationSyntax input operation instruction :=
  operationSyntax_of_match (CodeTrace.letOpSyntax_of_match matched).1

/-- Local syntax and terminator facts at a return trace node. -/
theorem CodeTrace.retSyntax_of_match
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {generated : Block}
    (matched : (CodeTrace.ret source block input entryValueCount sourceAtom
      targetAtom generated).syntaxMatches = true) :
    InputMap.translateAtom input sourceAtom = some targetAtom ∧
      generated.terminator = .ret targetAtom := by
  change ((InputMap.translateAtom input sourceAtom == some targetAtom) &&
    (generated.terminator == Terminator.ret targetAtom)) = true at matched
  simp only [Bool.and_eq_true] at matched
  exact ⟨beq_iff_eq.mp matched.1, beq_iff_eq.mp matched.2⟩

/-- A coherent addressed tail-call node exposes the exact emitted argument
vector and terminator. -/
theorem CodeTrace.tailCallSyntax_of_match
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {address : Address} {sourceArgs : Array IxIR1.Atom}
    {generated : Block}
    (matched : (CodeTrace.tailCall source block input entryValueCount address
      sourceArgs generated).syntaxMatches = true) :
    ∃ targetArgs,
      InputMap.translateAtoms input sourceArgs = some targetArgs ∧
        generated.terminator = .tailCall address targetArgs := by
  cases terminatorEq : generated.terminator with
  | jump edge => simp [CodeTrace.syntaxMatches, terminatorEq] at matched
  | switchValue scrutinee constructors natPeel =>
      simp [CodeTrace.syntaxMatches, terminatorEq] at matched
  | branchCredit credit someEdge noneEdge =>
      simp [CodeTrace.syntaxMatches, terminatorEq] at matched
  | ret value => simp [CodeTrace.syntaxMatches, terminatorEq] at matched
  | tailCall targetAddress targetArgs =>
      simp only [CodeTrace.syntaxMatches, terminatorEq, Bool.and_eq_true] at matched
      have addressEq : address = targetAddress := beq_iff_eq.mp matched.1
      subst targetAddress
      exact ⟨targetArgs, beq_iff_eq.mp matched.2, rfl⟩
  | tailCallSelf targetArgs =>
      simp [CodeTrace.syntaxMatches, terminatorEq] at matched

/-- A coherent self-tail-call node exposes the exact emitted argument vector
and terminator. -/
theorem CodeTrace.tailCallSelfSyntax_of_match
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {sourceArgs : Array IxIR1.Atom} {generated : Block}
    (matched : (CodeTrace.tailCallSelf source block input entryValueCount
      sourceArgs generated).syntaxMatches = true) :
    ∃ targetArgs,
      InputMap.translateAtoms input sourceArgs = some targetArgs ∧
        generated.terminator = .tailCallSelf targetArgs := by
  cases terminatorEq : generated.terminator with
  | jump edge => simp [CodeTrace.syntaxMatches, terminatorEq] at matched
  | switchValue scrutinee constructors natPeel =>
      simp [CodeTrace.syntaxMatches, terminatorEq] at matched
  | branchCredit credit someEdge noneEdge =>
      simp [CodeTrace.syntaxMatches, terminatorEq] at matched
  | ret value => simp [CodeTrace.syntaxMatches, terminatorEq] at matched
  | tailCall targetAddress targetArgs =>
      simp [CodeTrace.syntaxMatches, terminatorEq] at matched
  | tailCallSelf targetArgs =>
      simp only [CodeTrace.syntaxMatches, terminatorEq] at matched
      exact ⟨targetArgs, beq_iff_eq.mp matched, rfl⟩

/-- A coherent switch node exposes its translated scrutinee and exact emitted
switch terminator payload. -/
theorem CodeTrace.switchSyntax_of_match
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List EdgeTrace}
    {children : List CodeTrace}
    (matched : (CodeTrace.switchValue source block input entryValueCount
      sourceScrutinee peelNat alternatives targetScrutinee generated outgoing
      children).syntaxMatches = true) :
    ∃ constructors natPeel,
      InputMap.translateAtom input sourceScrutinee = some targetScrutinee ∧
        generated.terminator =
          .switchValue targetScrutinee constructors natPeel := by
  cases terminatorEq : generated.terminator with
  | jump edge => simp [CodeTrace.syntaxMatches, terminatorEq] at matched
  | switchValue actual constructors natPeel =>
      simp only [CodeTrace.syntaxMatches, terminatorEq, Bool.and_eq_true] at matched
      have scrutineeEq : actual = targetScrutinee := beq_iff_eq.mp matched.1.2
      subst actual
      exact ⟨constructors, natPeel, beq_iff_eq.mp matched.1.1, rfl⟩
  | branchCredit credit someEdge noneEdge =>
      simp [CodeTrace.syntaxMatches, terminatorEq] at matched
  | ret value => simp [CodeTrace.syntaxMatches, terminatorEq] at matched
  | tailCall targetAddress targetArgs =>
      simp [CodeTrace.syntaxMatches, terminatorEq] at matched
  | tailCallSelf targetArgs =>
      simp [CodeTrace.syntaxMatches, terminatorEq] at matched

private theorem codeTraceListSyntaxMatches_of_mem
    {traces : List CodeTrace} {child : CodeTrace}
    (matched : codeTraceListSyntaxMatches traces = true)
    (member : child ∈ traces) : child.syntaxMatches = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListSyntaxMatches, Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Syntax coherence is inherited by every immediate recursive call. -/
theorem CodeTrace.syntaxMatches_of_child {parent child : CodeTrace}
    (matched : parent.syntaxMatches = true)
    (member : child ∈ parent.children) :
    child.syntaxMatches = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      simp [CodeTrace.children] at member
      subst child
      exact (CodeTrace.letOpSyntax_of_match matched).2
  | switchValue source block input entryValueCount sourceScrutinee peel
      alternatives targetScrutinee generated outgoing children =>
      simp only [CodeTrace.syntaxMatches, Bool.and_eq_true] at matched
      exact codeTraceListSyntaxMatches_of_mem matched.2 member

/-- Every descendant of a syntax-coherent compiler trace retains exact
source operands and target instruction/terminator syntax. -/
theorem CodeTrace.Descendant.syntaxMatches {root child : CodeTrace}
    (descendant : Descendant root child)
    (matched : root.syntaxMatches = true) :
    child.syntaxMatches = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.syntaxMatches_of_child ih childMem

/-- Value-register delta for the syntax-directed baseline instruction subset.
Credit-producing/consuming optimized instructions are deliberately absent. -/
def Instr.baselineValueDelta : Instr → Option Nat
  | .move _ | .alloc .. | .retainShared _ | .fetch ..
  | .call .. | .callSelf _ | .papp .. | .apply .. | .extern .. => some 1
  | .releaseShared _ | .dropUnique _ | .freeUnique .. => some 0
  | .allocWith .. | .discardCredit _ | .takeUnique .. | .resetShared .. => none

/-- Proof-map atom installed for the new IxIR₁ binder produced by one
baseline target instruction. -/
def Instr.baselineBinderAtom (entryValueCount : Nat) : Instr → Option Atom
  | .move _ | .alloc .. | .retainShared _ | .fetch ..
  | .call .. | .callSelf _ | .papp .. | .apply .. | .extern .. =>
      some (.reg entryValueCount)
  | .releaseShared _ | .dropUnique _ | .freeUnique .. => some .erased
  | .allocWith .. | .discardCredit _ | .takeUnique .. | .resetShared .. => none

mutual

/-- Executable internal coherence check for instruction coordinates retained
by the recursive trace. -/
def CodeTrace.instructionsMatch : CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | .letOp source block _ nextInput entryValueCount _ index instruction next =>
      match Instr.baselineValueDelta instruction with
      | some delta =>
          (next.source == source.next) &&
            (next.sourceBlock == block) &&
            (next.sourceInputMap == nextInput) &&
            (next.entryPc == index + 1) &&
            (next.entryValueCount == entryValueCount + delta) &&
            (next.headBlock.1 == block) &&
            (next.headBlock.2.instructions[index]? == some instruction) &&
            next.instructionsMatch
      | none => false
  | .switchValue _ _ _ _ _ _ _ _ _ _ children =>
      codeTraceListInstructionsMatch children

private def codeTraceListInstructionsMatch : List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.instructionsMatch && codeTraceListInstructionsMatch rest

end

mutual

/-- Executable coherence check for proof-map progression at every recursive
instruction node. The new binder is retained at the head; every older slot
may stay identical or become dead, but can never be retargeted. -/
def CodeTrace.inputMapsMatch : CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | .letOp _ _ input nextInput entryValueCount _ _ instruction next =>
      match Instr.baselineBinderAtom entryValueCount instruction with
      | some head =>
          (nextInput.size == input.size + 1) &&
            (nextInput[0]? == some (some head)) &&
            InputMap.checksForgets nextInput (#[some head] ++ input) &&
            next.inputMapsMatch
      | none => false
  | .switchValue _ _ _ _ _ _ _ _ _ _ children =>
      codeTraceListInputMapsMatch children

private def codeTraceListInputMapsMatch : List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.inputMapsMatch && codeTraceListInputMapsMatch rest

end


/-- Decode the local proof-map coherence at an instruction node. -/
theorem CodeTrace.inputMapForgets_of_match
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {operation : IxIR1.Op}
    {index : Nat} {instruction : Instr} {next : CodeTrace}
    {head : Atom}
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      operation index instruction next).inputMapsMatch = true)
    (binder : Instr.baselineBinderAtom entryValueCount instruction =
      some head) :
    nextInput.size = input.size + 1 ∧
      nextInput[0]? = some (some head) ∧
      InputMap.Forgets nextInput (#[some head] ++ input) ∧
      next.inputMapsMatch = true := by
  change (match Instr.baselineBinderAtom entryValueCount instruction with
    | some actual =>
        (nextInput.size == input.size + 1) &&
          (nextInput[0]? == some (some actual)) &&
          InputMap.checksForgets nextInput (#[some actual] ++ input) &&
          next.inputMapsMatch
    | none => false) = true at matched
  rw [binder] at matched
  simp only [Bool.and_eq_true] at matched
  exact ⟨beq_iff_eq.mp matched.1.1.1,
    beq_iff_eq.mp matched.1.1.2,
    InputMap.forgets_of_check matched.1.2, matched.2⟩

/-- Every retained instruction binder grows the source proof map by exactly
one slot, even when its target instruction is effect-only. -/
theorem CodeTrace.inputMapSize_of_match
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {operation : IxIR1.Op}
    {index : Nat} {instruction : Instr} {next : CodeTrace}
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      operation index instruction next).inputMapsMatch = true) :
    nextInput.size = input.size + 1 := by
  cases binder : Instr.baselineBinderAtom entryValueCount instruction with
  | none => simp [CodeTrace.inputMapsMatch, binder] at matched
  | some head =>
      exact (CodeTrace.inputMapForgets_of_match matched binder).1

/-- Structural facts certified at one instruction/continuation node. -/
structure CodeTrace.LetOpMatch
    (source : SourceSite) (block : BlockId)
    (input nextInput : Array (Option Atom)) (entryValueCount : Nat)
    (operation : IxIR1.Op)
    (index : Nat) (instruction : Instr) (next : CodeTrace) : Prop where
  nextSource : next.source = source.next
  nextBlock : next.sourceBlock = block
  nextInput : next.sourceInputMap = nextInput
  nextPc : next.entryPc = index + 1
  nextValueCount : next.entryValueCount = entryValueCount +
    ((Instr.baselineValueDelta instruction).getD 0)
  headBlock : next.headBlock.1 = block
  instructionAt : next.headBlock.2.instructions[index]? = some instruction
  nextInstructions : next.instructionsMatch = true

/-- Decode the executable instruction-node coherence check into the exact
source-site, environment-map, block, and instruction equalities used by the
semantic induction. -/
theorem CodeTrace.letOpMatch_of_match
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {operation : IxIR1.Op}
    {index : Nat} {instruction : Instr} {next : CodeTrace}
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      operation index instruction next).instructionsMatch = true) :
    CodeTrace.LetOpMatch source block input nextInput entryValueCount operation
      index instruction next := by
  change (match Instr.baselineValueDelta instruction with
    | some delta =>
        (next.source == source.next) &&
          (next.sourceBlock == block) &&
          (next.sourceInputMap == nextInput) &&
          (next.entryPc == index + 1) &&
          (next.entryValueCount == entryValueCount + delta) &&
          (next.headBlock.1 == block) &&
          (next.headBlock.2.instructions[index]? == some instruction) &&
          next.instructionsMatch
    | none => false) = true at matched
  cases deltaEq : Instr.baselineValueDelta instruction with
  | none => simp [deltaEq] at matched
  | some delta =>
      rw [deltaEq] at matched
      simp only [Bool.and_eq_true] at matched
      obtain ⟨⟨⟨⟨⟨⟨⟨nextSource, nextBlock⟩, nextInput⟩,
        nextPc⟩, nextValueCount⟩, headBlock⟩, instructionAt⟩,
        nextInstructions⟩ := matched
      exact
        { nextSource := beq_iff_eq.mp nextSource
          nextBlock := beq_iff_eq.mp nextBlock
          nextInput := beq_iff_eq.mp nextInput
          nextPc := beq_iff_eq.mp nextPc
          nextValueCount := by
            simpa [deltaEq] using (beq_iff_eq.mp nextValueCount)
          headBlock := beq_iff_eq.mp headBlock
          instructionAt := beq_iff_eq.mp instructionAt
          nextInstructions }

/-- A coherent recursive trace positioned at its completed block terminator
and exposing a target self tail call is itself the corresponding source
self-tail node.  A nested instruction node is excluded by its retained
instruction slot, while every other terminal trace kind emits a distinct
terminator constructor. -/
theorem CodeTrace.tailCallSelf_of_terminal
    (trace : CodeTrace) {targetArgs : Array Atom}
    (syntaxMatch : trace.syntaxMatches = true)
    (instructions : trace.instructionsMatch = true)
    (terminalPc : trace.entryPc = trace.headBlock.2.instructions.size)
    (terminator : trace.headBlock.2.terminator =
      .tailCallSelf targetArgs) :
    ∃ (source : SourceSite) (block : BlockId)
        (input : Array (Option Atom)) (entryValueCount : Nat)
        (sourceArgs : Array IxIR1.Atom) (generated : Block),
      trace = .tailCallSelf source block input entryValueCount sourceArgs
          generated ∧
        InputMap.translateAtoms input sourceArgs = some targetArgs := by
  cases trace with
  | ret source block input entryValueCount sourceAtom targetAtom generated =>
      simp only [CodeTrace.headBlock] at terminator
      have emitted := (CodeTrace.retSyntax_of_match syntaxMatch).2
      rw [emitted] at terminator
      cases terminator
  | tailCall source block input entryValueCount address sourceArgs generated =>
      simp only [CodeTrace.headBlock] at terminator
      obtain ⟨target, _translated, emitted⟩ :=
        CodeTrace.tailCallSyntax_of_match syntaxMatch
      rw [emitted] at terminator
      cases terminator
  | tailCallSelf source block input entryValueCount sourceArgs generated =>
      simp only [CodeTrace.headBlock] at terminator
      obtain ⟨target, translated, emitted⟩ :=
        CodeTrace.tailCallSelfSyntax_of_match syntaxMatch
      have targetEq : target = targetArgs := by
        rw [emitted] at terminator
        injection terminator
      subst target
      exact ⟨source, block, input, entryValueCount, sourceArgs, generated,
        rfl, translated⟩
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      have matched := CodeTrace.letOpMatch_of_match instructions
      have bound := (Array.getElem?_eq_some_iff.mp matched.instructionAt).1
      simp only [CodeTrace.entryPc, CodeTrace.headBlock] at terminalPc
      omega
  | switchValue source block input entryValueCount sourceScrutinee peelNat
      alternatives targetScrutinee generated outgoing children =>
      simp only [CodeTrace.headBlock] at terminator
      obtain ⟨constructors, natPeel, _translated, emitted⟩ :=
        CodeTrace.switchSyntax_of_match syntaxMatch
      rw [emitted] at terminator
      cases terminator

/-- A coherent instruction trace points to the exact retained instruction in
the completed block shared with its continuation. -/
theorem CodeTrace.instructionAt_of_match
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {operation : IxIR1.Op}
    {index : Nat} {instruction : Instr} {next : CodeTrace}
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      operation index instruction next).instructionsMatch = true) :
    next.headBlock.2.instructions[index]? = some instruction :=
  (CodeTrace.letOpMatch_of_match matched).instructionAt

/-- Instruction coherence also identifies the recursive run's completed head
block with the block in which that source run began. -/
theorem CodeTrace.headBlock_eq_sourceBlock_of_match {trace : CodeTrace}
    (matched : trace.instructionsMatch = true) :
    trace.headBlock.1 = trace.sourceBlock := by
  cases trace with
  | ret source sourceBlock sourceInput entryValueCount sourceAtom targetAtom generated => rfl
  | tailCall source sourceBlock sourceInput entryValueCount address arguments generated => rfl
  | tailCallSelf source sourceBlock sourceInput entryValueCount arguments generated => rfl
  | letOp source block input nextInput entryValueCount operation index instruction next =>
      exact (CodeTrace.letOpMatch_of_match matched).headBlock
  | switchValue source sourceBlock sourceInput entryValueCount sourceScrutinee peelNat
      alternatives targetScrutinee generated outgoing children => rfl

private theorem codeTraceListInstructionsMatch_of_mem
    {traces : List CodeTrace} {child : CodeTrace}
    (matched : codeTraceListInstructionsMatch traces = true)
    (member : child ∈ traces) : child.instructionsMatch = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListInstructionsMatch, Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Instruction coherence is inherited by every immediate recursive call. -/
theorem CodeTrace.instructionsMatch_of_child {parent child : CodeTrace}
    (matched : parent.instructionsMatch = true)
    (member : child ∈ parent.children) :
    child.instructionsMatch = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index instruction next =>
      simp [CodeTrace.children] at member
      subst child
      exact (CodeTrace.letOpMatch_of_match matched).nextInstructions
  | switchValue source block input entryValueCount sourceScrutinee peel alternatives
      targetScrutinee generated outgoing children =>
      exact codeTraceListInstructionsMatch_of_mem matched member

/-- Every descendant of a coherent compiler trace is instruction-coherent. -/
theorem CodeTrace.Descendant.instructionsMatch {root child : CodeTrace}
    (descendant : Descendant root child)
    (matched : root.instructionsMatch = true) :
    child.instructionsMatch = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.instructionsMatch_of_child ih childMem

private theorem codeTraceListInputMapsMatch_of_mem
    {traces : List CodeTrace} {child : CodeTrace}
    (matched : codeTraceListInputMapsMatch traces = true)
    (member : child ∈ traces) : child.inputMapsMatch = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListInputMapsMatch, Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Proof-map coherence is inherited by every immediate recursive call. -/
theorem CodeTrace.inputMapsMatch_of_child {parent child : CodeTrace}
    (matched : parent.inputMapsMatch = true)
    (member : child ∈ parent.children) :
    child.inputMapsMatch = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index instruction next =>
      simp [CodeTrace.children] at member
      subst child
      cases binder : Instr.baselineBinderAtom entryValueCount instruction with
      | none => simp [CodeTrace.inputMapsMatch, binder] at matched
      | some head =>
          exact (CodeTrace.inputMapForgets_of_match matched binder).2.2.2
  | switchValue source block input entryValueCount sourceScrutinee peel alternatives
      targetScrutinee generated outgoing children =>
      exact codeTraceListInputMapsMatch_of_mem matched member

/-- Every descendant of a coherent compiler trace has coherent proof-map
progression. -/
theorem CodeTrace.Descendant.inputMapsMatch {root child : CodeTrace}
    (descendant : Descendant root child)
    (matched : root.inputMapsMatch = true) :
    child.inputMapsMatch = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.inputMapsMatch_of_child ih childMem

private def sourceOpEq : IxIR1.Op → IxIR1.Op → Bool
  | .pure left, .pure right => left == right
  | .alloc lw lc la, .alloc rw rc ra =>
      lw == rw && lc == rc && la == ra
  | .reuse lt lc la, .reuse rt rc ra =>
      lt == rt && lc == rc && la == ra
  | .free left, .free right
  | .dup left, .dup right
  | .drop left, .drop right
  | .dropU left, .dropU right => left == right
  | .fetch lt lf, .fetch rt rf => lt == rt && lf == rf
  | .call lf la, .call rf ra
  | .papp lf la, .papp rf ra
  | .extern lf la, .extern rf ra => lf == rf && la == ra
  | .callSelf left, .callSelf right => left == right
  | .apply lf la, .apply rf ra => lf == rf && la == ra
  | _, _ => false

private theorem sourceOpEq_eq_true_iff (left right : IxIR1.Op) :
    sourceOpEq left right = true ↔ left = right := by
  cases left <;> cases right <;>
    simp [sourceOpEq, beq_iff_eq, and_assoc]

mutual

private def sourceCodeEq : IxIR1.Code → IxIR1.Code → Bool
  | .ret left, .ret right => left == right
  | .letOp leftOp leftRest, .letOp rightOp rightRest =>
      sourceOpEq leftOp rightOp && sourceCodeEq leftRest rightRest
  | .case ls lp la, .case rs rp ra =>
      ls == rs && lp == rp && sourceAltListEq la.toList ra.toList
  | _, _ => false

private def sourceAltEq : IxIR1.Alt → IxIR1.Alt → Bool
  | .mk lc lf lb, .mk rc rf rb =>
      lc == rc && lf == rf && sourceCodeEq lb rb

private def sourceAltListEq : List IxIR1.Alt → List IxIR1.Alt → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      sourceAltEq left right && sourceAltListEq leftRest rightRest
  | _, _ => false

end

mutual

private theorem sourceCodeEq_eq_true_iff
    (left right : IxIR1.Code) :
    sourceCodeEq left right = true ↔ left = right := by
  cases left <;> cases right <;>
    simp [sourceCodeEq, sourceOpEq_eq_true_iff,
      sourceCodeEq_eq_true_iff, sourceAltListEq_eq_true_iff,
      beq_iff_eq, and_assoc]

private theorem sourceAltEq_eq_true_iff
    (left right : IxIR1.Alt) :
    sourceAltEq left right = true ↔ left = right := by
  cases left
  cases right
  simp [sourceAltEq, sourceCodeEq_eq_true_iff, beq_iff_eq, and_assoc]

private theorem sourceAltListEq_eq_true_iff
    (left right : List IxIR1.Alt) :
    sourceAltListEq left right = true ↔ left = right := by
  cases left with
  | nil => cases right <;> simp [sourceAltListEq]
  | cons left leftRest =>
      cases right with
      | nil => simp [sourceAltListEq]
      | cons right rightRest =>
          simp [sourceAltListEq, sourceAltEq_eq_true_iff,
            sourceAltListEq_eq_true_iff]

end

/-- Locate the unique source alternative selected by a constructor tag,
retaining its source-array ordinal for `SourceSite.alternative`. Successful
lowering rejects duplicate tags before constructing a switch trace. -/
def sourceAlternativeAtTag? (alternatives : Array IxIR1.Alt) (tag : Nat) :
    Option (IxIR1.Alt × Nat) :=
  alternatives.toList.zipIdx.find? fun pair =>
    match pair.1 with
    | .mk candidate _ _ => candidate == tag

/-- Forgetting the retained source ordinal recovers the evaluator's ordinary
first-matching-alternative lookup. -/
theorem sourceAlternativeAtTag?_map_fst
    (alternatives : Array IxIR1.Alt) (tag : Nat) :
    (sourceAlternativeAtTag? alternatives tag).map Prod.fst =
      alternatives.find? (fun alternative =>
        match alternative with
        | .mk candidate _ _ => candidate == tag) := by
  rw [sourceAlternativeAtTag?]
  rw [← Array.find?_toList]
  let predicate : IxIR1.Alt → Bool := fun alternative =>
    match alternative with
    | .mk candidate _ _ => candidate == tag
  change Option.map Prod.fst
      (alternatives.toList.zipIdx.find? (predicate ∘ Prod.fst)) =
    alternatives.toList.find? predicate
  rw [← List.find?_map]
  simp only [List.zipIdx_map_fst]

/-- Lift the evaluator's successful alternative lookup to the indexed form
retained by a lowering trace. -/
theorem sourceAlternativeAtTag?_of_find?
    {alternatives : Array IxIR1.Alt} {tag : Nat}
    {alternative : IxIR1.Alt}
    (found : alternatives.find? (fun candidate =>
      match candidate with
      | .mk candidateTag _ _ => candidateTag == tag) = some alternative) :
    ∃ index,
      sourceAlternativeAtTag? alternatives tag = some (alternative, index) := by
  have mapped :
      (sourceAlternativeAtTag? alternatives tag).map Prod.fst =
        some alternative := by
    rw [sourceAlternativeAtTag?_map_fst, found]
  obtain ⟨pair, pairFound, first⟩ := Option.map_eq_some_iff.mp mapped
  obtain ⟨selected, index⟩ := pair
  simp only at first
  subst selected
  exact ⟨index, pairFound⟩

/-- A successful tag lookup retains the literal source-array ordinal of the
selected alternative. -/
theorem sourceAlternativeAtTag?_getElem? {alternatives : Array IxIR1.Alt}
    {tag : Nat} {alternative : IxIR1.Alt} {index : Nat}
    (found : sourceAlternativeAtTag? alternatives tag =
      some (alternative, index)) :
    alternatives[index]? = some alternative := by
  have member : (alternative, index) ∈ alternatives.toList.zipIdx :=
    List.mem_of_find?_eq_some found
  have selected : alternatives.toList[index]? = some alternative :=
    List.mk_mem_zipIdx_iff_getElem?.mp member
  simpa using selected

/-- The constructor tag stored in a successful lookup is the searched tag. -/
theorem sourceAlternativeAtTag?_tag {alternatives : Array IxIR1.Alt}
    {tag actualTag fieldCount : Nat} {body : IxIR1.Code} {index : Nat}
    (found : sourceAlternativeAtTag? alternatives tag =
      some (.mk actualTag fieldCount body, index)) :
    actualTag = tag := by
  have matched := List.find?_some found
  exact beq_iff_eq.mp matched

/-- Source proof map after a constructor edge and its generated field-fetch
prologue. IxIR₁ binds fields in reverse order, while IxIR₂ appends fetch
results in increasing field order. -/
def constructorChildInputMap (parameterCount fieldCount : Nat) :
    Array (Option Atom) :=
  (List.range fieldCount).reverse.toArray.map fun field =>
    some (.reg (parameterCount + field))

/-- Executable certificate for the exact fetch prefix inserted before a
constructor alternative's source body. -/
def fetchPrologueMatches (instructions : Array Instr) (target : Atom)
    (cid : CtorId) (fieldCount : Nat) : Bool :=
  (List.range fieldCount).all fun field =>
    instructions[field]? == some (.fetch target cid field)

/-- Every certified field ordinal names the exact generated fetch. -/
theorem fetchPrologueAt_of_match {instructions : Array Instr} {target : Atom}
    {cid : CtorId} {fieldCount field : Nat}
    (matched : fetchPrologueMatches instructions target cid fieldCount = true)
    (bound : field < fieldCount) :
    instructions[field]? = some (.fetch target cid field) := by
  have member : field ∈ List.range fieldCount := List.mem_range.mpr bound
  have checked := List.all_eq_true.mp matched field member
  exact beq_iff_eq.mp checked

/-- Exact association of one emitted constructor target, its retained edge,
and the recursive compiler call for the corresponding source alternative. -/
def constructorBranchMatches (source : SourceSite) (sourceBlock : BlockId)
    (sourceInputMap : Array (Option Atom))
    (sourceScrutinee : IxIR1.Atom) (alternatives : Array IxIR1.Alt)
    (target : CtorAlt) (edge : EdgeTrace) (child : CodeTrace) : Bool :=
  match sourceAlternativeAtTag? alternatives target.cid.cidx,
      InputMap.translateAtom (EdgeTrace.explicitMapOf sourceInputMap)
        sourceScrutinee with
  | some (.mk tag fieldCount body, alternativeIndex), some childScrutinee =>
      (tag == target.cid.cidx) &&
      (edge.source == source) &&
      (edge.sourceBlock == sourceBlock) &&
      (edge.sourceInputMap == sourceInputMap) &&
      (edge.implicitScalars == 0) &&
      (edge.targetParams.size ==
        edge.implicitScalars + edge.sourceInputMap.size) &&
      (edge.target == target.edge.target) &&
      (target.edge.values == edge.explicitValues) &&
      target.edge.credits.isEmpty &&
      (child.source == source.alternative alternativeIndex) &&
      sourceCodeEq child.sourceCode body &&
      (child.sourceBlock == edge.target) &&
      (child.sourceInputMap ==
        constructorChildInputMap edge.targetParams.size fieldCount ++
          EdgeTrace.explicitMapOf edge.sourceInputMap) &&
      (child.entryPc == fieldCount) &&
      (child.entryValueCount == edge.targetParams.size + fieldCount) &&
      (child.headBlock.1 == edge.target) &&
      (child.headBlock.2.valueParams == edge.targetParams) &&
      child.headBlock.2.creditParams.isEmpty &&
      fetchPrologueMatches child.headBlock.2.instructions childScrutinee
        target.cid fieldCount
  | _, _ => false

/-- Exact association for one literal-Nat edge. The successor edge has one
implicit scalar parameter; the zero edge has none. -/
def natBranchMatches (source : SourceSite) (sourceBlock : BlockId)
    (sourceInputMap : Array (Option Atom)) (alternatives : Array IxIR1.Alt)
    (tag fieldCount implicitScalars : Nat) (target : Edge)
    (edge : EdgeTrace) (child : CodeTrace) : Bool :=
  match sourceAlternativeAtTag? alternatives tag with
  | some (.mk actualTag actualFieldCount body, alternativeIndex) =>
      (actualTag == tag) &&
      (actualFieldCount == fieldCount) &&
      (edge.source == source) &&
      (edge.sourceBlock == sourceBlock) &&
      (edge.sourceInputMap == sourceInputMap) &&
      (edge.implicitScalars == implicitScalars) &&
      (edge.targetParams.size ==
        edge.implicitScalars + edge.sourceInputMap.size) &&
      (edge.target == target.target) &&
      (target.values == edge.explicitValues) &&
      target.credits.isEmpty &&
      (child.source == source.alternative alternativeIndex) &&
      sourceCodeEq child.sourceCode body &&
      (child.sourceBlock == edge.target) &&
      (child.sourceInputMap == edge.sourceMap) &&
      (child.entryPc == 0) &&
      (child.entryValueCount == edge.targetParams.size) &&
      (child.headBlock.1 == edge.target) &&
      (child.headBlock.2.valueParams == edge.targetParams) &&
      child.headBlock.2.creditParams.isEmpty &&
      (if implicitScalars == 1 then
        edge.targetParams[0]? == some .scalar
      else implicitScalars == 0)
  | none => false

/-- Proof-facing facts reflected from one successful constructor-branch
association check. -/
structure ConstructorBranchMatch (source : SourceSite)
    (sourceBlock : BlockId) (sourceInputMap : Array (Option Atom))
    (sourceScrutinee : IxIR1.Atom) (alternatives : Array IxIR1.Alt)
    (target : CtorAlt) (edge : EdgeTrace) (child : CodeTrace) : Type where
  alternativeIndex : Nat
  tag : Nat
  fieldCount : Nat
  body : IxIR1.Code
  childScrutinee : Atom
  sourceAlternative : sourceAlternativeAtTag? alternatives target.cid.cidx =
    some (.mk tag fieldCount body, alternativeIndex)
  translatedScrutinee :
    InputMap.translateAtom (EdgeTrace.explicitMapOf sourceInputMap)
      sourceScrutinee = some childScrutinee
  constructorTag : tag = target.cid.cidx
  edgeSource : edge.source = source
  edgeSourceBlock : edge.sourceBlock = sourceBlock
  edgeSourceInput : edge.sourceInputMap = sourceInputMap
  edgeImplicitScalars : edge.implicitScalars = 0
  edgeParameterCount : edge.targetParams.size =
    edge.implicitScalars + edge.sourceInputMap.size
  edgeTarget : edge.target = target.edge.target
  edgeValues : target.edge.values = edge.explicitValues
  edgeCredits : target.edge.credits.isEmpty = true
  childSource : child.source = source.alternative alternativeIndex
  childCode : child.sourceCode = body
  childBlock : child.sourceBlock = edge.target
  childInput : child.sourceInputMap =
    constructorChildInputMap edge.targetParams.size fieldCount ++
      EdgeTrace.explicitMapOf edge.sourceInputMap
  childPc : child.entryPc = fieldCount
  childValueCount : child.entryValueCount =
    edge.targetParams.size + fieldCount
  childHeadBlock : child.headBlock.1 = edge.target
  childParams : child.headBlock.2.valueParams = edge.targetParams
  childCredits : child.headBlock.2.creditParams.isEmpty = true
  fetchPrologue : fetchPrologueMatches child.headBlock.2.instructions
    childScrutinee target.cid fieldCount = true

/-- Reflect an executable constructor association into exact source, edge,
child, and fetch-prologue facts. -/
def constructorBranchMatch_of_match
    {source : SourceSite} {sourceBlock : BlockId}
    {sourceInputMap : Array (Option Atom)}
    {sourceScrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {target : CtorAlt} {edge : EdgeTrace} {child : CodeTrace}
    (matched : constructorBranchMatches source sourceBlock sourceInputMap
      sourceScrutinee alternatives target edge child = true) :
    ConstructorBranchMatch source sourceBlock sourceInputMap sourceScrutinee
      alternatives target edge child := by
  unfold constructorBranchMatches at matched
  generalize alternativeEq :
    sourceAlternativeAtTag? alternatives target.cid.cidx = alternative at matched
  cases alternative with
  | none => simp at matched
  | some pair =>
      obtain ⟨alternative, alternativeIndex⟩ := pair
      cases alternative with
      | mk tag fieldCount body =>
          generalize translatedEq :
            InputMap.translateAtom
              (EdgeTrace.explicitMapOf sourceInputMap) sourceScrutinee =
                translated at matched
          cases translated with
          | none => simp at matched
          | some childScrutinee =>
              simp only [Bool.and_eq_true] at matched
              obtain ⟨rest, fetchPrologue⟩ := matched
              obtain ⟨rest, childCredits⟩ := rest
              obtain ⟨rest, childParams⟩ := rest
              obtain ⟨rest, childHeadBlock⟩ := rest
              obtain ⟨rest, childValueCount⟩ := rest
              obtain ⟨rest, childPc⟩ := rest
              obtain ⟨rest, childInput⟩ := rest
              obtain ⟨rest, childBlock⟩ := rest
              obtain ⟨rest, childCode⟩ := rest
              obtain ⟨rest, childSource⟩ := rest
              obtain ⟨rest, edgeCredits⟩ := rest
              obtain ⟨rest, edgeValues⟩ := rest
              obtain ⟨rest, edgeTarget⟩ := rest
              obtain ⟨rest, edgeParameterCount⟩ := rest
              obtain ⟨rest, edgeImplicitScalars⟩ := rest
              obtain ⟨rest, edgeSourceInput⟩ := rest
              obtain ⟨rest, edgeSourceBlock⟩ := rest
              obtain ⟨constructorTag, edgeSource⟩ := rest
              exact
                { alternativeIndex
                  tag
                  fieldCount
                  body
                  childScrutinee
                  sourceAlternative := alternativeEq
                  translatedScrutinee := translatedEq
                  constructorTag := beq_iff_eq.mp constructorTag
                  edgeSource := beq_iff_eq.mp edgeSource
                  edgeSourceBlock := beq_iff_eq.mp edgeSourceBlock
                  edgeSourceInput := beq_iff_eq.mp edgeSourceInput
                  edgeImplicitScalars := beq_iff_eq.mp edgeImplicitScalars
                  edgeParameterCount := beq_iff_eq.mp edgeParameterCount
                  edgeTarget := beq_iff_eq.mp edgeTarget
                  edgeValues := beq_iff_eq.mp edgeValues
                  edgeCredits
                  childSource := beq_iff_eq.mp childSource
                  childCode := (sourceCodeEq_eq_true_iff _ _).mp childCode
                  childBlock := beq_iff_eq.mp childBlock
                  childInput := beq_iff_eq.mp childInput
                  childPc := beq_iff_eq.mp childPc
                  childValueCount := beq_iff_eq.mp childValueCount
                  childHeadBlock := beq_iff_eq.mp childHeadBlock
                  childParams := beq_iff_eq.mp childParams
                  childCredits
                  fetchPrologue }

/-- Proof-facing facts reflected from one successful literal-Nat branch
association check. -/
structure NatBranchMatch (source : SourceSite) (sourceBlock : BlockId)
    (sourceInputMap : Array (Option Atom)) (alternatives : Array IxIR1.Alt)
    (tag fieldCount implicitScalars : Nat) (target : Edge)
    (edge : EdgeTrace) (child : CodeTrace) : Type where
  alternativeIndex : Nat
  body : IxIR1.Code
  sourceAlternative : sourceAlternativeAtTag? alternatives tag =
    some (.mk tag fieldCount body, alternativeIndex)
  edgeSource : edge.source = source
  edgeSourceBlock : edge.sourceBlock = sourceBlock
  edgeSourceInput : edge.sourceInputMap = sourceInputMap
  edgeImplicitScalars : edge.implicitScalars = implicitScalars
  edgeParameterCount : edge.targetParams.size =
    edge.implicitScalars + edge.sourceInputMap.size
  edgeTarget : edge.target = target.target
  edgeValues : target.values = edge.explicitValues
  edgeCredits : target.credits.isEmpty = true
  childSource : child.source = source.alternative alternativeIndex
  childCode : child.sourceCode = body
  childBlock : child.sourceBlock = edge.target
  childInput : child.sourceInputMap = edge.sourceMap
  childPc : child.entryPc = 0
  childValueCount : child.entryValueCount = edge.targetParams.size
  childHeadBlock : child.headBlock.1 = edge.target
  childParams : child.headBlock.2.valueParams = edge.targetParams
  childCredits : child.headBlock.2.creditParams.isEmpty = true
  implicitConvention :
    (if implicitScalars == 1 then
      edge.targetParams[0]? == some .scalar
    else implicitScalars == 0) = true

/-- Reflect an executable Nat association into exact source, edge, child, and
implicit-predecessor facts. -/
def natBranchMatch_of_match
    {source : SourceSite} {sourceBlock : BlockId}
    {sourceInputMap : Array (Option Atom)} {alternatives : Array IxIR1.Alt}
    {tag fieldCount implicitScalars : Nat} {target : Edge}
    {edge : EdgeTrace} {child : CodeTrace}
    (matched : natBranchMatches source sourceBlock sourceInputMap alternatives
      tag fieldCount implicitScalars target edge child = true) :
    NatBranchMatch source sourceBlock sourceInputMap alternatives tag
      fieldCount implicitScalars target edge child := by
  unfold natBranchMatches at matched
  generalize alternativeEq :
    sourceAlternativeAtTag? alternatives tag = alternative at matched
  cases alternative with
  | none => simp at matched
  | some pair =>
      obtain ⟨alternative, alternativeIndex⟩ := pair
      cases alternative with
      | mk actualTag actualFieldCount body =>
          simp only [Bool.and_eq_true] at matched
          obtain ⟨rest, implicitConvention⟩ := matched
          obtain ⟨rest, childCredits⟩ := rest
          obtain ⟨rest, childParams⟩ := rest
          obtain ⟨rest, childHeadBlock⟩ := rest
          obtain ⟨rest, childValueCount⟩ := rest
          obtain ⟨rest, childPc⟩ := rest
          obtain ⟨rest, childInput⟩ := rest
          obtain ⟨rest, childBlock⟩ := rest
          obtain ⟨rest, childCode⟩ := rest
          obtain ⟨rest, childSource⟩ := rest
          obtain ⟨rest, edgeCredits⟩ := rest
          obtain ⟨rest, edgeValues⟩ := rest
          obtain ⟨rest, edgeTarget⟩ := rest
          obtain ⟨rest, edgeParameterCount⟩ := rest
          obtain ⟨rest, edgeImplicitScalars⟩ := rest
          obtain ⟨rest, edgeSourceInput⟩ := rest
          obtain ⟨rest, edgeSourceBlock⟩ := rest
          obtain ⟨rest, edgeSource⟩ := rest
          obtain ⟨actualTagEq, actualFieldCountEq⟩ := rest
          have tagEq : actualTag = tag := beq_iff_eq.mp actualTagEq
          have fieldCountEq : actualFieldCount = fieldCount :=
            beq_iff_eq.mp actualFieldCountEq
          subst actualTag
          subst actualFieldCount
          exact
            { alternativeIndex
              body
              sourceAlternative := alternativeEq
              edgeSource := beq_iff_eq.mp edgeSource
              edgeSourceBlock := beq_iff_eq.mp edgeSourceBlock
              edgeSourceInput := beq_iff_eq.mp edgeSourceInput
              edgeImplicitScalars := beq_iff_eq.mp edgeImplicitScalars
              edgeParameterCount := beq_iff_eq.mp edgeParameterCount
              edgeTarget := beq_iff_eq.mp edgeTarget
              edgeValues := beq_iff_eq.mp edgeValues
              edgeCredits
              childSource := beq_iff_eq.mp childSource
              childCode := (sourceCodeEq_eq_true_iff _ _).mp childCode
              childBlock := beq_iff_eq.mp childBlock
              childInput := beq_iff_eq.mp childInput
              childPc := beq_iff_eq.mp childPc
              childValueCount := beq_iff_eq.mp childValueCount
              childHeadBlock := beq_iff_eq.mp childHeadBlock
              childParams := beq_iff_eq.mp childParams
              childCredits
              implicitConvention }

/-- Local switch certificate. Constructor targets consume the first parallel
edge/child entries in emitted order; an optional Nat zero/successor pair
consumes exactly the final two. No unassociated edge or child is permitted. -/
def switchNodeBranchesMatch (source : SourceSite) (sourceBlock : BlockId)
    (sourceInputMap : Array (Option Atom))
    (sourceScrutinee : IxIR1.Atom) (peelNat : Bool)
    (alternatives : Array IxIR1.Alt) (generated : Block)
    (outgoing : List EdgeTrace) (children : List CodeTrace) : Bool :=
  match generated.terminator with
  | .switchValue _ constructors natPeel =>
      let constructorCount := constructors.size
      let natCount := if natPeel.isSome then 2 else 0
      (outgoing.length == constructorCount + natCount) &&
      (children.length == constructorCount + natCount) &&
      (constructors.toList.zipIdx.all fun pair =>
        match outgoing[pair.2]?, children[pair.2]? with
        | some edge, some child =>
            constructorBranchMatches source sourceBlock sourceInputMap
              sourceScrutinee alternatives pair.1 edge child
        | _, _ => false) &&
      match peelNat, natPeel with
      | false, none => true
      | true, some peel =>
          match outgoing[constructorCount]?, children[constructorCount]?,
              outgoing[constructorCount + 1]?, children[constructorCount + 1]?
              with
          | some zeroEdge, some zeroChild, some succEdge, some succChild =>
              natBranchMatches source sourceBlock sourceInputMap alternatives
                0 0 0 peel.zero zeroEdge zeroChild &&
              natBranchMatches source sourceBlock sourceInputMap alternatives
                1 1 1 peel.succ succEdge succChild
          | _, _, _, _ => false
      | _, _ => false
  | _ => false

/-- A checked switch exposes its exact emitted target vectors, with no spare
edge or child and with Nat presence agreeing with the source flag. -/
theorem switchBranchShape_of_match
    {source : SourceSite} {sourceBlock : BlockId}
    {sourceInputMap : Array (Option Atom)}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {generated : Block}
    {outgoing : List EdgeTrace} {children : List CodeTrace}
    (matched : switchNodeBranchesMatch source sourceBlock sourceInputMap
      sourceScrutinee peelNat alternatives generated outgoing children = true) :
    ∃ targetScrutinee constructors natPeel,
      generated.terminator =
          .switchValue targetScrutinee constructors natPeel ∧
        outgoing.length = constructors.size +
          (if natPeel.isSome then 2 else 0) ∧
        children.length = constructors.size +
          (if natPeel.isSome then 2 else 0) ∧
        peelNat = natPeel.isSome := by
  cases terminatorEq : generated.terminator with
  | jump edge => simp [switchNodeBranchesMatch, terminatorEq] at matched
  | branchCredit credit someEdge noneEdge =>
      simp [switchNodeBranchesMatch, terminatorEq] at matched
  | ret value => simp [switchNodeBranchesMatch, terminatorEq] at matched
  | tailCall function arguments =>
      simp [switchNodeBranchesMatch, terminatorEq] at matched
  | tailCallSelf arguments =>
      simp [switchNodeBranchesMatch, terminatorEq] at matched
  | switchValue targetScrutinee constructors natPeel =>
      simp only [switchNodeBranchesMatch, terminatorEq, Bool.and_eq_true] at matched
      obtain ⟨⟨⟨outgoingLength, childrenLength⟩, _⟩, natMatched⟩ := matched
      refine ⟨targetScrutinee, constructors, natPeel, rfl,
        beq_iff_eq.mp outgoingLength, beq_iff_eq.mp childrenLength, ?_⟩
      cases peelNat <;> cases natPeel <;> simp_all

/-- Select one constructor association from a checked switch once its three
parallel entries are named. The list-shape theorem above supplies their
existence; this definition supplies all semantic facts. -/
def constructorBranchMatchAt_of_switch_match
    {source : SourceSite} {sourceBlock : BlockId}
    {sourceInputMap : Array (Option Atom)}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {generated : Block}
    {outgoing : List EdgeTrace} {children : List CodeTrace}
    {targetScrutinee : Atom} {constructors : Array CtorAlt}
    {natPeel : Option NatPeel} {index : Nat} {target : CtorAlt}
    {edge : EdgeTrace} {child : CodeTrace}
    (matched : switchNodeBranchesMatch source sourceBlock sourceInputMap
      sourceScrutinee peelNat alternatives generated outgoing children = true)
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors natPeel)
    (targetAt : constructors[index]? = some target)
    (edgeAt : outgoing[index]? = some edge)
    (childAt : children[index]? = some child) :
    ConstructorBranchMatch source sourceBlock sourceInputMap sourceScrutinee
      alternatives target edge child := by
  unfold switchNodeBranchesMatch at matched
  rw [terminator] at matched
  simp only [Bool.and_eq_true] at matched
  obtain ⟨⟨⟨_, _⟩, constructorsMatched⟩, _⟩ := matched
  have targetListAt : constructors.toList[index]? = some target := by
    simpa using targetAt
  have member : (target, index) ∈ constructors.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr targetListAt
  have branchMatched :=
    List.all_eq_true.mp constructorsMatched (target, index) member
  simp [edgeAt, childAt] at branchMatched
  exact constructorBranchMatch_of_match branchMatched

/-- Select the checked Nat-zero association at the first post-constructor
ordinal. -/
def natZeroBranchMatchAt_of_switch_match
    {source : SourceSite} {sourceBlock : BlockId}
    {sourceInputMap : Array (Option Atom)}
    {sourceScrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {generated : Block} {outgoing : List EdgeTrace}
    {children : List CodeTrace} {targetScrutinee : Atom}
    {constructors : Array CtorAlt} {peel : NatPeel}
    {edge : EdgeTrace} {child : CodeTrace}
    (matched : switchNodeBranchesMatch source sourceBlock sourceInputMap
      sourceScrutinee true alternatives generated outgoing children = true)
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors (some peel))
    (edgeAt : outgoing[constructors.size]? = some edge)
    (childAt : children[constructors.size]? = some child) :
    NatBranchMatch source sourceBlock sourceInputMap alternatives 0 0 0
      peel.zero edge child := by
  unfold switchNodeBranchesMatch at matched
  rw [terminator] at matched
  simp only [Bool.and_eq_true] at matched
  obtain ⟨⟨⟨_, _⟩, _⟩, natMatched⟩ := matched
  cases succEdgeAt : outgoing[constructors.size + 1]? with
  | none => simp [edgeAt, childAt, succEdgeAt] at natMatched
  | some succEdge =>
      cases succChildAt : children[constructors.size + 1]? with
      | none => simp [edgeAt, childAt, succEdgeAt, succChildAt] at natMatched
      | some succChild =>
          simp [edgeAt, childAt, succEdgeAt, succChildAt,
            Bool.and_eq_true] at natMatched
          exact natBranchMatch_of_match natMatched.1

/-- Select the checked Nat-successor association at the second
post-constructor ordinal. -/
def natSuccBranchMatchAt_of_switch_match
    {source : SourceSite} {sourceBlock : BlockId}
    {sourceInputMap : Array (Option Atom)}
    {sourceScrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {generated : Block} {outgoing : List EdgeTrace}
    {children : List CodeTrace} {targetScrutinee : Atom}
    {constructors : Array CtorAlt} {peel : NatPeel}
    {edge : EdgeTrace} {child : CodeTrace}
    (matched : switchNodeBranchesMatch source sourceBlock sourceInputMap
      sourceScrutinee true alternatives generated outgoing children = true)
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors (some peel))
    (edgeAt : outgoing[constructors.size + 1]? = some edge)
    (childAt : children[constructors.size + 1]? = some child) :
    NatBranchMatch source sourceBlock sourceInputMap alternatives 1 1 1
      peel.succ edge child := by
  unfold switchNodeBranchesMatch at matched
  rw [terminator] at matched
  simp only [Bool.and_eq_true] at matched
  obtain ⟨⟨⟨_, _⟩, _⟩, natMatched⟩ := matched
  cases zeroEdgeAt : outgoing[constructors.size]? with
  | none => simp [edgeAt, childAt, zeroEdgeAt] at natMatched
  | some zeroEdge =>
      cases zeroChildAt : children[constructors.size]? with
      | none => simp [edgeAt, childAt, zeroEdgeAt, zeroChildAt] at natMatched
      | some zeroChild =>
          simp [edgeAt, childAt, zeroEdgeAt, zeroChildAt,
            Bool.and_eq_true] at natMatched
          exact natBranchMatch_of_match natMatched.2

/-- Both literal-Nat branches selected from one checked switch. Keeping their
parallel list coordinates in one record lets semantic clients enter either
child without repeating list-length or lookup reasoning. -/
structure NatBranchPairMatch (source : SourceSite) (sourceBlock : BlockId)
    (sourceInputMap : Array (Option Atom))
    (alternatives : Array IxIR1.Alt) (constructors : Array CtorAlt)
    (peel : NatPeel) (outgoing : List EdgeTrace)
    (children : List CodeTrace) : Type where
  zeroEdge : EdgeTrace
  zeroChild : CodeTrace
  succEdge : EdgeTrace
  succChild : CodeTrace
  zeroEdgeAt : outgoing[constructors.size]? = some zeroEdge
  zeroChildAt : children[constructors.size]? = some zeroChild
  succEdgeAt : outgoing[constructors.size + 1]? = some succEdge
  succChildAt : children[constructors.size + 1]? = some succChild
  zero : NatBranchMatch source sourceBlock sourceInputMap alternatives
    0 0 0 peel.zero zeroEdge zeroChild
  succ : NatBranchMatch source sourceBlock sourceInputMap alternatives
    1 1 1 peel.succ succEdge succChild

/-- Reflect the complete zero/successor pair from a checked Nat switch. -/
def natBranchPairMatch_of_switch_match
    {source : SourceSite} {sourceBlock : BlockId}
    {sourceInputMap : Array (Option Atom)}
    {sourceScrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {generated : Block} {outgoing : List EdgeTrace}
    {children : List CodeTrace} {targetScrutinee : Atom}
    {constructors : Array CtorAlt} {peel : NatPeel}
    (matched : switchNodeBranchesMatch source sourceBlock sourceInputMap
      sourceScrutinee true alternatives generated outgoing children = true)
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors (some peel)) :
    NatBranchPairMatch source sourceBlock sourceInputMap alternatives
      constructors peel outgoing children := by
  unfold switchNodeBranchesMatch at matched
  rw [terminator] at matched
  simp only [Bool.and_eq_true] at matched
  obtain ⟨⟨⟨_, _⟩, _⟩, natMatched⟩ := matched
  cases zeroEdgeAt : outgoing[constructors.size]? with
  | none => simp [zeroEdgeAt] at natMatched
  | some zeroEdge =>
      cases zeroChildAt : children[constructors.size]? with
      | none => simp [zeroEdgeAt, zeroChildAt] at natMatched
      | some zeroChild =>
          cases succEdgeAt : outgoing[constructors.size + 1]? with
          | none =>
              simp [zeroEdgeAt, zeroChildAt, succEdgeAt] at natMatched
          | some succEdge =>
              cases succChildAt : children[constructors.size + 1]? with
              | none =>
                  simp [zeroEdgeAt, zeroChildAt, succEdgeAt, succChildAt]
                    at natMatched
              | some succChild =>
                  simp only [zeroEdgeAt, zeroChildAt, succEdgeAt, succChildAt,
                    Bool.and_eq_true] at natMatched
                  exact
                    { zeroEdge
                      zeroChild
                      succEdge
                      succChild
                      zeroEdgeAt
                      zeroChildAt
                      succEdgeAt
                      succChildAt
                      zero := natBranchMatch_of_match natMatched.1
                      succ := natBranchMatch_of_match natMatched.2 }

mutual

/-- Recursive switch/child/prologue coherence for a whole compiler trace. -/
def CodeTrace.switchBranchesMatch : CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | .letOp _ _ _ _ _ _ _ _ next => next.switchBranchesMatch
  | .switchValue source block input _ sourceScrutinee peelNat alternatives _
      generated outgoing children =>
      switchNodeBranchesMatch source block input sourceScrutinee peelNat
        alternatives generated outgoing children &&
      codeTraceListSwitchBranchesMatch children

private def codeTraceListSwitchBranchesMatch : List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.switchBranchesMatch && codeTraceListSwitchBranchesMatch rest

end

/-- Extract the local switch association check from the recursive trace
certificate. -/
theorem CodeTrace.switchNodeBranchesMatch_of_match
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List EdgeTrace}
    {children : List CodeTrace}
    (matched : (CodeTrace.switchValue source block input entryValueCount
      sourceScrutinee peelNat alternatives targetScrutinee generated outgoing
      children).switchBranchesMatch = true) :
    switchNodeBranchesMatch source block input sourceScrutinee peelNat
      alternatives generated outgoing children = true := by
  change (switchNodeBranchesMatch source block input sourceScrutinee peelNat
    alternatives generated outgoing children &&
      codeTraceListSwitchBranchesMatch children) = true at matched
  simp only [Bool.and_eq_true] at matched
  exact matched.1

private theorem codeTraceListSwitchBranchesMatch_of_mem
    {traces : List CodeTrace} {child : CodeTrace}
    (matched : codeTraceListSwitchBranchesMatch traces = true)
    (member : child ∈ traces) : child.switchBranchesMatch = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListSwitchBranchesMatch, Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Switch coherence is inherited by every immediate recursive call. -/
theorem CodeTrace.switchBranchesMatch_of_child {parent child : CodeTrace}
    (matched : parent.switchBranchesMatch = true)
    (member : child ∈ parent.children) :
    child.switchBranchesMatch = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      simp [CodeTrace.children] at member
      subst child
      simpa [CodeTrace.switchBranchesMatch] using matched
  | switchValue source block input entryValueCount sourceScrutinee peel
      alternatives targetScrutinee generated outgoing children =>
      simp only [CodeTrace.switchBranchesMatch, Bool.and_eq_true] at matched
      exact codeTraceListSwitchBranchesMatch_of_mem matched.2 member

/-- Every descendant inherits exact switch-edge/child/prologue coherence. -/
theorem CodeTrace.Descendant.switchBranchesMatch {root child : CodeTrace}
    (descendant : Descendant root child)
    (matched : root.switchBranchesMatch = true) :
    child.switchBranchesMatch = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.switchBranchesMatch_of_child ih childMem

/-! ## Allocation-schema evidence retained for semantic simulation -/

/-- The schema fact needed by one ordinary source allocation: the lookup is
present, has exactly the source operand count, and is uniform in the source
allocation world required by IxIR₂ v0. -/
private def allocationSchemaMatches
    (schemas : Owned → CtorId → Option CtorSchema) : IxIR1.Op → Bool
  | .alloc world identity arguments =>
      match schemas world identity with
      | some schema =>
          schema.fields == Array.replicate arguments.size world
      | none => false
  | _ => true

mutual

/-- Recursive allocation-schema coherence for one compiler derivation. This
is checked after ordinary validation and retained by `Checked`, avoiding any
later inversion of the validator's dataflow implementation. -/
def CodeTrace.allocationSchemasMatch
    (schemas : Owned → CtorId → Option CtorSchema) : CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | .letOp _ _ _ _ _ operation _ _ next =>
      allocationSchemaMatches schemas operation &&
        next.allocationSchemasMatch schemas
  | .switchValue _ _ _ _ _ _ _ _ _ _ children =>
      codeTraceListAllocationSchemasMatch schemas children

private def codeTraceListAllocationSchemasMatch
    (schemas : Owned → CtorId → Option CtorSchema) :
    List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.allocationSchemasMatch schemas &&
        codeTraceListAllocationSchemasMatch schemas rest

end

/-- Reflect the exact schema lookup and uniform field vector at one retained
ordinary allocation node. -/
theorem CodeTrace.allocationSchema_of_match
    (schemas : Owned → CtorId → Option CtorSchema)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {world : Owned} {identity : CtorId}
    {arguments : Array IxIR1.Atom} {index : Nat}
    {instruction : Instr} {next : CodeTrace}
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      (.alloc world identity arguments) index instruction next).allocationSchemasMatch
        schemas = true) :
    ∃ schema, schemas world identity = some schema ∧
      schema.fields = Array.replicate arguments.size world := by
  change (allocationSchemaMatches schemas (.alloc world identity arguments) &&
    next.allocationSchemasMatch schemas) = true at matched
  simp only [Bool.and_eq_true] at matched
  have localMatch := matched.1
  unfold allocationSchemaMatches at localMatch
  cases lookup : schemas world identity with
  | none => simp [lookup] at localMatch
  | some schema =>
      refine ⟨schema, rfl, ?_⟩
      exact beq_iff_eq.mp (by simpa [lookup] using localMatch)

private theorem codeTraceListAllocationSchemasMatch_of_mem
    (schemas : Owned → CtorId → Option CtorSchema)
    {traces : List CodeTrace} {child : CodeTrace}
    (matched : codeTraceListAllocationSchemasMatch schemas traces = true)
    (member : child ∈ traces) :
    child.allocationSchemasMatch schemas = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListAllocationSchemasMatch,
        Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Allocation-schema coherence is inherited by every immediate recursive
compiler call. -/
theorem CodeTrace.allocationSchemasMatch_of_child
    (schemas : Owned → CtorId → Option CtorSchema)
    {parent child : CodeTrace}
    (matched : parent.allocationSchemasMatch schemas = true)
    (member : child ∈ parent.children) :
    child.allocationSchemasMatch schemas = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      simp [CodeTrace.children] at member
      subst child
      simp only [CodeTrace.allocationSchemasMatch, Bool.and_eq_true] at matched
      exact matched.2
  | switchValue source block input entryValueCount sourceScrutinee peel
      alternatives targetScrutinee generated outgoing children =>
      exact codeTraceListAllocationSchemasMatch_of_mem schemas matched member

/-- Every recursive trace descendant inherits the checked allocation-schema
facts of its root. -/
theorem CodeTrace.Descendant.allocationSchemasMatch
    (schemas : Owned → CtorId → Option CtorSchema)
    {root child : CodeTrace} (descendant : Descendant root child)
    (matched : root.allocationSchemasMatch schemas = true) :
    child.allocationSchemasMatch schemas = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.allocationSchemasMatch_of_child schemas ih childMem


/-- Executable structural equality for retained IxIR₁ function sources. -/
def functionSourceEq (left right : IxIR1.FnDef) : Bool :=
  left.arity == right.arity && left.result == right.result &&
    left.papSafe == right.papSafe && sourceCodeEq left.body right.body

/-- Reflection theorem for retained IxIR₁ function-source equality. -/
theorem functionSourceEq_eq_true_iff
    (left right : IxIR1.FnDef) :
    functionSourceEq left right = true ↔ left = right := by
  cases left
  cases right
  simp [functionSourceEq, sourceCodeEq_eq_true_iff,
    beq_iff_eq, and_assoc]

private def sourceDeclEq : IxIR1.Decl → IxIR1.Decl → Bool
  | .extern left, .extern right => left == right
  | .fn left, .fn right => functionSourceEq left right
  | _, _ => false

private theorem sourceDeclEq_eq_true_iff (left right : IxIR1.Decl) :
    sourceDeclEq left right = true ↔ left = right := by
  cases left <;> cases right <;>
    simp [sourceDeclEq, functionSourceEq_eq_true_iff, beq_iff_eq]

private def sourceEntryEq
    (left right : Address × IxIR1.Decl) : Bool :=
  left.1 == right.1 && sourceDeclEq left.2 right.2

private theorem sourceEntryEq_eq_true_iff
    (left right : Address × IxIR1.Decl) :
    sourceEntryEq left right = true ↔ left = right := by
  obtain ⟨leftAddress, leftDecl⟩ := left
  obtain ⟨rightAddress, rightDecl⟩ := right
  simp [sourceEntryEq, sourceDeclEq_eq_true_iff, beq_iff_eq]

private def sourceDeclListEq :
    List (Address × IxIR1.Decl) → List (Address × IxIR1.Decl) → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      sourceEntryEq left right && sourceDeclListEq leftRest rightRest
  | _, _ => false

private theorem sourceDeclListEq_eq_true_iff
    (left right : List (Address × IxIR1.Decl)) :
    sourceDeclListEq left right = true ↔ left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [sourceDeclListEq]
  | cons head tail ih =>
      cases right with
      | nil => simp [sourceDeclListEq]
      | cons rightHead rightTail =>
          simp [sourceDeclListEq, sourceEntryEq_eq_true_iff, ih]

/-- Executable equality for lowering inputs. Source syntax deliberately lacks
global `BEq` instances, so the producer reuses its exact structural source
comparators at this boundary. -/
def inputEq (left right : Input) : Bool :=
  sourceDeclListEq left.declarations right.declarations &&
    sourceCodeEq left.main right.main && left.mainResult == right.mainResult

/-- Reflection theorem for the checked lowering-input equality. -/
theorem inputEq_eq_true_iff (left right : Input) :
    inputEq left right = true ↔ left = right := by
  cases left
  cases right
  simp [inputEq, sourceDeclListEq_eq_true_iff,
    sourceCodeEq_eq_true_iff, beq_iff_eq, and_assoc]

/-- Canonical proof map at a function entry: source de Bruijn parameters are
reversed onto target call-order registers. -/
def entryInputMap (arity : Nat) : Array (Option Atom) :=
  (List.range arity).toArray.map fun sourceIndex =>
    some (.reg (arity - 1 - sourceIndex))


/-- Exact source/target identity retained around one recursive compiler
derivation.  Parameter ownership is intentionally target-only, while arity,
result world, PAP safety, and code remain the source function's facts. -/
structure FunctionSourceMatch (source : IxIR1.FnDef) (generated : Function)
    (root : CodeTrace) : Prop where
  code : root.sourceCode = source.body
  arity : generated.signature.params.size = source.arity
  result : generated.signature.result = source.result
  papSafe : generated.signature.papSafe = source.papSafe
  entryBlock : root.sourceBlock = 0
  entryPc : root.entryPc = 0
  entryValueCount : root.entryValueCount = source.arity
  entryInput : root.sourceInputMap = entryInputMap source.arity

/-- Executable producer check for `FunctionSourceMatch`. -/
def functionSourceMatches (source : IxIR1.FnDef) (generated : Function)
    (root : CodeTrace) : Bool :=
  sourceCodeEq root.sourceCode source.body &&
    (generated.signature.params.size == source.arity) &&
    (generated.signature.result == source.result) &&
    (generated.signature.papSafe == source.papSafe) &&
    (root.sourceBlock == 0) &&
    (root.entryPc == 0) &&
    (root.entryValueCount == source.arity) &&
    (root.sourceInputMap == entryInputMap source.arity)

/-- Turn the executable source-identity check into the proof-facing record. -/
theorem functionSourceMatch_of_match {source : IxIR1.FnDef}
    {generated : Function} {root : CodeTrace}
    (matched : functionSourceMatches source generated root = true) :
    FunctionSourceMatch source generated root := by
  simp only [functionSourceMatches, Bool.and_eq_true] at matched
  rcases matched with ⟨⟨⟨⟨⟨⟨⟨code, arity⟩, result⟩, papSafe⟩,
    entryBlock⟩, entryPc⟩, entryValueCount⟩, entryInput⟩
  exact
    { code := (sourceCodeEq_eq_true_iff _ _).mp code
      arity := beq_iff_eq.mp arity
      result := beq_iff_eq.mp result
      papSafe := beq_iff_eq.mp papSafe
      entryBlock := beq_iff_eq.mp entryBlock
      entryPc := beq_iff_eq.mp entryPc
      entryValueCount := beq_iff_eq.mp entryValueCount
      entryInput := beq_iff_eq.mp entryInput }

/-- One source function and the exact recursive compiler derivation that
produced its target function. -/
structure FunctionTrace where
  owner : Validate.Owner
  source : IxIR1.FnDef
  generated : Function
  root : CodeTrace
  /-- The recursive compiler run begins at this owner's empty branch path and
  zero source offset. -/
  rootSource : root.source = ({ owner := owner } : SourceSite)
  /-- The recursive trace reconstructs the literal source body, and the
  generated signature preserves every non-ownership source signature fact. -/
  sourceOrder : FunctionSourceMatch source generated root
  /-- Every instruction node names the exact instruction retained at its
  final generated block coordinate. -/
  instructionOrder : root.instructionsMatch = true
  /-- Every instruction continuation keeps or forgets source slots without
  retargeting them. -/
  inputMapOrder : root.inputMapsMatch = true
  /-- Every recursive compiler node at target PC zero has the value-register
  count declared by its completed head block's parameter ABI. -/
  entryValueCountOrder : root.entryValueCountsMatch = true
  /-- Every retained source operand translates to the target operand emitted
  at that node, and every terminal node retains its exact terminator. -/
  syntaxOrder : root.syntaxMatches = true
  /-- Every switch target is associated in order with exactly one generated
  edge and recursive child; constructor children additionally certify their
  field-fetch prologue and Nat children their implicit-prefix convention. -/
  switchBranchOrder : root.switchBranchesMatch = true
  /-- Every retained terminal block is exactly the corresponding generated
  block, in canonical block-id order.  The producer checks this internal
  invariant once after finishing the mutable block array. -/
  blockOrder : root.blocks =
    generated.blocks.toList.zipIdx.map fun pair => (pair.2, pair.1)

/-- External identity of a retained function trace at an artifact boundary. -/
structure FunctionTraceMatch (trace : FunctionTrace) (owner : Validate.Owner)
    (source : IxIR1.FnDef) (generated : Function) : Prop where
  owner : trace.owner = owner
  source : trace.source = source
  generated : trace.generated = generated

/-- Executable check tying a function trace to an external source/target
pair. The trace's internal source/signature/code certificate remains separate. -/
def functionTraceMatches (trace : FunctionTrace) (owner : Validate.Owner)
    (source : IxIR1.FnDef) (generated : Function) : Bool :=
  (trace.owner == owner) && functionSourceEq trace.source source &&
    (trace.generated == generated)

/-- Reflect the executable external trace-identity check. -/
theorem functionTraceMatch_of_match {trace : FunctionTrace}
    {owner : Validate.Owner} {source : IxIR1.FnDef} {generated : Function}
    (matched : functionTraceMatches trace owner source generated = true) :
    FunctionTraceMatch trace owner source generated := by
  simp only [functionTraceMatches, Bool.and_eq_true] at matched
  exact
    { owner := beq_iff_eq.mp matched.1.1
      source := (functionSourceEq_eq_true_iff _ _).mp matched.1.2
      generated := beq_iff_eq.mp matched.2 }

namespace FunctionTrace

/-- The recursive derivation is rooted at the literal retained source body. -/
theorem rootSourceCode (trace : FunctionTrace) :
    trace.root.sourceCode = trace.source.body :=
  trace.sourceOrder.code

/-- Generated parameter ownership may be richer, but arity is unchanged. -/
theorem sourceArity (trace : FunctionTrace) :
    trace.generated.signature.params.size = trace.source.arity :=
  trace.sourceOrder.arity

/-- Lowering preserves the declared result world. -/
theorem sourceResult (trace : FunctionTrace) :
    trace.generated.signature.result = trace.source.result :=
  trace.sourceOrder.result

/-- Lowering preserves the source PAP-entry policy. -/
theorem sourcePapSafe (trace : FunctionTrace) :
    trace.generated.signature.papSafe = trace.source.papSafe :=
  trace.sourceOrder.papSafe

/-- Every retained compiler derivation starts at CFG block zero. -/
theorem entryBlock (trace : FunctionTrace) :
    trace.root.sourceBlock = 0 :=
  trace.sourceOrder.entryBlock

/-- Every retained compiler derivation starts before its first instruction. -/
theorem entryPc (trace : FunctionTrace) :
    trace.root.entryPc = 0 :=
  trace.sourceOrder.entryPc

/-- Entry value-register count is exactly the source arity. -/
theorem entryValueCount (trace : FunctionTrace) :
    trace.root.entryValueCount = trace.source.arity :=
  trace.sourceOrder.entryValueCount

/-- Every retained compiler derivation starts with the canonical reversed
source-parameter map. -/
theorem entryInput (trace : FunctionTrace) :
    trace.root.sourceInputMap = entryInputMap trace.source.arity :=
  trace.sourceOrder.entryInput

/-- The completed root block is the function entry block. -/
theorem rootHeadBlock (trace : FunctionTrace) :
    trace.root.headBlock.1 = 0 :=
  (CodeTrace.headBlock_eq_sourceBlock_of_match trace.instructionOrder).trans
    trace.entryBlock

/-- Indexing the derivation's canonical block list yields exactly the block
at that identifier in the generated function.  This is the direct bridge
from recursive trace induction to evaluator block lookup. -/
theorem blockAt (trace : FunctionTrace) (id : BlockId) :
    trace.root.blocks[id]? =
      (trace.generated.blocks[id]?).map fun block => (id, block) := by
  rw [trace.blockOrder]
  simp [Function.comp_def]

/-- Any block reached through recursive trace traversal is the actual block
installed at its retained identifier.  This membership-oriented form is what
the semantic induction uses for switch children, whose block-list ordinal is
not carried separately by the induction hypothesis. -/
theorem blockAt_of_mem (trace : FunctionTrace) {id : BlockId} {block : Block}
    (member : (id, block) ∈ trace.root.blocks) :
    trace.generated.blocks[id]? = some block := by
  rw [trace.blockOrder] at member
  simp only [List.mem_map] at member
  obtain ⟨⟨candidate, index⟩, zipped, equal⟩ := member
  have indexEq : index = id := congrArg Prod.fst equal
  have blockEq : candidate = block := congrArg Prod.snd equal
  subst index
  subst candidate
  simpa using (List.mk_mem_zipIdx_iff_getElem?.mp zipped)

/-- The head block exposed by the recursive derivation is executable directly
from the generated function, without a caller-supplied block-lookup premise. -/
theorem headBlockAt (trace : FunctionTrace) :
    trace.generated.blocks[trace.root.headBlock.1]? =
      some trace.root.headBlock.2 :=
  trace.blockAt_of_mem trace.root.headBlock_mem_blocks

/-- Every successfully retained function has its certified entry/head block. -/
theorem generatedNonempty (trace : FunctionTrace) :
    trace.generated.blocks.isEmpty = false := by
  have found := trace.headBlockAt
  apply Array.isEmpty_eq_false_iff.mpr
  intro empty
  rw [empty] at found
  simp at found

/-- Every recursive continuation or switch child names its exact executable
head block in the generated function.  This removes block lookup as a premise
from induction hypotheses over `CodeTrace.Descendant`. -/
theorem descendantHeadBlockAt (trace : FunctionTrace) {child : CodeTrace}
    (descendant : trace.root.Descendant child) :
    trace.generated.blocks[child.headBlock.1]? = some child.headBlock.2 :=
  trace.blockAt_of_mem
    (descendant.blocks_subset child.headBlock_mem_blocks)

/-- Every recursive continuation/switch child inherits the producer's exact
instruction-coordinate certificate. -/
theorem descendantInstructionsMatch (trace : FunctionTrace)
    {child : CodeTrace} (descendant : trace.root.Descendant child) :
    child.instructionsMatch = true :=
  descendant.instructionsMatch trace.instructionOrder

/-- Every recursive continuation/switch child inherits proof-map
progression coherence. -/
theorem descendantInputMapsMatch (trace : FunctionTrace)
    {child : CodeTrace} (descendant : trace.root.Descendant child) :
    child.inputMapsMatch = true :=
  descendant.inputMapsMatch trace.inputMapOrder

/-- Every recursive continuation or switch child beginning at target PC zero
has exactly the target values declared by its head block's parameter ABI. -/
theorem descendantEntryValueCount (trace : FunctionTrace)
    {child : CodeTrace} (descendant : trace.root.Descendant child)
    (pc : child.entryPc = 0) :
    child.entryValueCount = child.headBlock.2.valueParams.size :=
  CodeTrace.entryValueCount_eq_headParams_of_match
    (descendant.entryValueCountsMatch trace.entryValueCountOrder) pc

/-- Every recursive continuation/switch child inherits exact source/target
operand and terminator syntax. -/
theorem descendantSyntaxMatches (trace : FunctionTrace)
    {child : CodeTrace} (descendant : trace.root.Descendant child) :
    child.syntaxMatches = true :=
  descendant.syntaxMatches trace.syntaxOrder

/-- Every recursive continuation/switch child inherits exact branch-edge,
child-body, successor-map, and constructor-prologue coherence. -/
theorem descendantSwitchBranchesMatch (trace : FunctionTrace)
    {child : CodeTrace} (descendant : trace.root.Descendant child) :
    child.switchBranchesMatch = true :=
  descendant.switchBranchesMatch trace.switchBranchOrder

/-- A recursive instruction node exposes its checked proof-facing operation
syntax directly from trace membership. -/
theorem descendantOperationSyntax (trace : FunctionTrace)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {operation : IxIR1.Op} {index : Nat} {instruction : Instr}
    {next : CodeTrace}
    (descendant : trace.root.Descendant
      (.letOp source block input nextInput entryValueCount operation index
        instruction next)) :
    OperationSyntax input operation instruction :=
  CodeTrace.letOpOperationSyntax_of_match
    (trace.descendantSyntaxMatches descendant)

/-- A recursive instruction node carries all exact continuation metadata and
names an instruction in the generated function's actual block array. -/
theorem descendantLetOpMatch (trace : FunctionTrace)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {operation : IxIR1.Op}
    {index : Nat} {instruction : Instr} {next : CodeTrace}
    (descendant : trace.root.Descendant
      (.letOp source block input nextInput entryValueCount operation index
        instruction next)) :
    CodeTrace.LetOpMatch source block input nextInput entryValueCount operation
        index instruction next ∧
      trace.generated.blocks[block]? = some next.headBlock.2 := by
  have matched := trace.descendantInstructionsMatch descendant
  have localMatch := CodeTrace.letOpMatch_of_match matched
  refine ⟨localMatch, ?_⟩
  have blockAt := trace.descendantHeadBlockAt descendant
  simpa [CodeTrace.headBlock, localMatch.headBlock] using blockAt

end FunctionTrace

structure Trace where
  positions : List PositionTrace := []
  edges : List EdgeTrace := []
  functions : List FunctionTrace := []

/-! ## Producer-retained source capabilities -/

/-- Live/dead and representation agreement between one producer capability
and the corresponding partial source-slot map entry.  Scalars may retain any
scalar-compatible atom; owners and borrows must name concrete SSA registers;
a consumed binding must be absent. -/
def BindingCap.matchesInput : BindingCap → Option Atom → Bool
  | .dead, none => true
  | .dead, some _ => false
  | .scalar, some _ => true
  | .owned _, some (.reg _) | .borrowed _ _, some (.reg _) => true
  | .owned _, _ | .borrowed _ _, _ | .scalar, none => false

/-- Exact agreement between a producer-side source capability and the
capability declared for a target block parameter.  Dead bindings have no
target-parameter counterpart; their source input-map entry is absent. -/
def BindingCap.matchesParameter : BindingCap → ValueCap → Bool
  | .scalar, .scalar => true
  | .owned sourceWorld, .owned targetWorld => sourceWorld == targetWorld
  | .borrowed sourceWorld sourceLender,
      .borrowed targetWorld targetLender =>
      sourceWorld == targetWorld && sourceLender == targetLender
  | _, _ => false

/-- Every live source slot that still names an inherited block parameter
retains exactly that parameter's declared capability.  Registers appended by
instructions are intentionally outside this check; their capability flow is
audited by the operation-specific transition predicates below. -/
def PositionTrace.parameterCapabilitiesMatch (position : PositionTrace)
    (input : Array (Option Atom)) (parameters : Array ValueCap) : Bool :=
  (List.range input.size).all fun sourceIndex =>
    match input[sourceIndex]? with
    | some (some (.reg targetIndex)) =>
        match parameters[targetIndex]? with
        | none => true
        | some parameter =>
            match position.sourceCapabilities[sourceIndex]? with
            | some capability => capability.matchesParameter parameter
            | none => false
    | _ => true

/-- Reflection of parameter-capability coherence without specializing the
parameter kind.  In particular, an inherited target parameter can never be
backed by a dead producer binding. -/
theorem PositionTrace.capability_of_parameterCapabilitiesMatch
    {position : PositionTrace} {input : Array (Option Atom)}
    {parameters : Array ValueCap}
    (matched : position.parameterCapabilitiesMatch input parameters = true)
    {sourceIndex targetIndex : Nat} {parameter : ValueCap}
    (inputAt : input[sourceIndex]? = some (some (.reg targetIndex)))
    (parameterAt : parameters[targetIndex]? = some parameter) :
    ∃ capability,
      position.sourceCapabilities[sourceIndex]? = some capability ∧
        capability.matchesParameter parameter = true := by
  have inputBound : sourceIndex < input.size :=
    (Array.getElem?_eq_some_iff.mp inputAt).1
  have point := List.all_eq_true.mp matched sourceIndex
    (List.mem_range.mpr inputBound)
  simp only [inputAt] at point
  rw [parameterAt] at point
  cases capabilityAt : position.sourceCapabilities[sourceIndex]? with
  | none => simp [capabilityAt] at point
  | some capability =>
      exact ⟨capability, rfl, by
        simpa [capabilityAt] using point⟩

/-- Reflection of parameter-capability coherence for an owned parameter.
This is the ownership bridge used by semantic clients: a source slot mapped
to an owned target parameter is itself the exact producer owner. -/
theorem PositionTrace.owned_of_parameterCapabilitiesMatch
    {position : PositionTrace} {input : Array (Option Atom)}
    {parameters : Array ValueCap}
    (matched : position.parameterCapabilitiesMatch input parameters = true)
    {sourceIndex targetIndex : Nat} {world : Owned}
    (inputAt : input[sourceIndex]? = some (some (.reg targetIndex)))
    (parameterAt : parameters[targetIndex]? = some (.owned world)) :
    position.sourceCapabilities[sourceIndex]? = some (.owned world) := by
  have inputBound : sourceIndex < input.size :=
    (Array.getElem?_eq_some_iff.mp inputAt).1
  have point := List.all_eq_true.mp matched sourceIndex
    (List.mem_range.mpr inputBound)
  simp only [inputAt] at point
  rw [parameterAt] at point
  cases capabilityAt : position.sourceCapabilities[sourceIndex]? with
  | none => simp [capabilityAt] at point
  | some capability =>
      cases capability with
      | scalar => simp [capabilityAt, BindingCap.matchesParameter] at point
      | owned actualWorld =>
          have worldEq : actualWorld = world := by
            exact beq_iff_eq.mp (by
              simpa [capabilityAt, BindingCap.matchesParameter] using point)
          subst actualWorld
          rfl
      | borrowed actualWorld lender =>
          simp [capabilityAt, BindingCap.matchesParameter] at point
      | dead => simp [capabilityAt, BindingCap.matchesParameter] at point

/-- Whether a source capability may cross an owned boundary in `expected`.
Scalars are accepted in either world; concrete owners must match exactly;
borrows and dead bindings cannot be consumed. -/
def BindingCap.canConsume (expected : Owned) : BindingCap → Bool
  | .scalar => true
  | .owned actual => actual == expected
  | .borrowed .. | .dead => false

/-- Capability of a source operand at one retained position. -/
def sourceCapability? (capabilities : Array BindingCap) :
    IxIR1.Atom → Option BindingCap
  | .lit _ | .erased => some .scalar
  | .var index => capabilities[index]?

/-- Retire a borrow whose dynamic lifetime is rooted at a consumed SSA owner.
Other capabilities, including caller-rooted borrows, are unchanged. -/
def BindingCap.retireLender (lender : ValueId) : BindingCap → BindingCap
  | .borrowed world (.value actual) =>
      if actual == lender then .dead else .borrowed world (.value actual)
  | capability => capability

/-- Retire every source borrow rooted at one consumed target register. -/
def retireLenderCapabilities (capabilities : Array BindingCap)
    (lender : ValueId) : Array BindingCap :=
  capabilities.map (BindingCap.retireLender lender)

/-- Consume one source owner and retire all of its target-register loans.  The
retained source input map supplies the exact SSA lender identity. -/
def retireOwnerCapabilities? (capabilities : Array BindingCap)
    (input : Array (Option Atom)) (index : Nat) :
    Option (Array BindingCap) :=
  match input[index]? with
  | some (some (.reg lender)) =>
      some (retireLenderCapabilities
        (capabilities.setIfInBounds index .dead) lender)
  | _ => none

/-- Retiring one owner and its loans preserves source-slot cardinality. -/
theorem retireOwnerCapabilities?_size
    {capabilities remaining : Array BindingCap}
    {input : Array (Option Atom)} {index : Nat}
    (retired : retireOwnerCapabilities? capabilities input index =
      some remaining) :
    remaining.size = capabilities.size := by
  unfold retireOwnerCapabilities? at retired
  split at retired <;> try contradiction
  next lender _ =>
    injection retired with remainingEq
    subst remaining
    simp [retireLenderCapabilities]

/-- Capability vector produced by the lowerer's `pure`/`move` rule. Scalars
and borrows are copied; an owned source slot is consumed before the same owner
is rebound at the new de Bruijn head, and loans rooted at the old SSA owner
are retired. -/
def moveCapabilities? (capabilities : Array BindingCap)
    (input : Array (Option Atom)) (source : IxIR1.Atom) :
    Option (Array BindingCap) :=
  match sourceCapability? capabilities source with
  | none | some .dead => none
  | some capability =>
      let remaining? :=
        match source, capability with
        | .var index, .owned _ =>
            retireOwnerCapabilities? capabilities input index
        | _, _ => some capabilities
      remaining?.map fun remaining => #[capability] ++ remaining

/-- One retained before/after position pair agrees with the exact
`pure`/`move` capability effect. -/
def PositionTrace.moveMatches (before after : PositionTrace)
    (input : Array (Option Atom)) (source : IxIR1.Atom) : Bool :=
  match moveCapabilities? before.sourceCapabilities input source with
  | some expected => expected == after.sourceCapabilities
  | none => false

/-- A flat producer position names this exact recursive trace coordinate and
its capability vector has the same live/dead shape as the proof input map. -/
def PositionTrace.coordinateMatches (position : PositionTrace)
    (source : SourceSite) (block : BlockId) (target : TargetPosition)
    (input : Array (Option Atom)) : Bool :=
  position.source == source && position.block == block &&
    position.target == target &&
    position.sourceCapabilities.size == input.size &&
    (List.range input.size).all fun index =>
      match position.sourceCapabilities[index]?, input[index]? with
      | some capability, some slot => capability.matchesInput slot
      | _, _ => false

/-- A matching flat coordinate carries exactly one capability for every
source slot in the recursive trace input map. -/
theorem PositionTrace.sourceCapabilities_size_of_coordinateMatch
    {position : PositionTrace} {source : SourceSite} {block : BlockId}
    {target : TargetPosition} {input : Array (Option Atom)}
    (matched : position.coordinateMatches source block target input = true) :
    position.sourceCapabilities.size = input.size := by
  unfold PositionTrace.coordinateMatches at matched
  simp only [Bool.and_eq_true] at matched
  exact beq_iff_eq.mp matched.1.2

/-- An owned capability at a matching producer position names an exact SSA
register in the recursive source input map. -/
theorem PositionTrace.inputReg_of_owned_coordinateMatch
    {position : PositionTrace} {source : SourceSite} {block : BlockId}
    {target : TargetPosition} {input : Array (Option Atom)}
    (matched : position.coordinateMatches source block target input = true)
    {index : Nat} {world : Owned}
    (capabilityAt : position.sourceCapabilities[index]? =
      some (.owned world)) :
    ∃ id, input[index]? = some (some (.reg id)) := by
  have sizeEq := position.sourceCapabilities_size_of_coordinateMatch matched
  have bound : index < input.size := by
    rw [← sizeEq]
    exact (Array.getElem?_eq_some_iff.mp capabilityAt).1
  unfold PositionTrace.coordinateMatches at matched
  simp only [Bool.and_eq_true] at matched
  have point := List.all_eq_true.mp matched.2 index
    (List.mem_range.mpr bound)
  rw [capabilityAt] at point
  cases inputAt : input[index]? with
  | none => simp [inputAt] at point
  | some slot =>
      cases slot with
      | none => simp [inputAt, BindingCap.matchesInput] at point
      | some atom =>
          cases atom with
          | reg id => exact ⟨id, rfl⟩
          | lit literal | erased =>
              simp [inputAt, BindingCap.matchesInput] at point

/-- Whether the flat producer index contains the exact coordinate and
live/dead capability shape for one recursive code node. -/
def CodeTrace.positionMatches (positions : List PositionTrace)
    (trace : CodeTrace) : Bool :=
  positions.any fun position =>
    position.coordinateMatches trace.source trace.sourceBlock
      trace.targetPosition trace.sourceInputMap

mutual

/-- Every recursive code node has a matching producer position.  This is the
whole-trace coordinate audit used to select dynamic ownership invariants on
both sides of an instruction or branch transition. -/
def CodeTrace.positionsMatch
    (positions : List PositionTrace) : CodeTrace → Bool
  | trace@(.ret ..) | trace@(.tailCall ..) | trace@(.tailCallSelf ..) =>
      trace.positionMatches positions
  | trace@(.letOp _ _ _ _ _ _ _ _ next) =>
      trace.positionMatches positions && next.positionsMatch positions
  | trace@(.switchValue _ _ _ _ _ _ _ _ _ _ children) =>
      trace.positionMatches positions &&
        codeTraceListPositionsMatch positions children

private def codeTraceListPositionsMatch
    (positions : List PositionTrace) : List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.positionsMatch positions &&
        codeTraceListPositionsMatch positions rest

end

/-- Project the current node's flat-position audit from recursive
whole-subtree coherence. -/
theorem CodeTrace.positionMatches_of_positionsMatch
    (positions : List PositionTrace) {trace : CodeTrace}
    (matched : trace.positionsMatch positions = true) :
    trace.positionMatches positions = true := by
  cases trace <;>
    simp_all [CodeTrace.positionsMatch, Bool.and_eq_true]

/-- Reflect the exact producer position for any recursively audited node. -/
theorem CodeTrace.position_of_positionsMatch
    (positions : List PositionTrace) {trace : CodeTrace}
    (matched : trace.positionsMatch positions = true) :
    ∃ position, position ∈ positions ∧
      position.coordinateMatches trace.source trace.sourceBlock
        trace.targetPosition trace.sourceInputMap = true := by
  exact List.any_eq_true.mp
    (trace.positionMatches_of_positionsMatch positions matched)

private theorem codeTraceListPositionsMatch_of_mem
    (positions : List PositionTrace)
    {traces : List CodeTrace} {child : CodeTrace}
    (matched : codeTraceListPositionsMatch positions traces = true)
    (member : child ∈ traces) :
    child.positionsMatch positions = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListPositionsMatch, Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Position coherence is inherited by every immediate recursive compiler
call. -/
theorem CodeTrace.positionsMatch_of_child
    (positions : List PositionTrace) {parent child : CodeTrace}
    (matched : parent.positionsMatch positions = true)
    (member : child ∈ parent.children) :
    child.positionsMatch positions = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      simp [CodeTrace.children] at member
      subst child
      simp only [CodeTrace.positionsMatch, Bool.and_eq_true] at matched
      exact matched.2
  | switchValue source block input entryValueCount sourceScrutinee peel
      alternatives targetScrutinee generated outgoing children =>
      have childrenMatched :
          codeTraceListPositionsMatch positions children = true := by
        simp only [CodeTrace.positionsMatch, Bool.and_eq_true] at matched
        exact matched.2
      exact codeTraceListPositionsMatch_of_mem positions childrenMatched member

/-- Every recursive descendant inherits whole-position coherence. -/
theorem CodeTrace.Descendant.positionsMatch
    (positions : List PositionTrace) {root child : CodeTrace}
    (descendant : Descendant root child)
    (matched : root.positionsMatch positions = true) :
    child.positionsMatch positions = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.positionsMatch_of_child positions ih childMem

/-- Whole-program producer-position coordinate audit. -/
def Trace.positionsMatch (trace : Trace) : Bool :=
  trace.functions.all fun functionTrace =>
    functionTrace.root.positionsMatch trace.positions

/-- Project whole-program position coherence to one retained function. -/
theorem Trace.functionPositionsMatch {trace : Trace}
    (matched : trace.positionsMatch = true)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ trace.functions) :
    functionTrace.root.positionsMatch trace.positions = true :=
  List.all_eq_true.mp matched functionTrace member

/-! ### Producer capabilities at inherited block parameters -/

/-- Every flat producer position naming this recursive node agrees with the
capabilities declared by the node's inherited block parameters. -/
def CodeTrace.positionParameterCapabilitiesMatch
    (positions : List PositionTrace) (trace : CodeTrace) : Bool :=
  positions.all fun position =>
    if position.coordinateMatches trace.source trace.sourceBlock
        trace.targetPosition trace.sourceInputMap then
      position.parameterCapabilitiesMatch trace.sourceInputMap
        trace.headBlock.2.valueParams
    else
      true

mutual

/-- Recursive audit connecting every source capability vector to the target
block parameters still named by its input map. -/
def CodeTrace.parameterCapabilitiesMatch
    (positions : List PositionTrace) : CodeTrace → Bool
  | trace@(.ret ..) | trace@(.tailCall ..) | trace@(.tailCallSelf ..) =>
      trace.positionParameterCapabilitiesMatch positions
  | trace@(.letOp _ _ _ _ _ _ _ _ next) =>
      trace.positionParameterCapabilitiesMatch positions &&
        next.parameterCapabilitiesMatch positions
  | trace@(.switchValue _ _ _ _ _ _ _ _ _ _ children) =>
      trace.positionParameterCapabilitiesMatch positions &&
        codeTraceListParameterCapabilitiesMatch positions children

private def codeTraceListParameterCapabilitiesMatch
    (positions : List PositionTrace) : List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.parameterCapabilitiesMatch positions &&
        codeTraceListParameterCapabilitiesMatch positions rest

end

/-- Project the current node's parameter-capability audit from recursive
whole-subtree coherence. -/
theorem CodeTrace.positionParameterCapabilitiesMatch_of_match
    (positions : List PositionTrace) {trace : CodeTrace}
    (matched : trace.parameterCapabilitiesMatch positions = true) :
    trace.positionParameterCapabilitiesMatch positions = true := by
  cases trace <;>
    simp_all [CodeTrace.parameterCapabilitiesMatch, Bool.and_eq_true]

/-- Reflect parameter-capability agreement for any matching flat position at
the current recursive trace node. -/
theorem CodeTrace.positionParameterCapabilities_of_match
    (positions : List PositionTrace) {trace : CodeTrace}
    (matched : trace.parameterCapabilitiesMatch positions = true)
    {position : PositionTrace} (member : position ∈ positions)
    (coordinate : position.coordinateMatches trace.source trace.sourceBlock
      trace.targetPosition trace.sourceInputMap = true) :
    position.parameterCapabilitiesMatch trace.sourceInputMap
      trace.headBlock.2.valueParams = true := by
  have localMatch := trace.positionParameterCapabilitiesMatch_of_match positions
    matched
  have point := List.all_eq_true.mp localMatch position member
  rw [if_pos coordinate] at point
  exact point

private theorem codeTraceListParameterCapabilitiesMatch_of_mem
    (positions : List PositionTrace)
    {traces : List CodeTrace} {child : CodeTrace}
    (matched : codeTraceListParameterCapabilitiesMatch positions traces = true)
    (member : child ∈ traces) :
    child.parameterCapabilitiesMatch positions = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListParameterCapabilitiesMatch,
        Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Parameter-capability coherence is inherited by every immediate recursive
compiler call. -/
theorem CodeTrace.parameterCapabilitiesMatch_of_child
    (positions : List PositionTrace) {parent child : CodeTrace}
    (matched : parent.parameterCapabilitiesMatch positions = true)
    (member : child ∈ parent.children) :
    child.parameterCapabilitiesMatch positions = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      simp [CodeTrace.children] at member
      subst child
      simp only [CodeTrace.parameterCapabilitiesMatch,
        Bool.and_eq_true] at matched
      exact matched.2
  | switchValue source block input entryValueCount sourceScrutinee peel
      alternatives targetScrutinee generated outgoing children =>
      have childrenMatched :
          codeTraceListParameterCapabilitiesMatch positions children = true :=
        by
          simp only [CodeTrace.parameterCapabilitiesMatch,
            Bool.and_eq_true] at matched
          exact matched.2
      exact codeTraceListParameterCapabilitiesMatch_of_mem positions
        childrenMatched member

/-- Every recursive descendant inherits parameter-capability coherence. -/
theorem CodeTrace.Descendant.parameterCapabilitiesMatch
    (positions : List PositionTrace) {root child : CodeTrace}
    (descendant : Descendant root child)
    (matched : root.parameterCapabilitiesMatch positions = true) :
    child.parameterCapabilitiesMatch positions = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.parameterCapabilitiesMatch_of_child positions ih
        childMem

/-- Whole-program audit of producer capabilities against inherited target
block parameters. -/
def Trace.parameterCapabilitiesMatch (trace : Trace) : Bool :=
  trace.functions.all fun functionTrace =>
    functionTrace.root.parameterCapabilitiesMatch trace.positions

/-- Project the whole-program parameter-capability audit to one retained
function. -/
theorem Trace.functionParameterCapabilitiesMatch {trace : Trace}
    (matched : trace.parameterCapabilitiesMatch = true)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ trace.functions) :
    functionTrace.root.parameterCapabilitiesMatch trace.positions = true :=
  List.all_eq_true.mp matched functionTrace member

/-! ### Producer capability flow for `pure` / `move` -/

/-- Every flat position naming the continuation of this `pure` node is paired
with a current position whose capability vector evolves by `moveCapabilities?`.
The separate whole-position audit guarantees that the continuation set is
nonempty. -/
def CodeTrace.pureTransitionMatches (positions : List PositionTrace)
    (current next : CodeTrace) (source : IxIR1.Atom) : Bool :=
  positions.all fun after =>
    if after.coordinateMatches next.source next.sourceBlock
        next.targetPosition next.sourceInputMap then
          positions.any fun before =>
        before.coordinateMatches current.source current.sourceBlock
            current.targetPosition current.sourceInputMap &&
          before.moveMatches after current.sourceInputMap source
    else
      true

mutual

/-- Recursive audit of every `pure` capability transition in a code tree. -/
def CodeTrace.pureCapabilitiesMatch
    (positions : List PositionTrace) : CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | trace@(.letOp _ _ _ _ _ operation _ _ next) =>
      (match operation with
       | .pure source => trace.pureTransitionMatches positions next source
       | _ => true) &&
        next.pureCapabilitiesMatch positions
  | .switchValue _ _ _ _ _ _ _ _ _ _ children =>
      codeTraceListPureCapabilitiesMatch positions children

private def codeTraceListPureCapabilitiesMatch
    (positions : List PositionTrace) : List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.pureCapabilitiesMatch positions &&
        codeTraceListPureCapabilitiesMatch positions rest

end

/-- Reflect the checked before-position for an arbitrary matching
continuation position of one `pure` node. -/
theorem CodeTrace.pureTransition_of_match
    (positions : List PositionTrace)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {index : Nat} {targetAtom : Atom}
    {next : CodeTrace} {after : PositionTrace}
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      (.pure sourceAtom) index (.move targetAtom) next
        ).pureCapabilitiesMatch positions = true)
    (afterMember : after ∈ positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    ∃ before, before ∈ positions ∧
      before.coordinateMatches source block (.instruction index) input = true ∧
      before.moveMatches after input sourceAtom = true := by
  change (CodeTrace.pureTransitionMatches positions
      (.letOp source block input nextInput entryValueCount
        (.pure sourceAtom) index (.move targetAtom) next)
      next sourceAtom && next.pureCapabilitiesMatch positions) = true at matched
  simp only [Bool.and_eq_true] at matched
  have point := List.all_eq_true.mp matched.1 after afterMember
  rw [if_pos afterCoordinate] at point
  obtain ⟨before, beforeMember, beforeMatch⟩ := List.any_eq_true.mp point
  simp only [Bool.and_eq_true] at beforeMatch
  exact ⟨before, beforeMember, by
    simpa [CodeTrace.source, CodeTrace.sourceBlock, CodeTrace.targetPosition,
      CodeTrace.sourceInputMap] using beforeMatch.1, beforeMatch.2⟩

private theorem codeTraceListPureCapabilitiesMatch_of_mem
    (positions : List PositionTrace)
    {traces : List CodeTrace} {child : CodeTrace}
    (matched : codeTraceListPureCapabilitiesMatch positions traces = true)
    (member : child ∈ traces) :
    child.pureCapabilitiesMatch positions = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListPureCapabilitiesMatch,
        Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- `pure` capability-flow coherence is inherited by immediate recursive
compiler calls. -/
theorem CodeTrace.pureCapabilitiesMatch_of_child
    (positions : List PositionTrace) {parent child : CodeTrace}
    (matched : parent.pureCapabilitiesMatch positions = true)
    (member : child ∈ parent.children) :
    child.pureCapabilitiesMatch positions = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      simp [CodeTrace.children] at member
      subst child
      simp only [CodeTrace.pureCapabilitiesMatch,
        Bool.and_eq_true] at matched
      exact matched.2
  | switchValue source block input entryValueCount sourceScrutinee peel
      alternatives targetScrutinee generated outgoing children =>
      exact codeTraceListPureCapabilitiesMatch_of_mem positions matched member

/-- Every recursive descendant inherits the checked `pure` capability-flow
audit. -/
theorem CodeTrace.Descendant.pureCapabilitiesMatch
    (positions : List PositionTrace) {root child : CodeTrace}
    (descendant : Descendant root child)
    (matched : root.pureCapabilitiesMatch positions = true) :
    child.pureCapabilitiesMatch positions = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.pureCapabilitiesMatch_of_child positions ih childMem

/-- Whole-program `pure` capability-flow audit. -/
def Trace.pureCapabilitiesMatch (trace : Trace) : Bool :=
  trace.functions.all fun functionTrace =>
    functionTrace.root.pureCapabilitiesMatch trace.positions

/-- Project whole-program `pure` capability flow to one retained function. -/
theorem Trace.functionPureCapabilitiesMatch {trace : Trace}
    (matched : trace.pureCapabilitiesMatch = true)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ trace.functions) :
    functionTrace.root.pureCapabilitiesMatch trace.positions = true :=
  List.all_eq_true.mp matched functionTrace member

/-! ### Producer capability flow for `dup` / `retainShared` -/

/-- Capability vector produced by the lowerer's shared-retain rule. Scalars
remain scalar; an owned or borrowed shared value produces a new shared owner
without consuming the source slot. -/
def dupCapabilities? (capabilities : Array BindingCap)
    (source : IxIR1.Atom) : Option (Array BindingCap) :=
  match sourceCapability? capabilities source with
  | some .scalar => some (#[.scalar] ++ capabilities)
  | some (.owned .shared) | some (.borrowed .shared _) =>
      some (#[.owned .shared] ++ capabilities)
  | none | some (.owned .unique) | some (.borrowed .unique _) |
      some .dead => none

/-- One retained before/after position pair agrees with the exact
`dup`/`retainShared` capability effect. -/
def PositionTrace.dupMatches (before after : PositionTrace)
    (source : IxIR1.Atom) : Bool :=
  match dupCapabilities? before.sourceCapabilities source with
  | some expected => expected == after.sourceCapabilities
  | none => false

/-- Every flat position naming the continuation of this `dup` node is paired
with a current position whose capability vector evolves by `dupCapabilities?`.
-/
def CodeTrace.dupTransitionMatches (positions : List PositionTrace)
    (current next : CodeTrace) (source : IxIR1.Atom) : Bool :=
  positions.all fun after =>
    if after.coordinateMatches next.source next.sourceBlock
        next.targetPosition next.sourceInputMap then
      positions.any fun before =>
        before.coordinateMatches current.source current.sourceBlock
            current.targetPosition current.sourceInputMap &&
          before.dupMatches after source
    else
      true

mutual

/-- Recursive audit of every `dup` capability transition in a code tree. -/
def CodeTrace.dupCapabilitiesMatch
    (positions : List PositionTrace) : CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | trace@(.letOp _ _ _ _ _ operation _ _ next) =>
      (match operation with
       | .dup source => trace.dupTransitionMatches positions next source
       | _ => true) &&
        next.dupCapabilitiesMatch positions
  | .switchValue _ _ _ _ _ _ _ _ _ _ children =>
      codeTraceListDupCapabilitiesMatch positions children

private def codeTraceListDupCapabilitiesMatch
    (positions : List PositionTrace) : List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.dupCapabilitiesMatch positions &&
        codeTraceListDupCapabilitiesMatch positions rest

end

/-- Reflect the checked before-position for an arbitrary matching
continuation position of one `dup` node. -/
theorem CodeTrace.dupTransition_of_match
    (positions : List PositionTrace)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {index : Nat} {targetAtom : Atom}
    {next : CodeTrace} {after : PositionTrace}
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      (.dup sourceAtom) index (.retainShared targetAtom) next
        ).dupCapabilitiesMatch positions = true)
    (afterMember : after ∈ positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    ∃ before, before ∈ positions ∧
      before.coordinateMatches source block (.instruction index) input = true ∧
      before.dupMatches after sourceAtom = true := by
  change (CodeTrace.dupTransitionMatches positions
      (.letOp source block input nextInput entryValueCount
        (.dup sourceAtom) index (.retainShared targetAtom) next)
      next sourceAtom && next.dupCapabilitiesMatch positions) = true at matched
  simp only [Bool.and_eq_true] at matched
  have point := List.all_eq_true.mp matched.1 after afterMember
  rw [if_pos afterCoordinate] at point
  obtain ⟨before, beforeMember, beforeMatch⟩ := List.any_eq_true.mp point
  simp only [Bool.and_eq_true] at beforeMatch
  exact ⟨before, beforeMember, by
    simpa [CodeTrace.source, CodeTrace.sourceBlock, CodeTrace.targetPosition,
      CodeTrace.sourceInputMap] using beforeMatch.1, beforeMatch.2⟩

private theorem codeTraceListDupCapabilitiesMatch_of_mem
    (positions : List PositionTrace)
    {traces : List CodeTrace} {child : CodeTrace}
    (matched : codeTraceListDupCapabilitiesMatch positions traces = true)
    (member : child ∈ traces) :
    child.dupCapabilitiesMatch positions = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListDupCapabilitiesMatch,
        Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- `dup` capability-flow coherence is inherited by immediate recursive
compiler calls. -/
theorem CodeTrace.dupCapabilitiesMatch_of_child
    (positions : List PositionTrace) {parent child : CodeTrace}
    (matched : parent.dupCapabilitiesMatch positions = true)
    (member : child ∈ parent.children) :
    child.dupCapabilitiesMatch positions = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      simp [CodeTrace.children] at member
      subst child
      simp only [CodeTrace.dupCapabilitiesMatch,
        Bool.and_eq_true] at matched
      exact matched.2
  | switchValue source block input entryValueCount sourceScrutinee peel
      alternatives targetScrutinee generated outgoing children =>
      exact codeTraceListDupCapabilitiesMatch_of_mem positions matched member

/-- Every recursive descendant inherits the checked `dup` capability-flow
audit. -/
theorem CodeTrace.Descendant.dupCapabilitiesMatch
    (positions : List PositionTrace) {root child : CodeTrace}
    (descendant : Descendant root child)
    (matched : root.dupCapabilitiesMatch positions = true) :
    child.dupCapabilitiesMatch positions = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.dupCapabilitiesMatch_of_child positions ih childMem

/-- Whole-program `dup` capability-flow audit. -/
def Trace.dupCapabilitiesMatch (trace : Trace) : Bool :=
  trace.functions.all fun functionTrace =>
    functionTrace.root.dupCapabilitiesMatch trace.positions

/-- Project whole-program `dup` capability flow to one retained function. -/
theorem Trace.functionDupCapabilitiesMatch {trace : Trace}
    (matched : trace.dupCapabilitiesMatch = true)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ trace.functions) :
    functionTrace.root.dupCapabilitiesMatch trace.positions = true :=
  List.all_eq_true.mp matched functionTrace member

/-! ### Producer capability flow for `fetch` -/

/-- Capability vector accepted by the ownership simulation for the lowerer's
non-consuming projection rule.  The baseline schema is uniform in the
constructor world, so the projected value is borrowed in that same world.
An owned constructor lends through its translated register; an existing
borrow preserves its original lender. -/
def fetchCapabilities? (capabilities : Array BindingCap)
    (source : IxIR1.Atom) (target : Atom) : Option (Array BindingCap) :=
  match sourceCapability? capabilities source with
  | some (.owned world) =>
      match target with
      | .reg id =>
          some (#[.borrowed world (.value id)] ++ capabilities)
      | .lit _ | .erased => none
  | some (.borrowed world lender) =>
      some (#[.borrowed world lender] ++ capabilities)
  | none | some .scalar | some .dead => none

/-- One retained before/after position pair agrees with the exact
baseline-compatible `fetch` capability effect. -/
def PositionTrace.fetchMatches (before after : PositionTrace)
    (source : IxIR1.Atom) (target : Atom) : Bool :=
  match fetchCapabilities? before.sourceCapabilities source target with
  | some expected => expected == after.sourceCapabilities
  | none => false

/-- Every flat position naming the continuation of this `fetch` node is
paired with a current position whose capability vector evolves by
`fetchCapabilities?`. -/
def CodeTrace.fetchTransitionMatches (positions : List PositionTrace)
    (current next : CodeTrace) (source : IxIR1.Atom) (target : Atom) : Bool :=
  positions.all fun after =>
    if after.coordinateMatches next.source next.sourceBlock
        next.targetPosition next.sourceInputMap then
      positions.any fun before =>
        before.coordinateMatches current.source current.sourceBlock
            current.targetPosition current.sourceInputMap &&
          before.fetchMatches after source target
    else
      true

mutual

/-- Recursive audit of every `fetch` capability transition in a code tree. -/
def CodeTrace.fetchCapabilitiesMatch
    (positions : List PositionTrace) : CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | trace@(.letOp _ _ _ _ _ operation _ instruction next) =>
      (match operation, instruction with
       | .fetch source _, .fetch target _ _ =>
           trace.fetchTransitionMatches positions next source target
       | .fetch .., _ => false
       | _, _ => true) &&
        next.fetchCapabilitiesMatch positions
  | .switchValue _ _ _ _ _ _ _ _ _ _ children =>
      codeTraceListFetchCapabilitiesMatch positions children

private def codeTraceListFetchCapabilitiesMatch
    (positions : List PositionTrace) : List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.fetchCapabilitiesMatch positions &&
        codeTraceListFetchCapabilitiesMatch positions rest

end

/-- Reflect the checked before-position for an arbitrary matching
continuation position of one `fetch` node. -/
theorem CodeTrace.fetchTransition_of_match
    (positions : List PositionTrace)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {sourceField index : Nat}
    {targetAtom : Atom} {targetCid : CtorId} {targetField : Nat}
    {next : CodeTrace} {after : PositionTrace}
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      (.fetch sourceAtom sourceField) index
        (.fetch targetAtom targetCid targetField) next
        ).fetchCapabilitiesMatch positions = true)
    (afterMember : after ∈ positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    ∃ before, before ∈ positions ∧
      before.coordinateMatches source block (.instruction index) input = true ∧
      before.fetchMatches after sourceAtom targetAtom = true := by
  change (CodeTrace.fetchTransitionMatches positions
      (.letOp source block input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
          (.fetch targetAtom targetCid targetField) next)
      next sourceAtom targetAtom && next.fetchCapabilitiesMatch positions) =
        true at matched
  simp only [Bool.and_eq_true] at matched
  have point := List.all_eq_true.mp matched.1 after afterMember
  rw [if_pos afterCoordinate] at point
  obtain ⟨before, beforeMember, beforeMatch⟩ := List.any_eq_true.mp point
  simp only [Bool.and_eq_true] at beforeMatch
  exact ⟨before, beforeMember, by
    simpa [CodeTrace.source, CodeTrace.sourceBlock, CodeTrace.targetPosition,
      CodeTrace.sourceInputMap] using beforeMatch.1, beforeMatch.2⟩

private theorem codeTraceListFetchCapabilitiesMatch_of_mem
    (positions : List PositionTrace)
    {traces : List CodeTrace} {child : CodeTrace}
    (matched : codeTraceListFetchCapabilitiesMatch positions traces = true)
    (member : child ∈ traces) :
    child.fetchCapabilitiesMatch positions = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListFetchCapabilitiesMatch,
        Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- `fetch` capability-flow coherence is inherited by immediate recursive
compiler calls. -/
theorem CodeTrace.fetchCapabilitiesMatch_of_child
    (positions : List PositionTrace) {parent child : CodeTrace}
    (matched : parent.fetchCapabilitiesMatch positions = true)
    (member : child ∈ parent.children) :
    child.fetchCapabilitiesMatch positions = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      simp [CodeTrace.children] at member
      subst child
      simp only [CodeTrace.fetchCapabilitiesMatch,
        Bool.and_eq_true] at matched
      exact matched.2
  | switchValue source block input entryValueCount sourceScrutinee peel
      alternatives targetScrutinee generated outgoing children =>
      exact codeTraceListFetchCapabilitiesMatch_of_mem positions matched member

/-- Every recursive descendant inherits the checked `fetch` capability-flow
audit. -/
theorem CodeTrace.Descendant.fetchCapabilitiesMatch
    (positions : List PositionTrace) {root child : CodeTrace}
    (descendant : Descendant root child)
    (matched : root.fetchCapabilitiesMatch positions = true) :
    child.fetchCapabilitiesMatch positions = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.fetchCapabilitiesMatch_of_child positions ih childMem

/-- Whole-program `fetch` capability-flow audit. -/
def Trace.fetchCapabilitiesMatch (trace : Trace) : Bool :=
  trace.functions.all fun functionTrace =>
    functionTrace.root.fetchCapabilitiesMatch trace.positions

/-- Project whole-program `fetch` capability flow to one retained function. -/
theorem Trace.functionFetchCapabilitiesMatch {trace : Trace}
    (matched : trace.fetchCapabilitiesMatch = true)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ trace.functions) :
    functionTrace.root.fetchCapabilitiesMatch trace.positions = true :=
  List.all_eq_true.mp matched functionTrace member

/-! ### Shared owned-boundary capability consumption -/

/-- Consume one source operand at an owned boundary, mirroring
`consumeExpected`. Scalars are ownership-inert; an exact owner and all loans
rooted at its SSA register are retired; borrows, dead slots, and wrong-world
owners fail closed. -/
def consumeCapability? (capabilities : Array BindingCap)
    (input : Array (Option Atom)) (world : Owned) (source : IxIR1.Atom) :
    Option (Array BindingCap) :=
  match source, sourceCapability? capabilities source with
  | _, some .scalar => some capabilities
  | .var index, some (.owned actual) =>
      if actual == world then
        retireOwnerCapabilities? capabilities input index
      else
        none
  | _, _ => none

/-- Sequential owned-boundary consumption in source argument order. -/
def consumeCapabilitiesList? (capabilities : Array BindingCap)
    (input : Array (Option Atom))
    (world : Owned) : List IxIR1.Atom → Option (Array BindingCap)
  | [] => some capabilities
  | source :: rest => do
      let remaining ← consumeCapability? capabilities input world source
      consumeCapabilitiesList? remaining input world rest

/-- Sequentially consume a heterogeneous owned parameter telescope.  The
two lists must have identical cardinality; each argument is checked and
retired in the world of its corresponding parameter. -/
def consumeCapabilitiesWorlds? (capabilities : Array BindingCap)
    (input : Array (Option Atom)) :
    List Owned → List IxIR1.Atom → Option (Array BindingCap)
  | [], [] => some capabilities
  | world :: worlds, source :: sources => do
      let remaining ← consumeCapability? capabilities input world source
      consumeCapabilitiesWorlds? remaining input worlds sources
  | _, _ => none

/-- A successful heterogeneous consumption has matching parameter and
argument cardinalities. -/
theorem consumeCapabilitiesWorlds?_length
    {capabilities remaining : Array BindingCap}
    {input : Array (Option Atom)} {worlds : List Owned}
    {sources : List IxIR1.Atom}
    (consumed : consumeCapabilitiesWorlds? capabilities input worlds sources =
      some remaining) :
    worlds.length = sources.length := by
  induction worlds generalizing capabilities sources with
  | nil =>
      cases sources with
      | nil => rfl
      | cons source rest => simp [consumeCapabilitiesWorlds?] at consumed
  | cons world worlds ih =>
      cases sources with
      | nil => simp [consumeCapabilitiesWorlds?] at consumed
      | cons source sources =>
          simp only [consumeCapabilitiesWorlds?] at consumed
          cases step : consumeCapability? capabilities input world source with
          | none => simp [step] at consumed
          | some next =>
              simp only [step] at consumed
              simp [ih consumed]

/-! ### Exact capability flow for destructive operations -/

/-- The ownership world and operand consumed by a baseline destruction
operation. Other operations do not participate in this audit. -/
def destructionSpec? : IxIR1.Op → Option (Owned × IxIR1.Atom)
  | .free source => some (.unique, source)
  | .drop source => some (.shared, source)
  | .dropU source => some (.unique, source)
  | _ => none

/-- Exact continuation capability vector after destruction: consume the
selected owner (and retire its rooted loans), then bind the erased scalar
result at the de Bruijn head. -/
def destructionCapabilities? (capabilities : Array BindingCap)
    (input : Array (Option Atom)) (world : Owned)
    (source : IxIR1.Atom) : Option (Array BindingCap) := do
  let remaining ← consumeCapability? capabilities input world source
  return #[.scalar] ++ remaining

/-- One retained destruction before/after pair has the exact
consume-and-bind-scalar effect. -/
def PositionTrace.destructionResultMatches (before after : PositionTrace)
    (input : Array (Option Atom)) (world : Owned)
    (source : IxIR1.Atom) : Bool :=
  match destructionCapabilities? before.sourceCapabilities input world source with
  | some expected => expected == after.sourceCapabilities
  | none => false

/-- Every continuation position of one destruction node has an exact
capability predecessor. -/
def CodeTrace.destructionTransitionMatches (positions : List PositionTrace)
    (current next : CodeTrace) (world : Owned)
    (source : IxIR1.Atom) : Bool :=
  positions.all fun after =>
    if after.coordinateMatches next.source next.sourceBlock
        next.targetPosition next.sourceInputMap then
      positions.any fun before =>
        before.coordinateMatches current.source current.sourceBlock
            current.targetPosition current.sourceInputMap &&
          before.destructionResultMatches after current.sourceInputMap world
            source
    else
      true

mutual

/-- Recursive exact capability audit for shallow free and shared/unique deep
destruction. -/
def CodeTrace.destructionCapabilitiesMatch
    (positions : List PositionTrace) : CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | trace@(.letOp _ _ _ _ _ operation _ _ next) =>
      (match destructionSpec? operation with
       | some (world, source) =>
           trace.destructionTransitionMatches positions next world source
       | none => true) &&
        next.destructionCapabilitiesMatch positions
  | .switchValue _ _ _ _ _ _ _ _ _ _ children =>
      codeTraceListDestructionCapabilitiesMatch positions children

private def codeTraceListDestructionCapabilitiesMatch
    (positions : List PositionTrace) : List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.destructionCapabilitiesMatch positions &&
        codeTraceListDestructionCapabilitiesMatch positions rest

end

/-- Reflect the exact capability predecessor of any matching continuation
position at an audited destruction node. -/
theorem CodeTrace.destructionTransition_of_match
    (positions : List PositionTrace)
    {sourceSite : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {operation : IxIR1.Op} {world : Owned} {sourceAtom : IxIR1.Atom}
    {index : Nat} {instruction : Instr} {next : CodeTrace}
    {after : PositionTrace}
    (operationMatch : destructionSpec? operation = some (world, sourceAtom))
    (matched : (CodeTrace.letOp sourceSite block input nextInput
      entryValueCount operation index instruction next
        ).destructionCapabilitiesMatch positions = true)
    (afterMember : after ∈ positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    ∃ before, before ∈ positions ∧
      before.coordinateMatches sourceSite block (.instruction index) input =
        true ∧
      before.destructionResultMatches after input world sourceAtom = true := by
  change (((match destructionSpec? operation with
      | some (world, source) =>
          (CodeTrace.letOp sourceSite block input nextInput entryValueCount
            operation index instruction next).destructionTransitionMatches
              positions next world source
      | none => true) &&
    next.destructionCapabilitiesMatch positions) = true) at matched
  rw [operationMatch] at matched
  simp only [Bool.and_eq_true] at matched
  have point := List.all_eq_true.mp matched.1 after afterMember
  rw [if_pos afterCoordinate] at point
  obtain ⟨before, beforeMember, beforeMatch⟩ := List.any_eq_true.mp point
  simp only [Bool.and_eq_true] at beforeMatch
  exact ⟨before, beforeMember, by
    simpa [CodeTrace.source, CodeTrace.sourceBlock, CodeTrace.targetPosition,
      CodeTrace.sourceInputMap] using beforeMatch.1, beforeMatch.2⟩

private theorem codeTraceListDestructionCapabilitiesMatch_of_mem
    (positions : List PositionTrace) {traces : List CodeTrace}
    {child : CodeTrace}
    (matched : codeTraceListDestructionCapabilitiesMatch positions traces =
      true)
    (member : child ∈ traces) :
    child.destructionCapabilitiesMatch positions = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListDestructionCapabilitiesMatch,
        Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Destruction capability coherence is inherited by every immediate
recursive compiler call. -/
theorem CodeTrace.destructionCapabilitiesMatch_of_child
    (positions : List PositionTrace) {parent child : CodeTrace}
    (matched : parent.destructionCapabilitiesMatch positions = true)
    (member : child ∈ parent.children) :
    child.destructionCapabilitiesMatch positions = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      simp [CodeTrace.children] at member
      subst child
      simp only [CodeTrace.destructionCapabilitiesMatch,
        Bool.and_eq_true] at matched
      exact matched.2
  | switchValue source block input entryValueCount sourceScrutinee peel
      alternatives targetScrutinee generated outgoing children =>
      exact codeTraceListDestructionCapabilitiesMatch_of_mem positions matched
        member

/-- Every recursive descendant inherits checked destruction capability
coherence. -/
theorem CodeTrace.Descendant.destructionCapabilitiesMatch
    (positions : List PositionTrace) {root child : CodeTrace}
    (descendant : Descendant root child)
    (matched : root.destructionCapabilitiesMatch positions = true) :
    child.destructionCapabilitiesMatch positions = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.destructionCapabilitiesMatch_of_child positions ih
        childMem

/-- Whole-program destructive capability-flow audit. -/
def Trace.destructionCapabilitiesMatch (trace : Trace) : Bool :=
  trace.functions.all fun functionTrace =>
    functionTrace.root.destructionCapabilitiesMatch trace.positions

/-- Project whole-program destruction capability flow to one retained
function. -/
theorem Trace.functionDestructionCapabilitiesMatch {trace : Trace}
    (matched : trace.destructionCapabilitiesMatch = true)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ trace.functions) :
    functionTrace.root.destructionCapabilitiesMatch trace.positions = true :=
  List.all_eq_true.mp matched functionTrace member

/-! ### Exact producer capability flow for ordinary allocation -/

/-- Consuming one operand changes capability state, never its cardinality. -/
theorem consumeCapability?_size {capabilities remaining : Array BindingCap}
    {input : Array (Option Atom)} {world : Owned} {source : IxIR1.Atom}
    (consumed : consumeCapability? capabilities input world source =
      some remaining) :
    remaining.size = capabilities.size := by
  cases source with
  | lit literal =>
      simp [consumeCapability?, sourceCapability?] at consumed
      subst remaining
      rfl
  | erased =>
      simp [consumeCapability?, sourceCapability?] at consumed
      subst remaining
      rfl
  | var index =>
      cases capabilityAt : capabilities[index]? with
      | none => simp [consumeCapability?, sourceCapability?, capabilityAt] at consumed
      | some capability =>
          cases capability with
          | scalar =>
              simp [consumeCapability?, sourceCapability?, capabilityAt] at consumed
              subst remaining
              rfl
          | borrowed actual lender =>
              simp [consumeCapability?, sourceCapability?, capabilityAt] at consumed
          | dead =>
              simp [consumeCapability?, sourceCapability?, capabilityAt] at consumed
          | owned actual =>
              simp [consumeCapability?, sourceCapability?, capabilityAt] at consumed
              obtain ⟨_, remainingEq⟩ := consumed
              exact retireOwnerCapabilities?_size remainingEq

/-- Sequential consumption preserves the source-slot cardinality. -/
theorem consumeCapabilitiesList?_size
    {capabilities remaining : Array BindingCap} {world : Owned}
    {input : Array (Option Atom)} {sources : List IxIR1.Atom}
    (consumed : consumeCapabilitiesList? capabilities input world sources =
      some remaining) :
    remaining.size = capabilities.size := by
  induction sources generalizing capabilities with
  | nil =>
      simp [consumeCapabilitiesList?] at consumed
      subst remaining
      rfl
  | cons source rest ih =>
      simp only [consumeCapabilitiesList?] at consumed
      cases step : consumeCapability? capabilities input world source with
      | none => simp [step] at consumed
      | some next =>
          simp only [step] at consumed
          exact (ih consumed).trans (consumeCapability?_size step)

/-- Heterogeneous consumption preserves source-slot cardinality. -/
theorem consumeCapabilitiesWorlds?_size
    {capabilities remaining : Array BindingCap}
    {input : Array (Option Atom)} {worlds : List Owned}
    {sources : List IxIR1.Atom}
    (consumed : consumeCapabilitiesWorlds? capabilities input worlds sources =
      some remaining) :
    remaining.size = capabilities.size := by
  induction worlds generalizing capabilities sources with
  | nil =>
      cases sources with
      | nil =>
          simp [consumeCapabilitiesWorlds?] at consumed
          subst remaining
          rfl
      | cons source rest => simp [consumeCapabilitiesWorlds?] at consumed
  | cons world worlds ih =>
      cases sources with
      | nil => simp [consumeCapabilitiesWorlds?] at consumed
      | cons source sources =>
          simp only [consumeCapabilitiesWorlds?] at consumed
          cases step : consumeCapability? capabilities input world source with
          | none => simp [step] at consumed
          | some next =>
              simp only [step] at consumed
              exact (ih consumed).trans (consumeCapability?_size step)

/-- Exact capability vector after an ordinary uniform-world allocation. -/
def allocationCapabilities? (capabilities : Array BindingCap)
    (input : Array (Option Atom)) (world : Owned)
    (arguments : Array IxIR1.Atom) :
    Option (Array BindingCap) := do
  let remaining ← consumeCapabilitiesList? capabilities input world
    arguments.toList
  return #[.owned world] ++ remaining

/-- One retained allocation before/after pair has the exact sequential
consume-and-bind capability effect. -/
def PositionTrace.allocationResultMatches (before after : PositionTrace)
    (input : Array (Option Atom)) (world : Owned)
    (arguments : Array IxIR1.Atom) : Bool :=
  match allocationCapabilities? before.sourceCapabilities input world
      arguments with
  | some expected => expected == after.sourceCapabilities
  | none => false

/-- Checked allocation-specific projection of one producer position.  Besides
coordinate/live-map agreement, every source field operand is scalar or an
owner in the allocation world. -/
def PositionTrace.allocationMatches (position : PositionTrace)
    (source : SourceSite) (block : BlockId) (index : Nat)
    (input : Array (Option Atom)) (world : Owned)
    (arguments : Array IxIR1.Atom) : Bool :=
  position.coordinateMatches source block (.instruction index) input &&
    arguments.toList.all fun argument =>
      match sourceCapability? position.sourceCapabilities argument with
      | some capability => capability.canConsume world
      | none => false

/-- Every continuation position of one ordinary allocation is paired with a
current position carrying its exact sequential consumption effect. -/
def CodeTrace.allocationTransitionMatches (positions : List PositionTrace)
    (current next : CodeTrace) (world : Owned)
    (arguments : Array IxIR1.Atom) : Bool :=
  positions.all fun after =>
    if after.coordinateMatches next.source next.sourceBlock
        next.targetPosition next.sourceInputMap then
          positions.any fun before =>
        before.coordinateMatches current.source current.sourceBlock
            current.targetPosition current.sourceInputMap &&
          before.allocationResultMatches after current.sourceInputMap world
            arguments
    else
      true

mutual

/-- Every ordinary constructor or function-PAP allocation node has an exact
sequential consume-and-bind continuation. Constructor allocations additionally
retain their schema-facing producer position; recursive continuations and
switch children satisfy the same audit. -/
def CodeTrace.allocationCapabilitiesMatch
    (positions : List PositionTrace) : CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | trace@(.letOp source block input _ _ operation index _ next) =>
      (match operation with
       | .alloc world _ arguments =>
           (positions.any fun position =>
             position.allocationMatches source block index input world arguments) &&
           trace.allocationTransitionMatches positions next world arguments
       | .papp _ arguments =>
           trace.allocationTransitionMatches positions next .shared arguments
       | _ => true) &&
        next.allocationCapabilitiesMatch positions
  | .switchValue _ _ _ _ _ _ _ _ _ _ children =>
      codeTraceListAllocationCapabilitiesMatch positions children

private def codeTraceListAllocationCapabilitiesMatch
    (positions : List PositionTrace) : List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.allocationCapabilitiesMatch positions &&
        codeTraceListAllocationCapabilitiesMatch positions rest

end

/-- Reflect the retained producer position at one audited allocation node. -/
theorem CodeTrace.allocationPosition_of_capabilities_match
    (positions : List PositionTrace)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {world : Owned} {identity : CtorId}
    {arguments : Array IxIR1.Atom} {index : Nat}
    {instruction : Instr} {next : CodeTrace}
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      (.alloc world identity arguments) index instruction next
        ).allocationCapabilitiesMatch positions = true) :
    ∃ position, position ∈ positions ∧
      position.allocationMatches source block index input world arguments =
        true := by
  change (((positions.any fun position =>
      position.allocationMatches source block index input world arguments) &&
        (CodeTrace.letOp source block input nextInput entryValueCount
          (.alloc world identity arguments) index instruction next
        ).allocationTransitionMatches positions next world arguments) &&
    next.allocationCapabilitiesMatch positions) = true at matched
  simp only [Bool.and_eq_true] at matched
  exact List.any_eq_true.mp matched.1.1

/-- Reflect the exact producer capability predecessor of any matching
continuation position at an audited ordinary allocation. -/
theorem CodeTrace.allocationTransition_of_capabilities_match
    (positions : List PositionTrace)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {world : Owned} {identity : CtorId}
    {arguments : Array IxIR1.Atom} {index : Nat}
    {instruction : Instr} {next : CodeTrace} {after : PositionTrace}
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      (.alloc world identity arguments) index instruction next
        ).allocationCapabilitiesMatch positions = true)
    (afterMember : after ∈ positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    ∃ before, before ∈ positions ∧
      before.coordinateMatches source block (.instruction index) input = true ∧
      before.allocationResultMatches after input world arguments = true := by
  change (((positions.any fun position =>
      position.allocationMatches source block index input world arguments) &&
        (CodeTrace.letOp source block input nextInput entryValueCount
          (.alloc world identity arguments) index instruction next
        ).allocationTransitionMatches positions next world arguments) &&
    next.allocationCapabilitiesMatch positions) = true at matched
  simp only [Bool.and_eq_true] at matched
  have point := List.all_eq_true.mp matched.1.2 after afterMember
  rw [if_pos afterCoordinate] at point
  obtain ⟨before, beforeMember, beforeMatch⟩ := List.any_eq_true.mp point
  simp only [Bool.and_eq_true] at beforeMatch
  exact ⟨before, beforeMember, by
    simpa [CodeTrace.source, CodeTrace.sourceBlock, CodeTrace.targetPosition,
      CodeTrace.sourceInputMap] using beforeMatch.1, beforeMatch.2⟩

/-- Reflect the exact shared capture consumption and fresh PAP-owner binding
at any audited function partial application. -/
theorem CodeTrace.pappTransition_of_capabilities_match
    (positions : List PositionTrace)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {address : Address} {arguments : Array IxIR1.Atom} {index : Nat}
    {instruction : Instr} {next : CodeTrace} {after : PositionTrace}
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      (.papp address arguments) index instruction next
        ).allocationCapabilitiesMatch positions = true)
    (afterMember : after ∈ positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    ∃ before, before ∈ positions ∧
      before.coordinateMatches source block (.instruction index) input = true ∧
      before.allocationResultMatches after input .shared arguments = true := by
  change (((CodeTrace.letOp source block input nextInput entryValueCount
      (.papp address arguments) index instruction next
        ).allocationTransitionMatches positions next .shared arguments &&
    next.allocationCapabilitiesMatch positions) = true) at matched
  simp only [Bool.and_eq_true] at matched
  have point := List.all_eq_true.mp matched.1 after afterMember
  rw [if_pos afterCoordinate] at point
  obtain ⟨before, beforeMember, beforeMatch⟩ := List.any_eq_true.mp point
  simp only [Bool.and_eq_true] at beforeMatch
  exact ⟨before, beforeMember, by
    simpa [CodeTrace.source, CodeTrace.sourceBlock, CodeTrace.targetPosition,
      CodeTrace.sourceInputMap] using beforeMatch.1, beforeMatch.2⟩

/-- An audited allocation position has the exact capability/input-map
cardinality. -/
theorem PositionTrace.sourceCapabilities_size_of_allocationMatch
    {position : PositionTrace} {source : SourceSite} {block : BlockId}
    {index : Nat} {input : Array (Option Atom)} {world : Owned}
    {arguments : Array IxIR1.Atom}
    (matched : position.allocationMatches source block index input world
      arguments = true) :
    position.sourceCapabilities.size = input.size := by
  unfold PositionTrace.allocationMatches at matched
  simp only [Bool.and_eq_true] at matched
  exact sourceCapabilities_size_of_coordinateMatch matched.1

/-- Allocation-specific matching includes the generic recursive-node
coordinate match used by the dynamic ownership invariant. -/
theorem PositionTrace.coordinateMatches_of_allocationMatch
    {position : PositionTrace} {source : SourceSite} {block : BlockId}
    {index : Nat} {input : Array (Option Atom)} {world : Owned}
    {arguments : Array IxIR1.Atom}
    (matched : position.allocationMatches source block index input world
      arguments = true) :
    position.coordinateMatches source block (.instruction index) input =
      true := by
  unfold PositionTrace.allocationMatches at matched
  simp only [Bool.and_eq_true] at matched
  exact matched.1

/-- Every retained allocation argument resolves through a scalar or an exact
owner in the allocation world. -/
theorem PositionTrace.sourceCapability_canConsume_of_allocationMatch
    {position : PositionTrace} {source : SourceSite} {block : BlockId}
    {index : Nat} {input : Array (Option Atom)} {world : Owned}
    {arguments : Array IxIR1.Atom}
    (matched : position.allocationMatches source block index input world
      arguments = true) {argument : IxIR1.Atom}
    (member : argument ∈ arguments.toList) :
    ∃ capability,
      sourceCapability? position.sourceCapabilities argument =
          some capability ∧
        capability.canConsume world = true := by
  unfold PositionTrace.allocationMatches at matched
  simp only [Bool.and_eq_true] at matched
  have argumentsMatched := matched.2
  have argumentMatched :=
    List.all_eq_true.mp argumentsMatched argument member
  cases capabilityAt : sourceCapability? position.sourceCapabilities argument with
  | none => simp [capabilityAt] at argumentMatched
  | some capability =>
      exact ⟨capability, rfl, by simpa [capabilityAt] using argumentMatched⟩

private theorem codeTraceListAllocationCapabilitiesMatch_of_mem
    (positions : List PositionTrace)
    {traces : List CodeTrace} {child : CodeTrace}
    (matched : codeTraceListAllocationCapabilitiesMatch positions traces = true)
    (member : child ∈ traces) :
    child.allocationCapabilitiesMatch positions = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListAllocationCapabilitiesMatch,
        Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Allocation-capability coherence is inherited by every immediate
recursive compiler call. -/
theorem CodeTrace.allocationCapabilitiesMatch_of_child
    (positions : List PositionTrace) {parent child : CodeTrace}
    (matched : parent.allocationCapabilitiesMatch positions = true)
    (member : child ∈ parent.children) :
    child.allocationCapabilitiesMatch positions = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      simp [CodeTrace.children] at member
      subst child
      simp only [CodeTrace.allocationCapabilitiesMatch,
        Bool.and_eq_true] at matched
      exact matched.2
  | switchValue source block input entryValueCount sourceScrutinee peel
      alternatives targetScrutinee generated outgoing children =>
      exact codeTraceListAllocationCapabilitiesMatch_of_mem positions matched
        member

/-- Every recursive descendant inherits the producer capability audit. -/
theorem CodeTrace.Descendant.allocationCapabilitiesMatch
    (positions : List PositionTrace) {root child : CodeTrace}
    (descendant : Descendant root child)
    (matched : root.allocationCapabilitiesMatch positions = true) :
    child.allocationCapabilitiesMatch positions = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.allocationCapabilitiesMatch_of_child positions ih childMem

/-- Whole-program producer capability audit. -/
def Trace.allocationCapabilitiesMatch (trace : Trace) : Bool :=
  trace.functions.all fun functionTrace =>
    functionTrace.root.allocationCapabilitiesMatch trace.positions

/-- Project the whole capability audit to one retained function. -/
theorem Trace.functionAllocationCapabilitiesMatch {trace : Trace}
    (matched : trace.allocationCapabilitiesMatch = true)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ trace.functions) :
    functionTrace.root.allocationCapabilitiesMatch trace.positions = true :=
  List.all_eq_true.mp matched functionTrace member

/-- Does this capability contribute an external ownership root? -/
def BindingCap.hasOwnedRoot : BindingCap → Bool
  | .owned _ => true
  | .scalar | .borrowed .. | .dead => false

/-- Is this capability a borrow whose provenance would have to cross a
suspended source call? -/
def BindingCap.isBorrowed : BindingCap → Bool
  | .borrowed .. => true
  | .scalar | .owned _ | .dead => false

def noOwnedRoots (capabilities : Array BindingCap) : Bool :=
  capabilities.toList.all fun capability => !capability.hasOwnedRoot

def noBorrows (capabilities : Array BindingCap) : Bool :=
  capabilities.toList.all fun capability => !capability.isBorrowed

/-! ### Borrow-free producer state at terminal allocations

The reset/reuse pass only recognizes allocations whose recursive source
continuation is a self tail call.  At that boundary every value which can
survive the allocation is about to cross the owned call ABI, so the producer
must have retired all outstanding borrows.  Keep this as a focused recursive
audit: ordinary allocations may legitimately coexist with live borrows. -/

/-- Check every producer position for one terminal allocation coordinate.
Nonmatching flat positions are irrelevant to the recursive trace node. -/
def terminalAllocationPositionsNoBorrows (positions : List PositionTrace)
    (source : SourceSite) (block : BlockId)
    (input : Array (Option Atom)) (index : Nat) : Bool :=
  positions.all fun position =>
    if position.coordinateMatches source block (.instruction index) input then
      noBorrows position.sourceCapabilities
    else
      true

mutual

/-- Recursive producer audit for allocations immediately followed by a
self-tail terminal.  This is precisely the allocation shape consumed by the
dynamic reset/reuse recognizer. -/
def CodeTrace.terminalAllocationNoBorrows
    (positions : List PositionTrace) : CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | .letOp source block input _ _ operation index _ next =>
      (match operation, next with
       | .alloc .., .tailCallSelf .. =>
           terminalAllocationPositionsNoBorrows positions source block input
             index
       | _, _ => true) &&
        next.terminalAllocationNoBorrows positions
  | .switchValue _ _ _ _ _ _ _ _ _ _ children =>
      codeTraceListTerminalAllocationNoBorrows positions children

private def codeTraceListTerminalAllocationNoBorrows
    (positions : List PositionTrace) : List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.terminalAllocationNoBorrows positions &&
        codeTraceListTerminalAllocationNoBorrows positions rest

end

/-- Reflect the focused audit at one named producer position. -/
theorem CodeTrace.terminalAllocationPositionNoBorrows_of_match
    (positions : List PositionTrace)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {world : Owned} {identity : CtorId} {arguments : Array IxIR1.Atom}
    {index : Nat} {instruction : Instr}
    {tailSource : SourceSite} {tailBlock : BlockId}
    {tailInput : Array (Option Atom)} {tailEntryValueCount : Nat}
    {tailArguments : Array IxIR1.Atom} {generated : Block}
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      (.alloc world identity arguments) index instruction
        (.tailCallSelf tailSource tailBlock tailInput tailEntryValueCount
          tailArguments generated)).terminalAllocationNoBorrows positions =
            true)
    {position : PositionTrace} (member : position ∈ positions)
    (coordinate : position.coordinateMatches source block
      (.instruction index) input = true) :
    noBorrows position.sourceCapabilities = true := by
  change (terminalAllocationPositionsNoBorrows positions source block input
      index && _) = true at matched
  simp only [Bool.and_eq_true] at matched
  have point := List.all_eq_true.mp matched.1 position member
  rw [if_pos coordinate] at point
  exact point

private theorem codeTraceListTerminalAllocationNoBorrows_of_mem
    (positions : List PositionTrace)
    {traces : List CodeTrace} {child : CodeTrace}
    (matched : codeTraceListTerminalAllocationNoBorrows positions traces = true)
    (member : child ∈ traces) :
    child.terminalAllocationNoBorrows positions = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListTerminalAllocationNoBorrows,
        Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- The terminal-allocation audit is inherited by every immediate recursive
compiler call. -/
theorem CodeTrace.terminalAllocationNoBorrows_of_child
    (positions : List PositionTrace) {parent child : CodeTrace}
    (matched : parent.terminalAllocationNoBorrows positions = true)
    (member : child ∈ parent.children) :
    child.terminalAllocationNoBorrows positions = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      simp [CodeTrace.children] at member
      subst child
      simp only [CodeTrace.terminalAllocationNoBorrows,
        Bool.and_eq_true] at matched
      exact matched.2
  | switchValue source block input entryValueCount sourceScrutinee peel
      alternatives targetScrutinee generated outgoing children =>
      exact codeTraceListTerminalAllocationNoBorrows_of_mem positions matched
        member

/-- Every recursive descendant inherits the focused terminal-allocation
borrow audit. -/
theorem CodeTrace.Descendant.terminalAllocationNoBorrows
    (positions : List PositionTrace) {root child : CodeTrace}
    (descendant : Descendant root child)
    (matched : root.terminalAllocationNoBorrows positions = true) :
    child.terminalAllocationNoBorrows positions = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.terminalAllocationNoBorrows_of_child positions ih
        childMem

/-- Whole-program audit for borrow-free terminal allocation coordinates. -/
def Trace.terminalAllocationNoBorrows (trace : Trace) : Bool :=
  trace.functions.all fun functionTrace =>
    functionTrace.root.terminalAllocationNoBorrows trace.positions

/-- Project the whole-program audit to one retained function. -/
theorem Trace.functionTerminalAllocationNoBorrows {trace : Trace}
    (matched : trace.terminalAllocationNoBorrows = true)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ trace.functions) :
    functionTrace.root.terminalAllocationNoBorrows trace.positions = true :=
  List.all_eq_true.mp matched functionTrace member

/-! ### Exact producer capability flow for dynamic application -/

/-- Exact continuation capability vector after dynamic application.  The
function value and every newly supplied argument cross the shared owned
boundary in source order; the dynamically returned value is then bound as a
fresh shared owner. -/
def applyCapabilities? (capabilities : Array BindingCap)
    (input : Array (Option Atom)) (function : IxIR1.Atom)
    (arguments : Array IxIR1.Atom) : Option (Array BindingCap) := do
  let remaining ← consumeCapability? capabilities input .shared function
  let remaining ← consumeCapabilitiesList? remaining input .shared
    arguments.toList
  return #[.owned .shared] ++ remaining

/-- One retained dynamic-application before/after pair has the exact
consume-function/consume-arguments/bind-result effect. -/
def PositionTrace.applyResultMatches (before after : PositionTrace)
    (input : Array (Option Atom)) (function : IxIR1.Atom)
    (arguments : Array IxIR1.Atom) : Bool :=
  match applyCapabilities? before.sourceCapabilities input function arguments with
  | some expected =>
      noBorrows expected && expected == after.sourceCapabilities
  | none => false

/-- Every continuation position of one dynamic application has an exact
capability predecessor. -/
def CodeTrace.applyTransitionMatches (positions : List PositionTrace)
    (current next : CodeTrace) (function : IxIR1.Atom)
    (arguments : Array IxIR1.Atom) : Bool :=
  positions.all fun after =>
    if after.coordinateMatches next.source next.sourceBlock
        next.targetPosition next.sourceInputMap then
      positions.any fun before =>
        before.coordinateMatches current.source current.sourceBlock
            current.targetPosition current.sourceInputMap &&
          before.applyResultMatches after current.sourceInputMap function
            arguments
    else
      true

mutual

/-- Recursive exact capability audit for dynamic application. -/
def CodeTrace.applyCapabilitiesMatch
    (positions : List PositionTrace) : CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | trace@(.letOp _ _ _ _ _ operation _ _ next) =>
      (match operation with
       | .apply function arguments =>
           trace.applyTransitionMatches positions next function arguments
       | _ => true) &&
        next.applyCapabilitiesMatch positions
  | .switchValue _ _ _ _ _ _ _ _ _ _ children =>
      codeTraceListApplyCapabilitiesMatch positions children

private def codeTraceListApplyCapabilitiesMatch
    (positions : List PositionTrace) : List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.applyCapabilitiesMatch positions &&
        codeTraceListApplyCapabilitiesMatch positions rest

end

/-- Reflect the exact producer capability predecessor of any matching
continuation position at an audited dynamic application. -/
theorem CodeTrace.applyTransition_of_capabilities_match
    (positions : List PositionTrace)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {function : IxIR1.Atom} {arguments : Array IxIR1.Atom} {index : Nat}
    {instruction : Instr} {next : CodeTrace} {after : PositionTrace}
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      (.apply function arguments) index instruction next
        ).applyCapabilitiesMatch positions = true)
    (afterMember : after ∈ positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    ∃ before, before ∈ positions ∧
      before.coordinateMatches source block (.instruction index) input = true ∧
      before.applyResultMatches after input function arguments = true := by
  change (((CodeTrace.letOp source block input nextInput entryValueCount
      (.apply function arguments) index instruction next
        ).applyTransitionMatches positions next function arguments &&
    next.applyCapabilitiesMatch positions) = true) at matched
  simp only [Bool.and_eq_true] at matched
  have point := List.all_eq_true.mp matched.1 after afterMember
  rw [if_pos afterCoordinate] at point
  obtain ⟨before, beforeMember, beforeMatch⟩ := List.any_eq_true.mp point
  simp only [Bool.and_eq_true] at beforeMatch
  exact ⟨before, beforeMember, by
    simpa [CodeTrace.source, CodeTrace.sourceBlock, CodeTrace.targetPosition,
      CodeTrace.sourceInputMap] using beforeMatch.1, beforeMatch.2⟩

private theorem codeTraceListApplyCapabilitiesMatch_of_mem
    (positions : List PositionTrace)
    {traces : List CodeTrace} {child : CodeTrace}
    (matched : codeTraceListApplyCapabilitiesMatch positions traces = true)
    (member : child ∈ traces) :
    child.applyCapabilitiesMatch positions = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListApplyCapabilitiesMatch,
        Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Dynamic-application capability coherence is inherited by every immediate
recursive compiler call. -/
theorem CodeTrace.applyCapabilitiesMatch_of_child
    (positions : List PositionTrace) {parent child : CodeTrace}
    (matched : parent.applyCapabilitiesMatch positions = true)
    (member : child ∈ parent.children) :
    child.applyCapabilitiesMatch positions = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      simp [CodeTrace.children] at member
      subst child
      simp only [CodeTrace.applyCapabilitiesMatch,
        Bool.and_eq_true] at matched
      exact matched.2
  | switchValue source block input entryValueCount sourceScrutinee peel
      alternatives targetScrutinee generated outgoing children =>
      exact codeTraceListApplyCapabilitiesMatch_of_mem positions matched member

/-- Every recursive descendant inherits checked dynamic-application
capability coherence. -/
theorem CodeTrace.Descendant.applyCapabilitiesMatch
    (positions : List PositionTrace) {root child : CodeTrace}
    (descendant : Descendant root child)
    (matched : root.applyCapabilitiesMatch positions = true) :
    child.applyCapabilitiesMatch positions = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.applyCapabilitiesMatch_of_child positions ih childMem

/-- Whole-program dynamic-application capability-flow audit. -/
def Trace.applyCapabilitiesMatch (trace : Trace) : Bool :=
  trace.functions.all fun functionTrace =>
    functionTrace.root.applyCapabilitiesMatch trace.positions

/-- Project the whole dynamic-application audit to one retained function. -/
theorem Trace.functionApplyCapabilitiesMatch {trace : Trace}
    (matched : trace.applyCapabilitiesMatch = true)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ trace.functions) :
    functionTrace.root.applyCapabilitiesMatch trace.positions = true :=
  List.all_eq_true.mp matched functionTrace member

/-! ### Exact producer capability flow for calls and returns -/

/-- The baseline call ABI accepts only owned parameters.  Keeping this
projection executable makes a future borrowed-parameter ABI an explicit
extension rather than silently treating a borrow as a transfer. -/
def ownedParameterWorlds? : List Param → Option (List Owned)
  | [] => some []
  | parameter :: rest =>
      if parameter.passing == .owned then
        (ownedParameterWorlds? rest).map (parameter.world :: ·)
      else
        none

/-- Capability vector visible in source de Bruijn order at a target function
entry. Target parameters arrive in call order, hence the reversal. -/
def entryCapabilities (signature : Signature) : Array BindingCap :=
  signature.params.toList.reverse.map (fun parameter =>
    match parameter.passing with
    | .owned => .owned parameter.world
    | .borrowed => .borrowed parameter.world .caller) |>.toArray

/-! ### PAP-safe function-entry capabilities -/

/-- A PAP-safe retained function must expose the all-owned/shared entry
capability vector required by dynamic saturation.  Keeping this check in the
artifact audit makes the runtime PAP boundary independent of validator
implementation details. -/
def FunctionTrace.sharedPapEntryCapabilitiesMatch
    (trace : FunctionTrace) : Bool :=
  if trace.generated.signature.papSafe then
    entryCapabilities trace.generated.signature ==
      Array.replicate trace.generated.signature.params.size (.owned .shared)
  else
    true

/-- Whole-program PAP-entry capability audit. -/
def Trace.sharedPapEntryCapabilitiesMatch (trace : Trace) : Bool :=
  trace.functions.all FunctionTrace.sharedPapEntryCapabilitiesMatch

/-- Project the PAP-entry audit to one retained function. -/
theorem Trace.functionSharedPapEntryCapabilitiesMatch {trace : Trace}
    (matched : trace.sharedPapEntryCapabilitiesMatch = true)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ trace.functions) :
    functionTrace.sharedPapEntryCapabilitiesMatch = true :=
  List.all_eq_true.mp matched functionTrace member

/-- Consume the arguments of one baseline call using its owned parameter
telescope. -/
def callRemainingCapabilities? (capabilities : Array BindingCap)
    (input : Array (Option Atom)) (signature : Signature)
    (arguments : Array IxIR1.Atom) : Option (Array BindingCap) := do
  let worlds ← ownedParameterWorlds? signature.params.toList
  consumeCapabilitiesWorlds? capabilities input worlds arguments.toList

/-- Exact ordinary-call continuation state: transferred argument owners are
retired, no borrow remains suspended in the baseline ABI, and the returned
owner is bound at the source-environment head. -/
def PositionTrace.callResultMatches (before after : PositionTrace)
    (input : Array (Option Atom)) (signature : Signature)
    (arguments : Array IxIR1.Atom) : Bool :=
  match callRemainingCapabilities? before.sourceCapabilities input signature
      arguments with
  | some remaining =>
      noBorrows remaining &&
        (#[.owned signature.result] ++ remaining) == after.sourceCapabilities
  | none => false

/-- Every matching predecessor/continuation pair of an ordinary call has the
same exact consume/suspend/result-bind transition. Quantifying both sides
prevents duplicate flat coordinates from choosing different suspended root
frames. -/
def CodeTrace.callTransitionMatches (positions : List PositionTrace)
    (current next : CodeTrace) (signature : Signature)
    (arguments : Array IxIR1.Atom) : Bool :=
  positions.all fun after =>
    if after.coordinateMatches next.source next.sourceBlock
        next.targetPosition next.sourceInputMap then
      positions.all fun before =>
        if before.coordinateMatches current.source current.sourceBlock
            current.targetPosition current.sourceInputMap then
          before.callResultMatches after current.sourceInputMap signature
            arguments
        else
          true
    else
      true

/-- A tail call transfers every local owner before discarding its frame. -/
def PositionTrace.tailCallMatches (position : PositionTrace)
    (source : SourceSite) (block : BlockId)
    (input : Array (Option Atom)) (signature : Signature)
    (arguments : Array IxIR1.Atom) : Bool :=
  position.coordinateMatches source block .terminator input &&
    match callRemainingCapabilities? position.sourceCapabilities input
        signature arguments with
    | some remaining => noOwnedRoots remaining
    | none => false

/-- A source return transfers exactly its declared result owner and leaves no
other local owner behind. Scalars remain ownership-inert. -/
def PositionTrace.returnMatches (position : PositionTrace)
    (source : SourceSite) (block : BlockId)
    (input : Array (Option Atom)) (result : Owned)
    (atom : IxIR1.Atom) : Bool :=
  position.coordinateMatches source block .terminator input &&
    match consumeCapability? position.sourceCapabilities input result atom with
    | some remaining => noOwnedRoots remaining
    | none => false

/-- Lookup the checked target signature used to audit an addressed source
call. -/
def targetSignature? (declarations : List (Address × Decl))
    (address : Address) : Option Signature := do
  let declaration ←
    (declarations.find? fun entry => entry.1 == address).map (fun entry => entry.2)
  match declaration with
  | .fn definition => some definition.signature
  | .extern _ => none

/-- All flat positions matching one function root carry the canonical entry
capability vector of its emitted signature. -/
def FunctionTrace.entryCapabilitiesMatch (trace : FunctionTrace)
    (positions : List PositionTrace) : Bool :=
  positions.all fun position =>
    if position.coordinateMatches trace.root.source trace.root.sourceBlock
        trace.root.targetPosition trace.root.sourceInputMap then
      position.sourceCapabilities == entryCapabilities trace.generated.signature
    else
      true

mutual

/-- Recursive call/return capability audit for one retained function. -/
def CodeTrace.callCapabilitiesMatch (positions : List PositionTrace)
    (declarations : List (Address × Decl)) (current : Signature) :
    CodeTrace → Bool
  | trace@(.ret source block input _ atom _ _) =>
      positions.all fun position =>
        if position.coordinateMatches trace.source trace.sourceBlock
            trace.targetPosition trace.sourceInputMap then
          position.returnMatches source block input current.result atom
        else
          true
  | .tailCall source block input _ address arguments _ =>
      match targetSignature? declarations address with
      | some signature => signature.result == current.result &&
          positions.any fun position =>
            position.tailCallMatches source block input signature arguments
      | none => false
  | .tailCallSelf source block input _ arguments _ =>
      positions.any fun position =>
        position.tailCallMatches source block input current arguments
  | trace@(.letOp _ _ _ _ _ operation _ _ next) =>
      (match operation with
       | .call address arguments =>
           match targetSignature? declarations address with
           | some signature =>
               trace.callTransitionMatches positions next signature arguments
           | none => false
       | .callSelf arguments =>
           trace.callTransitionMatches positions next current arguments
       | _ => true) &&
        next.callCapabilitiesMatch positions declarations current
  | .switchValue _ _ _ _ _ _ _ _ _ _ children =>
      codeTraceListCallCapabilitiesMatch positions declarations current children

private def codeTraceListCallCapabilitiesMatch
    (positions : List PositionTrace)
    (declarations : List (Address × Decl)) (current : Signature) :
    List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.callCapabilitiesMatch positions declarations current &&
        codeTraceListCallCapabilitiesMatch positions declarations current rest

end

/-- One retained function has canonical entry capabilities and exact
call/return ownership flow throughout its recursive trace. -/
def FunctionTrace.callCapabilitiesMatch (trace : FunctionTrace)
    (positions : List PositionTrace)
    (declarations : List (Address × Decl)) : Bool :=
  trace.entryCapabilitiesMatch positions &&
    trace.root.callCapabilitiesMatch positions declarations
      trace.generated.signature

/-- Whole-program call/return capability-flow audit. -/
def FunctionTrace.targetSignatureMatches (trace : FunctionTrace)
    (declarations : List (Address × Decl)) : Bool :=
  match trace.owner with
  | .main => true
  | .declaration address =>
      targetSignature? declarations address == some trace.generated.signature

/-- Whole-program call/return capability-flow audit. Besides local flow, each
declaration-owned trace is tied to the signature selected by the executable
target declaration lookup used at call sites. -/
def Trace.callCapabilitiesMatch (trace : Trace)
    (declarations : List (Address × Decl)) : Bool :=
  (trace.functions.all fun functionTrace =>
    functionTrace.callCapabilitiesMatch trace.positions declarations) &&
  (trace.functions.all fun functionTrace =>
    functionTrace.targetSignatureMatches declarations)

private theorem codeTraceListCallCapabilitiesMatch_of_mem
    (positions : List PositionTrace)
    (declarations : List (Address × Decl)) (current : Signature)
    {traces : List CodeTrace} {child : CodeTrace}
    (matched : codeTraceListCallCapabilitiesMatch positions declarations
      current traces = true)
    (member : child ∈ traces) :
    child.callCapabilitiesMatch positions declarations current = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListCallCapabilitiesMatch,
        Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Call/return capability coherence is inherited by every recursive child. -/
theorem CodeTrace.callCapabilitiesMatch_of_child
    (positions : List PositionTrace)
    (declarations : List (Address × Decl)) (current : Signature)
    {parent child : CodeTrace}
    (matched : parent.callCapabilitiesMatch positions declarations current =
      true)
    (member : child ∈ parent.children) :
    child.callCapabilitiesMatch positions declarations current = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      simp [CodeTrace.children] at member
      subst child
      simp only [CodeTrace.callCapabilitiesMatch,
        Bool.and_eq_true] at matched
      exact matched.2
  | switchValue source block input entryValueCount sourceScrutinee peel
      alternatives targetScrutinee generated outgoing children =>
      exact codeTraceListCallCapabilitiesMatch_of_mem positions declarations
        current matched member

/-- Every recursive descendant inherits checked call/return capability flow. -/
theorem CodeTrace.Descendant.callCapabilitiesMatch
    (positions : List PositionTrace)
    (declarations : List (Address × Decl)) (current : Signature)
    {root child : CodeTrace} (descendant : Descendant root child)
    (matched : root.callCapabilitiesMatch positions declarations current =
      true) :
    child.callCapabilitiesMatch positions declarations current = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.callCapabilitiesMatch_of_child positions declarations
        current ih childMem

/-- Project the whole-program call audit to one retained function. -/
theorem Trace.functionCallCapabilitiesMatch {trace : Trace}
    {declarations : List (Address × Decl)}
    (matched : trace.callCapabilitiesMatch declarations = true)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ trace.functions) :
    functionTrace.callCapabilitiesMatch trace.positions declarations = true :=
  by
    simp only [Trace.callCapabilitiesMatch, Bool.and_eq_true] at matched
    exact List.all_eq_true.mp matched.1 functionTrace member

/-- A declaration-owned retained trace has the exact signature selected by
the call audit's target lookup. -/
theorem Trace.targetSignature_of_call_match {trace : Trace}
    {declarations : List (Address × Decl)}
    (matched : trace.callCapabilitiesMatch declarations = true)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ trace.functions)
    {address : Address} (owner : functionTrace.owner = .declaration address) :
    targetSignature? declarations address =
      some functionTrace.generated.signature := by
  simp only [Trace.callCapabilitiesMatch, Bool.and_eq_true] at matched
  have point := List.all_eq_true.mp matched.2 functionTrace member
  unfold FunctionTrace.targetSignatureMatches at point
  rw [owner] at point
  exact beq_iff_eq.mp point

/-- Recover canonical entry capabilities from a checked function audit. -/
theorem FunctionTrace.entryCapabilities_of_call_match
    {trace : FunctionTrace} {positions : List PositionTrace}
    {declarations : List (Address × Decl)}
    (matched : trace.callCapabilitiesMatch positions declarations = true)
    {position : PositionTrace} (member : position ∈ positions)
    (coordinate : position.coordinateMatches trace.root.source
      trace.root.sourceBlock trace.root.targetPosition
      trace.root.sourceInputMap = true) :
    position.sourceCapabilities = entryCapabilities trace.generated.signature := by
  simp only [FunctionTrace.callCapabilitiesMatch, Bool.and_eq_true] at matched
  have point := List.all_eq_true.mp matched.1 position member
  rw [if_pos coordinate] at point
  exact beq_iff_eq.mp point

/-- Reflect an addressed ordinary call's exact predecessor and continuation
effect. -/
theorem CodeTrace.callTransition_of_capabilities_match
    (positions : List PositionTrace)
    (declarations : List (Address × Decl)) (current : Signature)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {address : Address} {signature : Signature}
    {arguments : Array IxIR1.Atom} {index : Nat} {instruction : Instr}
    {next : CodeTrace} {before after : PositionTrace}
    (signatureAt : targetSignature? declarations address = some signature)
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      (.call address arguments) index instruction next).callCapabilitiesMatch positions
        declarations current = true)
    (beforeMember : before ∈ positions)
    (beforeCoordinate : before.coordinateMatches source block
      (.instruction index) input = true)
    (afterMember : after ∈ positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    before.callResultMatches after input signature arguments = true := by
  simp only [CodeTrace.callCapabilitiesMatch, signatureAt,
    Bool.and_eq_true] at matched
  have transition := matched.1
  have point := List.all_eq_true.mp transition after afterMember
  rw [if_pos afterCoordinate] at point
  have beforePoint := List.all_eq_true.mp point before beforeMember
  rw [if_pos (by
    simpa [CodeTrace.source, CodeTrace.sourceBlock, CodeTrace.targetPosition,
      CodeTrace.sourceInputMap] using beforeCoordinate)] at beforePoint
  exact beforePoint

/-- Reflect a self call's exact predecessor and continuation effect. -/
theorem CodeTrace.callSelfTransition_of_capabilities_match
    (positions : List PositionTrace)
    (declarations : List (Address × Decl)) (current : Signature)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {arguments : Array IxIR1.Atom} {index : Nat} {instruction : Instr}
    {next : CodeTrace} {before after : PositionTrace}
    (matched : (CodeTrace.letOp source block input nextInput entryValueCount
      (.callSelf arguments) index instruction next).callCapabilitiesMatch
        positions declarations current = true)
    (beforeMember : before ∈ positions)
    (beforeCoordinate : before.coordinateMatches source block
      (.instruction index) input = true)
    (afterMember : after ∈ positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    before.callResultMatches after input current arguments = true := by
  simp only [CodeTrace.callCapabilitiesMatch, Bool.and_eq_true] at matched
  have point := List.all_eq_true.mp matched.1 after afterMember
  rw [if_pos afterCoordinate] at point
  have beforePoint := List.all_eq_true.mp point before beforeMember
  rw [if_pos (by
    simpa [CodeTrace.source, CodeTrace.sourceBlock, CodeTrace.targetPosition,
      CodeTrace.sourceInputMap] using beforeCoordinate)] at beforePoint
  exact beforePoint

/-- Reflect the exact terminal transfer at a checked addressed tail call. -/
theorem CodeTrace.tailCallPosition_of_capabilities_match
    (positions : List PositionTrace)
    (declarations : List (Address × Decl)) (current : Signature)
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {address : Address} {signature : Signature}
    {arguments : Array IxIR1.Atom} {generated : Block}
    (signatureAt : targetSignature? declarations address = some signature)
    (matched : (CodeTrace.tailCall source block input entryValueCount address
      arguments generated).callCapabilitiesMatch positions declarations current =
        true) :
    ∃ position, position ∈ positions ∧
      position.tailCallMatches source block input signature arguments = true := by
  change (match targetSignature? declarations address with
    | some found => found.result == current.result &&
        positions.any fun position =>
          position.tailCallMatches source block input found arguments
    | none => false) = true at matched
  rw [signatureAt] at matched
  simp only [Bool.and_eq_true] at matched
  exact List.any_eq_true.mp matched.2

/-- A checked addressed tail call preserves the dynamic result world. This
is needed when source completion crosses a replaced caller frame. -/
theorem CodeTrace.tailCallResult_of_capabilities_match
    (positions : List PositionTrace)
    (declarations : List (Address × Decl)) (current : Signature)
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {address : Address} {signature : Signature}
    {arguments : Array IxIR1.Atom} {generated : Block}
    (signatureAt : targetSignature? declarations address = some signature)
    (matched : (CodeTrace.tailCall source block input entryValueCount address
      arguments generated).callCapabilitiesMatch positions declarations current =
        true) :
    signature.result = current.result := by
  simp only [CodeTrace.callCapabilitiesMatch, signatureAt,
    Bool.and_eq_true, beq_iff_eq] at matched
  exact matched.1

/-- Reflect the exact terminal transfer at a checked self tail call. -/
theorem CodeTrace.tailCallSelfPosition_of_capabilities_match
    (positions : List PositionTrace)
    (declarations : List (Address × Decl)) (current : Signature)
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {arguments : Array IxIR1.Atom} {generated : Block}
    (matched : (CodeTrace.tailCallSelf source block input entryValueCount
      arguments generated).callCapabilitiesMatch positions declarations current =
        true) :
    ∃ position, position ∈ positions ∧
      position.tailCallMatches source block input current arguments = true := by
  exact List.any_eq_true.mp matched

/-- Reflect the exact return transfer at one checked terminal position. -/
theorem CodeTrace.returnPositionMatch_of_capabilities_match
    (positions : List PositionTrace)
    (declarations : List (Address × Decl)) (current : Signature)
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {atom : IxIR1.Atom} {target : Atom} {generated : Block}
    (matched : (CodeTrace.ret source block input entryValueCount atom target
      generated).callCapabilitiesMatch positions declarations current = true)
    {position : PositionTrace} (member : position ∈ positions)
    (coordinate : position.coordinateMatches source block .terminator input =
      true) :
    position.returnMatches source block input current.result atom = true := by
  change (positions.all fun candidate =>
    if candidate.coordinateMatches source block .terminator input then
      candidate.returnMatches source block input current.result atom
    else true) = true at matched
  have point := List.all_eq_true.mp matched position member
  rw [if_pos coordinate] at point
  exact point

/-! ### Producer capability flow across switch edges -/

/-- The first source slot whose live owner is carried by a given predecessor
register. This is the source-index form of the lowerer's private
`ownerParameter?` search. -/
def edgeOwnerIndex? (capabilities : Array BindingCap)
    (input : Array (Option Atom)) (lender : ValueId) : Option Nat :=
  (List.range capabilities.size).find? fun index =>
    match capabilities[index]?, input[index]? with
    | some (.owned _), some (some (.reg actual)) => actual == lender
    | _, _ => false

/-- Rebase one producer capability onto the canonical same-index registers of
a generated CFG edge. Local borrows are accepted only when the lowerer's
selected owner has the same world as the borrow. -/
def BindingCap.rebaseEdge? (capabilities : Array BindingCap)
    (input : Array (Option Atom)) : BindingCap → Option BindingCap
  | .scalar => some .scalar
  | .owned world => some (.owned world)
  | .borrowed world .caller => some (.borrowed world .caller)
  | .borrowed world (.value lender) =>
      match edgeOwnerIndex? capabilities input lender with
      | some ownerIndex =>
          match capabilities[ownerIndex]? with
          | some (.owned ownerWorld) =>
              if ownerWorld == world then
                some (.borrowed world (.value ownerIndex))
              else
                none
          | _ => none
      | none => none
  | .dead => some .dead

/-- Canonical capability vector after a generated edge has copied every live
source slot into the same-index target parameter. -/
def edgeCapabilities? (capabilities : Array BindingCap)
    (input : Array (Option Atom)) : Option (Array BindingCap) :=
  if capabilities.toList.all fun capability =>
      (capability.rebaseEdge? capabilities input).isSome then
    some (capabilities.map fun capability =>
      (capability.rebaseEdge? capabilities input).getD .dead)
  else
    none

/-- Edge rebasing preserves the producer capability-vector cardinality. -/
theorem edgeCapabilities?_size
    {capabilities output : Array BindingCap}
    {input : Array (Option Atom)}
    (result : edgeCapabilities? capabilities input = some output) :
    output.size = capabilities.size := by
  unfold edgeCapabilities? at result
  split at result
  · injection result with outputEq
    subst output
    simp
  · contradiction

/-- Shift local lender registers across an implicit block-parameter prefix. -/
def BindingCap.shiftLender (amount : Nat) : BindingCap → BindingCap
  | .borrowed world (.value lender) =>
      .borrowed world (.value (lender + amount))
  | capability => capability

/-- Exact capability vector at a constructor child: the edge-rebased source
slots are preceded by borrowed fields in reverse source-binding order. -/
def constructorChildCapabilities?
    (schemas : Owned → CtorId → Option CtorSchema)
    (input : Array (Option Atom)) (scrutinee : IxIR1.Atom) (cid : CtorId)
    (capabilities : Array BindingCap) : Option (Array BindingCap) :=
  match edgeCapabilities? capabilities input with
  | none => none
  | some rebased =>
      match scrutinee with
      | .var sourceIndex =>
          match rebased[sourceIndex]? with
          | some (.owned world) =>
              match schemas world cid with
              | some schema =>
                  let fields := schema.fields.map fun fieldWorld =>
                    BindingCap.borrowed fieldWorld (.value sourceIndex)
                  some (fields.reverse ++ rebased)
              | none => none
          | some (.borrowed world lender) =>
              match schemas world cid with
              | some schema =>
                  let fields := schema.fields.map fun fieldWorld =>
                    BindingCap.borrowed fieldWorld lender
                  some (fields.reverse ++ rebased)
              | none => none
          | _ => none
      | .lit _ | .erased => none

/-- Exact capability vector at a literal-zero child. -/
def natZeroChildCapabilities? (input : Array (Option Atom))
    (capabilities : Array BindingCap) : Option (Array BindingCap) :=
  edgeCapabilities? capabilities input

/-- Exact capability vector at a literal-successor child. The peeled scalar
occupies register zero, so every local lender is shifted once. -/
def natSuccChildCapabilities? (input : Array (Option Atom))
    (capabilities : Array BindingCap) : Option (Array BindingCap) :=
  match edgeCapabilities? capabilities input with
  | some rebased =>
      some (#[.scalar] ++ rebased.map (BindingCap.shiftLender 1))
  | none => none

/-- Every matching child position has a producer predecessor whose capability
vector evolves by `expected`. The whole-position audit separately guarantees
that both coordinate sets are inhabited. -/
def CodeTrace.branchTransitionMatches (positions : List PositionTrace)
    (current child : CodeTrace)
    (expected : Array BindingCap → Option (Array BindingCap)) : Bool :=
  positions.all fun after =>
    if after.coordinateMatches child.source child.sourceBlock
        child.targetPosition child.sourceInputMap then
      positions.any fun before =>
        before.coordinateMatches current.source current.sourceBlock
            current.targetPosition current.sourceInputMap &&
          (expected before.sourceCapabilities ==
            some after.sourceCapabilities)
    else
      true

/-- Local switch ownership-flow audit. Constructor children use their selected
schema; optional Nat children occupy the two canonical post-constructor
ordinals. Structural branch coherence independently certifies those ordinals. -/
def CodeTrace.switchNodeCapabilitiesMatch
    (schemas : Owned → CtorId → Option CtorSchema)
    (positions : List PositionTrace) : CodeTrace → Bool
  | trace@(.switchValue _ _ input _ sourceScrutinee peelNat _ _ generated _
      children) =>
      match generated.terminator with
      | .switchValue _ constructors natPeel =>
          (constructors.toList.zipIdx.all fun pair =>
            match children[pair.2]? with
            | some child =>
                trace.branchTransitionMatches positions child fun before =>
                  constructorChildCapabilities? schemas input sourceScrutinee
                    pair.1.cid before
            | none => false) &&
          match peelNat, natPeel with
          | false, none => true
          | true, some _ =>
              match children[constructors.size]?,
                  children[constructors.size + 1]? with
              | some zeroChild, some succChild =>
                  trace.branchTransitionMatches positions zeroChild
                      (natZeroChildCapabilities? input) &&
                    trace.branchTransitionMatches positions succChild
                      (natSuccChildCapabilities? input)
              | _, _ => false
          | _, _ => false
      | _ => false
  | _ => true

mutual

/-- Recursive audit of every switch capability transition in a code tree. -/
def CodeTrace.switchCapabilitiesMatch
    (schemas : Owned → CtorId → Option CtorSchema)
    (positions : List PositionTrace) : CodeTrace → Bool
  | .ret .. | .tailCall .. | .tailCallSelf .. => true
  | .letOp _ _ _ _ _ _ _ _ next =>
      next.switchCapabilitiesMatch schemas positions
  | trace@(.switchValue _ _ _ _ _ _ _ _ _ _ children) =>
      trace.switchNodeCapabilitiesMatch schemas positions &&
        codeTraceListSwitchCapabilitiesMatch schemas positions children

private def codeTraceListSwitchCapabilitiesMatch
    (schemas : Owned → CtorId → Option CtorSchema)
    (positions : List PositionTrace) : List CodeTrace → Bool
  | [] => true
  | trace :: rest =>
      trace.switchCapabilitiesMatch schemas positions &&
        codeTraceListSwitchCapabilitiesMatch schemas positions rest

end

/-- Whole-program switch capability-flow audit. -/
def Trace.switchCapabilitiesMatch (trace : Trace)
    (schemas : Owned → CtorId → Option CtorSchema) : Bool :=
  trace.functions.all fun functionTrace =>
    functionTrace.root.switchCapabilitiesMatch schemas trace.positions

/-- Reflect the producer predecessor of one matching switch-child position. -/
theorem CodeTrace.branchTransition_of_match
    (positions : List PositionTrace) {current child : CodeTrace}
    {expected : Array BindingCap → Option (Array BindingCap)}
    {after : PositionTrace}
    (matched : current.branchTransitionMatches positions child expected = true)
    (afterMember : after ∈ positions)
    (afterCoordinate : after.coordinateMatches child.source child.sourceBlock
      child.targetPosition child.sourceInputMap = true) :
    ∃ before, before ∈ positions ∧
      before.coordinateMatches current.source current.sourceBlock
        current.targetPosition current.sourceInputMap = true ∧
      expected before.sourceCapabilities = some after.sourceCapabilities := by
  have point := List.all_eq_true.mp matched after afterMember
  rw [if_pos afterCoordinate] at point
  obtain ⟨before, beforeMember, beforeMatch⟩ := List.any_eq_true.mp point
  simp only [Bool.and_eq_true] at beforeMatch
  exact ⟨before, beforeMember, beforeMatch.1,
    beq_iff_eq.mp beforeMatch.2⟩

/-- Select the checked constructor capability transition at one exact
parallel branch ordinal. -/
theorem CodeTrace.constructorBranchTransition_of_switch_match
    (schemas : Owned → CtorId → Option CtorSchema)
    (positions : List PositionTrace)
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List EdgeTrace}
    {children : List CodeTrace} {constructors : Array CtorAlt}
    {natPeel : Option NatPeel} {index : Nat} {target : CtorAlt}
    {child : CodeTrace} {after : PositionTrace}
    (matched : (CodeTrace.switchValue source block input entryValueCount
      sourceScrutinee peelNat alternatives targetScrutinee generated outgoing
      children).switchNodeCapabilitiesMatch schemas positions = true)
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors natPeel)
    (targetAt : constructors[index]? = some target)
    (childAt : children[index]? = some child)
    (afterMember : after ∈ positions)
    (afterCoordinate : after.coordinateMatches child.source child.sourceBlock
      child.targetPosition child.sourceInputMap = true) :
    ∃ before, before ∈ positions ∧
      before.coordinateMatches source block .terminator input = true ∧
      constructorChildCapabilities? schemas input sourceScrutinee target.cid
        before.sourceCapabilities = some after.sourceCapabilities := by
  have matched' := matched
  simp only [CodeTrace.switchNodeCapabilitiesMatch, terminator,
    Bool.and_eq_true] at matched'
  have targetListAt : constructors.toList[index]? = some target := by
    simpa using targetAt
  have targetMember : (target, index) ∈ constructors.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr targetListAt
  have point := List.all_eq_true.mp matched'.1 (target, index) targetMember
  simp only [childAt] at point
  have transition := CodeTrace.branchTransition_of_match positions point
    afterMember afterCoordinate
  simpa [CodeTrace.source, CodeTrace.sourceBlock, CodeTrace.targetPosition,
    CodeTrace.sourceInputMap] using transition

/-- Select the checked literal-zero capability transition at its canonical
post-constructor ordinal. -/
theorem CodeTrace.natZeroBranchTransition_of_switch_match
    (schemas : Owned → CtorId → Option CtorSchema)
    (positions : List PositionTrace)
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {targetScrutinee : Atom} {generated : Block}
    {outgoing : List EdgeTrace} {children : List CodeTrace}
    {constructors : Array CtorAlt} {peel : NatPeel}
    {zeroChild succChild : CodeTrace} {after : PositionTrace}
    (matched : (CodeTrace.switchValue source block input entryValueCount
      sourceScrutinee true alternatives targetScrutinee generated outgoing
      children).switchNodeCapabilitiesMatch schemas positions = true)
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors (some peel))
    (zeroChildAt : children[constructors.size]? = some zeroChild)
    (succChildAt : children[constructors.size + 1]? = some succChild)
    (afterMember : after ∈ positions)
    (afterCoordinate : after.coordinateMatches zeroChild.source
      zeroChild.sourceBlock zeroChild.targetPosition zeroChild.sourceInputMap =
        true) :
    ∃ before, before ∈ positions ∧
      before.coordinateMatches source block .terminator input = true ∧
      natZeroChildCapabilities? input before.sourceCapabilities =
        some after.sourceCapabilities := by
  have matched' := matched
  simp only [CodeTrace.switchNodeCapabilitiesMatch, terminator, zeroChildAt,
    succChildAt, Bool.and_eq_true] at matched'
  have transition := CodeTrace.branchTransition_of_match positions
    matched'.2.1 afterMember afterCoordinate
  simpa [CodeTrace.source, CodeTrace.sourceBlock, CodeTrace.targetPosition,
    CodeTrace.sourceInputMap] using transition

/-- Select the checked literal-successor capability transition at its
canonical post-constructor ordinal. -/
theorem CodeTrace.natSuccBranchTransition_of_switch_match
    (schemas : Owned → CtorId → Option CtorSchema)
    (positions : List PositionTrace)
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {targetScrutinee : Atom} {generated : Block}
    {outgoing : List EdgeTrace} {children : List CodeTrace}
    {constructors : Array CtorAlt} {peel : NatPeel}
    {zeroChild succChild : CodeTrace} {after : PositionTrace}
    (matched : (CodeTrace.switchValue source block input entryValueCount
      sourceScrutinee true alternatives targetScrutinee generated outgoing
      children).switchNodeCapabilitiesMatch schemas positions = true)
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors (some peel))
    (zeroChildAt : children[constructors.size]? = some zeroChild)
    (succChildAt : children[constructors.size + 1]? = some succChild)
    (afterMember : after ∈ positions)
    (afterCoordinate : after.coordinateMatches succChild.source
      succChild.sourceBlock succChild.targetPosition succChild.sourceInputMap =
        true) :
    ∃ before, before ∈ positions ∧
      before.coordinateMatches source block .terminator input = true ∧
      natSuccChildCapabilities? input before.sourceCapabilities =
        some after.sourceCapabilities := by
  have matched' := matched
  simp only [CodeTrace.switchNodeCapabilitiesMatch, terminator, zeroChildAt,
    succChildAt, Bool.and_eq_true] at matched'
  have transition := CodeTrace.branchTransition_of_match positions
    matched'.2.2 afterMember afterCoordinate
  simpa [CodeTrace.source, CodeTrace.sourceBlock, CodeTrace.targetPosition,
    CodeTrace.sourceInputMap] using transition

private theorem codeTraceListSwitchCapabilitiesMatch_of_mem
    (schemas : Owned → CtorId → Option CtorSchema)
    (positions : List PositionTrace)
    {traces : List CodeTrace} {child : CodeTrace}
    (matched : codeTraceListSwitchCapabilitiesMatch schemas positions traces =
      true)
    (member : child ∈ traces) :
    child.switchCapabilitiesMatch schemas positions = true := by
  induction traces with
  | nil => simp at member
  | cons head tail ih =>
      simp only [codeTraceListSwitchCapabilitiesMatch,
        Bool.and_eq_true] at matched
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simpa [equal] using matched.1
      | inr member => exact ih matched.2 member

/-- Switch capability-flow coherence is inherited by every immediate
recursive compiler call. -/
theorem CodeTrace.switchCapabilitiesMatch_of_child
    (schemas : Owned → CtorId → Option CtorSchema)
    (positions : List PositionTrace) {parent child : CodeTrace}
    (matched : parent.switchCapabilitiesMatch schemas positions = true)
    (member : child ∈ parent.children) :
    child.switchCapabilitiesMatch schemas positions = true := by
  cases parent with
  | ret _ _ _ _ _ _ _ | tailCall _ _ _ _ _ _ _
  | tailCallSelf _ _ _ _ _ _ =>
      simp [CodeTrace.children] at member
  | letOp source block input nextInput entryValueCount operation index
      instruction next =>
      simp [CodeTrace.children] at member
      subst child
      exact matched
  | switchValue source block input entryValueCount sourceScrutinee peel
      alternatives targetScrutinee generated outgoing children =>
      simp only [CodeTrace.switchCapabilitiesMatch,
        Bool.and_eq_true] at matched
      exact codeTraceListSwitchCapabilitiesMatch_of_mem schemas positions
        matched.2 member

/-- Every recursive descendant inherits the checked switch capability-flow
audit. -/
theorem CodeTrace.Descendant.switchCapabilitiesMatch
    (schemas : Owned → CtorId → Option CtorSchema)
    (positions : List PositionTrace) {root child : CodeTrace}
    (descendant : Descendant root child)
    (matched : root.switchCapabilitiesMatch schemas positions = true) :
    child.switchCapabilitiesMatch schemas positions = true := by
  induction descendant with
  | refl => exact matched
  | @step parent child parentDescendant childMem ih =>
      exact CodeTrace.switchCapabilitiesMatch_of_child schemas positions ih
        childMem

/-- Project whole-program switch capability flow to one retained function. -/
theorem Trace.functionSwitchCapabilitiesMatch {trace : Trace}
    {schemas : Owned → CtorId → Option CtorSchema}
    (matched : trace.switchCapabilitiesMatch schemas = true)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ trace.functions) :
    functionTrace.root.switchCapabilitiesMatch schemas trace.positions = true :=
  List.all_eq_true.mp matched functionTrace member

/-- Every retained function derivation agrees with the checked constructor
schemas at its ordinary allocation nodes. -/
def Trace.allocationSchemasMatch (trace : Trace)
    (schemas : Owned → CtorId → Option CtorSchema) : Bool :=
  trace.functions.all fun functionTrace =>
    functionTrace.root.allocationSchemasMatch schemas

/-- Project whole-trace allocation-schema coherence to one retained function. -/
theorem Trace.functionAllocationSchemasMatch {trace : Trace}
    {schemas : Owned → CtorId → Option CtorSchema}
    (matched : trace.allocationSchemasMatch schemas = true)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ trace.functions) :
    functionTrace.root.allocationSchemasMatch schemas = true := by
  exact List.all_eq_true.mp matched functionTrace member

/-- Executable whole-program alignment of source declarations, emitted target
declarations, and retained function traces. Externs consume no trace; each
function consumes one exact owner/source/target trace; the sole remaining
trace must be the closed main. -/
def programTraceMatches :
    List (Address × IxIR1.Decl) → List (Address × Decl) →
      List FunctionTrace → IxIR1.FnDef → Function → Bool
  | [], [], [trace], mainSource, mainGenerated =>
      functionTraceMatches trace .main mainSource mainGenerated
  | (sourceAddress, .extern sourceArity) :: sourceRest,
      (targetAddress, .extern targetArity) :: targetRest,
      traces, mainSource, mainGenerated =>
      sourceAddress == targetAddress && sourceArity == targetArity &&
        programTraceMatches sourceRest targetRest traces mainSource mainGenerated
  | (sourceAddress, .fn sourceDefinition) :: sourceRest,
      (targetAddress, .fn targetDefinition) :: targetRest,
      trace :: traces, mainSource, mainGenerated =>
      sourceAddress == targetAddress &&
        functionTraceMatches trace (.declaration sourceAddress)
          sourceDefinition targetDefinition &&
        programTraceMatches sourceRest targetRest traces mainSource mainGenerated
  | _, _, _, _, _ => false

/-- Proof-facing declaration/trace alignment reflected from
`programTraceMatches`. -/
inductive ProgramTraceOrder (mainSource : IxIR1.FnDef)
    (mainGenerated : Function) :
    List (Address × IxIR1.Decl) → List (Address × Decl) →
      List FunctionTrace → Prop where
  | main {trace : FunctionTrace}
      (matched : FunctionTraceMatch trace .main mainSource mainGenerated) :
      ProgramTraceOrder mainSource mainGenerated [] [] [trace]
  | extern {address : Address} {arity : Nat}
      {sourceRest : List (Address × IxIR1.Decl)}
      {targetRest : List (Address × Decl)}
      {traces : List FunctionTrace}
      (rest : ProgramTraceOrder mainSource mainGenerated sourceRest targetRest
        traces) :
      ProgramTraceOrder mainSource mainGenerated
        ((address, .extern arity) :: sourceRest)
        ((address, .extern arity) :: targetRest) traces
  | function {address : Address} {sourceDefinition : IxIR1.FnDef}
      {targetDefinition : Function}
      {sourceRest : List (Address × IxIR1.Decl)}
      {targetRest : List (Address × Decl)}
      {trace : FunctionTrace} {traces : List FunctionTrace}
      (matched : FunctionTraceMatch trace (.declaration address)
        sourceDefinition targetDefinition)
      (rest : ProgramTraceOrder mainSource mainGenerated sourceRest targetRest
        traces) :
      ProgramTraceOrder mainSource mainGenerated
        ((address, .fn sourceDefinition) :: sourceRest)
        ((address, .fn targetDefinition) :: targetRest) (trace :: traces)

/-- Reflect the executable whole-program trace-order check. -/
theorem programTraceOrder_of_match
    {source : List (Address × IxIR1.Decl)}
    {target : List (Address × Decl)} {traces : List FunctionTrace}
    {mainSource : IxIR1.FnDef} {mainGenerated : Function}
    (matched : programTraceMatches source target traces mainSource
      mainGenerated = true) :
    ProgramTraceOrder mainSource mainGenerated source target traces := by
  induction source generalizing target traces with
  | nil =>
      cases target with
      | cons targetEntry targetRest =>
          simp [programTraceMatches] at matched
      | nil =>
          cases traces with
          | nil => simp [programTraceMatches] at matched
          | cons trace rest =>
              cases rest with
              | nil =>
                  exact .main (functionTraceMatch_of_match
                    (by simpa [programTraceMatches] using matched))
              | cons next tail => simp [programTraceMatches] at matched
  | cons sourceEntry sourceRest ih =>
      obtain ⟨sourceAddress, sourceDeclaration⟩ := sourceEntry
      cases target with
      | nil => simp [programTraceMatches] at matched
      | cons targetEntry targetRest =>
          obtain ⟨targetAddress, targetDeclaration⟩ := targetEntry
          cases sourceDeclaration with
          | extern sourceArity =>
              cases targetDeclaration with
              | fn targetDefinition =>
                  simp [programTraceMatches] at matched
              | extern targetArity =>
                  simp only [programTraceMatches, Bool.and_eq_true] at matched
                  have addressEq : sourceAddress = targetAddress :=
                    beq_iff_eq.mp matched.1.1
                  have arityEq : sourceArity = targetArity :=
                    beq_iff_eq.mp matched.1.2
                  subst targetAddress
                  subst targetArity
                  exact .extern (ih matched.2)
          | fn sourceDefinition =>
              cases targetDeclaration with
              | extern targetArity =>
                  simp [programTraceMatches] at matched
              | fn targetDefinition =>
                  cases traces with
                  | nil => simp [programTraceMatches] at matched
                  | cons trace rest =>
                      simp only [programTraceMatches, Bool.and_eq_true] at matched
                      have addressEq : sourceAddress = targetAddress :=
                        beq_iff_eq.mp matched.1.1
                      subst targetAddress
                      exact .function
                        (functionTraceMatch_of_match matched.1.2)
                        (ih matched.2)

/-- Every source function occurrence in a checked program order has the
corresponding emitted declaration and retained exact function trace. -/
theorem ProgramTraceOrder.function_exists_of_source_mem
    {mainSource : IxIR1.FnDef} {mainGenerated : Function}
    {source : List (Address × IxIR1.Decl)}
    {target : List (Address × Decl)} {traces : List FunctionTrace}
    (order : ProgramTraceOrder mainSource mainGenerated source target traces)
    {address : Address} {sourceDefinition : IxIR1.FnDef}
    (member : (address, .fn sourceDefinition) ∈ source) :
    ∃ targetDefinition trace,
      (address, .fn targetDefinition) ∈ target ∧
        trace ∈ traces ∧
        FunctionTraceMatch trace (.declaration address) sourceDefinition
          targetDefinition := by
  induction order with
  | main matched => simp at member
  | @extern headAddress arity sourceRest targetRest traces rest ih =>
      simp only [List.mem_cons] at member
      cases member with
      | inl equal => simp at equal
      | inr member =>
          obtain ⟨targetDefinition, trace, targetMember, traceMember,
            traceMatch⟩ := ih member
          exact ⟨targetDefinition, trace, List.mem_cons_of_mem _ targetMember,
            traceMember, traceMatch⟩
  | @function headAddress headSource headTarget sourceRest targetRest trace traces
      matched rest ih =>
      simp only [List.mem_cons] at member
      cases member with
      | inl equal =>
          cases equal
          exact ⟨headTarget, trace, by simp, by simp, matched⟩
      | inr member =>
          obtain ⟨targetDefinition, childTrace, targetMember, traceMember,
            traceMatch⟩ := ih member
          exact ⟨targetDefinition, childTrace,
            List.mem_cons_of_mem _ targetMember,
            List.mem_cons_of_mem _ traceMember, traceMatch⟩

/-- Source and target declaration lookup traverse the same checked order.
Consequently a source function selected by first-binding-wins lookup has the
exact emitted definition and retained trace selected at the corresponding
target address, even if the raw lists contain repeated keys. -/
theorem ProgramTraceOrder.function_exists_of_source_lookup
    {mainSource : IxIR1.FnDef} {mainGenerated : Function}
    {source : List (Address × IxIR1.Decl)}
    {target : List (Address × Decl)} {traces : List FunctionTrace}
    (order : ProgramTraceOrder mainSource mainGenerated source target traces)
    {address : Address} {sourceDefinition : IxIR1.FnDef}
    (lookup : IxIR1.Env.ofList source address =
      some (.fn sourceDefinition)) :
    ∃ targetDefinition trace,
      (target.find? fun entry => entry.1 == address).map (·.2) =
          some (.fn targetDefinition) ∧
        trace ∈ traces ∧
        FunctionTraceMatch trace (.declaration address) sourceDefinition
          targetDefinition := by
  induction order with
  | main matched =>
      simp [IxIR1.Env.ofList] at lookup
  | @extern headAddress arity sourceRest targetRest traces rest ih =>
      by_cases same : headAddress = address
      · subst address
        simp [IxIR1.Env.ofList] at lookup
      · have tailLookup : IxIR1.Env.ofList sourceRest address =
            some (.fn sourceDefinition) := by
          simpa [IxIR1.Env.ofList, same] using lookup
        obtain ⟨targetDefinition, trace, targetLookup, traceMember,
          traceMatch⟩ := ih tailLookup
        exact ⟨targetDefinition, trace, by simpa [same] using targetLookup,
          traceMember, traceMatch⟩
  | @function headAddress headSource headTarget sourceRest targetRest trace
      traces matched rest ih =>
      by_cases same : headAddress = address
      · subst address
        have sourceEq : headSource = sourceDefinition := by
          simpa [IxIR1.Env.ofList] using lookup
        subst sourceDefinition
        exact ⟨headTarget, trace, by simp, by simp, matched⟩
      · have tailLookup : IxIR1.Env.ofList sourceRest address =
            some (.fn sourceDefinition) := by
          simpa [IxIR1.Env.ofList, same] using lookup
        obtain ⟨targetDefinition, childTrace, targetLookup, traceMember,
          traceMatch⟩ := ih tailLookup
        exact ⟨targetDefinition, childTrace,
          by simpa [same] using targetLookup,
          List.mem_cons_of_mem _ traceMember, traceMatch⟩

/-- Symmetric lookup form of the declaration-order theorem. A target function
selected by first-binding-wins lookup comes from the exact source function and
retained trace at the same address; an extern entry can therefore never be
mistaken for a function in either direction. -/
theorem ProgramTraceOrder.function_exists_of_target_lookup
    {mainSource : IxIR1.FnDef} {mainGenerated : Function}
    {source : List (Address × IxIR1.Decl)}
    {target : List (Address × Decl)} {traces : List FunctionTrace}
    (order : ProgramTraceOrder mainSource mainGenerated source target traces)
    {address : Address} {targetDefinition : Function}
    (lookup : (target.find? fun entry => entry.1 == address).map (·.2) =
      some (.fn targetDefinition)) :
    ∃ sourceDefinition trace,
      IxIR1.Env.ofList source address = some (.fn sourceDefinition) ∧
        trace ∈ traces ∧
        FunctionTraceMatch trace (.declaration address) sourceDefinition
          targetDefinition := by
  induction order with
  | main matched => simp at lookup
  | @extern headAddress arity sourceRest targetRest traces rest ih =>
      by_cases same : headAddress = address
      · subst address
        simp at lookup
      · have tailLookup :
            (targetRest.find? fun entry => entry.1 == address).map (·.2) =
              some (.fn targetDefinition) := by
          simpa [same] using lookup
        obtain ⟨sourceDefinition, trace, sourceLookup, traceMember,
            traceMatch⟩ := ih tailLookup
        exact ⟨sourceDefinition, trace,
          by simpa [IxIR1.Env.ofList, same] using sourceLookup,
          traceMember, traceMatch⟩
  | @function headAddress headSource headTarget sourceRest targetRest trace
      traces matched rest ih =>
      by_cases same : headAddress = address
      · subst address
        have targetEq : headTarget = targetDefinition := by
          simpa using lookup
        subst targetDefinition
        exact ⟨headSource, trace, by simp [IxIR1.Env.ofList], by simp, matched⟩
      · have tailLookup :
            (targetRest.find? fun entry => entry.1 == address).map (·.2) =
              some (.fn targetDefinition) := by
          simpa [same] using lookup
        obtain ⟨sourceDefinition, childTrace, sourceLookup, traceMember,
            traceMatch⟩ := ih tailLookup
        exact ⟨sourceDefinition, childTrace,
          by simpa [IxIR1.Env.ofList, same] using sourceLookup,
          List.mem_cons_of_mem _ traceMember, traceMatch⟩

/-- A target extern selected by first-binding-wins lookup is the matching
source extern.  In particular, a checked function declaration cannot be
observed as an extern on only one side of the lowering boundary. -/
theorem ProgramTraceOrder.extern_of_target_lookup
    {mainSource : IxIR1.FnDef} {mainGenerated : Function}
    {source : List (Address × IxIR1.Decl)}
    {target : List (Address × Decl)} {traces : List FunctionTrace}
    (order : ProgramTraceOrder mainSource mainGenerated source target traces)
    {address : Address} {arity : Nat}
    (lookup : (target.find? fun entry => entry.1 == address).map (·.2) =
      some (.extern arity)) :
    IxIR1.Env.ofList source address = some (.extern arity) := by
  induction order with
  | main matched => simp at lookup
  | @extern headAddress headArity sourceRest targetRest traces rest ih =>
      by_cases same : headAddress = address
      · subst address
        have arityEq : headArity = arity := by simpa using lookup
        subst arity
        simp [IxIR1.Env.ofList]
      · have tailLookup :
            (targetRest.find? fun entry => entry.1 == address).map (·.2) =
              some (.extern arity) := by
          simpa [same] using lookup
        simpa [IxIR1.Env.ofList, same] using ih tailLookup
  | @function headAddress headSource headTarget sourceRest targetRest trace
      traces matched rest ih =>
      by_cases same : headAddress = address
      · subst address
        simp at lookup
      · have tailLookup :
            (targetRest.find? fun entry => entry.1 == address).map (·.2) =
              some (.extern arity) := by
          simpa [same] using lookup
        simpa [IxIR1.Env.ofList, same] using ih tailLookup

/-- A retained trace whose certified owner is `main` is the unique final main
entry of the whole-program declaration/trace alignment. -/
theorem ProgramTraceOrder.main_of_mem_owner
    {mainSource : IxIR1.FnDef} {mainGenerated : Function}
    {source : List (Address × IxIR1.Decl)}
    {target : List (Address × Decl)} {traces : List FunctionTrace}
    (order : ProgramTraceOrder mainSource mainGenerated source target traces)
    {trace : FunctionTrace}
    (member : trace ∈ traces) (owner : trace.owner = .main) :
    FunctionTraceMatch trace .main mainSource mainGenerated := by
  induction order with
  | main matched =>
      simp only [List.mem_singleton] at member
      subst trace
      exact matched
  | @extern address arity sourceRest targetRest traces rest ih =>
      exact ih member
  | @function address sourceDefinition targetDefinition sourceRest targetRest
      head traces matched rest ih =>
      simp only [List.mem_cons] at member
      cases member with
      | inl equal =>
          subst trace
          rw [matched.owner] at owner
          cases owner
      | inr member => exact ih member

structure Artifact where
  source : Input
  program : Program
  validationContext : Validate.Context
  trace : Trace
  mainTrace : FunctionTrace
  /-- The distinguished synthetic-main derivation is retained in the exact
  whole-program trace consumed by recursive simulation. -/
  mainTraceMember : mainTrace ∈ trace.functions
  mainTraceOrder : FunctionTraceMatch mainTrace .main source.mainDefinition
    program.main
  /-- Exact declaration/function-trace order, ending in the retained main. -/
  functionTraceOrder : programTraceMatches source.declarations
    program.declarations trace.functions source.mainDefinition program.main = true

namespace Artifact

/-- Proof-facing whole-program declaration/function-trace alignment. -/
theorem functionTraceOrderProof (artifact : Artifact) :
    ProgramTraceOrder artifact.source.mainDefinition artifact.program.main
      artifact.source.declarations artifact.program.declarations
      artifact.trace.functions :=
  programTraceOrder_of_match artifact.functionTraceOrder

/-- Resolve one retained source function occurrence to its emitted definition
and exact recursive trace. -/
theorem functionTrace_of_source_mem (artifact : Artifact)
    {address : Address} {sourceDefinition : IxIR1.FnDef}
    (member : (address, .fn sourceDefinition) ∈
      artifact.source.declarations) :
    ∃ targetDefinition trace,
      (address, .fn targetDefinition) ∈ artifact.program.declarations ∧
        trace ∈ artifact.trace.functions ∧
        FunctionTraceMatch trace (.declaration address) sourceDefinition
          targetDefinition :=
  artifact.functionTraceOrderProof.function_exists_of_source_mem member

/-- Lookup-facing form of `functionTrace_of_source_mem`, aligned with the
declaration function installed by `Eval.Context.ofProgram`. -/
theorem functionTrace_of_source_lookup (artifact : Artifact)
    {address : Address} {sourceDefinition : IxIR1.FnDef}
    (lookup : IxIR1.Env.ofList artifact.source.declarations address =
      some (.fn sourceDefinition)) :
    ∃ targetDefinition trace,
      (artifact.program.declarations.find? fun entry =>
        entry.1 == address).map (·.2) = some (.fn targetDefinition) ∧
      trace ∈ artifact.trace.functions ∧
      FunctionTraceMatch trace (.declaration address) sourceDefinition
        targetDefinition :=
  artifact.functionTraceOrderProof.function_exists_of_source_lookup lookup

/-- Lookup-facing inverse of `functionTrace_of_source_lookup`, used by
forward target execution proofs to recover the exact retained source callee. -/
theorem functionTrace_of_target_lookup (artifact : Artifact)
    {address : Address} {targetDefinition : Function}
    (lookup : (artifact.program.declarations.find? fun entry =>
      entry.1 == address).map (·.2) = some (.fn targetDefinition)) :
    ∃ sourceDefinition trace,
      IxIR1.Env.ofList artifact.source.declarations address =
          some (.fn sourceDefinition) ∧
        trace ∈ artifact.trace.functions ∧
        FunctionTraceMatch trace (.declaration address) sourceDefinition
          targetDefinition :=
  artifact.functionTraceOrderProof.function_exists_of_target_lookup lookup

/-- Resolve a target extern lookup to the exact source extern selected at the
same address. -/
theorem sourceExtern_of_target_lookup (artifact : Artifact)
    {address : Address} {arity : Nat}
    (lookup : (artifact.program.declarations.find? fun entry =>
      entry.1 == address).map (·.2) = some (.extern arity)) :
    IxIR1.Env.ofList artifact.source.declarations address =
      some (.extern arity) :=
  artifact.functionTraceOrderProof.extern_of_target_lookup lookup

/-- The distinguished trace is the source main's trace. -/
theorem mainOwner (artifact : Artifact) :
    artifact.mainTrace.owner = .main :=
  artifact.mainTraceOrder.owner

/-- The distinguished trace retains the exact synthetic source main. -/
theorem mainSource (artifact : Artifact) :
    artifact.mainTrace.source = artifact.source.mainDefinition :=
  artifact.mainTraceOrder.source

/-- The distinguished trace generated the target program's actual main. -/
theorem mainGenerated (artifact : Artifact) :
    artifact.mainTrace.generated = artifact.program.main :=
  artifact.mainTraceOrder.generated

/-- The emitted main remains closed. -/
theorem mainArity (artifact : Artifact) :
    artifact.program.main.signature.params.size = 0 := by
  have arity := artifact.mainTrace.sourceArity
  rw [artifact.mainGenerated, artifact.mainSource] at arity
  simpa [Input.mainDefinition] using arity

/-- The recursive main derivation reconstructs the literal input main code. -/
theorem mainRootSourceCode (artifact : Artifact) :
    artifact.mainTrace.root.sourceCode = artifact.source.main := by
  rw [artifact.mainTrace.rootSourceCode, artifact.mainSource]
  rfl

/-- A closed source main starts with the empty source-slot map. -/
theorem mainEntryInput (artifact : Artifact) :
    artifact.mainTrace.root.sourceInputMap = #[] := by
  rw [artifact.mainTrace.entryInput, artifact.mainSource]
  simp [Input.mainDefinition, entryInputMap]

/-- The trace's completed root block is the actual block-zero entry of the
emitted target main. -/
theorem mainHeadBlockAt (artifact : Artifact) :
    artifact.program.main.blocks[0]? =
      some artifact.mainTrace.root.headBlock.2 := by
  have blockAt := artifact.mainTrace.headBlockAt
  rw [artifact.mainGenerated, artifact.mainTrace.rootHeadBlock] at blockAt
  exact blockAt

/-- The retained entry-block witness discharges the evaluator's nonempty-main
entry check. -/
theorem mainNonempty (artifact : Artifact) :
    artifact.program.main.blocks.isEmpty = false := by
  have found := artifact.mainHeadBlockAt
  obtain ⟨bound, _⟩ := Array.getElem?_eq_some_iff.mp found
  simpa [Array.isEmpty] using (Nat.ne_of_gt bound)

end Artifact

/-- A successful lower-and-check result retains the exact validator equation,
so later simulation files never need to trust a Boolean acceptance claim. -/
structure Checked where
  artifact : Artifact
  stats : Validate.Stats
  accepted : Validate.validate artifact.validationContext artifact.program =
    .ok stats
  /-- The emitted baseline contains no credit operations. This checked
  syntactic inventory supports exact interpretation independence. -/
  creditFree : CreditFree.program artifact.program = true
  /-- Every recursive derivation node is represented by a flat producer
  position with the exact source/block/target coordinate and input-map
  capability shape. -/
  positionCoordinates : artifact.trace.positionsMatch = true
  /-- Every live source slot that names an inherited target block parameter
  carries exactly that parameter's declared ownership capability. -/
  parameterCapabilities : artifact.trace.parameterCapabilitiesMatch = true
  /-- Every retained `pure` node has the producer's exact move/copy/consume
  transition between its current and continuation capability vectors. -/
  pureCapabilities : artifact.trace.pureCapabilitiesMatch = true
  /-- Every retained `dup` node has the producer's exact scalar-copy or
  shared-owner retention transition. -/
  dupCapabilities : artifact.trace.dupCapabilitiesMatch = true
  /-- Every retained `fetch` node borrows in the source constructor world and
  retains the producer's exact lender. -/
  fetchCapabilities : artifact.trace.fetchCapabilitiesMatch = true
  /-- Every retained shallow/deep destruction node consumes its exact owner,
  retires rooted loans, and binds the erased scalar result. -/
  destructionCapabilities :
    artifact.trace.destructionCapabilitiesMatch = true
  /-- The post-validation semantic projection used by allocation simulation:
  every retained source allocation has the exact uniform target schema. -/
  allocationSchemas : artifact.trace.allocationSchemasMatch
    artifact.validationContext.schemas = true
  /-- Every retained constructor or function-PAP allocation is paired with
  the producer's exact pre-operation capability vector and exact sequential
  consume-and-bind continuation, checked against its recursive input map and
  owned operand world. -/
  allocationCapabilities : artifact.trace.allocationCapabilitiesMatch = true
  /-- Every allocation immediately followed by a recursive self tail call is
  reached only after the producer has retired all outstanding borrows. -/
  terminalAllocationNoBorrows :
    artifact.trace.terminalAllocationNoBorrows = true
  /-- Every retained dynamic application consumes its function operand and
  supplied arguments at the shared boundary, then binds one shared result
  owner. -/
  applyCapabilities : artifact.trace.applyCapabilitiesMatch = true
  /-- Every PAP-safe retained function has the canonical all-owned/shared
  entry capability vector used by dynamic exact and over-saturation. -/
  sharedPapEntryCapabilities :
    artifact.trace.sharedPapEntryCapabilitiesMatch = true
  /-- Every switch edge rebases local lenders exactly; constructor children
  prepend schema-world field borrows and Nat-successor children shift lenders
  across their implicit scalar parameter. -/
  switchCapabilities : artifact.trace.switchCapabilitiesMatch
    artifact.validationContext.schemas = true
  /-- Function entries, ordinary and tail calls, and returns implement the
  exact baseline ownership-transfer ABI. -/
  callCapabilities : artifact.trace.callCapabilitiesMatch
    artifact.program.declarations = true

namespace Checked

/-- Every returned checked artifact satisfies the public bounded-validity
predicate by construction. -/
theorem valid (checked : Checked) :
    Validate.Valid checked.artifact.validationContext checked.artifact.program :=
  ⟨checked.stats, checked.accepted⟩

/-- Recover the borrow-free producer vector at a terminal allocation node. -/
theorem terminalAllocationPositionNoBorrows (checked : Checked)
    {functionTrace : FunctionTrace}
    (functionMember : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {world : Owned} {identity : CtorId} {arguments : Array IxIR1.Atom}
    {index : Nat} {instruction : Instr}
    {tailSource : SourceSite} {tailBlock : BlockId}
    {tailInput : Array (Option Atom)} {tailEntryValueCount : Nat}
    {tailArguments : Array IxIR1.Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.letOp source block input nextInput entryValueCount
        (.alloc world identity arguments) index instruction
          (.tailCallSelf tailSource tailBlock tailInput tailEntryValueCount
            tailArguments generated)))
    {position : PositionTrace}
    (positionMember : position ∈ checked.artifact.trace.positions)
    (coordinate : position.coordinateMatches source block
      (.instruction index) input = true) :
    noBorrows position.sourceCapabilities = true := by
  have rootMatch := checked.artifact.trace.functionTerminalAllocationNoBorrows
    checked.terminalAllocationNoBorrows functionMember
  have localMatch := descendant.terminalAllocationNoBorrows
    checked.artifact.trace.positions rootMatch
  exact CodeTrace.terminalAllocationPositionNoBorrows_of_match
    checked.artifact.trace.positions localMatch positionMember coordinate

/-- Recover the exact flat producer position for any recursive trace node in
a retained function. -/
theorem position (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {trace : CodeTrace}
    (descendant : functionTrace.root.Descendant trace) :
    ∃ position, position ∈ checked.artifact.trace.positions ∧
      position.coordinateMatches trace.source trace.sourceBlock
        trace.targetPosition trace.sourceInputMap = true := by
  have rootMatch := Trace.functionPositionsMatch
    checked.positionCoordinates member
  exact CodeTrace.position_of_positionsMatch checked.artifact.trace.positions
    (descendant.positionsMatch checked.artifact.trace.positions rootMatch)

/-- Recover the exact producer owner behind an inherited owned target
parameter at any retained recursive trace node. -/
theorem ownedParameterCapability (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {trace : CodeTrace}
    (descendant : functionTrace.root.Descendant trace)
    {position : PositionTrace}
    (positionMember : position ∈ checked.artifact.trace.positions)
    (coordinate : position.coordinateMatches trace.source trace.sourceBlock
      trace.targetPosition trace.sourceInputMap = true)
    {sourceIndex targetIndex : Nat} {world : Owned}
    (inputAt : trace.sourceInputMap[sourceIndex]? =
      some (some (.reg targetIndex)))
    (parameterAt : trace.headBlock.2.valueParams[targetIndex]? =
      some (.owned world)) :
    position.sourceCapabilities[sourceIndex]? = some (.owned world) := by
  have rootMatch := Trace.functionParameterCapabilitiesMatch
    checked.parameterCapabilities member
  have localMatch := descendant.parameterCapabilitiesMatch
    checked.artifact.trace.positions rootMatch
  have positionMatch := trace.positionParameterCapabilities_of_match
    checked.artifact.trace.positions localMatch positionMember coordinate
  exact position.owned_of_parameterCapabilitiesMatch positionMatch inputAt
    parameterAt

/-- Recover the producer capability corresponding to any inherited target
block parameter.  The reflected `matchesParameter` equation retains the exact
scalar/owned/borrowed kind and excludes a consumed source binding. -/
theorem parameterCapability (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {trace : CodeTrace}
    (descendant : functionTrace.root.Descendant trace)
    {position : PositionTrace}
    (positionMember : position ∈ checked.artifact.trace.positions)
    (coordinate : position.coordinateMatches trace.source trace.sourceBlock
      trace.targetPosition trace.sourceInputMap = true)
    {sourceIndex targetIndex : Nat} {parameter : ValueCap}
    (inputAt : trace.sourceInputMap[sourceIndex]? =
      some (some (.reg targetIndex)))
    (parameterAt : trace.headBlock.2.valueParams[targetIndex]? =
      some parameter) :
    ∃ capability,
      position.sourceCapabilities[sourceIndex]? = some capability ∧
        capability.matchesParameter parameter = true := by
  have rootMatch := Trace.functionParameterCapabilitiesMatch
    checked.parameterCapabilities member
  have localMatch := descendant.parameterCapabilitiesMatch
    checked.artifact.trace.positions rootMatch
  have positionMatch := trace.positionParameterCapabilities_of_match
    checked.artifact.trace.positions localMatch positionMember coordinate
  exact position.capability_of_parameterCapabilitiesMatch positionMatch inputAt
    parameterAt

/-- Recover the local switch capability audit at any retained switch node. -/
theorem switchNodeCapabilities (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List EdgeTrace}
    {children : List CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue source block input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children)) :
    (CodeTrace.switchValue source block input entryValueCount sourceScrutinee
      peelNat alternatives targetScrutinee generated outgoing children
        ).switchNodeCapabilitiesMatch
          checked.artifact.validationContext.schemas
          checked.artifact.trace.positions = true := by
  have rootMatch := Trace.functionSwitchCapabilitiesMatch
    checked.switchCapabilities member
  have nodeMatch := descendant.switchCapabilitiesMatch
    checked.artifact.validationContext.schemas
    checked.artifact.trace.positions rootMatch
  change ((CodeTrace.switchValue source block input entryValueCount
    sourceScrutinee peelNat alternatives targetScrutinee generated outgoing
    children).switchNodeCapabilitiesMatch
      checked.artifact.validationContext.schemas
      checked.artifact.trace.positions &&
    codeTraceListSwitchCapabilitiesMatch
      checked.artifact.validationContext.schemas
      checked.artifact.trace.positions children) = true at nodeMatch
  simp only [Bool.and_eq_true] at nodeMatch
  exact nodeMatch.1

/-- Recover the exact constructor-child capability transition at a checked
switch ordinal. -/
theorem constructorBranchTransition (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List EdgeTrace}
    {children : List CodeTrace} {constructors : Array CtorAlt}
    {natPeel : Option NatPeel} {index : Nat} {target : CtorAlt}
    {child : CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue source block input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children))
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors natPeel)
    (targetAt : constructors[index]? = some target)
    (childAt : children[index]? = some child)
    {after : PositionTrace}
    (afterMember : after ∈ checked.artifact.trace.positions)
    (afterCoordinate : after.coordinateMatches child.source child.sourceBlock
      child.targetPosition child.sourceInputMap = true) :
    ∃ before, before ∈ checked.artifact.trace.positions ∧
      before.coordinateMatches source block .terminator input = true ∧
      constructorChildCapabilities?
        checked.artifact.validationContext.schemas input sourceScrutinee
          target.cid before.sourceCapabilities =
        some after.sourceCapabilities := by
  exact CodeTrace.constructorBranchTransition_of_switch_match
    checked.artifact.validationContext.schemas
    checked.artifact.trace.positions
    (checked.switchNodeCapabilities member descendant) terminator targetAt
      childAt afterMember afterCoordinate

/-- A checked constructor-child transition fixes the selected schema arity.
The child coordinate counts both the edge-rebased source vector and every
borrowed constructor field, so comparison with the source alternative is
exact rather than merely a lower bound from the generated fetch prologue. -/
theorem constructorBranchSchemaArity
    (checked : Checked) {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {site : SourceSite} {blockId : BlockId} {input : Array (Option Atom)}
    {entryValueCount : Nat} {sourceScrutinee : IxIR1.Atom}
    {peelNat : Bool} {alternatives : Array IxIR1.Alt}
    {targetScrutinee : Atom} {generated : Block}
    {outgoing : List EdgeTrace} {children : List CodeTrace}
    {constructors : Array CtorAlt} {targetPeel : Option NatPeel}
    {index : Nat} {target : CtorAlt} {edge : EdgeTrace}
    {child : CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children))
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors targetPeel)
    (targetAt : constructors[index]? = some target)
    (childAt : children[index]? = some child)
    (branch : ConstructorBranchMatch site blockId input sourceScrutinee
      alternatives target edge child) :
    ∃ world schema,
      checked.artifact.validationContext.schemas world target.cid =
          some schema ∧
        schema.fields.size = branch.fieldCount := by
  have childMember : child ∈ children := List.mem_of_getElem? childAt
  have childDescendant : functionTrace.root.Descendant child :=
    .step descendant childMember
  obtain ⟨after, afterMember, afterCoordinate⟩ :=
    checked.position member childDescendant
  obtain ⟨before, _beforeMember, beforeCoordinate, transition⟩ :=
    checked.constructorBranchTransition member descendant terminator targetAt
      childAt afterMember afterCoordinate
  have beforeSize : before.sourceCapabilities.size = input.size :=
    before.sourceCapabilities_size_of_coordinateMatch beforeCoordinate
  have afterSize : after.sourceCapabilities.size = child.sourceInputMap.size :=
    after.sourceCapabilities_size_of_coordinateMatch afterCoordinate
  have childSize : child.sourceInputMap.size =
      branch.fieldCount + input.size := by
    rw [branch.childInput]
    simp [constructorChildInputMap, EdgeTrace.explicitMapOf,
      branch.edgeSourceInput]
  unfold constructorChildCapabilities? at transition
  cases rebasedEq : edgeCapabilities? before.sourceCapabilities input with
  | none => simp [rebasedEq] at transition
  | some rebased =>
      simp only [rebasedEq] at transition
      cases sourceScrutinee with
      | lit literal => simp at transition
      | erased => simp at transition
      | var sourceIndex =>
          cases capabilityEq : rebased[sourceIndex]? with
          | none => simp [capabilityEq] at transition
          | some capability =>
              cases capability with
              | scalar => simp [capabilityEq] at transition
              | dead => simp [capabilityEq] at transition
              | owned world =>
                  cases schemaEq : checked.artifact.validationContext.schemas
                      world target.cid with
                  | none => simp [capabilityEq, schemaEq] at transition
                  | some schema =>
                      simp only [capabilityEq, schemaEq] at transition
                      injection transition with afterEq
                      have rebasedSize : rebased.size =
                          before.sourceCapabilities.size :=
                        edgeCapabilities?_size rebasedEq
                      refine ⟨world, schema, schemaEq, ?_⟩
                      have sizeEq := congrArg Array.size afterEq
                      simp only [Array.size_append, Array.size_reverse,
                        Array.size_map] at sizeEq
                      omega
              | borrowed world lender =>
                  cases schemaEq : checked.artifact.validationContext.schemas
                      world target.cid with
                  | none => simp [capabilityEq, schemaEq] at transition
                  | some schema =>
                      simp only [capabilityEq, schemaEq] at transition
                      injection transition with afterEq
                      have rebasedSize : rebased.size =
                          before.sourceCapabilities.size :=
                        edgeCapabilities?_size rebasedEq
                      refine ⟨world, schema, schemaEq, ?_⟩
                      have sizeEq := congrArg Array.size afterEq
                      simp only [Array.size_append, Array.size_reverse,
                        Array.size_map] at sizeEq
                      omega

/-- Recover the exact literal-zero child capability transition. -/
theorem natZeroBranchTransition (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {targetScrutinee : Atom} {generated : Block}
    {outgoing : List EdgeTrace} {children : List CodeTrace}
    {constructors : Array CtorAlt} {peel : NatPeel}
    {zeroChild succChild : CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue source block input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children))
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors (some peel))
    (zeroChildAt : children[constructors.size]? = some zeroChild)
    (succChildAt : children[constructors.size + 1]? = some succChild)
    {after : PositionTrace}
    (afterMember : after ∈ checked.artifact.trace.positions)
    (afterCoordinate : after.coordinateMatches zeroChild.source
      zeroChild.sourceBlock zeroChild.targetPosition zeroChild.sourceInputMap =
        true) :
    ∃ before, before ∈ checked.artifact.trace.positions ∧
      before.coordinateMatches source block .terminator input = true ∧
      natZeroChildCapabilities? input before.sourceCapabilities =
        some after.sourceCapabilities := by
  exact CodeTrace.natZeroBranchTransition_of_switch_match
    checked.artifact.validationContext.schemas
    checked.artifact.trace.positions
    (checked.switchNodeCapabilities member descendant) terminator zeroChildAt
      succChildAt afterMember afterCoordinate

/-- Recover the exact literal-successor child capability transition. -/
theorem natSuccBranchTransition (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {targetScrutinee : Atom} {generated : Block}
    {outgoing : List EdgeTrace} {children : List CodeTrace}
    {constructors : Array CtorAlt} {peel : NatPeel}
    {zeroChild succChild : CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue source block input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children))
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors (some peel))
    (zeroChildAt : children[constructors.size]? = some zeroChild)
    (succChildAt : children[constructors.size + 1]? = some succChild)
    {after : PositionTrace}
    (afterMember : after ∈ checked.artifact.trace.positions)
    (afterCoordinate : after.coordinateMatches succChild.source
      succChild.sourceBlock succChild.targetPosition succChild.sourceInputMap =
        true) :
    ∃ before, before ∈ checked.artifact.trace.positions ∧
      before.coordinateMatches source block .terminator input = true ∧
      natSuccChildCapabilities? input before.sourceCapabilities =
        some after.sourceCapabilities := by
  exact CodeTrace.natSuccBranchTransition_of_switch_match
    checked.artifact.validationContext.schemas
    checked.artifact.trace.positions
    (checked.switchNodeCapabilities member descendant) terminator zeroChildAt
      succChildAt afterMember afterCoordinate

/-- Recover the producer capability predecessor of any matching continuation
position at a retained `pure`/`move` node. -/
theorem pureTransition (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {index : Nat} {targetAtom : Atom}
    {next : CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp source block input nextInput entryValueCount
        (.pure sourceAtom) index (.move targetAtom) next))
    {after : PositionTrace}
    (afterMember : after ∈ checked.artifact.trace.positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    ∃ before, before ∈ checked.artifact.trace.positions ∧
      before.coordinateMatches source block (.instruction index) input = true ∧
      before.moveMatches after input sourceAtom = true := by
  have rootMatch := Trace.functionPureCapabilitiesMatch
    checked.pureCapabilities member
  exact CodeTrace.pureTransition_of_match checked.artifact.trace.positions
    (descendant.pureCapabilitiesMatch checked.artifact.trace.positions
      rootMatch) afterMember afterCoordinate

/-- Recover the producer capability predecessor of any matching continuation
position at a retained `dup`/`retainShared` node. -/
theorem dupTransition (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {index : Nat} {targetAtom : Atom}
    {next : CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp source block input nextInput entryValueCount
        (.dup sourceAtom) index (.retainShared targetAtom) next))
    {after : PositionTrace}
    (afterMember : after ∈ checked.artifact.trace.positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    ∃ before, before ∈ checked.artifact.trace.positions ∧
      before.coordinateMatches source block (.instruction index) input = true ∧
      before.dupMatches after sourceAtom = true := by
  have rootMatch := Trace.functionDupCapabilitiesMatch
    checked.dupCapabilities member
  exact CodeTrace.dupTransition_of_match checked.artifact.trace.positions
    (descendant.dupCapabilitiesMatch checked.artifact.trace.positions
      rootMatch) afterMember afterCoordinate

/-- Recover the producer capability predecessor of any matching continuation
position at a retained `fetch` node. -/
theorem fetchTransition (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {sourceField index : Nat}
    {targetAtom : Atom} {targetCid : CtorId} {targetField : Nat}
    {next : CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp source block input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
          (.fetch targetAtom targetCid targetField) next))
    {after : PositionTrace}
    (afterMember : after ∈ checked.artifact.trace.positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    ∃ before, before ∈ checked.artifact.trace.positions ∧
      before.coordinateMatches source block (.instruction index) input = true ∧
      before.fetchMatches after sourceAtom targetAtom = true := by
  have rootMatch := Trace.functionFetchCapabilitiesMatch
    checked.fetchCapabilities member
  exact CodeTrace.fetchTransition_of_match checked.artifact.trace.positions
    (descendant.fetchCapabilitiesMatch checked.artifact.trace.positions
      rootMatch) afterMember afterCoordinate

/-- Recover the exact consume/loan-retirement/scalar-bind transition at any
retained destruction node. -/
theorem destructionTransition (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {sourceSite : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {operation : IxIR1.Op} {world : Owned} {sourceAtom : IxIR1.Atom}
    {index : Nat} {instruction : Instr} {next : CodeTrace}
    (operationMatch : destructionSpec? operation = some (world, sourceAtom))
    (descendant : functionTrace.root.Descendant
      (.letOp sourceSite block input nextInput entryValueCount operation index
        instruction next))
    {after : PositionTrace}
    (afterMember : after ∈ checked.artifact.trace.positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    ∃ before, before ∈ checked.artifact.trace.positions ∧
      before.coordinateMatches sourceSite block (.instruction index) input =
        true ∧
      before.destructionResultMatches after input world sourceAtom = true := by
  have rootMatch := Trace.functionDestructionCapabilitiesMatch
    checked.destructionCapabilities member
  exact CodeTrace.destructionTransition_of_match
    checked.artifact.trace.positions operationMatch
      (descendant.destructionCapabilitiesMatch
        checked.artifact.trace.positions rootMatch)
      afterMember afterCoordinate

/-- Recover the exact checked schema at any retained ordinary allocation in a
function trace belonging to this artifact. -/
theorem allocationSchema (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {world : Owned} {identity : CtorId}
    {arguments : Array IxIR1.Atom} {index : Nat}
    {instruction : Instr} {next : CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp source block input nextInput entryValueCount
        (.alloc world identity arguments) index instruction next)) :
    ∃ schema,
      checked.artifact.validationContext.schemas world identity = some schema ∧
      schema.fields = Array.replicate arguments.size world := by
  have rootMatch := checked.artifact.trace.functionAllocationSchemasMatch
    checked.allocationSchemas member
  exact CodeTrace.allocationSchema_of_match
    checked.artifact.validationContext.schemas
      (descendant.allocationSchemasMatch
        checked.artifact.validationContext.schemas rootMatch)

/-- Recover the producer capability position at any retained allocation. -/
theorem allocationPosition (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {world : Owned} {identity : CtorId}
    {arguments : Array IxIR1.Atom} {index : Nat}
    {instruction : Instr} {next : CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp source block input nextInput entryValueCount
        (.alloc world identity arguments) index instruction next)) :
    ∃ position, position ∈ checked.artifact.trace.positions ∧
      position.allocationMatches source block index input world arguments =
        true := by
  have rootMatch := Trace.functionAllocationCapabilitiesMatch
    checked.allocationCapabilities member
  exact CodeTrace.allocationPosition_of_capabilities_match
    checked.artifact.trace.positions
      (descendant.allocationCapabilitiesMatch
        checked.artifact.trace.positions rootMatch)

/-- Recover the exact sequential consume-and-bind transition at any retained
ordinary allocation. -/
theorem allocationTransition (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {world : Owned} {identity : CtorId}
    {arguments : Array IxIR1.Atom} {index : Nat}
    {instruction : Instr} {next : CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp source block input nextInput entryValueCount
        (.alloc world identity arguments) index instruction next))
    {after : PositionTrace}
    (afterMember : after ∈ checked.artifact.trace.positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    ∃ before, before ∈ checked.artifact.trace.positions ∧
      before.coordinateMatches source block (.instruction index) input = true ∧
      before.allocationResultMatches after input world arguments = true := by
  have rootMatch := Trace.functionAllocationCapabilitiesMatch
    checked.allocationCapabilities member
  exact CodeTrace.allocationTransition_of_capabilities_match
    checked.artifact.trace.positions
      (descendant.allocationCapabilitiesMatch
        checked.artifact.trace.positions rootMatch)
      afterMember afterCoordinate

/-- Recover the exact shared capture consumption and fresh-owner transition at
any retained function partial application. -/
theorem pappTransition (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {address : Address} {arguments : Array IxIR1.Atom} {index : Nat}
    {instruction : Instr} {next : CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp source block input nextInput entryValueCount
        (.papp address arguments) index instruction next))
    {after : PositionTrace}
    (afterMember : after ∈ checked.artifact.trace.positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    ∃ before, before ∈ checked.artifact.trace.positions ∧
      before.coordinateMatches source block (.instruction index) input = true ∧
      before.allocationResultMatches after input .shared arguments = true := by
  have rootMatch := Trace.functionAllocationCapabilitiesMatch
    checked.allocationCapabilities member
  exact CodeTrace.pappTransition_of_capabilities_match
    checked.artifact.trace.positions
      (descendant.allocationCapabilitiesMatch
        checked.artifact.trace.positions rootMatch)
      afterMember afterCoordinate

/-- Recover the exact shared function/argument consumption and shared-result
binding transition at any retained dynamic application. -/
theorem applyTransition (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {function : IxIR1.Atom} {arguments : Array IxIR1.Atom} {index : Nat}
    {instruction : Instr} {next : CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp source block input nextInput entryValueCount
        (.apply function arguments) index instruction next))
    {after : PositionTrace}
    (afterMember : after ∈ checked.artifact.trace.positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    ∃ before, before ∈ checked.artifact.trace.positions ∧
      before.coordinateMatches source block (.instruction index) input = true ∧
      before.applyResultMatches after input function arguments = true := by
  have rootMatch := Trace.functionApplyCapabilitiesMatch
    checked.applyCapabilities member
  exact CodeTrace.applyTransition_of_capabilities_match
    checked.artifact.trace.positions
      (descendant.applyCapabilitiesMatch checked.artifact.trace.positions
        rootMatch)
      afterMember afterCoordinate

/-- A caller-selected schema lookup at a retained allocation is necessarily
the exact uniform schema certified by the checked compiler trace. -/
theorem allocationSchemaFields (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {world : Owned} {identity : CtorId}
    {arguments : Array IxIR1.Atom} {index : Nat}
    {instruction : Instr} {next : CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp source block input nextInput entryValueCount
        (.alloc world identity arguments) index instruction next))
    {schema : CtorSchema}
    (schemaAt : checked.artifact.validationContext.schemas world identity =
      some schema) :
    schema.fields = Array.replicate arguments.size world := by
  obtain ⟨found, foundAt, fields⟩ := checked.allocationSchema member descendant
  have equal : found = schema := Option.some.inj (foundAt.symm.trans schemaAt)
  simpa [equal] using fields

/-- Recover the complete call/return capability audit for one retained
function. -/
theorem functionCallCapabilitiesMatch (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions) :
    functionTrace.callCapabilitiesMatch checked.artifact.trace.positions
      checked.artifact.program.declarations = true :=
  checked.artifact.trace.functionCallCapabilitiesMatch
    checked.callCapabilities member

/-- Recover the canonical capability vector at any retained function root. -/
theorem entryCapabilities (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {position : PositionTrace}
    (positionMember : position ∈ checked.artifact.trace.positions)
    (coordinate : position.coordinateMatches functionTrace.root.source
      functionTrace.root.sourceBlock functionTrace.root.targetPosition
      functionTrace.root.sourceInputMap = true) :
    position.sourceCapabilities =
      Lower.entryCapabilities functionTrace.generated.signature := by
  exact FunctionTrace.entryCapabilities_of_call_match
    (checked.functionCallCapabilitiesMatch member) positionMember coordinate

/-- PAP safety in a checked artifact exposes the exact all-owned/shared
capability vector expected at the dynamically selected callee root. -/
theorem papSafeEntryCapabilities (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    (papSafe : functionTrace.generated.signature.papSafe = true) :
    Lower.entryCapabilities functionTrace.generated.signature =
      Array.replicate functionTrace.generated.signature.params.size
        (.owned .shared) := by
  have point := checked.artifact.trace.functionSharedPapEntryCapabilitiesMatch
    checked.sharedPapEntryCapabilities member
  unfold FunctionTrace.sharedPapEntryCapabilitiesMatch at point
  rw [papSafe] at point
  exact beq_iff_eq.mp point

/-- A retained declaration trace exposes the exact signature used by checked
addressed calls. -/
theorem targetSignature (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {address : Address} (owner : functionTrace.owner = .declaration address) :
    targetSignature? checked.artifact.program.declarations address =
      some functionTrace.generated.signature :=
  checked.artifact.trace.targetSignature_of_call_match
    checked.callCapabilities member owner

/-- Recover an addressed ordinary call's exact consume/suspend/result-bind
transition. -/
theorem callTransition (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {address : Address} {signature : Signature}
    {arguments : Array IxIR1.Atom} {index : Nat} {instruction : Instr}
    {next : CodeTrace} {before : PositionTrace}
    (signatureAt : targetSignature? checked.artifact.program.declarations
      address = some signature)
    (descendant : functionTrace.root.Descendant
      (.letOp source block input nextInput entryValueCount
        (.call address arguments) index instruction next))
    (beforeMember : before ∈ checked.artifact.trace.positions)
    (beforeCoordinate : before.coordinateMatches source block
      (.instruction index) input = true)
    {after : PositionTrace}
    (afterMember : after ∈ checked.artifact.trace.positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    before.callResultMatches after input signature arguments = true := by
  have rootMatch := checked.functionCallCapabilitiesMatch member
  simp only [FunctionTrace.callCapabilitiesMatch,
    Bool.and_eq_true] at rootMatch
  exact CodeTrace.callTransition_of_capabilities_match
    checked.artifact.trace.positions checked.artifact.program.declarations
      functionTrace.generated.signature signatureAt
      (descendant.callCapabilitiesMatch checked.artifact.trace.positions
        checked.artifact.program.declarations
        functionTrace.generated.signature rootMatch.2)
      beforeMember beforeCoordinate afterMember afterCoordinate

/-- Recover a self call's exact consume/suspend/result-bind transition. -/
theorem callSelfTransition (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input nextInput : Array (Option Atom)} {entryValueCount : Nat}
    {arguments : Array IxIR1.Atom} {index : Nat} {instruction : Instr}
    {next : CodeTrace} {before : PositionTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp source block input nextInput entryValueCount
        (.callSelf arguments) index instruction next))
    (beforeMember : before ∈ checked.artifact.trace.positions)
    (beforeCoordinate : before.coordinateMatches source block
      (.instruction index) input = true)
    {after : PositionTrace}
    (afterMember : after ∈ checked.artifact.trace.positions)
    (afterCoordinate : after.coordinateMatches next.source next.sourceBlock
      next.targetPosition next.sourceInputMap = true) :
    before.callResultMatches after input
      functionTrace.generated.signature arguments = true := by
  have rootMatch := checked.functionCallCapabilitiesMatch member
  simp only [FunctionTrace.callCapabilitiesMatch,
    Bool.and_eq_true] at rootMatch
  exact CodeTrace.callSelfTransition_of_capabilities_match
    checked.artifact.trace.positions checked.artifact.program.declarations
      functionTrace.generated.signature
      (descendant.callCapabilitiesMatch checked.artifact.trace.positions
        checked.artifact.program.declarations
        functionTrace.generated.signature rootMatch.2)
      beforeMember beforeCoordinate afterMember afterCoordinate

/-- Recover an addressed tail call's exact all-local-owner transfer. -/
theorem tailCallPosition (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {address : Address} {signature : Signature}
    {arguments : Array IxIR1.Atom} {generated : Block}
    (signatureAt : targetSignature? checked.artifact.program.declarations
      address = some signature)
    (descendant : functionTrace.root.Descendant
      (.tailCall source block input entryValueCount address arguments generated)) :
    ∃ position, position ∈ checked.artifact.trace.positions ∧
      position.tailCallMatches source block input signature arguments = true := by
  have rootMatch := checked.functionCallCapabilitiesMatch member
  simp only [FunctionTrace.callCapabilitiesMatch,
    Bool.and_eq_true] at rootMatch
  exact CodeTrace.tailCallPosition_of_capabilities_match
    checked.artifact.trace.positions checked.artifact.program.declarations
      functionTrace.generated.signature signatureAt
      (descendant.callCapabilitiesMatch checked.artifact.trace.positions
        checked.artifact.program.declarations
        functionTrace.generated.signature rootMatch.2)

/-- Recover result ownership agreement at an addressed tail call. -/
theorem tailCallResult (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {address : Address} {signature : Signature}
    {arguments : Array IxIR1.Atom} {generated : Block}
    (signatureAt : targetSignature? checked.artifact.program.declarations
      address = some signature)
    (descendant : functionTrace.root.Descendant
      (.tailCall source block input entryValueCount address arguments generated)) :
    signature.result = functionTrace.generated.signature.result := by
  have rootMatch := checked.functionCallCapabilitiesMatch member
  simp only [FunctionTrace.callCapabilitiesMatch,
    Bool.and_eq_true] at rootMatch
  exact CodeTrace.tailCallResult_of_capabilities_match
    checked.artifact.trace.positions checked.artifact.program.declarations
      functionTrace.generated.signature signatureAt
      (descendant.callCapabilitiesMatch checked.artifact.trace.positions
        checked.artifact.program.declarations
        functionTrace.generated.signature rootMatch.2)

/-- Recover a self tail call's exact all-local-owner transfer. -/
theorem tailCallSelfPosition (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {arguments : Array IxIR1.Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.tailCallSelf source block input entryValueCount arguments generated)) :
    ∃ position, position ∈ checked.artifact.trace.positions ∧
      position.tailCallMatches source block input
        functionTrace.generated.signature arguments = true := by
  have rootMatch := checked.functionCallCapabilitiesMatch member
  simp only [FunctionTrace.callCapabilitiesMatch,
    Bool.and_eq_true] at rootMatch
  exact CodeTrace.tailCallSelfPosition_of_capabilities_match
    checked.artifact.trace.positions checked.artifact.program.declarations
      functionTrace.generated.signature
      (descendant.callCapabilitiesMatch checked.artifact.trace.positions
        checked.artifact.program.declarations
        functionTrace.generated.signature rootMatch.2)

/-- Recover the exact result-owner transfer at a retained return. -/
theorem returnPositionMatch (checked : Checked)
    {functionTrace : FunctionTrace}
    (member : functionTrace ∈ checked.artifact.trace.functions)
    {source : SourceSite} {block : BlockId}
    {input : Array (Option Atom)} {entryValueCount : Nat}
    {atom : IxIR1.Atom} {target : Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.ret source block input entryValueCount atom target generated))
    {position : PositionTrace}
    (positionMember : position ∈ checked.artifact.trace.positions)
    (coordinate : position.coordinateMatches source block .terminator input =
      true) :
    position.returnMatches source block input
      functionTrace.generated.signature.result atom = true := by
  have rootMatch := checked.functionCallCapabilitiesMatch member
  simp only [FunctionTrace.callCapabilitiesMatch,
    Bool.and_eq_true] at rootMatch
  exact CodeTrace.returnPositionMatch_of_capabilities_match
    checked.artifact.trace.positions checked.artifact.program.declarations
      functionTrace.generated.signature
      (descendant.callCapabilitiesMatch checked.artifact.trace.positions
        checked.artifact.program.declarations
        functionTrace.generated.signature rootMatch.2)
      positionMember coordinate

end Checked

private def sourceDeclAt?
    (declarations : List (Address × IxIR1.Decl)) (address : Address) :
    Option IxIR1.Decl :=
  (declarations.find? fun entry => entry.1 == address).map (fun entry => entry.2)

private def duplicateAddress? :
    List (Address × IxIR1.Decl) → Option Address
  | [] => none
  | (address, _) :: rest =>
      if rest.any fun entry => entry.1 == address then some address
      else duplicateAddress? rest

private def signatureOf (context : Context) (owner : Validate.Owner)
    (address : Address) (definition : IxIR1.FnDef) : Except Error Signature := do
  let worlds ← match context.parameterWorlds address with
    | some worlds => pure worlds
    | none => .error (.missingParameterWorlds address)
  if worlds.size != definition.arity then
    .error (.signature owner "parameter-world arity does not match IxIR₁")
  else
    let parameters := worlds.map fun world =>
      ({ world, passing := .owned } : Param)
    let signature : Signature :=
      { params := parameters
        result := definition.result
        papSafe := definition.papSafe }
    if signature.papSafe &&
        !(signature.result == .shared &&
          signature.params.all fun parameter => parameter.world == .shared) then
      .error (.signature owner "IxIR₁ papSafe declaration is not all-shared")
    else
      return signature

private def declarationSignature (context : Context)
    (declarations : List (Address × IxIR1.Decl)) (site : SourceSite)
    (address : Address) : Except Error Signature := do
  match sourceDeclAt? declarations address with
  | some (.fn definition) =>
      signatureOf context (.declaration address) address definition
  | some (.extern _) =>
      .error (.source site "compiler call expected a function declaration")
  | none => .error (.source site "call target is not declared")

structure Binding where
  atom : Atom
  cap : BindingCap
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

abbrev SourceEnv := Array Binding

/-- Runtime operand retained for a live compiler binding. -/
def Binding.inputAtom (binding : Binding) : Option Atom :=
  match binding.cap with
  | .dead => none
  | _ => some binding.atom

def SourceEnv.inputMap (env : SourceEnv) : Array (Option Atom) :=
  env.map Binding.inputAtom

structure Local where
  env : SourceEnv
  valueParams : Array ValueCap
  instructions : Array Instr := #[]
  nextValue : Nat

def Local.inputMap (cursor : Local) : Array (Option Atom) :=
  cursor.env.inputMap

private def sourceAtom (site : SourceSite) (env : SourceEnv) :
    IxIR1.Atom → Except Error (Atom × BindingCap)
  | .lit literal => return (.lit literal, .scalar)
  | .erased => return (.erased, .scalar)
  | .var index =>
      match env[index]? with
      | none => .error (.source site s!"unbound IxIR₁ variable {index}")
      | some { cap := .dead, .. } =>
          .error (.ownership site s!"IxIR₁ variable {index} was already consumed")
      | some binding => return (binding.atom, binding.cap)

private def setDead (site : SourceSite) (env : SourceEnv) (index : Nat) :
    Except Error SourceEnv :=
  match env[index]? with
  | none => .error (.source site s!"unbound IxIR₁ variable {index}")
  | some binding =>
      let consumed := env.setIfInBounds index { binding with cap := .dead }
      match binding.atom with
      | .reg lender =>
          return consumed.map fun candidate =>
            { candidate with
              cap := candidate.cap.retireLender lender }
      | .lit _ | .erased => return consumed

private def consumeExpected (site : SourceSite) (expected : Owned)
    (env : SourceEnv) (source : IxIR1.Atom) :
    Except Error (SourceEnv × Atom) := do
  let (atom, capability) ← sourceAtom site env source
  match source, capability with
  | .lit _, .scalar | .erased, .scalar => return (env, atom)
  | .var _, .scalar => return (env, atom)
  | .var index, .owned world =>
      if world == expected then return (← setDead site env index, atom)
      else .error (.ownership site "operand has the wrong ownership world")
  | .var _, .borrowed .. =>
      .error (.ownership site "a borrowed value cannot cross an owned boundary")
  | _, .dead =>
      .error (.internal "dead source binding escaped sourceAtom")
  | _, _ => .error (.ownership site "invalid scalar capability")

private def consumeConcrete (site : SourceSite) (expected : Owned)
    (env : SourceEnv) (source : IxIR1.Atom) :
    Except Error (SourceEnv × ValueId) := do
  let (atom, capability) ← sourceAtom site env source
  match source, atom, capability with
  | .var index, .reg id, .owned world =>
      if world == expected then return (← setDead site env index, id)
      else .error (.ownership site "constructor operand has the wrong world")
  | .var _, _, .scalar =>
      .error (.ownership site "a concrete constructor location was required")
  | .var _, _, .borrowed .. =>
      .error (.ownership site "a borrowed constructor cannot be consumed")
  | _, _, _ =>
      .error (.ownership site "a concrete constructor register was required")

private def observeExpected (site : SourceSite) (expected : Owned)
    (env : SourceEnv) (source : IxIR1.Atom) : Except Error Atom := do
  let (atom, capability) ← sourceAtom site env source
  match capability with
  | .scalar => return atom
  | .owned world | .borrowed world _ =>
      if world == expected then return atom
      else .error (.ownership site "observed operand has the wrong world")
  | .dead => .error (.internal "dead source binding escaped sourceAtom")

private def requireScalar (site : SourceSite) (env : SourceEnv)
    (source : IxIR1.Atom) : Except Error Atom := do
  let (atom, capability) ← sourceAtom site env source
  match capability with
  | .scalar => return atom
  | _ => .error (.ownership site "extern operands must be statically scalar")

private def consumeArguments (site : SourceSite) (env : SourceEnv)
    (arguments : Array IxIR1.Atom) (worlds : Array Owned) :
    Except Error (SourceEnv × Array Atom) := do
  if arguments.size != worlds.size then
    .error (.source site "operand count does not match its ownership signature")
  else
    let (env, reversed) ←
      (arguments.toList.zip worlds.toList).foldlM (fun state pair => do
        let (env, atom) ← consumeExpected site pair.2 state.1 pair.1
        return (env, atom :: state.2)) (env, [])
    return (env, reversed.reverse.toArray)

private def consumeSharedArguments (site : SourceSite) (env : SourceEnv)
    (arguments : Array IxIR1.Atom) : Except Error (SourceEnv × Array Atom) :=
  consumeArguments site env arguments (Array.replicate arguments.size .shared)

private def bindResult (cursor : Local) (instruction : Instr)
    (capability : BindingCap) : Local :=
  { cursor with
    env := #[{ atom := .reg cursor.nextValue, cap := capability }] ++ cursor.env
    instructions := cursor.instructions.push instruction
    nextValue := cursor.nextValue + 1 }

private def bindEffect (cursor : Local) (instruction : Instr) : Local :=
  { cursor with
    env := #[{ atom := .erased, cap := .scalar }] ++ cursor.env
    instructions := cursor.instructions.push instruction }

private structure EdgeView where
  params : Array ValueCap
  sourceInputMap : Array (Option Atom)
  childEnv : SourceEnv

private def EdgeView.arguments (view : EdgeView) : Array Atom :=
  EdgeTrace.explicitValuesOf view.sourceInputMap

private def ownerParameter? (env : SourceEnv) (lender : ValueId) : Option Nat :=
  (List.range env.size).find? fun index =>
    match env[index]? with
    | some { atom := .reg id, cap := .owned _ } => id == lender
    | _ => false

private def edgeView (site : SourceSite) (env : SourceEnv) :
    Except Error EdgeView := do
  let rec go (index : Nat) (params : Array ValueCap)
      (child : SourceEnv) : Except Error EdgeView :=
    if h : index < env.size then
      let binding := env[index]
      match binding.cap with
      | .dead =>
          go (index + 1) (params.push .scalar)
            (child.push { atom := .reg index, cap := .dead })
      | .scalar =>
          go (index + 1) (params.push .scalar)
            (child.push { atom := .reg index, cap := .scalar })
      | .owned world =>
          go (index + 1) (params.push (.owned world))
            (child.push { atom := .reg index, cap := .owned world })
      | .borrowed world .caller =>
          go (index + 1) (params.push (.borrowed world .caller))
            (child.push { atom := .reg index, cap := .borrowed world .caller })
      | .borrowed world (.value lender) =>
          match ownerParameter? env lender with
          | none =>
              .error (.ownership site "edge borrow has no transferred lender")
          | some targetLender =>
              go (index + 1)
                (params.push (.borrowed world (.value targetLender)))
                (child.push
                  { atom := .reg index
                    cap := .borrowed world (.value targetLender) })
    else
      return { params, sourceInputMap := env.inputMap, childEnv := child }
  go 0 #[] #[]

private def shiftLender (amount : Nat) : BorrowLender → BorrowLender
  | .caller => .caller
  | .value id => .value (id + amount)

private def shiftBinding (amount : Nat) (binding : Binding) : Binding :=
  { atom := shiftAtom amount binding.atom
    cap := match binding.cap with
      | .borrowed world lender => .borrowed world (shiftLender amount lender)
      | capability => capability }

structure BuildState where
  blocks : Array (Option Block) := #[]
  scalarLeaves : List Validate.ScalarLeafFact := []
  positions : List PositionTrace := []
  edges : List EdgeTrace := []

abbrev BuildM := EStateM Error BuildState

private def reserveBlock : BuildM BlockId := do
  let state ← get
  let id := state.blocks.size
  set { state with blocks := state.blocks.push none }
  return id

private def installBlock (id : BlockId) (block : Block) : BuildM Unit := do
  let state ← get
  match state.blocks[id]? with
  | some none => set { state with blocks := state.blocks.setIfInBounds id (some block) }
  | some (some _) => throw (.internal s!"block {id} was installed twice")
  | none => throw (.internal s!"block {id} was never reserved")

private def recordPosition (source : SourceSite) (block : BlockId)
    (target : TargetPosition) (env : SourceEnv) : BuildM Unit :=
  modify fun state =>
    { state with
      positions :=
        { source, block, target
          sourceCapabilities := env.map (·.cap) } :: state.positions }

private def recordEdge (source : SourceSite) (sourceBlock target : BlockId)
    (view : EdgeView) (implicitScalars : Nat := 0) : BuildM EdgeTrace := do
  let trace : EdgeTrace :=
    { source
      sourceBlock
      target
      sourceInputMap := view.sourceInputMap
      targetParams := view.params
      implicitScalars }
  modify fun state => { state with edges := trace :: state.edges }
  return trace

private def recordScalarLeaf (owner : Validate.Owner) (block : BlockId)
    (value : ValueId) (cid : CtorId) : BuildM Unit :=
  modify fun state =>
    { state with scalarLeaves := { owner, block, value, cid } :: state.scalarLeaves }

private def lookupSchema (context : Context) (site : SourceSite)
    (world : Owned) (cid : CtorId) : BuildM CtorSchema :=
  match context.schemas world cid with
  | some schema => return schema
  | none => throw (.schema site "missing constructor schema")

private def liftExcept : Except Error α → BuildM α
  | .ok value => return value
  | .error error => throw error

private def lowerInstruction (context : Context)
    (declarations : List (Address × IxIR1.Decl)) (signature : Signature)
    (block : BlockId) (site : SourceSite) (cursor : Local)
    (operation : IxIR1.Op) : BuildM Local := do
  match operation with
  | .pure source =>
      let (atom, capability) ← liftExcept (sourceAtom site cursor.env source)
      let env ← match source, capability with
        | .var index, .owned _ => liftExcept (setDead site cursor.env index)
        | _, _ => pure cursor.env
      return (bindResult { cursor with env } (.move atom) capability)
  | .alloc world cid arguments =>
      let schema ← lookupSchema context site world cid
      let (env, atoms) ← liftExcept
        (consumeArguments site cursor.env arguments schema.fields)
      return bindResult { cursor with env } (.alloc world cid atoms) (.owned world)
  | .reuse .. =>
      throw (.unsupported site "raw IxIR₁ reuse is outside the baseline subset")
  | .free target =>
      let cid ← match context.scalarFreeCtor site with
        | some cid => pure cid
        | none => throw (.schema site "missing checked scalar-leaf free fact")
      let _ ← lookupSchema context site .unique cid
      let (env, value) ← liftExcept
        (consumeConcrete site .unique cursor.env target)
      recordScalarLeaf site.owner block value cid
      return bindEffect { cursor with env } (.freeUnique (.reg value) cid)
  | .dup target =>
      let (atom, capability) ← liftExcept (sourceAtom site cursor.env target)
      match capability with
      | .scalar =>
          return bindResult cursor (.retainShared atom) .scalar
      | .owned .shared | .borrowed .shared _ =>
          return bindResult cursor (.retainShared atom) (.owned .shared)
      | .owned .unique | .borrowed .unique _ =>
          throw (.ownership site "IxIR₁ dup requires a shared operand")
      | .dead => throw (.internal "dead source binding escaped sourceAtom")
  | .drop target =>
      let (env, atom) ← liftExcept
        (consumeExpected site .shared cursor.env target)
      return bindEffect { cursor with env } (.releaseShared atom)
  | .dropU target =>
      let (env, atom) ← liftExcept
        (consumeExpected site .unique cursor.env target)
      return bindEffect { cursor with env } (.dropUnique atom)
  | .fetch target field =>
      let cid ← match context.fetchCtor site with
        | some cid => pure cid
        | none => throw (.schema site "missing exact fetch constructor")
      let (atom, capability) ← liftExcept (sourceAtom site cursor.env target)
      let (world, lender) ← match capability, atom with
        | .owned world, .reg id => pure (world, BorrowLender.value id)
        | .borrowed world lender, _ => pure (world, lender)
        | .scalar, _ => throw (.ownership site "fetch requires a constructor")
        | .owned _, _ => throw (.internal "owned source binding is not a register")
        | .dead, _ => throw (.internal "dead source binding escaped sourceAtom")
      let schema ← lookupSchema context site world cid
      let fieldWorld ← match schema.fields[field]? with
        | some fieldWorld => pure fieldWorld
        | none => throw (.schema site s!"constructor field {field} is out of bounds")
      return bindResult cursor (.fetch atom cid field) (.borrowed fieldWorld lender)
  | .call address arguments =>
      let callee ← liftExcept
        (declarationSignature context declarations site address)
      let worlds := callee.params.map (fun parameter => parameter.world)
      let (env, atoms) ← liftExcept
        (consumeArguments site cursor.env arguments worlds)
      return bindResult { cursor with env } (.call address atoms)
        (.owned callee.result)
  | .callSelf arguments =>
      let worlds := signature.params.map (fun parameter => parameter.world)
      let (env, atoms) ← liftExcept
        (consumeArguments site cursor.env arguments worlds)
      return bindResult { cursor with env } (.callSelf atoms)
        (.owned signature.result)
  | .papp address arguments =>
      match sourceDeclAt? declarations address with
      | none => throw (.source site "partial-application target is not declared")
      | some (.extern arity) =>
          if !context.allowExtern then
            throw (.unsupported site "extern partial applications are disabled")
          else if arguments.size >= arity then
            throw (.source site "partial application is not under-saturated")
          else
            let atoms ← arguments.toList.mapM fun argument =>
              liftExcept (requireScalar site cursor.env argument)
            return bindResult cursor (.papp address atoms.toArray) (.owned .shared)
      | some (.fn _) =>
          let callee ← liftExcept
            (declarationSignature context declarations site address)
          if !callee.papSafe || arguments.size >= callee.params.size then
            throw (.source site "partial application target is not safely under-saturated")
          else
            let worlds := (callee.params.extract 0 arguments.size).map
              (fun parameter => parameter.world)
            let (env, atoms) ← liftExcept
              (consumeArguments site cursor.env arguments worlds)
            return bindResult { cursor with env } (.papp address atoms)
              (.owned .shared)
  | .apply function arguments =>
      let (env, function) ← liftExcept
        (consumeExpected site .shared cursor.env function)
      let (env, atoms) ← liftExcept
        (consumeSharedArguments site env arguments)
      return bindResult { cursor with env } (.apply function atoms)
        (.owned .shared)
  | .extern address arguments =>
      if !context.allowExtern then
        throw (.unsupported site "extern instructions are disabled")
      else
        match sourceDeclAt? declarations address with
        | some (.extern arity) =>
            if arguments.size != arity then
              throw (.source site "extern arity mismatch")
            else
              let atoms ← arguments.toList.mapM fun argument =>
                liftExcept (requireScalar site cursor.env argument)
              return bindResult cursor (.extern address atoms.toArray) .scalar
        | _ => throw (.source site "extern target is not an extern declaration")

private def initialEnv (signature : Signature) : SourceEnv :=
  let size := signature.params.size
  (List.range size).foldl (fun env sourceIndex =>
    let targetIndex := size - 1 - sourceIndex
    match signature.params[targetIndex]? with
    | some parameter =>
        env.push
          { atom := .reg targetIndex
            cap := match parameter.passing with
              | .owned => .owned parameter.world
              | .borrowed => .borrowed parameter.world .caller }
    | none => env) #[]

private def duplicateAltTag? : List IxIR1.Alt → Option Nat
  | [] => none
  | .mk tag _ _ :: rest =>
      if rest.any fun
          | .mk other _ _ => other == tag then some tag
      else duplicateAltTag? rest

private def finishBlocks (state : BuildState) : Except Error (Array Block) :=
  state.blocks.toList.mapM (fun (candidate : Option Block) =>
    match candidate with
    | some block => (Except.ok block : Except Error Block)
    | none => Except.error (Error.internal "reserved block was not installed"))
    |>.map List.toArray

/-- Fuel-bounded recursive block compiler. Exposing this worker and its state
is the proof seam for induction over the exact instruction/block generation
run retained by `CheckedRun`; production callers continue through `lower`. -/
def compileCode (context : Context)
    (declarations : List (Address × IxIR1.Decl)) (signature : Signature)
    (fuel : Nat) (block : BlockId) (site : SourceSite)
    (cursor : Local) (code : IxIR1.Code) : BuildM CodeTrace := do
    match fuel with
    | 0 => throw (.resources site)
    | fuel + 1 =>
      match code with
      | .ret source =>
          let (env, atom) ← liftExcept
            (consumeExpected site signature.result cursor.env source)
          recordPosition site block .terminator cursor.env
          let generated : Block :=
            { valueParams := cursor.valueParams
              creditParams := #[]
              instructions := cursor.instructions
              terminator := .ret atom }
          installBlock block generated
          let _ := env
          return .ret site block cursor.inputMap cursor.nextValue source atom
            generated
      | .letOp (.call address arguments) (.ret (.var 0)) =>
          match sourceDeclAt? declarations address with
          | some (.fn _) =>
              let callee ← liftExcept
                (declarationSignature context declarations site address)
              if callee.result == signature.result then
                let worlds := callee.params.map (fun parameter => parameter.world)
                let (tailEnv, atoms) ← liftExcept
                  (consumeArguments site cursor.env arguments worlds)
                recordPosition site block .terminator cursor.env
                let resultEnv : SourceEnv :=
                  #[{ atom := .erased, cap := .owned callee.result }] ++ tailEnv
                recordPosition site.next block .terminator resultEnv
                let generated : Block :=
                  { valueParams := cursor.valueParams
                    creditParams := #[]
                    instructions := cursor.instructions
                    terminator := .tailCall address atoms }
                installBlock block generated
                return .tailCall site block cursor.inputMap cursor.nextValue
                  address arguments generated
              else
                let inputMap := cursor.inputMap
                let positionEnv := cursor.env
                let entryValueCount := cursor.nextValue
                let index := cursor.instructions.size
                let cursor ← lowerInstruction context declarations signature block
                  site cursor (.call address arguments)
                let targetInstruction ← match cursor.instructions[index]? with
                  | some instruction => pure instruction
                  | none => throw (.internal
                      "lowered call was not appended at its trace index")
                recordPosition site block (.instruction index) positionEnv
                let next ← compileCode context declarations signature fuel block
                  site.next cursor (.ret (.var 0))
                return .letOp site block inputMap cursor.inputMap
                  entryValueCount (.call address arguments) index
                    targetInstruction next
          | _ =>
              let inputMap := cursor.inputMap
              let positionEnv := cursor.env
              let entryValueCount := cursor.nextValue
              let index := cursor.instructions.size
              let cursor ← lowerInstruction context declarations signature block
                site cursor (.call address arguments)
              let targetInstruction ← match cursor.instructions[index]? with
                | some instruction => pure instruction
                | none => throw (.internal
                    "lowered call was not appended at its trace index")
              recordPosition site block (.instruction index) positionEnv
              let next ← compileCode context declarations signature fuel block
                site.next cursor (.ret (.var 0))
              return .letOp site block inputMap cursor.inputMap entryValueCount
                (.call address arguments) index targetInstruction next
      | .letOp (.callSelf arguments) (.ret (.var 0)) =>
          let worlds := signature.params.map (fun parameter => parameter.world)
          let (tailEnv, atoms) ← liftExcept
            (consumeArguments site cursor.env arguments worlds)
          recordPosition site block .terminator cursor.env
          let resultEnv : SourceEnv :=
            #[{ atom := .erased, cap := .owned signature.result }] ++ tailEnv
          recordPosition site.next block .terminator resultEnv
          let generated : Block :=
            { valueParams := cursor.valueParams
              creditParams := #[]
              instructions := cursor.instructions
              terminator := .tailCallSelf atoms }
          installBlock block generated
          return .tailCallSelf site block cursor.inputMap cursor.nextValue
            arguments generated
      | .letOp operation rest =>
          let inputMap := cursor.inputMap
          let positionEnv := cursor.env
          let entryValueCount := cursor.nextValue
          let index := cursor.instructions.size
          let cursor ← lowerInstruction context declarations signature block
            site cursor operation
          let targetInstruction ← match cursor.instructions[index]? with
            | some instruction => pure instruction
            | none => throw (.internal
                "lowered instruction was not appended at its trace index")
          recordPosition site block (.instruction index) positionEnv
          let next ← compileCode context declarations signature fuel block
            site.next cursor rest
          return .letOp site block inputMap cursor.inputMap entryValueCount
            operation index targetInstruction next
      | .case scrutinee peelNat alternatives =>
          if let some tag := duplicateAltTag? alternatives.toList then
            throw (.source site s!"duplicate IxIR₁ case tag {tag}")
          let (_, scrutineeCap) ← liftExcept
            (sourceAtom site cursor.env scrutinee)
          let world ← match scrutineeCap with
            | .owned world | .borrowed world _ => pure world
            | .scalar => pure .shared
            | .dead => throw (.internal "dead source binding escaped sourceAtom")
          let view ← liftExcept (edgeView site cursor.env)
          let mut constructorTargets : Array CtorAlt := #[]
          let mut outgoing : Array EdgeTrace := #[]
          let mut children : Array CodeTrace := #[]
          for pair in alternatives.toList.zipIdx do
            let (.mk tag fieldCount altBody, altIndex) := pair
            let caseCtors := context.caseCtors site altIndex
            if caseCtors.isEmpty then
              if peelNat then pure ()
              else throw (.schema site
                "non-Nat case alternative lacks a constructor identity")
            for cid in caseCtors do
                if cid.cidx != tag then
                  throw (.schema site "case constructor tag does not match IxIR₁")
                let schema ← lookupSchema context site world cid
                if schema.fields.size != fieldCount then
                  throw (.schema site "case field count does not match constructor schema")
                let child ← reserveBlock
                let childSite := site.alternative altIndex
                let (scrutinee, scrutineeCapability) ← liftExcept
                  (sourceAtom childSite view.childEnv scrutinee)
                let lender ← match scrutineeCapability, scrutinee with
                  | .owned _, .reg id => pure (BorrowLender.value id)
                  | .borrowed _ lender, _ => pure lender
                  | _, _ => throw (.ownership childSite "constructor arm lost its scrutinee")
                let mut childLocal : Local :=
                  { env := view.childEnv
                    valueParams := view.params
                    nextValue := view.params.size }
                let mut fields : SourceEnv := #[]
                for field in List.range fieldCount do
                  let fieldWorld := schema.fields[field]!
                  let resultId := childLocal.nextValue
                  childLocal :=
                    { childLocal with
                      instructions := childLocal.instructions.push
                        (.fetch scrutinee cid field)
                      nextValue := resultId + 1 }
                  fields := fields.push
                    { atom := .reg resultId
                      cap := .borrowed fieldWorld lender }
                childLocal :=
                  { childLocal with env := fields.reverse ++ childLocal.env }
                let edge ← recordEdge site block child view
                let childTrace ← compileCode context declarations signature fuel child
                  childSite childLocal altBody
                outgoing := outgoing.push edge
                children := children.push childTrace
                constructorTargets := constructorTargets.push
                  { cid, edge := { target := child, values := view.arguments, credits := #[] } }
          let natPeel ← if peelNat then do
            let zero ← match sourceAlternativeAtTag? alternatives 0 with
              | some (.mk _ 0 body, index) => pure (body, index)
              | _ => throw (.source site "Nat peel requires a nullary zero arm")
            let succ ← match sourceAlternativeAtTag? alternatives 1 with
              | some (.mk _ 1 body, index) => pure (body, index)
              | _ => throw (.source site "Nat peel requires a unary successor arm")
            let zeroBlock ← reserveBlock
            let zeroSite := site.alternative zero.2
            let zeroEdge ← recordEdge site block zeroBlock view
            let zeroTrace ← compileCode context declarations signature fuel
              zeroBlock zeroSite
              { env := view.childEnv
                valueParams := view.params
                nextValue := view.params.size } zero.1
            outgoing := outgoing.push zeroEdge
            children := children.push zeroTrace
            let succBlock ← reserveBlock
            let succSite := site.alternative succ.2
            let shifted := view.childEnv.map (shiftBinding 1)
            let succEnv :=
              #[{ atom := .reg 0, cap := .scalar }] ++ shifted
            let succParams := #[.scalar] ++ view.params
            let succEdge ← recordEdge site block succBlock
              { view with params := succParams } 1
            let succTrace ← compileCode context declarations signature fuel
              succBlock succSite
              { env := succEnv
                valueParams := succParams
                nextValue := succParams.size } succ.1
            outgoing := outgoing.push succEdge
            children := children.push succTrace
            pure (some
              { zero := { target := zeroBlock, values := view.arguments, credits := #[] }
                succ := { target := succBlock, values := view.arguments, credits := #[] } })
          else
            pure none
          if constructorTargets.isEmpty && natPeel.isNone then
            throw (.source site "case has no translated alternatives")
          let (targetScrutinee, _) ←
            liftExcept (sourceAtom site cursor.env scrutinee)
          recordPosition site block .terminator cursor.env
          let generated : Block :=
            { valueParams := cursor.valueParams
              creditParams := #[]
              instructions := cursor.instructions
              terminator :=
                .switchValue targetScrutinee constructorTargets natPeel }
          installBlock block generated
          return .switchValue site block cursor.inputMap cursor.nextValue
            scrutinee peelNat alternatives targetScrutinee generated
              outgoing.toList children.toList
termination_by fuel

private def compileFunction (context : Context)
    (declarations : List (Address × IxIR1.Decl)) (owner : Validate.Owner)
    (signature : Signature) (source : IxIR1.FnDef) :
    Except Error (Function × List Validate.ScalarLeafFact × Trace) :=
  let action : BuildM CodeTrace := do
    let entry ← reserveBlock
    if entry != 0 then throw (.internal "function entry block is not zero")
    let params := signature.params.map fun parameter =>
      match parameter.passing with
      | .owned => .owned parameter.world
      | .borrowed => .borrowed parameter.world .caller
    compileCode context declarations signature context.maxDepth entry { owner }
      { env := initialEnv signature
        valueParams := params
        nextValue := params.size } source.body
  match action.run {} with
  | .error error _ => .error error
  | .ok root state => do
      let blocks ← finishBlocks state
      let generated : Function := ⟨signature, blocks⟩
      let expectedBlocks : List (BlockId × Block) :=
        blocks.toList.zipIdx.map fun pair => (pair.2, pair.1)
      if sourceCoherent : functionSourceMatches source generated root then
        if coherent : root.blocks == expectedBlocks then
          have blockOrder : root.blocks = expectedBlocks :=
            beq_iff_eq.mp coherent
          if instructionCoherent : root.instructionsMatch then
            if inputMapsCoherent : root.inputMapsMatch then
              if entryValueCountsCoherent : root.entryValueCountsMatch then
                if syntaxCoherent : root.syntaxMatches then
                  if switchCoherent : root.switchBranchesMatch then
                    if rootSourceCoherent :
                        root.source == ({ owner := owner } : SourceSite) then
                      let functionTrace : FunctionTrace :=
                        { owner, source, generated, root
                          rootSource := beq_iff_eq.mp rootSourceCoherent
                          sourceOrder := functionSourceMatch_of_match sourceCoherent
                          instructionOrder := instructionCoherent
                          inputMapOrder := inputMapsCoherent
                          entryValueCountOrder := entryValueCountsCoherent
                          syntaxOrder := syntaxCoherent
                          switchBranchOrder := switchCoherent
                          blockOrder := by
                            simpa [generated, expectedBlocks] using blockOrder }
                      let trace : Trace :=
                        { positions := state.positions.reverse
                          edges := state.edges.reverse
                          functions := [functionTrace] }
                      return (generated, state.scalarLeaves.reverse, trace)
                    else
                      throw (.internal
                        "recursive trace root has the wrong source coordinate")
                  else
                    throw (.internal
                      "recursive trace switch branches do not match generated edges")
                else
                  throw (.internal
                    "recursive trace source and target syntax do not match")
              else
                throw (.internal
                  "recursive trace block-entry value counts do not match block parameters")
            else
              throw (.internal
                "recursive trace source maps retarget a retained slot")
          else
            throw (.internal
              "recursive trace instruction coordinates do not match its blocks")
        else
          throw (.internal "recursive trace does not match installed block order")
      else
        throw (.internal
          "recursive trace does not match its retained source function")

private def appendTrace (left right : Trace) : Trace :=
  { positions := left.positions ++ right.positions
    edges := left.edges ++ right.edges
    functions := left.functions ++ right.functions }

/-- Syntax-directed baseline lowering. This constructs all validator sidecars
that depend on target block/register identities, but does not hide validation;
use `lowerChecked` at an artifact boundary. -/
def lower (context : Context) (input : Input) : Except Error Artifact := do
  let _ ← match duplicateAddress? input.declarations with
    | some address => Except.error (.duplicateDeclaration address)
    | none => Except.ok ()
  let mut declarations : List (Address × Decl) := []
  let mut scalarLeaves : List Validate.ScalarLeafFact := []
  let mut trace : Trace := {}
  for entry in input.declarations do
    match entry.2 with
    | .extern arity =>
        declarations := declarations ++ [(entry.1, .extern arity)]
    | .fn definition =>
        let owner := Validate.Owner.declaration entry.1
        let signature ← signatureOf context owner entry.1 definition
        let (lowered, leaves, functionTrace) ←
          compileFunction context input.declarations owner signature definition
        declarations := declarations ++ [(entry.1, .fn lowered)]
        scalarLeaves := scalarLeaves ++ leaves
        trace := appendTrace trace functionTrace
  let mainSignature : Signature :=
    { params := #[], result := input.mainResult, papSafe := false }
  let mainSource := input.mainDefinition
  let (main, mainLeaves, mainTrace) ←
    compileFunction context input.declarations .main mainSignature mainSource
  let mainTraceWitness : { trace // trace ∈ mainTrace.functions } ←
    match membersEq : mainTrace.functions with
    | [functionTrace] =>
        pure ⟨functionTrace, by simp [membersEq]⟩
    | _ => throw (.internal
        "main compiler run did not retain exactly one function trace")
  let mainFunctionTrace := mainTraceWitness.1
  let validationContext : Validate.Context :=
    { schemas := context.schemas
      scalarLeaves := scalarLeaves ++ mainLeaves
      allowExtern := context.allowExtern }
  let program : Program := { declarations, main }
  let fullTrace := appendTrace trace mainTrace
  if mainCoherent : functionTraceMatches mainFunctionTrace .main
      input.mainDefinition program.main then
    if functionsCoherent : programTraceMatches input.declarations
        program.declarations fullTrace.functions input.mainDefinition
          program.main then
      let artifact : Artifact :=
        { source := input
          program
          validationContext
          trace := fullTrace
          mainTrace := mainFunctionTrace
          mainTraceMember := by
            change mainFunctionTrace ∈ trace.functions ++ mainTrace.functions
            exact List.mem_append_right trace.functions mainTraceWitness.2
          mainTraceOrder := functionTraceMatch_of_match mainCoherent
          functionTraceOrder := functionsCoherent }
      return artifact
    else
      throw (.internal
        "retained function traces do not match lowered declarations")
  else
    throw (.internal "retained main trace does not match the lowered artifact")

/-- The validation schema oracle in a successfully lowered artifact is the
exact oracle supplied to the lowerer. -/
theorem validationSchemas_of_lower
    {context : Context} {input : Input} {artifact : Artifact}
    (produced : lower context input = .ok artifact) :
    artifact.validationContext.schemas = context.schemas := by
  unfold lower at produced
  simp_all [Except.bind, bind, pure]
  all_goals split at produced <;> try simp_all
  all_goals split at produced <;> try simp_all
  all_goals split at produced <;> try simp_all
  all_goals split at produced <;> try simp_all
  all_goals simp only [Except.pure] at produced
  all_goals split at produced <;> try simp_all
  all_goals split at produced <;> try simp_all
  all_goals subst artifact
  all_goals rfl

/-- Proof-facing execution record for checked lowering. The ordinary
`lowerChecked` API projects the same checked artifact, while simulation can
retain the exact producer equation without executing the lowerer twice. -/
structure CheckedRun (context : Context) (input : Input) where
  checked : Checked
  produced : lower context input = .ok checked.artifact
  /-- The checked artifact retains the exact input passed to this run. -/
  source : checked.artifact.source = input

namespace CheckedRun

/-- The artifact named by the retained producer equation is validator-valid. -/
theorem valid {context : Context} {input : Input}
    (run : CheckedRun context input) :
    Validate.Valid run.checked.artifact.validationContext
      run.checked.artifact.program :=
  run.checked.valid

end CheckedRun

/-- Lower and validate once while retaining both exact executable equations. -/
def lowerCheckedWithTrace (context : Context) (input : Input) :
    Except Error (CheckedRun context input) :=
  match produced : lower context input with
  | .error error => .error error
  | .ok artifact =>
      if creditFree : CreditFree.program artifact.program then
        match accepted : Validate.validate artifact.validationContext
            artifact.program with
        | .error error => .error (.validation error)
        | .ok stats =>
            if positionsMatched : artifact.trace.positionsMatch then
              if parameterCapabilitiesMatched :
                  artifact.trace.parameterCapabilitiesMatch then
                if pureMatched : artifact.trace.pureCapabilitiesMatch then
                  if dupMatched : artifact.trace.dupCapabilitiesMatch then
                    if fetchMatched : artifact.trace.fetchCapabilitiesMatch then
                      if destructionMatched :
                          artifact.trace.destructionCapabilitiesMatch then
                        if schemasMatched : artifact.trace.allocationSchemasMatch
                            artifact.validationContext.schemas then
                          if capabilitiesMatched :
                              artifact.trace.allocationCapabilitiesMatch then
                            if terminalAllocationsBorrowFree :
                                artifact.trace.terminalAllocationNoBorrows then
                              if applyMatched : artifact.trace.applyCapabilitiesMatch then
                                if sharedPapEntriesMatched :
                                    artifact.trace.sharedPapEntryCapabilitiesMatch then
                                  if switchMatched : artifact.trace.switchCapabilitiesMatch
                                      artifact.validationContext.schemas then
                                    if callsMatched : artifact.trace.callCapabilitiesMatch
                                        artifact.program.declarations then
                                      if sourceMatched : inputEq artifact.source input then
                                        .ok
                                          { checked :=
                                              { artifact, stats, accepted, creditFree
                                                positionCoordinates := positionsMatched
                                                parameterCapabilities :=
                                                  parameterCapabilitiesMatched
                                                pureCapabilities := pureMatched
                                                dupCapabilities := dupMatched
                                                fetchCapabilities := fetchMatched
                                                destructionCapabilities := destructionMatched
                                                allocationSchemas := schemasMatched
                                                allocationCapabilities := capabilitiesMatched
                                                terminalAllocationNoBorrows :=
                                                  terminalAllocationsBorrowFree
                                                applyCapabilities := applyMatched
                                                sharedPapEntryCapabilities :=
                                                  sharedPapEntriesMatched
                                                switchCapabilities := switchMatched
                                                callCapabilities := callsMatched }
                                            produced
                                            source :=
                                              (inputEq_eq_true_iff _ _).mp sourceMatched }
                                      else
                                        .error (.internal
                                          "lowered artifact retained the wrong source input")
                                    else
                                      .error (.internal
                                        "call/return traces lack exact capability transitions")
                                  else
                                    .error (.internal
                                      "switch traces lack exact capability transitions")
                                else
                                  .error (.internal
                                    "PAP-safe functions lack shared entry capabilities")
                              else
                                .error (.internal
                                  "dynamic-application traces lack exact capability transitions")
                            else
                              .error (.internal
                                "terminal allocations retain borrowed capabilities")
                          else
                            .error (.internal
                              "allocation/PAP traces lack exact capability transitions")
                        else
                          .error (.internal
                            "validator accepted inconsistent allocation schemas")
                      else
                        .error (.internal
                          "destruction traces lack exact capability transitions")
                    else
                      .error (.internal
                        "fetch traces lack producer capability transitions")
                  else
                    .error (.internal
                      "dup traces lack producer capability transitions")
                else
                  .error (.internal
                    "pure traces lack producer capability transitions")
              else
                .error (.internal
                  "source capabilities disagree with inherited block parameters")
            else
              .error (.internal
                "recursive traces lack producer position coordinates")
      else
        .error (.internal "baseline lowering emitted a credit operation")

/-- Lower and immediately validate the exact artifact returned to the caller. -/
def lowerChecked (context : Context) (input : Input) : Except Error Checked := do
  return (← lowerCheckedWithTrace context input).checked

end Ix.Compiler.IxIR2.Lower
