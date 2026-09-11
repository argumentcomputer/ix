import Ix.Compiler.IxIR2.Reuse
import Ix.Compiler.IxIR2.CallEval
import Ix.Compiler.IxIR2.CreditFree

/-!
# Checked shared reuse across direct calls

The v1 pass recognizes a consuming constructor prefix followed by a nonempty
straight-line sequence of direct calls, an allocation, and a return. Reset
exposes the owned fields; moves retain the original result-register numbering.
The optional credit stays in the caller until the matching allocation. Every
accepted site retains exact syntax, last-use, and representation evidence.
-/

namespace Ix.Compiler.IxIR2.CallReuse

open Ix.Compiler.Ixon (Address)

def policy : CreditPolicy := .suspendedCallsV1

def policyTag : String := "shared-call-reuse/1"

/-- Structural source facts used by the executable simulation. The ordinary
compiler produces this subset; unsupported checked input uses the baseline. -/
def functionReady (definition : Function) : Bool :=
  CreditFree.function definition &&
    definition.blocks.all (fun block => block.creditParams.isEmpty) &&
    match definition.blocks[0]? with
    | none => false
    | some entry => entry.valueParams.size == definition.signature.params.size

def programReady (source : Program) : Bool :=
  functionReady source.main && source.declarations.all (fun (_, declaration) =>
    match declaration with
    | .fn definition => functionReady definition
    | .extern _ => true)

theorem functionReady_creditFree {definition : Function}
    (ready : functionReady definition = true) : CreditFree.function definition = true := by
  simp only [functionReady, Bool.and_eq_true] at ready
  exact ready.1.1

theorem functionReady_entry {definition : Function} {entry : Block}
    (ready : functionReady definition = true) (found : definition.blocks[0]? = some entry) :
    entry.valueParams.size = definition.signature.params.size := by
  simp only [functionReady, Bool.and_eq_true] at ready
  have checked := ready.2
  simpa only [found, beq_iff_eq] using checked

theorem functionReady_credits {definition : Function} {block : Block} {blockId : Nat}
    (ready : functionReady definition = true) (found : definition.blocks[blockId]? = some block) :
    block.creditParams = #[] := by
  simp only [functionReady, Bool.and_eq_true] at ready
  have checked := ready.1.2
  obtain ⟨bound, atBlock⟩ := Array.getElem?_eq_some_iff.mp found
  have empty := Array.all_eq_true.mp checked blockId bound
  simpa only [atBlock, Array.isEmpty_iff] using empty

structure Shape where
  valueParams : Array ValueCap
  source : ValueId
  sourceConstructor : CtorId
  fieldCount : Nat
  calls : Array Instr
  allocationConstructor : CtorId
  allocationArguments : Array Atom
  result : Atom
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def Shape.fetches (shape : Shape) : Array Instr :=
  (List.range shape.fieldCount).toArray.map fun field =>
    .fetch (.reg shape.source) shape.sourceConstructor field

def Shape.retains (shape : Shape) : Array Instr :=
  (List.range shape.fieldCount).toArray.map fun field =>
    .retainShared (.reg (shape.valueParams.size + field))

def Shape.moves (shape : Shape) : Array Instr :=
  (List.range shape.fieldCount).toArray.map fun field =>
    .move (.reg (shape.valueParams.size + field))

def Shape.baseline (shape : Shape) : Block :=
  { valueParams := shape.valueParams
    creditParams := #[]
    instructions := shape.fetches ++ shape.retains ++
      #[.releaseShared (.reg shape.source)] ++ shape.calls ++
      #[.alloc .shared shape.allocationConstructor shape.allocationArguments]
    terminator := .ret shape.result }

def Shape.target (shape : Shape) : Block :=
  { valueParams := shape.valueParams
    creditParams := #[]
    instructions := #[.resetShared (.reg shape.source) shape.sourceConstructor] ++
      shape.moves ++ shape.calls ++
      #[.allocWith 0 .shared shape.allocationConstructor shape.allocationArguments]
    terminator := .ret shape.result }

/-- Reuse the established exact-layout checker, independently of its v0
tail-call shape recognizer. -/
def Shape.layoutInput (shape : Shape) : Reuse.Shape :=
  { parameterCount := shape.valueParams.size
    source := shape.source
    sourceConstructor := shape.sourceConstructor
    fieldCount := shape.fieldCount
    releasePosition := 2 * shape.fieldCount
    allocationConstructor := shape.allocationConstructor
    allocationArguments := shape.allocationArguments
    tailArguments := #[] }

def propose? (block : Block) : Option Shape := do
  let .fetch (.reg source) sourceConstructor 0 ← block.instructions[0]? | none
  let release ← block.instructions.findIdx? fun instruction =>
    instruction == .releaseShared (.reg source)
  let fieldCount := release / 2
  let .alloc .shared allocationConstructor allocationArguments ← block.instructions.back? | none
  let .ret result := block.terminator | none
  return {
    valueParams := block.valueParams, source, sourceConstructor, fieldCount
    calls := block.instructions.extract (release + 1) (block.instructions.size - 1)
    allocationConstructor, allocationArguments, result }

structure Site (limits : Validate.Limits) (context : Validate.Context) (block : Block) where
  shape : Shape
  exact : block = shape.baseline
  fieldsPositive : 0 < shape.fieldCount
  sourceOwned : shape.valueParams[shape.source]? = some (.owned .shared)
  callsNonempty : shape.calls.isEmpty = false
  directCalls : shape.calls.all (Eval.Policy.DirectCall.ofInstruction? · |>.isSome) = true
  placement : Reuse.Placement block
  placementProduced : Reuse.inferPlacementWith limits block shape.source
    (2 * shape.fieldCount) = .ok (some placement)
  representation : Reuse.Representation
  representationProduced : Reuse.representation? context shape.layoutInput = some representation

def inspect (limits : Validate.Limits) (context : Validate.Context) (block : Block) :
    Option (Site limits context block) := do
  let shape ← propose? block
  if exact : block = shape.baseline then
    if fieldsPositive : 0 < shape.fieldCount then
      if sourceOwned : shape.valueParams[shape.source]? = some (.owned .shared) then
        if callsNonempty : shape.calls.isEmpty = false then
          if directCalls : shape.calls.all
              (Eval.Policy.DirectCall.ofInstruction? · |>.isSome) = true then
            match placed : Reuse.inferPlacementWith limits block shape.source
                (2 * shape.fieldCount) with
            | .ok (some placement) =>
                match represented : Reuse.representation? context shape.layoutInput with
                | some representation => some {
                    shape, exact, fieldsPositive, sourceOwned, callsNonempty, directCalls
                    placement, placementProduced := placed
                    representation, representationProduced := represented }
                | none => none
            | _ => none
          else none
        else none
      else none
    else none
  else none

inductive Decision (limits : Validate.Limits) (context : Validate.Context) (block : Block) where
  | unchanged (rejected : inspect limits context block = none)
  | accepted (site : Site limits context block)
      (produced : inspect limits context block = some site)

def decideBlock (limits : Validate.Limits) (context : Validate.Context) (block : Block) :
    Decision limits context block :=
  match produced : inspect limits context block with
  | none => .unchanged produced
  | some site => .accepted site produced

def Decision.target {limits : Validate.Limits} {context : Validate.Context} {block : Block} :
    Decision limits context block → Block
  | .unchanged _ => block
  | .accepted site _ => site.shape.target

def rewriteBlock (limits : Validate.Limits) (context : Validate.Context) (block : Block) : Block :=
  (decideBlock limits context block).target

def rewriteFunction (limits : Validate.Limits) (context : Validate.Context)
    (definition : Function) : Function :=
  { definition with blocks := definition.blocks.map (rewriteBlock limits context) }

def rewriteProgram (limits : Validate.Limits) (context : Validate.Context) (source : Program) : Program :=
  { declarations := source.declarations.map fun (address, declaration) =>
      (address, match declaration with
        | .fn definition => .fn (rewriteFunction limits context definition)
        | .extern arity => .extern arity)
    main := rewriteFunction limits context source.main }

structure Report where
  scannedBlocks : Nat := 0
  rewritten : Nat := 0
  suspendedCallSites : Nat := 0
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def reportBlock (limits : Validate.Limits) (context : Validate.Context)
    (report : Report) (block : Block) : Report :=
  match inspect limits context block with
  | none => { report with scannedBlocks := report.scannedBlocks + 1 }
  | some site =>
      { scannedBlocks := report.scannedBlocks + 1
        rewritten := report.rewritten + 1
        suspendedCallSites := report.suspendedCallSites + site.shape.calls.size }

def report (limits : Validate.Limits) (context : Validate.Context) (source : Program) : Report :=
  let declarations := source.declarations.foldl (fun current (_, declaration) =>
    match declaration with
    | .extern _ => current
    | .fn definition => definition.blocks.foldl (reportBlock limits context) current) {}
  source.main.blocks.foldl (reportBlock limits context) declarations

structure Output (limits : Validate.Limits) (context : Validate.Context) (source : Program) where
  sourceChecked : Validate.Checked limits context source
  sourceReady : programReady source = true
  targetChecked : Validate.CheckedWithPolicy policy limits context
    (rewriteProgram limits context source)

def Output.target {limits : Validate.Limits} {context : Validate.Context} {source : Program}
    (_output : Output limits context source) : Program := rewriteProgram limits context source

inductive Error where
  | invalidSource (error : Validate.Error)
  | unsupportedSource
  | invalidTarget (error : Validate.Error)
  deriving Repr

def optimizeWith (limits : Validate.Limits) (context : Validate.Context) (source : Program) :
    Except Error (Output limits context source) :=
  match sourceAccepted : Validate.validateWith limits context source with
  | .error error => .error (.invalidSource error)
  | .ok sourceStats =>
      if sourceReady : programReady source = true then
        match targetAccepted : Validate.validateWithPolicy policy limits context
            (rewriteProgram limits context source) with
        | .error error => .error (.invalidTarget error)
        | .ok targetStats => .ok {
            sourceChecked := ⟨sourceStats, sourceAccepted⟩
            sourceReady
            targetChecked := ⟨targetStats, targetAccepted⟩ }
      else .error .unsupportedSource

inductive Selection (limits : Validate.Limits) (context : Validate.Context) (source : Program) where
  | optimized (output : Output limits context source)
      (produced : optimizeWith limits context source = .ok output)
  | baseline (checked : Validate.Checked limits context source) (error : Error)
      (rejected : optimizeWith limits context source = .error error)

def Selection.target {limits : Validate.Limits} {context : Validate.Context} {source : Program} :
    Selection limits context source → Program
  | .optimized output _ => output.target
  | .baseline _ _ _ => source

def Selection.policy {limits : Validate.Limits} {context : Validate.Context} {source : Program} :
    Selection limits context source → CreditPolicy
  | .optimized _ _ => CallReuse.policy
  | .baseline _ _ _ => .callLocalV0

def selectChecked (limits : Validate.Limits) (context : Validate.Context) (source : Program)
    (checked : Validate.Checked limits context source) : Selection limits context source :=
  match produced : optimizeWith limits context source with
  | .ok output => .optimized output produced
  | .error error => .baseline checked error produced

theorem Selection.valid {limits : Validate.Limits} {context : Validate.Context} {source : Program}
    (selection : Selection limits context source) :
    ∃ stats, Validate.validateWithPolicy selection.policy limits context selection.target = .ok stats := by
  cases selection with
  | optimized output produced => exact ⟨output.targetChecked.stats, output.targetChecked.accepted⟩
  | baseline checked error rejected => exact ⟨checked.stats, checked.accepted⟩

theorem rewriteFunction_signature (limits : Validate.Limits) (context : Validate.Context)
    (definition : Function) :
    (rewriteFunction limits context definition).signature = definition.signature := rfl

theorem rewriteFunction_blockCount (limits : Validate.Limits) (context : Validate.Context)
    (definition : Function) :
    (rewriteFunction limits context definition).blocks.size = definition.blocks.size := by
  simp [rewriteFunction]

end Ix.Compiler.IxIR2.CallReuse
