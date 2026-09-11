import Ix.Compiler.IxIR2.Borrow.OpenSim

/-! An open-input selector. All proposed summaries and all rewritten bodies
must have a finite structural derivation. Selection never evaluates an input.
The original main/factory continues to export the owned PAP entry. -/

namespace Ix.Compiler.IxIR2.Borrow.Open

open Ix.Compiler.Ixon (Address)

structure Policy where
  enabled : Bool := true
  maxDepth : Nat := 32
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def moduleMain (factoryAddress : Address) : Function :=
  { signature := { params := #[], result := .shared, papSafe := false }
    blocks := #[{
      valueParams := #[], creditParams := #[], instructions := #[]
      terminator := .tailCall factoryAddress #[] }] }

def readerSchema? (definition : Function) : Option Schema := do
  let entry ← definition.blocks[0]?
  let .switchValue _ alternatives _ := entry.terminator | none
  let zero ← alternatives[0]?
  let succ ← alternatives[1]?
  let zeroBlock ← definition.blocks[1]?
  let succBlock ← definition.blocks[2]?
  let .ret (.lit (.nat zeroResult)) := zeroBlock.terminator | none
  let .ret (.lit (.nat succResult)) := succBlock.terminator | none
  let schema : Schema := { zero := zero.cid, succ := succ.cid, zeroResult, succResult }
  if definition == reader schema false then some schema else none

def inferSchema (program : Program) : Option Schema :=
  program.declarations.findSome? fun
    | (_, .fn definition) => readerSchema? definition
    | _ => none

def context (validation : Validate.Context) (program : Program) : Eval.Context :=
  .ofProgram program validation.schemas

structure Export (validation : Validate.Context) (program : Program) where
  factoryAddress : Address
  entryAddress : Address
  main : program.main = moduleMain factoryAddress
  factoryAt : (context validation program).declarations factoryAddress = some (.fn (factory entryAddress))

def checkExport (validation : Validate.Context) (program : Program) : Option (Export validation program) := do
  let block ← program.main.blocks[0]?
  let .tailCall factoryAddress _ := block.terminator | none
  let some (.fn declaration) := (context validation program).declarations factoryAddress | none
  let first ← declaration.blocks[0]?
  let instruction ← first.instructions[0]?
  let .papp entryAddress _ := instruction | none
  if hm : program.main = moduleMain factoryAddress then
    if hf : (context validation program).declarations factoryAddress = some (.fn (factory entryAddress)) then
      some ⟨factoryAddress, entryAddress, hm, hf⟩
    else none
  else none

structure Entry (beforeContext afterContext : Eval.Context) (schema : Schema) where
  summary : Summary
  before : Function
  after : Function
  beforeAt : beforeContext.declarations summary.owner = some (.fn before)
  afterAt : afterContext.declarations summary.borrowed = some (.fn after)
  wrapperAt : afterContext.declarations summary.owner = some (.fn (ownedWrapper summary.borrowed before))
  beforeBody : Body beforeContext schema false before
  afterBody : Body afterContext schema true after
  sameKind : beforeBody.isTwice = afterBody.isTwice
  sameDepth : beforeBody.depth = afterBody.depth

def checkEntry (beforeContext afterContext : Eval.Context) (schema : Schema)
    (maxDepth : Nat) (summary : Summary) : Option (Entry beforeContext afterContext schema) := do
  let some (.fn before) := beforeContext.declarations summary.owner | none
  let some (.fn after) := afterContext.declarations summary.borrowed | none
  let beforeBody ← recognizeBody beforeContext schema false maxDepth before
  let afterBody ← recognizeBody afterContext schema true maxDepth after
  if beforeAt : beforeContext.declarations summary.owner = some (.fn before) then
    if afterAt : afterContext.declarations summary.borrowed = some (.fn after) then
      if wrapperAt : afterContext.declarations summary.owner = some (.fn (ownedWrapper summary.borrowed before)) then
        if sameKind : beforeBody.isTwice = afterBody.isTwice then
          if sameDepth : beforeBody.depth = afterBody.depth then
            some ⟨summary, before, after, beforeAt, afterAt, wrapperAt, beforeBody, afterBody, sameKind, sameDepth⟩
          else none
        else none
      else none
    else none
  else none

inductive Rejection where
  | disabled
  | noCandidates
  | schema
  | rewrite (error : Borrow.Error)
  | export
  | body
  | coverage
  | noImprovement
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

structure Certificate (limits : Limits) (validation : Validate.Context) (baseline : Program) where
  rewrite : Checked limits validation baseline
  schema : Schema
  distinct : schema.zero ≠ schema.succ
  entries : List (Entry (context validation baseline) (context validation rewrite.program) schema)
  coverage : entries.map (·.summary) = rewrite.summaries
  exported : Export validation baseline
  targetExported : Export validation rewrite.program
  sameFactory : exported.factoryAddress = targetExported.factoryAddress
  sameExport : exported.entryAddress = targetExported.entryAddress
  entry : Entry (context validation baseline) (context validation rewrite.program) schema
  entryMember : entry.summary ∈ rewrite.summaries
  entryAddress : entry.summary.owner = exported.entryAddress
  improvement : entry.beforeBody.isTwice = true

def certify (limits : Limits) (validation : Validate.Context) (baseline : Program)
    (summaries : List Summary) (policy : Policy := {}) :
    Except Rejection (Certificate limits validation baseline) := do
  let rewrite ← (Borrow.check limits validation baseline summaries).mapError Rejection.rewrite
  let some schema := inferSchema baseline | throw .schema
  if distinct : schema.zero ≠ schema.succ then
    let some exported := checkExport validation baseline | throw .export
    let some targetExported := checkExport validation rewrite.program | throw .export
    let some entries := summaries.mapM (checkEntry (context validation baseline)
        (context validation rewrite.program) schema policy.maxDepth) | throw .body
    if coverage : entries.map (·.summary) = rewrite.summaries then
      if sameFactory : exported.factoryAddress = targetExported.factoryAddress then
        if sameExport : exported.entryAddress = targetExported.entryAddress then
          let some entry := entries.find? (fun entry => entry.summary.owner == exported.entryAddress) | throw .export
          if entryAddress : entry.summary.owner = exported.entryAddress then
            if entryMember : entry.summary ∈ rewrite.summaries then
              if improvement : entry.beforeBody.isTwice = true then
                return ⟨rewrite, schema, distinct, entries, coverage, exported, targetExported,
                  sameFactory, sameExport, entry, entryMember, entryAddress, improvement⟩
              else throw .noImprovement
            else throw .coverage
          else throw .export
        else throw .export
      else throw .export
    else throw .coverage
  else throw .schema

structure Selection (limits : Limits) (validation : Validate.Context) (baseline : Program) where
  baselineChecked : Validate.Checked limits.validator validation baseline
  inference : Inference
  attempt : Except Rejection (Certificate limits validation baseline)

def optimize {limits : Limits} {validation : Validate.Context} {baseline : Program}
    (checked : Validate.Checked limits.validator validation baseline) (policy : Policy := {}) :
    Selection limits validation baseline :=
  if !policy.enabled then ⟨checked, {}, .error .disabled⟩ else
    let inference := infer limits validation baseline
    let attempt := if inference.summaries.isEmpty then .error .noCandidates
      else certify limits validation baseline inference.summaries policy
    ⟨checked, inference, attempt⟩

def Selection.program {limits validation baseline} (selection : Selection limits validation baseline) : Program :=
  match selection.attempt with
  | .ok certificate => certificate.rewrite.program
  | .error _ => baseline

theorem Selection.valid {limits validation baseline} (selection : Selection limits validation baseline) :
    Validate.ValidWith limits.validator validation selection.program := by
  cases h : selection.attempt with
  | error _ => simpa [Selection.program, h] using
      (show Validate.ValidWith limits.validator validation baseline from
        ⟨selection.baselineChecked.stats, selection.baselineChecked.accepted⟩)
  | ok certificate => simpa [Selection.program, h] using certificate.rewrite.valid

theorem Selection.fallbackExact {limits validation baseline} (selection : Selection limits validation baseline)
    {reason : Rejection} (fallback : selection.attempt = .error reason) : selection.program = baseline := by
  simp [Selection.program, fallback]

end Ix.Compiler.IxIR2.Borrow.Open
