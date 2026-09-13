import Compilatrix.X86.PhysicalHeapSelect
import Compilatrix.X86.HeapArena
import Compilatrix.X86.BlockSharing

namespace Compilatrix.X86.HeapTarget
open PhysicalHeap

def increment (field amount : Nat) : List Instr :=
  [.load .w64 .rcx (HeapArena.header field),
   .alu .add .w64 .rcx (.imm (UInt32.ofNat amount)), .store .w64 (HeapArena.header field) .rcx]

def decrement (field : Nat) : List Instr :=
  [.load .w64 .rcx (HeapArena.header field), .alu .sub .w64 .rcx (.imm 1),
   .store .w64 (HeapArena.header field) .rcx]

def setTag (tag : Word) : List Instr :=
  [.mov .w64 .rcx (.imm tag), .store .w64 (HeapArena.cellField 0) .rcx]

def fields (arguments : Array Scalar.Atom) : List Instr :=
  [Scalar.load .r8 (arguments[0]?.getD (.constant 0)),
   Scalar.load .r9 (arguments[1]?.getD (.constant 0))]

def writeCell (ctor : Constructor) : List Instr :=
  setTag ctor.tag ++ [.store .w64 (HeapArena.cellField 1) .r8,
    .store .w64 (HeapArena.cellField 2) .r9, .mov .w64 .rcx (.imm 0),
    .store .w64 (HeapArena.cellField 3) .rcx]

def reserveFields (count destination : Nat) : List Instr :=
  (List.range count).flatMap fun index =>
    [.load .w64 .rcx (HeapArena.cellField (index + 1)), .spill (Scalar.slot (destination + index)) .rcx]

def primitive : Primitive → List Instr
  | .nop => []
  | .move destination source => [Scalar.load .rax source, .spill (Scalar.slot destination) .rax]
  | .alloc _ ctor arguments destination =>
      fields arguments ++ [.load .w64 .rax (HeapArena.header 0), .alu .add .w64 .rax (.reg .r15),
        .alu .add .w64 .rax (.imm 128)] ++ writeCell ctor ++ increment 0 32 ++ increment 2 1 ++
        [.spill (Scalar.slot destination) .rax]
  | .fetch source field destination =>
      [Scalar.load .rax source, .load .w64 .rax (HeapArena.cellField (field + 1)), .spill (Scalar.slot destination) .rax]
  | .reserve world ctor source destination credit =>
      [Scalar.load .rax source] ++ reserveFields ctor.schema.fields.size destination ++ setTag 1 ++ increment 9 1 ++
        (if world == .shared then increment 6 1 ++ increment 7 1 else []) ++
        [.spill (Scalar.slot (creditBase + credit)) .rax]
  | .reuse _ ctor credit arguments destination =>
      fields arguments ++ [.reload .rax (Scalar.slot (creditBase + credit))] ++ writeCell ctor ++
        increment 4 1 ++ increment 8 ctor.schema.fields.size ++ decrement 9 ++ [.spill (Scalar.slot destination) .rax]
  | .release world source =>
      [Scalar.load .rax source] ++ setTag 0 ++ increment 3 1 ++
        (if world == .shared then increment 5 1 else [])
  | .discard credit =>
      [.reload .rax (Scalar.slot (creditBase + credit))] ++ setTag 0 ++ increment 3 1 ++ decrement 9

def copySourceInstructions : CopySource → List Instr
  | .atom source => [Scalar.load .rax source]
  | .predecessor source => [Scalar.load .rax source, .alu .sub .w64 .rax (.imm 1)]

def stageCopies (start : Nat) : List Copy → List Instr
  | [] => []
  | copy :: rest => copySourceInstructions copy.source ++ [.spill (Scalar.slot (scratchBase + start)) .rax] ++ stageCopies (start + 1) rest

def commitCopies (start : Nat) : List Copy → List Instr
  | [] => []
  | copy :: rest => [.reload .rax (Scalar.slot (scratchBase + start)), .spill (Scalar.slot copy.destination) .rax] ++
      commitCopies (start + 1) rest

def transfer (copies : Transfer) : List Instr := stageCopies 0 copies.copies.toList ++ commitCopies 0 copies.copies.toList

def copySourceValid : CopySource → Bool
  | .atom source | .predecessor source => source.valid scratchBase

def transferValid (transfer : Transfer) : Bool :=
  transfer.copies.size ≤ maxEdge && transfer.copies.all (fun copy => copySourceValid copy.source && copy.destination < scratchBase) &&
    decide (transfer.copies.toList.map (·.destination)).Nodup

def constructorValid (ctor : Constructor) : Bool := ctor.schema.fields.size ≤ 2 && 2 ≤ ctor.tag && ctor.tag < 34

def primitiveValid : Primitive → Bool
  | .nop => true
  | .move destination source => destination < maxValues && source.valid maxValues
  | .alloc _ ctor arguments destination =>
      constructorValid ctor && arguments.size == ctor.schema.fields.size && arguments.all (·.valid maxValues) && destination < maxValues
  | .fetch source field destination => source.valid maxValues && field < 2 && destination < maxValues
  | .reserve _ ctor source destination credit =>
      constructorValid ctor && source.valid maxValues && destination + ctor.schema.fields.size ≤ maxValues && credit < maxCredits
  | .reuse _ ctor credit arguments destination =>
      constructorValid ctor && credit < maxCredits && arguments.size == ctor.schema.fields.size && arguments.all (·.valid maxValues) && destination < maxValues
  | .release _ source => source.valid maxValues
  | .discard credit => credit < maxCredits

def arguments (target : BlockId) (operands : Array Scalar.Atom) : List Instr := Scalar.callInstructions target operands
def tailArguments (operands : Array Scalar.Atom) : List Instr :=
  [Scalar.load .rdi (operands[0]?.getD (.constant 0)), Scalar.load .rsi (operands[1]?.getD (.constant 0))]

inductive Plan where
  | ret (entry : BlockId) (kind : Kind) (value : Scalar.Atom)
  | primitive (entry : BlockId) (operation : Primitive) (next : Plan)
  | jump (entry : BlockId) (transfer : Transfer) (next : Plan)
  | branch (entry zeroEdge succEdge : BlockId) (value : Scalar.Atom)
      (zeroTransfer : Transfer) (zero : Plan) (succTransfer : Transfer) (successor : Plan)
  | call (entry : BlockId) (function : Nat) (arguments : Array Scalar.Atom) (destination : Nat) (next : Plan)
  | tailCall (entry : BlockId) (kind : Kind) (function : Nat) (arguments : Array Scalar.Atom)
  deriving Repr, Inhabited

def Plan.entry : Plan → BlockId
  | .ret entry .. | .primitive entry .. | .jump entry .. | .branch entry .. | .call entry .. | .tailCall entry .. => entry

def Plan.tree : Plan → Tree
  | .ret _ kind value => .ret kind value
  | .primitive _ operation next => .primitive operation next.tree
  | .jump _ transfer next => .jump transfer next.tree
  | .branch _ _ _ value zeroTransfer zero succTransfer successor =>
      .branch value zeroTransfer zero.tree succTransfer successor.tree
  | .call _ function arguments destination next => .call function arguments destination next.tree
  | .tailCall _ kind function arguments => .tailCall kind function arguments

def Plan.matches (program : X86.Program) (entries : Array BlockId) (exit : BlockId) : Plan → Bool
  | .ret entry _ value => value.valid maxValues && Scalar.blockMatches program entry [Scalar.load .rax value] (.jump exit)
  | .primitive entry operation next =>
      primitiveValid operation && Scalar.blockMatches program entry (HeapTarget.primitive operation) (.jump next.entry) && next.matches program entries exit
  | .jump entry copies next =>
      transferValid copies && Scalar.blockMatches program entry (transfer copies) (.jump next.entry) && next.matches program entries exit
  | .branch entry zeroEdge succEdge value zeroTransfer zero succTransfer successor =>
      value.valid maxValues && transferValid zeroTransfer && transferValid succTransfer &&
      Scalar.blockMatches program entry [Scalar.load .rax value] (.branch Scalar.zeroCompare .eq zeroEdge succEdge) &&
      Scalar.blockMatches program zeroEdge (transfer zeroTransfer) (.jump zero.entry) &&
      Scalar.blockMatches program succEdge (transfer succTransfer) (.jump successor.entry) &&
      zero.matches program entries exit && successor.matches program entries exit
  | .call entry function operands destination next =>
      operands.size ≤ 2 && operands.all (·.valid maxValues) && destination < maxValues &&
      match entries[function]? with
      | none => false
      | some target => Scalar.blockMatches program entry (arguments target operands ++ [.spill (Scalar.slot destination) .rax])
          (.jump next.entry) && next.matches program entries exit
  | .tailCall entry _ function operands =>
      operands.size ≤ 2 && operands.all (·.valid maxValues) &&
      match entries[function]? with
      | none => false
      | some target => Scalar.blockMatches program entry (arguments target operands) (.jump exit)

structure FunctionPlan where
  entry : BlockId
  exit : BlockId
  body : Plan
  deriving Repr, Inhabited

def FunctionPlan.matches (program : X86.Program) (entries : Array BlockId) (parameters : Nat)
    (tree : Tree) (plan : FunctionPlan) : Bool :=
  plan.body.tree == tree && parameters ≤ 2 &&
    Scalar.blockMatches program plan.entry (Scalar.prologue parameters) (.jump plan.body.entry) &&
    Scalar.blockMatches program plan.exit Scalar.successInstructions .ret && plan.body.matches program entries plan.exit

private def emitTree (entries : Array BlockId) (exit : BlockId) : Tree → BlockSharing.Emit Plan
  | .ret kind value => return .ret (← BlockSharing.emit [Scalar.load .rax value] (.jump exit)) kind value
  | .primitive operation next => do
      let next ← emitTree entries exit next
      return .primitive (← BlockSharing.emit (HeapTarget.primitive operation) (.jump next.entry)) operation next
  | .jump copies next => do
      let next ← emitTree entries exit next
      return .jump (← BlockSharing.emit (transfer copies) (.jump next.entry)) copies next
  | .branch value zeroTransfer zero succTransfer successor => do
      let zero ← emitTree entries exit zero
      let successor ← emitTree entries exit successor
      let zeroEdge ← BlockSharing.emit (transfer zeroTransfer) (.jump zero.entry)
      let succEdge ← BlockSharing.emit (transfer succTransfer) (.jump successor.entry)
      let entry ← BlockSharing.emit [Scalar.load .rax value] (.branch Scalar.zeroCompare .eq zeroEdge succEdge)
      return .branch entry zeroEdge succEdge value zeroTransfer zero succTransfer successor
  | .call function operands destination next => do
      let some target := entries[function]? | throw "heap target callee is missing"
      let next ← emitTree entries exit next
      let entry ← BlockSharing.emit (arguments target operands ++ [.spill (Scalar.slot destination) .rax]) (.jump next.entry)
      return .call entry function operands destination next
  | .tailCall kind function operands => do
      let some target := entries[function]? | throw "heap target tail callee is missing"
      return .tailCall (← BlockSharing.emit (arguments target operands) (.jump exit)) kind function operands

private def emitFunction (entries : Array BlockId) (parameters : Nat) (tree : Tree) : BlockSharing.Emit FunctionPlan := do
  let exit ← BlockSharing.emit Scalar.successInstructions .ret
  let body ← emitTree entries exit tree
  return { entry := ← BlockSharing.emit (Scalar.prologue parameters) (.jump body.entry), exit, body }

/-- The dead source export closure is represented by a counter baseline.
The native arena starts with zero allocated cells; the prefix has no address
in that arena. Standalone physical CFGs use baseline zero. -/
def headerInit (baseline : Bool) : List Instr :=
  (List.range 10).filter (· != 1) |>.flatMap fun field =>
    [.mov .w64 .rcx (.imm (if baseline && (field == 2 || field == 3 || field == 5) then 1 else 0)),
      .store .w64 (HeapArena.header field) .rcx]

def adapter (baseline : Bool) (target : BlockId) : List Instr :=
  [.push .r15, .mov .w64 .r15 (.reg .rdx)] ++ headerInit baseline ++ [.call target, .pop .r15]

def rejectInstructions : List Instr := [.mov .w64 .rax (.imm 0), .mov .w64 .rdx (.imm 1)]
def capacityCompare (bound : Nat) : Compare := { width := .w64, left := .rax, right := .imm (UInt32.ofNat bound) }

structure EntryPlan where
  entry : BlockId
  lower : BlockId
  adapter : BlockId
  reject : BlockId
  deriving Repr, Inhabited

def EntryPlan.matches (program : X86.Program) (baseline : Bool) (target : BlockId) (demand : Nat)
    (plan : EntryPlan) : Bool :=
  Scalar.blockMatches program plan.entry [.load .w64 .rax (HeapArena.memory .rdx 1)]
    (.branch (capacityCompare HeapArena.capacity) .unsignedGt plan.reject plan.lower) &&
  Scalar.blockMatches program plan.lower [] (.branch (capacityCompare demand) .unsignedLt plan.reject plan.adapter) &&
  Scalar.blockMatches program plan.adapter (HeapTarget.adapter baseline target) .ret &&
  Scalar.blockMatches program plan.reject rejectInstructions .ret

def emitEntry (baseline : Bool) (target : BlockId) (demand : Nat) : BlockSharing.Emit EntryPlan := do
  let reject ← BlockSharing.emit rejectInstructions .ret
  let adapter ← BlockSharing.emit (HeapTarget.adapter baseline target) .ret
  let lower ← BlockSharing.emit [] (.branch (capacityCompare demand) .unsignedLt reject adapter)
  let entry ← BlockSharing.emit [.load .w64 .rax (HeapArena.memory .rdx 1)]
    (.branch (capacityCompare HeapArena.capacity) .unsignedGt reject lower)
  return { entry, lower, adapter, reject }

structure Output {schemas program root} (selected : PhysicalHeap.Selected schemas program root) (baseline : Bool) where
  target : X86.Checked
  plans : Array FunctionPlan
  size : plans.size = selected.rows.size
  entry : EntryPlan
  entryAt : target.program.entry = entry.entry
  verified : (plans.zip selected.rows).all (fun (plan, row) =>
    plan.matches target.program (plans.map (·.entry)) row.interface.parameters.size row.source.tree) = true
  entryVerified : entry.matches target.program baseline ((plans.map (·.entry))[selected.entry]?.getD 0)
    selected.entryInterface.allocations = true

/-- Object compilation strategies. `graph` additionally preserves selected
control-flow sharing and checks a graph certificate through `HeapGraph`.
The two tree-selection strategies retain their exact previous artifacts. -/
inductive Emission where
  | tree | shared | graph
  deriving BEq, DecidableEq, Repr, Inhabited

def Emission.policy : Emission → String
  | .tree => "heap-block-tree/1"
  | .shared => "heap-block-sharing/1"
  | .graph => "heap-cfg-graph/1"

/-- An untrusted emission proposal, also used for independent rechecking. -/
structure Candidate where
  blocks : Array Block
  plans : Array FunctionPlan
  entry : EntryPlan

def Candidate.program (candidate : Candidate) : X86.Program :=
  { blocks := candidate.blocks, entry := candidate.entry.entry }

def emitCandidate {schemas program root} (selected : PhysicalHeap.Selected schemas program root)
    (baseline : Bool := false) (emission : Emission := .tree) : Except String Candidate := do
  if emission == .graph then throw "graph emission requires HeapGraph.emitCandidate and checked graph selection"
  let ((plans, entry), state) ← (do
    let mut plans : Array FunctionPlan := #[]
    for row in selected.rows do
      plans := plans.push (← emitFunction (plans.map (·.entry)) row.interface.parameters.size row.source.tree)
    let entry ← emitEntry baseline ((plans.map (·.entry))[selected.entry]?.getD 0) selected.entryInterface.allocations
    return (plans, entry) : BlockSharing.Emit (Array FunctionPlan × EntryPlan)).run { sharing := emission == .shared }
  return { plans, entry, blocks := state.blocks }

/-- Check every use of every proposed block, including shared entries. This
retains the original instruction, simultaneous-copy, call, and arena-guard
obligations; interning does not bypass any of them. -/
def checkCandidate {schemas program root} (selected : PhysicalHeap.Selected schemas program root)
    (baseline : Bool) (candidate : Candidate) : Except String (Output selected baseline) := do
  let { blocks, plans, entry } := candidate
  let target ← (X86.Program.check { blocks, entry := entry.entry }).mapError reprStr
  if size : plans.size = selected.rows.size then
    if entryAt : target.program.entry = entry.entry then
      if verified : (plans.zip selected.rows).all (fun (plan, row) =>
          plan.matches target.program (plans.map (·.entry)) row.interface.parameters.size row.source.tree) = true then
        if entryVerified : entry.matches target.program baseline ((plans.map (·.entry))[selected.entry]?.getD 0)
            selected.entryInterface.allocations = true then
          return { target, plans, size, entry, entryAt, verified, entryVerified }
        else throw "heap target adapter certificate failed"
      else throw "heap target instruction/slot/control certificate failed"
    else throw "heap target entry changed"
  else throw "heap target function coverage is incomplete"

/-- A successful check certifies the exact proposed program, even when plan
entries coincide. It cannot silently substitute another emitted graph. -/
theorem checkCandidate_program {schemas program root}
    {selected : PhysicalHeap.Selected schemas program root} {baseline : Bool}
    {candidate : Candidate} {output : Output selected baseline}
    (accepted : checkCandidate selected baseline candidate = .ok output) :
    output.target.program = candidate.program := by
  unfold checkCandidate at accepted
  simp only [Program.check] at accepted
  split at accepted
  · simp only [Except.mapError, Except.bind, bind, pure] at accepted
    split at accepted
    · split at accepted
      · split at accepted
        · split at accepted
          · cases accepted
            rfl
          · contradiction
        · contradiction
      · contradiction
    · contradiction
  · contradiction

/-- Baseline emission, with its original exact artifact bytes. -/
def compile {schemas program root} (selected : PhysicalHeap.Selected schemas program root) (baseline : Bool := false) :
    Except String (Output selected baseline) := do
  checkCandidate selected baseline (← emitCandidate selected baseline .tree)

/-- Emit each identical native continuation once. The result has exactly the
same proof contract as `compile`, including arbitrary incoming edges. -/
def compileShared {schemas program root} (selected : PhysicalHeap.Selected schemas program root) (baseline : Bool := false) :
    Except String (Output selected baseline) := do
  checkCandidate selected baseline (← emitCandidate selected baseline .shared)

end Compilatrix.X86.HeapTarget
