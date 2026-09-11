import Ix.Compiler.X86.Scalar
import Ix.Compiler.X86.FrameExecution

namespace Ix.Compiler.X86.Scalar

def frameSize : FrameSize := ⟨16⟩
def frameBytes : Nat := 256
def frameStride : Nat := 34

def slot (index : Nat) : StackSlot := ⟨UInt16.ofNat index⟩

def load (destination : GPR) : Atom → Instr
  | .var index => .reload destination (slot index)
  | .constant value => .mov .w64 destination (.imm value)

def addInstructions (left right : Atom) : List Instr :=
  [load .rax left, load .rcx right, .mov .w64 .r10 (.reg .rax), .alu .add .w64 .rax (.reg .rcx)]

def carryCompare : Compare := { width := .w64, left := .rax, right := .reg .r10 }
def operandsCompare : Compare := { width := .w64, left := .rax, right := .reg .rcx }
def zeroCompare : Compare := { width := .w64, left := .rax, right := .imm 0 }
def failedCompare : Compare := { width := .w64, left := .rdx, right := .imm 0 }

def callInstructions (target : BlockId) (arguments : Array Atom) : List Instr :=
  [load .rdi (arguments[0]?.getD (.constant 0)),
   load .rsi (arguments[1]?.getD (.constant 0)), .call target]

def prologue (parameters : Nat) : List Instr :=
  [.push .rbp, .mov .w64 .rbp (.reg .rsp), .allocFrame frameSize] ++
    (if 0 < parameters then [.spill (slot 0) .rdi] else []) ++
    (if 1 < parameters then [.spill (slot 1) .rsi] else [])

def epilogue : List Instr := [.freeFrame frameSize, .pop .rbp]
def successInstructions : List Instr := [.mov .w64 .rdx (.imm 0)] ++ epilogue
def failureInstructions : List Instr := [.mov .w64 .rax (.imm 0), .mov .w64 .rdx (.imm 1)] ++ epilogue

/-- The plan retains all block labels needed by a structural certificate.
The checker reconstructs every instruction and continuation from this tree. -/
inductive Plan where
  | atom (entry : BlockId) (value : Atom)
  | add (entry : BlockId) (left right : Atom)
  | sub (entry underflow ordinary : BlockId) (left right : Atom)
  | letE (join : BlockId) (value body : Plan)
  | branch (entry : BlockId) (scrutinee : Atom) (zero successor : Plan)
  | call (entry : BlockId) (function : Nat) (arguments : Array Atom)
  deriving Repr, Inhabited

def Plan.expression : Plan → Expr
  | .atom _ value => .atom value
  | .add _ left right => .add left right
  | .sub _ _ _ left right => .sub left right
  | .letE _ value body => .letE value.expression body.expression
  | .branch _ scrutinee zero successor => .branch scrutinee zero.expression successor.expression
  | .call _ function arguments => .call function arguments

def Plan.entry : Plan → BlockId
  | .atom entry _ | .add entry _ _ | .sub entry _ _ _ _ |
    .branch entry _ _ _ | .call entry _ _ => entry
  | .letE _ value _ => value.entry

def blockMatches (program : X86.Program) (entry : BlockId) (instructions : List Instr)
    (terminator : Terminator) : Bool :=
  program.blocks[entry.toNat]? == some ⟨instructions.toArray, terminator⟩ && instructions.length < UInt32.size

theorem blockMatches_code {checked : X86.Checked} {entry : BlockId} {instructions : List Instr}
    {terminator : Terminator} (matched : blockMatches checked.program entry instructions terminator = true) :
    BlockCode checked entry instructions terminator := by
  simp only [blockMatches, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at matched
  exact ⟨matched.1, matched.2⟩

def Plan.matches (program : X86.Program) (entries : Array BlockId) :
    Plan → Nat → BlockId → BlockId → Bool
  | .atom entry value, _, success, _ => blockMatches program entry [load .rax value] (.jump success)
  | .add entry left right, _, success, failure =>
      blockMatches program entry (addInstructions left right)
        (.branch carryCompare .unsignedLt failure success)
  | .sub entry underflow ordinary left right, _, success, _ =>
      blockMatches program entry [load .rax left, load .rcx right]
        (.branch operandsCompare .unsignedLt underflow ordinary) &&
      blockMatches program underflow [.mov .w64 .rax (.imm 0)] (.jump success) &&
      blockMatches program ordinary [.alu .sub .w64 .rax (.reg .rcx)] (.jump success)
  | .letE join value body, locals, success, failure =>
      blockMatches program join [.spill (slot locals) .rax] (.jump body.entry) &&
      value.matches program entries locals join failure &&
      body.matches program entries (locals + 1) success failure
  | .branch entry scrutinee zero successor, locals, success, failure =>
      blockMatches program entry [load .rax scrutinee] (.branch zeroCompare .eq zero.entry successor.entry) &&
      zero.matches program entries locals success failure && successor.matches program entries locals success failure
  | .call entry function arguments, _, success, failure =>
      match entries[function]? with
      | none => false
      | some target => blockMatches program entry (callInstructions target arguments)
          (.branch failedCompare .ne failure success)

structure FunctionPlan where
  entry : BlockId
  success : BlockId
  failure : BlockId
  body : Plan
  deriving Repr, Inhabited

def FunctionPlan.matches (program : X86.Program) (entries : Array BlockId)
    (source : Function) (plan : FunctionPlan) : Bool :=
  plan.body.expression == source.body &&
  blockMatches program plan.entry (prologue source.parameters) (.jump plan.body.entry) &&
  blockMatches program plan.success successInstructions .ret &&
  blockMatches program plan.failure failureInstructions .ret &&
  plan.body.matches program entries source.parameters plan.success plan.failure

abbrev Emit := StateT (Array Block) (Except String)

def emit (instructions : List Instr) (terminator : Terminator) : Emit BlockId := do
  let blocks ← get
  if blocks.size + 1 >= UInt32.size then throw "scalar target exceeds the block-address range"
  set (blocks.push ⟨instructions.toArray, terminator⟩)
  return UInt32.ofNat blocks.size

def emitExpr (entries : Array BlockId) (locals : Nat) (success failure : BlockId) : Expr → Emit Plan
  | .atom value => return .atom (← emit [load .rax value] (.jump success)) value
  | .add left right => do
      let entry ← emit (addInstructions left right) (.branch carryCompare .unsignedLt failure success)
      return .add entry left right
  | .sub left right => do
      let underflow ← emit [.mov .w64 .rax (.imm 0)] (.jump success)
      let ordinary ← emit [.alu .sub .w64 .rax (.reg .rcx)] (.jump success)
      let entry ← emit [load .rax left, load .rcx right] (.branch operandsCompare .unsignedLt underflow ordinary)
      return .sub entry underflow ordinary left right
  | .letE value body => do
      let body ← emitExpr entries (locals + 1) success failure body
      let join ← emit [.spill (slot locals) .rax] (.jump body.entry)
      let value ← emitExpr entries locals join failure value
      return .letE join value body
  | .branch scrutinee zero successor => do
      let zero ← emitExpr entries locals success failure zero
      let successor ← emitExpr entries locals success failure successor
      let entry ← emit [load .rax scrutinee] (.branch zeroCompare .eq zero.entry successor.entry)
      return .branch entry scrutinee zero successor
  | .call function arguments => do
      let some target := entries[function]? | throw "scalar call is not an earlier function"
      return .call (← emit (callInstructions target arguments) (.branch failedCompare .ne failure success))
        function arguments

def emitFunction (entries : Array BlockId) (function : Function) : Emit FunctionPlan := do
  let success ← emit successInstructions .ret
  let failure ← emit failureInstructions .ret
  let body ← emitExpr entries function.parameters success failure function.body
  let entry ← emit (prologue function.parameters) (.jump body.entry)
  return { entry, success, failure, body }

structure Output (source : Checked) where
  target : X86.Checked
  plans : Array FunctionPlan
  size : plans.size = source.program.functions.size
  entry : target.program.entry = (plans.map (·.entry))[source.program.entry]?.getD 0
  verified : (plans.zip source.program.functions).all
    (fun (plan, function) => plan.matches target.program (plans.map (·.entry)) function) = true

def compile (source : Checked) : Except String (Output source) := do
  let (plans, blocks) ← ((source.program.functions.foldlM (fun plans function => do
    let plan ← emitFunction (plans.map (·.entry)) function
    return plans.push plan) #[] : Emit (Array FunctionPlan))).run #[]
  let target ← (X86.Program.check
    { blocks, entry := (plans.map (·.entry))[source.program.entry]?.getD 0 }).mapError reprStr
  if size : plans.size = source.program.functions.size then
    if entry : target.program.entry = (plans.map (·.entry))[source.program.entry]?.getD 0 then
      if verified : (plans.zip source.program.functions).all
          (fun (plan, function) => plan.matches target.program (plans.map (·.entry)) function) = true then
        return { target, plans, size, entry, verified }
      else throw "scalar target failed its structural instruction and control-flow certificate"
    else throw "scalar target entry mismatch"
  else throw "scalar function count mismatch"

end Ix.Compiler.X86.Scalar
