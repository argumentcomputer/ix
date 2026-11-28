import IxCC.X86.Basic
import IxCC.X86.Table.Exec

/-!
# Executable local semantics for the typed x86-64 v0 fragment

The model is intentionally architectural where the first encoder bridge needs
it to be: fixed-width registers, little-endian byte memory, observable `rsp`
effects, call return slots, and normal/trap outcomes.  A PC is still a symbolic
block/operation pair.  Calls store its stable 64-bit structural token in the
modeled stack; the later layout proof relates that token to the encoded return
RIP.

Linear operations run their table row through `Op.exec`, the executor the
byte machine also uses. The typed machine has no flags: a row's semantics
observes only the flags it declares, and linear rows declare none. A branch
runs its producer row and tests the condition on the flags that row sets, as
`jcc` tests them; the producer defines every flag the condition reads
(`FusedOk`), so no flag value ever crosses a typed instruction boundary.

Runtime intrinsics are supplied as an explicit semantic parameter.  Their
result type can mutate memory and caller-saved registers only, so preservation
of the System V callee-saved set and `rsp` is structural rather than a promise
made by an opaque callback.

`misalignedCall`, `stackMismatch`, `corruptReturn`, and
`calleeSavedClobber` are compiler/ABI contract failures, not claims that the
processor raises corresponding architectural exceptions. A native refinement
must prove those cases unreachable. Likewise, a top-level `ret` is observed as
halt rather than executing the surrounding harness's return instruction.
-/

namespace IxCC.X86

def MoveSource.eval (source : MoveSource) (core : Core) : Word :=
  match source with
  | .reg register => core.readReg register
  | .imm value => value

def AluSource.eval (source : AluSource) (core : Core) : Word :=
  match source with
  | .reg register => core.readReg register
  | .imm value => signExtend32 value

/-- The mathematical meaning of a condition on the low `width` bits. The
row semantics is proved to agree with it (`ByteEval.condition_agrees`). -/
def Condition.holds (condition : Condition) (width : Width)
    (left right : Word) : Bool :=
  let leftUnsigned := width.truncate left
  let rightUnsigned := width.truncate right
  match condition with
  | .eq => leftUnsigned == rightUnsigned
  | .ne => leftUnsigned != rightUnsigned
  | .unsignedLt => decide (leftUnsigned < rightUnsigned)
  | .unsignedLe => decide (leftUnsigned ≤ rightUnsigned)
  | .unsignedGt => decide (leftUnsigned > rightUnsigned)
  | .unsignedGe => decide (leftUnsigned ≥ rightUnsigned)
  | .signedLt => decide (width.signedValue left < width.signedValue right)
  | .signedLe => decide (width.signedValue left ≤ width.signedValue right)
  | .signedGt => decide (width.signedValue left > width.signedValue right)
  | .signedGe => decide (width.signedValue left ≥ width.signedValue right)

/-- The flags a comparison produces: its `cmp` row, executed. -/
def Compare.flags (comparison : Compare) (core : Core) : ByteEval.Flags :=
  match comparison.row.1.exec comparison.row.2 core {} with
  | .ok (_, flags) => flags
  | .error _ => {}

/-- Whether a compare-and-branch is taken: the `cmp` row's flags, tested by
the condition exactly as the `jcc` row's semantics tests them. -/
def Compare.holds (comparison : Compare) (condition : Condition)
    (core : Core) : Bool :=
  ((comparison.flags core).test condition).getD false

/-- Symbolic instruction position.  Its encoding is a stable stack token, not
an emitted byte address; encoder correctness will relate the two. -/
structure PC where
  block : BlockId
  offset : UInt32
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def PC.encode (pc : PC) : Word :=
  (pc.block.toUInt64 <<< 32) ||| pc.offset.toUInt64

def PC.decode (word : Word) : PC :=
  { block := (word >>> 32).toUInt32
    offset := word.toUInt32 }

def PC.next? (pc : PC) : Option PC :=
  if pc.offset == (0xffffffff : UInt32) then
    none
  else
    some { pc with offset := pc.offset + 1 }

structure ReturnFrame where
  continuation : PC
  returnSlot : Word
  calleeSaved : Array Word
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive Trap where
  | invalidBlock (block : BlockId)
  | invalidOffset (pc : PC)
  | pcOverflow (pc : PC)
  | memoryFault (fault : MemoryFault)
  | misalignedCall (stack : Word)
  | stackMismatch (expected actual : Word)
  | corruptReturn (expected actual : Word)
  | calleeSavedClobber
  | intrinsicFailure (intrinsic : Intrinsic) (code : Nat)
  /-- A row's semantics faulted (for example by reading an undefined flag). -/
  | semantic (fault : SemFault)
  /-- An `unwind` reloaded a stack pointer that no active ghost frame returns
  to. -/
  | unwindMismatch (stack : Word)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive Status where
  | running
  | halted (result : Word)
  | trapped (fault : Trap)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Machine where
  core : Core
  pc : PC
  returns : List ReturnFrame
  status : Status

/-- An intrinsic can change memory, the result register, and caller-saved
registers.  There is no field through which it can mutate `rsp` or a
callee-saved register. -/
structure IntrinsicResult where
  memory : Memory
  result : Word
  clobber : GPR → Word

structure Runtime where
  invoke : Intrinsic → Array Word → Memory →
    Except Nat IntrinsicResult

def Runtime.rejecting : Runtime where
  invoke intrinsic _ _ := .error intrinsic.arity

def Core.calleeSavedSnapshot (core : Core) : Array Word :=
  SysV.calleeSaved.map core.readReg

def Core.calleeSavedMatch (core : Core) (snapshot : Array Word) : Bool :=
  core.calleeSavedSnapshot == snapshot

def Core.intrinsicArguments (core : Core) (intrinsic : Intrinsic) : Array Word :=
  (List.range intrinsic.arity).toArray.map fun index =>
    match SysV.argumentRegister? index with
    | some register => core.readReg register
    | none => 0

def Core.applyIntrinsicResult (core : Core)
    (result : IntrinsicResult) : Core :=
  { memory := result.memory
    registers := fun register =>
      if register == SysV.resultRegister then
        result.result
      else if SysV.isCallerSaved register then
        result.clobber register
      else
        core.readReg register }

/-- An atomic runtime call cannot change the architectural stack pointer. -/
@[simp] theorem Core.applyIntrinsicResult_rsp (core : Core)
    (result : IntrinsicResult) :
    (core.applyIntrinsicResult result).readReg .rsp = core.readReg .rsp := by
  simp [Core.applyIntrinsicResult, Core.readReg, SysV.isCallerSaved,
    SysV.callerSaved, SysV.resultRegister]

/-- An atomic runtime call preserves the complete System V callee-saved
snapshot by construction. -/
@[simp] theorem Core.applyIntrinsicResult_calleeSaved (core : Core)
    (result : IntrinsicResult) :
    (core.applyIntrinsicResult result).calleeSavedSnapshot =
      core.calleeSavedSnapshot := by
  simp [Core.calleeSavedSnapshot, SysV.calleeSaved,
    Core.applyIntrinsicResult, Core.readReg, SysV.isCallerSaved,
    SysV.callerSaved, SysV.resultRegister]

def Machine.trap (machine : Machine) (fault : Trap) : Machine :=
  { machine with status := .trapped fault }

def Machine.advanceWith (machine : Machine) (core : Core) : Machine :=
  match machine.pc.next? with
  | none => machine.trap (.pcOverflow machine.pc)
  | some next => { machine with core, pc := next }

def Machine.goto (checked : Checked) (machine : Machine)
    (target : BlockId) : Machine :=
  if checked.program.hasBlock target then
    { machine with pc := { block := target, offset := 0 } }
  else
    machine.trap (.invalidBlock target)

/-- The typed outcome of a row: advance with its core, or trap. -/
def Machine.afterRow (machine : Machine) :
    Except ExecFault (Core × ByteEval.Flags) → Machine
  | .ok (core, _) => machine.advanceWith core
  | .error (.memory fault) => machine.trap (.memoryFault fault)
  | .error (.semantic fault) => machine.trap (.semantic fault)

/-- The ghost frames kept when execution resumes with stack pointer `sp`:
every frame at depth 0; otherwise the frames outside the
first one whose return slot is `sp − 8`, which is the frame the reloaded
stack returns through. `none` when no frame matches. -/
def cutAt (sp : Word) : List ReturnFrame → Option (List ReturnFrame)
  | [] => some []
  | frames => (frames.findIdx? (·.returnSlot + 8 == sp)).map fun index => frames.drop (index + 1)

def executeInstr (runtime : Runtime) (checked : Checked)
    (instruction : Instr) (machine : Machine) : Machine :=
  let core := machine.core
  match instruction with
  | .op o args => machine.afterRow (o.exec args core {})
  | .fused producer pargs consumer cargs =>
      match producer.exec pargs core {} with
      | .error fault => machine.afterRow (.error fault)
      | .ok (core, flags) => machine.afterRow (consumer.exec cargs core flags)
  | .unwind source =>
      match unwindRow.exec [.reg .rsp, .mem source] core {} with
      | .error fault => machine.afterRow (.error fault)
      | .ok (core, _) =>
          match cutAt (core.readReg .rsp) machine.returns with
          | none => machine.trap (.unwindMismatch (core.readReg .rsp))
          | some returns => { machine.advanceWith core with returns }
  | .call target =>
      if !SysV.callSiteAligned (core.readReg .rsp) then
        machine.trap (.misalignedCall (core.readReg .rsp))
      else if checked.program.hasBlock target then
        match machine.pc.next? with
        | none => machine.trap (.pcOverflow machine.pc)
        | some continuation =>
            let stack := core.readReg .rsp - 8
            match core.memory.write64? stack continuation.encode with
            | .error fault => machine.trap (.memoryFault fault)
            | .ok memory =>
                let frame : ReturnFrame :=
                  { continuation
                    returnSlot := stack
                    calleeSaved := core.calleeSavedSnapshot }
                let called := { core.setReg .rsp stack with memory }
                { machine with
                  core := called
                  pc := { block := target, offset := 0 }
                  returns := frame :: machine.returns }
      else
        machine.trap (.invalidBlock target)
  | .callRuntime intrinsic =>
      if !SysV.callSiteAligned (core.readReg .rsp) then
        machine.trap (.misalignedCall (core.readReg .rsp))
      else
        match runtime.invoke intrinsic (core.intrinsicArguments intrinsic)
            core.memory with
        | .error code => machine.trap (.intrinsicFailure intrinsic code)
        | .ok result => machine.advanceWith (core.applyIntrinsicResult result)

def executeTerminator (checked : Checked) (terminator : Terminator)
    (machine : Machine) : Machine :=
  let core := machine.core
  match terminator with
  | .jump target => machine.goto checked target
  | .branch producer args condition ifTrue ifFalse _ =>
      match producer.exec args core {} with
      | .error fault => machine.afterRow (.error fault)
      | .ok (core, flags) =>
          match flags.test condition with
          | none => machine.trap (.semantic (.undefinedCondition condition))
          | some taken => { machine with core }.goto checked (if taken then ifTrue else ifFalse)
  | .tailCall target => machine.goto checked target
  | .ret =>
      match machine.returns with
      | [] => { machine with status := .halted (core.readReg .rax) }
      | frame :: returns =>
          let stack := core.readReg .rsp
          if stack != frame.returnSlot then
            machine.trap (.stackMismatch frame.returnSlot stack)
          else
            match core.memory.read64? stack with
            | .error fault => machine.trap (.memoryFault fault)
            | .ok actual =>
                let expected := frame.continuation.encode
                if actual != expected then
                  machine.trap (.corruptReturn expected actual)
                else if !core.calleeSavedMatch frame.calleeSaved then
                  machine.trap .calleeSavedClobber
                else
                  { machine with
                    core := core.setReg .rsp (stack + 8)
                    pc := frame.continuation
                    returns }

def Machine.initial (checked : Checked) (core : Core) : Machine :=
  { core
    pc := { block := checked.program.entry, offset := 0 }
    returns := []
    status := .running }

/-- One target step.  A block's terminator occupies the position immediately
after its instruction array. -/
def step (runtime : Runtime) (checked : Checked)
    (machine : Machine) : Machine :=
  match machine.status with
  | .halted _ | .trapped _ => machine
  | .running =>
      match checked.program.blocks[machine.pc.block.toNat]? with
      | none => machine.trap (.invalidBlock machine.pc.block)
      | some block =>
          match block.instructions[machine.pc.offset.toNat]? with
          | some instruction => executeInstr runtime checked instruction machine
          | none =>
              if machine.pc.offset.toNat == block.instructions.size then
                executeTerminator checked block.terminator machine
              else
                machine.trap (.invalidOffset machine.pc)

def run (runtime : Runtime) (checked : Checked) : Nat → Machine → Machine
  | 0, machine => machine
  | fuel + 1, machine =>
      let next := step runtime checked machine
      match next.status with
      | .running => run runtime checked fuel next
      | .halted _ | .trapped _ => next

def runFrom (runtime : Runtime) (checked : Checked) (fuel : Nat)
    (core : Core) : Machine :=
  run runtime checked fuel (Machine.initial checked core)

/-- Finished target states are stable under a further local step. -/
theorem step_of_not_running (runtime : Runtime) (checked : Checked)
    (machine : Machine) (notRunning : machine.status ≠ .running) :
    step runtime checked machine = machine := by
  cases status : machine.status with
  | running => exact False.elim (notRunning status)
  | halted result => simp [step, status]
  | trapped fault => simp [step, status]

end IxCC.X86
