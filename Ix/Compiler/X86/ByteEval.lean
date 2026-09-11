import Ix.Compiler.X86.Decode
import Ix.Compiler.X86.Eval

/-! Local execution of independently decoded instructions with byte RIP and
the four condition flags read by the emitted branches. Memory permissions are
the existing per-byte local ISA model. Undefined IMUL sign/zero flags remain
unknown, so an unsupported use is explicit rather than silently assumed. -/

namespace Ix.Compiler.X86.ByteEval

structure Flags where
  carry : Option Bool := none
  zero : Option Bool := none
  sign : Option Bool := none
  overflow : Option Bool := none
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Flags.test (flags : Flags) : Condition → Option Bool
  | .eq => flags.zero
  | .ne => flags.zero.map not
  | .unsignedLt => flags.carry
  | .unsignedLe => do return (← flags.carry) || (← flags.zero)
  | .unsignedGt => do return !((← flags.carry) || (← flags.zero))
  | .unsignedGe => flags.carry.map not
  | .signedLt => do return (← flags.sign) ^^ (← flags.overflow)
  | .signedLe => do return ((← flags.sign) ^^ (← flags.overflow)) || (← flags.zero)
  | .signedGt => do return !(((← flags.sign) ^^ (← flags.overflow)) || (← flags.zero))
  | .signedGe => do return !((← flags.sign) ^^ (← flags.overflow))

def resultFlags (result : BitVec bits) (carry overflow : Bool) : Flags :=
  ⟨some carry, some (result == 0), some result.msb, some overflow⟩

def addFlags (left right : BitVec bits) : Flags :=
  resultFlags (left + right) (BitVec.uaddOverflow left right) (BitVec.saddOverflow left right)

def subFlags (left right : BitVec bits) : Flags :=
  resultFlags (left - right) (BitVec.usubOverflow left right) (BitVec.ssubOverflow left right)

def aluFlags (operation : AluOp) (width : Width) (left right : Word) : Flags :=
  let left := left.toBitVec.setWidth width.bits
  let right := right.toBitVec.setWidth width.bits
  match operation with
  | .add => addFlags left right
  | .sub => subFlags left right
  | .and => resultFlags (left &&& right) false false
  | .or => resultFlags (left ||| right) false false
  | .xor => resultFlags (left ^^^ right) false false

def mulFlags (width : MulWidth) (left right : Word) : Flags :=
  let overflow := BitVec.smulOverflow
    (left.toBitVec.setWidth width.width.bits) (right.toBitVec.setWidth width.width.bits)
  { carry := some overflow, overflow := some overflow }

def operand (source : Decode.Operand) (core : Core) : Word :=
  match source with
  | .reg register => core.readReg register
  | .imm value => value

structure State where
  core : Core
  rip : Word
  flags : Flags := {}

inductive Fault where
  | memory (fault : MemoryFault)
  | decode (rip : Word)
  | undefinedCondition (condition : Condition)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Arithmetic RIP addition wraps at 64 bits, as do effective addresses. -/
def relative (next : Word) (displacement : Imm32) : Word := next + signExtend32 displacement

def execute (decoded : Decode.Decoded) (state : State) : Except Fault State := do
  let core := state.core
  let next := state.rip + UInt64.ofNat decoded.length
  match decoded.operation with
  | .mov width destination source =>
      return { state with core := core.writeReg width destination (operand source core), rip := next }
  | .load width destination source =>
      let core ← (core.loadReg? width destination (source.eval core)).mapError Fault.memory
      return { state with core, rip := next }
  | .store width destination source =>
      let core ← (core.storeReg? width (destination.eval core) source).mapError Fault.memory
      return { state with core, rip := next }
  | .lea destination source =>
      return { state with core := core.setReg destination (source.eval core), rip := next }
  | .alu operation width destination source =>
      let left := core.readReg destination
      let right := operand source core
      return {
        core := core.writeReg width destination (operation.eval left right)
        rip := next, flags := aluFlags operation width left right }
  | .imul width destination source =>
      let left := core.readReg destination
      let right := core.readReg source
      return {
        core := core.writeReg width.width destination (left * right)
        rip := next, flags := mulFlags width left right }
  | .compare width left right =>
      return { state with
        rip := next
        flags := aluFlags .sub width (core.readReg left) (operand right core) }
  | .push source =>
      let stack := core.readReg .rsp - 8
      let memory ← (core.memory.write64? stack (core.readReg source)).mapError Fault.memory
      return { state with core := { core.setReg .rsp stack with memory }, rip := next }
  | .pop destination =>
      let stack := core.readReg .rsp
      let value ← (core.memory.read64? stack).mapError Fault.memory
      return { state with core := (core.setReg .rsp (stack + 8)).setReg destination value, rip := next }
  | .call displacement =>
      let stack := core.readReg .rsp - 8
      let memory ← (core.memory.write64? stack next).mapError Fault.memory
      return { state with core := { core.setReg .rsp stack with memory }, rip := relative next displacement }
  | .jump displacement => return { state with rip := relative next displacement }
  | .branch condition displacement =>
      match state.flags.test condition with
      | none => .error (.undefinedCondition condition)
      | some take => return { state with rip := if take then relative next displacement else next }
  | .ret =>
      let stack := core.readReg .rsp
      let target ← (core.memory.read64? stack).mapError Fault.memory
      return { state with core := core.setReg .rsp (stack + 8), rip := target }

def step (text : ByteArray) (textBase : Word) (state : State) : Except Fault State :=
  match Decode.decodeAt text (state.rip - textBase).toNat with
  | none => .error (.decode state.rip)
  | some decoded => execute decoded state

def run (text : ByteArray) (textBase : Word) : Nat → State → Except Fault State
  | 0, state => .ok state
  | fuel + 1, state => do
      let next ← step text textBase state
      run text textBase fuel next

end Ix.Compiler.X86.ByteEval
