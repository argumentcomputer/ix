import Compilatrix.X86.Decode
import Compilatrix.X86.Eval

/-! Local execution of independently decoded instructions with byte RIP and
the four condition flags read by the emitted branches. Linear rows run the
table's executor `Op.exec` on the machine's flags, exactly the executor and
semantic function the typed machine uses; control rows move RIP and the
stack. Memory permissions are the per-byte local model. Undefined flags
(IMUL's SF and ZF) stay unknown, so an unsupported read is a fault rather
than a guess. -/

namespace Compilatrix.X86

namespace Decode.Operation

/-- `call rel32` with a displacement's 32-bit pattern. -/
def call (displacement : Imm32) : Operation := .op Op.callRel32 [.imm (signExtend32 displacement)]
/-- `jmp rel32`. -/
def jump (displacement : Imm32) : Operation := .op Op.jmpRel32 [.imm (signExtend32 displacement)]
/-- `jcc rel32`. -/
def branch (condition : Condition) (displacement : Imm32) : Operation :=
  .op (Op.jccRel32 condition) [.imm (signExtend32 displacement)]
/-- `ret`. -/
def ret : Operation := .op Op.retZO []

end Decode.Operation

namespace ByteEval

structure State where
  core : Core
  rip : Word
  flags : Flags := {}

inductive Fault where
  | memory (fault : MemoryFault)
  | decode (rip : Word)
  | undefinedCondition (condition : Condition)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Fault.ofExec : ExecFault → Fault
  | .memory fault => .memory fault
  | .semantic (.undefinedCondition condition) => .undefinedCondition condition

/-- Arithmetic RIP addition wraps at 64 bits, as do effective addresses. -/
def relative (next : Word) (displacement : Imm32) : Word := next + signExtend32 displacement

/-- Execute one decoded row. Control rows use their canonical rel32 value;
a conditional row asks its semantics whether it is taken. -/
def execute (decoded : Decode.Decoded) (state : State) : Except Fault State := do
  let core := state.core
  let next := state.rip + UInt64.ofNat decoded.length
  match decoded.operation with
  | .op o args =>
    match o.mn, args with
    | .call, [.imm displacement] =>
        let stack := core.readReg .rsp - 8
        let memory ← (core.memory.write64? stack next).mapError Fault.memory
        return { state with core := { core.setReg .rsp stack with memory }, rip := next + displacement }
    | .jmp, [.imm displacement] => return { state with rip := next + displacement }
    | .jcc _, [.imm displacement] =>
        let out ← ((desc o).sem ⟨[displacement], state.flags.restrict (desc o).flagsIn⟩).mapError
          (Fault.ofExec ∘ ExecFault.semantic)
        return { state with rip := if out.taken == some true then next + displacement else next }
    | .ret, [] =>
        let stack := core.readReg .rsp
        let target ← (core.memory.read64? stack).mapError Fault.memory
        return { state with core := core.setReg .rsp (stack + 8), rip := target }
    | _, _ =>
        let (core, flags) ← (o.exec args core state.flags).mapError Fault.ofExec
        return { core, rip := next, flags }

def step (text : ByteArray) (textBase : Word) (state : State) : Except Fault State :=
  match Decode.decodeAt text (state.rip - textBase).toNat with
  | none => .error (.decode state.rip)
  | some decoded => execute decoded state

def run (text : ByteArray) (textBase : Word) : Nat → State → Except Fault State
  | 0, state => .ok state
  | fuel + 1, state => do
      let next ← step text textBase state
      run text textBase fuel next

end ByteEval
end Compilatrix.X86
