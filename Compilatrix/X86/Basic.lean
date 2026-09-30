import Compilatrix.X86.Table.Rows

/-!
# Typed x86-64 v0 target syntax

This is the proof-facing target boundary for the first native wedge. Every
non-control instruction is one row of the instruction table (`X86.Table`)
applied to operands of that row's slot kinds; validation checks the row and
the operands. Branch and call destinations are bounded symbolic block
identifiers, and byte layout and relocation belong to the encoder and object
layer.

A branch terminator owns the row that produces its flags (a `cmp` or
`test` in any operand form, or `add`/`sub` for carry and borrow), and a
fused instruction pairs a producer with a flag-reading row (`setcc`,
`cmovcc`). This keeps EFLAGS local by construction while the encoder emits
the usual producer/consumer pairs. Memory operands separate index registers
from general registers, excluding the x86 `rsp`-as-index encoding hole by
type.

The former per-form constructors (`mov`, `load`, `alu`, `spill`, ...) remain
as definitions choosing a row; they are how programs are written.
-/

namespace Compilatrix.X86

/-- Target operations. A linear operation is one table row; `call` and
`callRuntime` are control rows with symbolic targets. There is no arbitrary
runtime symbol, no indirect call and no raw byte escape hatch. -/
inductive Instr where
  | op (o : Op) (args : List Arg)
  /-- A flag producer (`cmp`, `test`) and a flag consumer (`setcc`,
  `cmovcc`) as one typed instruction: the producer's flags exist only
  between the two rows, which the encoder emits back to back. -/
  | fused (producer : Op) (pargs : List Arg) (consumer : Op) (cargs : List Arg)
  | call (target : BlockId)
  | callRuntime (intrinsic : Intrinsic)
  /-- The failure exit: `mov rsp, [source]` (the `mov r64, r/m64` row), after
  which the typed machine drops the ghost return frames the reloaded stack
  pointer has left (`cutAt`). Only an export wrapper's exit group uses it. -/
  | unwind (source : MemAddr)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- How a branch's false edge is encoded (05 §7): `rel32` is a `jmp rel32`
after the `jcc`; `fall` is no bytes, since the false target is the next
block in the text. The typed semantics ignores it; E2's stream check
(`terminatorMatches`) requires a `fall` target to start where the `jcc`
ends. -/
inductive Reach where
  | fall
  | rel32
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Control operations close a target block. A conditional branch owns the
row that produces its flags (`cmp` or `test` in any operand form, or `add`
and `sub` for carry and borrow), so no other operation can consume stale
EFLAGS: flags exist only inside the terminator. A branch's `ifFalse` edge
carries its encoding (`Reach`): `rel32` unless layout sets `fall`. A
pattern that omits it matches `rel32` only. -/
inductive Terminator where
  | jump (target : BlockId)
  | branch (producer : Op) (args : List Arg) (condition : Condition)
      (ifTrue ifFalse : BlockId) (falseReach : Reach := .rel32)
  | tailCall (target : BlockId)
  | ret
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Block where
  instructions : Array Instr
  terminator : Terminator
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Blocks form one linked target text world.  Function symbols and local
labels both resolve to block IDs before this semantics, but byte offsets do
not: instruction encoding remains a separate pass. -/
structure Program where
  blocks : Array Block
  entry : BlockId
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-! ## Choosing rows -/

/-- Scale bits have no effect without an index; drop them. -/
def MemAddr.normalize (address : MemAddr) : MemAddr :=
  { address with scale := if address.index.isSome then address.scale else .one }

def AluOp.mnemonic : AluOp → Mnemonic
  | .add => .add
  | .sub => .sub
  | .and => .and
  | .or => .or
  | .xor => .xor

/-- Whether an imm8 field, sign-extended, has the same low `width` bits. -/
def fitsImm8 (width : Width) (value : Word) : Bool :=
  width != .w8 && width.truncate (ImmKind.imm8.norm value) == width.truncate value

/-- An ALU or compare row with an immediate operand: `op r/m, imm8` (83 /d)
when the value sign-extends from a byte, otherwise the full-size form.
`value` is the immediate's sign-extended 64-bit value; only its low `width`
bits matter. -/
def aluImmRow (mn : Mnemonic) (width : Width) (target : Arg) (value : Word) : Op × List Arg :=
  if fitsImm8 width value then
    ({ mn, w := width, form := .MI8 }, [target, .imm (ImmKind.imm8.norm value)])
  else
    ({ mn, w := width, form := .MI }, [target, .imm ((Table.fullImm width).norm value)])

/-- `mov r, imm`, choosing the shortest row: a 64-bit value that fits in 32
unsigned bits uses the zero-extending `mov r32, imm32` (B8+r), one that
sign-extends from 32 bits uses `mov r/m64, imm32` (C7 /0), and any other
uses `movabs` (REX.W B8+r). -/
def movImmRow (width : Width) (destination : GPR) (value : Word) : Op × List Arg :=
  match width with
  | .w64 =>
      if value.toNat < 2 ^ 32 then
        ({ mn := .mov, w := .w32, form := .OI }, [.reg destination, .imm (ImmKind.imm32.norm value)])
      else if ImmKind.imm32.norm value == value then
        ({ mn := .mov, w := .w64, form := .MI }, [.reg destination, .imm value])
      else
        ({ mn := .mov, w := .w64, form := .OI }, [.reg destination, .imm value])
  | width => ({ mn := .mov, w := width, form := .OI }, [.reg destination, .imm ((Table.moveImm width).norm value)])

/-- The row a comparison executes. -/
def Compare.row (comparison : Compare) : Op × List Arg :=
  match comparison.right with
  | .reg right => ({ mn := .cmp, w := comparison.width, form := .MR }, [.reg comparison.left, .reg right])
  | .imm value => aluImmRow .cmp comparison.width (.reg comparison.left) (signExtend32 value)

/-- The row an `unwind` executes: `mov r64, r/m64` (REX.W 8B /r) with `rsp` as
its destination. -/
def unwindRow : Op := { mn := .mov, w := .w64, form := .RM }

/-- Compare-and-branch: the comparison's `cmp` row produces the flags. -/
def Terminator.compare (comparison : Compare) (condition : Condition) (ifTrue ifFalse : BlockId) : Terminator :=
  .branch comparison.row.1 comparison.row.2 condition ifTrue ifFalse

namespace Instr

def ofRow (row : Op × List Arg) : Instr := .op row.1 row.2

/-- `mov r, r` or `mov r, imm`. -/
def mov (width : Width) (destination : GPR) : MoveSource → Instr
  | .reg source => .op { mn := .mov, w := width, form := .MR } [.reg destination, .reg source]
  | .imm value => ofRow (movImmRow width destination value)

/-- Narrow loads zero-extend (`movzx`); w32 follows the architectural
zero-extension rule and w64 is a normal move. -/
def load (width : Width) (destination : GPR) (source : MemAddr) : Instr :=
  match width with
  | .w8 => .op { mn := .movzx, w := .w32, form := .RM, src := .w8 } [.reg destination, .mem source.normalize]
  | .w16 => .op { mn := .movzx, w := .w32, form := .RM, src := .w16 } [.reg destination, .mem source.normalize]
  | .w32 => .op { mn := .mov, w := .w32, form := .RM } [.reg destination, .mem source.normalize]
  | .w64 => .op { mn := .mov, w := .w64, form := .RM } [.reg destination, .mem source.normalize]

def store (width : Width) (destination : MemAddr) (source : GPR) : Instr :=
  .op { mn := .mov, w := width, form := .MR } [.mem destination.normalize, .reg source]

def lea (destination : GPR) (source : MemAddr) : Instr :=
  .op { mn := .lea, w := .w64, form := .RM } [.reg destination, .mem source.normalize]

/-- `op r, r` or `op r, imm`; the immediate is sign-extended at width 64. -/
def alu (operation : AluOp) (width : Width) (destination : GPR) : AluSource → Instr
  | .reg source =>
      .op { mn := operation.mnemonic, w := width, form := .MR } [.reg destination, .reg source]
  | .imm value => ofRow (aluImmRow operation.mnemonic width (.reg destination) (signExtend32 value))

def imul (width : MulWidth) (destination source : GPR) : Instr :=
  .op { mn := .imul, w := width.width, form := .RM } [.reg destination, .reg source]

/-- `imul r, r, imm`: 6B with an imm8 when the value sign-extends from a
byte, otherwise 69 with the full-size immediate. -/
def imulImm (width : MulWidth) (destination source : GPR) (value : Imm32) : Instr :=
  if fitsImm8 width.width (signExtend32 value) then
    .op { mn := .imul, w := width.width, form := .RMI8 }
      [.reg destination, .reg source, .imm (ImmKind.imm8.norm (signExtend32 value))]
  else
    .op { mn := .imul, w := width.width, form := .RMI }
      [.reg destination, .reg source, .imm ((Table.fullImm width.width).norm (signExtend32 value))]

def push (source : GPR) : Instr := .op { mn := .push, w := .w64, form := .O } [.reg source]
def pop (destination : GPR) : Instr := .op { mn := .pop, w := .w64, form := .O } [.reg destination]

/-- `sub rsp, size`. -/
def allocFrame (size : FrameSize) : Instr := ofRow (aluImmRow .sub .w64 (.reg .rsp) size.bytes)
/-- `add rsp, size`. -/
def freeFrame (size : FrameSize) : Instr := ofRow (aluImmRow .add .w64 (.reg .rsp) size.bytes)

end Instr

/-- A spill slot's address `[rbp - 8(i+1)]`. -/
def spillAddress (slot : StackSlot) : MemAddr :=
  { base := some .rbp
    displacement := (0 - slot.displacement).toUInt32 }

namespace Instr

def spill (slot : StackSlot) (source : GPR) : Instr := store .w64 (spillAddress slot) source
def reload (destination : GPR) (slot : StackSlot) : Instr := load .w64 destination (spillAddress slot)

end Instr

/-! ## Closed-fragment theorem -/

/-- A vocabulary wider than the v0 AST, used to state what remains excluded. -/
inductive Form where
  | move | load | store | address | arithmetic | multiply
  | shift | conditionSet | conditionalMove | scalarDivision
  | stack | spill | reload | directCall | runtimeCall
  | jump | compareBranch | tailCall | ret
  | float | simd | atomic | indirectCall | syscall | tls
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- The reviewed sequential v0 emitted fragment. Unsigned scalar division
(`div`, with its `#DE` precondition) joined it with the Phase 1 rows. -/
def Form.InV0 : Form → Prop
  | .move | .load | .store | .address | .arithmetic | .multiply
  | .shift | .conditionSet | .conditionalMove | .scalarDivision
  | .stack | .spill | .reload | .directCall | .runtimeCall
  | .jump | .compareBranch | .tailCall | .ret => True
  | .float | .simd | .atomic | .indirectCall | .syscall | .tls => False

/-- The fragment vocabulary of a table mnemonic. The table has no
floating-point, vector, atomic, indirect-call, system-call or TLS rows. -/
def Mnemonic.form : Mnemonic → Form
  | .add | .or | .and | .sub | .xor | .cmp | .test => .arithmetic
  | .shl | .shr | .sar => .shift
  | .mov => .move
  | .movzx => .load
  | .lea => .address
  | .imul => .multiply
  | .div => .scalarDivision
  | .setcc _ => .conditionSet
  | .cmovcc _ => .conditionalMove
  | .push | .pop => .stack
  | .call => .directCall
  | .jmp => .jump
  | .jcc _ => .compareBranch
  | .ret => .ret

def Instr.form : Instr → Form
  | .op o _ => o.mn.form
  | .fused _ _ consumer _ => consumer.mn.form
  | .call .. => .directCall
  | .callRuntime .. => .runtimeCall
  | .unwind .. => .stack

def Terminator.form : Terminator → Form
  | .jump .. => .jump
  | .branch .. => .compareBranch
  | .tailCall .. => .tailCall
  | .ret => .ret

/-- The table's mnemonics are all inside the v0 fragment. -/
theorem Mnemonic.inV0 (mn : Mnemonic) : mn.form.InV0 := by
  cases mn <;> trivial

/-- Unsupported ISA forms cannot be constructed as v0 instructions. -/
theorem Instr.inV0 (instruction : Instr) : instruction.form.InV0 := by
  cases instruction with
  | op o args => exact o.mn.inV0
  | fused producer pargs consumer cargs => exact consumer.mn.inV0
  | call target => trivial
  | callRuntime intrinsic => trivial
  | unwind source => trivial

/-- Unsupported ISA forms cannot be constructed as v0 terminators. -/
theorem Terminator.inV0 (terminator : Terminator) : terminator.form.InV0 := by
  cases terminator <;> trivial

def Block.InV0 (block : Block) : Prop :=
  (∀ instruction ∈ block.instructions, instruction.form.InV0) ∧
    block.terminator.form.InV0

def Program.InV0 (program : Program) : Prop :=
  ∀ block ∈ program.blocks, block.InV0

/-- Fragment containment is structural: validation cannot widen the emitted
ISA because the target AST has no constructor for an excluded form. -/
theorem Program.inV0 (program : Program) : program.InV0 := by
  intro block blockMember
  constructor
  · intro instruction instructionMember
    exact instruction.inV0
  · exact block.terminator.inV0

/-! ## Validation -/

def Program.hasBlock (program : Program) (target : BlockId) : Bool :=
  decide (target.toNat < program.blocks.size)

def Instr.targetsValid (program : Program) : Instr → Bool
  | .call target => program.hasBlock target
  | _ => true

def Terminator.targetsValid (program : Program) : Terminator → Bool
  | .jump target | .tailCall target => program.hasBlock target
  | .branch _ _ _ ifTrue ifFalse _ =>
      program.hasBlock ifTrue && program.hasBlock ifFalse
  | .ret => true

def Block.targetsValid (program : Program) (block : Block) : Bool :=
  block.instructions.all (Instr.targetsValid program) &&
    block.terminator.targetsValid program

def Block.offsetsFit (block : Block) : Bool :=
  decide (block.instructions.size < 2 ^ 32)

/-- A linear operation is a listed, non-control row with operands of its
slot kinds. A fused pair is a listed producer that reads no flags and
writes nothing but flags (`flagsOnly`), and a listed flag consumer whose
flags the producer sets (`FusedOk`). An `unwind`'s source is a canonical
address for the `mov r64, r/m64` row. -/
def Instr.wellFormed : Instr → Bool
  | .op o args => Op.rows.contains o && o.linear && o.argsOk args
  | .fused producer pargs consumer cargs =>
      Op.rows.contains producer && producer.linear && (desc producer).flagsIn.isEmpty && producer.flagsOnly &&
        producer.argsOk pargs && Op.rows.contains consumer && consumer.consumer && consumer.argsOk cargs &&
        FusedOk producer consumer
  | .unwind source => unwindRow.argsOk [.reg .rsp, .mem source]
  | .call _ | .callRuntime _ => true

def Block.instructionsValid (block : Block) : Bool :=
  block.instructions.all Instr.wellFormed

/-- A branch's producer is a listed linear row that reads no flags, with
operands of its slot kinds, and it sets every flag the condition reads
(`FusedOk` with the `jcc` row). -/
def Terminator.wellFormed : Terminator → Bool
  | .branch producer args condition _ _ _ =>
      Op.rows.contains producer && producer.linear && (desc producer).flagsIn.isEmpty &&
        producer.argsOk args && FusedOk producer (Op.jccRel32 condition)
  | .jump _ | .tailCall _ | .ret => true

def Program.wellFormed (program : Program) : Bool :=
  !program.blocks.isEmpty &&
    decide (program.blocks.size < 2 ^ 32) &&
    program.hasBlock program.entry &&
    program.blocks.all fun block =>
      block.offsetsFit && block.targetsValid program && block.instructionsValid &&
        block.terminator.wellFormed

structure Checked where
  program : Program
  valid : program.wellFormed = true

inductive ValidationError where
  | malformedControl
  | malformedInstruction
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Program.check (program : Program) : Except ValidationError Checked :=
  if valid : program.wellFormed = true then
    .ok ⟨program, valid⟩
  else if program.blocks.all Block.instructionsValid then
    .error .malformedControl
  else
    .error .malformedInstruction

/-- Validation adds control-bounds evidence but cannot change the closed ISA
fragment established by the typed program. -/
theorem Checked.inV0 (checked : Checked) : checked.program.InV0 :=
  checked.program.inV0

end Compilatrix.X86
