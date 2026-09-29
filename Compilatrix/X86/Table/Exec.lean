import Compilatrix.X86.Table.Rows

/-!
# Executing a table row

`Op.exec` is the one executor of linear rows. It reads the row's input
slots (and an implicitly popped word), applies the row's semantic function
to them and to the flags the row declares in `flagsIn`, pushes or pops
through `rsp`, and writes the results back to the output slots with the
architectural partial-register rule (`Core.writeReg`). The typed machine
calls it with undefined flags; the byte machine calls it with its current
flags and keeps the merged result. Because a linear row declares no input
flags, both machines compute the same core.

`Op.reads` and `Op.writes` describe the memory the row touches, derived
from its memory slots and stack effect.
-/

namespace Compilatrix.X86

/-- A slot operand's value: a full register word, `width` little-endian
bytes of memory, or the canonical immediate. -/
def Arg.load (core : Core) (width : Width) : Arg → Except MemoryFault Word
  | .reg register => .ok (core.readReg register)
  | .mem address => core.memory.read? width (address.eval core)
  | .imm value => .ok value

/-- The effective address of a memory operand (`lea`). -/
def Arg.address (core : Core) : Arg → Word
  | .mem address => address.eval core
  | .reg register => core.readReg register
  | .imm value => value

/-- Write a slot operand. Effective addresses use the state before the
instruction; register writes follow the width's partial-write rule. -/
def Arg.store (before : Core) (width : Width) (value : Word) (core : Core) :
    Arg → Except MemoryFault Core
  | .reg register => .ok (core.writeReg width register value)
  | .mem address => do
      let memory ← core.memory.write? width (address.eval before) value
      pure { core with memory }
  | .imm _ => .ok core

/-- Values of the input slots, in slot order. -/
def readSlots (core : Core) : List Slot → List Arg → Except MemoryFault (List Word)
  | slot :: slots, arg :: args =>
      match slot.role with
      | .read | .readWrite => do
          let value ← arg.load core slot.width
          let values ← readSlots core slots args
          pure (value :: values)
      | .address => do
          let values ← readSlots core slots args
          pure (arg.address core :: values)
      | .write => readSlots core slots args
  | _, _ => pure []

/-- Store results into the output slots, in slot order. Every output slot is
written, so the footprint is the slots' (`Op.writes`). -/
def writeSlots (before : Core) : Core → List Slot → List Arg → List Word → Except MemoryFault Core
  | core, slot :: slots, arg :: args, results =>
      match slot.role with
      | .write | .readWrite => do
          let core ← arg.store before slot.width (results.headD 0) core
          writeSlots before core slots args results.tail
      | .read | .address => writeSlots before core slots args results
  | core, _, _, _ => pure core

/-- Values of the implicit registers a row reads, in order: full register
words, as for explicit register slots. -/
def readImplicits (core : Core) (implicits : List Implicit) : List Word :=
  implicits.filterMap fun implicit => if implicit.role.reads then some (core.readReg implicit.reg) else none

/-- Write the implicit registers a row writes, in order, with the width's
partial-register rule. Register writes cannot fault. -/
def writeImplicits : Core → List Implicit → List Word → Core
  | core, implicit :: implicits, results =>
      if implicit.role.writes then
        writeImplicits (core.writeReg implicit.width implicit.reg (results.headD 0)) implicits results.tail
      else writeImplicits core implicits results
  | core, [], _ => core

@[simp] theorem readImplicits_nil (core : Core) : readImplicits core [] = [] := rfl
@[simp] theorem writeImplicits_nil (core : Core) (results : List Word) : writeImplicits core [] results = core := by
  cases results <;> rfl

inductive ExecFault where
  | memory (fault : MemoryFault)
  | semantic (fault : SemFault)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- A row's inputs: its read slots, the implicit registers it reads, then an
implicitly popped word. -/
def Op.inputs (o : Op) (args : List Arg) (core : Core) : Except MemoryFault (List Word) := do
  let inputs ← readSlots core (desc o).slots args
  let inputs := inputs ++ readImplicits core (desc o).implicit
  match (desc o).stack with
  | .pop => do
      let value ← core.memory.read64? (core.readReg .rsp)
      pure (inputs ++ [value])
  | .push | .none => pure inputs

/-- A row's stack effect through `rsp`, before its slots are written. -/
def Op.stage (o : Op) (core : Core) (out : SemOut) : Except MemoryFault Core :=
  match (desc o).stack with
  | .push => do
      let memory ← core.memory.write64? (core.readReg .rsp - 8) (out.results.headD 0)
      pure { core.setReg .rsp (core.readReg .rsp - 8) with memory }
  | .pop => pure (core.setReg .rsp (core.readReg .rsp + 8))
  | .none => pure core

/-- Execute a row whose semantics observes the flags `observed`. -/
def Op.run (o : Op) (args : List Arg) (core : Core) (observed : ByteEval.Flags) :
    Except ExecFault (Core × SemOut) := do
  let inputs ← (o.inputs args core).mapError ExecFault.memory
  let out ← ((desc o).sem ⟨inputs, observed⟩).mapError ExecFault.semantic
  let staged ← (o.stage core out).mapError ExecFault.memory
  let final ← (writeSlots core staged (desc o).slots args out.results).mapError ExecFault.memory
  pure (writeImplicits final (desc o).implicit out.implicit, out)

/-- Execute a row over flags: the semantics observes only the flags the row
declares, and the result merges its flag effects. -/
def Op.exec (o : Op) (args : List Arg) (core : Core) (flags : ByteEval.Flags) :
    Except ExecFault (Core × ByteEval.Flags) := do
  let (final, out) ← o.run args core (flags.restrict (desc o).flagsIn)
  pure (final, flags.merge (desc o).flagsOut out.flags)

/-! ## Memory footprint -/

/-- A byte range an instruction reads or writes. -/
structure Access where
  address : Word
  bytes : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Arg.access (core : Core) (width : Width) : Arg → List Access
  | .mem address => [⟨address.eval core, width.bytes⟩]
  | _ => []

def slotReads (core : Core) : List Slot → List Arg → List Access
  | slot :: slots, arg :: args =>
      (match slot.role with
        | .read | .readWrite => arg.access core slot.width
        | .write | .address => []) ++ slotReads core slots args
  | _, _ => []

def slotWrites (core : Core) : List Slot → List Arg → List Access
  | slot :: slots, arg :: args =>
      (match slot.role with
        | .write | .readWrite => arg.access core slot.width
        | .read | .address => []) ++ slotWrites core slots args
  | _, _ => []

/-- The word a row pops. -/
def Op.pops (o : Op) (core : Core) : List Access :=
  match (desc o).stack with
  | .pop => [⟨core.readReg .rsp, 8⟩]
  | .push | .none => []

/-- The word a row pushes. -/
def Op.pushes (o : Op) (core : Core) : List Access :=
  match (desc o).stack with
  | .push => [⟨core.readReg .rsp - 8, 8⟩]
  | .pop | .none => []

/-- Memory a linear row reads: its memory input slots and a popped word. -/
def Op.reads (o : Op) (args : List Arg) (core : Core) : List Access :=
  slotReads core (desc o).slots args ++ o.pops core

/-- Memory a linear row writes, in execution order: a pushed word, then its
memory output slots. -/
def Op.writes (o : Op) (args : List Arg) (core : Core) : List Access :=
  o.pushes core ++ slotWrites core (desc o).slots args

end Compilatrix.X86
