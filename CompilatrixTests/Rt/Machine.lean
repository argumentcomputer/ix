import CompilatrixTests.Rt.Support
import CompilatrixTests.Backend.Support
import Compilatrix.Rt.Backend
import Compilatrix.Xv.Select.Driver
import Compilatrix.Xv.Alloc.Driver
import Compilatrix.Xv.Semantics
import Compilatrix.Xv.XlSemantics

/-! `Rt.lower`'s output through the backend, run at every level below Lir
(M1.F6):

* **Xv** (`Xv.eval`, after selection) and **Xl** (`Xl.eval`, after M1.B4's
  allocation) from the memory `cx_init` left, as Lir runs;
* **typed x86** and the **byte machine** on the object `Backend.emit` makes:
  `cx_init`'s wrapper on a zero region (with a mapped stack), then the
  root's wrapper on what it left, with sentinels in the callee-saved
  registers (`CompilatrixTests.Backend.Support`'s runners and entry core).

An Lir outcome must come back as the same outcome at Xv and Xl, and as
`rax:rdx` from both machines (`ok w` as `0:w`, a resource failure as its
status and a trap as 4, 04 §6), with the callee-saved registers and `rsp`
restored and the object area and the `bump`/`limit` fields equal to Lir's.
The models share Lir's region address, so pointer results agree as words. -/

namespace CompilatrixTests.Rt.Machine

open Compilatrix Compilatrix.Xv CompilatrixTests.Src
open CompilatrixTests.Backend (Exit expected runTyped runBytes Shadow sentinels sp0 retSentinel stackLo stackHi entryCore)

def testProvenance : X86.ELF.Provenance := .ixir1Policy (Compilatrix.Ixon.Address.replicate 0x42) 1 1

/-- A lowered program through selection, allocation and emission. -/
structure Compiled where
  lir : Compilatrix.Rt.Lowered
  xv : VProgram
  xl : LProgram
  artifact : Backend.Artifact

def compile (l : Compilatrix.Rt.Lowered) : Except String Compiled := do
  let (xv, _) ← (Select.run l.program).mapError fun e => s!"selection: {e.form}: {e.reason}"
  let r ← (Alloc.run {} xv).mapError (s!"allocation: " ++ ·)
  let a ← (Backend.emit r.program (l.config testProvenance)).mapError toString
  -- `Rt.Lowered.compile` (the glue M1.I1 uses) makes the same object
  let whole ← (l.compile testProvenance).mapError toString
  unless whole.object == a.object do throw "Rt.Lowered.compile made a different object"
  pure { lir := l, xv, xl := r.program, artifact := a }

/-- The region plus the stack, with the return sentinel on top. -/
def machineMem (size : Nat) : X86.Memory :=
  let inside := fun a => inRegion size a || (stackLo ≤ a && a < stackHi)
  let m : X86.Memory := { bytes := fun _ => 0, readable := inside, writable := inside }
  m.write64 sp0 retSentinel

/-- The object area and the allocator's fields, for comparing memories. -/
def heapWords (m : X86.Memory) (bump : Word) : List Word :=
  [m.read64 (ctx - 40), m.read64 (ctx - 32)] ++
    (List.range ((bump - start).toNat / 8)).map fun i => m.read64 (start + UInt64.ofNat (8 * i))

structure Machines where
  typed : Shadow
  bytes : Shadow
  typedSteps : Nat := 0
  byteSteps : Nat := 0

def Machines.initial (size : Nat) : Machines := { typed := { base := machineMem size }, bytes := { base := machineMem size } }

/-- One export's wrapper on the typed machine: its `rax:rdx`, the memory
after it and the steps taken. -/
def runExportTyped (c : Compiled) (symbol : String) (args : List Word) (s : Shadow) (fuel : Nat := 50000000) :
    Except String (Exit × Shadow × Nat) := do
  let some (_, block) := c.artifact.exports.find? (·.1 == symbol) | throw s!"no export {symbol}"
  let checked ← (X86.Program.check { c.artifact.checked.program with entry := block }).mapError
    fun e => s!"typed: the export does not check: {repr e}"
  let typed := runTyped checked (entryCore s.memory args) s fuel
  let m := typed.machine
  let exitT ← match m.status with
    | .halted st => pure (⟨st, m.core.readReg .rdx⟩ : Exit)
    | s => throw s!"typed: {repr s} after {typed.steps} steps"
  unless m.core.readReg .rsp == sp0 && m.returns.isEmpty do throw "typed: rsp or frames not restored"
  unless sentinels.all (fun (r, v) => m.core.readReg r == v) do throw "typed: a callee-saved register changed"
  pure (exitT, typed.shadow, typed.steps)

/-- One export's wrapper on the byte machine over the object's own `.text`:
its `rax:rdx`, the memory after it and the steps taken. -/
def runExportBytes (c : Compiled) (symbol : String) (args : List Word) (s : Shadow) (fuel : Nat := 50000000) :
    Except String (Exit × Shadow × Nat) := do
  let some text := X86.ELFRead.text? c.artifact.object | throw "the object has no text"
  let some offset := X86.ELF.symbol? c.artifact.object symbol <|> X86.ELF.entry? c.artifact.object symbol
    | throw s!"the object has no symbol {symbol}"
  let base : Word := 0x400000
  let bytes := runBytes text base ⟨entryCore s.memory args, base + UInt64.ofNat offset, {}⟩ s retSentinel fuel
  let exitB ← match bytes.result with
    | .ok st =>
      unless st.rip == retSentinel do throw s!"bytes: stopped at {st.rip} after {bytes.steps} steps"
      unless st.core.readReg .rsp == sp0 + 8 do throw "bytes: rsp not restored"
      unless sentinels.all (fun (r, v) => st.core.readReg r == v) do throw "bytes: a callee-saved register changed"
      pure (⟨st.core.readReg .rax, st.core.readReg .rdx⟩ : Exit)
    | .error f => throw s!"bytes: fault {repr f}"
  pure (exitB, bytes.shadow, bytes.steps)

/-- Run one export's wrapper on both machines: its `rax:rdx`, and the
machines' memories after it. -/
def runExport (c : Compiled) (symbol : String) (args : List Word) (ms : Machines) (fuel : Nat := 50000000) :
    Except String (Exit × Machines) := do
  let (exitT, typed, typedSteps) ← runExportTyped c symbol args ms.typed fuel
  let (exitB, bytes, byteSteps) ← runExportBytes c symbol args ms.bytes fuel
  unless exitT == exitB do throw s!"typed {exitT.status}:{exitT.value}, bytes {exitB.status}:{exitB.value}"
  pure (exitT, { typed, bytes, typedSteps := ms.typedSteps + typedSteps, byteSteps := ms.byteSteps + byteSteps })

/-- `cx_init` on both machines: status 0 and the free bytes. -/
def initMachines (c : Compiled) (size : Nat := defaultSize) (budget : Word := defaultBudget) :
    Except String Machines := do
  let (e, ms) ← runExport c Compilatrix.Rt.Procs.initSymbol [UInt64.ofNat size, budget] (Machines.initial size)
  unless e == ⟨0, limitOf size - start⟩ do throw s!"cx_init returned {e.status}:{e.value}"
  pure ms

structure Report where
  runs : Nat := 0
  typedSteps : Nat := 0
  byteSteps : Nat := 0

/-- One root on one input at Lir, Xv, Xl and both machines. `wrapperOnly`:
an argument the wrapper rejects (at least 2^63), so only the machines run
and must return status 3. -/
def check (c : Compiled) (root : Nat) (args : List Nat) (clock : Nat) (ms : Machines) (r : Report)
    (wrapperOnly : Bool := false) : Except String Report := do
  let some symbol := c.lir.roots.lookup root | throw s!"f{root} is not a root"
  if wrapperOnly then
    let (e, _) ← runExport c symbol (args.map UInt64.ofNat) ms
    unless e == ⟨3, 0⟩ do throw s!"an argument past 2^63: {e.status}:{e.value}, expected 3:0"
    return { r with runs := r.runs + 1 }
  let mem ← initRegion c.lir
  let words := args.map tag
  let lir := Lir.eval { c.lir.program with main := root } clock words mem ctx
  let xv := Xv.eval { c.xv with main := root } clock words mem ctx
  let xl := Xl.eval { c.xl with main := root } {} clock words mem ctx
  let some want := expected lir | throw s!"Lir {lirOutcome lir}: nothing to compare"
  unless expected xv == some want do throw s!"Xv {lirOutcome xv}, Lir {lirOutcome lir}"
  unless expected xl == some want do throw s!"Xl {lirOutcome xl}, Lir {lirOutcome lir}"
  let (e, ms') ← runExport c symbol (args.map UInt64.ofNat) ms
  unless e == want do throw s!"machines {e.status}:{e.value}, Lir {want.status}:{want.value}"
  if let .ok (_, m) := lir then
    let bump := m.read64 (ctx - 40)
    let lw := heapWords m bump
    for (label, other) in [("Xv", xv), ("Xl", xl)] do
      if let .ok (_, m') := other then
        unless heapWords m' bump == lw do throw s!"{label}: the object area differs from Lir's"
    unless heapWords ms'.typed.memory bump == lw do throw "typed: the object area differs from Lir's"
    unless heapWords ms'.bytes.memory bump == lw do throw "bytes: the object area differs from Lir's"
  pure { runs := r.runs + 1, typedSteps := r.typedSteps + ms'.typedSteps - ms.typedSteps
         byteSteps := r.byteSteps + ms'.byteSteps - ms.byteSteps }

end CompilatrixTests.Rt.Machine
