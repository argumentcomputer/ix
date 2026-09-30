import Compilatrix.Backend
import Compilatrix.Xv.XlSemantics
import CompilatrixTests.Backend.Machine
import CompilatrixTests.Lir.Region

/-!
# The backend differential harness

One Xl program is stacked, laid out, encoded and written as an ELF object
(`Backend.emit`), then run on every input at three levels:

- **Xl** (`Xl.eval`), the reference, on the Lir region with the context
  fields the wrapper and the driver set (`stackBudget`, `entrySp`,
  `stackLimit`), and arguments in the internal convention (tagged if the
  export passes `Nat`s);
- **typed x86** (`X86.step` from the wrapper, `runTyped`) and the **byte
  machine** on the object's own `.text` (`ByteEval.step` from the exported
  symbol, `runBytes`), both on the same region plus a mapped stack, with
  the C-level arguments, `rdi` the region and sentinels in the callee-saved
  registers.

An Xl result `ok [v]` must come back as `rax:rdx = 0:v`, `resource r` as
`statusOf r : 0` and `trap` as `4 : 0` (04 §6), with the callee-saved
registers and `rsp` restored and, after a return, the heap and context
words equal to Xl's. The typed machine halts at its final `ret` (depth 0);
the byte machine executes it and must land on the sentinel return address.
Native execution (`Native`) links the object with the C driver.
-/

namespace CompilatrixTests.Backend

open Compilatrix Compilatrix.Xv CompilatrixTests.Lir

/-! ## The machine region -/

def stackLo : Word := 0x100000
def stackHi : Word := 0x200000
/-- `rsp` at the export's entry, where the return address is: 8 mod 16. -/
def sp0 : Word := stackHi - 8
/-- The wrapper's `rsp` at its call (05 §6.1): six pushes and a pad below `sp0`. -/
def entrySp : Word := sp0 - 56
/-- The return address the byte machine's final `ret` jumps to. -/
def retSentinel : Word := 0x7e57000000
def defaultBudget : Word := 0xE0000

/-- Distinct values in the callee-saved registers at entry. -/
def sentinels : List (X86.GPR × Word) :=
  [(.rbx, 0x1111111111111111), (.rbp, 0x2222222222222222), (.r12, 0x3333333333333333),
   (.r13, 0x4444444444444444), (.r14, 0x5555555555555555), (.r15, 0x6666666666666666)]

/-- The Xl-level memory: the region, with the context fields set as the
driver (`stackBudget`) and the wrapper (`entrySp`, `stackLimit`) set them. -/
def refMemory (seed : UInt64) (budget : Word) : X86.Memory :=
  let m := (Region.initial seed).write64 (Region.ctx - 48) budget
  let m := m.write64 (Region.ctx - 64) entrySp
  m.write64 (Region.ctx - 56) (entrySp - budget)

/-- The machine memory: the region with `stackBudget` set, plus a mapped
stack whose top slot holds the sentinel return address. -/
def machineMemory (seed : UInt64) (budget : Word) : X86.Memory :=
  let m := (Region.initial seed).write64 (Region.ctx - 48) budget
  let m : X86.Memory :=
    { bytes := m.bytes
      readable := fun a => m.readable a || (stackLo ≤ a && a < stackHi)
      writable := fun a => m.writable a || (stackLo ≤ a && a < stackHi) }
  m.write64 sp0 retSentinel

/-- The core at the export's entry: `rdi` the region, the C arguments in
`rsi, rdx, rcx, r8, r9`, sentinels in the callee-saved registers. -/
def entryCore (mem : X86.Memory) (args : List Word) : X86.Core :=
  let regs := [(X86.GPR.rdi, Region.base)] ++ Stacking.sysvArgs.zip args ++ sentinels ++ [(.rsp, sp0)]
  { registers := regs.foldl (fun rs (r, v) => rs.set r v) X86.Registers.zero, memory := mem }

/-! ## Outcomes -/

/-- An export's result: `rax:rdx`. -/
structure Exit where
  status : Word
  value : Word
  deriving BEq, Repr, Inhabited

/-- What the export must return for an Xl outcome; `none` for timeouts,
stuck runs and wrong arities, which the harness does not compare. -/
def expected : Lir.Outcome → Option Exit
  | .ok ([v], _) => some ⟨0, v⟩
  | .resource r => some ⟨UInt64.ofNat (Stacking.statusOf r), 0⟩
  | .trap => some ⟨UInt64.ofNat Stacking.trapStatus, 0⟩
  | _ => none

/-- The heap and context words of a memory. -/
def words (m : X86.Memory) : List Word := Region.heapWords m ++ Region.ctxWords m

/-- How an argument reaches Xl: tagged for a `Nat`, as is for a word. -/
def internalArg : Stacking.ArgRep → Word → Word
  | .nat, a => 2 * a + 1
  | .word, a => a

/-- One input's results at every level. -/
structure Run where
  args : List Word
  xl : Lir.Outcome
  exit : Option Exit
  typedSteps : Nat
  byteSteps : Nat

/-- Compare the three levels on one input; an error names the first
disagreement. With `root` (an export's symbol and wrapper block), the
typed machine starts at that wrapper and the byte machine at that symbol;
`p`'s `main` is then that export's function. -/
def runOne (p : LProgram) (a : Backend.Artifact) (reps : List Stacking.ArgRep) (env : Xl.Env) (clock : Nat)
    (seed : UInt64) (budget : Word) (args : List Word) (override : Option Exit := none) (fuel : Nat := 20000000)
    (root : Option (String × X86.BlockId) := none) : Except String Run := do
  let xl := Xl.eval p env clock ((reps.zip args).map fun (r, v) => internalArg r v) (refMemory seed budget) Region.ctx
  let exit := override <|> expected xl
  let mem := machineMemory seed budget
  let core := entryCore mem args
  -- typed x86, from the laid-out program's entry (main's wrapper) or the root's wrapper
  let checked ← match root with
    | none => pure a.checked
    | some (_, block) =>
        (X86.Program.check { a.checked.program with entry := block }).mapError
          (fun e => s!"typed: the root does not check: {repr e}")
  let typed := runTyped checked core { base := mem } fuel
  let m := typed.machine
  let savedOk (read : X86.GPR → Word) := sentinels.all fun (r, v) => read r == v
  match exit with
  | some e =>
      unless m.status == .halted e.status do
        throw s!"typed: {repr m.status}, expected status {e.status}"
      unless m.core.readReg .rdx == e.value do throw s!"typed: value {m.core.readReg .rdx}, expected {e.value}"
      unless m.core.readReg .rsp == sp0 && m.returns.isEmpty do throw "typed: rsp or frames not restored"
      unless savedOk m.core.readReg do throw "typed: a callee-saved register is not restored"
  | none => pure ()
  -- the byte machine, on the object's text from the exported symbol
  let some text := X86.ELFRead.text? a.object | throw "the object has no text"
  let symbolOffset := match root with
    | none => X86.ELF.entry? a.object a.exportName
    | some (name, _) => X86.ELF.symbol? a.object name
  let some offset := symbolOffset | throw "the object has no symbol for the export"
  let base : Word := 0x400000
  let bytes := runBytes text base ⟨core, base + UInt64.ofNat offset, {}⟩ { base := mem } retSentinel fuel
  match exit, bytes.result with
  | some e, .ok st =>
      unless st.rip == retSentinel do throw s!"bytes: stopped at {st.rip} after {bytes.steps} steps"
      unless st.core.readReg .rax == e.status && st.core.readReg .rdx == e.value do
        throw s!"bytes: {st.core.readReg .rax}:{st.core.readReg .rdx}, expected {e.status}:{e.value}"
      unless st.core.readReg .rsp == sp0 + 8 do throw "bytes: rsp not restored"
      unless savedOk st.core.readReg do throw "bytes: a callee-saved register is not restored"
  | some _, .error f => throw s!"bytes: fault {repr f}"
  | none, _ => pure ()
  -- memory after a return
  match xl with
  | .ok (_, final) =>
      unless override.isSome do
        let want := words final
        unless words typed.shadow.memory == want do throw "typed: heap or context words differ"
        unless words bytes.shadow.memory == want do throw "bytes: heap or context words differ"
  | _ => pure ()
  pure { args, xl, exit, typedSteps := typed.steps, byteSteps := bytes.steps }

end CompilatrixTests.Backend
