import Compilatrix.Xv.Select.Branch

/-!
# The selection driver

`Select.run` maps each Lir function to an Xv function with the same
parameters, labels, block parameters, edges and cold flags, so the two run
in lock-step: they charge the clock at the same calls, tail calls and
edges (05 §2, §4).

Each block is scanned backwards (after Cranelift's `machinst/lower.rs`):
first the terminator, then the statements from last to first. A rule may
consume an earlier statement of the block whose only use it is (address
arithmetic, or a load with no store or call in between); the scan then
skips it. Scanning backwards means a consumer is always selected before
the statements it could fold. Use counts are over the whole function, so a
consumed register has no other reader.

Selection is total over the forms the current table expresses; any other
form is an `Error` naming it (`Select.Rules`, `Select.Branch`).
-/

namespace Compilatrix.Xv.Select

open Compilatrix.Lir (VReg Label FunId)

/-- Uses of each register in a function: statements, terminators and edge
arguments. -/
def useCounts (f : Lir.Func) : Std.HashMap VReg Nat := Id.run do
  let mut counts : Std.HashMap VReg Nat := {}
  for b in f.blocks do
    let xs := b.body.toList.flatMap Lir.Stmt.uses ++ b.term.uses ++ b.term.edgeUses
    for x in xs do
      counts := counts.insert x (counts.getD x 0 + 1)
  return counts

/-- The statement of a block assigning each register. -/
def defSites (b : Lir.Block) : Std.HashMap VReg Nat := Id.run do
  let mut sites : Std.HashMap VReg Nat := {}
  for h : i in [:b.body.size] do
    if let .assign x _ := b.body[i] then sites := sites.insert x i
  return sites

/-- The largest register a function names. -/
def maxVReg (f : Lir.Func) : VReg :=
  let blockMax (b : Lir.Block) : VReg :=
    (b.params ++ b.body.toList.flatMap (fun s => s.uses ++ s.defs) ++ b.term.uses ++ b.term.defs ++
      b.term.edgeUses).foldl max 0
  f.blocks.foldl (fun m b => max m (blockMax b)) (f.params.foldl max 0)

def selectBlock (fn : FunId) (uses : Std.HashMap VReg Nat) (label : Label) (b : Lir.Block) :
    StateT St (Except Error) (Block VReg) := do
  modify fun s => { s with consumed := {} }
  let ctx : Ctx := { fn, label, block := b, uses, defAt := defSites b }
  let (pre, term) ← (selectTerm b.term).run { ctx with site := none }
  let mut out := pre
  for k in [:b.body.size] do
    let i := b.body.size - 1 - k
    if (← get).consumed.contains i then continue
    let insts ← (selectStmt i b.body[i]!).run { ctx with site := some i }
    out := insts ++ out
  return { params := b.params, body := out.toArray, term, cold := b.cold }

def selectFunc (fn : FunId) (f : Lir.Func) : StateT (Std.HashMap String Nat) (Except Error) (Func VReg) := do
  let uses := useCounts f
  let fired ← get
  let (blocks, st) ← (f.blocks.zipIdx.mapM fun (b, l) => selectBlock fn uses l b).run
    { next := maxVReg f + 1, fired }
  set st.fired
  return { name := f.name, params := f.params, results := f.results, blocks, conv := f.conv }

/-- Select a Lir program: the Xv program and how often each rule fired. -/
def run (p : Lir.Program) : Except Error (VProgram × Std.HashMap String Nat) := do
  let (funcs, fired) ← (p.funcs.zipIdx.mapM fun (f, fn) => selectFunc fn f).run {}
  return ({ funcs, main := p.main }, fired)

/-- The rule names `run` reports, in table order (05 §4). -/
def ruleNames : List String :=
  ["br.cmp", "br.cmpImm8", "br.cmpImm32", "br.swap", "br.and", "br.andImm8", "br.andImm32",
   "br.cmpMem", "br.cmpMemImm8", "br.cmpMemImm32", "brOvf.add", "brOvf.addImm8", "brOvf.addImm32",
   "brOvf.sub", "brOvf.subImm8", "brOvf.subImm32",
   "imm.xorZero", "imm.mov32", "imm.movSext32", "imm.movabs", "move",
   "alu.rr", "alu.imm8", "alu.imm32", "alu.swap", "alu.narrow", "lea.add", "lea.addr", "amode.fold",
   "load.sink", "imul.load", "imul.rr", "imul.imm8", "imul.imm32", "shl.zero", "shl.lea", "shl.imul",
   "load.mov64", "load.mov32", "load.movzx", "load.sext", "store.reg", "store.imm",
   "tie.swap", "call", "jmp", "ret", "tail", "exit"]

end Compilatrix.Xv.Select
