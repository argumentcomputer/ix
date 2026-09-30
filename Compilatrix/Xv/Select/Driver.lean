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

The driver is in kernel-evaluable style (`Select.Basic`): the analyses are
persistent `Nat`-keyed maps built by folds over lists, and blocks and
statements are visited as lists by structural recursion.
-/

namespace Compilatrix.Xv.Select

open Compilatrix.Lir (VReg Label FunId)

def countUses (counts : NatMap Nat) (xs : List VReg) : NatMap Nat :=
  xs.foldl (fun m x => m.insert x (m.getD x 0 + 1)) counts

/-- Uses of each register in a function: statements, terminators and edge
arguments. -/
def useCounts (f : Lir.Func) : NatMap Nat :=
  f.blocks.toList.foldl (init := {}) fun m b =>
    countUses m (b.body.toList.flatMap Lir.Stmt.uses ++ b.term.uses ++ b.term.edgeUses)

/-- The statement of a block assigning each register, with its right-hand
side. -/
def defSites (body : List Lir.Stmt) : NatMap (Nat × Lir.Rhs) :=
  body.zipIdx.foldl (init := {}) fun m (s, i) =>
    match s with
    | .assign x r => m.insert x (i, r)
    | _ => m

/-- Positions of a block's stores and calls, ascending. -/
def effectSites (body : List Lir.Stmt) : List Nat :=
  body.zipIdx.filterMap fun (s, i) =>
    match s with
    | .store .. | .call .. => some i
    | _ => none

/-- The largest register a function names. -/
def maxVReg (f : Lir.Func) : VReg :=
  let blockMax (b : Lir.Block) : VReg :=
    (b.params ++ b.body.toList.flatMap (fun s => s.uses ++ s.defs) ++ b.term.uses ++ b.term.defs ++
      b.term.edgeUses).foldl max 0
  f.blocks.toList.foldl (fun m b => max m (blockMax b)) (f.params.foldl max 0)

/-- Select statements from last to first, prepending each one's
instructions to `out` and skipping consumed statements. -/
def selectStmts (ctx : Ctx) : List (Lir.Stmt × Nat) → List (Inst VReg) →
    StateT St (Except Error) (List (Inst VReg))
  | [], out => pure out
  | (s, i) :: rest, out => do
      if (← get).consumed.contains i then selectStmts ctx rest out
      else
        let insts ← (selectStmt i s).run { ctx with site := some i }
        selectStmts ctx rest (insts ++ out)

def selectBlock (fn : FunId) (uses : NatMap Nat) (label : Label) (b : Lir.Block) :
    StateT St (Except Error) (Block VReg) := do
  modify fun s => { s with consumed := [] }
  let body := b.body.toList
  let ctx : Ctx := { fn, label, size := body.length, uses, defs := defSites body, effects := effectSites body }
  let (pre, term) ← (selectTerm b.term).run ctx
  let out ← selectStmts ctx body.zipIdx.reverse pre
  return { params := b.params, body := out.toArray, term, cold := b.cold }

def selectBlocks (fn : FunId) (uses : NatMap Nat) : List (Lir.Block × Label) →
    StateT St (Except Error) (List (Block VReg))
  | [] => pure []
  | (b, l) :: rest => do
      let b ← selectBlock fn uses l b
      return b :: (← selectBlocks fn uses rest)

def selectFunc (fn : FunId) (f : Lir.Func) :
    StateT (Std.TreeMap String Nat compare) (Except Error) (Func VReg) := do
  let (blocks, st) ← (selectBlocks fn (useCounts f) f.blocks.toList.zipIdx).run
    { next := maxVReg f + 1, fired := ← get }
  set st.fired
  return { name := f.name, params := f.params, results := f.results, blocks := blocks.toArray, conv := f.conv }

def selectFuncs : List (Lir.Func × FunId) →
    StateT (Std.TreeMap String Nat compare) (Except Error) (List (Func VReg))
  | [] => pure []
  | (f, fn) :: rest => do
      let f ← selectFunc fn f
      return f :: (← selectFuncs rest)

/-- Select a Lir program: the Xv program and how often each rule fired. -/
def run (p : Lir.Program) : Except Error (VProgram × Std.TreeMap String Nat compare) := do
  let (funcs, fired) ← (selectFuncs p.funcs.toList.zipIdx).run {}
  return ({ funcs := funcs.toArray, main := p.main }, fired)

/-- The rule names `run` reports, in table order (05 §4). -/
def ruleNames : List String :=
  ["br", "cmp.rr", "cmp.imm8", "cmp.imm32", "cmp.swap", "cmp.testSelf",
   "cmp.mem.rr", "cmp.mem.imm8", "cmp.mem.imm32", "test.rr", "test.imm", "test.mem",
   "brOvf.add.rr", "brOvf.add.imm8", "brOvf.add.imm32", "brOvf.add.mem",
   "brOvf.sub.rr", "brOvf.sub.imm8", "brOvf.sub.imm32", "brOvf.sub.mem",
   "imm.xorZero", "imm.mov32", "imm.movSext32", "imm.movabs", "move",
   "alu.rr", "alu.imm8", "alu.imm32", "alu.swap", "alu.load", "alu.narrow", "tie.swap",
   "lea.add", "lea.addr", "amode.fold", "load.sink",
   "imul.rr", "imul.imm8", "imul.imm32", "imul.load",
   "shift.zero", "shift.imm", "shift.cl", "shl.lea", "div.quot", "div.rem", "div.load",
   "select.cmov", "select.load", "test.setcc",
   "load.mov64", "load.mov32", "load.movzx", "load.sext", "store.reg", "store.imm",
   "call", "jmp", "ret", "tail", "exit"]

end Compilatrix.Xv.Select
