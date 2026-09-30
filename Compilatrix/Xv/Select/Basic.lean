import Compilatrix.Xv.Syntax
import Compilatrix.X86.Basic
import Std.Data.TreeMap

/-!
# Selection: context, state and shared helpers

Selection (05 §4) scans each Lir block backwards, turning each statement
and the terminator into Xv instructions with the first rule that applies.
This module holds what the rules share:

- **Analyses** (`Ctx`): the number of uses of each register in the whole
  function (statements, terminators and edge arguments), the statement of
  the current block that assigns each register, with its right-hand side,
  and the positions of the block's stores and calls, so that
  `pureBetween j i` holds when none lies strictly between statements `j`
  and `i`. A rule may fold (consume) an earlier statement of the block whose
  single use it is: address arithmetic at any distance, a load only if
  `pureBetween` holds, so folding never crosses a store or a call (06 S18).
- **State** (`St`): fresh registers (after the function's largest), the
  statements already consumed, and a count of each rule's firings.
- **Immediates** (rule 5): `xor r32, r32` for 0, `mov r32, imm32` below
  2^32, `mov r/m64, imm32` for sign-extended 32-bit values, `movabs`
  otherwise; and the imm8/imm32 fits of rule 6.

**Kernel-evaluable style** (roadmap D17, M1.K1): selection is on the
`Recheck.run` path, so it keeps its tables in persistent `Nat`-keyed maps
(`Std.TreeMap`, which the kernel reduces), recurses structurally over
lists, and never indexes an `Array`: blocks and statements are read as
lists (`Array.toList` is a projection).

A form the table cannot express is an `unsupported` error naming the form,
never a miscompilation.
-/

namespace Compilatrix.Xv.Select

open Compilatrix.Lir (VReg Label FunId Word)

/-- A persistent map keyed by virtual registers or positions. -/
abbrev NatMap (α : Type) := Std.TreeMap Nat α compare

/-- A selection failure: the site, the Lir form and why it has no rule. -/
structure Error where
  fn : FunId
  block : Label
  /-- The statement, or `none` for the terminator. -/
  stmt : Option Nat
  form : String
  reason : String
  deriving Repr, Inhabited

def Error.text (e : Error) : String :=
  let site := match e.stmt with
    | some i => s!"statement {i}"
    | none => "terminator"
  s!"function {e.fn} block {e.block} {site}: unsupported form {e.form}: {e.reason}"

structure Ctx where
  fn : FunId
  label : Label
  /-- The block's statement count; the terminator's position. -/
  size : Nat
  /-- Uses of each register in the whole function. -/
  uses : NatMap Nat
  /-- The statement of this block that assigns each register, and its
  right-hand side. -/
  defs : NatMap (Nat × Lir.Rhs)
  /-- Positions of this block's stores and calls, ascending. -/
  effects : List Nat
  /-- The statement being selected, or `none` for the terminator. -/
  site : Option Nat := none

structure St where
  next : VReg
  /-- Statements of the current block already folded into a consumer. -/
  consumed : List Nat := []
  fired : Std.TreeMap String Nat compare := {}

abbrev SelM := ReaderT Ctx (StateT St (Except Error))

def fresh : SelM VReg := modifyGet fun s => (s.next, { s with next := s.next + 1 })

/-- Count one firing of the rule `name`. -/
def fire (name : String) : SelM Unit :=
  modify fun s => { s with fired := s.fired.insert name (s.fired.getD name 0 + 1) }

def consume (j : Nat) : SelM Unit := modify fun s => { s with consumed := j :: s.consumed }

def unsupported {α : Type} (form reason : String) : SelM α := do
  let c ← read
  throw { fn := c.fn, block := c.label, stmt := c.site, form, reason }

def useCount (x : VReg) : SelM Nat := return (← read).uses.getD x 0

def singleUse (x : VReg) : SelM Bool := return (← useCount x) == 1

/-- The current site's position: a statement, or the terminator. -/
def sitePos : SelM Nat := do
  let c ← read
  return c.site.getD c.size

/-- The unconsumed statement of this block, before the current site, that
assigns `x`, and its right-hand side. -/
def defStmt? (x : VReg) : SelM (Option (Nat × Lir.Rhs)) := do
  let some (j, r) := (← read).defs[x]? | return none
  unless j < (← sitePos) do return none
  if (← get).consumed.contains j then return none
  return some (j, r)

/-- No `store` or `call` strictly between statements `j` and `i` (`i` may be
the terminator's position). -/
def pureBetween (j i : Nat) : SelM Bool := do
  return (← read).effects.all fun p => p ≤ j || i ≤ p

/-! ## Rows and immediates -/

def row (mn : X86.Mnemonic) (w : X86.Width) (form : X86.OpEn) (src : X86.Width := w) : X86.Op :=
  { mn, w, form, src }

def leaRow : X86.Op := row .lea .w64 .RM

/-- The canonical imm8 for `k` at width `w` (16 or more), if a sign-extended
byte has `k`'s low `w` bits. -/
def imm8? (w : X86.Width) (k : Word) : Option Word :=
  if X86.fitsImm8 w k then some (X86.ImmKind.imm8.norm k) else none

/-- The canonical full-size immediate (imm8, imm16 or sign-extended imm32)
of an `MI`/`RMI` row at `w`, if it has `k`'s low `w` bits. -/
def immFull? (w : X86.Width) (k : Word) : Option Word :=
  let c := (X86.Table.fullImm w).norm k
  if w.truncate c == w.truncate k then some c else none

/-- Rule 5: `x := k`. -/
def movImm (x : VReg) (k : Word) : SelM (List (Inst VReg)) := do
  if k == 0 then
    fire "imm.xorZero"
    return [.zero x]
  if k.toNat < 2 ^ 32 then
    fire "imm.mov32"
    return [.op (row .mov .w32 .OI) [x] [.i (X86.ImmKind.imm32.norm k)]]
  if X86.ImmKind.imm32.norm k == k then
    fire "imm.movSext32"
    return [.op (row .mov .w64 .MI) [x] [.i k]]
  fire "imm.movabs"
  return [.op (row .mov .w64 .OI) [x] [.i k]]

/-- A fresh register holding `k`. -/
def materialize (k : Word) : SelM (VReg × List (Inst VReg)) := do
  let x ← fresh
  return (x, ← movImm x k)

/-- A Lir argument in a register, materializing an immediate. -/
def argReg : Lir.Arg → SelM (VReg × List (Inst VReg))
  | .v x => pure (x, [])
  | .imm k => materialize k

def argRegs : List Lir.Arg → SelM (List VReg × List (Inst VReg))
  | [] => pure ([], [])
  | a :: as => do
      let (v, pre) ← argReg a
      let (vs, pres) ← argRegs as
      return (v :: vs, pre ++ pres)

/-- `x := w.truncate src`, the zero-extended low `w` bits. -/
def truncTo (w : X86.Width) (x src : VReg) : List (Inst VReg) :=
  match w with
  | .w64 => [.move x src]
  | .w32 => [.op (row .mov .w32 .RM) [x] [.r src]]
  | w => [.op (row .movzx .w32 .RM w) [x] [.r src]]

/-- `x := w.truncate a` for a Lir argument: a register, or an immediate
materialized already truncated. -/
def argTrunc (w : X86.Width) (a : Lir.Arg) : SelM (VReg × List (Inst VReg)) := do
  match a with
  | .imm k => materialize (w.truncate k)
  | .v y =>
      if w == .w64 then return (y, [])
      let x ← fresh
      return (x, truncTo w x y)

end Compilatrix.Xv.Select
