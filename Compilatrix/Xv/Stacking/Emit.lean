import Compilatrix.Xv.Stacking.Frame
import Compilatrix.Xv.Semantics
import Compilatrix.X86.Basic

/-!
# Stacking: Xl functions to typed x86 (05 §6)

Each Xl function becomes a run of typed x86 blocks:

- **Stack check** (only when `FrameLayout.checked`): `lea r11, [rsp −
  (size + slack)]` and a branch `cmp r11, [r15 − 56]; jb fail₂`, where
  `[r15 − 56]` is the context's `stackLimit` (04 §6) and `fail₂` the exit
  group's stack block (05 §6.1).
- **Label 0** starts with the rest of the prologue: `sub rsp, size`, then a
  `mov [rsp + o], r` per saved register. Label `l` is block `labelBase + l`,
  so labels keep their order.
- **Body.** Rows run on the same operands, with a stack cell (a slot, an
  incoming or an outgoing argument cell) as an `rsp`-relative memory
  operand in its r/m slot; `move` is a `mov` (never cell to cell);
  `zero x` is `xor x32, x32`; a fused `setcc` is preceded by the `xor`
  that zeroes its destination (its early definition); `call f` is a direct
  `call` to `f`'s entry, with the arguments already in the convention's
  locations.
- **Terminators.** `jmp` and `jcc` keep their targets (edges carry no
  arguments at Xl); `ret` restores the saved registers, frees the frame and
  returns; `tail f` does the same and jumps to `f`'s entry (register
  arguments only, 05 §6); `fail r` and `trap` jump to the exit group's
  `fail_k` block for status `k` (04 §6).

Every check the Xl semantics makes by getting stuck (reserved registers,
ties, fixed operands, convention locations, arities) is repeated here, so a
program that stacks names only encodable operands. Emission is a
proved-once, re-run pass (P, 05 §1.1), written in kernel-evaluable style.
-/

namespace Compilatrix.Xv.Stacking

open Compilatrix.Lir (FunId Label)

abbrev NatMap (α : Type) := Std.TreeMap Nat α compare

/-! ## Addresses and rows -/

/-- A context-block cell `[r15 + off]` (04 §6). -/
def ctxAt (off : Int) : X86.MemAddr := { base := some .r15, displacement := (Int32.ofInt off).toUInt32 }

/-- `entrySp`: the wrapper's `rsp` at its call, for the failure exit. -/
def entrySpCell : X86.MemAddr := ctxAt (-64)
/-- `stackLimit`: the lowest address a checked frame may reach. -/
def stackLimitCell : X86.MemAddr := ctxAt (-56)
/-- `stackBudget`: the stack an entry may use below `entrySp`. -/
def stackBudgetCell : X86.MemAddr := ctxAt (-48)

/-- `[rsp + off]`. -/
def rspAt (off : Nat) : X86.MemAddr := { base := some .rsp, displacement := UInt32.ofNat off }

/-- `[rsp − off]`. -/
def rspBelow (off : Nat) : X86.MemAddr :=
  { base := some .rsp, displacement := (Int32.ofInt (-(off : Int))).toUInt32 }

def cmpRM : X86.Op := { mn := .cmp, w := .w64, form := .RM }
def testMR : X86.Op := { mn := .test, w := .w64, form := .MR }
def orMR : X86.Op := { mn := .or, w := .w64, form := .MR }
def subRM : X86.Op := { mn := .sub, w := .w64, form := .RM }

def subRsp (n : Nat) : X86.Instr := X86.Instr.ofRow (X86.aluImmRow .sub .w64 (.reg .rsp) (UInt64.ofNat n))
def addRsp (n : Nat) : X86.Instr := X86.Instr.ofRow (X86.aluImmRow .add .w64 (.reg .rsp) (UInt64.ofNat n))

/-- `xor r32, r32`. -/
def zeroReg (r : X86.GPR) : X86.Instr := .op zeroRow [.reg r, .reg r]

/-- Status codes the export wrapper returns in `rax` (04 §6). -/
def statusOf : Sem.Resource → Nat
  | .heap => 1
  | .stack => 2
  | .natOverflow => 3

def trapStatus : Nat := 4

/-! ## Frames -/

/-- The prologue after the stack check: allocate the frame, save. -/
def prologue (l : FrameLayout) : List X86.Instr :=
  (if l.size == 0 then [] else [subRsp l.size]) ++
    l.saveOff.map fun (r, o) => X86.Instr.store .w64 (rspAt o) r

/-- The epilogue before `ret` or a tail call: restore, free the frame. -/
def epilogue (l : FrameLayout) : List X86.Instr :=
  l.saveOff.map (fun (r, o) => X86.Instr.load .w64 r (rspAt o)) ++
    (if l.size == 0 then [] else [addRsp l.size])

/-- The stack check (05 §6): `lea r11, [rsp − (size + slack)]; cmp r11,
[r15 − 56]; jb fail₂`, else on to label 0. -/
def stackCheck (l : FrameLayout) (fail₂ next : X86.BlockId) : X86.Block :=
  { instructions := #[X86.Instr.lea .r11 (rspBelow (l.size + slack))]
    terminator := .branch cmpRM [.reg .r11, .mem stackLimitCell] .unsignedLt fail₂ next }

/-! ## One function -/

/-- What emitting one function needs. -/
structure FnCtx where
  layout : FrameLayout
  inArgs : Nat
  /-- The block of label 0; label `l` is block `labelBase + l`. -/
  labelBase : Nat
  labels : Nat
  /-- Each function's entry block and parameter count. -/
  funcs : NatMap (Nat × Nat)
  /-- The exit group's first block (`fail₁`); `fail_k` is `exit + k − 1`. -/
  exit : Nat

namespace FnCtx

def failBlock (c : FnCtx) (k : Nat) : X86.BlockId := UInt32.ofNat (c.exit + k - 1)

def label (c : FnCtx) (l : Label) : Except String X86.BlockId :=
  if l < c.labels then pure (UInt32.ofNat (c.labelBase + l)) else throw s!"label {l} is not a block"

def callee (c : FnCtx) (g : FunId) : Except String (X86.BlockId × Nat) :=
  match c.funcs.get? g with
  | some (entry, arity) => pure (UInt32.ofNat entry, arity)
  | none => throw s!"function {g} does not exist"

/-- The frame cell of a stack location. -/
def cell (c : FnCtx) : Loc → Except String X86.MemAddr
  | .slot i =>
      match c.layout.slotOff[i]? with
      | some o => pure (rspAt o)
      | none => throw s!"slot {i} has no cell"
  | .outArg i => if i < c.layout.outArgs then pure (rspAt (8 * i)) else throw s!"outArg {i} is outside the frame"
  | .inArg i =>
      if i < c.inArgs then pure (rspAt (c.layout.size + 8 + 8 * i)) else throw s!"inArg {i} is not a parameter"
  | .reg _ => throw "a register is not a cell"

end FnCtx

/-- A register location that Xl operands may name. -/
def gpr : Loc → Except String X86.GPR
  | .reg r => if Xl.reserved r then throw s!"reserved register {repr r}" else pure r
  | _ => throw "a stack cell where a register is required"

/-- A machine address; address registers are registers, `ctx` is `r15`. -/
def amode (a : Amode Loc) : Except String X86.MemAddr :=
  match a.toMem (fun | .reg r => if Xl.reserved r then none else some r | _ => none) with
  | some m => pure m
  | none => throw "an address register is a stack cell or reserved"

namespace FnCtx

/-- A location as a machine operand: a register, or its frame cell. -/
def arg (c : FnCtx) : Loc → Except String X86.Arg
  | .reg r => (.reg ·) <$> gpr (.reg r)
  | l => (.mem ·) <$> c.cell l

/-- The machine operand of a bound slot (`Bound.isSlot`). -/
def slotArg (c : FnCtx) : Bound Loc → Except String X86.Arg
  | .input _ (.r l) | .output _ l | .tied _ l _ => c.arg l
  | .input _ (.m a) | .memory _ a => (.mem ·) <$> amode a
  | .input _ (.i w) => pure (.imm w)
  | .fixedUse .. | .fixedDef .. | .fixedTied .. => throw "an implicit operand has no slot"

/-- The machine operands of a bound row, after the placement checks of
`Xl.execBound`: cells only in r/m slots (and written only at width 64),
ties at their use's location, implicit operands at their registers. -/
def rowArgs (c : FnCtx) (bs : List (Bound Loc)) : Except String (List X86.Arg) := do
  unless bs.all Xl.Bound.placeable do throw "an operand is not placeable"
  (bs.filter Bound.isSlot).mapM c.slotArg

def bind (o : X86.Op) (defs : List Loc) (args : List (XArg Loc)) : Except String (List (Bound Loc)) :=
  match bindRow o defs args with
  | some bs => pure bs
  | none => throw s!"operands do not bind to {repr o}"

/-- A `mov` between locations; never cell to cell. -/
def move (c : FnCtx) (dst src : Loc) : Except String (List X86.Instr) :=
  if dst == src then pure []
  else match dst, src with
    | .reg d, .reg s => do pure [X86.Instr.mov .w64 (← gpr (.reg d)) (.reg (← gpr (.reg s)))]
    | .reg d, s => do pure [X86.Instr.load .w64 (← gpr (.reg d)) (← c.cell s)]
    | d, .reg s => do pure [X86.Instr.store .w64 (← c.cell d) (← gpr (.reg s))]
    | _, _ => throw "a move between stack cells"

def inst (c : FnCtx) : Inst Loc → Except String (List X86.Instr)
  | .op o defs args => do
      let xs ← c.rowArgs (← bind o defs args)
      unless o.linear && (X86.desc o).stack == .none && o.argsOk xs do
        throw s!"{repr o} is not a stack-free linear row on these operands"
      pure [.op o xs]
  | .fused p pargs q defs cargs => do
      let pb ← bind p [] pargs
      let qb ← bind q defs cargs
      let pxs ← c.rowArgs pb
      let qxs ← c.rowArgs qb
      unless p.argsOk pxs && q.argsOk qxs do throw "fused operands do not fit their rows"
      let uses := (pb ++ qb).flatMap Bound.uses
      let zeroes ← ((qb.filter Bound.narrowOutput).flatMap Bound.defs).mapM fun l => do
        if uses.contains l then throw "a zeroed destination is also a use"
        pure (zeroReg (← gpr l))
      pure (zeroes ++ [.fused p pxs q qxs])
  | .move dst src => c.move dst src
  | .zero x => do pure [zeroReg (← gpr x)]
  | .call g args rets => do
      unless Xl.conventionArgs args && Xl.conventionResults rets do
        throw "call operands are off the convention"
      let (entry, arity) ← c.callee g
      unless args.length == arity do throw s!"call to {g} with {args.length} of {arity} arguments"
      pure [.call entry]

def edge (c : FnCtx) (e : Edge Loc) : Except String X86.BlockId := do
  unless e.args.isEmpty do throw "an edge passes arguments"
  c.label e.target

def term (c : FnCtx) : Term Loc → Except String (List X86.Instr × X86.Terminator)
  | .jmp e => do pure ([], .jump (← c.edge e))
  | .jcc p pargs defs cond t f => do
      let xs ← c.rowArgs (← bind p defs pargs)
      unless p.argsOk xs do throw "branch operands do not fit the producer"
      pure ([], .branch p xs cond (← c.edge t) (← c.edge f))
  | .ret vs => do
      unless Xl.conventionResults vs do throw "results are off the convention"
      pure (epilogue c.layout, .ret)
  | .tail g args => do
      unless args.length ≤ Xl.nArgRegs && Xl.conventionArgs args do
        throw "tail-call arguments are off the convention or on the stack"
      let (entry, arity) ← c.callee g
      unless args.length == arity do throw s!"tail call to {g} with {args.length} of {arity} arguments"
      pure (epilogue c.layout, .tailCall entry)
  | .fail r => pure ([], .jump (c.failBlock (statusOf r)))
  | .trap => pure ([], .jump (c.failBlock trapStatus))

def block (c : FnCtx) (pre : List X86.Instr) (b : Block Loc) : Except String X86.Block := do
  unless b.params.isEmpty do throw "a block has parameters"
  let body ← b.body.toList.zipIdx.mapM fun (i, k) => (c.inst i).mapError (s!"instruction {k}: " ++ ·)
  let (post, t) ← (c.term b.term).mapError ("terminator: " ++ ·)
  pure { instructions := (pre ++ body.flatten ++ post).toArray, terminator := t }

end FnCtx

/-- The blocks of one function starting at block `start`: the stack check
(if any), then one block per label. -/
def emitFunc (funcs : NatMap (Nat × Nat)) (exit : Nat) (f : Func Loc) (l : FrameLayout) (a : Facts)
    (start : Nat) : Except String (List X86.Block) := do
  unless f.blocks.size != 0 do throw "no blocks"
  unless a.inArgsUsed ≤ a.inArgs do throw "reads an incoming cell past its parameters"
  unless f.blocks.toList.all (fun b => !b.term.succs.contains 0) do throw "the entry block has a predecessor"
  let chk := FrameLayout.checked a l
  let shift := if chk then 1 else 0
  let c : FnCtx := { layout := l, inArgs := a.inArgs, labelBase := start + shift, labels := f.blocks.size, funcs, exit }
  let body ← f.blocks.toList.zipIdx.mapM fun (b, lbl) =>
    (c.block (if lbl == 0 then prologue l else []) b).mapError (s!"block {lbl}: " ++ ·)
  pure ((if chk then [stackCheck l (c.failBlock 2) (UInt32.ofNat (start + 1))] else []) ++ body)

/-- How many blocks `emitFunc` produces. -/
def funcBlocks (f : Func Loc) (l : FrameLayout) (a : Facts) : Nat :=
  (if FrameLayout.checked a l then 1 else 0) + f.blocks.size

end Compilatrix.Xv.Stacking
