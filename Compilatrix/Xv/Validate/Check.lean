import Compilatrix.Xv.Validate.State
import Compilatrix.Xv.Alloc.Apply

/-!
# The allocation validator

`Validate.func env p fi f o` checks an allocation `o` of Xv function `f`
(05 §5): a forward pass over each block from its certificate, through the
edits and instructions, with local checks on every edge instead of a
fixpoint. It accepts only allocations whose Xl code (`Alloc.apply f o`)
runs in lock-step with `f`; its soundness (`Validate.sound`,
`program_sound`) is M2 work. It assumes nothing about the allocator, and
nothing about `f` beyond its operand metadata (`Inst.operands`, derived
from the table rows by M1.B3).

**Per instruction** (`stepInst`), on the state before it:
1. every use, early or late, finds its register at its location
   (regalloc2 gap 3);
2. locations are usable: registers from the allocatable set, never `rsp`,
   `rbp` or the context register `r15`, including fixed registers (gap 5);
   slots below `numSlots`; incoming cells of this function's stack
   parameters; outgoing cells only where the convention puts them;
3. constraints: `reg` a register, `any` a register or cell, `stack` a
   cell, `fixed r` exactly `r`, `reuse i` the location of use `i`, which
   must be an early use;
4. aliasing (05 §3): distinct definitions (as registers and as
   locations), early definitions off every use location (gap 4), late uses
   off every definition location;
5. Xl's remaining stuck cases: a row's stack cells must fit the scratch
   registers it does not name; calls, returns and tail calls take exactly
   the convention's locations, at most two results, and tail calls at most
   seven arguments; a move is never cell to cell.

Then each definition forgets its register everywhere and holds its
location; a call also forgets the callee's clobber set (`Xl.Env.clobbers`)
and every outgoing cell.

**Edits** are moves (`AState.stepMove`, gap 1) with the same location
rules; outgoing cells are allowed as their endpoints (argument setup). A
move's source must hold something known: Xl's move is stuck on an undefined
location, so gap 1's erasing transfer alone would accept code that gets
stuck (a borrowed victim register saved while empty, for instance).

**Edges and the entry.** After each terminator, every edge `b → s` checks
`cert s ≤ bindParams (state) s.params args`; block 0's certificate must
also be below the entry convention's state (gap 2: no `Top`). Nothing
follows a terminator (gap 7); the code checked is the code `apply` builds.
Gap 6 (trusted operand descriptions) is closed where the metadata is
derived (M1.B3).

The whole pass recurses structurally over lists and uses `NatMap`, so the
kernel can evaluate it (D17, M1.K1).
-/

namespace Compilatrix.Xv.Validate

open Compilatrix.Lir (VReg Label FunId Operand Kind Pos Con)
open Compilatrix.Xv.Alloc (Edit Output BlockOut takeAt editsOrdered)

/-- Why an allocation is rejected. -/
inductive Code where
  /-- Location or block counts differ from the function's. -/
  | shape
  /-- Edits out of order, or after the terminator. -/
  | editOrder
  /-- A use's register is not known to be at its location. -/
  | useMissing
  /-- `rsp`, `rbp` or `r15` as an operand or a move endpoint. -/
  | reserved
  /-- A slot at or beyond `numSlots`, an incoming cell the function does not
  have, or an outgoing cell outside argument setup. -/
  | cellRange
  /-- A `reg`, `any`, `stack` or `fixed` constraint is not met. -/
  | constraint
  /-- A `reuse` definition is not at its use's location. -/
  | tie
  /-- Definitions share a location, an early definition sits on a use, or a
  late use on a definition. -/
  | alias
  /-- A move from one stack cell to another. -/
  | cellMove
  /-- Call, return or tail-call operands off the convention. -/
  | convention
  /-- More stack cells than free scratch registers in one row. -/
  | cells
  /-- A function or block lists a parameter twice. -/
  | params
  /-- Block 0's certificate claims more than the entry convention gives. -/
  | entry
  /-- A certificate claims more than an incoming edge gives. -/
  | edge
  /-- An edge to a block that does not exist. -/
  | missingBlock
  /-- A move from a location holding nothing known: Xl's move is stuck on an
  undefined source, so the validator requires a known one. -/
  | unknownSource
  deriving DecidableEq, Repr, Inhabited

def Code.name : Code → String
  | .shape => "shape" | .editOrder => "editOrder" | .useMissing => "useMissing" | .reserved => "reserved"
  | .cellRange => "cellRange" | .constraint => "constraint" | .tie => "tie" | .alias => "alias"
  | .cellMove => "cellMove" | .convention => "convention" | .cells => "cells" | .params => "params"
  | .entry => "entry" | .edge => "edge" | .missingBlock => "missingBlock" | .unknownSource => "unknownSource"

structure Err where
  fn : Nat := 0
  block : Nat := 0
  /-- A body position (edits before instruction `pos`); the body size is the
  terminator; one more is its edges. -/
  pos : Nat := 0
  code : Code
  deriving DecidableEq, Repr, Inhabited

def Err.text (e : Err) : String :=
  s!"function {e.fn} block {e.block} position {e.pos}: {e.code.name}"

/-- What the checks of one function need. -/
structure Ctx where
  env : Xl.Env
  numSlots : Nat
  /-- Parameters passed in incoming cells. -/
  stackParams : Nat

/-! ## Locations -/

def allocatable (r : X86.GPR) : Bool := !Xl.reserved r

def isOutArg : Loc → Bool
  | .outArg _ => true
  | _ => false

/-- A location an operand may name: an allocatable register, a slot, or an
incoming cell of this function. -/
def locCode (c : Ctx) : Loc → Option Code
  | .reg r => if allocatable r then none else some .reserved
  | .slot i => if i < c.numSlots then none else some .cellRange
  | .inArg i => if i < c.stackParams then none else some .cellRange
  | .outArg _ => some .cellRange

/-- A location a move may name: an operand location or an outgoing cell. -/
def editLocCode (c : Ctx) : Loc → Option Code
  | .outArg _ => none
  | l => locCode c l

def conOk (con : Con) (l : Loc) : Bool :=
  match con, l with
  | .any, _ => true
  | .reg, .reg _ => true
  | .reg, _ => false
  | .stack, l => l.isCell
  | .fixed r, l => l == .reg r
  | .reuse _, _ => true

def firstCode : List (Option Code) → Option Code
  | [] => none
  | some c :: _ => some c
  | none :: cs => firstCode cs

def allDistinct : List Loc → Bool
  | [] => true
  | l :: ls => !ls.contains l && allDistinct ls

/-- Registers without repetition. Xv binds a register defined twice by one
instruction (or passed as a parameter twice) to the last value, so the
symbolic transfer, which gives each definition its own location, would
claim a stale value; such code is rejected. -/
def nodup : List VReg → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodup xs

/-! ## Instructions -/

/-- Uses, then definitions, as `(operand, location)` pairs. -/
abbrev Pairs := List (Operand VReg × Loc)

def usesOf (ps : Pairs) : Pairs := ps.filter fun (o, _) => o.kind == .use

def defsOf (ps : Pairs) : Pairs := ps.filter fun (o, _) => o.kind == .define

def tieOk (ps : Pairs) : Operand VReg × Loc → Bool
  | (o, l) =>
      match o.con with
      | .reuse i =>
          match ps[i]? with
          | some (u, lu) => o.kind == .define && u.kind == .use && u.pos == .early && lu == l
          | none => false
      | _ => true

/-- The checks common to rows, moves and the zeroing idiom: locations,
constraints, ties, aliasing and cell pressure. -/
def operandCode (c : Ctx) (ps : Pairs) (row : Bool) : Option Code :=
  match firstCode (ps.map fun (_, l) => locCode c l) with
  | some code => some code
  | none =>
  if !ps.all (fun (o, l) => conOk o.con l) then some .constraint else
  if !ps.all (tieOk ps) then some .tie else
  let useLocs := (usesOf ps).map (·.2)
  let defs := defsOf ps
  if !allDistinct (defs.map (·.2)) || !nodup (defs.map (·.1.v)) then some .alias else
  if defs.any (fun (o, l) => o.pos == .early && useLocs.contains l) then some .alias else
  if (usesOf ps).any (fun (o, l) => o.pos == .late && defs.any (·.2 == l)) then some .alias else
  let locs := dedup (ps.map (·.2))
  if row && (locs.filter Loc.isCell).length + (locs.filter (!·.isCell)).length > scratch.length then
    some .cells
  else none

/-- Every use holds at its location. -/
def usesHold (a : AState) (ps : Pairs) : Bool :=
  (usesOf ps).all fun (o, l) => a.holds l o.v

def defsOfPairs (ps : Pairs) : List (VReg × Loc) := (defsOf ps).map fun (o, l) => (o.v, l)

def argLocs (n : Nat) : List Loc := (List.range n).map Xl.argLoc

def resultLocs (n : Nat) : List Loc := (List.range n).filterMap Xl.resultLoc

/-- A generic instruction: checks, then definitions. -/
def stepOperands (c : Ctx) (a : AState) (ops : List (Operand VReg)) (ls : List Loc) (row : Bool) :
    Except Code AState := do
  unless ops.length == ls.length do throw .shape
  let ps := ops.zip ls
  if let some code := operandCode c ps row then throw code
  unless usesHold a ps do throw .useMissing
  pure (a.define (defsOfPairs ps) [])

def stepInst (c : Ctx) (a : AState) (inst : Inst VReg) (ls : List Loc) : Except Code AState :=
  match inst with
  | .call g args rets => do
      let ops := inst.operands
      unless ops.length == ls.length do throw .shape
      let n := args.length
      unless rets.length ≤ Xl.nResultRegs do throw .convention
      unless nodup rets do throw .alias
      unless ls.take n == argLocs n && ls.drop n == resultLocs rets.length do throw .convention
      unless (args.zip (argLocs n)).all (fun (v, l) => a.holds l v) do throw .useMissing
      let clobbers := (c.env.clobbers g).map Loc.reg
      pure ((a.clearOutArgs).define (rets.zip (resultLocs rets.length)) clobbers)
  | .move .. => do
      match ls with
      | [src, dst] => if src.isCell && dst.isCell then throw .cellMove
      | _ => pure ()
      stepOperands c a inst.operands ls false
  | .zero _ => stepOperands c a inst.operands ls false
  | .op .. | .fused .. => stepOperands c a inst.operands ls true

def stepTerm (c : Ctx) (a : AState) (t : Term VReg) (ls : List Loc) : Except Code AState :=
  match t with
  | .jcc .. => stepOperands c a t.operands ls true
  | .ret vs => do
      unless vs.length ≤ Xl.nResultRegs && ls == resultLocs vs.length do throw .convention
      unless (vs.zip ls).all (fun (v, l) => a.holds l v) do throw .useMissing
      pure a
  | .tail _ args => do
      unless args.length ≤ Xl.nArgRegs && ls == argLocs args.length do throw .convention
      unless (args.zip ls).all (fun (v, l) => a.holds l v) do throw .useMissing
      pure a
  | .jmp _ | .fail _ | .trap => do
      unless ls.isEmpty do throw .shape
      pure a

def stepEdit (c : Ctx) (a : AState) : Edit → Except Code AState
  | .move dst src => do
      if let some code := editLocCode c dst then throw code
      if let some code := editLocCode c src then throw code
      if dst.isCell && src.isCell then throw .cellMove
      if (a.get src).isEmpty then throw .unknownSource
      pure (a.stepMove dst src)

def stepEdits (c : Ctx) : AState → List Edit → Except Code AState
  | a, [] => pure a
  | a, e :: es => do stepEdits c (← stepEdit c a e) es

/-! ## Blocks and functions -/

/-- Parameters and certificate of each block, by label. -/
abbrev BlockInfo := NatMap (List VReg × AState)

def blockInfo (blocks : List (Block VReg)) (outs : List BlockOut) : BlockInfo :=
  ((blocks.zip outs).zipIdx).foldl
    (fun m ((b, o), l) => m.insert l (b.params, AState.ofList o.cert)) .leaf

/-- The state after the body: edits and instructions in order. `i` is the
position; errors carry it. -/
def walkBody (c : Ctx) : AState → List (Inst VReg) → List (List Loc) → List (Nat × Edit) → Nat →
    Except (Nat × Code) (AState × List (Nat × Edit))
  | a, [], [], es, _ => pure (a, es)
  | a, inst :: insts, ls :: lss, es, i => do
      let (now, later) := takeAt i es
      let a ← (stepEdits c a now).mapError (i, ·)
      let a ← (stepInst c a inst ls).mapError (i, ·)
      walkBody c a insts lss later (i + 1)
  | _, _, _, _, i => throw (i, .shape)

/-- Check every edge of a terminator against its target's certificate. -/
def checkEdges (info : BlockInfo) (a : AState) : List (Edge VReg) → Option Code
  | [] => none
  | e :: es =>
      match info.find? e.target with
      | none => some .missingBlock
      | some (params, cert) =>
          if params.length != e.args.length then some .shape
          else if !cert.le (a.bindParams params e.args) then some .edge
          else checkEdges info a es

def checkBlock (c : Ctx) (info : BlockInfo) (b : Block VReg) (o : BlockOut) : Except (Nat × Code) Unit := do
  let body := b.body.toList
  let n := body.length
  unless nodup b.params do throw (0, .params)
  unless editsOrdered n o.edits 0 do throw (0, .editOrder)
  let (a, left) ← walkBody c (AState.ofList o.cert) body o.locs o.edits 0
  let (now, rest) := takeAt n left
  unless rest.isEmpty do throw (n, .editOrder)
  let a ← (stepEdits c a now).mapError (n, ·)
  let a ← (stepTerm c a b.term o.termLocs).mapError (n, ·)
  if let some code := checkEdges info a b.term.edges then throw (n + 1, code)

/-- The state the entry convention gives: parameter `i` at `Xl.paramLoc i`. -/
def entryState (params : List VReg) : AState :=
  params.zipIdx.foldl (fun a (p, i) => a.set (Xl.paramLoc i) [p]) AState.empty

def checkBlocks (c : Ctx) (fi : Nat) (info : BlockInfo) :
    List (Block VReg) → List BlockOut → Nat → Except Err Unit
  | [], [], _ => pure ()
  | b :: bs, o :: os, l => do
      match checkBlock c info b o with
      | .error (pos, code) => throw { fn := fi, block := l, pos, code }
      | .ok () => checkBlocks c fi info bs os (l + 1)
  | _, _, l => throw { fn := fi, block := l, code := .shape }

/-- Validate allocation `o` of function `fi` (`f`). -/
def func (env : Xl.Env) (fi : Nat) (f : Func VReg) (o : Output) : Except Err Unit := do
  let blocks := f.blocks.toList
  unless blocks.length == o.blocks.length do throw { fn := fi, code := .shape }
  unless nodup f.params do throw { fn := fi, code := .params }
  let c : Ctx := { env, numSlots := o.numSlots, stackParams := f.params.length - Xl.nArgRegs }
  match o.blocks with
  | [] => throw { fn := fi, code := .shape }
  | o0 :: _ =>
      unless (AState.ofList o0.cert).le (entryState f.params) do throw { fn := fi, code := .entry }
  checkBlocks c fi (blockInfo blocks o.blocks) blocks o.blocks 0

/-- Validate one allocation per function. -/
def program (env : Xl.Env) (p : VProgram) (outs : List Output) : Except Err Unit :=
  go p.funcs.toList outs 0
where
  go : List (Func VReg) → List Output → Nat → Except Err Unit
    | [], [], _ => pure ()
    | f :: fs, o :: os, i => do func env i f o; go fs os (i + 1)
    | _, _, i => throw { fn := i, code := .shape }

/-- Whether allocation `o` of `f` is accepted (for kernel evaluation). -/
def accepts (env : Xl.Env) (f : Func VReg) (o : Output) : Bool := (func env 0 f o).toBool

/-- The recheck step for allocation (D17): validate, then build the Xl
program that was validated. -/
def run (env : Xl.Env) (p : VProgram) (outs : List Output) : Except String LProgram := do
  match program env p outs with
  | .error e => throw e.text
  | .ok () => Alloc.applyProgram p outs

end Compilatrix.Xv.Validate
