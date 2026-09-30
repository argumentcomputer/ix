import Compilatrix.Xv.Stacking.Wrapper
import Compilatrix.X86.Layout.Basic

/-!
# Stacking a program (05 §6)

`Stacking.run p layouts` checks each function's `FrameLayout` (the
certificate, one per function, from `Stacking.produce` or elsewhere), then
emits one typed x86 program:

```text
[0, 5)                       the exit group: fail₁ … fail₄, failExit (laid out last)
wrappers                     one per sysvExport function, in function order
functions                    per function: the stack check (if any), then one block per label
```

The program starts at `main`'s wrapper, which must exist. Besides the
program, `run` returns its layout shape (a group per function, wrapper and
the exit group, with the blocks to place last) and the exported symbols.
Kernel-evaluable style: lists, folds, and a persistent map from function
to entry block.

**Clobber sets** (06 S15). The allocation validator trusts `Xl.Env.clobbers`:
after a call it keeps the caller's values in every register outside the
callee's declared set. Stacking checks the declaration against the code it
emits: what each function writes and does not save, `r11` for a stack
check, and what its callees may change must lie within its clobbers and
result registers. The default (every caller-saved register) always passes;
a runtime procedure declaring less (04 §7) is checked here.
-/

namespace Compilatrix.Xv.Stacking

open Compilatrix.Lir (FunId)

inductive Error where
  /-- A layout per function is required. -/
  | layouts (expected given : Nat)
  /-- `FrameLayout.check` rejected the layout of a function. -/
  | layout (fn : FunId)
  | func (fn : FunId) (why : String)
  | «export» (fn : FunId) (why : String)
  /-- `main` is not a SysV export, so nothing can call the program. -/
  | noEntry
  | tooLarge (blocks : Nat)
  /-- A function may change registers outside its declared clobber set
  (`Xl.Env.clobbers`) and results. -/
  | clobbers (fn : FunId) (extra : List X86.GPR)
  deriving DecidableEq, Repr, Inhabited

def Error.toString : Error → String
  | .layouts e g => s!"stacking: {g} frame layouts for {e} functions"
  | .layout fn => s!"stacking: the frame layout of function {fn} fails its check"
  | .func fn why => s!"stacking: function {fn}: {why}"
  | .export fn why => s!"stacking: the wrapper of function {fn}: {why}"
  | .noEntry => "stacking: main is not a SysV export"
  | .tooLarge n => s!"stacking: {n} blocks"
  | .clobbers fn extra => s!"stacking: function {fn} changes {repr extra} beyond its declared clobbers"

instance : ToString Error := ⟨Error.toString⟩

/-- An exported symbol and its wrapper's entry block. -/
structure Export where
  fn : FunId
  symbol : String
  block : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The stacked program, its layout shape and its exports. -/
structure Stacked where
  program : X86.Program
  shape : X86.Layout.Shape
  exports : List Export
  deriving Repr, Inhabited

/-- The oracle's layouts (05 §6): one per function, from its facts. -/
def produce (p : LProgram) : List FrameLayout :=
  p.funcs.toList.map fun f => FrameLayout.produce f.facts

/-- A function with its layout, facts and first block. -/
structure Placed where
  func : Func Loc
  fn : FunId
  layout : FrameLayout
  facts : Facts
  start : Nat

/-- An export with its argument passing and first block. -/
structure PlacedExport where
  fn : FunId
  symbol : String
  reps : List ArgRep
  start : Nat

/-- An export passes each argument as a `Nat` unless told otherwise. -/
def exportReps (reps : FunId → Option (List ArgRep)) (fn : FunId) (f : Func Loc) : List ArgRep :=
  (reps fn).getD (List.replicate f.params.length .nat)

/-- The labels of a function's cold blocks, as program blocks. -/
def coldBlocks (pl : Placed) : List Nat :=
  let shift := if FrameLayout.checked pl.facts pl.layout then 1 else 0
  pl.func.blocks.toList.zipIdx.filterMap fun (b, l) => if b.cold then some (pl.start + shift + l) else none

/-- The functions a function calls or tail-calls. -/
def callees (f : Func Loc) : List FunId :=
  f.blocks.toList.flatMap fun b =>
    b.body.toList.filterMap (fun | .call g _ _ => some g | _ => none) ++
      match b.term with
      | .tail g _ => [g]
      | _ => []

/-- The registers a call to a function may change, as its caller sees them
once the emitted code runs: those it writes and does not save, `r11` if its
prologue checks the stack, and whatever its own calls and tail calls may
change (their declared clobbers). -/
def mayChange (env : Xl.Env) (f : Func Loc) (a : Facts) (l : FrameLayout) : List X86.GPR :=
  a.writes.filter (!l.saved.contains ·) ++ (if FrameLayout.checked a l then [.r11] else []) ++
    (callees f).flatMap env.clobbers

/-- The registers a call may change in Xl (`Xl.returnRegs`): the callee's
declared clobbers and its result registers. -/
def allowedChanges (env : Xl.Env) (fn : FunId) (f : Func Loc) : List X86.GPR :=
  env.clobbers fn ++ Lir.Conv.resultRegs.take f.results

def run (p : LProgram) (layouts : List FrameLayout) (reps : FunId → Option (List ArgRep) := fun _ => none)
    (env : Xl.Env := {}) : Except Error Stacked := do
  let funcs := p.funcs.toList.zipIdx
  unless layouts.length == funcs.length do throw (.layouts funcs.length layouts.length)
  let checkedFns := (funcs.zip layouts).map fun ((f, fn), l) => (f, fn, l, f.facts)
  match checkedFns.find? (fun (_, _, l, a) => !l.check a) with
  | some (_, fn, _, _) => throw (.layout fn)
  | none => pure ()
  -- The validator trusts `env.clobbers` (06 S15): every function must change
  -- no register its callers assume it keeps.
  let extra (f : Func Loc) (fn : FunId) (l : FrameLayout) (a : Facts) : List X86.GPR :=
    (mayChange env f a l).filter (!(allowedChanges env fn f).contains ·)
  match checkedFns.find? (fun (f, fn, l, a) => !(extra f fn l a).isEmpty) with
  | some (f, fn, l, a) => throw (.clobbers fn (extra f fn l a))
  | none => pure ()
  let exports := checkedFns.filterMap fun (f, fn, _, _) =>
    match f.conv with
    | .sysvExport s => some (fn, s, exportReps reps fn f, f)
    | .internal => none
  let exit := 0
  let (wrappers, next) := exports.foldl (init := ([], exitBlocks)) fun (acc, n) (fn, symbol, rs, _) =>
    (acc ++ [({ fn, symbol, reps := rs, start := n } : PlacedExport)], n + wrapperBlocks rs)
  let (placed, total) := checkedFns.foldl (init := ([], next)) fun (acc, n) (func, fn, layout, facts) =>
    (acc ++ [({ func, fn, layout, facts, start := n } : Placed)], n + funcBlocks func layout facts)
  unless total < 2 ^ 32 do throw (.tooLarge total)
  let entries : NatMap (Nat × Nat) := placed.foldl (init := {}) fun m pl =>
    m.insert pl.fn (pl.start, pl.func.params.length)
  let wrapperCode ← (wrappers.zip exports).mapM fun (w, (_, _, _, f)) => do
    unless f.results == 1 do throw (.export w.fn "an export returns one value")
    unless w.reps.length == f.params.length do throw (.export w.fn "one representation per parameter")
    let some (entry, _) := entries.get? w.fn | throw (.export w.fn "no entry")
    (wrapper (UInt32.ofNat entry) (UInt32.ofNat (exit + statusOf .natOverflow - 1)) w.reps w.start).mapError
      (.export w.fn)
  let funcCode ← placed.mapM fun pl =>
    (emitFunc entries exit pl.func pl.layout pl.facts pl.start).mapError (.func pl.fn)
  let some main := wrappers.find? (·.fn == p.main) | throw .noEntry
  -- Laid out as wrappers, functions, then the exit group, so an export's
  -- symbol starts the text.
  let groups : List X86.Layout.Group :=
    (wrappers.map fun w => { start := w.start, count := wrapperBlocks w.reps, entry := some w.start }) ++
    (placed.map fun pl =>
      { start := pl.start, count := funcBlocks pl.func pl.layout pl.facts, entry := some pl.start,
        cold := coldBlocks pl }) ++
    [{ start := exit, count := exitBlocks, cold := (List.range exitBlocks).map (exit + ·) }]
  pure {
    program := { blocks := (exitGroup exit ++ wrapperCode.flatten ++ funcCode.flatten).toArray,
                 entry := UInt32.ofNat main.start }
    shape := { groups, roots := wrappers.map (·.start) }
    exports := wrappers.map fun w => { fn := w.fn, symbol := w.symbol, block := w.start } }

end Compilatrix.Xv.Stacking
