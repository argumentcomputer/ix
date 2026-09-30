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
  deriving DecidableEq, Repr, Inhabited

def Error.toString : Error → String
  | .layouts e g => s!"stacking: {g} frame layouts for {e} functions"
  | .layout fn => s!"stacking: the frame layout of function {fn} fails its check"
  | .func fn why => s!"stacking: function {fn}: {why}"
  | .export fn why => s!"stacking: the wrapper of function {fn}: {why}"
  | .noEntry => "stacking: main is not a SysV export"
  | .tooLarge n => s!"stacking: {n} blocks"

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

def run (p : LProgram) (layouts : List FrameLayout) (reps : FunId → Option (List ArgRep) := fun _ => none) :
    Except Error Stacked := do
  let funcs := p.funcs.toList.zipIdx
  unless layouts.length == funcs.length do throw (.layouts funcs.length layouts.length)
  let checkedFns := (funcs.zip layouts).map fun ((f, fn), l) => (f, fn, l, f.facts)
  match checkedFns.find? (fun (_, _, l, a) => !l.check a) with
  | some (_, fn, _, _) => throw (.layout fn)
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
