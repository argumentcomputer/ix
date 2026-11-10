import IxCC.Xv.Stacking.Wrapper
import IxCC.X86.Layout.Basic
import IxCC.X86.CheckK

/-!
# Stacking a program

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

**Clobber sets**. The allocation validator trusts `Xl.Env.clobbers`:
after a call it keeps the caller's values in every register outside the
callee's declared set. Stacking checks the declaration against the code it
emits: what each function writes and does not save, `r11` for a stack
check, and what its callees may change must lie within its clobbers and
result registers. The default (every caller-saved register) always passes;
a runtime procedure declaring less is checked here. -/

namespace IxCC.Xv.Stacking

open IxCC.Lir (FunId)

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
  (`Xl.Env.clobbers`) and results, or declares a callee-saved register
  clobbered. -/
  | clobbers (fn : FunId) (extra : List X86.GPR)
  /-- The emitted program is not a well-formed typed program
  (`X86.Program.wellFormed`). -/
  | malformed
  /-- A call, a return or a tail call disagrees with a function's declared
  result count. -/
  | arity (fn : FunId)
  deriving DecidableEq, Repr, Inhabited

def Error.toString : Error → String
  | .layouts e g => s!"stacking: {g} frame layouts for {e} functions"
  | .layout fn => s!"stacking: the frame layout of function {fn} fails its check"
  | .func fn why => s!"stacking: function {fn}: {why}"
  | .export fn why => s!"stacking: the wrapper of function {fn}: {why}"
  | .noEntry => "stacking: main is not a SysV export"
  | .tooLarge n => s!"stacking: {n} blocks"
  | .clobbers fn extra => s!"stacking: function {fn} changes {repr extra} beyond its declared clobbers"
  | .malformed => "stacking: the emitted program is not well formed"
  | .arity fn => s!"stacking: function {fn} calls, returns or tail-calls with a result count its callee or itself does not declare"

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

/-- The oracle's layouts: one per function, from its facts. -/
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

/-- Each function with its number, its layout and its facts. -/
def withLayouts (p : LProgram) (layouts : List FrameLayout) : List (Func Loc × FunId × FrameLayout × Facts) :=
  (p.funcs.toList.zipIdx.zip layouts).map fun ((f, fn), l) => (f, fn, l, f.facts)

/-- The result registers of the functions a function tail-calls: a tail call
returns to the caller's caller, so its callee's results are changes the
caller must allow. -/
def tailResults (p : LProgram) (f : Func Loc) : List X86.GPR :=
  f.blocks.toList.flatMap fun b =>
    match b.term with
    | .tail g _ => Lir.Conv.resultRegs.take ((p.funcs.toList[g]?.map (·.results)).getD 0)
    | _ => []

/-- The registers a function may change beyond what its callers allow
(`allowedChanges`): what it and its callees may change, and what its tail
callees return in; and the callee-saved registers its declaration claims it
may change (a call must keep them). -/
def extraChanges (p : LProgram) (env : Xl.Env) (f : Func Loc) (fn : FunId) (l : FrameLayout) (a : Facts) :
    List X86.GPR :=
  (mayChange env f a l ++ tailResults p f).filter (!(allowedChanges env fn f).contains ·) ++
    (env.clobbers fn).filter (fun r => !X86.SysV.callerSaved.toList.contains r)

/-- A function's declared result count. -/
def resultsOf (p : LProgram) (g : FunId) : Option Nat := (p.funcs.toList[g]?).map (·.results)

/-- Every call binds, every return returns, and every tail callee declares,
as many results as expected: `allowedChanges` counts a callee's result
registers by its declaration, Xl by the values it returns. -/
def aritiesOk (p : LProgram) (f : Func Loc) : Bool :=
  f.blocks.toList.all fun b =>
    b.body.toList.all (fun | .call g _ rets => resultsOf p g == some rets.length | _ => true) &&
      match b.term with
      | .ret vs => vs.length == f.results
      | .tail g _ => resultsOf p g == some f.results
      | _ => true

/-- The exports, with their argument passing. -/
def exportsOf (reps : FunId → Option (List ArgRep)) (fns : List (Func Loc × FunId × FrameLayout × Facts)) :
    List (FunId × String × List ArgRep × Func Loc) :=
  fns.filterMap fun (f, fn, _, _) =>
    match f.conv with
    | .sysvExport s => some (fn, s, exportReps reps fn f, f)
    | .internal => none

/-- The wrappers' first blocks, after the exit group, and the next free block. -/
def placeExports (exports : List (FunId × String × List ArgRep × Func Loc)) : List PlacedExport × Nat :=
  exports.foldl (init := ([], exitBlocks)) fun (acc, n) (fn, symbol, rs, _) =>
    (acc ++ [({ fn, symbol, reps := rs, start := n } : PlacedExport)], n + wrapperBlocks rs)

/-- The functions' first blocks, from block `next`, and the block count. -/
def placeFuncs (fns : List (Func Loc × FunId × FrameLayout × Facts)) (next : Nat) : List Placed × Nat :=
  fns.foldl (init := ([], next)) fun (acc, n) (func, fn, layout, facts) =>
    (acc ++ [({ func, fn, layout, facts, start := n } : Placed)], n + funcBlocks func layout facts)

/-- Each function's entry block and parameter count. -/
def entriesOf (placed : List Placed) : NatMap (Nat × Nat) :=
  placed.foldl (init := {}) fun m pl => m.insert pl.fn (pl.start, pl.func.params.length)

/-- The wrapper of an export calling its function's entry. -/
def wrapperOf (entries : NatMap (Nat × Nat)) (w : PlacedExport) (f : Func Loc) : Except Error (List X86.Block) := do
  unless f.results == 1 do throw (.export w.fn "an export returns one value")
  unless w.reps.length == f.params.length do throw (.export w.fn "one representation per parameter")
  let some (entry, _) := entries.get? w.fn | throw (.export w.fn "no entry")
  (wrapper (UInt32.ofNat entry) (UInt32.ofNat (0 + statusOf .natOverflow - 1)) w.reps w.start).mapError
    (.export w.fn)

/-- The layout shape: wrappers, functions, then the exit group, so an
export's symbol starts the text. -/
def groupsOf (wrappers : List PlacedExport) (placed : List Placed) : List X86.Layout.Group :=
  (wrappers.map fun w => { start := w.start, count := wrapperBlocks w.reps, entry := some w.start }) ++
  (placed.map fun pl =>
    { start := pl.start, count := funcBlocks pl.func pl.layout pl.facts, entry := some pl.start,
      cold := coldBlocks pl }) ++
  [{ start := 0, count := exitBlocks, cold := (List.range exitBlocks).map (0 + ·) }]

def run (p : LProgram) (layouts : List FrameLayout) (reps : FunId → Option (List ArgRep) := fun _ => none)
    (env : Xl.Env := {}) : Except Error Stacked := do
  let funcs := p.funcs.toList.zipIdx
  unless layouts.length == funcs.length do throw (.layouts funcs.length layouts.length)
  let checkedFns := withLayouts p layouts
  match checkedFns.find? (fun (_, _, l, a) => !l.check a) with
  | some (_, fn, _, _) => throw (.layout fn)
  | none => pure ()
  -- The validator trusts `env.clobbers`: every function must change
  -- no register its callers assume it keeps.
  match checkedFns.find? (fun (f, fn, l, a) => !(extraChanges p env f fn l a).isEmpty) with
  | some (f, fn, l, a) => throw (.clobbers fn (extraChanges p env f fn l a))
  | none => pure ()
  match checkedFns.find? (fun (f, _, _, _) => !aritiesOk p f) with
  | some (_, fn, _, _) => throw (.arity fn)
  | none => pure ()
  let exports := exportsOf reps checkedFns
  let (wrappers, next) := placeExports exports
  let (placed, total) := placeFuncs checkedFns next
  unless total < 2 ^ 32 do throw (.tooLarge total)
  let entries := entriesOf placed
  let wrapperCode ← (wrappers.zip exports).mapM fun (w, (_, _, _, f)) => wrapperOf entries w f
  let funcCode ← placed.mapM fun pl =>
    (emitFunc entries 0 pl.func pl.layout pl.facts pl.start).mapError (.func pl.fn)
  let some main := wrappers.find? (·.fn == p.main) | throw .noEntry
  let program : X86.Program :=
    { blocks := (exitGroup 0 ++ wrapperCode.flatten ++ funcCode.flatten).toArray, entry := UInt32.ofNat main.start }
  unless program.wellFormedK do throw .malformed
  pure {
    program
    shape := { groups := groupsOf wrappers placed, roots := wrappers.map (·.start) }
    exports := wrappers.map fun w => { fn := w.fn, symbol := w.symbol, block := w.start } }

end IxCC.Xv.Stacking
