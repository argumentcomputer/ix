import IxCC.Backend
import IxCC.Rt.Backend
import IxCC.Cfg.Rc.Public
import IxCC.Recheck.Rc.Replay
import IxCCTests.Backend.Programs

/-! # Stacking's array reads and one-pass placements against their first forms

`Stacking.run` reads a callee's declared result count from the function array (`resultsOf`,
`tailResults`) and places wrappers and functions in one pass (`placeExports`, `placeFuncs`);
`Xv/Stacking/Proof/Linear.lean` proves each equal to its first form (`resultsOfList`,
`tailResultsList`, `placeExportsList`, `placeFuncsList`). Tested before it was landed, and kept:
on each Xl program given, every result-count read (every function id, one past the last and one
far past it), every function's tail results, both placements and the whole of `run` must agree
with the first forms, `run` with them written out here (`runList`, the definition before
2026-11-13). `tests-own-owned` passes every corpus root's program on both routes (the immortal
route and the plain-RC route under the canonical map, each allocated as the producer does), then
`synthetic`'s: the backend suite's hand-written programs and generated programs of many
functions that call and tail-call one another. -/

set_option autoImplicit false

namespace IxCCTests.Xv.StackingLinear

open IxCC IxCC.Xv IxCC.Xv.Stacking
open IxCC.Lir (FunId)

/-- `Stacking.run` with the first forms: the definition before 2026-11-13, written out. -/
def runList (p : LProgram) (layouts : List FrameLayout) (reps : FunId → Option (List ArgRep) := fun _ => none)
    (env : Xl.Env := {}) : Except Error Stacked := do
  let funcs := p.funcs.toList.zipIdx
  unless layouts.length == funcs.length do throw (.layouts funcs.length layouts.length)
  let checkedFns := withLayouts p layouts
  let extraList (f : Func Loc) (fn : FunId) (l : FrameLayout) (a : Facts) : List X86.GPR :=
    (mayChange env f a l ++ tailResultsList p f).filter (!(allowedChanges env fn f).contains ·) ++
      (env.clobbers fn).filter (fun r => !X86.SysV.callerSaved.toList.contains r)
  let aritiesList (f : Func Loc) : Bool :=
    f.blocks.toList.all fun b =>
      b.body.toList.all (fun | .call g _ rets => resultsOfList p g == some rets.length | _ => true) &&
        match b.term with
        | .ret vs => vs.length == f.results
        | .tail g _ => resultsOfList p g == some f.results
        | _ => true
  match checkedFns.find? (fun (_, _, l, a) => !l.check a) with
  | some (_, fn, _, _) => throw (.layout fn)
  | none => pure ()
  match checkedFns.find? (fun (f, fn, l, a) => !(extraList f fn l a).isEmpty) with
  | some (f, fn, l, a) => throw (.clobbers fn (extraList f fn l a))
  | none => pure ()
  match checkedFns.find? (fun (f, _, _, _) => !aritiesList f) with
  | some (_, fn, _, _) => throw (.arity fn)
  | none => pure ()
  let exports := exportsOf reps checkedFns
  let (wrappers, next) := placeExportsList exports
  let (placed, total) := placeFuncsList checkedFns next
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

structure Tally where
  programs : Nat := 0
  functions : Nat := 0
  /-- result-count reads compared, and those that find no function -/
  reads : Nat := 0
  readsNone : Nat := 0
  callSites : Nat := 0
  tailCalls : Nat := 0
  /-- runs that stack, and runs both forms refuse (with the same error) -/
  stacked : Nat := 0
  refused : Nat := 0
  failures : List String := []

def Tally.fail (t : Tally) (msg : String) : Tally := { t with failures := t.failures ++ [msg] }

def wrapperKey (w : PlacedExport) : FunId × String × Nat × Nat := (w.fn, w.symbol, w.reps.length, w.start)

def placedKey (pl : Placed) : FunId × Nat × Nat × Nat := (pl.fn, pl.start, pl.func.blocks.size, pl.func.params.length)

def sameStacked (a b : Except Error Stacked) : Bool :=
  match a, b with
  | .ok x, .ok y => x.program == y.program && x.shape == y.shape && x.exports == y.exports
  | .error e, .error e' => e == e'
  | _, _ => false

/-- Compare the forms on one program with its frame layouts. -/
def checkProgram (t : Tally) (label : String) (p : LProgram) (layouts : List FrameLayout)
    (reps : FunId → Option (List ArgRep)) (env : Xl.Env) : Tally := Id.run do
  let mut t := { t with programs := t.programs + 1, functions := t.functions + p.funcs.size }
  let n := p.funcs.size
  for g in List.range (n + 1) ++ [n + 1000] do
    t := { t with reads := t.reads + 1, readsNone := t.readsNone + (if (resultsOf p g).isNone then 1 else 0) }
    unless resultsOf p g == resultsOfList p g do t := t.fail s!"{label}: resultsOf {g}"
  for (f, fi) in p.funcs.toList.zipIdx do
    let (c, tc) := f.blocks.toList.foldl (fun (c, tc) b =>
      (c + (b.body.toList.filter fun | .call .. => true | _ => false).length,
       tc + match b.term with | .tail .. => 1 | _ => 0)) (0, 0)
    t := { t with callSites := t.callSites + c, tailCalls := t.tailCalls + tc }
    unless tailResults p f == tailResultsList p f do t := t.fail s!"{label}: tailResults of {fi}"
  let fns := withLayouts p layouts
  let exports := exportsOf reps fns
  let (w, n1) := placeExports exports
  let (w', n1') := placeExportsList exports
  unless w.map wrapperKey == w'.map wrapperKey && n1 == n1' do t := t.fail s!"{label}: placeExports"
  for start in [n1, 0, 2 ^ 32 - 3] do
    let (pl, m) := placeFuncs fns start
    let (pl', m') := placeFuncsList fns start
    unless pl.map placedKey == pl'.map placedKey && m == m' do t := t.fail s!"{label}: placeFuncs from {start}"
  let r := Stacking.run p layouts reps env
  unless sameStacked r (runList p layouts reps env) do t := t.fail s!"{label}: run"
  match r with
  | .ok _ => t := { t with stacked := t.stacked + 1 }
  | .error _ => t := { t with refused := t.refused + 1 }
  return t

/-- A program's Xl on the immortal route and on the plain-RC route under `bodies`, each allocated
as the producer allocates it, with the layouts the producer gives, its export passing and its
clobber sets. -/
def routes (names : List String) (env : Xl.Env) (F : Fir.Program) (bodies : Src.NatMap Own.Plain.Code) :
    Except String (List (String × LProgram × (FunId → Option (List ArgRep)) × Xl.Env)) := do
  let lowered ← (Rt.lower { names } (Cfg.lower (Own.immortal F))).mapError fun e => s!"Rt.lower: {e}"
  let (xv, _) ← (Select.run lowered.program).mapError fun e => s!"select: {e.form}: {e.reason}"
  let zero ← Alloc.runProducer env xv
  let some cand := Cfg.Rc.generate F bodies | return [("immortal", zero.program, lowered.reps, env)]
  let pub ← Cfg.Rc.Public.lower { names } F bodies cand
  let layout : Cfg.Rc.Native.Layout := ⟨cand.base.size, cand.base.ctors.filter (fun c => c.arity > 0)⟩
  let rcEnv := layout.env env
  let (pxv, _) ← (Select.run pub.runtime.program).mapError fun e => s!"select: {e.form}: {e.reason}"
  let plain ← Alloc.runProducer rcEnv pxv
  return [("immortal", zero.program, lowered.reps, env),
          ("plain-RC", plain.program, (⟨pub.runtime, pub.drop⟩ : Cfg.Rc.Public.Lowered).reps, rcEnv)]

/-- Both routes of one corpus root. -/
def checkRoot (t : Tally) (label : String) (names : List String) (env : Xl.Env) (F : Fir.Program)
    (bodies : Src.NatMap Own.Plain.Code) : Tally :=
  match routes names env F bodies with
  | .error e => t.fail s!"{label}: lowering: {e}"
  | .ok rs => rs.foldl (fun t (route, p, reps, env) =>
      checkProgram t s!"{label} ({route})" p (Stacking.produce p) reps env) t

/-! ## Synthetic programs -/

/-- `n` functions; function `i` calls `i + 1` and `(i * 7) % n` (when they exist) and returns one
value, or tail-calls `i + 1` when `i` is odd; every third function is exported; function 0 is
`main`. Each call binds one result, so every arity check passes. -/
def chain (n : Nat) : LProgram :=
  let r := fun g => Loc.reg g
  let fn (i : Nat) : Func Loc :=
    let calls : List (Inst Loc) :=
      ([i + 1, (i * 7) % n].filter (· < n)).map fun g => .call g [r .rdi] [r .rax]
    let term : Term Loc := if i % 2 == 1 && i + 1 < n then .tail (i + 1) [r .rdi] else .ret [r .rax]
    { name := s!"f{i}", params := [r .rdi], results := 1
      blocks := #[{ body := (.move (r .rax) (r .rdi) :: calls).toArray, term }]
      conv := if i % 3 == 0 then .sysvExport s!"s_f{i}" else .internal }
  { main := 0, funcs := ((List.range n).map fn).toArray }

/-- `chain n` with function `n / 2`'s calls to a function id past the program (the arity check
refuses it in both forms). -/
def chainPast (n : Nat) : LProgram :=
  let p := chain n
  let k := n / 2
  { p with funcs := p.funcs.modify k fun f =>
      { f with blocks := f.blocks.map fun b => { b with body := b.body.push (.call (n + 5) [.reg .rdi] [.reg .rax]) } } }

def synthetic (t : Tally) : Tally := Id.run do
  let mut t := t
  let hand : List (String × LProgram) := open IxCCTests.Backend.Programs in
    [("leaf", leaf), ("slots", slots), ("bigFrame", bigFrame), ("calls", calls), ("stackArgs", stackArgs),
     ("countdown", countdown), ("deep", deep), ("loop", loop), ("twoExports", twoExports), ("heap", heap),
     ("fused", fused)]
  for (name, p) in hand do
    t := checkProgram t s!"hand-written {name}" p (Stacking.produce p) (fun _ => none) {}
  for n in [1, 2, 3, 5, 17, 64, 257, 1000] do
    t := checkProgram t s!"chain {n}" (chain n) (Stacking.produce (chain n)) (fun _ => none) {}
    t := checkProgram t s!"chain {n} past" (chainPast n) (Stacking.produce (chainPast n)) (fun _ => none) {}
  return t

def report (t : Tally) : List String × List String :=
  ([s!"stacking forms: {t.programs} programs, {t.functions} functions, {t.reads} result-count reads \
      ({t.readsNone} finding none), {t.callSites} call sites, {t.tailCalls} tail calls; run stacked \
      {t.stacked}, refused {t.refused}; {t.failures.length} failures"], t.failures)

end IxCCTests.Xv.StackingLinear
