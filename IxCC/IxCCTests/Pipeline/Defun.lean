import IxCCTests.Pipeline.Support
import IxCCTests.Anf.Support
import IxCC.Anf.Defun
import IxCC.Recheck.RootArity
import IxCC.CompileClaim
import IxCCTests.Pipeline.Twin
import IxCCTests.Corpus.Manifest
import IxCCTests.Pipeline.Compiler

/-! The closures step end to end, under chosen middle-end schedules
(`tests-pipeline --only defun`).

The production compiler runs the closures step (`Recheck.closuresOf`: the
roots' entries at their declared counts and P8) after the middle end. This
part runs the compiler's own stages under a middle-end schedule it chooses:
the producer's front end (table, relevance, admission, erasure), the schedule,
the closures step, then `Fir.lower`, the immortal Own and Cfg, the root
checks (each root's compiled arity is its declared parameter count, which
the entries make true, `Recheck.checkRootArities`, and the entry wrapper's
parameter limit), the
switch check, `Rt.lower`, selection, the producer's allocation, stacking
and layout, and `Backend.finish`; the object runs natively as a test
executable (with `--native`). On `Decline.composeClosure`, two schedules:
the Phase 1 middle end (`Anf.Pipeline.produce`), and P1 and P2 alone, so that
P8 meets every closure specialisation would otherwise remove (the closures
design's "P4 disabled"); the expected values are the Lean interpreter's
(`lean --run` on `fixtures/corpus/phase2-closures/src/Closures.lean`, whose
`composeClosure` is `Decline.composeClosure` word for word). On the five K1
roots without equations (the fallback route: recursors at run time leave
closures), the Phase 1 middle end; the expected values are the Lean-compiled
twin's. On each input the Anf before and after the step give the expected
value, and natively the object does.

The other workloads of the closures design (dictionary-passing polymorphic
recursion, a `StateT`-over-`Except` loop, partial and over-application
through a stored closure, a fuel-indexed record of closures) and a copy of
`composeClosure` are the roots of `fixtures/corpus/phase2-closures` (frozen
with the ix of this repository, a registered family since the closures step
runs in production): each under both schedules, against the manifest's
interpreter values, and each but `Closures.stateLoop` certified under the
production schedule and with specialisation and inlining disabled, a compile
claim verified both ways (exit criterion 2, `certifiedBoth`);
`Closures.stateLoop` must be refused by register allocation
(`alloc.fallback`): a dispatcher tail-calls `StateT.bind`, of eight
parameters, and an internal tail call passes at most seven arguments.
`Closures.stateLoopSE` is the same loop within that limit.

`Decline.applyArg`, a root with a function parameter, at each surface
(`applyArgSurfaces`): `ixcc compile` writes the object; `--exe` and every
compile claim refuse it.

The roots of `fixtures/corpus/phase2-arity` (unregistered) have stored values
with fewer or more leading λs than their declared types show. Without an
entry, P8 would compile a point-free root at its stored arity, and a
field-less closure cell would read back natively as a number or a Boolean on
a well-typed input. The closures step gives each such root an entry at its
declared count (`expectEntry`), and they agree with Lean, as does a `csimp`
table entry that gives a root arity 0; a root whose result type is a
definition of a function type returns a closure through its entry, with no
readback type; the roots whose counts agree, and a point-free root given an
η-long equation, compile unchanged and agree with Lean. -/

namespace IxCCTests.Pipeline.Defun

open IxCC IxCC.Recheck IxCCTests.Src
open System

/-- The producer's front end: the table, the annotation, admission and
erasure (`Recheck.produceWith`'s first half). -/
def front (cfg : Config) (inp : Input) : Except Err (Src.Program × Lam.Program) := do
  let P := inp.program
  let (table, _, _) := Src.Table.build cfg.table P inp.hints.proposals
  let p0 := { P with table }
  (Src.Table.validate cfg.table p0).mapError fun m => { stage := .table, code := "table.entry", message := m }
  let ann ← (Src.Relevance.annotate inp.env p0).mapError fun m =>
    { stage := .relevance, code := "relevance-oracle", message := m }
  let (src, checked) ← match Src.Recheck.annotation p0 ann with
    | .ok r => pure r
    | .error (.install m) => throw { stage := .relevance, code := "relevance-S1", message := m }
    | .error (.relevance errs) =>
      throw { stage := .relevance, code := s!"relevance-{(errs[0]?.map (·.rule)).getD "S1"}"
              message := "; ".intercalate (errs.toList.take 8 |>.map (·.render p0)) }
    | .error (.table m) => throw { stage := .table, code := "table.entry", message := m }
  match Src.admit src (sidecarName inp.hints) cfg.admit with
  | .ok _ => pure ()
  | .error diags =>
    let d := diags[0]?.getD (Src.Diag.of "admit" "rejected")
    throw (Err.ofDiag .admit d)
  let (lam, _) ← (IxCC.Lam.erase src checked).mapError Err.ofErase
  pure (src, lam)

/-- What the compiler made: the schedule's program, the closures step's, the
roots and the object. -/
structure Made where
  before : Anf.Program
  after : Anf.Program
  roots : List Root
  object : ByteArray

/-- The compiler with the closures step after the middle-end schedule `mid`. -/
def compile (cfg : Config) (inp : Input) (mid : Lam.Program → Except String Anf.Program) :
    Except Err Made := do
  let cfg := cfg.forInput inp
  let (src, lam) ← front cfg inp
  let before ← (mid lam).mapError fun m => { stage := .anf, code := "anf.produce", message := m }
  let after ← closuresOf src before
  let fir ← (IxCC.Fir.lower after).mapError Err.ofFir
  let C := IxCC.Cfg.lower (IxCC.Own.immortal fir)
  checkRootArities cfg src C
  checkParams cfg C (C.exports.zipIdx.map fun (f, i) => (i, f))
  (IxCC.Rt.checkSwitches C).mapError Err.ofSwitch
  let lowered ← (IxCC.Rt.lower { names := cfg.names } C).mapError Err.ofRt
  let (xv, _) ← (Xv.Select.run lowered.program).mapError Err.ofSelect
  let r ← (Xv.Alloc.run cfg.env xv).mapError fun m => { stage := .alloc, code := "alloc.fallback", message := m }
  let layouts := Xv.Stacking.produce r.program
  let stacked ← (Xv.Stacking.run r.program layouts lowered.reps cfg.env).mapError (Err.ofBackend ∘ .stacking)
  let order := X86.Layout.Order.produce (X86.Layout.tunnel stacked.program) stacked.shape
  let c : Cert := { alloc := r.outs, frames := layouts, order }
  let root := (src.roots.head?.map (·.1)).getD default
  let (_, xl, stacked, program, exports) ← backTyped cfg lowered root c
  checkSymbols stacked.exports
  let backend ← (Backend.finish xl.main stacked program exports (cfg.provenance.getD (defaultProvenance root))).mapError
    Err.ofBackend
  let rows := (List.range src.roots.length).zip (src.roots.zip (C.exports.zip lowered.roots))
  pure { before, after, roots := rootsOf cfg src C lowered rows, object := backend.object }

/-- The Phase 1 middle end's schedule. -/
def midDefault (L : Lam.Program) : Except String Anf.Program := do
  let t ← Anf.Pipeline.produce {} L
  pure ((t.stages.getLast?.map (·.2)).getD default)

/-- P1 and P2 alone, then pruning: no inlining, no specialisation. -/
def midMinimal (L : Lam.Program) : Except String Anf.Program := do
  let P ← Anf.Pipeline.checkLamNodes L >>= Anf.convert
  let (_, P, _) ← Anf.Shrink.produce {} P
  pure (Anf.Prune.run P)

def declineIxe : FilePath := "fixtures/corpus/phase1-decline/closures.ixe"
def declineEqs : FilePath := "fixtures/corpus/phase1-decline/closures.equations.json"

/-- `Decline.composeClosure k n` on Lean's interpreter (`lean --run` on
`Closures.lean`, 2026-11-10): `n + 2^k`. -/
def composeCases : List (List Nat × Nat) :=
  [([0, 5], 6), ([1, 5], 7), ([4, 3], 19), ([10, 0], 1024), ([12, 7], 4103), ([16, 1], 65537)]

/-- The Anf before and after P8 agree with the expected values on the inputs
whose first argument is at most `small` (the Anf evaluators are slow on the
larger ones). -/
def anfAgree (a : Assert) (m : Made) (label : String) (cases : List (List Nat × Nat)) (small : Nat) :
    IO Unit := do
  let some r := m.before.roots.head? | expect a false s!"{label}: no root"
  -- the step may point the root at its entry
  let some r' := m.after.roots.head? | expect a false s!"{label}: no root after the step"
  for (args, want) in cases.filter (fun (xs, _) => xs.headD 0 ≤ small) do
    let rb ← IxCCTests.Anf.runAnf m.before 100000 r args
    let ra ← IxCCTests.Anf.runAnf m.after 800000 r' args
    expect a (IxCCTests.Anf.anfOutcome rb == s!"ok lit {want}")
      s!"{label} {args}: the Anf before P8 gives {IxCCTests.Anf.anfOutcome rb}, Lean {want}"
    expect a (IxCCTests.Anf.anfOutcome ra == s!"ok lit {want}")
      s!"{label} {args}: the Anf after P8 gives {IxCCTests.Anf.anfOutcome ra}, Lean {want}"

/-- One input and schedule: P8's output is first order, the Anf before and
after P8 give Lean's values, and natively the object does. With `closures`,
the middle end must have left closures (so that P8 is exercised); otherwise
the line says whether it did. -/
def one (a : Assert) (native : Option IxCCTests.Rt.Native.Tools) (label : String) (inp : Input)
    (mid : Lam.Program → Except String Anf.Program) (cases : List (List Nat × Nat)) (small : Nat)
    (closures : Bool := true) : IO String := do
  let m ← ofErr label fun _ => compile {} inp mid
  expect a (IxCC.Anf.firstOrder m.after) s!"{label}: the output is not first order"
  let residual := IxCC.Anf.Pipeline.residual m.before
  let left := !residual.fns.isEmpty || !residual.apps.isEmpty || !residual.globs.isEmpty
  if closures then expect a left s!"{label}: the middle end left no closure, so P8 is not exercised"
  anfAgree a m label cases small
  let lifted := (m.after.globalList.filter fun (_, g) => g.key matches .lam ..).length
  let disps := (m.after.globalList.filter fun (_, g) => g.key matches .dispatch _).length
  let mut line := if left then
      s!"{label}: {m.before.size} globals before P8, {lifted} lifted λs, {disps} dispatchers, \
        {m.after.ctors.length - m.before.ctors.length} closure keys; object {m.object.size} bytes"
    else s!"{label}: the middle end left no closure ({m.before.size} globals); object {m.object.size} bytes"
  if let some nt := native then
    let some root := m.roots.head? | do expect a false s!"{label}: no root"; return line
    let exe ← link nt s!"defun_{label}" m.object root.symbol
    let lines ← IxCCTests.Rt.Native.run exe { stack := 1 <<< 28, ty := root.ty } (cases.map (·.1))
    for ((args, want), l) in cases.zip lines do
      expect a (l.status == 0 && l.ok) s!"{label} {args}: status {l.status}, registers restored {l.ok}"
      expect a (l.obs == some (toString want)) s!"{label} {args}: native {l.obs}, Lean {want}"
    line := line ++ s!"; natively, {cases.length} cases equal Lean's"
  return line

/-- One input whose result the Anf evaluators do not print as a number (a
`Bool`): compiled, first order after the step, and natively the object reads
back what the interpreter printed (`Corpus.Case.sourceObs`). -/
def oneObs (a : Assert) (native : Option IxCCTests.Rt.Native.Tools) (label : String) (inp : Input)
    (mid : Lam.Program → Except String Anf.Program) (cases : List (List Nat × String)) : IO String := do
  let m ← ofErr label fun _ => compile {} inp mid
  expect a (IxCC.Anf.firstOrder m.after) s!"{label}: the output is not first order"
  let mut line := s!"{label}: compiled; object {m.object.size} bytes"
  if let some nt := native then
    let some root := m.roots.head? | do expect a false s!"{label}: no root"; return line
    let exe ← link nt s!"defun_{label}" m.object root.symbol
    let lines ← IxCCTests.Rt.Native.run exe { stack := 1 <<< 28, ty := root.ty } (cases.map (·.1))
    expect a (lines.length == cases.length) s!"{label}: {lines.length} result lines"
    for ((args, want), l) in cases.zip lines do
      expect a (l.status == 0 && l.ok) s!"{label} {args}: status {l.status}, registers restored {l.ok}"
      expect a (l.obs == some want) s!"{label} {args}: native {l.obs}, Lean {want}"
    line := line ++ s!"; natively, {cases.length} cases equal Lean's"
  return line

/-- The fallback route: `k1.ixe` with a sidecar without equations, so the
roots run their recursors and the middle end leaves closures (the production
compiler declines them, `tests-pipeline`'s declines part). Inputs small
enough for the immortal heap; expected values from the Lean-compiled twin
(`IxCCTests.Fixtures.K1`). -/
def fallbackInputs : List (String × List (List Nat)) :=
  [("K1.fib", [[0], [1], [10], [15]]), ("K1.sumLoop", [[0], [5], [100]]),
   ("K1.ack", [[1, 2], [2, 3]]), ("K1.tak", [[4, 3, 2, 1], [6, 6, 4, 2]]),
   ("K1.gcd", [[12, 18], [100, 75], [0, 5]])]

def closuresDir : FilePath := "fixtures/corpus/phase2-closures"

/-- The workloads a later stage refuses, by root, with the refusal's stage
and code: register allocation's limit on tail calls (`alloc.fallback`: a
dispatcher tail-calls a source function of eight parameters, `StateT.bind`,
and an internal tail call passes at most seven arguments). -/
def refusedLater : List (String × String) := [("Closures.stateLoop", "alloc.fallback")]

/-- The producer's budgets with specialisation disabled (the closures
design's "P4 disabled"), and inlining with it: P4 makes no decision and P3 no
round, so the certificate's middle end is P1, P2, pruning and empty P4 steps
(the certified form of the `p1p2` schedule), and every closure the Phase 1
middle end would remove reaches the closures step. -/
def noSpec : Config := { budgets := { spec := { maxSpecs := 0 }, inline := { rounds := 0 } } }

def policyName : CompilePolicy → String
  | .immortal => "immortal"
  | .zeroRc => "zero-RC"
  | .plainRc => "plain-RC"

/-- Exit criterion 2 of the closures design for one workload: under the
production schedule and with specialisation disabled, the production compiler
certifies the root (`Recheck.compileInput`: the producer's certificate,
re-checked by `Recheck.run`), a compile claim (`CompileClaim.produce`) is
accepted by `verifyProgram` and `verifyBytes`, and natively both objects
give Lean's value on every case, so the two agree. With specialisation and
inlining disabled (`noSpec`) the closures step changes the program. -/
def certifiedBoth (a : Assert) (native : Option IxCCTests.Rt.Native.Tools) (root label : String)
    (inp : Input) (bytes : ByteArray) (json : Lean.Json) (cases : List (List Nat × Nat)) : IO String := do
  let mut line := s!"{label}-certified:"
  for (sched, cfg0) in [("default", ({} : Config)), ("no-P3-P4", noSpec)] do
    -- the root by name, as `verifyBytes` selects it from the sidecar (`selectTargetRoots`)
    let cfg := { cfg0 with names := [root] }
    let l := s!"{label}-{sched}"
    let (cert, art) ← ofErr s!"{l}: compileInput" fun _ => compileInput cfg inp
    let pre := (IxCC.Anf.Pipeline.run cert.mid art.lam).toOption
    let changed := pre.any fun p => !p.beq art.anf
    if sched == "no-P3-P4" then
      expect a (cert.mid.steps.all fun s => match s with
          | .specialize c => c.decisions.isEmpty | .inline _ => false | _ => true)
        s!"{l}: a specialisation decision or an inline round with both disabled"
      expect a changed s!"{l}: the closures step left the program unchanged"
    let (claim, certText, _) ← ofErr s!"{l}: CompileClaim.produce" fun _ => CompileClaim.produce cfg inp
    expect a (CompileClaim.verifyProgram cfg inp.program claim certText) s!"{l}: verifyProgram refuses the claim"
    expect a (CompileClaim.verifyBytes cfg bytes json claim certText) s!"{l}: verifyBytes refuses the claim"
    line := line ++ s!" {sched}: certified, {if changed then "P8 ran" else "first order before P8"}, \
      claim ({policyName claim.policy}) verified;"
    if let some nt := native then
      let some root := art.roots.head? | do expect a false s!"{l}: no root"; return line
      let exe ← link nt s!"defun_{l}_certified" art.object root.symbol
      let lines ← IxCCTests.Rt.Native.run exe { stack := 1 <<< 28, ty := root.ty } (cases.map (·.1))
      expect a (lines.length == cases.length) s!"{l}: {lines.length} result lines"
      for ((args, want), r) in cases.zip lines do
        expect a (r.status == 0 && r.ok) s!"{l} {args}: status {r.status}"
        expect a (r.obs == some (toString want)) s!"{l} {args}: native {r.obs}, Lean {want}"
  if native.isSome then line := line ++ s!" natively both give Lean's {cases.length} values"
  return line

/-- The closures design's workloads (`fixtures/corpus/phase2-closures`):
every root under both schedules, against the manifest's interpreter values,
and certified with and without specialisation (`certifiedBoth`); a root of
`refusedLater` must be refused by that stage, after P8, with the globals over
seven parameters all the program's own (none of P8's lifted functions or
dispatchers). -/
def workloads (a : Assert) (native : Option IxCCTests.Rt.Native.Tools) : IO (Array String) := do
  let fam ← IxCCTests.Corpus.Family.read (closuresDir / "corpus.json")
  let some fx := fam.fixtures.head? | do expect a false "phase2-closures: no fixture"; return #[]
  let bytes ← IO.FS.readBinFile (closuresDir / fx.closure.path)
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (closuresDir / fx.equations.path)))
  let mut out := #[]
  for r in fx.roots do
    let cases := r.cases.map fun c => (c.args, c.value.toNat!)
    let inp ← ingressFile (closuresDir / fx.closure.path) (closuresDir / fx.equations.path) [r.name]
    if refusedLater.lookup r.name |>.isNone then
      out := out.push (← certifiedBoth a native r.name (r.name.replace "." "_") inp bytes json cases)
    for (sched, mid) in [("phase1", midDefault), ("p1p2", midMinimal)] do
      let label := s!"{r.name.replace "." "_"}-{sched}"
      let res ← IO.lazyPure fun _ => compile {} inp mid
      match res, refusedLater.lookup r.name with
      | .error e, some code =>
        expect a (e.code == code) s!"{label}: refused with {e.render}, expected {code}"
        -- the program's functions of more than seven parameters (a dispatcher tail-calls them)
        let wide : List (Anf.GlobalId × Key.GKey × Nat) := match front (({} : Config).forInput inp) inp with
          | .ok (src, lam) =>
            match (mid lam).toOption.bind fun pre => (closuresOf src pre).toOption with
            | some q => q.globalList.filterMap fun ((g : Anf.GlobalId), (gd : Anf.GDef)) =>
                if gd.ps.length > 7 then some (g, gd.key, gd.ps.length) else none
            | none => []
          | .error _ => []
        expect a (!wide.isEmpty && wide.all fun (_, k, _) => !(Anf.Defun.reservedKey k))
          s!"{label}: the globals over seven parameters are not the program's own"
        out := out.push s!"{label}: refused after P8, as expected: {e.render}; globals over seven \
          parameters: {wide.map fun (g, k, n) => s!"{g} ({k.render}, {n})"}"
      | .error e, none => expect a false s!"{label}: refused: {e.render}"
      | .ok _, some code => expect a false s!"{label}: compiled, expected a refusal with {code}"
      | .ok _, none => out := out.push (← one a native label inp mid cases 10 (closures := false))
  return out

def arityDir : FilePath := "fixtures/corpus/phase2-arity"

/-- The roots of `fixtures/corpus/phase2-arity` whose Anf arity is not their
declared parameter count: the root, its Anf arity (the leading λs of the body
the table gives it) and its declared count. The closures step gives each an
entry at the declared count. `Arity.main7`'s result type is a definition of a
function type, so its declared count is below its arity and its entry returns
a closure; `Arity.spin` builds no closure (it compiled at its own arity before
the closures step) and runs forever. -/
def arityEntered : List (String × Nat × Nat) :=
  [("Arity.main3", 1, 2), ("Arity.main4", 0, 2), ("Arity.addTo", 1, 2), ("Arity.halve", 1, 2),
   ("Arity.main7", 2, 1), ("Arity.main8p", 1, 3), ("Arity.main9", 0, 2), ("Arity.main9r", 0, 2),
   ("Arity.main10", 0, 1), ("Arity.main11", 1, 2), ("Arity.main12", 1, 2), ("Arity.mainB3", 1, 2),
   ("Arity.mainB4", 0, 2), ("Arity.spin", 1, 2)]

/-- A root given an entry: compiled, the root's Anf arity `m` before the step and
its entry's `n` parameters after it, the entry keyed `GKey.entry`, and the
exported function taking `n` parameters. -/
def expectEntry (a : Assert) (label : String) (m n : Nat) (res : Except Err Made) : IO (Option Made) :=
  match res with
  | .error e => do
    expect a false s!"{label}: refused with {e.render}, expected an entry at {n} parameters"
    return none
  | .ok made => do
    let before := made.before.roots.head?.bind made.before.arity?
    let after := made.after.roots.head?.bind made.after.global?
    expect a (before == some m) s!"{label}: the root takes {before} parameters before the step, expected {m}"
    expect a (after.any fun gd => gd.ps.length == n && gd.key matches .entry _ _)
      s!"{label}: the root after the step is not an entry of {n} parameters"
    expect a (made.roots.head?.any (·.params == n)) s!"{label}: the export does not take {n} parameters"
    return some made

/-- An input whose table proposals include `ps` (what a certificate's table
may choose). -/
def withProposals (inp : Input) (ps : List Src.Proposal) : Input :=
  { inp with hints := { inp.hints with proposals := inp.hints.proposals ++ ps.toArray } }

/-- A sidecar root's address by name. -/
def sidecarAddr (h : Src.Hints) (n : String) : IO Ixon.Address :=
  match h.roots.find? (·.2 == some n) with
  | some (addr, _) => pure addr
  | none => throw (IO.userError s!"phase2-arity: no sidecar root {n}")

/-- The roots of `fixtures/corpus/phase2-arity` under the Phase 1 schedule:
those of `arityEntered` compiled through an entry at their declared count
(`expectEntry`) and agreeing with Lean, except `Arity.main7` (its entry
returns a closure: one parameter, no readback type) and `Arity.spin` (two
parameters, no case: it runs forever); `Arity.main7b` (declared and
compiled count 1, its result a closure) compiled with no readback type; the
others compiled unchanged and agreeing with Lean. Then two table entries: an
η-long equation for `Arity.main4` (it compiles at its declared count with no
entry) and a `csimp` entry for `Arity.slowDouble` (arity 0 against 1: an
entry, agreeing with Lean). -/
def arity (a : Assert) (native : Option IxCCTests.Rt.Native.Tools) : IO (Array String) := do
  let fam ← IxCCTests.Corpus.Family.read (arityDir / "corpus.json")
  let some fx := fam.fixtures.head? | do expect a false "phase2-arity: no fixture"; return #[]
  let ixe := arityDir / fx.closure.path
  let eqs := arityDir / fx.equations.path
  let mut out := #[]
  let mut entered : List String := []
  for r in fx.roots do
    let inp ← ingressFile ixe eqs [r.name]
    let label := s!"{r.name.replace "." "_"}-phase1"
    let res ← IO.lazyPure fun _ => compile {} inp midDefault
    match arityEntered.find? (·.1 == r.name) with
    | some (_, m, n) =>
      let some made ← expectEntry a label m n res | pure ()
      entered := entered ++ [s!"{r.name} ({m}/{n})"]
      if r.name == "Arity.main7" then
        expect a (made.roots.head?.any (·.ty.isNone)) s!"{label}: expected no readback type"
        out := out.push s!"{label}: an entry of one parameter returning a closure, with no readback type"
      else if r.name == "Arity.spin" then
        out := out.push s!"{label}: an entry of two parameters (it runs forever; no case)"
      else if r.result == "bool" then
        let cases := r.cases.filterMap fun c => (c.sourceObs r).map (c.args, ·)
        out := out.push (← oneObs a native label inp midDefault cases)
      else
        let cases := r.cases.map fun c => (c.args, c.value.toNat!)
        out := out.push (← one a native label inp midDefault cases 10 (closures := false))
    | none =>
      match res with
      | .error e => expect a false s!"{label}: refused: {e.render}"
      | .ok made =>
        if r.name == "Arity.main7b" then
          expect a (made.roots.head?.any fun root => root.params == 1 && root.ty.isNone)
            s!"{label}: expected one parameter and no readback type"
          out := out.push s!"{label}: compiled at its declared count 1, with no readback type"
        else
          let cases := r.cases.map fun c => (c.args, c.value.toNat!)
          out := out.push (← one a native label inp midDefault cases 10 (closures := false))
  out := out.push s!"phase2-arity: given an entry (Anf/declared): {", ".intercalate entered}"
  let h ← IO.ofExcept (Src.Hints.ofK1Json (← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))))
  let main4 ← ingressFile ixe eqs ["Arity.main4"]
  let eta : Src.Proposal := { kind := .eqn, subject := ← sidecarAddr h "Arity.main4"
                              theorem? := some (← sidecarAddr h "Arity.main4_eta"), name? := some "Arity.main4" }
  out := out.push (← one a native "main4_eta-phase1" (withProposals main4 [eta]) midDefault
    [([3, 4], 34), ([12, 5], 125)] 10 (closures := false))
  let sd ← ingressFile ixe eqs ["Arity.slowDouble"]
  let cs : Src.Proposal := { kind := .csimp, subject := ← sidecarAddr h "Arity.slowDouble"
                             target? := some (← sidecarAddr h "Arity.fastDouble")
                             theorem? := some (← sidecarAddr h "Arity.slowDouble_eq"), name? := some "Arity.slowDouble" }
  let sdc := withProposals sd [cs]
  let _ ← expectEntry a "slowDouble_csimp-phase1" 0 1 (← IO.lazyPure fun _ => compile {} sdc midDefault)
  out := out.push (← one a native "slowDouble_csimp-phase1" sdc midDefault [([5], 10), ([0], 0)] 10
    (closures := false))
  return out

/-- `Decline.composeClosure` through the production compiler: certified
(`Recheck.compileInput`: the producer's certificate, which `Recheck.run`
re-checks, the closures step running on both), the closures step changing the
program (a dispatcher and closure keys), natively Lean's values, and a
compile claim (`CompileClaim.produce`) that `verifyProgram` and `verifyBytes`
accept, with the closure typed. -/
def certified (a : Assert) (native : Option IxCCTests.Rt.Native.Tools) : IO String := do
  let inp ← ingressFile declineIxe declineEqs ["Decline.composeClosure"]
  let (cert, art) ← ofErr "composeClosure: compileInput" fun _ => compileInput {} inp
  expect a (IxCC.Anf.firstOrder art.anf) "composeClosure: the program Fir lowers is not first order"
  let pre := (IxCC.Anf.Pipeline.run cert.mid art.lam).toOption
  expect a (pre.any fun p => !p.beq art.anf) "composeClosure: the closures step left the program unchanged"
  let disps := (art.anf.globalList.filter fun (_, g) => g.key matches .dispatch _).length
  expect a (disps > 0) "composeClosure: no dispatcher"
  let mut line := s!"composeClosure-certified: compileInput accepts; {disps} dispatchers; \
    object {art.object.size} bytes"
  if let some nt := native then
    let some root := art.roots.head? | do expect a false "composeClosure: no root"; return line
    let exe ← link nt "defun_composeClosure_certified" art.object root.symbol
    let lines ← IxCCTests.Rt.Native.run exe { stack := 1 <<< 28, ty := root.ty } (composeCases.map (·.1))
    for ((args, want), l) in composeCases.zip lines do
      expect a (l.status == 0 && l.ok) s!"composeClosure-certified {args}: status {l.status}"
      expect a (l.obs == some (toString want)) s!"composeClosure-certified {args}: native {l.obs}, Lean {want}"
    line := line ++ s!"; natively, {composeCases.length} cases equal Lean's"
  -- no names: `verifyBytes` then selects the sidecar root by the claim's target
  let cfg : Config := {}
  let (claim, certText, _) ← ofErr "composeClosure: CompileClaim.produce" fun _ => CompileClaim.produce cfg inp
  expect a (claim.abiArity == 2) s!"composeClosure: the claim's arity is {claim.abiArity}"
  expect a (CompileClaim.verifyProgram cfg inp.program claim certText)
    "composeClosure: verifyProgram refuses the claim"
  let bytes ← IO.FS.readBinFile declineIxe
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile declineEqs))
  expect a (CompileClaim.verifyBytes cfg bytes json claim certText)
    "composeClosure: verifyBytes refuses the claim"
  return line ++ "; its compile claim (arity 2) verifies on the program and on the bytes"

/-- The closures step is not in the certificate: no certificate codec names a
global key, and for a root given an entry (`Arity.main3`, Anf arity 1,
declared 2) through the production compiler the certificate's middle end is
the schedule's own certificate (`Anf.Pipeline.produce`), the certificate
parses back to itself, and `Recheck.run` on the parsed certificate makes the
same object, whose Anf program has the entry. -/
def entryNotInCert (a : Assert) : IO String := do
  let fam ← IxCCTests.Corpus.Family.read (arityDir / "corpus.json")
  let some fx := fam.fixtures.head? | do expect a false "phase2-arity: no fixture"; return ""
  let inp ← ingressFile (arityDir / fx.closure.path) (arityDir / fx.equations.path) ["Arity.main3"]
  let cfg := ({} : Config).forInput inp
  let (cert, art) ← ofErr "main3: compileInput" fun _ => compileInput {} inp
  expect a ((art.anf.global? (art.anf.roots.headD 0)).any fun g => g.key matches .entry _ 2)
    "main3: the compiled root is not an entry of two parameters"
  let t ← ofErr "main3: Anf.Pipeline.produce" fun _ =>
    (IxCC.Anf.Pipeline.produce cfg.budgets art.lam).mapError fun m => ({ stage := .anf, code := "anf.produce", message := m } : Err)
  expect a ((CertJson.mid t.cert).compress == (CertJson.mid cert.mid).compress)
    "main3: the certificate's middle end is not the schedule's"
  let text := cert.toText
  let c' ← ofErr "main3: Cert.ofText" fun _ => Cert.ofText text
  expect a (c'.toText == text) "main3: the certificate does not round-trip"
  let art' ← ofErr "main3: run" fun _ => run cfg inp.program c'
  expect a (art'.object == art.object) "main3: the parsed certificate makes a different object"
  return s!"main3: compiled through an entry; the certificate ({text.utf8ByteSize} bytes) is the \
    schedule's middle end, round-trips and makes the same object"

/-- `Decline.applyArg` (a function parameter applied): compiled through the
closures step, which finds no closure source in the program (no local
function, no function global's value), so the one dispatcher it makes, of
arity 1, has no alternative and no default. Natively it traps: `Rt.lower`
closes a switch with no alternative and no default with a trap. Every input
the driver passes is words, never a closure, and on such an input the source
is stuck as well (it applies a number), so nothing is claimed of the run
(`Front.GoesWrong`); the trap is the target's choice where the source is
stuck (`Rt.lower_refines`). -/
def applyArg (a : Assert) (native : Option IxCCTests.Rt.Native.Tools) : IO String := do
  let inp ← ingressFile declineIxe declineEqs ["Decline.applyArg"]
  let m ← ofErr "applyArg" fun _ => compile {} inp midDefault
  let disps := m.after.globalList.filter fun (_, g) => g.key matches .dispatch _
  expect a (disps.length == 1) s!"applyArg: {disps.length} dispatchers, expected one"
  expect a (disps.all fun (_, g) => match g.body with | .case _ [] none => true | _ => false)
    "applyArg: the dispatcher has an alternative or a default"
  expect a (m.after.ctors.length == m.before.ctors.length) "applyArg: the step added closure keys"
  let mut line := s!"applyArg: compiled, one dispatcher with no alternative; object {m.object.size} bytes"
  if let some nt := native then
    let some root := m.roots.head? | do expect a false "applyArg: no root"; return line
    let exe ← link nt "defun_applyArg" m.object root.symbol
    let inputs : List (List Nat) := [[0, 5], [3, 4], [7, 0]]
    let lines ← IxCCTests.Rt.Native.run exe { stack := 1 <<< 28, ty := root.ty } inputs
    expect a (lines.length == inputs.length) s!"applyArg: {lines.length} result lines"
    for (args, l) in inputs.zip lines do
      expect a (l.status == 4) s!"applyArg {args}: status {l.status}, expected 4 (a trap)"
    line := line ++ s!"; natively, {inputs.length} inputs trap (status 4)"
  return line

/-- What a user sees for `Decline.applyArg`, a root with a parameter of
function type, at each surface. Closures do not cross a program boundary, so
no caller can pass a closure: such a root has no meaningful caller.
`ixcc compile` writes its object (exit 0; nothing refuses the root before run
time, where every input traps); `ixcc compile --exe` refuses it (`exe.params`,
exit 1, no executable); and every compile claim refuses it:
`CompileClaim.produce` with `cert: roots` under each RC mode, and
`verifyProgram` and `verifyBytes` reject a claim naming it at its arity with
the producer's own certificate and object (`rootParamsAllNat` is false), so no
claim covers it. -/
def applyArgSurfaces (a : Assert) (t : Compiler.Tools) : IO String := do
  let root := "Decline.applyArg"
  let inp ← ingressFile declineIxe declineEqs [root]
  let (cert, art) ← ofErr "applyArg: compileInput" fun _ => compileInput {} inp
  let some r := art.roots.head? | do expect a false "applyArg: no root"; return ""
  expect a (r.params == 2) s!"applyArg: {r.params} parameters, expected 2"
  expect a (!CompileClaim.rootParamsAllNat art.src r) "applyArg: rootParamsAllNat accepts a function parameter"
  -- the command line: the object, then the executable
  let obj := t.work / "defun_applyArg.o"
  let exe := t.work / "defun_applyArg.exe"
  let code ← Compiler.cli t ["compile", declineIxe.toString, "--equations", declineEqs.toString,
    "--root", root, "-o", obj.toString]
  expectEq a code 0 "applyArg: ixcc compile's exit code"
  expect a (← obj.pathExists) "applyArg: ixcc compile wrote no object"
  let code ← Compiler.cli t ["compile", declineIxe.toString, "--equations", declineEqs.toString,
    "--root", root, "--exe", exe.toString]
  expectEq a code 1 "applyArg: ixcc compile --exe's exit code"
  expect a (!(← exe.pathExists)) "applyArg: ixcc compile --exe wrote an executable"
  match IxCC.Exe.fragment art with
  | .error e => expect a (e.code == "exe.params") s!"applyArg: the executable refused with {e.render}, expected exe.params"
  | .ok _ => expect a false "applyArg: the executables' fragment accepts it"
  -- compile claims: the producer, under each RC mode
  for mode in [IxCC.Compiler.RcMode.auto, .immortal, .zeroRc, .plainRc] do
    match CompileClaim.produce {} inp mode with
    | .error (e : Err) =>
      let msg := s!"applyArg: CompileClaim.produce refused with {e.render}, expected cert: roots"
      expect a (e.stage == .cert && e.code == "roots") msg
    | .ok _ => expect a false "applyArg: CompileClaim.produce made a claim"
  -- and the verifiers, on a claim right in every field but the root's parameters
  let some (target, _) := inp.program.roots.head? | do expect a false "applyArg: no source root"; return ""
  let bytes ← IO.FS.readBinFile declineIxe
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile declineEqs))
  let claim : CompileClaim :=
    { env := inp.env.root, roleTable := inp.env.bindingAddress, target, policy := .immortal,
      abiArity := r.params, elfHash := Ixon.Address.blake3Pure art.object }
  let text := cert.toText
  expect a ((run (({} : Config).forInput inp) inp.program cert).toOption.any (·.object == art.object))
    "applyArg: the certificate does not replay to the object"
  expect a (!CompileClaim.verifyProgram {} inp.program claim text) "applyArg: verifyProgram accepts the claim"
  expect a (!CompileClaim.verifyBytes {} bytes json claim text) "applyArg: verifyBytes accepts the claim"
  return s!"applyArg: ixcc compile writes the object; --exe refuses it (exe.params); \
    CompileClaim.produce refuses it under each RC mode (cert: roots); verifyProgram and \
    verifyBytes refuse a claim naming it"

def run (a : Assert) (t : Compiler.Tools) : IO (Array String) := do
  let native := t.native
  let mut out := #[]
  out := out.push (← applyArg a native)
  out := out.push (← applyArgSurfaces a t)
  out := out.push (← certified a native)
  out := out.push (← entryNotInCert a)
  let compose ← ingressFile declineIxe declineEqs ["Decline.composeClosure"]
  out := out.push (← one a native "composeClosure-phase1" compose midDefault composeCases 10)
  out := out.push (← one a native "composeClosure-p1p2" compose midMinimal composeCases 10)
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile k1Eqs))
  let noEqs := json.setObjVal! "equations" (Lean.Json.arr #[])
  let bytes ← IO.FS.readBinFile k1Ixe
  for (root, inputs) in fallbackInputs do
    let inp ← ofErr root fun _ => ingress bytes noEqs [root] (typecheck := false)
    let cases := inputs.map fun xs => (xs, (Twin.twin root xs).getD 0)
    out := out.push (← one a native s!"fallback-{root.replace "." "_"}" inp midDefault cases 10)
  out := out ++ (← workloads a native)
  out := out ++ (← arity a native)
  return out

end IxCCTests.Pipeline.Defun
