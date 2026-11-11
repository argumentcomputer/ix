import IxCCTests.Pipeline.Support
import IxCCTests.Anf.Support
import IxCC.Anf.Defun
import IxCC.Recheck.RootArity
import IxCCTests.Pipeline.Twin
import IxCCTests.Corpus.Manifest

/-! P8 end to end, outside the production pipeline (`tests-pipeline --only defun`).

The production compiler declines a program whose closures survive the middle
end (`fir.closures`); `Recheck.run` does not run P8 yet. This part runs the
compiler's own stages with `Anf.defun` between the middle end and Fir: the
producer's front end (table, relevance, admission, erasure), a middle-end
schedule, `Anf.defun`, then `Fir.lower`, the immortal Own and Cfg, the root
checks (each root's compiled arity is its declared parameter count,
`Recheck.checkRootArities`, and the entry wrapper's parameter limit), the
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
twin's. On each input the Anf before and after P8 give the expected value,
and natively the object does.

The other workloads of the closures design (dictionary-passing polymorphic
recursion, a `StateT`-over-`Except` loop, partial and over-application
through a stored closure, a fuel-indexed record of closures) and a copy of
`composeClosure` are the roots of `fixtures/corpus/phase2-closures` (frozen
with the ix of this repository, not yet a registered family): each under both
schedules, against the manifest's interpreter values; `Closures.stateLoop` must
be refused by register allocation (`alloc.fallback`): a source global of eight
parameters exceeds its limit on parameter counts, which is independent of closures.

The roots of `fixtures/corpus/phase2-arity` (also unregistered) have stored
values with fewer or more leading λs than their declared types show. With P8
and no root-arity check, the point-free ones would compile at their stored
arity, and a field-less closure cell would read back natively as a number or
a Boolean on a well-typed input: `checkRootArities` must refuse each of them
(`rt.arity`, with both counts), as it must a `csimp` table entry that gives a
root arity 0; the roots whose counts agree, and a point-free root given an
η-long equation, compile and agree with Lean. -/

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

/-- What the compiler with P8 made. -/
structure Made where
  before : Anf.Program
  after : Anf.Program
  roots : List Root
  object : ByteArray

/-- The compiler with `Anf.defun` after the middle-end schedule `mid`. -/
def compile (cfg : Config) (inp : Input) (mid : Lam.Program → Except String Anf.Program) :
    Except Err Made := do
  let cfg := cfg.forInput inp
  let (src, lam) ← front cfg inp
  let before ← (mid lam).mapError fun m => { stage := .anf, code := "anf.produce", message := m }
  let after ← (IxCC.Anf.defun before).mapError fun m => { stage := .anf, code := "anf.defun", message := m }
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
  for (args, want) in cases.filter (fun (xs, _) => xs.headD 0 ≤ small) do
    let rb ← IxCCTests.Anf.runAnf m.before 100000 r args
    let ra ← IxCCTests.Anf.runAnf m.after 800000 r args
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
and code: register allocation's limit on parameter counts (`alloc.fallback`:
a source global of eight parameters, past the internal calling convention's
seven argument registers), which is independent of closures. -/
def refusedLater : List (String × String) := [("Closures.stateLoop", "alloc.fallback")]

/-- The closures design's workloads (`fixtures/corpus/phase2-closures`, not
yet a registered family): every root under both schedules, against the
manifest's interpreter values; a root of `refusedLater` must be refused by
that stage, after P8, with the globals over seven parameters all the
program's own (none of P8's lifted functions or dispatchers). -/
def workloads (a : Assert) (native : Option IxCCTests.Rt.Native.Tools) : IO (Array String) := do
  let fam ← IxCCTests.Corpus.Family.read (closuresDir / "corpus.json")
  let some fx := fam.fixtures.head? | do expect a false "phase2-closures: no fixture"; return #[]
  let mut out := #[]
  for r in fx.roots do
    let cases := r.cases.map fun c => (c.args, c.value.toNat!)
    let inp ← ingressFile (closuresDir / fx.closure.path) (closuresDir / fx.equations.path) [r.name]
    for (sched, mid) in [("phase1", midDefault), ("p1p2", midMinimal)] do
      let label := s!"{r.name.replace "." "_"}-{sched}"
      let res ← IO.lazyPure fun _ => compile {} inp mid
      match res, refusedLater.lookup r.name with
      | .error e, some code =>
        expect a (e.code == code) s!"{label}: refused with {e.render}, expected {code}"
        -- the globals past the internal convention's seven argument registers
        let wide : List (Anf.GlobalId × Key.GKey × Nat) := match front (({} : Config).forInput inp) inp with
          | .ok (_, lam) =>
            match (mid lam >>= IxCC.Anf.defun : Except String Anf.Program) with
            | .ok q => q.globalList.filterMap fun ((g : Anf.GlobalId), (gd : Anf.GDef)) =>
                if gd.ps.length > 7 then some (g, gd.key, gd.ps.length) else none
            | .error _ => []
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

/-- The roots of `fixtures/corpus/phase2-arity` whose compiled arity is not
their declared parameter count: the root, its compiled arity (the leading λs
of the body the table gives it) and its declared count. `Arity.main7`'s
result type is a definition of a function type, so its declared count is
below its arity; `Arity.spin` builds no closure (it compiles today without
P8). -/
def arityRefused : List (String × Nat × Nat) :=
  [("Arity.main3", 1, 2), ("Arity.main4", 0, 2), ("Arity.addTo", 1, 2), ("Arity.halve", 1, 2),
   ("Arity.main7", 2, 1), ("Arity.main8p", 1, 3), ("Arity.main9", 0, 2), ("Arity.main9r", 0, 2),
   ("Arity.main10", 0, 1), ("Arity.main11", 1, 2), ("Arity.main12", 1, 2), ("Arity.mainB3", 1, 2),
   ("Arity.mainB4", 0, 2), ("Arity.spin", 1, 2)]

/-- The start of `checkRootArities`' diagnostic for a root. -/
def arityText (name : String) (m n : Nat) : String :=
  s!"root {name} takes {m} parameters, its declared type shows {n};"

/-- A refusal by the root-arity check with both counts. -/
def expectArity (a : Assert) (label name : String) (m n : Nat) (res : Except Err Made) : IO Unit :=
  match res with
  | .error e => expect a (e.code == "rt.arity" && e.message.startsWith (arityText name m n))
      s!"{label}: refused with {e.render}, expected rt.arity: {arityText name m n}"
  | .ok _ => expect a false s!"{label}: compiled, expected rt.arity ({m} parameters against {n})"

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
those of `arityRefused` refused by the root-arity check, `Arity.main7b`
(declared and compiled count 1, its result a closure) compiled with no
readback type, the others compiled and agreeing with Lean; then two table
entries: an η-long equation for `Arity.main4` (it compiles at its declared
count) and a `csimp` entry for `Arity.slowDouble` (arity 0 against 1,
refused). -/
def arity (a : Assert) (native : Option IxCCTests.Rt.Native.Tools) : IO (Array String) := do
  let fam ← IxCCTests.Corpus.Family.read (arityDir / "corpus.json")
  let some fx := fam.fixtures.head? | do expect a false "phase2-arity: no fixture"; return #[]
  let ixe := arityDir / fx.closure.path
  let eqs := arityDir / fx.equations.path
  let mut out := #[]
  let mut refused : List String := []
  for r in fx.roots do
    let inp ← ingressFile ixe eqs [r.name]
    let label := s!"{r.name.replace "." "_"}-phase1"
    let res ← IO.lazyPure fun _ => compile {} inp midDefault
    match arityRefused.find? (·.1 == r.name) with
    | some (_, m, n) =>
      expectArity a label r.name m n res
      refused := refused ++ [s!"{r.name} ({m}/{n})"]
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
  out := out.push s!"phase2-arity: refused by the root-arity check (compiled/declared): {", ".intercalate refused}"
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
  expectArity a "slowDouble_csimp-phase1" "Arity.slowDouble" 0 1
    (← IO.lazyPure fun _ => compile {} (withProposals sd [cs]) midDefault)
  out := out.push "slowDouble_csimp-phase1: refused by the root-arity check (0/1), as expected"
  return out

def run (a : Assert) (native : Option IxCCTests.Rt.Native.Tools) : IO (Array String) := do
  let mut out := #[]
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
