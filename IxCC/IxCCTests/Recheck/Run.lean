import IxCCTests.Recheck.Artifact
import IxCCTests.Recheck.Kernel
import IxCCTests.Recheck.Audit
import IxCCTests.Lir.Gen
import IxCC.Lir.SplitEdges
import IxCC.Recheck.Rc.Replay
import IxCCTests.Recheck.Hostile
import IxCCTests.Recheck.Deep
import IxCCTests.Recheck.Perf
import IxCCTests.Recheck.Producer
import IxCCTests.Recheck.RootShape
import IxCCTests.Recheck.Bound

/-! The `tests-recheck` suite: the recheck path in kernel-evaluable
style. Building the suite evaluates, in the kernel
(`IxCCTests.Recheck.Kernel`), `Recheck.runTyped` on the fib, tak and
gcd artifacts and the whole `Recheck.run` on fib. Running it checks that
every committed artifact (`IxCCTests/Recheck/Artifacts/*.lean`)
equals a fresh ingress, `produce` and native run, so the kernel's claims
are about the live compiler, and that the recheck path's statistics-free
selection (`Select.select`) selects what `Select.run` selects on generated
Lir (`--generated N` for a longer campaign; 1,000 by default). It also runs
the hostile-input regression tests (`Hostile`): hostile
certificates on pin-free programs through every program-level and byte-level
verifier, Stage A in `check-cert`, the erased-typing default, the root signature
checks, the specialisation bound, the reachability dedupe, the `--rc auto`
immortal fallback, and the middle end's budgets on the inline amplifier and
other over-budget steps; the producer (`Producer`, alone with `--producer`):
its oracles rewritten for speed give the output of reference copies of the
code they replaced, it stays within the re-run's budgets, and its work,
counted in allocations, grows near-linearly on scaling inputs; the root result shapes (`RootShape`: the view and the shape view accept
every result of the shape a root's declared type describes, also at roots compiled alone, whose
objects return each constructor and whose claims `verifyBytes` accepts; SrcEval's results on the
ABI fixture's roots are of it; the shape view rejects an ill-typed root's constructor of
another type, which the view relabels; and the plain-RC view accepts the constructor trees of a
plain-RC root's declared type); the role-bound closures (`Bound`: their claims, from `makeClaim`, are
accepted by `verifyBytes` and `checkClaim` and name the role-bound root, and their objects are
byte for byte those of the unbound twins); and every verifier entry point on the crashing inputs and on generated deep
and wide inputs in a child process whose Lean stack is 8 MiB (`--stack-8mib`).
`--producer-reference` counts the replaced code's allocations on the same
inputs. `--perf-write`, `--perf-stages` and `--perf-anf` write the producer's scaling
inputs and time the producer and the checker stage by stage (`Perf`). -/

namespace IxCCTests.Recheck.Run

open IxCCTests.Src

def part (a : Assert) (label : String) (action : IO (Array String)) : IO Unit := do
  let before ← a.get
  let (lines, ms) ← timed action
  IO.println s!"  {label}: {(← a.get) - before} assertions, {ms} ms"
  for line in lines do IO.println s!"    {line}"
  (← IO.getStdout).flush

/-- Every committed artifact equals the printer's output on a fresh run. -/
def artifacts (a : Assert) : IO (Array String) := do
  let mut lines := #[]
  for (name, modName) in Artifact.artifacts do
    let x ← Artifact.load name modName
    let (text, stats) := Artifact.render x
    let file := Artifact.path modName
    let old ← IO.FS.readFile file
    expect a (old == text) s!"{file} is stale (run lake exe gen-recheck-artifacts)"
    lines := lines.push stats
  return lines

/-- The recheck path's selection (`Select.select`, statistics off) selects
what `Select.run` selects, or declines alike, on generated Lir programs. -/
def selection (a : Assert) (count : Nat) : IO (Array String) := do
  let mut selected := 0
  let mut declined := 0
  for seed in [0:count] do
    let (raw, _) := IxCCTests.Lir.Gen.program {} (UInt64.ofNat seed)
    let p := raw.splitCriticalEdges
    match IxCC.Xv.Select.run p, IxCC.Xv.Select.select p with
    | .ok (q, _), .ok q' =>
      expect a (q == q') s!"seed {seed}: Select.select differs from Select.run"
      selected := selected + 1
    | .error e, .error e' =>
      expect a (e.form == e'.form && e.reason == e'.reason && e.fn == e'.fn && e.block == e'.block &&
        e.stmt == e'.stmt) s!"seed {seed}: the declines differ"
      declined := declined + 1
    | _, _ => expect a false s!"seed {seed}: one selection declines, the other does not"
  return #[s!"{count} generated programs: {selected} selected alike, {declined} declined alike"]

/-- Negative regression tests for hostile certificates, JSON inputs, axioms, and DAGs. -/
def negativeSecurityTests (a : Assert) : IO (Array String) := do
  let x ← Artifact.load "fib" "Fib"
  let P := x.program
  let C := x.cert
  let cfg := x.cfg
  -- The constants the mutations target, by their meaning in the program (a
  -- regeneration renumbers constants; a literal number could move a mutation
  -- onto a constant it does not affect), and each mutation must be refused at
  -- its own stage.
  let some (_, entry) := P.roots.head? | throw (IO.userError "fib: no root")
  let some natSucc := P.known.natSucc | throw (IO.userError "fib: no Nat.succ")
  let some nat := P.known.nat | throw (IO.userError "fib: no Nat")
  let some eqId := P.known.eq | throw (IO.userError "fib: no Eq")
  -- (ingress leaves the program's table empty; the certificate's table holds
  -- the definitions whose equations `produce` checked)
  let some eqnSubject := C.table.resolve.findSome? fun (c, e) =>
      match e with | .eqn _ => some c | _ => none
    | throw (IO.userError "fib: no definition with an equation in the certificate's table")
  let refusedAt (r : Except IxCC.Recheck.Err _) (stage : IxCC.Recheck.Stage) (code : Option String := none) :=
    match r with
    | .error e => e.stage == stage && code.all (· == e.code)
    | .ok _ => false

  -- 1. Truncated parameter relevance record (`params := []`) must be rejected.
  let cTrunc : IxCC.Recheck.Cert :=
    { C with relevance :=
        { C.relevance with consts :=
            IxCC.Src.NatMap.ofList (C.relevance.consts.toList.map fun (cid, cr) =>
              if cid == entry then (cid, { cr with params := [] }) else (cid, cr)) } }
  expect a (refusedAt (IxCC.Recheck.front cfg P cTrunc) .relevance) "S1/A4-1: truncated ConstRel.params not refused by the relevance check"

  -- 2. Relevant parameter forged as `.type` must be rejected.
  let cForgedParam : IxCC.Recheck.Cert :=
    { C with relevance :=
        { C.relevance with consts :=
            IxCC.Src.NatMap.ofList (C.relevance.consts.toList.map fun (cid, cr) =>
              if cid == entry then (cid, { cr with params := [.type] }) else (cid, cr)) } }
  expect a (refusedAt (IxCC.Recheck.front cfg P cForgedParam) .relevance) "S1/A1-1: forged .type parameter not refused by the relevance check"

  -- 3. Kept constructor field forged as `.type` must be rejected.
  let cForgedCtor : IxCC.Recheck.Cert :=
    { C with relevance :=
        { C.relevance with ctors :=
            IxCC.Src.NatMap.ofList (C.relevance.ctors.toList.map fun (cid, kr) =>
              if cid == natSucc then (cid, { fields := [.type] }) else (cid, kr)) } }
  expect a (refusedAt (IxCC.Recheck.front cfg P cForgedCtor) .relevance) "S1/A2-2: forged .type constructor field of Nat.succ not refused by the relevance check"

  -- 4. Hostile scientific notation in JSON certificate must be rejected immediately.
  let badSci := "{\"format\":\"ixcc/cert/1\",\"n\":1e100000000000}"
  expect a (IxCC.Recheck.Cert.ofText badSci).isOk.not "A4-2: scientific notation accepted by Cert.ofText"
  expect a (IxCC.Recheck.RcReplay.Cert.ofText badSci).isOk.not "A4-2: scientific notation accepted by RcReplay.Cert.ofText"

  -- 5. Huge NatMap key in certificate JSON must be rejected.
  let cHugeKey : IxCC.Recheck.Cert :=
    { C with table := { C.table with inline := [2000000] } }
  expect a (IxCC.Recheck.Cert.ofText (IxCC.Recheck.Cert.toText cHugeKey)).isOk.not
    "A4-5: key > maxNatMapKey accepted by Cert.ofText"

  -- 6. Excessive Shrink rounds or smallJoin parameter must be rejected.
  let cBadShrink : IxCC.Recheck.Cert :=
    { C with mid := { C.mid with steps := [.shrink [1000]] } }
  expect a (refusedAt (IxCC.Recheck.front cfg P cBadShrink) .anf "anf.replay") "A4-3: excessive shrink rounds not refused by the middle-end bounds"
  let cBadJoin : IxCC.Recheck.Cert :=
    { C with mid := { C.mid with shrink := { caseOfCase := 512, smallJoin := 500 } } }
  expect a (refusedAt (IxCC.Recheck.front cfg P cBadJoin) .anf "anf.replay") "A4-3: excessive smallJoin not refused by the middle-end bounds"

  -- 7. Self-inlining or excessive middle-end steps must be rejected.
  let cSelfInline : IxCC.Recheck.Cert :=
    { C with mid := { C.mid with steps := [.inline [(0, [0])]] } }
  expect a (refusedAt (IxCC.Recheck.front cfg P cSelfInline) .anf) "A4-4: self-inlining not refused by the middle end"
  let cTooManySteps : IxCC.Recheck.Cert :=
    { C with mid := { C.mid with steps := List.replicate 65 .prune } }
  expect a (refusedAt (IxCC.Recheck.front cfg P cTooManySteps) .anf "anf.replay") "A4-4: >64 mid steps not refused by the middle-end bounds"

  -- 8. Equation theorem depending on an untrusted user axiom must be rejected.
  let untrustedAxId := P.size
  let untrustedThmId := P.size + 1
  let axEntry : IxCC.Src.ConstEntry :=
    { ref := .member default 999, addr := default
      decl := .axio true 0 (.app (.app (.app (.const eqId [.succ .zero]) (.const nat []) .strict .rel)
        (.const eqnSubject []) .strict .rel) (.const eqnSubject []) .strict .rel) }
  let thmEntry : IxCC.Src.ConstEntry :=
    { ref := .member default 998, addr := default
      decl := .defn .thm .safe 0 axEntry.decl.type (.const untrustedAxId []) }
  let PWithAx : IxCC.Src.Program :=
    { P with
      consts := (P.consts.insert untrustedAxId axEntry).insert untrustedThmId thmEntry
      size := P.size + 2 }
  expect a (match IxCC.Src.Table.checkEqn PWithAx eqnSubject untrustedThmId with
      | .error msg => msg == "theorem depends on a non-standard axiom or exceeds closure budget"
      | .ok _ => false)
    "S5/A2-3: checkEqn did not refuse a theorem depending on an untrusted axiom for that reason"

  -- 9. Exponentially shared Term DAG must be rejected by Term.nodesLe in O(budget).
  let rec mkDeepDag : Nat → IxCC.Src.Term → IxCC.Src.Term
    | 0, t => t
    | k + 1, t => mkDeepDag k (.app t t .strict .rel)
  let dag := mkDeepDag 25 (.natLit 0)
  expect a (!dag.nodesLe IxCC.Src.Table.maxTermNodes)
    "A2-4: depth-25 shared DAG accepted by nodesLe"

  -- 10. Nothing checks the callee of a projection head, so its arguments must be relevant.
  let projCall (r : IxCC.Src.Rel) : IxCC.Src.Term :=
    .app (.proj 0 0 (.natLit 0)) (.natLit 1) .strict r
  expect a (!IxCC.Src.Relevance.Check.Canonical.checkTermBinders P C.relevance [] (projCall .type) [])
    "S1: irrelevant argument at a projection-headed call accepted"
  expect a (IxCC.Src.Relevance.Check.Canonical.checkTermBinders P C.relevance [] (projCall .rel) [])
    "S1: relevant argument at a projection-headed call refused"

  -- 11. The same number guard covers the equations sidecar.
  expect a (IxCC.Src.Hints.ofK1String "{\"n\":1e100000000000}" |>.toOption |>.isNone)
    "A4-2: scientific notation accepted in the equations sidecar"

  return #["14 hostile certificate/table/JSON/DAG regression checks passed"]

/-- The producer's part: its rewritten oracles against the reference copies
of the code they replaced, and its work on scaling inputs. -/
def producerPart (a : Assert) (count : Nat) : IO (Array String) := do
  let extra ← [("many", 60), ("fns", 20), ("dag", 8), ("tree", 9), ("wide", 9)].mapM fun (s, n) => do
    return (s!"{s} {n}", ← Producer.lamOf s n)
  return (← Producer.orderSame a (count / 4)) ++ (← Producer.middleSame a (count / 4) extra) ++
    (← Producer.budgets a) ++ (← Producer.work a)

def main (args : List String) : IO UInt32 := do
  if let "--probe" :: rest := args then return ← Deep.probe rest
  if let ["--probe-amp", f, g] := args then return ← Deep.probeAmp f.toNat! g.toNat!
  if let ["--probe-amp", f, g, stg] := args then return ← Deep.probeAmp f.toNat! g.toNat! stg
  if let ["--probe-walk", n] := args then return ← Deep.probeWalk n.toNat!
  if let ["--probe-back", kind, n, k] := args then return ← Deep.probeBack kind n.toNat! k.toNat!
  if let ["--probe-lam", kind, n, stg] := args then return ← Deep.probeLam kind n.toNat! stg
  if let ["--probe-walkk", kind, n, c, op] := args then return ← Deep.probeWalkKind kind n.toNat! c.toNat! op
  if args == ["--stack-8mib"] then return ← Deep.stack8
  if args == ["--stack-2mib"] then return ← Deep.stack2
  if args == ["--producer-reference"] then return ← Producer.referenceWork
  if args == ["--producer"] then
    -- the producer's part alone
    let a ← IO.mkRef 0
    try
      part a "the producer: rewritten oracles give the reference's output, and near-linear work"
        (producerPart a 1000)
      IO.println s!"tests-recheck --producer: {← a.get} assertions passed"
      return 0
    catch e =>
      IO.eprintln s!"tests-recheck --producer: FAILED after {← a.get} assertions: {e}"
      return 1
  if let ["--write-shrink", dir, d] := args then
    Deep.writeShrink dir d.toNat!
    return 0
  if let ["--write-shrink", dir, d, r, s] := args then
    Deep.writeShrink dir d.toNat! r.toNat! s.toNat! s!"tree-{d}-{r}-{s}"
    return 0
  if let ["--wide", kind, n] := args then return ← Deep.probeWide kind n.toNat!
  if let ["--size-diag", shp, n] := args then return ← Deep.sizeDiag shp n.toNat!
  if let ["--write-wide", dir, kind, n] := args then
    Deep.writeWide dir kind n.toNat!
    return 0
  if let ["--write-alloc", dir, kind, n] := args then
    Deep.writeAlloc dir kind n.toNat!
    return 0
  if let ["--write-amp", dir, f, g] := args then
    Deep.writeAmp dir f.toNat! g.toNat!
    return 0
  if let ["--perf-write", dir, shp, n] := args then
    Perf.write dir shp n.toNat!
    return 0
  if let "--perf-stages" :: file :: eqs :: mode :: roots := args then
    return ← Perf.stages file eqs mode roots
  if let ["--perf-anf", kind, n, k] := args then return ← Perf.anfStages kind n.toNat! k.toNat!
  if let ["--write-amp-shrink", dir, f, g] := args then
    Deep.writeAmpShrink dir f.toNat! g.toNat!
    return 0
  let count := match args with
    | ["--generated", n] => n.toNat!
    | _ => 1000
  let a ← IO.mkRef 0
  try
    IO.println "tests-recheck"
    part a "negative security checks (S1, S5, A2-2..A2-4, A4-1..A4-5)" (negativeSecurityTests a)
    part a "pin-free programs through the program-level verifiers (REPORT item 1)" do
      return #[← Hostile.pinFree a 3, ← Hostile.pinFree a 2]
    part a "Stage A in check-cert, erased typing by default, N4, N6 and S10 (B2-4)" do
      return #[← Hostile.cliStageA a, ← Hostile.typecheckDefault a, ← Hostile.rootChecks a,
        ← Hostile.reachDedupe a]
    part a "the --rc auto immortal fallback and check-cert --rc (B1-6, B1-8)" do
      return #[← Hostile.autoFallback a]
    part a "middle-end budgets (REPORT item 2)" do
      return #[← Hostile.budgets a, ← Hostile.betaMoves a, ← Hostile.retryFallbackMechanism a,
        ← Hostile.retryRound a, ← Hostile.retryLater a, ← Hostile.shrinkWork a,
        ← Hostile.inlineAmplifier a]
    part a "the producer: rewritten oracles give the reference's output, and near-linear work" do
      producerPart a count
    part a "root result shapes: totality of the view on the shapes, SrcEval results of the shape" do
      return (← RootShape.abi a).push (← RootShape.pinFree a)
    part a "roots compiled alone: every result constructor has a row; the shape view" do
      return (← RootShape.aloneCases a).push (← RootShape.illTyped a)
    part a "plain-RC roots: the view accepts the constructor trees of the declared type" do
      RootShape.plainRc a
    part a "role-bound closures: the byte-level verifiers accept their claims; the objects are the unbound twins'" do
      Bound.run a
    part a "every verifier on an 8 MiB stack (FA follow-up, item 1)" (Deep.stackPart a)
    part a "Select.select against Select.run on generated Lir" (selection a count)
    part a "recheck artifacts equal a fresh ingress, produce and run" (artifacts a)
    IO.println s!"tests-recheck: {← a.get} assertions passed"
    return 0
  catch e =>
    IO.eprintln s!"tests-recheck: FAILED after {← a.get} assertions: {e}"
    return 1

end IxCCTests.Recheck.Run
