import IxCCTests.Recheck.Artifact
import IxCCTests.Recheck.Kernel
import IxCCTests.Recheck.Audit
import IxCCTests.Lir.Gen
import IxCC.Lir.SplitEdges
import IxCC.Recheck.Rc.Replay

/-! The `tests-recheck` suite (M1.K1): the recheck path in kernel-evaluable
style. Building the suite evaluates, in the kernel
(`IxCCTests.Recheck.Kernel`), `Recheck.runTyped` on the fib, tak and
gcd artifacts and the whole `Recheck.run` on fib. Running it checks that
every committed artifact (`IxCCTests/Recheck/Artifacts/*.lean`)
equals a fresh ingress, `produce` and native run, so the kernel's claims
are about the live compiler, and that the recheck path's statistics-free
selection (`Select.select`) selects what `Select.run` selects on generated
Lir (`--generated N` for a longer campaign; 1,000 by default). -/

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

/-- Negative regression tests for hostile certificates, JSON inputs, axioms, and DAGs
(S1, S5, A2-2..A2-4, A4-1..A4-5). -/
def negativeSecurityTests (a : Assert) : IO (Array String) := do
  let x ← Artifact.load "fib" "Fib"
  let P := x.program
  let C := x.cert
  let cfg := x.cfg

  -- 1. S1 / A4-1: Truncated parameter relevance record (`params := []`) must be rejected.
  let cTrunc : IxCC.Recheck.Cert :=
    { C with relevance :=
        { C.relevance with consts :=
            IxCC.Src.NatMap.ofList (C.relevance.consts.toList.map fun (cid, cr) =>
              if cid == 22 then (cid, { cr with params := [] }) else (cid, cr)) } }
  expect a (IxCC.Recheck.front cfg P cTrunc).isOk.not "S1/A4-1: truncated ConstRel.params accepted"

  -- 2. S1 / A1-1: Relevant parameter forged as `.type` must be rejected.
  let cForgedParam : IxCC.Recheck.Cert :=
    { C with relevance :=
        { C.relevance with consts :=
            IxCC.Src.NatMap.ofList (C.relevance.consts.toList.map fun (cid, cr) =>
              if cid == 22 then (cid, { cr with params := [.type] }) else (cid, cr)) } }
  expect a (IxCC.Recheck.front cfg P cForgedParam).isOk.not "S1/A1-1: forged .type parameter accepted"

  -- 3. S1 / A2-2: Kept constructor field forged as `.type` must be rejected.
  let cForgedCtor : IxCC.Recheck.Cert :=
    { C with relevance :=
        { C.relevance with ctors :=
            IxCC.Src.NatMap.ofList (C.relevance.ctors.toList.map fun (cid, kr) =>
              if cid == 8 then (cid, { fields := [.type] }) else (cid, kr)) } }
  expect a (IxCC.Recheck.front cfg P cForgedCtor).isOk.not "S1/A2-2: forged .type constructor field accepted"

  -- 4. A4-2: Hostile scientific notation in JSON certificate must be rejected immediately.
  let badSci := "{\"format\":\"ixcc/cert/1\",\"n\":1e100000000000}"
  expect a (IxCC.Recheck.Cert.ofText badSci).isOk.not "A4-2: scientific notation accepted by Cert.ofText"
  expect a (IxCC.Recheck.RcReplay.Cert.ofText badSci).isOk.not "A4-2: scientific notation accepted by RcReplay.Cert.ofText"

  -- 5. A4-5: Huge NatMap key in certificate JSON must be rejected.
  let cHugeKey : IxCC.Recheck.Cert :=
    { C with table := { C.table with inline := [2000000] } }
  expect a (IxCC.Recheck.Cert.ofText (IxCC.Recheck.Cert.toText cHugeKey)).isOk.not
    "A4-5: key > maxNatMapKey accepted by Cert.ofText"

  -- 6. A4-3: Excessive Shrink rounds or smallJoin parameter must be rejected.
  let cBadShrink : IxCC.Recheck.Cert :=
    { C with mid := { C.mid with steps := [.shrink [1000]] } }
  expect a (IxCC.Recheck.front cfg P cBadShrink).isOk.not "A4-3: excessive shrink rounds accepted"
  let cBadJoin : IxCC.Recheck.Cert :=
    { C with mid := { C.mid with shrink := { caseOfCase := 512, smallJoin := 500 } } }
  expect a (IxCC.Recheck.front cfg P cBadJoin).isOk.not "A4-3: excessive smallJoin accepted"

  -- 7. A4-4: Self-inlining or excessive middle-end steps must be rejected.
  let cSelfInline : IxCC.Recheck.Cert :=
    { C with mid := { C.mid with steps := [.inline [(0, [0])]] } }
  expect a (IxCC.Recheck.front cfg P cSelfInline).isOk.not "A4-4: self-inlining accepted"
  let cTooManySteps : IxCC.Recheck.Cert :=
    { C with mid := { C.mid with steps := List.replicate 65 .prune } }
  expect a (IxCC.Recheck.front cfg P cTooManySteps).isOk.not "A4-4: >64 mid steps accepted"

  -- 8. S5 / A2-3: Equation theorem depending on an untrusted user axiom must be rejected.
  let untrustedAxId := P.size
  let untrustedThmId := P.size + 1
  let eqId := P.known.eq.getD 26
  let axEntry : IxCC.Src.ConstEntry :=
    { ref := .member default 999, addr := default
      decl := .axio true 0 (.app (.app (.app (.const eqId [.succ .zero]) (.const 31 []) .strict .rel)
        (.const 23 []) .strict .rel) (.const 23 []) .strict .rel) }
  let thmEntry : IxCC.Src.ConstEntry :=
    { ref := .member default 998, addr := default
      decl := .defn .thm .safe 0 axEntry.decl.type (.const untrustedAxId []) }
  let PWithAx : IxCC.Src.Program :=
    { P with
      consts := (P.consts.insert untrustedAxId axEntry).insert untrustedThmId thmEntry
      size := P.size + 2 }
  expect a (IxCC.Src.Table.checkEqn PWithAx 23 untrustedThmId).isOk.not
    "S5/A2-3: checkEqn accepted theorem depending on untrusted axiom"

  -- 9. A2-4: Exponentially shared Term DAG must be rejected by Term.nodesLe in O(budget).
  let rec mkDeepDag : Nat → IxCC.Src.Term → IxCC.Src.Term
    | 0, t => t
    | k + 1, t => mkDeepDag k (.app t t .strict .rel)
  let dag := mkDeepDag 25 (.natLit 0)
  expect a (!dag.nodesLe IxCC.Src.Table.maxTermNodes)
    "A2-4: depth-25 shared DAG accepted by nodesLe"

  -- 10. S1: nothing checks the callee of a projection head, so its arguments must be relevant.
  let projCall (r : IxCC.Src.Rel) : IxCC.Src.Term :=
    .app (.proj 0 0 (.natLit 0)) (.natLit 1) .strict r
  expect a (!IxCC.Src.Relevance.Check.Canonical.checkTermBinders P C.relevance [] (projCall .type) [])
    "S1: irrelevant argument at a projection-headed call accepted"
  expect a (IxCC.Src.Relevance.Check.Canonical.checkTermBinders P C.relevance [] (projCall .rel) [])
    "S1: relevant argument at a projection-headed call refused"

  -- 11. A4-2: the same number guard covers the equations sidecar.
  expect a (IxCC.Src.Hints.ofK1String "{\"n\":1e100000000000}" |>.toOption |>.isNone)
    "A4-2: scientific notation accepted in the equations sidecar"

  return #["14 hostile certificate/table/JSON/DAG regression checks passed"]

def main (args : List String) : IO UInt32 := do
  let count := match args with
    | ["--generated", n] => n.toNat!
    | _ => 1000
  let a ← IO.mkRef 0
  try
    IO.println "tests-recheck"
    part a "negative security checks (S1, S5, A2-2..A2-4, A4-1..A4-5)" (negativeSecurityTests a)
    part a "Select.select against Select.run on generated Lir" (selection a count)
    part a "recheck artifacts equal a fresh ingress, produce and run" (artifacts a)
    IO.println s!"tests-recheck: {← a.get} assertions passed"
    return 0
  catch e =>
    IO.eprintln s!"tests-recheck: FAILED after {← a.get} assertions: {e}"
    return 1

end IxCCTests.Recheck.Run
