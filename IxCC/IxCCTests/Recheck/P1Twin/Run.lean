import IxCCTests.Recheck.ErasedPartial
import IxCCTests.Recheck.P1Twin.Plants

/-! # `tests-p1-twin`: P1's invariant tested by running it

Relevance preservation (P1, `IxCC.Src.Relevance.Proof.P1.Defs`) is proved
(`IxCC.Src.Relevance.Proof.P1.Main`) with the run's sort events (`SortAgree`) as a hypothesis, which
is not proved. This suite runs SrcEval's twin (`Twin.lean`, SrcEval's control flow in `IO` checking the sort events (a), (c)-(f) of
`SortCoherent`) with the executable forms of `Pre`, `Post`, `Reads` and the invariants (`Exec.lean`,
clause by clause from `P1.Defs`, exact where decidable, `Live` cut at a stated depth) and a mutant pass
(`Pass.lean`) at sampled calls, on

* the registered runs: every root and case of the 12 corpus manifests (`phase1-boundary` with the 23
  cases whose exponent or shift argument exceeds 2^32 − 1 left out: compiled `Nat.pow`, `lean_nat_pow`,
  aborts the process there, in SrcEval and the twin alike; SrcEval's meaning is total), and every program
  the five erased-position test parts accept (through `Erased.Hooks`, the parts' own assertions run too);
* planted programs (`Plants.lean`), the reproductions of the statements repaired at the definitions
  landing among them.

It asserts: (a) on the registered runs, twin = SrcEval, no `SortAgree` violation, the root result `Live`
on every run that returns, the exact `Pre` true (or undecided by the depth cut, counted) at every sampled
call, and no `Post` or `Reads` failure; (b) no counterexample in any mutation class (a mutant `Pre`
accepts, `SortAgree` holds from it, and `Post`, a child step's `Pre` or `Reads` fails); (c) each
reproduction is closed: (i), (iii) in both forms and (iv) rejected by `Pre` with the repaired clause the
one broken alone, (v) at `Quot.lift` and at a `case` key refused by `appliedAt` alone. `SortAgree` is
tested here on the registered runs, not proved.

What the pass cannot reach: it mutates the values of sampled calls, never a declaration, a record or a
table entry, so a state whose distinguishing property is a declaration, record or table fact the
registered programs lack (a constructor field written erased under a subsingleton eliminator, a missing
record, a recursor with a table entry) is tested only where a plant builds it. "No counterexample" is
not coverage of adversarial programs.

The pass makes no mutation that moves the arguments of `Nat.pow` or `Nat.shiftLeft`, and runs no mutant
that saturates either with an exponent above 2^32 − 1 (the same abort; `bigExp`). Sampling is
deterministic: the seed, the budgets and the depth cut are printed, and the same ones give the same
counts. -/

namespace IxCCTests.Recheck.P1Twin
open IxCC IxCC.Src Lean
open IxCCTests.Src (Assert expect)

/-- The 12 corpus manifests (from `IxCC/`). -/
def manifests : List String :=
  ["fixtures/ixon-v4/k1/corpus.json", "fixtures/ownership/corpus.json", "fixtures/ixon-v4/bench-k1/corpus.json",
   "fixtures/corpus/phase1-scalar/corpus.json", "fixtures/corpus/phase1-boundary/corpus.json",
   "fixtures/corpus/phase1-resource/corpus.json", "fixtures/corpus/phase1-decline/corpus.json",
   "fixtures/corpus/phase1-abi/corpus.json", "fixtures/corpus/phase2-closures/corpus.json",
   "fixtures/corpus/phase2-arity/corpus.json", "fixtures/corpus/phase1-machines/corpus.json",
   "fixtures/corpus/grounding/corpus.json"]

/-- The argument of a `phase1-boundary` root that is an exponent or a shift (RO's `filter.jq`). -/
def expArgIdx : String → Option Nat
  | "Boundary.pow" => some 1 | "Boundary.kPow" => some 0 | "Boundary.powMod" => some 1
  | "Boundary.shl" => some 1 | "Boundary.kShl" => some 0 | "Boundary.shlShr" => some 1
  | _ => none

/-- A case left out: its exponent or shift argument exceeds 2^32 − 1. -/
def bigExpCase (root : String) (args : List Nat) : Bool :=
  match expArgIdx root with
  | some i => decide (args.getD i 0 > 4294967295)
  | none => false

structure CorpusTotals where
  roots : Nat := 0
  skipped : Nat := 0
  runs : Nat := 0
  filtered : Nat := 0

/-- Every root and case of `ms`, through the twin with the pass. -/
def corpus (ms : List String) : IO CorpusTotals := do
  let x0 ← newCx {} {} (looseChecked {})
  let mut t : CorpusTotals := {}
  for m in ms do
    let j ← IO.ofExcept (Json.parse (← IO.FS.readFile m))
    let fam := (j.getObjValAs? String "family").toOption.getD m
    let dir := (j.getObjValAs? String "directory").toOption.getD "."
    for f in (j.getObjValAs? (Array Json) "fixtures").toOption.getD #[] do
      let fx := (f.getObjValAs? String "name").toOption.getD "?"
      let clo := ((f.getObjVal? "closure").bind (·.getObjValAs? String "path")).toOption.getD ""
      let eqs := ((f.getObjVal? "equations").bind (·.getObjValAs? String "path")).toOption.getD ""
      let raw ← IO.FS.readBinFile (System.FilePath.mk dir / clo)
      let sc ← IO.ofExcept (Json.parse (← IO.FS.readFile (System.FilePath.mk dir / eqs)))
      for rt in (f.getObjValAs? (Array Json) "roots").toOption.getD #[] do
        let name := (rt.getObjValAs? String "name").toOption.getD "?"
        let addr := (rt.getObjValAs? String "address").toOption.getD "?"
        let tog := ((rt.getObjValAs? (Array String) "together").toOption.getD #[]).toList
        let cases := (rt.getObjValAs? (Array Json) "cases").toOption.getD #[]
        let res : Except String (Recheck.Artifact × Relevance.Ann) := do
          let inp ← (Recheck.ingress raw sc (name :: tog)).mapError (·.render)
          let cfg := Recheck.Config.forInput {} inp
          let cert ← (Recheck.produce cfg inp).mapError (·.render)
          let art ← (Recheck.run cfg inp.program cert).mapError (·.render)
          pure (art, cert.relevance)
        match res with
        | .error e => t := { t with skipped := t.skipped + 1 }; IO.println s!"SKIP {fam} {fx} {name}: {(e.take 90).toString}"
        | .ok (art, ann) =>
          match art.src.roots.find? (fun (a, _) => toString a == addr) with
          | none => t := { t with skipped := t.skipped + 1 }; IO.println s!"SKIP {fam} {fx} {name}: root not found"
          | some (_, cid) =>
            t := { t with roots := t.roots + 1 }
            let xp ← acceptedCx s!"{fam} {fx} {name}" art.src ann art.checked
            let counts ← IO.mkRef []
            let notes ← IO.mkRef []
            let x : TCx := { xp with counts := counts, notes := notes }
            if !ctorUniqueB art.src then x.bump "VIOLATION ShapeOk.ctorUnique"
            for cs in cases do
              let args := ((cs.getObjValAs? (Array Nat) "args").toOption.getD #[]).toList
              if bigExpCase name args then t := { t with filtered := t.filtered + 1 }
              else
                twinRun x kRun cid (args.map .lit)
                t := { t with runs := t.runs + 1 }
            if cases.isEmpty then
              twinRun x kRun cid []
              t := { t with runs := t.runs + 1 }
            recordAccepted x
            for (k, n) in ← x.counts.get do x0.add k n
      (← IO.getStdout).flush
  IO.println s!"CORPUS roots run {t.roots}, skipped {t.skipped}, runs {t.runs}, cases filtered {t.filtered}"
  report "corpus (all roots)" x0
  return t

/-- Options before the mode: `--no-pass`, `--unrepaired`, `--seed N`, `--samples N`, `--per N`,
`--checks N`, `--depth N`, `--trace`. -/
partial def options : List String → IO (List String)
  | "--no-pass" :: rest => do gPass.set false; options rest
  | "--unrepaired" :: rest => do gCfg.modify ({ · with repaired := false }); options rest
  | "--seed" :: n :: rest => do gCfg.modify ({ · with seed := n.toNat! }); options rest
  | "--samples" :: n :: rest => do gCfg.modify ({ · with samples := n.toNat! }); options rest
  | "--per" :: n :: rest => do gCfg.modify ({ · with perClass := n.toNat! }); options rest
  | "--checks" :: n :: rest => do gCfg.modify ({ · with maxChecks := n.toNat! }); options rest
  | "--depth" :: n :: rest => do gCfg.modify ({ · with depth := n.toNat! }); options rest
  | "--trace" :: rest => do gCfg.modify ({ · with trace := true }); options rest
  | rest => pure rest

/-- The five erased-position parts, hooked. -/
def tests (a : Assert) : IO Unit := do
  for (name, t) in [("Erased", IxCCTests.Recheck.Erased.run a hooks),
      ("ErasedBlocks", IxCCTests.Recheck.ErasedBlocks.run a hooks),
      ("ErasedPartial", IxCCTests.Recheck.ErasedPartial.run a hooks),
      ("Shape", IxCCTests.Recheck.Shape.run a hooks), ("ErasedArity", IxCCTests.Recheck.ErasedArity.run a hooks)] do
    let lines ← t
    IO.println s!"TESTS {name}: {lines.size} lines, assertions so far {← a.get}"

def sumCol (m : Std.HashMap String (Array Nat)) (i : Nat) : Nat :=
  m.fold (fun acc _ arr => acc + arr.getD i 0) 0

/-- The assertions on the registered runs (before the plants run): (a) and (b). -/
def assertRegistered (a : Assert) (t : CorpusTotals) : IO Unit := do
  let g ← theAgg
  let viol ← gAccViol.get
  expect a viol.isEmpty s!"(a) violations on the runs of accepted programs: {viol.take 10}"
  expectEq' a t.filtered 23 "(a) phase1-boundary cases filtered"
  let real ← g.real.get
  IO.println s!"REAL CALLS checked {sumCol real 0}, Pre holds {sumCol real 1}, undecided (depth cut \
    {(← gCfg.get).depth}) {sumCol real 2}, Pre fails {sumCol real 3}, Post fails {sumCol real 4}, child Pre \
    fails {sumCol real 5}, Reads fails {sumCol real 6}"
  expect a (sumCol real 3 == 0 && sumCol real 4 == 0 && sumCol real 5 == 0 && sumCol real 6 == 0)
    s!"(a) a sampled real call: Pre, Post, a child's Pre or Reads fails: {(← g.realRej.get).toList}"
  expect a ((← g.findings.get) == 0) s!"(b) counterexamples on the registered runs: {← g.findings.get}"
where expectEq' (a : Assert) (got want : Nat) (msg : String) : IO Unit :=
  expect a (got == want) s!"{msg}: {got}, expected {want}"

/-- (c): the repaired clause broken alone at each reproduction's state (the pass's own count). -/
def assertReproductions (a : Assert) : IO Unit := do
  let sole ← (← theAgg).sole.get
  let has := fun (label cls cs clause : String) => (sole.getD s!"{label}\t{cls}\t{cs}\t{clause}" 0) > 0
  expect a (has "recursor: minor λ a (0 b) c. c over field 1 written erased" "dropField" "F2 recr"
    "Live.con: MarkersPlaced.count (i)") "(c) (i): the short constructor value at F2 not rejected by MarkersPlaced.count alone"
  expect a (has "(iii) Key.rec with a csimp entry, rule 0's body Sort 0" "swapHead" "F1 ctor"
    "HeadSeen: specialHead? (iii)") "(c) (iii): `.recr Key.rec` with a table entry not rejected by specialHead? alone"
  expect a (has "Quot.lift idc h (Quot.mk r c₁)" "swapHead" "F8 Quot.lift" "HeadSeen: specialHead? (iii)")
    "(c) (iii): `.quotMk` of a non-quot constant not rejected by specialHead? alone"
  expect a (has "(iv) a second Quot.mk declaration writing its element erased (unreached, with its record)"
    "quotElem" "F8 Quot.lift" "Live.con: MarkersPlaced.quotElem (iv)")
    "(c) (iv): the marker element of a Quot.mk written erased not rejected by MarkersPlaced.quotElem alone"

def main (args0 : List String) : IO UInt32 := do
  let args ← options args0
  let cfg ← gCfg.get
  IO.println s!"tests-p1-twin: seed {cfg.seed}, depth cut {cfg.depth}, samples {cfg.samples} per case, \
    {cfg.perClass} mutants per class and case, {cfg.maxChecks} checks per program, repaired {cfg.repaired}, \
    pass {← gPass.get}; the exponent rule (no mutant moves or saturates Nat.pow/Nat.shiftLeft's \
    exponent above 2^32 - 1)"
  let a : Assert ← IO.mkRef 0
  try
    match args with
    | [] =>
      tests a
      let t ← corpus manifests
      assertRegistered a t
      Plants.run a
      assertReproductions a
      expect a ((← (← theAgg).findings.get) == 0) "(b) counterexamples on the plants"
    | ["tests"] => tests a
    | ["plants"] => Plants.run a
    | "corpus" :: ms => let _ ← corpus (if ms.isEmpty then manifests else ms)
    | _ => IO.println "usage: tests-p1-twin [options] [tests | plants | corpus [MANIFEST...]]"; return 2
    (← theAgg).print
    IO.println s!"tests-p1-twin: {← a.get} assertions passed"
    return 0
  catch e =>
    (← theAgg).print
    IO.eprintln s!"tests-p1-twin: FAILED: {e}"
    return 1

end IxCCTests.Recheck.P1Twin
