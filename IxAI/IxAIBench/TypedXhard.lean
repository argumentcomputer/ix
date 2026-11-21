import IxAIBench.Typed
import IxAICore.Xhard

/-!
# IxBench M2b: Tseitin parity formulas (`prop-xhard`)

`ixai bench typed-xhard` reports the `prop-xhard` family (`IxAICore.Xhard`): the label guarantee
of the generator (`XInst.check`, `XInst.check_sound`) on the validation and evaluation draws, the
refutation search's hit rate on unsatisfiable cores at budgets 16, 64 and 256 nodes, a model
without certificates, and the certificate + model + defer pipeline of `certSection` at the
16-node budget of `prop-hard`. Results go to `.truthmines/bench/bench-typed-xhard.tsv` with a
BLAKE3; `bench-typed.tsv` is not touched. `unresolvedSection` then compares the model with the
outer-form rule on the items left without a certificate and measures each pipeline's throughput,
in `bench-typed-xhard-unresolved.tsv`. `ixai bench typed-xhard-sweep` compares training seeds on
validation for the two models.

`ixai bench export-xhard DIR` writes the batches `prop-xhard-NN` (25 items each, the first
`exportItems` fresh instances), the key `DIR/keys/xhard.tsv` and their manifest rows;
`ixai bench score-xhard DIR` scores `DIR/answers/prop-xhard-*.txt`.
-/

namespace IxAIBench.TypedBench

open IxAICore IxAICore.Typed

/- Closed subterms such as the validation draws would otherwise become module initializers, run at
every start of `ixai` whatever the command. -/
set_option compiler.extract_closed false

def xGen : XGen := XGen.default
def xSpec : Spec PForm := xhardSpec xGen

def xFam : CertFam :=
  { name := "prop-xhard", heading := "Propositional status, Tseitin parity (`prop-xhard`)", atoms := xGen.atoms
    spec := xhardCertSpec xGen, config := logicXhardCertConfig }

/-- Refutation searches at 16, 64 and 256 nodes, each deep enough for a full tree of its budget. -/
def xBudgets : List RefuteCfg :=
  [LogicGen.refute, { LogicGen.refute with budget := 64, depth := 8 },
   { LogicGen.refute with budget := 256, depth := 10 }]

def drawX (g : XGen) : Nat → Rng → List XInst × Rng
  | 0, r => ([], r)
  | k + 1, r =>
    let (x, r) := sampleXInst g r
    let (xs, r) := drawX g k r
    (x :: xs, r)

/-- The construction: unsatisfiable, a satisfiable trap (odd charges, one clause removed), or a
satisfiable even instance. -/
def kindOf (x : XInst) : String :=
  if x.claim != .contingent then "unsatisfiable core" else if x.graph.odd then "trap" else "even"

/-- DPLL nodes to decide a CNF: `boundedDpll` follows `Dpll.dpll`'s search and counts its calls. -/
def dpllNodes (F : Dpll.CNF) : Nat :=
  let big := 1000000000
  big - (boundedDpll (Dpll.size F + 1) F big).2

def median (xs : List Nat) : Nat := ((xs.toArray.qsort (· < ·)).toList.drop (xs.length / 2)).headD 0

/-! ## What the model adds where the solver gives no certificate -/

/-- The outer-form rule: a CNF is answered contradiction and a DNF tautology (contingent for a
formula that is neither). It reads only the formula's top-level shape, so it is right on exactly
the unsatisfiable cores. -/
def outerFormAnswer (f : PForm) : Answer :=
  let s : Status := if f.cnf?.isSome then .contradiction else if f.dual.cnf?.isSome then .tautology else .contingent
  { pred := Finite.index s, conf := 256 }

/-- The solver alone at budget `rc`: the certified status (`certify_sound`), or no answer. -/
def solverAnswer (rc : RefuteCfg) (f : PForm) : Option Answer :=
  (certify xFam.atoms rc f).map fun s => { pred := Finite.index s, conf := 256, certified := true }

/-- The solver, and the outer-form rule where it gives no certificate. -/
def solverRuleAnswer (rc : RefuteCfg) (f : PForm) : Answer := (solverAnswer rc f).getD (outerFormAnswer f)

def optChecksum (as : List (Option Answer)) : Nat :=
  Answer.checksum (as.filterMap id) + (as.filter Option.isNone).length

/-- Per second, from a count and the nanoseconds it took. -/
def perSecond (k ns : Nat) : Nat := k * 1000000000 / max ns 1

/-- `timeNs` that also returns the timed function's result. -/
def timeResult {α β : Type} (input : α) (f : α → β) (force : β → Nat) : IO (Nat × β) := do
  let inp ← IO.mkRef input
  let res ← IO.mkRef 0
  let t0 ← IO.monoNanosNow
  let x ← inp.get
  let r := f x
  res.set (force r)
  let t1 ← IO.monoNanosNow
  return (t1 - t0, r)

/-- On the `prop-xhard` evaluation items the solver leaves unresolved at the `prop-xhard-cert`
budget, the certified model's answers against the outer-form rule's; and on all evaluation items,
the time and throughput of the solver alone, the solver with the rule, and the solver with the
model (with and without its defer threshold), all at that budget, single thread. Timed functions
return answers only; reference labels are joined afterwards. Results go to
`bench-typed-xhard-unresolved.tsv` (with a BLAKE3), wall clock to its `.clock.tsv`. -/
def unresolvedSection (mc : Model) (sc : Split PForm) : IO Unit := do
  let o ← Out.new
  let rc := LogicGen.refute
  let spec := xFam.spec rc
  let xs := sc.test
  let n := xs.length
  let statusLabels := ["contradiction", "contingent", "tautology"]
  let (sNs, solverAns) ← timeResult xs (fun xs => xs.map (solverAnswer rc)) optChecksum
  let (rNs, ruleAns) ← timeResult xs (fun xs => xs.map (solverRuleAnswer rc)) Answer.checksum
  let (mNs, modelAns) ← timeResult xs (fun xs => xs.map (certAnswerOf rc mc · xFam)) Answer.checksum
  let labels := xs.map (targetOf spec 0)
  let solver := solverAns.toArray
  let join := fun (as : List Answer) => ((as.zip labels).map fun (a, t) => a.withTarget t).toArray
  let ruleP := join ruleAns
  let modelP := join modelAns
  let reference := (xs.map fun f => (certPredOf rc mc f xFam).1).toArray
  let joinedOk := modelP.size == reference.size && (modelP.zip reference).all fun (a, b) =>
    a.target == b.target && a.pred == b.pred && a.conf == b.conf
  let flagsOk := (modelAns.toArray.zip solver).all fun (a, s) => a.certified == s.isSome
  let open_ := (Array.range n).filter fun i => solver[i]!.isNone
  let certified := n - open_.size
  let mU := pick modelP open_
  let rU := pick ruleP open_
  let rs := resamples boot open_.size
  let accM := fun (idx : Array Nat) => (accuracyBp (pick mU idx) : Int)
  let accR := fun (idx : Array Nat) => (accuracyBp (pick rU idx) : Int)
  let all := identity open_.size
  let agree := countIf (mU.zip rU) fun (a, b) => a.pred == b.pred
  let byLabel := fun (ps : Array Pred) => ", ".intercalate (statusLabels.zipIdx.map fun (l, k) =>
    s!"{l} {countIf ps fun p => p.target == k && p.correct}/{countIf ps (·.target == k)}")
  IO.println s!"### Where the solver gives no certificate (refutation budget {rc.budget} nodes)\n"
  IO.println s!"{open_.size} of {n} evaluation items have no certificate. The outer-form rule answers contradiction for a CNF and tautology for a DNF, from the top-level shape alone; the model is the `prop-xhard-cert` model. Bootstrap {boot.resamples} resamples, seed {boot.seed}, paired.\n"
  let ciM := bootCI rs accM
  let ciR := bootCI rs accR
  let gap := pairedCI rs accM accR
  IO.println (table ["decider", "n", "accuracy [95% CI]", "correct by label"]
    [["model", toString mU.size, s!"{showPct (accM all).toNat} {showCI ciM}", byLabel mU],
     ["outer-form rule", toString rU.size, s!"{showPct (accR all).toNat} {showCI ciR}", byLabel rU],
     ["model − rule (paired)", "", s!"{showGap (accM all - accR all)} {showGapCI gap}", s!"same answer on {agree} of {mU.size}"]])
  o.put "unresolved" "items" s!"{open_.size} of {n}"
  o.put "unresolved" "model.accuracy_bp" (toString (accM all))
  o.put "unresolved" "model.accuracy_ci_bp" s!"{ciM.1} {ciM.2}"
  o.put "unresolved" "model.correct_by_label" (byLabel mU)
  o.put "unresolved" "rule.accuracy_bp" (toString (accR all))
  o.put "unresolved" "rule.accuracy_ci_bp" s!"{ciR.1} {ciR.2}"
  o.put "unresolved" "rule.correct_by_label" (byLabel rU)
  o.put "unresolved" "model_minus_rule_bp" s!"{accM all - accR all} [{gap.1} {gap.2}]"
  o.put "unresolved" "same_answer" s!"{agree} of {mU.size}"
  -- The defer threshold of `certSection`, chosen on the same validation draws.
  let vrows := ((spec.sampleN 600 (Rng.seeded validationSeed)).1.map (certPredOf rc mc · xFam)).toArray
  let τ := chooseThreshold vrows deferTargetBp
  let keptIdx := (Array.range open_.size).filter fun i => mU[i]!.conf ≥ τ
  let mK := pick mU keptIdx
  let rK := pick rU keptIdx
  IO.println s!"Above the defer threshold τ = {τ}/256 the model answers {mK.size} of the {open_.size} at {showPct (accuracyBp mK)}; the rule is right on {showPct (accuracyBp rK)} of those same items ({byLabel rK}).\n"
  o.put "unresolved" "defer_threshold_raw" (toString τ)
  o.put "unresolved" "model_above_threshold" s!"{mK.size}, accuracy_bp {accuracyBp mK}"
  o.put "unresolved" "rule_on_model_above_threshold_accuracy_bp" (toString (accuracyBp rK))
  -- The pipelines, all with the same certificates.
  let correctOf := fun (ps : Array Pred) => countIf ps (·.correct)
  let solverCorrect := countIf ((solver.zip labels.toArray).filterMap fun (a, t) => a.map (·.withTarget t)) (·.correct)
  let deferred := countIf mU fun p => p.conf < τ
  let deferCorrect := solverCorrect + countIf mK (·.correct)
  let pipes : List (String × Nat × Nat × Nat) :=
    [("solver alone (uncertified items left undecided)", sNs, certified, solverCorrect),
     ("solver + outer-form rule", rNs, n, correctOf ruleP),
     ("solver + model", mNs, n, correctOf modelP),
     (s!"solver + model, deferring below τ = {τ}/256", mNs, n - deferred, deferCorrect)]
  IO.println s!"All {n} evaluation items, single thread. Checked decisions are certified ones (`certify_sound`); the rule and the model add none, so they add answers, not checked decisions. Answered and correct count every answer given.\n"
  IO.println (table ["pipeline", "µs per item", "checked", "answered", "correct", "accuracy", "checked / s", "answered / s", "correct / s", "correct beyond the solver / s"]
    (pipes.map fun (name, ns, answered, correct) =>
      [name, toString (ns / 1000 / max n 1), toString certified, toString answered, toString correct,
       showPct (bp correct n), toString (perSecond certified ns), toString (perSecond answered ns),
       toString (perSecond correct ns), toString (perSecond (correct - solverCorrect) ns)]))
  for (name, ns, answered, correct) in pipes do
    o.put "pipeline" name s!"checked {certified}, answered {answered}, correct {correct} of {n}"
    o.time s!"{name}.ns_per_item" (toString (ns / max n 1))
    o.time s!"{name}.checked_per_s" (toString (perSecond certified ns))
    o.time s!"{name}.correct_per_s" (toString (perSecond correct ns))
  o.put "integrity" "timed answers joined with labels equal `certPredOf`" (passFail joinedOk)
  o.put "integrity" "certified flags equal the solver's" (passFail flagsOk)
  IO.println s!"Timed answers joined with reference labels equal `certPredOf`: {passFail joinedOk}; certified flags equal the solver's: {passFail flagsOk}.\n"
  let path := benchDir / "bench-typed-xhard-unresolved.tsv"
  IO.FS.writeFile path ("\n".intercalate (← o.rows.get).toList ++ "\n")
  let clockPath := benchDir / "bench-typed-xhard-unresolved.clock.tsv"
  IO.FS.writeFile clockPath ("\n".intercalate (← o.clock.get).toList ++ "\n")
  IO.println s!"Results: {path} ({(← o.rows.get).size} rows), BLAKE3 {IxAI.blake3 (← IO.FS.readBinFile path)}"
  IO.println s!"Wall clock: {clockPath}"

def runXhard : IO UInt32 := do
  let o ← Out.new
  let t0 ← IO.monoMsNow
  let n := xGen.atoms
  IO.println "# IxBench M2b — Tseitin parity formulas (`prop-xhard`)\n"
  IO.println s!"A connected 3-regular graph on {xGen.verts} vertices, edge i = atom x(i+1) ({n} atoms), with a parity constraint per vertex as four 3-clauses; unsatisfiable when the charges have odd parity (`Tseitin.not_sat`). Satisfiable instances are traps (odd charges, the one clause the drawn assignment falsifies removed) or even. Up to {xGen.extras} extra planted clauses; CNF or De Morgan dual. Labels by `fastStatus` (`fastStatus_eq`). Evaluation seed {evalSeed}, validation seed {validationSeed}, bootstrap {boot.resamples} resamples, seed {boot.seed}.\n"
  o.put "meta" "eval_seed" (toString evalSeed)
  o.put "meta" "xhard_gen" ((repr xGen).pretty 10000)
  -- The generator's claims, on the validation and evaluation draws.
  let vx := (drawX xGen 600 (Rng.seeded validationSeed)).1
  let ex := (drawX xGen evalN (Rng.seeded evalSeed)).1
  let mut grows : Array (List String) := #[]
  for (name, xs) in [("validation", vx), ("evaluation (before `fresh`)", ex)] do
    let passed := (xs.filter (·.check n)).length
    let agree := (xs.filter fun x => x.claim == fastStatus n x.form).length
    let kinds := ["unsatisfiable core", "trap", "even"].map fun k => s!"{k} {(xs.filter (kindOf · == k)).length}"
    grows := grows.push [name, toString xs.length, s!"{passed}", s!"{agree}", ", ".intercalate kinds]
    o.put "generator" s!"{name}.check_passed" s!"{passed}/{xs.length}"
    o.put "generator" s!"{name}.claim_eq_fastStatus" s!"{agree}/{xs.length}"
  IO.println "### Label guarantee\n"
  IO.println "`XInst.check` verifies each draw by evaluation (every clause of an odd, well-formed Tseitin formula subsumed by a clause of the core, or a witness and a falsifiable clause); `XInst.check_sound` proves a checked draw's claimed status is its `status`.\n"
  IO.println (table ["draws", "n", "check passed", "claim = fastStatus", "construction"] grows.toList)
  -- DPLL cost and the refutation search by budget, on validation cores.
  let unsat := (vx.filter (kindOf · == "unsatisfiable core")).map (·.form.core)
  let traps := (vx.filter (kindOf · == "trap")).map (·.form.core)
  let evens := (vx.filter (kindOf · == "even")).map (·.form.core)
  let nU := unsat.map dpllNodes
  let nT := traps.map dpllNodes
  let nE := evens.map dpllNodes
  let nodeRow := fun (name : String) (ns : List Nat) =>
    [name, toString ns.length, toString (ns.foldl min 1000000000), toString (median ns), toString (ns.foldl max 0)]
  IO.println "### DPLL and the refutation search (validation draws)\n"
  IO.println (table ["core", "n", "DPLL nodes min", "median", "max"]
    [nodeRow "unsatisfiable" nU, nodeRow "trap" nT, nodeRow "even" nE])
  for (name, ns) in [("unsat", nU), ("trap", nT), ("even", nE)] do
    o.put "dpll_nodes" name s!"{ns.foldl min 1000000000} {median ns} {ns.foldl max 0}"
  let mut hrows : Array (List String) := #[]
  for rc in xBudgets do
    let (uNs, refuted) ← timeResult unsat (fun fs => fs.map (refuteCore n rc)) (fun rs => rs.foldl (· + ·.2) 0)
    let hits := (refuted.filter (·.1)).length
    let wrong := ((traps ++ evens).filter fun F => (refuteCore n rc F).1).length
    hrows := hrows.push [toString rc.budget, toString rc.depth, s!"{hits}/{unsat.length}",
      showPct (bp hits unsat.length), toString wrong, s!"{uNs / 1000 / max unsat.length 1}"]
    o.put "refute" s!"budget_{rc.budget}.refuted" s!"{hits}/{unsat.length}"
    o.put "refute" s!"budget_{rc.budget}.satisfiable_refuted" (toString wrong)
    o.time s!"typed_xhard.refute_{rc.budget}_us_per_unsat_core" (toString (uNs / 1000 / max unsat.length 1))
  IO.println (table ["budget (nodes)", "depth", "unsatisfiable cores refuted", "rate", "satisfiable refuted", "µs per unsat core"] hrows.toList)
  let foundT := (traps.filter fun F => modelFound n F && falsifiable n F).length
  let foundE := (evens.filter fun F => modelFound n F && falsifiable n F).length
  IO.println s!"Model found within {4 * n} DPLL nodes: traps {foundT}/{traps.length}, even {foundE}/{evens.length}.\n"
  o.put "model_found" "trap" s!"{foundT}/{traps.length}"
  o.put "model_found" "even" s!"{foundE}/{evens.length}"
  -- The model alone, then certificates + model + defer.
  let (mx, sx) ← familySection o "prop-xhard" s!"Propositional status, Tseitin parity (`prop-xhard`, {n} atoms), no certificates" xSpec logicXhardConfig logicQuestions
  let (mc, sc, crNs) ← certSection o "prop-xhard-cert" LogicGen.refute xFam
  IO.println "### Integrity and cost\n"
  let sizes := sx.test.map (·.size)
  let rows := [
    ["prop-xhard: evaluation instances equal to a training instance (`fresh_disjoint`)", s!"{sx.overlap} of {sx.test.length} ({sx.duplicates} removed of {sx.drawn} drawn)"],
    ["prop-xhard: formula size, min–max (mean) on the evaluation set",
      s!"{sizes.foldl min 100000}–{sizes.foldl max 0} ({sizes.foldl (· + ·) 0 / max sizes.length 1})"],
    ["prop-xhard model: parameters", toString (modelRaw mx).length],
    ["prop-xhard-cert model: parameters", toString (modelRaw mc).length]]
  IO.println (table ["check", "result"] rows)
  for r in rows do
    o.put "integrity" (r.getD 0 "") (r.getD 1 "")
  let (labNs, _) ← timeNs sx.test (fun xs => xs.map (fastStatus n)) (fun ls => (ls.filter (· == .contingent)).length)
  let (dNs, _) ← timeNs sx.test (fun xs => xs.map (answerOf xSpec mx 0)) Answer.checksum
  let (cNs, _) ← timeNs sc.test (fun xs => xs.map (certAnswerOf LogicGen.refute mc · xFam)) Answer.checksum
  let per := fun (ns k : Nat) => ns * 1000 / max k 1
  o.time "typed_xhard.label_ns_per_1000" (toString (per labNs sx.test.length))
  o.time "typed_xhard.decision_ns_per_1000" (toString (per dNs sx.test.length))
  o.time "typed_xhard.cert_decision_ns_per_1000" (toString (per cNs sc.test.length))
  o.time "typed_xhard.cert_train_ns" (toString crNs)
  IO.println "Wall clock (not in the digest; single thread; a decision is the answer, its confidence and whether a certificate gave it, without the reference label):\n"
  IO.println (table ["measurement", "time"]
    [["prop-xhard label (`fastStatus`, DPLL), per 1,000", showMs (per labNs sx.test.length)],
     ["prop-xhard decision (features + model), per 1,000", showMs (per dNs sx.test.length)],
     ["prop-xhard certified decision (certificates, else features + model), per 1,000", showMs (per cNs sc.test.length)],
     ["prop-xhard-cert training", showMs crNs]])
  IO.FS.createDirAll benchDir
  let path := benchDir / "bench-typed-xhard.tsv"
  IO.FS.writeFile path ("\n".intercalate (← o.rows.get).toList ++ "\n")
  let digest := IxAI.blake3 (← IO.FS.readBinFile path)
  let clockPath := benchDir / "bench-typed-xhard.clock.tsv"
  IO.FS.writeFile clockPath ("\n".intercalate (← o.clock.get).toList ++ "\n")
  IO.println s!"Results: {path} ({(← o.rows.get).size} rows), BLAKE3 {digest}"
  IO.println s!"Wall clock: {clockPath}; section {(← IO.monoMsNow) - t0} ms\n"
  unresolvedSection mc sc
  return 0

/-- Validation accuracy (seed `validationSeed`, 600 draws) of the plain model and of the
certificate + model pipeline for a few training seeds; `logicXhardConfig` and
`logicXhardCertConfig` take the best of each. -/
def sweepXhard : IO UInt32 := do
  let vs := (xSpec.sampleN 600 (Rng.seeded validationSeed)).1
  let mut rows : Array (List String) := #[]
  for seed in [2614, 2615, 2616, 2617, 2618] do
    let c := { logicXhardConfig with seed }
    let mx := train xSpec c
    let mc := train (xFam.spec LogicGen.refute) c
    let plain := accuracyBp (vs.map (predOf xSpec mx 0)).toArray
    let cps := (vs.map (certPredOf LogicGen.refute mc · xFam)).toArray
    let cert := accuracyBp (cps.map (·.1))
    let modelOnly := accuracyBp ((cps.filter (!·.2)).map (·.1))
    let row := [toString seed, showPct plain, showPct cert, showPct modelOnly]
    IO.println ("\t".intercalate row)
    rows := rows.push row
  IO.println (table ["seed", "plain model", "certified + model", "model-decided part"] rows.toList)
  return 0

/-! ## Baseline items -/

def xhardNotation : String :=
  s!"Notation: x1, x2, …, x{xGen.atoms} are the {xGen.atoms} propositional atoms. ¬ is negation, ∧ conjunction, ∨ disjunction. Every compound subformula is parenthesized, except that a chain of the same connective ∧ (or ∨) is written without inner parentheses, since both are associative: (x ∧ y ∧ z). ¬ applies to the atom right after it. There are 2^{xGen.atoms} assignments of true/false to the atoms (atoms that do not occur are irrelevant).\n"

def xhardQuestionText : String :=
  s!"Question: is the formula a tautology (true under all 2^{xGen.atoms} assignments), a contradiction (false under all of them), or contingent (true under some, false under others)?\nLabels: tautology | contradiction | contingent"

/-- The `prop-xhard` items for the instances `xs` with the plain model `mx`'s and the
certified-or-`mc` answers. Not inlined, so that the models stay arguments evaluated once rather than
expressions the compiler may copy into the per-item closure. -/
@[noinline] def xhardItemsOf (mx mc : Model) (xs : List PForm) : List Item :=
  logicQuestions.flatMap fun (q, pos, labels) =>
    xs.zipIdx.map fun (f, i) =>
      { id := s!"PX{pad 3 (i + 1)}", kind := "prop-xhard", question := q, labels
        text := s!"  {renderHard f}\n", instance_ := renderHard f, ours := predOf xSpec mx pos f
        cert := some (certPredOf LogicGen.refute mc f xFam).1 }

/-- The first `exportItems` fresh `prop-xhard` instances with both models' answers. -/
def xhardItems : IO (List Item) := do
  let (_, mx) ← timedTrain xSpec logicXhardConfig
  let (_, mc) ← timedTrain (xFam.spec LogicGen.refute) xFam.config
  let xs := (splitOf xSpec logicXhardConfig).test.take exportItems
  return xhardItemsOf mx mc xs

def xhardBatchText (name : String) (b : List Item) : String :=
  let first := b.headD { id := "", kind := "", question := "", labels := [], text := "", instance_ := "", ours := default }
  s!"IxBench v3 baseline batch {name} ({b.length} items)\n\n" ++
  "Answer each item yourself, by reasoning alone: do not write or run code.\n\n" ++
  xhardNotation ++ "\n" ++ xhardQuestionText ++ "\n" ++
  "For every item also give your confidence, an integer from 0 to 100, that your label is correct.\n\nItems:\n" ++
  String.join (b.map fun it => s!"=== {it.id}\n{it.text}") ++
  "\nAnswer format: exactly one line per item and nothing else, in the order above:\n" ++
  "ID<TAB>LABEL<TAB>CONFIDENCE\n" ++
  s!"LABEL is one of: {", ".intercalate first.labels}. CONFIDENCE is an integer 0-100.\n" ++
  s!"Example line: {first.id}\t{first.labels.headD "?"}\t80\n"

/-- Write the `prop-xhard` batches and key into `dir` and append their rows to its manifest. -/
def exportXhard (dir : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll (dir / "batches")
  IO.FS.createDirAll (dir / "keys")
  IO.FS.createDirAll (dir / "answers")
  let all ← xhardItems
  let mut manifest : Array String := #[]
  for (b, i) in (chunks all).zipIdx do
    let name := s!"prop-xhard-{pad 2 (i + 1)}"
    let path := dir / "batches" / s!"{name}.txt"
    IO.FS.writeFile path (xhardBatchText name b)
    manifest := manifest.push s!"{name}\tprop-xhard\t{b.length}\t{IxAI.blake3 (← IO.FS.readBinFile path)}"
  let kpath := dir / "keys" / "xhard.tsv"
  IO.FS.writeFile kpath ("id\tquestion\tinstance\tanswer\n" ++
    String.join (all.map fun it => s!"{it.id}\t{it.question}\t{it.instance_}\t{it.labels.getD it.ours.target "?"}\n"))
  let mpath := dir / "manifest.tsv"
  let old ← if ← mpath.pathExists then IO.FS.readFile mpath else pure "batch\tkind\titems\tblake3\n"
  let kept := (old.splitOn "\n").filter fun l => !l.isEmpty && !l.startsWith "prop-xhard-"
  IO.FS.writeFile mpath ("\n".intercalate (kept ++ manifest.toList) ++ "\n")
  IO.println s!"wrote {manifest.size} prop-xhard batches ({all.length} items); key {kpath}, BLAKE3 {IxAI.blake3 (← IO.FS.readBinFile kpath)}"
  IO.println s!"manifest {mpath}, BLAKE3 {IxAI.blake3 (← IO.FS.readBinFile mpath)}"
  return 0

def scoreXhard (dir : System.FilePath) : IO UInt32 := do
  scoreWith (← xhardItems) ["prop-xhard"] dir

end IxAIBench.TypedBench
