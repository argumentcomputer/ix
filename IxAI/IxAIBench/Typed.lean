import IxAIBench.Baseline
import IxAICore.Typed
import IxAICore.Dpll

/-!
# IxBench M2b: kernel-decided typed questions

`ixai bench typed` (also run after `ixai bench full`) trains one decision model per family
of `IxAICore.Typed` with the existing `train` and evaluates it on a fresh set: instances drawn from
`evalSeed`, which no training config uses, with exact duplicates of training instances removed
(`fresh`, `fresh_disjoint`). `prop-hard` is also answered by certificate where `certify` gives one
(`certify_sound`) and by a model with a refutation feature elsewhere, with a defer option
(`certSection`). Results go to `.truthmines/bench/bench-typed.tsv` with a BLAKE3, apart
from the v0 results file, whose digest is unchanged.

`ixai bench export DIR` adds the batches `stlc-typechecks-NN`, `stlc-type-NN`, `prop-status-NN` and
`prop-hard-NN` (25 items each, the first `exportItems` instances of each fresh set) next to the v0 batches, the
key `DIR/keys/typed.tsv`, and their manifest rows; `ixai bench score DIR` scores
`DIR/answers/{stlc,prop}-*.txt` against our models on the same items.
-/

namespace IxAIBench.TypedBench

open IxAICore IxAICore.Typed

/- Closed subterms such as `train tSpec typeConfig` would otherwise become module initializers,
run at every start of any executable that links this module, whatever the command. -/
set_option compiler.extract_closed false

/-- The evaluation seed. Training configs draw from `seed`, `seed + 3`, `seed + 7` and
`seed + 1000003` of their own seeds, none of which is this. -/
def evalSeed : Nat := 20261119
def evalN : Nat := 1000
/-- Validation instances for choosing the training config and the defer threshold, drawn from a
seed apart from both the training and the evaluation seeds. -/
def validationSeed : Nat := 31337
def exportItems : Nat := 100

def tSpec : Spec TypeItem := typeSpec TypeGen.default
def lSpec : Spec PForm := logicSpec LogicGen.default
def hSpec : Spec PForm := logicHardSpec LogicGen.hard
/-- Ablations of the hard family's features: the 21 features of `prop-status` only, and all but
the bounded search (`early`, position 24). -/
def hSpecBase : Spec PForm := { hSpec with features := PForm.features LogicGen.hard.atoms, numFeatures := 21 }
def hSpecNoSearch : Spec PForm := { hSpec with features := fun f => (hSpec.features f).set 24 0 }

/-- `prop-hard` with the refutation feature; certified items are answered by `certify`. -/
def cSpec : Spec PForm := logicCertSpec LogicGen.hard LogicGen.refute

/-- Accuracy that the answered validation items must reach when choosing the defer threshold. -/
def deferTargetBp : Nat := 9500

/-- Question name, answer-group position and answer labels in `Finite.all` order. -/
def typeQuestions : List (String × Nat × List String) :=
  [("typechecks", 0, ["no", "yes"]), ("type", 1, ["A", "B", "C", "D", "none"])]

def logicQuestions : List (String × Nat × List String) :=
  [("status", 0, ["contradiction", "contingent", "tautology"])]

def targetOf {σ : Type} (s : Spec σ) (pos : Nat) (x : σ) : Nat :=
  match (s.slots.drop pos).head? with
  | some q => q.target x
  | none => 0

/-- What a deployed decision returns, computed without the reference label: the answer's index,
its probability (raw `Fx`, 256 for a certified answer), and whether a certificate gave it. -/
structure Answer where
  pred : Nat
  conf : Int
  certified : Bool := false

/-- The answer scored against a reference label computed separately. -/
def Answer.withTarget (a : Answer) (target : Nat) : Pred := { target, pred := some a.pred, conf := a.conf }

/-- A checksum over answers, read under a timer so that every answer is computed there. -/
def Answer.checksum (as : List Answer) : Nat :=
  as.foldl (fun acc a => acc + a.pred + a.conf.natAbs + (if a.certified then 1 else 0)) 0

/-- The model's answer to question `pos`: features, forward pass and probabilities only. -/
def answerOf {σ : Type} (s : Spec σ) (m : Model) (pos : Nat) (x : σ) : Answer :=
  let group := getD (splitByArity s.slots (m.outputs (s.inputs x))) pos []
  let pred := argmax group
  { pred, conf := (getD (probabilities group) pred Fx.zero).raw }

def predOf {σ : Type} (s : Spec σ) (m : Model) (pos : Nat) (x : σ) : Pred :=
  (answerOf s m pos x).withTarget (targetOf s pos x)

/-- A propositional family answered with certificates: its name, report heading, atoms, the spec
with the refutation feature, and its training config. -/
structure CertFam where
  name : String
  heading : String
  atoms : Nat
  spec : RefuteCfg → Spec PForm
  config : Config

def hardFam : CertFam :=
  { name := "prop-hard", heading := "Propositional status, hard", atoms := LogicGen.hard.atoms
    spec := logicCertSpec LogicGen.hard, config := logicHardConfig }

/-- The certified answer when `certify` gives one (probability 1, by `certify_sound`), otherwise
the model's; the flag marks a certified answer. -/
def certAnswerOf (rc : RefuteCfg) (m : Model) (f : PForm) (fam : CertFam := hardFam) : Answer :=
  match certify fam.atoms rc f with
  | some s => { pred := Finite.index s, conf := 256, certified := true }
  | none => answerOf (fam.spec rc) m 0 f

/-- `certAnswerOf` scored against the reference label. -/
def certPredOf (rc : RefuteCfg) (m : Model) (f : PForm) (fam : CertFam := hardFam) : Pred × Bool :=
  let a := certAnswerOf rc m f fam
  (a.withTarget (targetOf (fam.spec rc) 0 f), a.certified)

/-- The items answered at threshold `τ`: certified ones, and model answers of confidence `≥ τ`. -/
def answeredAt (rows : Array (Pred × Bool)) (τ : Int) : Array Pred :=
  (rows.filter fun (p, c) => c || p.conf ≥ τ).map (·.1)

/-- The least threshold in `0…257` (257 defers every model answer) at which the answered items reach
`target` accuracy. -/
def chooseThreshold (rows : Array (Pred × Bool)) (target : Nat) : Int :=
  (((List.range 257).map Int.ofNat).find? fun τ => accuracyBp (answeredAt rows τ) ≥ target).getD 257

/-- Accuracy on the first `cov`% of the items, certified ones first, then by model confidence
(ties in input order). -/
def certAccuracyAtCoverage (rows : Array (Pred × Bool)) (cov : Nat) : Nat × Nat :=
  let cert := (rows.filter (·.2)).map (·.1)
  let model := ((rows.filter (!·.2)).map (·.1)).zipIdx.qsort fun (a, i) (b, j) =>
    a.conf > b.conf || (a.conf == b.conf && i < j)
  let ranked := cert ++ model.map (·.1)
  let k := (rows.size * cov + 99) / 100
  (accuracyBp (ranked.extract 0 k), k)

/-- A family's training instances and its fresh evaluation set. -/
structure Split (σ : Type) where
  train : List σ
  drawn : Nat
  duplicates : Nat
  test : List σ
  /-- Evaluation instances equal to a training instance after filtering; 0 by `fresh_disjoint`. -/
  overlap : Nat

/-- The split by its definition: `fresh`, and the duplicates and the overlap counted by separate
passes over the training set. -/
def splitOfSpec {σ : Type} [DecidableEq σ] (s : Spec σ) (c : Config) : Split σ :=
  let tr := c.data s
  let drawn := (s.sampleN evalN (Rng.seeded evalSeed)).1
  let test := fresh s tr evalSeed evalN
  { train := tr, drawn := drawn.length, duplicates := (drawn.filter (tr.contains ·)).length, test
    overlap := (test.filter (tr.contains ·)).length }

/-- `splitOfSpec` with one pass of the draws over the training set (`splitOf_eq`): the draws found
in it are the duplicates, the others the evaluation set, whose overlap is 0 (`fresh_disjoint`). -/
def splitOf {σ : Type} [DecidableEq σ] (s : Spec σ) (c : Config) : Split σ :=
  let tr := c.data s
  let drawn := (s.sampleN evalN (Rng.seeded evalSeed)).1
  let (dups, test) := drawn.partition (tr.contains ·)
  { train := tr, drawn := drawn.length, duplicates := dups.length, test, overlap := 0 }

theorem splitOf_eq {σ : Type} [DecidableEq σ] (s : Spec σ) (c : Config) :
    splitOf s c = splitOfSpec s c := by
  have h0 : ((fresh s (c.data s) evalSeed evalN).filter ((c.data s).contains ·)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro x hx
    simpa using fresh_disjoint s (c.data s) evalSeed evalN x hx
  simp only [splitOf, splitOfSpec, List.partition_eq_filter_filter, h0]
  rfl

/-! ## Report -/

def familySection {σ : Type} [DecidableEq σ] [Inhabited σ] (o : Out) (key title : String) (s : Spec σ)
    (c : Config) (qs : List (String × Nat × List String)) : IO (Model × Split σ) := do
  let m := train s c
  let sp := splitOf s c
  let rs := resamples boot sp.test.length
  IO.println s!"### {title}\n"
  IO.println s!"`train {s.name}`: {c.trainSize} instances (seed {c.seed}), {c.epochs} epochs, batch {c.batch}, hidden {c.hidden}, {s.numFeatures} features, {(modelRaw m).length} parameters. Evaluation: {sp.test.length} fresh instances from seed {evalSeed} ({sp.drawn} drawn, {sp.duplicates} exact duplicates of training instances removed).\n"
  let mut rows : Array (List String) := #[]
  let mut rcRows : Array (List String) := #[]
  for (q, pos, labels) in qs do
    let ps := (sp.test.map (predOf s m pos)).toArray
    let acc := accuracyBp ps
    let ci := bootCI rs fun idx => (accuracyBp (pick ps idx) : Int)
    let maj := majority labels.length (sp.train.map (targetOf s pos))
    let majAcc := bp (countIf ps (·.target == maj)) ps.size
    let f1 := macroF1Bp labels.length ps
    let majF1 := macroF1Bp labels.length (ps.map fun p => { p with pred := some maj })
    let bal := balancedAccBp labels.length ps
    let ece := eceMilli ps
    let dist := labels.zipIdx.map fun (l, k) => s!"{l} {countIf ps (·.target == k)}"
    rows := rows.push [q, toString ps.size, s!"{showPct acc} {showCI ci}", s!"{showPct f1} ({showPct majF1})",
      showPct bal, s!"{showPct majAcc} ({labels.getD maj "?"})", showMilli ece, ", ".intercalate dist]
    o.put key s!"{q}.accuracy_bp" (toString acc)
    o.put key s!"{q}.accuracy_ci_bp" s!"{ci.1} {ci.2}"
    o.put key s!"{q}.macro_f1_bp" (toString f1)
    o.put key s!"{q}.majority_macro_f1_bp" (toString majF1)
    o.put key s!"{q}.balanced_accuracy_bp" (toString bal)
    o.put key s!"{q}.majority_bp" (toString majAcc)
    o.put key s!"{q}.ece_milli" (toString ece)
    o.put key s!"{q}.labels" (", ".intercalate dist)
    let covs := [100, 90, 80, 50].map fun cov => accuracyAtCoverage ps cov
    rcRows := rcRows.push (q :: covs.map fun (a, k) => s!"{showPct a} ({k})")
    for (cov, (a, _)) in [100, 90, 80, 50].zip covs do
      o.put key s!"{q}.accuracy_at_coverage_{cov}_bp" (toString a)
  IO.println (table ["question", "n", "accuracy [95% CI]", "macro-F1 (majority)", "balanced acc.", "majority (train class)", "ECE", "labels"] rows.toList)
  IO.println (table ["question", "100%", "90%", "80%", "50%"] rcRows.toList)
  o.put key "train_config" ((repr c).pretty 10000)
  o.put key "weights_blake3" (toString (IxAI.digestOf "weights" (modelRaw m)))
  o.put key "eval_drawn" (toString sp.drawn)
  o.put key "eval_duplicates_removed" (toString sp.duplicates)
  o.put key "eval_overlap_after_filter" (toString sp.overlap)
  return (m, sp)

/-- `train s c` and its wall time; the checksum read under the clock forces the model there. -/
def timedTrain {σ : Type} [Inhabited σ] (s : Spec σ) (c : Config) : IO (Nat × Model) := do
  let inp ← IO.mkRef c
  let sink ← IO.mkRef 0
  let t0 ← IO.monoNanosNow
  let m := train s (← inp.get)
  sink.set (checksum (modelRaw m))
  let t1 ← IO.monoNanosNow
  return (t1 - t0, m)

/-- `prop-hard` answered by certificate where one fires and by a model trained with the refutation
feature elsewhere, with an option to defer uncertified items below a confidence threshold chosen
on validation draws (seed `validationSeed`). -/
def certSection (o : Out) (key : String) (rc : RefuteCfg) (fam : CertFam := hardFam) :
    IO (Model × Split PForm × Nat) := do
  let spec := fam.spec rc
  let n := fam.atoms
  let c := fam.config
  let labels := ["contradiction", "contingent", "tautology"]
  let (trainNs, m) ← timedTrain spec c
  let sp := splitOf spec c
  let rows := (sp.test.map (certPredOf rc m · fam)).toArray
  let ps := rows.map (·.1)
  let rs := resamples boot ps.size
  IO.println s!"### {fam.heading}, with certificates (refutation budget {rc.budget} nodes)\n"
  IO.println s!"The `{fam.name}` instances and labels. `certify` (`certify_sound`) answers when the refutation search (`Dpll.lookahead`: closure by unit propagation and failed literals, then splitting; depth {rc.depth}, at most {rc.budget} nodes, {rc.rounds} closure passes per node) refutes the CNF core, or the capped DPLL ({4 * n} nodes) finds a model of it; otherwise a model trained like `{fam.name}`'s with the refutation result as feature 27 answers. `train {spec.name}`: {c.trainSize} instances (seed {c.seed}), {spec.numFeatures} features, {(modelRaw m).length} parameters; {sp.test.length} fresh instances from seed {evalSeed}.\n"
  let acc := accuracyBp ps
  let ci := bootCI rs fun idx => (accuracyBp (pick ps idx) : Int)
  let maj := majority labels.length (sp.train.map (targetOf spec 0))
  let majAcc := bp (countIf ps (·.target == maj)) ps.size
  let f1 := macroF1Bp labels.length ps
  let majF1 := macroF1Bp labels.length (ps.map fun p => { p with pred := some maj })
  let bal := balancedAccBp labels.length ps
  let ece := eceMilli ps
  IO.println (table ["question", "n", "accuracy [95% CI]", "macro-F1 (majority)", "balanced acc.", "majority (train class)", "ECE"]
    [["status", toString ps.size, s!"{showPct acc} {showCI ci}", s!"{showPct f1} ({showPct majF1})", showPct bal,
      s!"{showPct majAcc} ({labels.getD maj "?"})", showMilli ece]])
  o.put key "status.accuracy_bp" (toString acc)
  o.put key "status.accuracy_ci_bp" s!"{ci.1} {ci.2}"
  o.put key "status.macro_f1_bp" (toString f1)
  o.put key "status.majority_macro_f1_bp" (toString majF1)
  o.put key "status.balanced_accuracy_bp" (toString bal)
  o.put key "status.majority_bp" (toString majAcc)
  o.put key "status.ece_milli" (toString ece)
  let cert := rows.filter (·.2) |>.map (·.1)
  let model := rows.filter (!·.2) |>.map (·.1)
  let partRow := fun (name : String) (xs : Array Pred) =>
    let r := resamples boot xs.size
    [name, toString xs.size, showPct (bp xs.size ps.size),
     s!"{showPct (accuracyBp xs)} {showCI (bootCI r fun idx => (accuracyBp (pick xs idx) : Int))}",
     ", ".intercalate (labels.zipIdx.map fun (l, k) => s!"{l} {countIf xs (·.target == k)}")]
  IO.println (table ["part", "n", "share", "accuracy [95% CI]", "labels"]
    [partRow "certified (by theorem)" cert, partRow "model-decided" model])
  o.put key "certified" (toString cert.size)
  o.put key "certified_accuracy_bp" (toString (accuracyBp cert))
  o.put key "model_decided_accuracy_bp" (toString (accuracyBp model))
  let hit := fun (k : Nat) => (countIf rows fun (p, c) => c && p.target == k, countIf rows (·.1.target == k))
  let (h0, n0) := hit 0
  let (h1, n1) := hit 1
  let (h2, n2) := hit 2
  IO.println (table ["label", "certificate", "certified"]
    [["contradiction", "refuted (lookahead)", s!"{h0}/{n0}"], ["tautology", "dual refuted (lookahead)", s!"{h2}/{n2}"],
     ["contingent", s!"model within {4 * n} DPLL nodes", s!"{h1}/{n1}"]])
  o.put key "certified_by_label" s!"contradiction {h0}/{n0}, contingent {h1}/{n1}, tautology {h2}/{n2}"
  let vrows := ((spec.sampleN 600 (Rng.seeded validationSeed)).1.map (certPredOf rc m · fam)).toArray
  let τ := chooseThreshold vrows deferTargetBp
  let ans := answeredAt rows τ
  let covCI := bootCI rs fun idx => (bp (answeredAt (pick rows idx) τ).size idx.size : Int)
  let selCI := bootCI rs fun idx => (accuracyBp (answeredAt (pick rows idx) τ) : Int)
  let vans := answeredAt vrows τ
  IO.println s!"Defer: threshold τ = {τ}/256 on model confidence, the least at which answered validation items reach {showPct deferTargetBp} (validation: {showPct (bp vans.size vrows.size)} answered at {showPct (accuracyBp vans)}). On the evaluation set: {showPct (bp ans.size ps.size)} {showCI covCI} answered, accuracy {showPct (accuracyBp ans)} {showCI selCI}; {ps.size - ans.size} deferred.\n"
  o.put key "defer_threshold_raw" (toString τ)
  o.put key "defer_coverage_bp" (toString (bp ans.size ps.size))
  o.put key "defer_coverage_ci_bp" s!"{covCI.1} {covCI.2}"
  o.put key "defer_accuracy_bp" (toString (accuracyBp ans))
  o.put key "defer_accuracy_ci_bp" s!"{selCI.1} {selCI.2}"
  let covs := [100, 95, 90, 80, 70, 50]
  let rc := covs.map fun cov =>
    let (a, k) := certAccuracyAtCoverage rows cov
    let ci := bootCI rs fun idx => ((certAccuracyAtCoverage (pick rows idx) cov).1 : Int)
    (cov, a, k, ci)
  IO.println (table ["coverage", "items", "accuracy [95% CI]"]
    (rc.map fun (cov, a, k, ci) => [s!"{cov}%", toString k, s!"{showPct a} {showCI ci}"]))
  for (cov, a, _, _) in rc do
    o.put key s!"status.accuracy_at_coverage_{cov}_bp" (toString a)
  o.put key "refute_config" ((repr rc).pretty 10000)
  o.put key "train_config" ((repr c).pretty 10000)
  o.put key "weights_blake3" (toString (IxAI.digestOf "weights" (modelRaw m)))
  return (m, sp, trainNs)

/-- The certified `prop-hard` section at smaller refutation budgets, where fewer items are certified
and the model and the defer option decide more of them (not part of the digest). -/
def runCert : IO UInt32 := do
  let o ← Out.new
  for b in [3, 4, 6, LogicGen.refute.budget] do
    let _ ← certSection o s!"prop-hard-cert-{b}" { LogicGen.refute with budget := b }
  return 0

def run : IO UInt32 := do
  let o ← Out.new
  let t0 ← IO.monoMsNow
  IO.println "# IxBench M2b — kernel-decided typed questions\n"
  IO.println s!"Labels are computed by `infer` (`infer_iff`: it decides `HasType`) and `fastStatus`, DPLL on the formula's clauses (`fastStatus_eq`: it equals `status`, which `status_*_iff` relates to evaluation under all assignments). Evaluation sets are drawn from seed {evalSeed}, apart from every training seed; exact duplicates of training instances are removed (`fresh_disjoint`). Bootstrap: {boot.resamples} resamples, seed {boot.seed}. Majority macro-F1 in parentheses.\n"
  o.put "meta" "eval_seed" (toString evalSeed)
  o.put "meta" "type_gen" ((repr TypeGen.default).pretty 10000)
  o.put "meta" "logic_gen" ((repr LogicGen.default).pretty 10000)
  let (mt, st) ← familySection o "stlc" "Simply typed λ-calculus (5 context variables, de Bruijn terms, 4 candidate types)" tSpec typeConfig typeQuestions
  let (ml, sl) ← familySection o "prop" "Propositional status (random 3-CNF, 12 atoms, 52 clauses, or its De Morgan dual)" lSpec logicConfig logicQuestions
  o.put "meta" "logic_hard_gen" ((repr LogicGen.hard).pretty 10000)
  let (mh, sh) ← familySection o "prop-hard" s!"Propositional status, hard (random 3-CNF, {LogicGen.hard.atoms} atoms, {LogicGen.hard.clauses} clauses, or its De Morgan dual)" hSpec logicHardConfig logicQuestions
  let (mc, sc, crNs) ← certSection o "prop-hard-cert" LogicGen.refute
  IO.println "### Integrity and cost\n"
  let tw := modelRaw mt
  let lw := modelRaw ml
  let tDepths := st.test.map (·.term.depth)
  let tSizes := st.test.map (·.term.size)
  let lSizes := sl.test.map (·.size)
  let hSizes := sh.test.map (·.size)
  let hw := modelRaw mh
  let rows := [
    ["stlc: evaluation instances equal to a training instance (`fresh_disjoint`)", s!"{st.overlap} of {st.test.length} ({st.duplicates} removed of {st.drawn} drawn)"],
    ["prop: evaluation instances equal to a training instance (`fresh_disjoint`)", s!"{sl.overlap} of {sl.test.length} ({sl.duplicates} removed of {sl.drawn} drawn)"],
    ["stlc: term size / depth, min–max (mean) on the evaluation set",
      s!"{tSizes.foldl min 1000}–{tSizes.foldl max 0} ({tSizes.foldl (· + ·) 0 / max tSizes.length 1}) / {tDepths.foldl min 1000}–{tDepths.foldl max 0} ({tDepths.foldl (· + ·) 0 / max tDepths.length 1})"],
    ["prop: formula size, min–max (mean) on the evaluation set",
      s!"{lSizes.foldl min 1000}–{lSizes.foldl max 0} ({lSizes.foldl (· + ·) 0 / max lSizes.length 1})"],
    ["prop-hard: evaluation instances equal to a training instance (`fresh_disjoint`)", s!"{sh.overlap} of {sh.test.length} ({sh.duplicates} removed of {sh.drawn} drawn)"],
    ["prop-hard: formula size, min–max (mean) on the evaluation set",
      s!"{hSizes.foldl min 100000}–{hSizes.foldl max 0} ({hSizes.foldl (· + ·) 0 / max hSizes.length 1})"],
    ["stlc model: parameters, weight bytes, canonical encoding bytes", s!"{tw.length}, {widthBytes tw}, {encBytes tw}"],
    ["prop model: parameters, weight bytes, canonical encoding bytes", s!"{lw.length}, {widthBytes lw}, {encBytes lw}"],
    ["prop-hard model: parameters, weight bytes, canonical encoding bytes", s!"{hw.length}, {widthBytes hw}, {encBytes hw}"]]
  IO.println (table ["check", "result"] rows)
  for r in rows do
    o.put "integrity" (r.getD 0 "") (r.getD 1 "")
  let (tNs, _) ← timeNs st.test (fun xs => xs.map (answerOf tSpec mt 1)) Answer.checksum
  let (lNs, _) ← timeNs sl.test (fun xs => xs.map (answerOf lSpec ml 0)) Answer.checksum
  let (trNs, _) ← timeNs typeConfig (fun c => train tSpec c) (fun m => checksum (modelRaw m))
  let (lrNs, _) ← timeNs logicConfig (fun c => train lSpec c) (fun m => checksum (modelRaw m))
  let (hNs, _) ← timeNs sh.test (fun xs => xs.map (answerOf hSpec mh 0)) Answer.checksum
  let (hrNs, _) ← timeNs logicHardConfig (fun c => train hSpec c) (fun m => checksum (modelRaw m))
  let (labNs, _) ← timeNs sh.test (fun xs => xs.map (fastStatus LogicGen.hard.atoms)) (fun ls => (ls.filter (· == .contingent)).length)
  let (cNs, _) ← timeNs sc.test (fun xs => xs.map (certAnswerOf LogicGen.refute mc ·)) Answer.checksum
  let (rfNs, _) ← timeNs sc.test (fun xs => xs.map fun f => (refuteCore LogicGen.hard.atoms LogicGen.refute f.core).2)
    (fun ls => ls.foldl (· + ·) 0)
  let per := fun (ns n : Nat) => ns * 1000 / max n 1
  o.time "typed.stlc_decision_ns_per_1000" (toString (per tNs st.test.length))
  o.time "typed.prop_decision_ns_per_1000" (toString (per lNs sl.test.length))
  o.time "typed.stlc_train_ns" (toString trNs)
  o.time "typed.prop_train_ns" (toString lrNs)
  o.time "typed.prop_hard_decision_ns_per_1000" (toString (per hNs sh.test.length))
  o.time "typed.prop_hard_train_ns" (toString hrNs)
  o.time "typed.prop_hard_label_ns_per_1000" (toString (per labNs sh.test.length))
  o.time "typed.prop_hard_cert_decision_ns_per_1000" (toString (per cNs sc.test.length))
  o.time "typed.prop_hard_cert_train_ns" (toString crNs)
  o.time "typed.prop_hard_refute_ns_per_1000" (toString (per rfNs sc.test.length))
  IO.println "Wall clock (not in the digest; single thread; a decision is the answer and its confidence, without the reference label; includes featurisation, which for `prop` evaluates 8 probe assignments):\n"
  IO.println (table ["measurement", "time"]
    [["stlc decision (features + model + probabilities), per 1,000", showMs (per tNs st.test.length)],
     ["prop decision (features + model + probabilities), per 1,000", showMs (per lNs sl.test.length)],
     ["prop-hard decision (features + model + probabilities), per 1,000", showMs (per hNs sh.test.length)],
     ["prop-hard label (`fastStatus`, DPLL), per 1,000", showMs (per labNs sh.test.length)],
     ["prop-hard certified decision (certificates, else features + model), per 1,000", showMs (per cNs sc.test.length)],
     ["prop-hard refutation search alone (`refuteCore`), per 1,000", showMs (per rfNs sc.test.length)],
     ["stlc training", showMs trNs], ["prop training", showMs lrNs], ["prop-hard training (sampling, labels, features, SGD)", showMs hrNs],
     ["prop-hard-cert training", showMs crNs]])
  IO.FS.createDirAll benchDir
  let path := benchDir / "bench-typed.tsv"
  IO.FS.writeFile path ("\n".intercalate (← o.rows.get).toList ++ "\n")
  let digest := IxAI.blake3 (← IO.FS.readBinFile path)
  let clockPath := benchDir / "bench-typed.clock.tsv"
  IO.FS.writeFile clockPath ("\n".intercalate (← o.clock.get).toList ++ "\n")
  IO.println s!"Results: {path} ({(← o.rows.get).size} rows), BLAKE3 {digest}"
  IO.println s!"Wall clock: {clockPath}; typed section {(← IO.monoMsNow) - t0} ms"
  return 0

/-- Validation accuracy of each question for a grid of batch sizes, learning rates, epoch counts,
hidden sizes and training-set sizes. -/
def sweep : IO UInt32 := do
  let tv := (tSpec.sampleN 600 (Rng.seeded validationSeed)).1
  let lv := (lSpec.sampleN 600 (Rng.seeded validationSeed)).1
  let hv := (hSpec.sampleN 600 (Rng.seeded validationSeed)).1
  let acc := fun {σ : Type} (s : Spec σ) (m : Model) (pos : Nat) (xs : List σ) =>
    showPct (accuracyBp (xs.map (predOf s m pos)).toArray)
  let mut rows : Array (List String) := #[]
  for (batch, lr, ep, hidden, n) in ([(100, 1, 30, 16, 2000), (100, 1, 20, 16, 2000), (100, 2, 20, 16, 2000),
      (50, 1, 10, 16, 2000), (100, 1, 30, 32, 2000)] : List (Nat × Int × Nat × Nat × Nat)) do
      let tc := { typeConfig with lrRaw := lr, epochs := ep, batch, hidden, trainSize := n }
      let lc := { logicConfig with lrRaw := lr, epochs := ep, batch, hidden, trainSize := n }
      let mt := train tSpec tc
      let ml := train lSpec lc
      let hc := { logicHardConfig with lrRaw := lr, epochs := ep, batch, hidden, trainSize := n }
      let mh := train hSpec hc
      let mb := train hSpecBase hc
      let mn := train hSpecNoSearch hc
      let row := [toString batch, toString lr, toString ep, toString hidden, toString n, acc tSpec mt 0 tv, acc tSpec mt 1 tv, acc lSpec ml 0 lv, acc hSpec mh 0 hv, acc hSpecBase mb 0 hv, acc hSpecNoSearch mn 0 hv]
      IO.println ("\t".intercalate row)
      rows := rows.push row
  IO.println (table ["batch", "lrRaw", "epochs", "hidden", "train size", "typechecks", "type", "status", "hard status", "hard, 21 features", "hard, no search"] rows.toList)
  return 0

/-- How often each refutation search certifies an unsatisfiable core among validation draws of
`prop-hard`, with the nodes it used and its time; and how often the capped model search certifies a
satisfiable one. -/
def refuteStats (cfgs : List RefuteCfg) (s : Spec PForm := hSpec) (n : Nat := LogicGen.hard.atoms) :
    IO UInt32 := do
  let xs := (s.sampleN 600 (Rng.seeded validationSeed)).1
  let labelled := xs.map fun f => (f, fastStatus n f)
  let unsat := (labelled.filter (·.2 != .contingent)).map (·.1.core)
  let sats := (labelled.filter (·.2 == .contingent)).map (·.1.core)
  let (mNs, found) ← timeNs sats (fun fs => fs.map fun F => modelFound n F && falsifiable n F)
    (fun bs => (bs.filter id).length)
  IO.println s!"{sats.length} satisfiable cores: model found within {4 * n} nodes for {found} ({mNs / 1000 / max sats.length 1} µs each)"
  let mut rows : Array (List String) := #[]
  for c in cfgs do
    let (uNs, _) ← timeNs unsat (fun fs => fs.map (refuteCore n c)) (fun rs => rs.foldl (· + ·.2) 0)
    let rs := unsat.map (refuteCore n c)
    let hits := rs.filter (·.1)
    let (sNs, wrong) ← timeNs sats (fun fs => fs.map (refuteCore n c)) (fun rs => (rs.filter (·.1)).length)
    let used := hits.map fun r => c.budget - r.2
    let row := [toString c.rounds, toString c.depth, toString c.budget, toString c.look,
      s!"{hits.length}/{unsat.length}", toString ((used.filter (· ≤ 1)).length),
      toString (used.foldl (· + ·) 0 / max hits.length 1), toString wrong,
      s!"{uNs / 1000 / max unsat.length 1}", s!"{sNs / 1000 / max sats.length 1}"]
    IO.println ("\t".intercalate row)
    rows := rows.push row
  IO.println (table ["rounds", "depth", "budget", "lookahead pick", "refuted", "at the root", "mean nodes (refuted)", "satisfiable refuted", "µs per unsat core", "µs per sat core"] rows.toList)
  return 0

def refuteSweep : List RefuteCfg :=
  [{ rounds := 3, depth := 1, budget := 1, look := false }] ++
  ([2, 3, 4, 6, 8, 12, 16].flatMap fun b =>
    [false, true].map fun look => { rounds := 3, depth := 6, budget := b, look }) ++
  [{ rounds := 1, depth := 6, budget := 16, look := false }, { rounds := 2, depth := 6, budget := 16, look := false },
   { rounds := 1, depth := 6, budget := 16, look := true }]

/-! ## Rendering -/

def renderTy (paren : Bool) : Ty → String
  | .nat => "N"
  | .bool => "B"
  | .arr a b => wrapIf paren s!"{renderTy true a} → {renderTy false b}"

/-- Precedence levels: 0 anywhere, 1 function position of an application, 2 argument. -/
def renderTm (lvl : Nat) : Term → String
  | .var i => s!"#{i}"
  | .zero => "0"
  | .tt => "true"
  | .ff => "false"
  | .lam a t => wrapIf (lvl > 0) s!"λ[{renderTy false a}]. {renderTm 0 t}"
  | .app f x => wrapIf (lvl > 1) s!"{renderTm 1 f} {renderTm 2 x}"
  | .succ t => wrapIf (lvl > 0) s!"succ {renderTm 2 t}"
  | .isZero t => wrapIf (lvl > 0) s!"iszero {renderTm 2 t}"
  | .ite c t e => wrapIf (lvl > 0) s!"if {renderTm 0 c} then {renderTm 0 t} else {renderTm 0 e}"

def renderCtx (ctx : List Ty) : String :=
  ", ".intercalate ((withIndex ctx 0).map fun (a, i) => s!"#{i} : {renderTy false a}")

def atomLetter (i : Nat) : String := (String.singleton (Char.ofNat (97 + i)))

/-- A formula; `parent` is 2 inside a `∧` and 3 inside a `∨`, where a chain of the same
connective is written without inner parentheses. -/
def renderFWith (name : Nat → String) (parent : Nat) : PForm → String
  | .atom i => name i
  | .neg a => "¬" ++ renderFWith name 0 a
  | .and a b =>
    let s := s!"{renderFWith name 2 a} ∧ {renderFWith name 2 b}"; if parent == 2 then s else s!"({s})"
  | .or a b =>
    let s := s!"{renderFWith name 3 a} ∨ {renderFWith name 3 b}"; if parent == 3 then s else s!"({s})"
  | .imp a b => s!"({renderFWith name 0 a} → {renderFWith name 0 b})"
  | .iff a b => s!"({renderFWith name 0 a} ↔ {renderFWith name 0 b})"

def renderF : Nat → PForm → String := renderFWith atomLetter

/-- Atoms of the hard family are `x1`, `x2`, …: there are more of them than letters. -/
def renderHard : PForm → String := renderFWith (fun i => s!"x{i + 1}") 0

def stlcNotation : String :=
  "Notation (simply typed λ-calculus with de Bruijn indices):\n" ++
  "- Types: N (natural numbers), B (booleans), S → T (functions). → associates to the right: N → B → N means N → (B → N).\n" ++
  "- Variables are written #k (de Bruijn index). Under k enclosing λs, #0 … #(k−1) are those λs' variables, #0 the innermost; #(k+j) is context entry #j. At the top level #j is context entry #j.\n" ++
  "- λ[S]. t is a function whose variable has type S; its body t extends as far right as possible. Application is juxtaposition and associates to the left: f x y means (f x) y.\n" ++
  "Typing rules (the only ones; no subtyping, polymorphism, coercion or inference of annotations):\n" ++
  "- #k has the type of the variable it refers to.\n" ++
  "- λ[S]. t has type S → T if t has type T when #0 has type S (every other index shifts up by one inside the body).\n" ++
  "- f x has type T if f has type S → T and x has type S, for the same S.\n" ++
  "- succ and iszero take one argument, written right after them; when such a term is itself applied or used as an argument it is parenthesized.\n" ++
  "- 0 : N. succ t : N if t : N. true : B. false : B. iszero t : B if t : N.\n" ++
  "- if c then t else e has type T if c : B, t : T and e : T.\n" ++
  "A term has a type only if every subterm satisfies its rule; a well-typed term has exactly one type.\n"

def propNotation : String :=
  "Notation: a, b, c, d, e, f, g, h, i, j, k, l are the 12 propositional atoms. ¬ is negation, ∧ conjunction, ∨ disjunction, → material implication (false only when the left side is true and the right side false), ↔ equivalence. Every compound subformula is parenthesized, except that a chain of the same connective ∧ (or ∨) is written without inner parentheses, since both are associative: (x ∧ y ∧ z). ¬ applies to the atom or parenthesized formula right after it. There are 2^12 = 4096 assignments of true/false to the atoms (atoms that do not occur are irrelevant).\n"

def hardNotation : String :=
  s!"Notation: x1, x2, …, x{LogicGen.hard.atoms} are the {LogicGen.hard.atoms} propositional atoms. ¬ is negation, ∧ conjunction, ∨ disjunction. Every compound subformula is parenthesized, except that a chain of the same connective ∧ (or ∨) is written without inner parentheses, since both are associative: (x ∧ y ∧ z). ¬ applies to the atom right after it. There are 2^{LogicGen.hard.atoms} assignments of true/false to the atoms (atoms that do not occur are irrelevant).\n"

def hardQuestionText : String :=
  s!"Question: is the formula a tautology (true under all 2^{LogicGen.hard.atoms} assignments), a contradiction (false under all of them), or contingent (true under some, false under others)?\nLabels: tautology | contradiction | contingent"

def questionText : String → String
  | "typechecks" => "Question: does the term have a type in the given context?\nLabels: yes | no"
  | "type" => "Question: which candidate is the term's type in the given context?\nLabels: A | B | C | D | none (the term has no type, or its type is none of the four)"
  | _ => "Question: is the formula a tautology (true under all 4096 assignments), a contradiction (false under all of them), or contingent (true under some, false under others)?\nLabels: tautology | contradiction | contingent"

/-! ## Baseline items -/

structure Item where
  id : String
  /-- The batch kind: `stlc-typechecks`, `stlc-type`, `prop-status` or `prop-hard`. -/
  kind : String
  question : String
  labels : List String
  text : String
  instance_ : String
  ours : Pred
  /-- For `prop-hard`: the certified-or-model answer (`certPredOf`). -/
  cert : Option Pred := none

def typeText (q : String) (it : TypeItem) : String :=
  s!"  context: {renderCtx it.ctx}\n  term: {renderTm 0 it.term}\n" ++
  (if q == "type" then
    String.join ((List.range 4).map fun k => s!"  {["A", "B", "C", "D"].getD k "?"}: {renderTy false (it.cand k)}\n")
  else "")

/-- The baseline items with our model's answers, a pure function of the specs and configs.
A function of `Unit`, so the four trainings run when called rather than at program start. -/
def items (_ : Unit) : List Item :=
  let mt := train tSpec typeConfig
  let ml := train lSpec logicConfig
  let ts := (splitOf tSpec typeConfig).test.take exportItems
  let ls := (splitOf lSpec logicConfig).test.take exportItems
  let mh := train hSpec logicHardConfig
  let hs := (splitOf hSpec logicHardConfig).test.take exportItems
  let mc := train cSpec logicHardConfig
  let tItems := typeQuestions.flatMap fun (q, pos, labels) =>
    ts.zipIdx.map fun (it, i) =>
      { id := s!"{if q == "type" then "TY" else "TC"}{pad 3 (i + 1)}", kind := s!"stlc-{q}", question := q, labels
        text := typeText q it
        instance_ := s!"{renderCtx it.ctx} ⊢ {renderTm 0 it.term}" ++
          (if q == "type" then s!" ? {" | ".intercalate ((List.range 4).map fun k => renderTy false (it.cand k))}" else "")
        ours := predOf tSpec mt pos it }
  let lItems := logicQuestions.flatMap fun (q, pos, labels) =>
    ls.zipIdx.map fun (f, i) =>
      { id := s!"PS{pad 3 (i + 1)}", kind := s!"prop-{q}", question := q, labels
        text := s!"  {renderF 0 f}\n", instance_ := renderF 0 f, ours := predOf lSpec ml pos f }
  let hItems := logicQuestions.flatMap fun (q, pos, labels) =>
    hs.zipIdx.map fun (f, i) =>
      { id := s!"PH{pad 3 (i + 1)}", kind := "prop-hard", question := q, labels
        text := s!"  {renderHard f}\n", instance_ := renderHard f, ours := predOf hSpec mh pos f
        cert := some (certPredOf LogicGen.refute mc f).1 }
  tItems ++ lItems ++ hItems

def kinds : List String := ["stlc-typechecks", "stlc-type", "prop-status", "prop-hard"]

def batchText (name : String) (b : List Item) : String :=
  let first := b.headD { id := "", kind := "", question := "", labels := [], text := "", instance_ := "", ours := default }
  let hard := first.kind == "prop-hard"
  let notes := if first.kind.startsWith "stlc" then stlcNotation else if hard then hardNotation else propNotation
  s!"IxBench v1 baseline batch {name} ({b.length} items)\n\n" ++
  "Answer each item yourself, by reasoning alone: do not write or run code.\n\n" ++
  notes ++ "\n" ++ (if hard then hardQuestionText else questionText first.question) ++ "\n" ++
  "For every item also give your confidence, an integer from 0 to 100, that your label is correct.\n\nItems:\n" ++
  String.join (b.map fun it => s!"=== {it.id}\n{it.text}") ++
  "\nAnswer format: exactly one line per item and nothing else, in the order above:\n" ++
  "ID<TAB>LABEL<TAB>CONFIDENCE\n" ++
  s!"LABEL is one of: {", ".intercalate first.labels}. CONFIDENCE is an integer 0-100.\n" ++
  s!"Example line: {first.id}\t{first.labels.headD "?"}\t80\n"

/-- Write the typed batches and key into `dir` and append their rows to its manifest. -/
def exportTo (dir : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll (dir / "batches")
  IO.FS.createDirAll (dir / "keys")
  IO.FS.createDirAll (dir / "answers")
  let all := items ()
  let mut manifest : Array String := #[]
  for k in kinds do
    for (b, i) in (chunks (all.filter (·.kind == k))).zipIdx do
      let name := s!"{k}-{pad 2 (i + 1)}"
      let path := dir / "batches" / s!"{name}.txt"
      IO.FS.writeFile path (batchText name b)
      manifest := manifest.push s!"{name}\t{k}\t{b.length}\t{IxAI.blake3 (← IO.FS.readBinFile path)}"
  IO.FS.writeFile (dir / "keys" / "typed.tsv") ("id\tquestion\tinstance\tanswer\n" ++
    String.join (all.map fun it => s!"{it.id}\t{it.question}\t{it.instance_}\t{it.labels.getD it.ours.target "?"}\n"))
  let mpath := dir / "manifest.tsv"
  let old ← if ← mpath.pathExists then IO.FS.readFile mpath else pure "batch\tkind\titems\tblake3\n"
  IO.FS.writeFile mpath (old ++ "\n".intercalate manifest.toList ++ "\n")
  IO.println s!"wrote {manifest.size} typed batches: {kinds.map fun k => s!"{k} {(chunks (all.filter (·.kind == k))).length}"} ({exportItems} fresh instances per question); key {dir / "keys" / "typed.tsv"}"
  IO.println s!"manifest {mpath}, BLAKE3 {IxAI.blake3 (← IO.FS.readBinFile mpath)}"
  return 0

/-! ## Score -/

/-- Score `dir/answers/K-*.txt` for the batch kinds `kinds` against `all`. -/
def scoreWith (all : List Item) (kinds : List String) (dir : System.FilePath) : IO UInt32 := do
  let ansDir := dir / "answers"
  let files ← if ← ansDir.pathExists then ansDir.readDir else pure #[]
  let files := (files.filter fun f => f.fileName.endsWith ".txt" && kinds.any (f.fileName.startsWith ·)).qsort
    (·.fileName < ·.fileName)
  let texts ← files.toList.mapM fun f => IO.FS.readFile f.path
  let byId : Std.HashMap String Item := all.foldl (fun m it => m.insert it.id it) {}
  let mut answers : Std.HashMap String (Nat × Int) := {}
  let mut lines := 0
  let mut invalid := 0
  let mut dups := 0
  for text in texts do
    for raw in text.splitOn "\n" do
      let l := trimPunct raw.trimAscii.toString
      if l.isEmpty || l.startsWith "```" then continue
      lines := lines + 1
      match tokens l with
      | [id, lab, conf] =>
        match byId.get? id, (conf.replace "%" "").toNat? with
        | some it, some c =>
          match it.labels.findIdx? (·.toLower == lab.toLower) with
          | some k =>
            if c > 100 then invalid := invalid + 1
            else if answers.contains id then dups := dups + 1
            else answers := answers.insert id (k, Int.ofNat (c * 256 / 100))
          | none => invalid := invalid + 1
        | _, _ => invalid := invalid + 1
      | _ => invalid := invalid + 1
  IO.println s!"# IxBench M2b baseline score ({files.size} answer files, {lines} answer lines: {invalid} invalid, {dups} duplicate IDs ignored)\n"
  let mut rows : Array (List String) := #[]
  for k in kinds do
    let its := (all.filter (·.kind == k)).toArray
    let arity := (its[0]?.map (·.labels.length)).getD 0
    let variants := [(k, its.map (·.ours))] ++
      (if its.all (·.cert.isSome) && !its.isEmpty then [(s!"{k}, certified + model", its.map fun it => it.cert.getD it.ours)] else [])
    for (name, ours) in variants do
      let theirs := its.map fun it => match answers.get? it.id with
        | some (p, c) => { target := it.ours.target, pred := some p, conf := c : Pred }
        | none => { target := it.ours.target, pred := none, conf := 0 }
      let answered := countIf theirs (·.pred.isSome)
      let rs := resamples boot its.size
      let accT := fun (idx : Array Nat) => (accuracyBp (pick theirs idx) : Int)
      let accO := fun (idx : Array Nat) => (accuracyBp (pick ours idx) : Int)
      let all := identity its.size
      let maj := majority arity (its.toList.map (·.ours.target))
      rows := rows.push [name, s!"{answered}/{its.size}",
        s!"{showPct (accT all).toNat} {showCI (bootCI rs accT)}", s!"{showPct (accO all).toNat} {showCI (bootCI rs accO)}",
        s!"{showGap (accT all - accO all)} {showGapCI (pairedCI rs accT accO)}",
        s!"{showPct (macroF1Bp arity theirs)} / {showPct (macroF1Bp arity ours)}",
        s!"{showMilli (eceMilli theirs)} / {showMilli (eceMilli ours)}",
        showPct (bp (countIf ours (·.target == maj)) its.size)]
  IO.println (table ["question", "answered", "LLM accuracy [95% CI]", "our model", "gap LLM − ours [95% CI]", "macro-F1 LLM / ours", "ECE LLM / ours", "majority on these items"] rows.toList)
  IO.println "Unanswered or invalid items count as wrong; ECE is over answered items.\n"
  return 0

def score (dir : System.FilePath) : IO UInt32 := scoreWith (items ()) kinds dir

end IxAIBench.TypedBench
