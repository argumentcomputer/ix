import IxAIBench.Stats
import IxAIData.Pipeline
import IxAICore.TriagePolicy

/-!
# IxBench v0: one deterministic report over the verified decision models

`ixai bench [tiny|small|full]` evaluates, for one model size:

1. triage decisions: accuracy, macro-F1, balanced accuracy, a majority-class baseline, a
   risk-coverage table and ECE, on a 1,000-formula held-out set whose prefix is the certified
   card's test set;
2. the RL routing policy against fixed policies and the oracle, and the gamed-reward check;
3. premise selection on both splits of `order-basic`, with bootstrap intervals and the paired gap
   to IDF;
4. triage under distribution shift (deeper formulas);
5. integrity checks;
6. cost.

Every number outside the wall-clock block is an integer computed by a pure function of the
configs, the dataset files and fixed seeds, so the results file is bit-identical across runs.
-/

namespace IxAIBench

open IxAICore IxAIData

/-- The configs of one benchmark size and the integrity checks computed by the caller. -/
structure Setup where
  size : String
  triage : Config
  rlBase : Config
  rl : RLConfig
  /-- Integrity checks the caller computes, as `(check, result)`. -/
  checks : List (String × String)

/-! ## Output -/

/-- The machine-readable rows `section ⟶ key ⟶ value` and the wall-clock rows, kept apart. -/
structure Out where
  rows : IO.Ref (Array String)
  clock : IO.Ref (Array String)

def Out.new : IO Out := return ⟨← IO.mkRef #[], ← IO.mkRef #[]⟩

def Out.put (o : Out) (sec key val : String) : IO Unit := o.rows.modify (·.push s!"{sec}\t{key}\t{val}")

def Out.time (o : Out) (key val : String) : IO Unit := o.clock.modify (·.push s!"{key}\t{val}")

/-- A Markdown table. -/
def table (header : List String) (rows : List (List String)) : String :=
  let line := fun (r : List String) => "| " ++ " | ".intercalate r ++ " |"
  "\n".intercalate ([line header, line (header.map fun _ => "---")] ++ rows.map line) ++ "\n"

def showCI (ci : Int × Int) : String :=
  s!"[{showPct ci.1.toNat}, {showPct ci.2.toNat}]"

def showGapCI (ci : Int × Int) : String := s!"[{showGap ci.1}, {showGap ci.2}]"

def showMrrCI (ci : Int × Int) : String := s!"[{showMicro3 ci.1.toNat}, {showMicro3 ci.2.toNat}]"

def showMrrGapCI (ci : Int × Int) : String := s!"[{showMicroGap ci.1}, {showMicroGap ci.2}]"

/-- `total / n` for a total in units of `1/256`, with three decimals. -/
def perItem (total : Int) (n : Nat) : String :=
  if n == 0 then "n/a" else
  let m := total * 1000 / (256 * n)
  (if m < 0 then "-" else "") ++ showMilli m.natAbs

/-! ## Timing

The input is read from a reference after the first clock read and the result is written to one
before the second, so the measured computation cannot move outside the interval. -/

def timeNs {α β : Type} (input : α) (f : α → β) (force : β → Nat) : IO (Nat × Nat) := do
  let inp ← IO.mkRef input
  let res ← IO.mkRef 0
  let t0 ← IO.monoNanosNow
  let x ← inp.get
  res.set (force (f x))
  let t1 ← IO.monoNanosNow
  return (t1 - t0, ← res.get)

def showMs (ns : Nat) : String := s!"{ns / 1000000}.{pad 1 (ns % 1000000 / 100000)} ms"

def modelRaw (m : Model) : List Int := (m.w1.flatten ++ m.b1 ++ m.w2.flatten ++ m.b2).map (·.raw)

def checksum (xs : List Int) : Nat := (xs.foldl (fun a x => a + x.natAbs) 0)

/-! ## 1. Triage decisions -/

/-- The three triage questions: name, answer-group position, arity and answer labels. -/
def questions : List (String × Nat × List String) :=
  [("valid", 0, ["false", "true"]), ("head", 1, ["P", "Q", "R", "top", "none"]),
   ("coverage", 2, ["never", "rarely", "mostly", "always"])]

def slotTarget (pos : Nat) (f : Formula) : Nat :=
  match (Triage.spec.slots.drop pos).head? with
  | some q => q.target f
  | none => 0

/-- The model's answer to question `pos` for each formula, as `evalQuestion` computes it. -/
def predsOf (m : Model) (pos : Nat) (fs : List Formula) : Array Pred :=
  fs.toArray.map fun f =>
    let group := getD (splitByArity Triage.spec.slots (m.outputs (Triage.spec.inputs f))) pos []
    let pred := argmax group
    { target := slotTarget pos f, pred := some pred, conf := (getD (probabilities group) pred Fx.zero).raw }

def testN : Nat := 1000

def boot : BootConfig := {}

def identity (n : Nat) : Array Nat := Array.range n

def triageSection (o : Out) (st : Setup) (m : Model) : IO Unit := do
  let c := st.triage
  let s := Triage.spec
  let test := { c with testSize := testN }.test s
  let trainFs := c.data s
  let rs := resamples boot test.length
  IO.println s!"## 1. Triage decisions ({st.size}: {c.trainSize} training formulas, {c.epochs} epochs, hidden {c.hidden}; {test.length} held-out formulas)\n"
  let mut rows : Array (List String) := #[]
  let mut rcRows : Array (List String) := #[]
  for (q, pos, labels) in questions do
    let ps := predsOf m pos test
    let acc := accuracyBp ps
    let ci := bootCI rs fun idx => (accuracyBp (pick ps idx) : Int)
    let maj := majority labels.length (trainFs.map (slotTarget pos))
    let majAcc := bp (countIf ps (·.target == maj)) ps.size
    let f1 := macroF1Bp labels.length ps
    let bal := balancedAccBp labels.length ps
    let ece := eceMilli ps
    rows := rows.push [q, toString ps.size, s!"{showPct acc} {showCI ci}", showPct f1, showPct bal,
      s!"{showPct majAcc} ({labels.getD maj "?"})", showMilli ece]
    o.put "triage" s!"{q}.accuracy_bp" (toString acc)
    o.put "triage" s!"{q}.accuracy_ci_bp" s!"{ci.1} {ci.2}"
    o.put "triage" s!"{q}.macro_f1_bp" (toString f1)
    o.put "triage" s!"{q}.balanced_accuracy_bp" (toString bal)
    o.put "triage" s!"{q}.majority_bp" (toString majAcc)
    o.put "triage" s!"{q}.ece_milli" (toString ece)
    let covs := [100, 90, 80, 50].map fun cov => accuracyAtCoverage ps cov
    rcRows := rcRows.push (q :: covs.map fun (a, k) => s!"{showPct a} ({k})")
    for (cov, (a, _)) in [100, 90, 80, 50].zip covs do
      o.put "triage" s!"{q}.accuracy_at_coverage_{cov}_bp" (toString a)
  IO.println (table ["question", "n", "accuracy [95% CI]", "macro-F1", "balanced acc.", "majority (train class)", "ECE"] rows.toList)
  IO.println "Risk-coverage: accuracy on the most confident fraction (by the probability of the predicted answer; items kept in parentheses).\n"
  IO.println (table ["question", "100%", "90%", "80%", "50%"] rcRows.toList)

/-! ## 2. Policy and RL -/

structure PolicyRow where
  name : String
  reward : Int
  attempts : Nat
  refuted : Nat
  missed : Nat
  falsePublished : Nat

def policyRow (name : String) (choose : Formula → Triage.Choice) (fs : List Formula) : PolicyRow :=
  fs.foldl (fun r f =>
    let ch := choose f
    let outcome : Triage.Action := match ch with
      | .attempt => if f.valid then .publish else .refuted
      | .defer => .defer
    { r with reward := r.reward + Triage.reward f ch
             attempts := r.attempts + (if ch == .attempt then 1 else 0)
             refuted := r.refuted + (if outcome == .refuted then 1 else 0)
             missed := r.missed + (if ch == .defer && f.valid then 1 else 0)
             falsePublished := r.falsePublished + (if outcome == .publish && !f.valid then 1 else 0) })
    ⟨name, 0, 0, 0, 0, 0⟩

/-- The threshold at which attempting pays under `Triage.reward`: `P(valid) > 192/512`. -/
def breakEvenRaw : Int := 96

def policySection (o : Out) (st : Setup) (triageModel : Model) : IO (Model × Model) := do
  let s := Triage.policySpec
  let test := st.rlBase.test s
  let m0 := st.rlBase.init s
  let honest := rlTrain s Triage.bandit st.rl m0
  let hacked := rlTrain s Triage.hackedBandit st.rl m0
  let oracle := test.foldl (fun a f => a + Triage.oracleReward f) 0
  let oracleRow := policyRow "oracle" (fun f => if f.valid then .attempt else .defer) test
  let rows := [oracleRow,
    policyRow "RL policy (specified reward)" (Triage.route honest) test,
    policyRow "RL policy (gamed reward)" (Triage.route hacked) test,
    policyRow "initial policy (untrained)" (Triage.route m0) test,
    policyRow "always attempt" (fun _ => .attempt) test,
    policyRow "always defer" (fun _ => .defer) test,
    policyRow "supervised triage model, attempt if P(valid) > 3/8"
      (fun f => if Triage.confidence triageModel f > breakEvenRaw then .attempt else .defer) test]
  let outcomeFalse := (test.filter fun f => Triage.outcome hacked f == .publish && !f.valid).length
  IO.println s!"## 2. Policy / RL ({st.size}: {st.rl.rounds} rounds of {st.rl.batch} contexts; {test.length} held-out formulas)\n"
  IO.println "Reward in units of 1/256 under `Triage.reward` (attempt: +256 valid, −192 invalid; defer: −64 valid, 0 invalid). Regret = oracle − policy.\n"
  IO.println (table ["policy", "total reward", "per formula", "regret", "attempts", "refuted", "missed", "false published"]
    (rows.map fun r => [r.name, toString r.reward, perItem r.reward test.length, toString (oracle - r.reward),
      toString r.attempts, toString r.refuted, toString r.missed, toString r.falsePublished]))
  for r in rows do
    let k := (r.name.splitOn " ").head!
    let key := if r.name.startsWith "RL policy (gamed" then "rl_gamed"
      else if r.name.startsWith "RL policy" then "rl_specified"
      else if r.name.startsWith "initial" then "initial"
      else if r.name.startsWith "always attempt" then "always_attempt"
      else if r.name.startsWith "always defer" then "always_defer"
      else if r.name.startsWith "supervised" then "supervised_gate"
      else k
    o.put "policy" s!"{key}.reward" (toString r.reward)
    o.put "policy" s!"{key}.regret" (toString (oracle - r.reward))
    o.put "policy" s!"{key}.false_published" (toString r.falsePublished)
  let hackedOwn := test.foldl (fun a f => a + Triage.hackedReward f (Triage.route hacked f)) 0
  let honestUnderHacked := test.foldl (fun a f => a + Triage.hackedReward f (Triage.route honest f)) 0
  IO.println s!"Gamed-reward check: under its own reward the gamed policy scores {hackedOwn} (the specified-reward policy {honestUnderHacked}); under the specified reward it scores {(rows.getD 2 oracleRow).reward}. False publications by `Triage.outcome` of the gamed policy: {outcomeFalse} of {test.length} (`outcome_publish_sound`: 0 for every model).\n"
  o.put "policy" "gamed.own_reward" (toString hackedOwn)
  o.put "policy" "gamed.outcome_false_published" (toString outcomeFalse)
  o.put "policy" "honest_weights_blake3" (toString (IxAI.digestOf "weights" (modelRaw honest)))
  o.put "policy" "gamed_weights_blake3" (toString (IxAI.digestOf "weights" (modelRaw hacked)))
  return (honest, hacked)

/-! ## 3. Premise selection -/

def scope : Scope :=
  scopes.headD { name := "", modules := [], pfx := "", testModules := [], validationModules := [] }

/-- The scorer configs `selectScorer` chooses by validation MRR on `order-basic`. -/
def pinnedScorer : SplitKind → ScorerConfig
  | .module => { lrRaw := 4096, decay := true, epochs := 12, negIdf := 0, negModule := 12, negRandom := 8, loss := .softmax }
  | .time => { lrRaw := 4096, decay := true, epochs := 12, negIdf := 0, negRandom := 16, loss := .softmax, residual := true,
               knn := 8, leaveOut := .module }

/-- The v2 scorer (2026-11-19), without the v3 pair features, kept for the paired comparison. -/
def v2Scorer : SplitKind → ScorerConfig
  | .module => { lrRaw := 4096, epochs := 4, negIdf := 0, negModule := 12, negRandom := 8, loss := .softmax, dropContext := v3Context }
  | .time => { lrRaw := 4096, epochs := 8, negIdf := 0, negRandom := 16, loss := .softmax, residual := true, dropContext := v3Context }

def splitName : SplitKind → String
  | .module => "module"
  | .time => "time"

/-- The curated `order-basic` dataset and its prepared library. -/
structure Premises where
  ld : Loaded
  lib : Library
  pl : PreparedLib
  /-- Every address's name: its first scope item's, else its first library theorem's. -/
  names : Std.HashMap Addr String
  /-- The extracted statement fields of each library theorem by name, with constant names:
  `TYPE-CONSTS`, `HEADS`, `ARITY` of `decls.tsv`. -/
  raw : Std.HashMap String (String × String × String)

def loadPremises : IO (Except String Premises) := do
  match ← load scope with
  | .error e => return .error e
  | .ok ld =>
    let lib := Library.of ld.ex
    let first := fun (m : Std.HashMap Addr String) (a : Addr) (n : String) =>
      if m.contains a then m else m.insert a n
    let names := ld.ex.library.foldl (fun m (p, n) => first m p.addr n)
      (ld.ex.items.foldl (fun m (it, n) => first m it.addr n) {})
    let mut raw : Std.HashMap String (String × String × String) := {}
    for l in (← IO.FS.lines (datasetsDir / scope.name / "decls.tsv")) do
      match l.splitOn "\t" with
      | ["lib", n, _, _, tc, _, hs, ar] => raw := raw.insert n (tc, hs, ar)
      | "lib" :: n :: _ :: _ :: tc :: _ => raw := raw.insert n (tc, "", "")
      | _ => pure ()
    return .ok { ld, lib, pl := PreparedLib.of ({} : ScorerConfig).features lib, names, raw }

def Premises.split (p : Premises) (k : SplitKind) : SplitData := splitOf scope p.ld.ex p.ld.curated k

def benchKs : List Nat := [1, 5, 10]

def recallStat (rs : Array ItemRank) (ki : Nat) : Statistic := fun idx =>
  let sel := pick rs idx
  bp (sel.foldl (fun a r => a + r.hits.getD ki 0) 0) (sel.foldl (fun a r => a + r.gold) 0)

/-- Mean reciprocal rank in units of `1/10^6`. -/
def mrrStat (rs : Array ItemRank) : Statistic := fun idx =>
  let sel := pick rs idx
  ((sel.foldl (fun a r => a + r.rrMicro) 0 / max sel.size 1 : Nat) : Int)

/-- One ranker's row: point estimates with bootstrap intervals. -/
def rankRow (rs : Array (Array Nat)) (name : String) (xs : Array ItemRank) : List String :=
  let all := identity xs.size
  name :: ((List.range benchKs.length).map fun ki =>
      s!"{showPct (recallStat xs ki all).toNat} {showCI (bootCI rs (recallStat xs ki))}") ++
    [s!"{showMicro3 (mrrStat xs all).toNat} {showMrrCI (bootCI rs (mrrStat xs))}"]

def gapRow (rs : Array (Array Nat)) (name : String) (a b : Array ItemRank) : List String :=
  let all := identity a.size
  name :: ((List.range benchKs.length).map fun ki =>
      s!"{showGap (recallStat a ki all - recallStat b ki all)} {showGapCI (pairedCI rs (recallStat a ki) (recallStat b ki))}") ++
    [s!"{showMicroGap (mrrStat a all - mrrStat b all)} {showMrrGapCI (pairedCI rs (mrrStat a) (mrrStat b))}"]

def putRanks (o : Out) (sp name : String) (rs : Array (Array Nat)) (xs : Array ItemRank) : IO Unit := do
  let all := identity xs.size
  for (k, ki) in benchKs.zip (List.range benchKs.length) do
    let ci := bootCI rs (recallStat xs ki)
    o.put "premises" s!"{sp}.{name}.R@{k}_bp" s!"{recallStat xs ki all} [{ci.1} {ci.2}]"
  let ci := bootCI rs (mrrStat xs)
  o.put "premises" s!"{sp}.{name}.MRR_micro" s!"{mrrStat xs all} [{ci.1} {ci.2}]"

/-- What the premise section leaves for the integrity and cost sections. -/
structure PremiseRun where
  split : SplitKind
  data : SplitData
  fitted : Fitted
  /-- `none` unless validation selection was run. -/
  selectionAgrees : Option Bool

def premiseSection (o : Out) (st : Setup) (p : Premises) : IO (List PremiseRun) := do
  IO.println s!"## 3. Premise selection (`order-basic`; every accessible library theorem is a candidate; {boot.resamples} bootstrap resamples of the test theorems, seed {boot.seed})\n"
  let mut runs : List PremiseRun := []
  for k in [SplitKind.module, .time] do
    let sd := p.split k
    let mut sel : Option Bool := none
    if st.size == "full" then
      let chosen ← selectScorer {} p.pl sd (log := false)
      sel := chosen.map fun c => (repr c).pretty == (repr (pinnedScorer k)).pretty
    match ← fitScorer (pinnedScorer k) p.pl sd with
    | .error e => IO.println s!"{splitName k} split: training left its bounds: {repr e}"
    | .ok f =>
      let items := sd.test
      let model := (items.map (rankItem benchKs p.pl (f.score p.pl))).toArray
      let idf := (items.map (rankItem benchKs p.pl (idfRankScore p.pl))).toArray
      let freq := (items.map (rankItem benchKs p.pl (frequencyScore p.pl f.prior))).toArray
      let v2 ← match ← fitScorer (v2Scorer k) p.pl sd with
        | .ok f2 => pure (items.map (rankItem benchKs p.pl (f2.score p.pl))).toArray
        | .error _ => pure #[]
      let rs := resamples boot items.length
      let cands := model.foldl (fun a r => a + r.candidates) 0
      IO.println s!"{splitName k} split: {items.length} test theorems, {cands / max items.length 1} candidates each on average; model {f.digest.short}\n"
      IO.println (table ["ranker", "R@1 [95% CI]", "R@5 [95% CI]", "R@10 [95% CI]", "MRR [95% CI]"]
        [rankRow rs "bilinear model" model, rankRow rs "IDF" idf, rankRow rs "frequency" freq,
         rankRow rs "bilinear model v2" v2,
         gapRow rs "model − IDF (paired)" model idf, gapRow rs "model − v2 model (paired)" model v2])
      putRanks o (splitName k) "model" rs model
      putRanks o (splitName k) "idf" rs idf
      putRanks o (splitName k) "frequency" rs freq
      putRanks o (splitName k) "model_v2" rs v2
      for (kk, ki) in benchKs.zip (List.range benchKs.length) do
        let ci := pairedCI rs (recallStat model ki) (recallStat idf ki)
        o.put "premises" s!"{splitName k}.gap_model_idf.R@{kk}_bp" s!"[{ci.1} {ci.2}]"
      let ci := pairedCI rs (mrrStat model) (mrrStat idf)
      o.put "premises" s!"{splitName k}.gap_model_idf.MRR_micro" s!"[{ci.1} {ci.2}]"
      o.put "premises" s!"{splitName k}.model_blake3" (toString f.digest)
      runs := runs ++ [{ split := k, data := sd, fitted := f, selectionAgrees := sel }]
  return runs

/-! ## 4. Distribution shift -/

def oodSection (o : Out) (st : Setup) (m : Model) : IO Unit := do
  let c := st.triage
  let trainFs := c.data Triage.spec
  IO.println s!"## 4. Distribution shift (triage, {st.size}; trained on depth-3 formulas; {testN} formulas per row)\n"
  let shifts : List (String × Nat × Nat) :=
    [("in-distribution test set (depth 3)", 3, c.seed + 1000003),
     ("depth 3, fresh seed", 3, c.seed + 2000003),
     ("depth 4", 4, c.seed + 2000003),
     ("depth 5", 5, c.seed + 2000003)]
  let mut rows : Array (List String) := #[]
  for (name, depth, seed) in shifts do
    let s := { Triage.spec with sample := Formula.gen depth }
    let fs := (s.sampleN testN (Rng.seeded seed)).1
    let cells := questions.map fun (_, pos, labels) =>
      let ps := predsOf m pos fs
      let maj := majority labels.length (trainFs.map (slotTarget pos))
      (accuracyBp ps, bp (countIf ps (·.target == maj)) ps.size, eceMilli ps)
    let validRate := bp (fs.filter (·.valid)).length fs.length
    let accCells := cells.map fun (a, mj, _) => s!"{showPct a} (maj. {showPct mj})"
    rows := rows.push ([name, showPct validRate] ++ accCells ++ [showMilli (cells.headD (0, 0, 0)).2.2])
    for ((q, _, _), (a, mj, e)) in questions.zip cells do
      o.put "ood" s!"depth{depth}.seed{seed}.{q}.accuracy_bp" (toString a)
      o.put "ood" s!"depth{depth}.seed{seed}.{q}.majority_bp" (toString mj)
      o.put "ood" s!"depth{depth}.seed{seed}.{q}.ece_milli" (toString e)
  IO.println (table ["test distribution", "valid formulas", "valid acc.", "head acc.", "coverage acc.", "ECE (valid)"] rows.toList)

/-! ## 5. Integrity -/

def passFail (b : Bool) : String := if b then "pass" else "FAIL"

/-- Lines of a TSV file under `.truthmines`, or none if it does not exist. -/
def readTsv (path : System.FilePath) : IO (List (List String)) := do
  if !(← path.pathExists) then return []
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (· ≠ "")
  return lines.map (·.splitOn "\t")

def integritySection (o : Out) (st : Setup) (m : Model) (p : Premises) (runs : List PremiseRun) :
    IO Unit := do
  IO.println "## 5. Integrity\n"
  let c := st.triage
  let s := Triage.spec
  let cd := card s c m
  let test := { c with testSize := testN }.test s
  let cardAgrees := questions.all fun (q, pos, _) =>
    let ps := predsOf m pos (test.take c.testSize)
    match cd.questions.find? (·.name == q) with
    | some qc => qc.correct == countIf ps (·.correct) && qc.total == ps.size
    | none => false
  let trainFs := c.data s
  let dup := (test.filter (trainFs.contains ·)).length
  let ld := p.ld
  let mut rows : Array (List String) := #[
    ["triage: bench test prefix reproduces the certified card's counts (`card`)", passFail cardAgrees],
    ["triage: held-out formulas equal to a training formula (small formula space; information)", s!"{dup} of {test.length}"],
    ["premises: module split train/test disjoint (`curate`, `split_disjoint`)", passFail ld.curated.disjoint],
    ["premises: premise rule agrees with the host filter (`premiseRuleAgrees`)", passFail (premiseRuleAgrees ld.ex ld.curated)]]
  for r in runs do
    let sd := r.data
    rows := rows.push [s!"premises: {splitName r.split} split train/test disjoint (`disjoint`, `splitBy_disjoint`)", passFail (disjoint sd.train sd.test)]
    rows := rows.push [s!"premises: {splitName r.split} split fit/validation disjoint", passFail (disjoint sd.fit sd.val)]
    match r.selectionAgrees with
    | some b => rows := rows.push [s!"premises: {splitName r.split} validation selection picks the pinned scorer config", passFail b]
    | none => rows := rows.push [s!"premises: {splitName r.split} validation selection picks the pinned scorer config", "not run at this size (run `ixai bench full`)"]
  for (k, v) in st.checks do
    rows := rows.push [k, v]
  -- Recorded Ix verdicts: forged claims proved by an earlier certificate run, and the reward harness.
  let index ← readTsv (projectDir / ".truthmines" / "index.tsv")
  let forged := index.filter fun r => (r.getD 1 "").startsWith "IxAIForged."
  let refusedForged := forged.filter fun r => (r.getD 8 "").startsWith "FAILED"
  let forgedLine := if forged.isEmpty then "requires certificate run (`ix/certify.sh` with the forged claims)"
    else s!"{refusedForged.length} of {forged.length} recorded Eval claims on `Forged_*.lean` failed in Ix ({", ".intercalate ((forged.map fun r => s!"{r.getD 1 ""}: {(r.getD 8 "").takeWhile (· != ':')}"))})"
  rows := rows.push [s!"forged claims refused by Ix itself (recorded in `.truthmines/index.tsv`; {st.size} not re-proved)", forgedLine]
  let rewards ← readTsv (projectDir / ".truthmines" / "rewards.tsv")
  let cheats := rewards.filter fun r => r.getD 1 "" != "honest"
  let cheatsAccepted := cheats.filter fun r => r.getD 2 "" == "RewardVerdict.accepted"
  let honestValid := rewards.filter fun r => r.getD 1 "" == "honest" && r.getD 0 "" != "converse"
  let rewardLine := if rewards.isEmpty then "requires certificate run (`ixai reward`)" else
    s!"{passFail (cheatsAccepted.isEmpty && honestValid.all (·.getD 2 "" == "RewardVerdict.accepted"))}: {cheats.length - cheatsAccepted.length} of {cheats.length} shortcut proofs (sorry, native_decide, smuggled axiom) refused; honest proofs of valid statements accepted"
  rows := rows.push ["reward harness: shortcut proofs refused by `ix check-lean` (recorded in `.truthmines/rewards.tsv`)", rewardLine]
  IO.println (table ["check", "result"] rows.toList)
  for r in rows do
    o.put "integrity" (r.getD 0 "") (r.getD 1 "")

/-! ## 6. Cost -/

def encBytes (xs : List Int) : Nat := (IxAI.Enc.enc ByteArray.empty xs).size

def fitsBits (bits : Nat) (xs : List Int) : Bool :=
  xs.all fun x => -(2 ^ (bits - 1) : Int) ≤ x && x < 2 ^ (bits - 1)

def widthBytes (xs : List Int) : String :=
  if fitsBits 8 xs then s!"{xs.length} (int8)"
  else if fitsBits 16 xs then s!"{2 * xs.length} (int16)"
  else if fitsBits 32 xs then s!"{4 * xs.length} (int32)"
  else s!"{8 * xs.length} (int64)"

def costSection (o : Out) (m policy : Model) (runs : List PremiseRun) : IO Unit := do
  IO.println "## 6. Cost\n"
  let tri := modelRaw m
  let pol := modelRaw policy
  let mut rows := #[["triage model", toString tri.length, widthBytes tri, toString (encBytes tri)],
                    ["routing policy", toString pol.length, widthBytes pol, toString (encBytes pol)]]
  for r in runs do
    let w := r.fitted.models.toList.flatMap fun m => (m.es ++ m.ep ++ m.wc).toList
    rows := rows.push [s!"premise scorer ({splitName r.split} split)", toString w.length, widthBytes w, toString (encBytes w)]
  IO.println (table ["model", "parameters", "weight bytes (fixed width)", "canonical encoding bytes"] rows.toList)
  for r in rows do
    o.put "cost" s!"{r.getD 0 ""}.parameters" (r.getD 1 "")
    o.put "cost" s!"{r.getD 0 ""}.weight_bytes" (r.getD 2 "")
    o.put "cost" s!"{r.getD 0 ""}.encoding_bytes" (r.getD 3 "")

/-- Wall-clock measurements, single-threaded, monotonic clock. -/
def clockSection (o : Out) (st : Setup) (m policy : Model) (p : Premises) (runs : List PremiseRun) :
    IO Unit := do
  let s := Triage.spec
  let n := 10000
  let fs := (s.sampleN n (Rng.seeded 777)).1
  let gate : Triage.Gate := ⟨200⟩
  let (trainNs, _) ← timeNs st.triage (fun c => train s c) (fun m => checksum (modelRaw m))
  let (rlNs, _) ← timeNs st.rl (fun rc => rlTrain Triage.policySpec Triage.bandit rc (st.rlBase.init Triage.policySpec))
    (fun m => checksum (modelRaw m))
  let (actNs, _) ← timeNs fs (fun fs => fs.map (Triage.act gate m)) (fun as => (as.filter (· == .publish)).length)
  let (askNs, _) ← timeNs fs (fun fs => fs.map fun f => (Triage.askCoverage m f).probs) (fun ps => ps.length)
  let (routeNs, _) ← timeNs fs (fun fs => fs.map (Triage.route policy)) (fun cs => (cs.filter (· == .attempt)).length)
  let mut rows := #[
    ["triage training (`train Triage.spec`, " ++ st.size ++ ")", showMs trainNs],
    ["RL training (`rlTrain`, specified reward, " ++ st.size ++ ")", showMs rlNs],
    ["gated triage decision (`Triage.act`), per 1,000", showMs (actNs * 1000 / n)],
    ["one triage question with probabilities (`askCoverage`), per 1,000", showMs (askNs * 1000 / n)],
    ["routing decision (`Triage.route`), per 1,000", showMs (routeNs * 1000 / n)]]
  o.time "triage_train_ns" (toString trainNs)
  o.time "rl_train_ns" (toString rlNs)
  o.time "triage_act_ns_per_1000" (toString (actNs * 1000 / n))
  o.time "triage_ask_ns_per_1000" (toString (askNs * 1000 / n))
  o.time "route_ns_per_1000" (toString (routeNs * 1000 / n))
  for r in runs do
    rows := rows.push [s!"premise scorer training ({splitName r.split} split)", s!"{r.fitted.trainMs} ms"]
    o.time s!"premise_train_ms.{splitName r.split}" (toString r.fitted.trainMs)
  match runs.find? (·.split == .time) with
  | some r =>
    let items := r.data.test.toArray
    let pl := p.pl
    let (rankNs, _) ← timeNs items (fun its => its.map (rankItem benchKs pl (r.fitted.score pl)))
      (fun xs => xs.foldl (fun a x => a + x.rrMicro) 0)
    let per := rankNs * 1000 / max items.size 1
    let avg := (items.foldl (fun a it => a + (candidates pl it).size) 0) / max items.size 1
    rows := rows.push [s!"premise ranking over all candidates (time split, {avg} on average), per 1,000 queries", showMs per]
    o.time "premise_rank_ns_per_1000" (toString per)
  | none => pure ()
  IO.println "## Wall clock (not part of the results digest; single thread, `IO.monoNanosNow`)\n"
  IO.println (table ["measurement", "time"] rows.toList)

/-! ## The report -/

def benchDir : System.FilePath := projectDir / ".truthmines" / "bench"

def run (st : Setup) : IO UInt32 := do
  let o ← Out.new
  IO.println s!"# IxBench v0 — size {st.size}\n"
  let t0 ← IO.monoMsNow
  let m := train Triage.spec st.triage
  o.put "meta" "size" st.size
  o.put "meta" "triage_config" ((repr st.triage).pretty 10000)
  o.put "meta" "triage_weights_blake3" (toString (IxAI.digestOf "weights" (modelRaw m)))
  o.put "meta" "bootstrap" s!"seed {boot.seed}, {boot.resamples} resamples, percentile 2.5/97.5"
  triageSection o st m
  let (honest, _) ← policySection o st m
  let p ← match ← loadPremises with
    | .ok p => pure p
    | .error e => IO.eprintln s!"premise dataset: {e}"; return 1
  let runs ← premiseSection o st p
  oodSection o st m
  integritySection o st m p runs
  costSection o m honest runs
  clockSection o st m honest p runs
  let t1 ← IO.monoMsNow
  IO.FS.createDirAll benchDir
  let path := benchDir / s!"bench-{st.size}.tsv"
  IO.FS.writeFile path ("\n".intercalate (← o.rows.get).toList ++ "\n")
  let digest := IxAI.blake3 (← IO.FS.readBinFile path)
  let clockPath := benchDir / s!"bench-{st.size}.clock.tsv"
  IO.FS.writeFile clockPath ("\n".intercalate (← o.clock.get).toList ++ "\n")
  IO.println s!"Results: {path} ({(← o.rows.get).size} rows), BLAKE3 {digest}"
  IO.println s!"Wall clock: {clockPath}; whole bench {t1 - t0} ms"
  return 0

end IxAIBench
