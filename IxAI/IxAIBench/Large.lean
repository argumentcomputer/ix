import IxAIBench.Baseline

/-!
# IxBench premise selection on all of Mathlib

`ixai bench mathlib-full module|time` trains the pinned v3 scorer of a split on the
`mathlib-full` dataset and ranks test theorems over every accessible library theorem against the
IDF and name-IDF baselines, with bootstrap intervals and paired gaps.
`ixai bench mathlib-full rerank RULE` trains the time-split scorer on Mathlib without the
`order-basic` rerank theorems and what depends on them (`RULE`: `theorem` or `module`, see
`excluded`) and scores the 157 rerank items of `.truthmines/bench/baseline-v0` next to the Opus
answers there. Each writes `.truthmines/bench/mathlib-full-PART.tsv` and prints its BLAKE3; wall
clock goes to a separate `.clock.tsv`.

At this size, three things differ from `ixai bench small`:
* the model scores a prefilter pool per theorem, the union of the IDF and name-IDF top `poolSize`
  (`rankFull`); candidates outside it follow in IDF order, and the pool's recall is reported;
* neighbour statistics ignore constants and name tokens with more than `fullCap` postings;
* at most `evalLimit` test theorems are ranked, a fixed stride through the test set.
-/

namespace IxAIBench.Large

open IxAICore IxAIData IxAIBench

def fullScope : Scope :=
  match scopes.find? (·.name == "mathlib-full") with
  | some s => s
  | none => { name := "mathlib-full", modules := [], pfx := "", testModules := [], validationModules := [] }

def poolSize : Nat := 500
def fullCap : Nat := 256
def evalLimit : Nat := 4000

/-- The pinned `order-basic` config with the posting cap. -/
def pinnedFull (k : SplitKind) : ScorerConfig := { pinnedScorer k with postingCap := fullCap }

/-- The config `runGrid` selects by validation MRR. The pinned 12 epochs are 46,000 steps per
epoch here, against 160 on `order-basic`; on the module split they leave the score bound. -/
def fullScorer : SplitKind → ScorerConfig
  | .module => { pinnedFull .module with epochs := 2, nearest := true }
  | .time => { pinnedFull .time with epochs := 2, lrRaw := 1024, nearest := true }

/-- Every `⌈n / limit⌉`-th element. -/
def stride {α : Type} (limit : Nat) (xs : List α) : List α :=
  let s := (xs.length + limit - 1) / max limit 1
  if s ≤ 1 then xs else (xs.zipIdx.filter fun (_, i) => i % s == 0).map (·.1)

def clockMs (t0 : Nat) : IO Nat := return (← IO.monoMsNow) - t0

def writeOut (o : Out) (part : String) : IO Unit := do
  IO.FS.createDirAll benchDir
  let path := benchDir / s!"mathlib-full-{part}.tsv"
  IO.FS.writeFile path ("\n".intercalate (← o.rows.get).toList ++ "\n")
  let clockPath := benchDir / s!"mathlib-full-{part}.clock.tsv"
  IO.FS.writeFile clockPath ("\n".intercalate (← o.clock.get).toList ++ "\n")
  IO.println s!"Results: {path} ({(← o.rows.get).size} rows), BLAKE3 {IxAI.blake3 (← IO.FS.readBinFile path)}"
  IO.println s!"Wall clock: {clockPath}; peak RSS {← peakRss}"

/-- The full-Mathlib dataset with its prepared library. -/
structure Full where
  ld : Loaded
  pl : PreparedLib

def loadFull (o : Out) : IO (Except String Full) := do
  let t0 ← IO.monoMsNow
  match ← load fullScope with
  | .error e => return .error e
  | .ok ld =>
    let c := ld.curated
    IO.println s!"mathlib-full: {ld.ex.modules.size} modules, {ld.ex.library.size} library theorems, {ld.ex.items.size} items; accepted {c.accepted.length}, deduped {c.deduped.length}, with premises {c.nonempty.length}; {← clockMs t0} ms"
    o.time "load_and_curate_ms" (toString (← clockMs t0))
    let t1 ← IO.monoMsNow
    let lib := Library.of ld.ex
    let pl := PreparedLib.of ({} : ScorerConfig).features lib
    IO.println s!"prepared library: {pl.prep.size} theorems, contiguous {pl.contiguous}, declarations ordered within modules {pl.declSorted}"
    let ms ← clockMs t1
    IO.println s!"prepared library: {ms} ms"
    o.time "prepare_ms" (toString ms)
    return .ok { ld, pl }

def maxAbs (xs : Array Int) : Nat := xs.foldl (fun a x => max a x.natAbs) 0

/-- `trainScorer`, step by step in `IO`, reporting the weights' magnitudes after each epoch and
the step at which a bound is left. -/
def trainLogged (c : ScorerConfig) (prep : Array Prepared) (st : Stats) (groups : Array Group) :
    IO (Except BoundError ScorerModel) := do
  let sched := (schedule c groups.size).toArray
  let perEpoch := sched.size / max c.epochs 1
  let mut m := ScorerModel.init c
  let t0 ← IO.monoMsNow
  for s in [:sched.size] do
    match step c prep st (c.lrAt s sched.size) m (sched[s]!.filterMap (groups[·]?)) with
    | .error e =>
      IO.println s!"bound left at step {s} of {sched.size} (epoch {s / max perEpoch 1 + 1}): {repr e}; |wc| {maxAbs m.wc}, |es| {maxAbs m.es}, |ep| {maxAbs m.ep}"
      return .error e
    | .ok m' => m := m'
    if perEpoch > 0 && (s + 1) % perEpoch == 0 then
      IO.println s!"epoch {(s + 1) / perEpoch}: {(← IO.monoMsNow) - t0} ms; |wc| {maxAbs m.wc} {m.wc}, |es| {maxAbs m.es}, |ep| {maxAbs m.ep}"
  return .ok m

/-- Train `c` on `train` with statistics for `eval`, timing each stage. -/
def fitTimed (o : Out) (c : ScorerConfig) (pl : PreparedLib) (train eval : List (Item Addr)) :
    IO (Except BoundError Fitted) := do
  let t0 ← IO.monoMsNow
  let stats := Stats.build pl c.leaveOut c.knn c.coUse train eval c.postingCap
  IO.println s!"statistics: {stats.thm.size} theorems"
  let ms0 ← clockMs t0
  IO.println s!"statistics: {ms0} ms"
  o.time "stats_ms" (toString ms0)
  let t1 ← IO.monoMsNow
  let groups := groupsOf c pl train
  let triples := (groups.map fun g => g.pos.size * g.neg.size).foldl (· + ·) 0
  IO.println s!"groups: {groups.size} theorems, {triples} (gold, negative) pairs"
  let ms1 ← clockMs t1
  IO.println s!"groups: {ms1} ms"
  o.time "groups_ms" (toString ms1)
  let t2 ← IO.monoMsNow
  match ← trainLogged c pl.prep stats groups with
  | .error e => return .error e
  | .ok m =>
    let ms ← clockMs t2
    IO.println s!"trained {c.describe} in {ms} ms"
    o.time "train_ms" (toString ms)
    return .ok { config := c, stats, groups, models := #[m], trainMs := ms }

def rankRows (o : Out) (sec : String) (rs : Array (Array Nat)) (named : List (String × Array ItemRank))
    (gaps : List (String × Array ItemRank × Array ItemRank)) : IO Unit := do
  IO.println (table ["ranker", "R@1 [95% CI]", "R@5 [95% CI]", "R@10 [95% CI]", "MRR [95% CI]"]
    (named.map (fun (n, xs) => rankRow rs n xs) ++ gaps.map fun (n, a, b) => gapRow rs n a b))
  for (n, xs) in named do putRanks o sec n rs xs
  for (n, a, b) in gaps do
    for (k, ki) in benchKs.zip (List.range benchKs.length) do
      let ci := pairedCI rs (recallStat a ki) (recallStat b ki)
      o.put sec s!"{n}.R@{k}_bp" s!"{recallStat a ki (identity a.size) - recallStat b ki (identity a.size)} [{ci.1} {ci.2}]"
    let ci := pairedCI rs (mrrStat a) (mrrStat b)
    o.put sec s!"{n}.MRR_micro" s!"{mrrStat a (identity a.size) - mrrStat b (identity a.size)} [{ci.1} {ci.2}]"

/-- Train the pinned scorer of split `k` on all of Mathlib and rank its test theorems. -/
def runSplit (k : SplitKind) : IO UInt32 := do
  let o ← Out.new
  let t0 ← IO.monoMsNow
  let full ← match ← loadFull o with
    | .ok f => pure f
    | .error e => IO.eprintln e; return 1
  let pl := full.pl
  let t1 ← IO.monoMsNow
  let sd := splitOf fullScope full.ld.ex full.ld.curated k
  let disj := disjointFast sd.train sd.test
  IO.println s!"{splitName k} split: train {sd.train.length}, test {sd.test.length}, dropped {sd.dropped}; disjoint {disj}; {← clockMs t1} ms"
  o.time "split_ms" (toString (← clockMs t1))
  let evalItems := stride evalLimit sd.test
  let poolsOk := poolsAgree pl (sd.train.take 200)
  IO.println s!"evaluating {evalItems.length} of {sd.test.length} test theorems; candidate pools agree with `candidates` on 200 training theorems: {poolsOk}"
  let c := fullScorer k
  o.put "meta" "dataset" s!"mathlib-full, {full.ld.curated.nonempty.length} items with premises, {pl.prep.size} library theorems"
  o.put "meta" "split" s!"{splitName k}: {sd.rule}"
  o.put "meta" "counts" s!"train {sd.train.length}, test {sd.test.length}, dropped {sd.dropped}, evaluated {evalItems.length}"
  o.put "meta" "config" c.describe
  o.put "meta" "prefilter" s!"IDF top {poolSize} ∪ name-IDF top {poolSize}; posting cap {fullCap}"
  o.put "meta" "bootstrap" s!"seed {boot.seed}, {boot.resamples} resamples, percentile 2.5/97.5"
  o.put "integrity" "train_test_disjoint" (passFail disj)
  o.put "integrity" "pools_agree" (passFail poolsOk)
  match ← fitTimed o c pl sd.train evalItems with
  | .error e => IO.eprintln s!"training left its bounds: {repr e}"; return 1
  | .ok f =>
    o.put "model" "blake3" (toString f.digest)
    o.put "model" "training_theorems" (toString f.groups.size)
    let t2 ← IO.monoMsNow
    let score := f.score pl
    let rows := parMap evalItems.toArray (rankFull benchKs pl poolSize score)
    let gold := rows.foldl (fun a r => a + r.model.gold) 0
    let inPool := rows.foldl (fun a r => a + r.inPool) 0
    let cands := rows.foldl (fun a r => a + r.model.candidates) 0
    let pool := rows.foldl (fun a r => a + r.poolSize) 0
    IO.println s!"ranked in {← clockMs t2} ms: {rows.size} theorems, {cands / max rows.size 1} candidates and a pool of {pool / max rows.size 1} each on average; {inPool} of {gold} gold premises in the pool ({showPct (bp inPool gold)})\n"
    o.time "rank_ms" (toString (← clockMs t2))
    o.put "prefilter" "gold_in_pool" s!"{inPool} of {gold}"
    o.put "prefilter" "mean_candidates" (toString (cands / max rows.size 1))
    let rs := resamples boot rows.size
    let model := rows.map (·.model)
    let idf := rows.map (·.idf)
    let name := rows.map (·.name)
    let mr := rows.map (·.modelRerank)
    let ir := rows.map (·.idfRerank)
    let nr := rows.map (·.nameRerank)
    let mut pinnedRows : Option (Array FullRank) := none
    if k == .time then
      IO.println s!"also training the pinned config: {(pinnedFull k).describe}"
      match ← fitTimed o (pinnedFull k) pl sd.train evalItems with
      | .error e =>
        IO.println s!"pinned config left its bounds: {repr e}"
        o.put "model" "pinned" s!"left its bounds: {repr e}"
      | .ok fp =>
        o.put "model" "pinned_blake3" (toString fp.digest)
        pinnedRows := some (parMap evalItems.toArray (rankFull benchKs pl poolSize (fp.score pl)))
    let pf := (pinnedRows.map (·.map (·.model))).toList.map fun xs => ("model_pinned", xs)
    let pr := (pinnedRows.map (·.map (·.modelRerank))).toList.map fun xs => ("model_pinned", xs)
    IO.println s!"## {splitName k} split, all accessible candidates\n"
    rankRows o s!"{splitName k}.full" rs ([("model", model), ("idf", idf), ("name_idf", name)] ++ pf)
      ([("model − IDF (paired)", model, idf), ("model − name-IDF (paired)", model, name)] ++
        pf.map fun (_, xs) => ("model − pinned model (paired)", model, xs))
    IO.println s!"## {splitName k} split, IDF top 30 reranked (MRR over the top 10)\n"
    rankRows o s!"{splitName k}.rerank30" rs ([("model", mr), ("idf", ir), ("name_idf", nr)] ++ pr)
      ([("model − IDF (paired)", mr, ir), ("model − name-IDF (paired)", mr, nr)] ++
        pr.map fun (_, xs) => ("model − pinned model (paired)", mr, xs))
    o.time "total_ms" (toString (← clockMs t0))
    writeOut o (splitName k)
    return 0

/-- Validation of a few configs around the pinned one on the split's fit set, ranked on at most
1,000 validation theorems; stops starting configs after 30 minutes. -/
def runGrid (k : SplitKind) : IO UInt32 := do
  let o ← Out.new
  let t0 ← IO.monoMsNow
  let full ← match ← loadFull o with
    | .ok f => pure f
    | .error e => IO.eprintln e; return 1
  let pl := full.pl
  let sd := splitOf fullScope full.ld.ex full.ld.curated k
  let val := stride 1000 sd.val
  IO.println s!"{splitName k} split: fit {sd.fit.length}, validation {sd.val.length} (ranking {val.length})"
  let base := pinnedFull k
  let grid := [{ base with epochs := 1 }, { base with epochs := 2, nearest := true },
    { base with epochs := 1, lrRaw := 1024 }, { base with epochs := 4, nearest := true },
    { base with epochs := 2, lrRaw := 1024, nearest := true }]
  for c in grid do
    if (← clockMs t0) > 30 * 60 * 1000 then IO.println "time budget reached"; break
    match ← fitTimed o c pl sd.fit val with
    | .error e => IO.println s!"validation: {c.describe}: bound error {repr e}"
    | .ok f =>
      let rows := parMap val.toArray (rankFull benchKs pl poolSize (f.score pl))
      let fmt := fun (xs : Array ItemRank) => ", ".intercalate ((RankEval.ofItems benchKs xs.toList).summary.filter
        (fun (key, _) => !key.startsWith "macro") |>.map fun (key, v) => s!"{key} {v}")
      IO.println s!"validation: {c.describe}: model {fmt (rows.map (·.model))}; rerank-30 {fmt (rows.map (·.modelRerank))}; IDF {fmt (rows.map (·.idf))}; name-IDF {fmt (rows.map (·.name))}"
  return 0

/-! ## The `order-basic` rerank items -/

/-- Items of `items` to leave out of training so that nothing trained on depends on the theorems
`held`. `theorem`: the held theorems and every item whose proof uses one of them, directly or
through the proofs of other items (dependencies through definitions are not followed). `module`:
every item of a module that is, or imports, a module of a held theorem. -/
def excluded (rule : String) (lib : Library) (items : List (Item Addr)) (held : List (Item Addr)) :
    Std.HashSet Addr := Id.run do
  if rule == "module" then
    let mods := (dedupNat (held.map (·.module))).toList
    let out : Std.HashSet Addr := {}
    return items.foldl (fun s it =>
      if mods.any (lib.reach[it.module]!.getD · false) then s.insert it.addr else s) out
  let users : Std.HashMap Addr (List Addr) := items.foldl (fun m it =>
    it.premises.foldl (fun m p => m.insert p (it.addr :: m.getD p [])) m) {}
  let mut seen : Std.HashSet Addr := held.foldl (fun s it => s.insert it.addr) {}
  let mut todo := held.map (·.addr)
  while !todo.isEmpty do
    let a := todo.head!
    todo := todo.tail
    for u in users.getD a [] do
      if !seen.contains u then
        seen := seen.insert u
        todo := u :: todo
  return seen

def runRerank (rule : String) : IO UInt32 := do
  let o ← Out.new
  let t0 ← IO.monoMsNow
  let p ← match ← loadPremises with
    | .ok p => pure p
    | .error e => IO.eprintln s!"premise dataset: {e}"; return 1
  let dir := benchDir / "baseline-v0"
  let ansDir := dir / "answers"
  let files : Array IO.FS.DirEntry ← ansDir.readDir
  let files := (files.filter fun f => f.fileName.endsWith ".txt" && f.fileName.startsWith "premises-").qsort
    (fun a b => a.fileName < b.fileName)
  let texts ← files.toList.mapM fun f => IO.FS.readFile f.path
  let rr := rerankSet p
  let parsed := parseAnswers p [] rr texts
  let addrs := fun (js : Array Nat) => js.map (p.pl.prep[·]!.premise.addr)
  let llm := (rr.map fun ri => ItemRank.ofRanked benchKs ri.item.premises
    (addrs ((parsed.ranking.get? ri.id).getD #[])) candidateCount).toArray
  let idf := (rr.map fun ri => ItemRank.ofRanked benchKs ri.item.premises
    ((rankAmong p.pl ri.item ri.cands (idfRankScore p.pl)).extract 0 10) candidateCount).toArray
  let some fv3 := (← fitScorer (pinnedScorer .time) p.pl (p.split .time)).toOption
    | IO.eprintln "order-basic scorer left its bounds"; return 1
  let v3 := (rr.map fun ri => ItemRank.ofRanked benchKs ri.item.premises
    ((rankAmong p.pl ri.item ri.cands (fv3.score p.pl)).extract 0 10) candidateCount).toArray
  IO.println s!"order-basic: {rr.length} rerank items, {parsed.ranking.size} answered by the LLM; v3 model {fv3.digest.short}"
  let same := fun (a b : ItemRank) => a.hits == b.hits && a.gold == b.gold && a.rrMicro == b.rrMicro && a.candidates == b.candidates
  let fastOk := (p.split .time).test.all fun it =>
    same (rankItemFast benchKs p.pl (fv3.score p.pl) it) (rankItem benchKs p.pl (fv3.score p.pl) it) &&
    same (rankItemFast benchKs p.pl (idfRankScore p.pl) it) (rankItem benchKs p.pl (idfRankScore p.pl) it)
  IO.println s!"`ItemRank.ofOrder` agrees with the sorted ranking on the order-basic time test set: {fastOk}"
  o.put "integrity" "fast_ranking_agrees_order_basic" (passFail fastOk)
  let fl ← match ← loadFull o with
    | .ok f => pure f
    | .error e => IO.eprintln e; return 1
  let pl := fl.pl
  let items := fl.ld.curated.nonempty
  let byAddr : Std.HashMap Addr (Item Addr) := items.foldl (fun m it => m.insert it.addr it) {}
  let held := rr.filterMap fun ri => byAddr.get? ri.item.addr
  let sameGold := (rr.filter fun ri => (byAddr.get? ri.item.addr).any (·.premises == ri.item.premises)).length
  IO.println s!"{held.length} of {rr.length} rerank theorems found in mathlib-full, {sameGold} with the same gold premises"
  let t1 ← IO.monoMsNow
  let ex := excluded rule pl.lib items held
  let other := if rule == "module" then "theorem" else "module"
  IO.println s!"rule {other} would exclude {(excluded other pl.lib items held).size} of {items.length} items"
  let train := items.filter fun it => !ex.contains it.addr
  let disj := disjointFast train held && held.all fun h => !train.any (·.premises.contains h.addr)
  IO.println s!"rule {rule}: excluded {ex.size} items, training on {train.length}; disjoint from the rerank theorems {disj}; {← clockMs t1} ms"
  o.put "meta" "rule" (if rule == "module" then "train = mathlib-full items of modules that neither are nor import a module of a rerank theorem"
    else "train = mathlib-full items other than the rerank theorems whose proofs use none of them, directly or through other items' proofs")
  o.put "meta" "counts" s!"rerank items {rr.length}, found {held.length}, same gold {sameGold}, excluded {ex.size}, train {train.length}"
  o.put "meta" "config" (fullScorer .time).describe
  o.put "integrity" "train_disjoint_from_rerank_theorems" (passFail disj)
  match ← fitTimed o (fullScorer .time) pl train held with
  | .error e => IO.eprintln s!"training left its bounds: {repr e}"; return 1
  | .ok f =>
    o.put "model" "blake3" (toString f.digest)
    let score := f.score pl
    let ours := (rr.map fun ri =>
      match byAddr.get? ri.item.addr with
      | none => ItemRank.ofRanked benchKs ri.item.premises #[] candidateCount
      | some it =>
        let cs := ri.cands.filterMap fun j => pl.index.get? p.pl.prep[j]!.premise.addr
        ItemRank.ofRanked benchKs ri.item.premises ((rankAmong pl it cs score).extract 0 10) candidateCount).toArray
    let rs := resamples boot rr.length
    IO.println s!"## order-basic rerank-30 ({rr.length} theorems; same candidates and keys as baseline-v0)\n"
    rankRows o "rerank" rs [("llm", llm), ("full_model", ours), ("v3_model", v3), ("idf", idf)]
      [("LLM − full model (paired)", llm, ours), ("full model − v3 model (paired)", ours, v3),
       ("full model − IDF (paired)", ours, idf)]
    o.time "total_ms" (toString (← clockMs t0))
    writeOut o s!"rerank-{rule}"
    return 0

def main (args : List String) : IO UInt32 :=
  match args with
  | ["module"] => runSplit .module
  | ["time"] => runSplit .time
  | ["grid", "module"] => runGrid .module
  | ["grid", "time"] => runGrid .time
  | ["rerank", rule] => if rule == "theorem" || rule == "module" then runRerank rule else
      do IO.eprintln "rule: theorem or module"; return 2
  | _ => do IO.eprintln "usage: ixai bench mathlib-full module|time|rerank theorem|module"; return 2

end IxAIBench.Large
