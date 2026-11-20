import IxAIData.Scorer
import IxAICommon.Paths
import Lean.Data.Json

/-!
# `ixai premises`: curate, commit, train and evaluate

`ixai premises extract SCOPE` runs `ix/premises/extract.sh` for a scope; `ixai premises run SCOPE`
reads the extraction, applies the curation rules, writes the dataset's items and manifest to
`.truthmines/datasets/`, then for each requested split trains a scorer and reports recall@k and
MRR on the held-out theorems against the frequency and IDF baselines.

* `--scorer bilinear` (default): the Fx16 bilinear scorer with a pairwise loss (`IxAIData.Scorer`).
* `--scorer mlp`: the relevance MLP trained by `IxAICore.train` (`IxAIData.Relevance`).
* `--split module`: test = whole held-out modules. `--split time`: test = the last fifth of every
  module's theorems. `--split both` (default) runs both.
-/

namespace IxAIData

open IxAI IxAICore Lean

structure Scope where
  name : String
  /-- The modules imported; their import closure is the environment. -/
  modules : List String
  /-- Items are the theorems of modules under this prefix. -/
  pfx : String
  /-- Held-out modules. -/
  testModules : List String
  /-- Training modules held out to choose the model config. -/
  validationModules : List String
  /-- When positive, the modules under `pfx` whose name's `fnv1a` is 0 modulo `sample` are test
  modules too, and those at 1 validation modules. -/
  sample : Nat := 0
  /-- Too large for `ixai premises run` to train and evaluate (`ixai bench mathlib-full` does). -/
  large : Bool := false

def Scope.isTest (s : Scope) (name : String) : Bool :=
  s.testModules.contains name || (s.sample > 0 && name.startsWith s.pfx && fnv1a name % s.sample == 0)

def Scope.isValidation (s : Scope) (name : String) : Bool :=
  s.validationModules.contains name || (s.sample > 0 && name.startsWith s.pfx && fnv1a name % s.sample == 1)

def scopes : List Scope :=
  [{ name := "order-basic"
     modules := ["Mathlib.Order.Basic", "Mathlib.Logic.Relation", "Mathlib.Logic.Function.Iterate"]
     pfx := "Mathlib"
     testModules := ["Mathlib.Order.Basic", "Mathlib.Logic.Function.Iterate"]
     validationModules := ["Mathlib.Logic.Relation"] },
   { name := "mathlib-full"
     modules := ["Mathlib"]
     pfx := "Mathlib"
     testModules := []
     validationModules := []
     sample := 50
     large := true }]

def projectDir : System.FilePath := IxAI.projectDir
def datasetsDir : System.FilePath := projectDir / ".truthmines" / "datasets"

def buckets : Nat := 32

def pairConfig (f : Features) : PairConfig := { features := f, seed := 17, hard := 4, random := 4 }

/-- Candidate featurizers and model configs; `trainSize` is set to the number of training pairs. -/
def grid : List (Features × Config) :=
  [true, false].flatMap fun statements => [1, 4].flatMap fun batch => [1, 2].map fun epochs =>
    ({ buckets, statements },
     { seed := 42, hidden := 16, lrRaw := 1, epochs, batch, trainSize := 0, testSize := 0 })

def ks : List Nat := [1, 5, 10]

def policyOf (ex : Extraction) : Except String (Policy Addr) := do
  let look := fun (n : String) => match ex.names.get? n with
    | some a => pure a
    | none => throw s!"{n} has no address in the extraction"
  pure { sorryAx := ← look "sorryAx"
         allowedAxioms := [← look "propext", ← look "Classical.choice", ← look "Quot.sound"] }

/-- An item's committed record: its address, module name, premises and split. -/
def itemLeaf (modules : Array Module) (split : String) (it : Item Addr) : Digest :=
  digestOf "premises/item" (it.addr, ((modules[it.module]?.map (·.name)).getD "", (it.premises, split)))

def rootFormat : String :=
  "ixai/merkle2: merkleRootV2, H(merkle2/root, leaf count, top); root = sorted item addresses, recordsRoot = train then test record leaves"

def rootsV1Note : String :=
  "merkleRootV1 of the same leaves: the format of roots recorded before 2026-11-19, which does not bind the leaf count; for matching those records only"

def acceptanceText : String :=
  "every constant and axiom name of the proof addressed (else refused as unresolvedName); no sorryAx; axioms within propext, Classical.choice, Quot.sound (so no Lean.ofReduceBool or ofReduceNat); no direct reference to an @[extern] or @[implemented_by] constant"

def sortAddrs (xs : List Addr) : List Addr :=
  ((xs.toArray.map fun a => (a.hex, a)).qsort fun a b => a.1 < b.1).toList.map (·.2)

def pct (num den : Nat) : String :=
  if den == 0 then "n/a" else
  let t := num * 1000 / den
  s!"{t / 10}.{t % 10}%"

def readSource (dir : System.FilePath) : IO (List (String × String)) := do
  let ls ← IO.FS.lines (dir / "source.txt")
  return ls.toList.filterMap fun l => match l.splitOn " " with
    | k :: v => some (k, " ".intercalate v)
    | [] => none

def envRoot (dir : System.FilePath) : IO String := do
  match Json.parse (← IO.FS.readFile (dir / "report.json")) with
  | .ok j =>
    for k in ["consts_root", "constsRoot", "canonical_consts_root", "env_root", "root"] do
      if let .ok (v : String) := j.getObjValAs? String k then return v
    return (j.compress.take 200).toString
  | .error e => return s!"unparsed report: {e}"

def recallJson (e : Eval) : Json :=
  Json.arr (e.recall.zip e.macroRecall |>.map fun ((k, h, g), (_, m)) =>
    Json.mkObj [("k", toJson k), ("hits", toJson h), ("gold", toJson g),
                ("microRecall", toJson (pct h g)), ("macroRecall", toJson (pct m (1000 * e.items)))]).toArray

def showEval (label : String) (e : Eval) : IO Unit := do
  let parts := e.recall.zip e.macroRecall |>.map fun ((k, h, g), (_, m)) =>
    s!"R@{k} {pct h g} (macro {pct m (1000 * e.items)})"
  IO.println s!"{label}: {", ".intercalate parts}; {e.items} theorems, {e.candidates} candidates"

/-! ## Splits and scorers -/

inductive ScorerKind where
  | mlp
  | bilinear
  deriving Repr, DecidableEq

inductive SplitKind where
  | module
  | time
  deriving Repr, DecidableEq

structure Options where
  scorer : ScorerKind := .bilinear
  splits : List SplitKind := [.module, .time]
  scorerConfig : ScorerConfig := {}
  grid : String := "default"
  /-- Train and evaluate; without it, `run` curates, commits and splits only. -/
  train : Bool := true

/-- A train/test split with a validation split carved out of its training set. -/
structure SplitData where
  name : String
  rule : String
  train : List (Item Addr)
  test : List (Item Addr)
  fit : List (Item Addr)
  val : List (Item Addr)
  dropped : Nat

/-- Each item's position among the items of its module, in the given (declaration) order, and the
number of those items. -/
def moduleRanks (items : List (Item Addr)) : Std.HashMap Addr (Nat × Nat) := Id.run do
  let counts : Std.HashMap Nat Nat := items.foldl (fun m it => m.insert it.module (m.getD it.module 0 + 1)) {}
  let mut seen : Std.HashMap Nat Nat := {}
  let mut out : Std.HashMap Addr (Nat × Nat) := {}
  for it in items do
    let r := seen.getD it.module 0
    out := out.insert it.addr (r, counts.getD it.module 0)
    seen := seen.insert it.module (r + 1)
  return out

/-- The time-ordered test set: the last fifth of every module's items. A set rather than a
predicate, so the ranks are computed once rather than on every application. -/
def lateFifth (items : List (Item Addr)) : Std.HashSet Addr :=
  let ranks := moduleRanks items
  items.foldl (fun s it => match ranks.get? it.addr with
    | some (r, n) => if heldOutLate 1 5 r n then s.insert it.addr else s
    | none => s) {}

def splitOf (scope : Scope) (ex : Extraction) (c : Curated) : SplitKind → SplitData
  | .module =>
    let valIdx := (List.range ex.modules.size).filter fun i => scope.isValidation (ex.modules[i]!.name)
    let valSet : Std.HashSet Nat := valIdx.foldl (·.insert ·) {}
    let (fit, val) := splitFast (valSet.contains ·) c.train
    { name := "module", rule := if scope.sample > 0 then s!"test = items of the modules under {scope.pfx} whose name's FNV-1a is 0 mod {scope.sample}; validation = 1 mod {scope.sample}" else s!"test = items of {scope.testModules}; validation = items of {scope.validationModules}"
      train := c.train, test := c.test, fit, val
      dropped := c.nonempty.length - c.train.length - c.test.length }
  | .time =>
    let late := lateFifth c.nonempty
    let (train, test) := splitByFast (fun it => late.contains it.addr) c.nonempty
    let lateTrain := lateFifth train
    let (fit, val) := splitByFast (fun it => lateTrain.contains it.addr) train
    { name := "time", rule := "test = the last fifth of every module's items by declaration order (IxAIData.splitBy, heldOutLate 1 5); train = other items that use no test theorem as a premise (splitBy_disjoint, splitBy_addr_disjoint); validation = the same rule applied to train"
      train, test, fit, val, dropped := c.nonempty.length - train.length - test.length }

def evalJson (e : RankEval) : Json :=
  Json.mkObj ((e.summary.map fun (k, v) => (k, Json.str v)) ++
    [("hits", toJson e.hits), ("gold", toJson e.gold), ("theorems", toJson e.items),
     ("candidates", toJson e.candidates)])

def showRank (label : String) (e : RankEval) : IO Unit :=
  IO.println s!"{label}: {", ".intercalate (e.summary.map fun (k, v) => s!"{k} {v}")}; {e.items} theorems, {e.candidates} candidates"

def baselines (pl : PreparedLib) (prior : Prior) (test : List (Item Addr)) : IO (List (String × Json)) := do
  let freq := evalRanking ks pl test (frequencyScore pl prior)
  let idf := evalRanking ks pl test (idfRankScore pl)
  let name := evalRanking ks pl test (nameRankScore pl)
  showRank "frequency baseline" freq
  showRank "IDF baseline" idf
  showRank "name-IDF baseline" name
  return [("frequencyBaseline", evalJson freq), ("idfBaseline", evalJson idf),
    ("nameIdfBaseline", evalJson name)]

/-- Candidate scorer configs; the one with the best validation MRR is retrained on the whole
training split. -/
def scorerGridV2 (base : ScorerConfig) : List ScorerConfig :=
  [(0, 4, 16), (8, 4, 8), (0, 12, 8)].flatMap fun (negIdf, negModule, negRandom) =>
  [(Loss.hinge, [4096, 16384]), (.softmax, [1024, 4096])].flatMap fun (loss, lrs) =>
  [false, true].flatMap fun residual => [true, false].flatMap fun nameTower =>
  lrs.flatMap fun lrRaw => [2, 4, 8, 12].map fun epochs =>
    { base with lrRaw, epochs, negIdf, negModule, negRandom, loss, residual, nameTower }

def ScorerConfig.describe (c : ScorerConfig) : String :=
  s!"negatives {c.negIdf} IDF + {c.negModule} module + {c.negRandom} random, {repr c.loss}{if c.residual then ", residual" else ""}{if c.nameTower then "" else ", no name tower"}, lr {c.lrRaw}/65536{if c.decay then " decayed" else ""}{if c.nearest then ", nearest" else ""}, epochs {c.epochs}{if c.ensemble > 1 then s!", ensemble {c.ensemble}" else ""}, knn {c.knn}, co {c.coUse}, leave out {repr c.leaveOut}{if c.dropContext.isEmpty then "" else s!", drop {c.dropContext}"}"

/-- The selection grid of `ixai premises run` and `ixai bench full`. -/
def scorerGrid (base : ScorerConfig) : List ScorerConfig :=
  [(0, 4, 16), (0, 12, 8)].flatMap fun (negIdf, negModule, negRandom) =>
  [4096, 8192].flatMap fun lrRaw => [false, true].flatMap fun residual =>
  [(0, LeaveOut.self), (8, .module)].flatMap fun (knn, leaveOut) => [4, 8, 12].map fun epochs =>
    { base with negIdf, negModule, negRandom, loss := .softmax, lrRaw, decay := true, residual,
                knn, leaveOut, epochs }

/-- The pair features added in v3: neighbour votes (25–28), the head and hypothesis cross
features (29–32) and co-usage (33–34). -/
def v3Context : List Nat := List.range' 25 10

/-- Named grids for `ixai premises run --grid NAME`; `default` is `scorerGrid`. -/
def namedGrid (name : String) (k : SplitKind) (base : ScorerConfig) : List ScorerConfig :=
  let pinned : ScorerConfig := match k with
    | .module => { base with lrRaw := 4096, epochs := 4, negIdf := 0, negModule := 12, negRandom := 8, loss := .softmax }
    | .time => { base with lrRaw := 4096, epochs := 8, negIdf := 0, negRandom := 16, loss := .softmax, residual := true }
  match name with
  | "v2" => scorerGridV2 { base with dropContext := v3Context }
  | "v2-pinned" => [{ pinned with dropContext := v3Context }]
  | "stats" => [0, 8, 16, 32].flatMap fun knn => [LeaveOut.self, .module, .later].flatMap fun leaveOut =>
      [[], List.range' 29 4].map fun dropContext => { pinned with knn, leaveOut, dropContext }
  | "co" => [(0, LeaveOut.self), (0, .module), (8, .module)].flatMap fun (knn, leaveOut) =>
      [5, 10, 20].map fun coUse => { pinned with knn, leaveOut, coUse }
  | "hard" => [(16, 0, 4), (30, 0, 0), (30, 4, 4)].flatMap fun (negIdf, negModule, negRandom) =>
      [2, 4, 8].map fun epochs => { pinned with negIdf, negModule, negRandom, epochs }
  | "ens" => [(0, LeaveOut.self), (8, .module)].flatMap fun (knn, leaveOut) =>
      [2, 4].map fun ensemble => { pinned with knn, leaveOut, ensemble }
  | "diag" => [5, 6, 7, 8, 9, 10].map (fun epochs => { pinned with epochs }) ++
      [4, 8, 12].map (fun epochs => { pinned with epochs, lrRaw := 2048 }) ++
      [8, 12].map (fun epochs => { pinned with epochs, lrRaw := 8192, decay := true })
  | "ensd" => [(0, LeaveOut.self), (8, .module)].flatMap fun (knn, leaveOut) =>
      [1, 4].map fun ensemble => { pinned with knn, leaveOut, ensemble, decay := true, lrRaw := 8192 }
  | "schedule" => [(false, false), (true, false), (false, true), (true, true)].flatMap fun (decay, nearest) =>
      [2, 4, 8, 12].map fun epochs => { pinned with decay, nearest, epochs, dropContext := v3Context }
  | _ => scorerGrid base

/-- One validation run: full-ranking MRR (micro, `1/10^6`) and the reranking items. -/
def validate (c : ScorerConfig) (pl : PreparedLib) (s : SplitData) (st : Stats) (log : Bool) :
    Except BoundError (RankEval × Array ItemRank × String) := do
  let ms ← trainEnsemble c pl st s.fit
  let score := ensembleScore c pl st ms
  let maxAbs := fun (xs : Array Int) => xs.foldl (fun a x => max a x.natAbs) 0
  let mags := ms.map fun m => s!"max |wc| {maxAbs m.wc} at {m.wc.findIdx? (·.natAbs == maxAbs m.wc)}, |es| {maxAbs m.es}, |ep| {maxAbs m.ep}"
  return (evalRanking ks pl s.val score, if log then rerankItems ks 30 pl s.val score else #[], s!"{mags}")

def showReranked (rs : Array ItemRank) : String :=
  let e := RankEval.ofItems ks rs.toList
  s!"rerank-30 {", ".intercalate ((e.summary.filter fun (k, _) => !k.startsWith "macro").map fun (k, v) => s!"{k} {v}")}"

/-- Train every config of `grid` on the split's fit set and return the one with the best
validation MRR. Statistics are built once per (leave-out rule, neighbour count, co-usage). -/
def selectScorer (base : ScorerConfig) (pl : PreparedLib) (s : SplitData) (log : Bool := true)
    (grid : List ScorerConfig := scorerGrid base) : IO (Option ScorerConfig) := do
  let mut cache : List ((LeaveOut × Nat × Nat × Nat) × Stats) := []
  let mut best : Option (ScorerConfig × Nat) := none
  for c in grid do
    let st ← match cache.lookup (c.leaveOut, c.knn, c.coUse, c.postingCap) with
      | some st => pure st
      | none =>
        let st := Stats.build pl c.leaveOut c.knn c.coUse s.fit s.val c.postingCap
        cache := ((c.leaveOut, c.knn, c.coUse, c.postingCap), st) :: cache
        pure st
    match validate c pl s st log with
    | .error e => if log then IO.println s!"validation: {c.describe}: bound error {repr e}"
    | .ok (e, rr, mags) =>
      if log && grid.length ≤ 24 then
        IO.println s!"validation baselines: IDF {showReranked (rerankItems ks 30 pl s.val (idfRankScore pl))}; name-IDF {showReranked (rerankItems ks 30 pl s.val (nameRankScore pl))}; votes {showReranked (rerankItems ks 30 pl s.val (knnRankScore pl st))}"
      if log then
        IO.println s!"validation: {c.describe}: {", ".intercalate (e.summary.map fun (k, v) => s!"{k} {v}")}; {showReranked rr}; {mags}"
      if best.all (·.2 < e.rrMicro) then best := some (c, e.rrMicro)
  return best.map (·.1)

/-- A scorer trained on a whole training split. -/
structure Fitted where
  config : ScorerConfig
  stats : Stats
  /-- The first member's groups. -/
  groups : Array Group
  models : Array ScorerModel
  trainMs : Nat

def Fitted.prior (f : Fitted) : Prior := f.stats.prior

def Fitted.digest (f : Fitted) : Digest :=
  digestOf "premises/scorer" (f.models.toList.flatMap fun m => m.es.toList ++ m.ep.toList ++ m.wc.toList)

def Fitted.score (f : Fitted) (pl : PreparedLib) : Item Addr → Array Nat → Array Int :=
  ensembleScore f.config pl f.stats f.models

/-- Train config `c` on the split's training set. -/
def fitScorer (c : ScorerConfig) (pl : PreparedLib) (s : SplitData) : IO (Except BoundError Fitted) := do
  let stats := Stats.build pl c.leaveOut c.knn c.coUse s.train s.test c.postingCap
  let groups := groupsOf c pl s.train
  let t0 ← IO.monoMsNow
  match trainEnsemble c pl stats s.train with
  | .error e => return .error e
  | .ok models =>
    let t1 ← IO.monoMsNow
    return .ok { config := c, stats, groups, models, trainMs := t1 - t0 }

def runBilinear (base : ScorerConfig) (grid : String) (pl : PreparedLib) (s : SplitData) (k : SplitKind) :
    IO Json := do
  let some c ← selectScorer base pl s (grid := namedGrid grid k base) | IO.eprintln "every config left its bounds"; return Json.null
  match ← fitScorer c pl s with
  | .error e => IO.eprintln s!"training left its bounds: {repr e}"; return Json.null
  | .ok f =>
    let weights := f.digest
    let groups := f.groups
    let triples := (groups.map fun g => g.pos.size * g.neg.size).foldl (· + ·) 0
    IO.println s!"bilinear scorer: {c.describe}, dim {c.dim}, {groups.size} theorems, {triples} triples per epoch, trained in {f.trainMs} ms; model {weights}"
    IO.println s!"pair weights {f.models.map (·.wc)}"
    let e := evalRanking ks pl s.test (f.score pl)
    showRank "bilinear model" e
    IO.println s!"bilinear model {showReranked (rerankItems ks 30 pl s.test (f.score pl))}"
    if c.knn > 0 then showRank "neighbour-vote baseline" (evalRanking ks pl s.test (knnRankScore pl f.stats))
    let bs ← baselines pl f.prior s.test
    return Json.mkObj ([("model", Json.mkObj [
        ("scorer", toJson "IxAIData.Scorer: φ(x)ᵀ Eₛᵀ Eₚ ψ(p) + wᵀ c(x, p), Fx16, pairwise hinge loss"),
        ("config", toJson s!"{repr c}"), ("modelDigest", toJson (toString weights)),
        ("trainingTheorems", toJson groups.size), ("triplesPerEpoch", toJson triples),
        ("recall", evalJson e)])] ++ bs)

/-- The relevance MLP's margin for every candidate, through the split scorer. -/
def mlpScore (m : Model) (f : Features) (pl : PreparedLib) (prior : Prior) :
    Item Addr → Array Nat → Array Int :=
  let s := Scorer.of m f
  let parts := pl.prep.map fun p =>
    (s.part s.width (stmtX f p.premise.stmt), constCounts f.buckets addrKey p.premise.stmt)
  fun it cs =>
    let sp := s.part 0 (stmtX f it.thm.stmt)
    let sc := constCounts f.buckets addrKey it.thm.stmt
    cs.map fun j =>
      let (pp, pc) := parts[j]!
      s.margin sp pp (pairPart sc pc (contextOf pl.lib prior it.thm pl.prep[j]!.premise))

def runMlp (lib : Library) (pl : PreparedLib) (sd : SplitData) : IO Json := do
  let fitPrior := priorOf sd.fit
  let mut best : Option ((Features × Config) × Nat) := none
  for (f, g) in grid do
    let fitPairs := pairsOf lib (pairConfig f) fitPrior sd.fit
    let cfg := { g with trainSize := fitPairs.length }
    let m := train (spec f fitPairs) cfg
    let e := evalRanking ks pl sd.val (mlpScore m f pl fitPrior)
    IO.println s!"validation: statements {f.statements}, batch {g.batch}, epochs {g.epochs}: {", ".intercalate (e.summary.map fun (k, v) => s!"{k} {v}")}"
    if best.all (·.2 < e.rrMicro) then best := some ((f, g), e.rrMicro)
  let some ((feat, chosen), _) := best | IO.eprintln "empty grid"; return Json.null
  let prior := priorOf sd.train
  let pc := pairConfig feat
  let pairs := pairsOf lib pc prior sd.train
  let s := spec feat pairs
  let cfg := { chosen with trainSize := pairs.length }
  let m := train s cfg
  let weights := digestOf "premises/model" ((m.w1.flatten ++ m.b1 ++ m.w2.flatten ++ m.b2).map (·.raw))
  let sample := (sd.test.take 20).flatMap fun it => (lib.premises.toList.take 50).map fun p => (it.thm, p)
  IO.println s!"relevance MLP: chosen {repr feat}, {repr cfg}; model {weights}; split scorer agrees with Model.outputs: {fastScore_agrees m feat lib prior sample}"
  let e := evalRanking ks pl sd.test (mlpScore m feat pl prior)
  showRank "relevance MLP" e
  let bs ← baselines pl prior sd.test
  return Json.mkObj ([("model", Json.mkObj [
      ("spec", toJson "IxAIData.spec: premise-relevance, one Bool question, IxAICore.train"),
      ("featurizer", toJson s!"{repr feat}"), ("config", toJson s!"{repr cfg}"),
      ("modelDigest", toJson (toString weights)), ("trainingPairs", toJson pairs.length),
      ("recall", evalJson e)])] ++ bs)

/-- A scope's extraction, curated and split into train and test modules. -/
structure Loaded where
  ex : Extraction
  policy : Policy Addr
  testIdx : List Nat
  curated : Curated

def load (scope : Scope) : IO (Except String Loaded) := do
  let ex ← readExtraction (datasetsDir / scope.name)
  match policyOf ex with
  | .error e => return .error e
  | .ok policy =>
    let testIdx := (List.range ex.modules.size).filter fun i => scope.isTest (ex.modules[i]!.name)
    let testSet : Std.HashSet Nat := testIdx.foldl (·.insert ·) {}
    return .ok { ex, policy, testIdx, curated := curate ex policy (testSet.contains ·) }

/-- Peak resident memory of this process, from `/proc/self/status`. -/
def peakRss : IO String := do
  try
    let ls ← IO.FS.lines "/proc/self/status"
    return ((ls.find? (·.startsWith "VmHWM")).map fun l => (l.drop 6).trimAscii.toString).getD "?"
  catch _ => return "?"

def run (scope : Scope) (opts : Options) : IO UInt32 := do
  let dir := datasetsDir / scope.name
  let opts := if scope.large then { opts with train := false } else opts
  let t0 ← IO.monoMsNow
  let ld ← match ← load scope with
    | .ok ld => pure ld
    | .error e => IO.eprintln e; return 1
  let ex := ld.ex
  IO.println s!"read {ex.items.size} items and {ex.library.size} library theorems in {(← IO.monoMsNow) - t0} ms"
  let t1 ← IO.monoMsNow
  let policy := ld.policy
  let testIdx := ld.testIdx
  let c := ld.curated
  IO.println s!"modules {ex.modules.size}, library theorems {ex.library.size}, scope theorems {ex.items.size}, unaddressed names {ex.unjoined}"
  IO.println s!"accepted {c.accepted.length} (refused: {c.refusals.map fun (r, n) => s!"{repr r} {n}"})"
  IO.println s!"after dedup {c.deduped.length}, with premises {c.nonempty.length}"
  IO.println s!"split: train {c.train.length}, test {c.test.length} from {testIdx.length} modules; dropped by the dependency rule {c.nonempty.length - c.train.length - c.test.length}; disjoint {c.disjoint}"
  IO.println s!"curated in {(← IO.monoMsNow) - t1} ms"
  let agrees := premiseRuleAgrees ex c
  IO.println s!"premise rule (pure List form) agrees with the host filter: {agrees}"
  -- Commit.
  let trainLeaves := c.train.map (itemLeaf ex.modules "train")
  let testLeaves := c.test.map (itemLeaf ex.modules "test")
  let rootLeaves := sortAddrs ((c.train ++ c.test).map Item.addr)
  let root := merkleRootV2 rootLeaves
  let recordsRoot := merkleRootV2 (trainLeaves ++ testLeaves)
  let rootsV1 := Json.mkObj [
    ("root", toJson (toString (merkleRootV1 rootLeaves))),
    ("recordsRoot", toJson (toString (merkleRootV1 (trainLeaves ++ testLeaves)))),
    ("note", toJson rootsV1Note)]
  let itemsPath := datasetsDir / s!"{scope.name}.items.tsv"
  let line := fun (sp : String) (it : Item Addr) =>
    s!"{sp}\t{it.addr}\t{(ex.modules[it.module]?.map (·.name)).getD ""}\t{",".intercalate (it.premises.map toString)}"
  IO.FS.writeFile itemsPath ("\n".intercalate (c.train.map (line "train") ++ c.test.map (line "test")) ++ "\n")
  let itemsDigest := blake3 (← IO.FS.readBinFile itemsPath)
  IO.println s!"dataset root {root}; records root {recordsRoot} ({rootFormat}); items {itemsPath} BLAKE3 {itemsDigest}; committed at {(← IO.monoMsNow) - t0} ms"
  IO.println s!"version 1 roots of the same leaves (for recorded artifacts only): {merkleRootV1 rootLeaves}, {merkleRootV1 (trainLeaves ++ testLeaves)}"
  let pl := if opts.train then PreparedLib.of opts.scorerConfig.features (Library.of ex) else
    { lib := { premises := #[], names := #[], constNames := {}, byAddr := {}, byModule := #[], reach := #[],
               ancestors := #[], docFreq := {} }, prep := #[], index := {} }
  let lib := pl.lib
  let mut results : List (String × Json) := []
  for sp in opts.splits do
    let t2 ← IO.monoMsNow
    let s := splitOf scope ex c sp
    IO.println s!"== split {s.name}: train {s.train.length}, test {s.test.length} ({s.dropped} dropped by the dependency rule), fit {s.fit.length}, validation {s.val.length}; disjoint {disjointFast s.train s.test}, validation disjoint {disjointFast s.fit s.val}; {(← IO.monoMsNow) - t2} ms"
    let j ← if !opts.train then pure Json.null else match opts.scorer with
      | .mlp => runMlp lib pl s
      | .bilinear => runBilinear opts.scorerConfig opts.grid pl s sp
    results := results ++ [(s.name, Json.mkObj [("rule", toJson s.rule), ("train", toJson s.train.length),
      ("test", toJson s.test.length), ("fit", toJson s.fit.length), ("validation", toJson s.val.length),
      ("dropped", toJson s.dropped), ("disjointChecked", toJson (disjointFast s.train s.test)),
      ("validationDisjointChecked", toJson (disjointFast s.fit s.val)), ("results", j)])]
  IO.println s!"total {(← IO.monoMsNow) - t0} ms, peak RSS {← peakRss}"
  let counts := Json.mkObj [
      ("modules", toJson (ex.modules.size)), ("libraryTheorems", toJson (ex.library.size)),
      ("scopeTheorems", toJson (ex.items.size)), ("unaddressedNames", toJson (ex.unjoined)),
      ("accepted", toJson (c.accepted.length)),
      ("refused", Json.mkObj (c.refusals.map fun (r, n) => (toString (repr r), toJson n))),
      ("deduped", toJson (c.deduped.length)), ("withPremises", toJson (c.nonempty.length)),
      ("train", toJson (c.train.length)), ("test", toJson (c.test.length))]
  let itemsJson := Json.mkObj [("path", toJson (toString itemsPath)), ("blake3", toJson (toString itemsDigest))]
  let mpath := datasetsDir / s!"{scope.name}.json"
  if !opts.train && !scope.large then
    -- Curation only: refresh the commitment fields of an existing manifest and keep its
    -- evaluation, which is marked stale if the committed items changed.
    if ← mpath.pathExists then
      match Json.parse (← IO.FS.readFile mpath) with
      | .ok old =>
        let oldItems := ((old.getObjValD "items").getObjValAs? String "blake3").toOption
        let stale := oldItems != some (toString itemsDigest)
        let m := old
          |>.setObjVal! "root" (toJson (toString root))
          |>.setObjVal! "recordsRoot" (toJson (toString recordsRoot))
          |>.setObjVal! "rootFormat" (toJson rootFormat)
          |>.setObjVal! "rootsV1" rootsV1
          |>.setObjVal! "counts" counts
          |>.setObjVal! "items" itemsJson
          |>.setObjVal! "policy" ((old.getObjValD "policy").setObjVal! "acceptance" (toJson acceptanceText))
        let m := if stale then m.setObjVal! "evaluationStale"
            (toJson "the committed items changed since the evaluation was run; rerun `ixai premises run`")
          else m
        IO.FS.writeFile mpath (m.pretty ++ "\n")
        IO.println s!"manifest {mpath}: commitment refreshed; evaluation {if stale then "stale (items changed)" else "kept (same items)"}"
      | .error e => IO.eprintln s!"manifest {mpath} unreadable ({e}); left unchanged"
    return 0
  -- Manifest.
  let source ← readSource dir
  let root0 ← envRoot dir
  let mfst := Json.mkObj [
    ("dataset", toJson (s!"premises/{scope.name}")),
    ("source", Json.mkObj (source.map fun (k, v) => (k, Json.str v))),
    ("environment", Json.mkObj [("ixe", toJson (toString (dir / "scope.ixe"))),
                                ("envRoot", toJson root0),
                                ("ixvm", toJson "5111b234907cf3ab87d43ac6673617c752b3a37fb0ca7485b60d9d7081f02576")]),
    ("policy", Json.mkObj [
      ("acceptance", toJson acceptanceText),
      ("allowedAxioms", Json.arr (policy.allowedAxioms.map (Json.str ∘ toString)).toArray),
      ("sorryAx", toJson (toString policy.sorryAx)),
      ("items", toJson (s!"theorems of modules under {scope.pfx} in the import closure of {scope.modules}, without internal names")),
      ("premises", toJson ("library theorems (outside Init, Std, Lean) in the proof term, other than the theorem itself")),
      ("dedup", toJson ("first item per Ixon address")),
      ("nonempty", toJson ("items with at least one premise")),
      ("rules", toJson ("IxAIData/Rules.lean"))]),
    ("split", Json.mkObj [
      ("testModules", Json.arr ((if scope.sample > 0 then testIdx.map fun i => ex.modules[i]!.name
        else scope.testModules).map Json.str).toArray),
      ("rule", toJson "test = items of the test modules; train = other items that are not test theorems and use no test theorem as a premise (IxAIData.split_disjoint, split_addr_disjoint)"),
      ("disjointChecked", toJson c.disjoint)]),
    ("evaluation", Json.mkObj ([("scorer", toJson (if opts.train then (repr opts.scorer).pretty else "not trained here; `ixai bench mathlib-full`"))] ++ results)),
    ("counts", counts),
    ("root", toJson (toString root)),
    ("recordsRoot", toJson (toString recordsRoot)),
    ("rootFormat", toJson rootFormat),
    ("rootsV1", rootsV1),
    ("items", itemsJson)]

  IO.FS.writeFile mpath (mfst.pretty ++ "\n")
  IO.println s!"manifest {mpath}"
  return 0

def extract (scope : Scope) : IO UInt32 := do
  let child ← IO.Process.spawn { cmd := (projectDir / "ix" / "premises" / "extract.sh").toString
                                 args := #[scope.name, ",".intercalate scope.modules, scope.pfx] }
  child.wait

def parseFlags (o : Options) : List String → Option Options
  | [] => some o
  | "--scorer" :: "bilinear" :: rest => parseFlags { o with scorer := .bilinear } rest
  | "--scorer" :: "mlp" :: rest => parseFlags { o with scorer := .mlp } rest
  | "--split" :: "module" :: rest => parseFlags { o with splits := [.module] } rest
  | "--split" :: "time" :: rest => parseFlags { o with splits := [.time] } rest
  | "--split" :: "both" :: rest => parseFlags { o with splits := [.module, .time] } rest
  | "--grid" :: g :: rest => parseFlags { o with grid := g } rest
  | "--no-train" :: rest => parseFlags { o with train := false } rest
  | _ => none

def main (args : List String) : IO UInt32 := do
  let usage := do
    IO.eprintln "usage: ixai premises extract SCOPE | ixai premises run SCOPE [--scorer bilinear|mlp] [--split module|time|both] [--grid NAME] [--no-train]"
    return (2 : UInt32)
  let cmd :: name :: flags := args | usage
  let some opts := parseFlags {} flags | usage
  let some scope := scopes.find? (·.name == name)
    | IO.eprintln s!"unknown scope {name}; scopes: {scopes.map (·.name)}"; return 2
  match cmd with
  | "extract" => extract scope
  | "run" => run scope opts
  | _ => usage

end IxAIData
