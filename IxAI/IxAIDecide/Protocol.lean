import IxAIDecide.Card
import IxAIDecide.Fast

/-!
# A training protocol: fan-in initialization, validation, selection, thresholds

`IxAICore.Config.init` draws every weight uniformly in `±16/256`, whatever a layer's fan-in.
`Recipe` keeps a `Config` for the seed, data sizes, schedule and learning rate, and replaces only
the initialization: each layer's weights are uniform in `±gain/√fanIn` and biases start at zero.
`Recipe.train` is then the same fold of `Config.stepFn` over `Config.schedule` as
`IxAICore.train`, from that initialization.

The rest of the protocol is also specified here, so a certificate can cover it:
- `validationSet`: examples from a generator stream of their own;
- `selectRecipe`: the candidate with the best validation accuracy, ties broken by Brier score
  and then by the smaller, shorter setting;
- `thresholdsFrom`: per-option gate thresholds from validation judgments and a target precision;
- `calibration`: per confidence bin, how many held-out answers, how many right, how many the gate
  decided and how many of those right.

Everything is integer arithmetic over `Nat`, `Int` and `Fx`, with structural recursion.
-/

namespace IxAIDecide

open IxAICore

/-- `⌊√n⌋`, by counting up from `k`; `fuel` bounds the steps. -/
def isqrtGo : Nat → Nat → Nat → Nat
  | 0, k, _ => k
  | fuel + 1, k, n => if (k + 1) * (k + 1) ≤ n then isqrtGo fuel (k + 1) n else k

def isqrt (n : Nat) : Nat := isqrtGo n 0 n

/-- `gain / √fanIn` in units of `1/256`, for `gain` in units of `1/256`:
`gain · 16 / ⌊√(256 · fanIn)⌋`. -/
def halfWidth (gainRaw fanIn : Nat) : Nat := gainRaw * 16 / max 1 (isqrt (256 * fanIn))

/-- A configuration and a fan-in-scaled initialization. -/
structure Recipe where
  config : Config
  /-- Initialization gain in units of `1/256`. -/
  gainRaw : Nat
  deriving Repr, DecidableEq

/-- `count` weights uniform in `[-a, a]` (raw), drawn in order. -/
def uniformWeights (r : Rng) (a count : Nat) : List Fx × Rng :=
  let (vs, r) := r.draws (2 * a + 1) count
  (vs.map fun v => Fx.ofRaw (Int.ofNat v - Int.ofNat a), r)

/-- Hidden weights in `±gain/√nIn`, output weights in `±gain/√hidden`, zero biases. -/
def Recipe.init {σ : Type} (r : Recipe) (s : Spec σ) : Model :=
  let c := r.config
  let nIn := s.numFeatures
  let nOut := s.outputs
  let (u, g) := uniformWeights (Rng.seeded (c.seed + 3)) (halfWidth r.gainRaw nIn) (c.hidden * nIn)
  let (v, _) := uniformWeights g (halfWidth r.gainRaw c.hidden) (nOut * c.hidden)
  { w1 := reshape nIn c.hidden u
    b1 := (List.range c.hidden).map fun _ => Fx.zero
    w2 := reshape c.hidden nOut v
    b2 := (List.range nOut).map fun _ => Fx.zero }

/-- The specified result of training a recipe. -/
def Recipe.train {σ : Type} [Inhabited σ] (r : Recipe) (s : Spec σ) : Model :=
  let c := r.config
  c.schedule.foldl (c.stepFn s ((c.data s).map s.example)) (r.init s)

/-- The model after every `every` epochs, as `(epochs, model)`. Equal to `Recipe.train` with
`epochs` set to each checkpoint, because a shorter schedule is a prefix of a longer one. -/
def Recipe.checkpoints {σ : Type} [Inhabited σ] (r : Recipe) (s : Spec σ) (every : Nat) :
    List (Nat × Model) :=
  let c := r.config
  let perEpoch := (c.trainSize + c.batch - 1) / c.batch
  let ex := (c.data s).map s.example
  let step := c.stepFn s ex
  (c.schedule.foldl (fun (acc : Nat × Model × List (Nat × Model)) idx =>
    let (i, m, out) := acc
    let m' := step m idx
    let i' := i + 1
    if i' % (every * perEpoch) == 0 then (i', m', out ++ [(i' / perEpoch, m')]) else (i', m', out))
    (0, r.init s, [])).2.2

/-- Validation examples: `testSize` draws from a stream distinct from training (`seed`) and the
held-out set (`seed + 1000003`). -/
def validationSet {σ : Type} (c : Config) (s : Spec σ) : List σ :=
  (s.sampleN c.testSize (Rng.seeded (c.seed + 2000003))).1

/-- Validation score of a model: examples whose most probable option is the label, and the
Brier sum. -/
def validationScore {ι ω : Type} [Encode ι] [Finite ω] [Inhabited ω] [DecidableEq ω]
    (m : Model) (val : List (Labelled ι ω)) : Nat × Int :=
  val.foldl (fun (acc : Nat × Int) e =>
    let j : Judgment ω := judge m e.input
    (acc.1 + (if j.option == e.label then 1 else 0),
      acc.2 + brierOf j.probs (Finite.index e.label))) (0, 0)

/-- A scored candidate: recipe (with its epochs), model, validation correct count and Brier. -/
structure Candidate where
  recipe : Recipe
  model : Model
  correct : Nat
  brier : Int

/-- `a` is preferred to `b`: more correct; then lower Brier; then fewer epochs, fewer hidden
units, lower learning rate, lower gain. -/
def Candidate.better (a b : Candidate) : Bool :=
  let key := fun (c : Candidate) =>
    (c.recipe.config.epochs, c.recipe.config.hidden, c.recipe.config.lrRaw, c.recipe.gainRaw)
  let ka := key a
  let kb := key b
  if a.correct != b.correct then decide (a.correct > b.correct)
  else if a.brier != b.brier then decide (a.brier < b.brier)
  else if ka.1 != kb.1 then decide (ka.1 < kb.1)
  else if ka.2.1 != kb.2.1 then decide (ka.2.1 < kb.2.1)
  else if ka.2.2.1 != kb.2.2.1 then decide (ka.2.2.1 < kb.2.2.1)
  else decide (ka.2.2.2 < kb.2.2.2)

/-- Every checkpoint of every recipe, scored on validation. -/
def candidates {ι ω : Type} [Encode ι] [Finite ω] [Inhabited ω] [DecidableEq ω]
    [Inhabited (Labelled ι ω)] (t : Task ι ω) (recipes : List Recipe) (every : Nat) :
    List Candidate :=
  recipes.flatMap fun r =>
    let val := validationSet r.config t.spec
    (r.checkpoints t.spec every).map fun (e, m) =>
      let (k, b) := validationScore m val
      ⟨{ r with config := { r.config with epochs := e } }, m, k, b⟩

/-- The preferred candidate, if any. -/
def selectRecipe (cs : List Candidate) : Option Candidate :=
  cs.foldl (fun best c => match best with
    | none => some c
    | some b => if c.better b then some c else some b) none

/-- The protocol's grid for a seed and the task's data sizes: gain 1.0 or 2.45, learning rate 4
or 8, 8 or 16 hidden units, 120 epochs (scored every 20). -/
def grid (base : Config) (seed : Nat) : List Recipe :=
  [256, 627].flatMap fun g => [4, 8].flatMap fun lr => [8, 16].map fun h =>
    ⟨{ base with seed, hidden := h, lrRaw := lr, epochs := 120 }, g⟩

/-! ## Thresholds from validation -/

/-- The smallest threshold in `128, 136, …, 256` at which validation answers of option `o` at
or above it number at least `minCount` and are right at least `num/den` of the time; `257`,
above every probability, if none. -/
def thresholdFor {ω : Type} [DecidableEq ω] (js : List (Judgment ω × ω)) (o : ω)
    (num den minCount : Nat) : Int :=
  let ok := fun (t : Int) =>
    let sel := js.filter fun (j, _) => j.option == o && decide (t ≤ j.confidence)
    let right := (sel.filter fun (_, l) => l == o).length
    decide (minCount ≤ sel.length) && decide (num * sel.length ≤ den * right)
  ((List.range 17).map fun (k : Nat) => (128 + 8 * (k : Int))).find? ok |>.getD 257

/-- Validation judgments of a model, with the labels. -/
def judgments {ι ω : Type} [Encode ι] [Finite ω] [Inhabited ω] (m : Model)
    (val : List (Labelled ι ω)) : List (Judgment ω × ω) :=
  val.map fun e => (judge m e.input, e.label)

/-! ## Thresholds that hold in every bin -/

/-- The bins a threshold rule checks, as `[lo, hi)` in units of `1/256`. -/
def gateBins : List (Int × Int) := [(128, 160), (160, 192), (192, 224), (224, 257)]

/-- Validation answers of option `o` with confidence in `[lo, hi)`: how many, and how many right. -/
def binCounts {ω : Type} [DecidableEq ω] (js : List (Judgment ω × ω)) (o : ω) (lo hi : Int) :
    Nat × Nat :=
  let sel := js.filter fun (j, _) =>
    j.option == o && decide (lo ≤ j.confidence) && decide (j.confidence < hi)
  (sel.length, (sel.filter fun (_, l) => l == o).length)

/-- The lowest bin edge from which every bin holds at least `minCount` answers of `o` meeting
`meets right count`; `257`, above every probability, if there is none. -/
def thresholdPerBin {ω : Type} [DecidableEq ω] (js : List (Judgment ω × ω)) (o : ω)
    (meets : Nat → Nat → Bool) (minCount : Nat) : Int :=
  let ok := fun (k : Nat) => (gateBins.drop k).all fun (lo, hi) =>
    let (n, r) := binCounts js o lo hi
    decide (minCount ≤ n) && meets r n
  match (List.range gateBins.length).find? ok with
  | some k => (getD gateBins k (257, 257)).1
  | none => 257

/-- A fixed precision target `num/den`. -/
def atLeast (num den : Nat) (right count : Nat) : Bool := decide (num * count ≤ den * right)

/-- A rule's `pay` precision on labelled examples: `(right, paid)`. -/
def rulePrecision {ι ω : Type} [DecidableEq ω] (rule : ι → ω) (o : ω) (xs : List (Labelled ι ω)) :
    Nat × Nat :=
  let paid := xs.filter fun e => rule e.input == o
  ((paid.filter fun e => e.label == o).length, paid.length)

/-- The rule's precision `R/P` plus one percentage point: `100·P·r ≥ (100·R + P)·n`. -/
def policyPayTarget (rp : Nat × Nat) (right count : Nat) : Bool :=
  decide ((100 * rp.1 + rp.2) * count ≤ 100 * rp.2 * right)

/-! ## A binomial test on cumulative answers -/

/-- `Σ_{k=r}^{n} C(n,k) · aᵏ · bⁿ⁻ᵏ`: with `p = a/(a + b)`, the upper tail `P(X ≥ r)` of a
binomial `(n, p)` is this over `(a + b)ⁿ`. `C(n,k)` is carried as `C(n,k+1) = C(n,k)·(n−k)/(k+1)`,
an exact division, and `bⁿ⁻ᵏ` as `bⁿ / bᵏ`, also exact when `b > 0`. -/
def binomTailNum (n r a b : Nat) : Nat :=
  if b = 0 then (if r ≤ n then a ^ n else 0) else
  let bn := b ^ n
  ((List.range (n + 1)).foldl (fun (acc : Nat × Nat × Nat × Nat) k =>
      let (c, ak, bk, sum) := acc
      let sum := if r ≤ k then sum + c * ak * (bn / bk) else sum
      (c * (n - k) / (k + 1), ak * a, bk * b, sum)) (1, 1, 1, 0)).2.2.2

/-- The one-sided test at the 95% level that `r` right of `n` shows a precision above
`a/(a + b)`: the binomial upper tail `P(X ≥ r)` at `a/(a + b)` is at most `1/20`. Passing it is
equivalent to the one-sided 95% Clopper–Pearson lower bound being at least `a/(a + b)`. -/
def binomTest (n r a b : Nat) : Bool := decide (20 * binomTailNum n r a b ≤ (a + b) ^ n)

/-- Validation answers of option `o` with confidence at least `e`: how many, and how many right. -/
def cumCounts {ω : Type} [DecidableEq ω] (js : List (Judgment ω × ω)) (o : ω) (e : Int) :
    Nat × Nat :=
  let sel := js.filter fun (j, _) => j.option == o && decide (e ≤ j.confidence)
  (sel.length, (sel.filter fun (_, l) => l == o).length)

/-- The edges a cumulative threshold rule tests. -/
def cumulativeEdges : List Int := [128, 160, 192, 224]

/-- The lowest edge whose cumulative answers (at least `minCount`) pass `binomTest` against
`a/(a + b)`, and above which every edge with at least `minCount` cumulative answers passes too;
`257`, above every probability, if there is none. -/
def thresholdCumulative {ω : Type} [DecidableEq ω] (js : List (Judgment ω × ω)) (o : ω)
    (a b minCount : Nat) : Int :=
  let status := cumulativeEdges.map fun e =>
    let (n, r) := cumCounts js o e
    (e, decide (minCount ≤ n), binomTest n r a b)
  let qualifies := fun (i : Nat) =>
    let (_, tested, passes) := getD status i (257, false, false)
    tested && passes && (status.drop (i + 1)).all fun (_, t, p) => !t || p
  match (List.range status.length).find? qualifies with
  | some i => (getD status i (257, false, false)).1
  | none => 257

/-- `n` validation examples from the validation stream (`seed + 2000003`). The first `testSize`
of them are `validationSet`. -/
def validationSetN {σ : Type} (c : Config) (s : Spec σ) (n : Nat) : List σ :=
  (s.sampleN n (Rng.seeded (c.seed + 2000003))).1

/-- `candidates`, scored on `valSize` validation examples. -/
def candidatesN {ι ω : Type} [Encode ι] [Finite ω] [Inhabited ω] [DecidableEq ω]
    [Inhabited (Labelled ι ω)] (t : Task ι ω) (recipes : List Recipe) (every valSize : Nat) :
    List Candidate :=
  recipes.flatMap fun r =>
    let val := validationSetN r.config t.spec valSize
    (r.checkpoints t.spec every).map fun (e, m) =>
      let (k, b) := validationScore m val
      ⟨{ r with config := { r.config with epochs := e } }, m, k, b⟩

/-! ## Calibration -/

/-- One confidence bin of a model's answers on a labelled set. -/
structure CalibrationRow where
  /-- The bin is `[lo, hi)` in units of `1/256`. -/
  lo : Int
  hi : Int
  /-- Answers whose confidence is in the bin. -/
  count : Nat
  /-- Of those, the answer equals the label. -/
  right : Nat
  /-- Of those, the gate returned the answer. -/
  decided : Nat
  decidedRight : Nat
  /-- Sum of the confidences in the bin. -/
  confSum : Int
  deriving Repr, DecidableEq

def calibrationBins : List (Int × Int) :=
  [(0, 128), (128, 160), (160, 192), (192, 224), (224, 257)]

def calibration {ι ω : Type} [Encode ι] [Finite ω] [Inhabited ω] [DecidableEq ω]
    (m : Model) (g : Gate ω) (test : List (Labelled ι ω)) : List CalibrationRow :=
  let rows := test.map fun e =>
    let j : Judgment ω := judge m e.input
    (j.confidence, j.option == e.label, g.apply j != .defer)
  calibrationBins.map fun (lo, hi) =>
    let inBin := rows.filter fun (c, _, _) => decide (lo ≤ c) && decide (c < hi)
    { lo, hi, count := inBin.length
      right := (inBin.filter (·.2.1)).length
      decided := (inBin.filter (·.2.2)).length
      decidedRight := (inBin.filter fun (_, r, d) => r && d).length
      confSum := (inBin.map (·.1)).foldl (· + ·) 0 }

end IxAIDecide
