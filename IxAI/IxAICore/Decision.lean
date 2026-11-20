import IxAICore.Fx
import IxAICore.Rng

/-!
# Typed decision models

A decision model answers fixed questions about a state, like Jev or the Decisions APIs, but every
answer has a Lean type. A question with answer type `α` is decided by the specification: the
spec supplies the function `σ → α` that defines the right answer, so training labels are computed,
never annotated or learned.

The model is a small network with a shared hidden layer and one output per possible answer of
every question. It is trained by squared error against one-hot targets (the Brier score, a proper
scoring rule), so each output estimates the probability of its answer. The typed answer is the
`α` value at the largest output.

Training is a pure function of the specification and the configuration. Every gradient entry is
an exact sum over the batch, rounded once, so the result does not depend on the order of
accumulation, and an independent implementation reproduces it bit for bit.
-/

namespace IxAICore

/-- Lean types usable as answers: finitely many values in a fixed order. -/
class Finite (α : Type) where
  all : List α
  index : α → Nat

instance : Finite Bool := ⟨[false, true], fun b => if b then 1 else 0⟩

/-- A question about states of type `σ` with answers of type `α`, decided by the specification. -/
structure Question (σ α : Type) [Finite α] where
  name : String
  decide : σ → α

/-- A question with its answer type erased to answer positions. -/
structure Slot (σ : Type) where
  name : String
  arity : Nat
  target : σ → Nat

def Question.slot {σ α : Type} [Finite α] (q : Question σ α) : Slot σ :=
  ⟨q.name, (Finite.all : List α).length, fun s => Finite.index (q.decide s)⟩

/-- A decision specification: how states are generated, what the model sees, and which questions
it must answer. -/
structure Spec (σ : Type) where
  name : String
  features : σ → List Int
  numFeatures : Nat
  slots : List (Slot σ)
  sample : Rng → σ × Rng

def Spec.outputs {σ : Type} (s : Spec σ) : Nat := (s.slots.map (·.arity)).foldl (· + ·) 0

/-- One-hot targets for every question, concatenated. -/
def Spec.targets {σ : Type} (s : Spec σ) (st : σ) : List Fx :=
  s.slots.flatMap fun q => (List.range q.arity).map fun k => if k == q.target st then Fx.one else Fx.zero

def Spec.inputs {σ : Type} (s : Spec σ) (st : σ) : List Fx := (s.features st).map Fx.ofInt

def Spec.sampleN {σ : Type} (s : Spec σ) : Nat → Rng → List σ × Rng
  | 0, r => ([], r)
  | n + 1, r =>
    let (x, r) := s.sample r
    let (xs, r) := s.sampleN n r
    (x :: xs, r)

structure Model where
  w1 : List (List Fx)
  b1 : List Fx
  w2 : List (List Fx)
  b2 : List Fx
  deriving DecidableEq, Repr, Inhabited

def Model.hidden (m : Model) (x : List Fx) : List Fx × List Fx :=
  let z := List.zipWith (fun row b => Fx.add (Fx.dot row x) b) m.w1 m.b1
  (z, z.map Fx.relu)

def Model.outputs (m : Model) (x : List Fx) : List Fx :=
  let h := (m.hidden x).2
  List.zipWith (fun row b => Fx.add (Fx.dot row h) b) m.w2 m.b2

/-- Split a flat output vector into the questions' answer groups. -/
def splitByArity {σ : Type} : List (Slot σ) → List Fx → List (List Fx)
  | [], _ => []
  | q :: qs, os => os.take q.arity :: splitByArity qs (os.drop q.arity)

/-- Probabilities from outputs: clamp to `[0, 1]` and normalize; uniform if every output is zero
or negative. Values are in units of `1/256`. -/
def probabilities (os : List Fx) : List Fx :=
  let cs := os.map Fx.clamp01
  let total := Fx.sumRaw cs
  if total ≤ 0 then os.map fun _ => ⟨(256 : Int) / os.length⟩
  else cs.map fun c => ⟨c.raw * 256 / total⟩

/-- A typed answer and the probability of each possible answer. -/
structure Answer (α : Type) where
  value : α
  probs : List Fx

/-- Ask the model one question of the spec, at the given answer-group position. -/
def Model.ask {σ α : Type} [Finite α] [Inhabited α] (m : Model) (s : Spec σ) (pos : Nat)
    (st : σ) : Answer α :=
  let group := getD (splitByArity s.slots (m.outputs (s.inputs st))) pos []
  ⟨getD (Finite.all : List α) (argmax group) default, probabilities group⟩

/-! ## Training -/

structure Config where
  seed : Nat
  hidden : Nat
  /-- Learning rate as `lrRaw / 256`, already divided by the batch size. -/
  lrRaw : Int
  epochs : Nat
  batch : Nat
  trainSize : Nat
  testSize : Nat
  deriving DecidableEq, Repr

def chunk {α : Type} (k : Nat) (l : List α) : Nat → List (List α)
  | 0 => []
  | fuel + 1 => if l.isEmpty then [] else l.take k :: chunk k (l.drop k) fuel

def Config.data {σ : Type} (c : Config) (s : Spec σ) : List σ := (s.sampleN c.trainSize (Rng.seeded c.seed)).1

def Config.test {σ : Type} (c : Config) (s : Spec σ) : List σ :=
  (s.sampleN c.testSize (Rng.seeded (c.seed + 1000003))).1

/-- Batches of training-set indices: every epoch is a fresh shuffle cut into batches. -/
def Config.schedule (c : Config) : List (List Nat) :=
  let rec go : Nat → Rng → List (List Nat)
    | 0, _ => []
    | e + 1, r =>
      let (perm, r) := shuffle (List.range c.trainSize) r
      chunk c.batch perm c.trainSize ++ go e r
  go c.epochs (Rng.seeded (c.seed + 7))

def reshape (cols : Nat) : Nat → List Fx → List (List Fx)
  | 0, _ => []
  | rows + 1, xs => xs.take cols :: reshape cols rows (xs.drop cols)

/-- Initial weights, uniform in `[-16/256, 16/256]`, drawn in parameter order. -/
def Config.init {σ : Type} (c : Config) (s : Spec σ) : Model :=
  let nIn := s.numFeatures
  let nOut := s.outputs
  let count := c.hidden * nIn + c.hidden + nOut * c.hidden + nOut
  let ws := ((Rng.seeded (c.seed + 3)).draws 33 count).1.map fun (v : Nat) => Fx.ofRaw (Int.ofNat v - 16)
  { w1 := reshape nIn c.hidden ws
    b1 := (ws.drop (c.hidden * nIn)).take c.hidden
    w2 := reshape c.hidden nOut (ws.drop (c.hidden * nIn + c.hidden))
    b2 := (ws.drop (c.hidden * nIn + c.hidden + nOut * c.hidden)).take nOut }

/-- What one example contributes to the batch gradient of `½ Σ (o − t)²`. -/
structure Delta where
  x : List Fx
  h : List Fx
  dz : List Fx
  dout : List Fx

/-- The first `n` columns of a list of rows, each column as a list. Built once per use, so later
indexing is linear rather than quadratic. -/
def transposeN : Nat → List (List Fx) → List (List Fx)
  | 0, _ => []
  | n + 1, rows => rows.map (·.headD Fx.zero) :: transposeN n (rows.map (·.tail))

/-- `w2T` is the transpose of `m.w2`: row `j` holds every output's weight from hidden unit `j`. -/
def Model.delta (m : Model) (w2T : List (List Fx)) (x t : List Fx) : Delta :=
  let (z, h) := m.hidden x
  let o := List.zipWith (fun row b => Fx.add (Fx.dot row h) b) m.w2 m.b2
  let dout := List.zipWith Fx.sub o t
  let dz := List.zipWith (fun zj col => if Fx.pos zj then Fx.dot col dout else Fx.zero) z w2T
  ⟨x, h, dz, dout⟩

/-- One SGD step. Every gradient entry is an exact sum over the batch, rounded once. -/
def Model.step (lr : Fx) (m : Model) (batch : List (List Fx × List Fx)) : Model :=
  if batch.isEmpty then m else
  let hidden := m.b1.length
  let w2T := transposeN hidden m.w2
  let ds := batch.map fun (x, t) => m.delta w2T x t
  let upd := fun (w g : Fx) => Fx.sub w (Fx.mul lr g)
  let dzT := transposeN hidden (ds.map (·.dz))
  let xT := transposeN (getD m.w1 0 []).length (ds.map (·.x))
  let hT := transposeN hidden (ds.map (·.h))
  let doutT := transposeN m.b2.length (ds.map (·.dout))
  { w1 := List.zipWith (fun row dzj => List.zipWith (fun w xi => upd w (Fx.dot dzj xi)) row xT) m.w1 dzT
    b1 := List.zipWith (fun b dzj => upd b (Fx.sum dzj)) m.b1 dzT
    w2 := List.zipWith (fun row dk => List.zipWith (fun w hj => upd w (Fx.dot dk hj)) row hT) m.w2 doutT
    b2 := List.zipWith (fun b dk => upd b (Fx.sum dk)) m.b2 doutT }

def Spec.example {σ : Type} (s : Spec σ) (st : σ) : List Fx × List Fx := (s.inputs st, s.targets st)

def Config.stepFn {σ : Type} [Inhabited σ] (c : Config) (s : Spec σ) (examples : List (List Fx × List Fx))
    (m : Model) (idx : List Nat) : Model :=
  m.step ⟨c.lrRaw⟩ (idx.map fun i => getD examples i (s.example default))

/-- The specified result of training: a pure function of the spec and the config. -/
def train {σ : Type} [Inhabited σ] (s : Spec σ) (c : Config) : Model :=
  let examples := (c.data s).map s.example
  c.schedule.foldl (c.stepFn s examples) (c.init s)

/-! ## Evaluation card -/

/-- Per-question results on the held-out set. Probabilities are in units of `1/256`. -/
structure QuestionCard where
  name : String
  correct : Nat
  total : Nat
  /-- `Σ` over examples of `Σ_k (p_k − t_k)²`, in units of `1/256`. -/
  brierRaw : Int
  /-- Calibration error: `Σ` over four confidence bins of `|Σ confidence − 256 · Σ correct|`. -/
  calibrationRaw : Int
  deriving DecidableEq, Repr

structure Card where
  questions : List QuestionCard
  deriving DecidableEq, Repr

def bin (p : Fx) : Nat := if p.raw < 128 then 0 else if p.raw < 172 then 1 else if p.raw < 214 then 2 else 3

def absInt (i : Int) : Int := if i < 0 then -i else i

def evalQuestion {σ : Type} (m : Model) (s : Spec σ) (test : List σ) (q : Slot σ) (pos : Nat) :
    QuestionCard :=
  let rows := test.map fun st =>
    let group := getD (splitByArity s.slots (m.outputs (s.inputs st))) pos []
    let ps := probabilities group
    let pred := argmax group
    let tgt := q.target st
    let conf := getD ps pred Fx.zero
    let brier := ((withIndex ps 0).map fun (p, k) =>
      let d := p.raw - (if k == tgt then 256 else 0)
      (d * d) >>> 8).foldl (· + ·) 0
    (pred == tgt, brier, bin conf, conf.raw)
  let correct := (rows.filter (·.1)).length
  let calib := ((List.range 4).map fun b =>
    let inBin := rows.filter (·.2.2.1 == b)
    let confSum := (inBin.map (·.2.2.2)).foldl (· + ·) 0
    let hits : Int := (inBin.filter (·.1)).length
    absInt (confSum - 256 * hits)).foldl (· + ·) 0
  { name := q.name, correct, total := test.length
    brierRaw := (rows.map (·.2.1)).foldl (· + ·) 0, calibrationRaw := calib }

def card {σ : Type} (s : Spec σ) (c : Config) (m : Model) : Card :=
  ⟨(withIndex s.slots 0).map fun (q, pos) => evalQuestion m s (c.test s) q pos⟩

end IxAICore
