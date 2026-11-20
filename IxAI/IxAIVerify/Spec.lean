import IxAICore
import IxAICommon.Merkle

/-!
# The expected job, from the specification alone

Everything a verifier compares proofs against is computed here from `IxAICore` and a config: the
examples, the schedule, the initial weights, the dataset root and the words of every expected
claim. None of it runs SGD: `Model.step` is never called. Intermediate models come from the
prover and are checked by the proofs, anchored at `config.init` and at the submitted model.

Claim encoding (version `stepClaimEncoding`): a model is its 331 parameters in `w1 ‖ b1 ‖ w2 ‖ b2`
order, row by row, as raw fixed-point integers; a batch is its 20 feature rows (8 each) then its
20 target rows (11 each); words are signed integers in canonical decimal form, read modulo the
Goldilocks prime, and every model word lies in the weight range (`checkModelWords`).
* `Fixed::step`: arguments `m ‖ xs ‖ ts ‖ lr`, output `step lr m batch`.
* `Fixed::train`: arguments `m₀ ‖ lr ‖ xs₀ ‖ … ‖ xs₅₉₉ ‖ ts₀ ‖ … ‖ ts₅₉₉`, output the final model.
-/

namespace IxAIVerify

open IxAI IxAICore

/-- The certified configs of the triage model. -/
def triageConfigs : List (String × Config) :=
  [("tiny", { seed := 42, hidden := 4, lrRaw := 2, epochs := 1, batch := 8, trainSize := 16, testSize := 16 }),
   ("small", { seed := 42, hidden := 8, lrRaw := 2, epochs := 2, batch := 16, trainSize := 64, testSize := 32 }),
   ("medium", { seed := 42, hidden := 16, lrRaw := 2, epochs := 3, batch := 20, trainSize := 400, testSize := 200 }),
   ("large", { seed := 42, hidden := 16, lrRaw := 2, epochs := 10, batch := 20, trainSize := 400, testSize := 200 }),
   ("full", { seed := 42, hidden := 16, lrRaw := 2, epochs := 30, batch := 20, trainSize := 400, testSize := 200 })]

def configNamed? (name : String) : Option Config := (triageConfigs.find? (·.1 == name)).map (·.2)

instance : Enc Config :=
  ⟨fun b c => Enc.enc (Enc.enc (Enc.enc (Enc.enc (Enc.enc (Enc.enc (Enc.enc b c.seed) c.hidden)
    c.lrRaw) c.epochs) c.batch) c.trainSize) c.testSize⟩

def configDigest (c : Config) : Digest := digestOf "job/config" c

def rawOfModel (m : Model) : List Int := (m.w1.flatten ++ m.b1 ++ m.w2.flatten ++ m.b2).map (·.raw)

def modelOfRaw (hidden : Nat) (raw : List Int) : Model :=
  let ws := raw.map (⟨·⟩ : Int → Fx)
  { w1 := reshape 8 hidden ws
    b1 := (ws.drop (hidden * 8)).take hidden
    w2 := reshape hidden 11 (ws.drop (hidden * 8 + hidden))
    b2 := (ws.drop (hidden * 8 + hidden + 11 * hidden)).take 11 }

def paramCount (hidden : Nat) : Nat := hidden * 8 + hidden + 11 * hidden + 11

/-- The weight commitment of a model. -/
def modelDigest (m : Model) : Digest := digestOf "weights" (rawOfModel m)

def examplesOf (c : Config) : List (List Fx × List Fx) :=
  (c.data Triage.spec).map Triage.spec.example

/-- The dataset leaf of one example. -/
def exampleLeaf (e : List Fx × List Fx) : Digest :=
  digestOf "job/example" (e.1.map (·.raw), e.2.map (·.raw))

/-- The dataset root: the length-binding Merkle root of the examples, in order. -/
def datasetRoot (c : Config) : Digest := merkleRootV2 ((examplesOf c).map exampleLeaf)

def batchOf (examples : List (List Fx × List Fx)) (idx : List Nat) : List (List Fx × List Fx) :=
  idx.map fun k => getD examples k (Triage.spec.example default)

def batchWords (batch : List (List Fx × List Fx)) : List Int × List Int :=
  ((batch.map (·.1)).flatten.map (·.raw), (batch.map (·.2)).flatten.map (·.raw))

/-- `Fixed::step` arguments for one step from `m` on `batch`. -/
def stepArgs (c : Config) (m : List Int) (batch : List (List Fx × List Fx)) : List Int :=
  let (xs, ts) := batchWords batch
  m ++ xs ++ ts ++ [c.lrRaw]

/-- `Fixed::train` arguments for the whole schedule from `config.init`. -/
def trainArgs (c : Config) : List Int :=
  let ex := examplesOf c
  let words := c.schedule.map fun idx => batchWords (batchOf ex idx)
  rawOfModel (c.init Triage.spec) ++ [c.lrRaw] ++ (words.map (·.1)).flatten ++ (words.map (·.2)).flatten

/-- The claim encoding this verifier implements; a commitment names it by this text's digest. -/
def stepClaimEncoding : String :=
  "ixai-aiur-claims-v1: model = w1 ‖ b1 ‖ w2 ‖ b2 raw Fx (row-major); batch = 20×8 features ‖ 20×11 targets; " ++
  "Fixed::step(m ‖ xs ‖ ts ‖ lr) = m'; Fixed::train(m0 ‖ lr ‖ xs_0..xs_599 ‖ ts_0..ts_599) = m_600; " ++
  "AiurExec::aiur_exec over Fixed::step (aiur_exec_check layout); signed words mod 2^64 - 2^32 + 1"

def claimEncodingDigest : Digest := digestOf "job/claim-encoding" stepClaimEncoding

def goldilocks : Int := 18446744069414584321

def decodeField (n : Nat) : Int := if (n : Int) > goldilocks / 2 then (n : Int) - goldilocks else n

def joinInts (xs : List Int) : String := " ".intercalate (xs.map toString)

def words (line : String) : List String :=
  ((line.map fun c => if c == '\t' || c == '\r' then ' ' else c).splitOn " ").filter (· ≠ "")

/-- The integer a word spells, if it is in canonical decimal form: `0`, or digits without a leading
zero, optionally after `-` (never `-0`). Every integer has exactly one accepted spelling, so the
text of a model determines its words. -/
def canonicalInt? (w : String) : Option Int :=
  let (neg, ds) := match w.toList with
    | '-' :: ds => (true, ds)
    | ds => (false, ds)
  if ds.isEmpty || !ds.all Char.isDigit then none
  else if ds.length > 1 && ds.head? == some '0' then none
  else if neg && ds == ['0'] then none
  else
    let n := ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
    some (if neg then -(n : Int) else n)

def parseInts (ws : List String) : Except String (List Int) :=
  ws.mapM fun w => match canonicalInt? w with
    | some i => pure i
    | none => throw s!"not a canonical integer: {String.ofList (w.toList.take 40)}"

/-- The signed range of every weight word: `Fixed`'s `bound` accepts `v` exactly when
`-4096 ≤ v < 4320` (`ix/aiur/FixedSoundness.lean`), and the refinement theorems read the circuit's
field elements as integers in that range. A model outside it has no integer reading that the
proofs cover, and two integers that agree modulo the field would have one proof and two digests. -/
def weightLo : Int := -4096
def weightHi : Int := 4320

/-- The first word of `raw` outside the weight range, with its index. -/
def outOfRange (raw : List Int) : Option (Nat × Int) :=
  (raw.zipIdx.find? fun (w, _) => w < weightLo || w ≥ weightHi).map fun (w, i) => (i, w)

/-- A model's words, checked: exactly `paramCount hidden` of them, each in the weight range. Run on
every model before it is hashed, encoded into a claim or compared. -/
def checkModelWords (hidden : Nat) (raw : List Int) : Except String Unit := do
  unless raw.length == paramCount hidden do
    throw s!"{raw.length} parameters, not {paramCount hidden}"
  if let some (i, w) := outOfRange raw then
    throw s!"parameter {i} is {w}, outside the weight range [{weightLo}, {weightHi})"

end IxAIVerify
