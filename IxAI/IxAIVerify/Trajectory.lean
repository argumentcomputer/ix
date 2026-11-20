import IxAI.TrainClaim
import IxAI.Float
import IxAIVerify.Spec

/-!
# Checking a submitted trajectory against the consumer's job

The consumer fixes the job: config, dataset and number format, by name (`namedJobs`) or by the
digest of its encoding (`TrajectoryJob.digest`). The submitted file's header is never the source of
what is checked. A header that names a different job is rejected before any step is read; the steps
are then checked against the consumer's job (`verifyRun`), so the schedule, and with it the number
of steps, is the job's. If the consumer also holds the weights the trainer returned, they must be
the verified result.

Text format, one record per line:

```
config SEED HIDDEN LR_RAW EPOCHS BATCH BOUND
format F
data SEED N DEPTH ROOT        (ROOT: `Dataset.root`, the length-binding `merkleRootV2`)
item LABEL F1 … F8            (data files only)
step I1 I2 …                  (trajectories: the batch indices)
w P1 P2 …                     (trajectories: parameters after the step; fixed-point raw values,
                               or IEEE bit patterns)
```
-/

namespace IxAIVerify

open IxAI

/-- How a value is written in trajectory files. `ofWire` accepts only the words `toWire` writes:
an IEEE value is its bit pattern, a natural number that reads back to itself. -/
class Wire (α : Type) where
  toWire : α → Int
  ofWire : Int → Option α

instance : Wire Fx := ⟨(·.raw), fun i => some ⟨i⟩⟩

instance {fmt : FloatLib.Floats.Formats.BinaryInterchange.FloatFormat} :
    Wire (FloatLib.Floats.Formats.BinaryInterchange.Model fmt) :=
  ⟨fun x => x.toNatBits, fun n =>
    if n < 0 then none else
      let x : FloatLib.Floats.Formats.BinaryInterchange.Model fmt := .ofNatBits n.toNat
      if (x.toNatBits : Int) == n then some x else none⟩

def defaultConfig : TrainConfig :=
  { seed := 7, hidden := 16, lrRaw := 1, epochs := 30, batchSize := 20, bound := 1 <<< 20 }

structure DataSpec where
  seed : UInt64 := 42
  n : Nat := 400
  depth : Nat := 3
  deriving BEq, Repr

def DataSpec.generate (s : DataSpec) : Dataset := Dataset.generate s.seed s.n s.depth

instance : Enc TrainConfig :=
  ⟨fun b c => Enc.enc (Enc.enc (Enc.enc (Enc.enc (Enc.enc (Enc.enc b c.seed) c.hidden) c.lrRaw)
    c.epochs) c.batchSize) c.bound⟩

instance : Enc DataSpec := ⟨fun b s => Enc.enc (Enc.enc (Enc.enc b s.seed) s.n) s.depth⟩

/-- A training job as the consumer specifies it. -/
structure TrajectoryJob where
  config : TrainConfig
  data : DataSpec
  format : String

/-- The job's identity: its config, dataset spec, dataset root and format. -/
def jobDigest (c : TrainConfig) (s : DataSpec) (root : Digest) (fmt : String) : Digest :=
  digestOf "job/trajectory" (c, (s, (root, fmt)))

def TrajectoryJob.root (j : TrajectoryJob) : Digest := j.data.generate.root

def TrajectoryJob.digest (j : TrajectoryJob) : Digest := jobDigest j.config j.data j.root j.format

def namedJobs : List (String × TrajectoryJob) :=
  [("default", ⟨defaultConfig, {}, "fx"⟩), ("default-bf16", ⟨defaultConfig, {}, "bf16"⟩),
   ("default-f32", ⟨defaultConfig, {}, "f32"⟩)]

def configLine (c : TrainConfig) : String :=
  s!"config {c.seed} {c.hidden} {c.lrRaw} {c.epochs} {c.batchSize} {c.bound}"

def dataLine (s : DataSpec) (d : Dataset) : String := s!"data {s.seed} {s.n} {s.depth} {d.root}"

structure Header where
  config : TrainConfig
  data : DataSpec
  root : Digest
  format : String

/-- A natural number written as a canonical integer; negative values are refused, never read as 0. -/
def natOf (what : String) (i : Int) : Except String Nat :=
  if i < 0 then throw s!"{what} is negative ({i})" else pure i.toNat

def seedOf (what : String) (i : Int) : Except String UInt64 := do
  let n ← natOf what i
  if n < 2 ^ 64 then pure n.toUInt64 else throw s!"{what} {n} does not fit 64 bits"

/-- The record kind of a line: its first word. -/
def kindOf (l : String) : String := (words l).headD ""

def headerKinds : List String := ["config", "format", "data"]

def parseHeader (lines : List String) : Except String Header := do
  let only := fun (k : String) => do
    match lines.filter (kindOf · == k) with
    | [l] => pure (some l)
    | [] => pure none
    | _ => throw s!"more than one {k} line"
  let some c ← only "config" | throw "missing config line"
  let some dl ← only "data" | throw "missing data line"
  let fmt ← match ← only "format" with
    | none => pure "fx"
    | some l => match words l with
      | [_, f] => pure f
      | _ => throw "malformed format line"
  let cv ← parseInts (words c).tail
  let some root := (words dl)[4]?.bind Digest.ofHex? | throw "malformed dataset root"
  unless (words dl).length == 5 do throw "malformed data line"
  let dv ← parseInts ((words dl).tail.take 3)
  match cv, dv with
  | [seed, h, lr, ep, bs, bound], [dseed, n, depth] =>
    pure { config := { seed := ← seedOf "seed" seed, hidden := ← natOf "hidden" h, lrRaw := lr,
                       epochs := ← natOf "epochs" ep, batchSize := ← natOf "batch" bs, bound }
           data := { seed := ← seedOf "dataset seed" dseed, n := ← natOf "dataset size" n,
                     depth := ← natOf "depth" depth }
           root, format := fmt }
  | _, _ => throw "malformed header"

def Header.digest (h : Header) : Digest := jobDigest h.config h.data h.root h.format

/-- How the submitted header differs from the expected job, if it does. -/
def headerMismatch (job : TrajectoryJob) (h : Header) : Option String :=
  let c := job.config
  let hc := h.config
  if hc.seed != c.seed || hc.hidden != c.hidden || hc.lrRaw != c.lrRaw || hc.epochs != c.epochs ||
      hc.batchSize != c.batchSize || hc.bound != c.bound then
    some s!"config differs from the expected job (submitted `{configLine hc}`, expected `{configLine c}`)"
  else if !(h.data == job.data) then some "dataset spec differs from the expected job"
  else if h.root != job.root then some "dataset root differs from the expected job's"
  else if h.format != job.format then some s!"format {h.format} differs from the expected {job.format}"
  else none

inductive TrajectoryVerdict where
  | accept (steps : Nat) (final : Digest) (trainAcc testAcc baseline : Nat)
  | reject (why : String)

def TrajectoryVerdict.accepted : TrajectoryVerdict → Bool
  | .accept .. => true
  | .reject _ => false

section Generic

variable {α : Type} [Arith α] [DecidableEq α] [Enc α] [Wire α]

/-- The number of parameters of an `MLP` with `hidden` hidden units. -/
def mlpParams (hidden : Nat) : Nat := hidden * numFeatures + 2 * hidden + 1

/-- Read the body into links, each starting where the previous one ended. Every line after the
header must be a `step` line followed by its `w` line, the `w` line carrying exactly the model's
parameters, each a word `Wire.ofWire` accepts; batch indices are natural numbers. -/
def parseLinks (c : TrainConfig) (lines : List String) :
    Except String (List (Link (MLP α) (List Nat))) := do
  let body := lines.filter fun l => !(headerKinds.contains (kindOf l)) && kindOf l != ""
  let rec go (prev : MLP α) : List String → Except String (List (Link (MLP α) (List Nat)))
    | [] => pure []
    | s :: w :: rest => do
      unless kindOf s == "step" do throw s!"expected a step line, found `{kindOf s}`"
      unless kindOf w == "w" do throw s!"expected a w line after a step line, found `{kindOf w}`"
      let idx ← (← parseInts (words s).tail).mapM (natOf "batch index")
      let ps ← parseInts (words w).tail
      unless ps.length == mlpParams c.hidden do
        throw s!"a w line has {ps.length} parameters, not {mlpParams c.hidden}"
      let some vs := ps.mapM (Wire.ofWire (α := α)) | throw "a parameter is not a canonical word of the format"
      let m := MLP.ofList c.hidden vs
      let tail ← go m rest
      pure (⟨prev, idx, m⟩ :: tail)
    | [l] => throw s!"trajectory ends with an unpaired `{kindOf l}` line"
  go c.init body

def trajectory (fmt : String) (c : TrainConfig) (s : DataSpec) (d : Dataset) : String :=
  let links : List (Link (MLP α) (List Nat)) := c.run d
  let body := links.flatMap fun l =>
    ["step " ++ joinInts (l.input.map (Int.ofNat ·)),
     "w " ++ joinInts (l.after.params.map Wire.toWire)]
  "\n".intercalate ([configLine c, s!"format {fmt}", dataLine s d] ++ body) ++ "\n"

/-- The first step that fails, for a useful rejection message. -/
def firstBadStep (c : TrainConfig) (d : Dataset) (links : List (Link (MLP α) (List Nat))) :
    Option Nat :=
  (links.zipIdx.find? fun (l, _) =>
    !(decide (l.after = c.stepFn d l.before l.input) && c.inv l.after)).map (·.2)

/-- Check the steps against the expected job, and the returned weights against the result. -/
def checkLinks (job : TrajectoryJob) (weights : Option Digest) (lines : List String) :
    TrajectoryVerdict :=
  let c := job.config
  match (parseLinks c lines : Except String (List (Link (MLP α) (List Nat)))) with
  | .error e => .reject e
  | .ok links =>
    let d := job.data.generate
    let final := chainEnd c.init links
    let claim : TrainClaim := { datasetRoot := job.root, config := c, finalCommit := final.commit }
    if verifyRun claim d links then
      match weights with
      | some w =>
        if w != final.commit then .reject s!"the returned weights {w} are not the verified result {final.commit}"
        else
          let test := Dataset.generate 4242 200 3
          .accept links.length final.commit (final.accuracy d) (final.accuracy test)
            ((test.items.size - test.positives) * 100 / test.items.size)
      | none =>
        let test := Dataset.generate 4242 200 3
        .accept links.length final.commit (final.accuracy d) (final.accuracy test)
          ((test.items.size - test.positives) * 100 / test.items.size)
    else
      .reject <|
        if links.map (·.input) != c.schedule d.items.size then
          s!"batches differ from the expected job's schedule ({links.length} steps submitted, {(c.schedule d.items.size).length} scheduled)"
        else match firstBadStep c d links with
          | some i => s!"step {i} does not match the specification"
          | none => "chain does not start at the specified initial weights"

end Generic

/-- Check a trajectory file's text against the consumer's job. With `expected = some digest`, the
job is identified by digest: the header's job must have exactly that digest. -/
def checkTrajectory (job : TrajectoryJob) (expected : Option Digest) (weights : Option Digest)
    (text : String) : TrajectoryVerdict :=
  let lines := text.splitOn "\n"
  match parseHeader lines with
  | .error e => .reject e
  | .ok h =>
    let bound := match expected with
      | some dg => if h.digest != dg then some s!"the submitted job's digest {h.digest} is not the expected {dg}" else none
      | none => none
    match bound.orElse fun _ => headerMismatch job h with
    | some why => .reject why
    | none =>
      match job.format with
      | "fx" => checkLinks (α := Fx) job weights lines
      | "bf16" => checkLinks (α := BF16) job weights lines
      | "f32" => checkLinks (α := F32) job weights lines
      | f => .reject s!"unknown format {f}"

def jobOfDigest? (d : Digest) : Option TrajectoryJob :=
  (namedJobs.find? fun (_, j) => j.digest == d).map (·.2)

def showTrajectoryVerdict : TrajectoryVerdict → List String
  | .accept n final tr te base =>
    [s!"ACCEPT: {n} steps of the expected job, final weights {final}",
     s!"  equal to the specified run; training accuracy {tr}%",
     s!"  held-out accuracy {te}% (majority baseline {base}%)"]
  | .reject why => [s!"REJECT: {why}"]

end IxAIVerify
