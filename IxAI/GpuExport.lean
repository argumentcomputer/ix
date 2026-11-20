import IxAICore
import IxAIGpu.HostKeys

/-!
# `ixai-gpu-export`: what the GPU trainer reads, and the spec's answers to compare against

* `problem SEED HIDDEN LR_RAW EPOCHS BATCH TRAIN TEST`: the training problem of the triage spec
  under that config, as the GPU trainer reads it: shapes, `config.init`, and the batches of
  `gather examples schedule` (`IxAICore.train_eq_foldl_gather`).
* `keys SEED HIDDEN LR_RAW EPOCHS BATCH TRAIN TEST`: for every step of that run, the hint keys of
  `hostStepHintKeys`, from the spec's own intermediate values.
* `random SEED COUNT`: random single-step cases of random shapes and values, each with the result
  of `Model.step`.

Text format, one record per line, raw fixed-point integers separated by spaces:

```
problem I H O LR STEPS        (or: case I H O LR)
w1 …  b1 …  w2 …  b2 …        (row-major; w1 is H×I, w2 is O×H)
batch B
x …                           (B×I, row-major)
t …                           (B×O)
expect w1 … / b1 … / w2 … / b2 …   (random cases: the parameters after Model.step)
keys N                        (keys: step N's fx.shr8 keys, then its fx.sign keys)
shr …
sign …
```
-/

open IxAICore

def joinInts (xs : List Int) : String := " ".intercalate (xs.map toString)
def joinFx (xs : List Fx) : String := joinInts (xs.map (·.raw))

def modelLines (m : Model) (pre : String := "") : List String :=
  [s!"{pre}w1 {joinFx m.w1.flatten}", s!"{pre}b1 {joinFx m.b1}", s!"{pre}w2 {joinFx m.w2.flatten}",
   s!"{pre}b2 {joinFx m.b2}"]

def batchLines (b : List (List Fx × List Fx)) : List String :=
  [s!"batch {b.length}", s!"x {joinFx (b.map (·.1)).flatten}", s!"t {joinFx (b.map (·.2)).flatten}"]

def configOf (args : List String) : Option Config :=
  match args.map String.toNat? with
  | [some seed, some hidden, some lr, some epochs, some batch, some train, some test] =>
    some { seed, hidden, lrRaw := lr, epochs, batch, trainSize := train, testSize := test }
  | _ => none

def batchesOf (c : Config) : List (List (List Fx × List Fx)) :=
  let s := Triage.spec
  gather ((c.data s).map s.example) c.schedule (s.example default)

def problem (c : Config) : IO Unit := do
  let s := Triage.spec
  let bs := batchesOf c
  let out := IO.println
  out s!"problem {s.numFeatures} {c.hidden} {s.outputs} {c.lrRaw} {bs.length}"
  for l in modelLines (c.init s) do out l
  for b in bs do
    for l in batchLines b do out l

def keys (c : Config) : IO Unit := do
  let lr : Fx := ⟨c.lrRaw⟩
  let mut m := c.init Triage.spec
  for (b, i) in (batchesOf c).zip (List.range (batchesOf c).length) do
    let (shr, sign) := IxAIGpu.hostStepHintKeys m b lr
    IO.println s!"keys {i}"
    IO.println s!"shr {joinInts shr}"
    IO.println s!"sign {joinInts sign}"
    m := m.step lr b

/-- A value in `[-bound, bound]`. -/
def IxAICore.Rng.signed (r : Rng) (bound : Nat) : Int × Rng :=
  let (v, r) := r.below (2 * bound + 1)
  (Int.ofNat v - bound, r)

def IxAICore.Rng.signedList (r : Rng) (bound : Nat) : Nat → List Fx × Rng
  | 0 => ([], r)
  | n + 1 =>
    let (v, r) := r.signed bound
    let (vs, r) := r.signedList bound n
    (⟨v⟩ :: vs, r)

/-- A random step: shapes up to 24; weights and inputs up to 64, 512 or 4096 in magnitude (the
largest often exceed the GPU's int64 bounds, which must then refuse the step); targets up to
`2^9`; a learning rate up to 16 either side of zero. -/
def randomCase (r : Rng) : String × Rng := Id.run do
  let (i, r) := r.below 24
  let (h, r) := r.below 24
  let (o, r) := r.below 24
  let (b, r) := r.below 24
  let (i, h, o, b) := (i + 1, h + 1, o + 1, b + 1)
  let (scale, r) := r.below 3
  let bound := [64, 512, 4096].getD scale 64
  let (lr, r) := r.signed 16
  let (w1, r) := r.signedList bound (h * i)
  let (b1, r) := r.signedList bound h
  let (w2, r) := r.signedList bound (o * h)
  let (b2, r) := r.signedList bound o
  let (xs, r) := r.signedList bound (b * i)
  let (ts, r) := r.signedList 512 (b * o)
  let m : Model := { w1 := reshape i h w1, b1, w2 := reshape h o w2, b2 }
  let batch := (List.range b).map fun k => ((xs.drop (k * i)).take i, (ts.drop (k * o)).take o)
  let lines := [s!"case {i} {h} {o} {lr}"] ++ modelLines m ++ batchLines batch ++
    modelLines (m.step ⟨lr⟩ batch) "expect "
  return ("\n".intercalate lines, r)

def random (seed count : Nat) : IO Unit := do
  let mut r := Rng.seeded seed
  for _ in [0:count] do
    let (text, r') := randomCase r
    IO.println text
    r := r'

def main (args : List String) : IO UInt32 := do
  match args with
  | "problem" :: rest => match configOf rest with
    | some c => problem c; return 0
    | none => IO.eprintln "bad config"; return 2
  | "keys" :: rest => match configOf rest with
    | some c => keys c; return 0
    | none => IO.eprintln "bad config"; return 2
  | ["random", seed, count] => random seed.toNat! count.toNat!; return 0
  | _ =>
    IO.eprintln "usage: ixai-gpu-export (problem|keys) SEED HIDDEN LR EPOCHS BATCH TRAIN TEST | random SEED COUNT"
    return 2
