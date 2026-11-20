import IxAIStep
import IxAIGpuHost.FFI
import Std.Data.HashSet

/-!
# The GPU trainer's host

Training is `IxAICore.train` as a fold of `Model.step` over `IxAICore.gather`'s batches
(`IxAICore.train_eq_foldl_gather`), with each step run by the CUDA kernels. The trainer is not
trusted: its weights are `train` when the kernels implement `IxAIGpu.gpuStep`, and `package`
writes every step's `Fixed::step` execution package, with the hint table built from the kernels'
own key buffers, for the Aiur prover and `ixai aiur-chain` to check.

* `train`: final weights, in the format of `ixai weights`.
* `keys`: every step's hint keys, in the format of `ixai-gpu-export keys`.
* `check`: `ixai-gpu-export random` cases against `Model.step`.
* `package`: the full run's execution packages, written by `IxAIAiur.exportWith`.
* `bench`: one step's time at a given shape, on CUDA cores and with tensor cores, whose results
  must be bit-identical.
-/

namespace IxAIGpuHost
open IxAICore

abbrev Batch := List (List Fx × List Fx)

structure Shape where
  nIn : Nat
  nHidden : Nat
  nOut : Nat
  deriving BEq, Repr

def Shape.modelLength (s : Shape) : Nat := s.nHidden * s.nIn + s.nHidden + s.nOut * s.nHidden + s.nOut

def Shape.fits (s : Shape) (m : Model) : Bool :=
  m.w1.length == s.nHidden && m.w1.all (·.length == s.nIn) && m.b1.length == s.nHidden &&
    m.w2.length == s.nOut && m.w2.all (·.length == s.nHidden) && m.b2.length == s.nOut

/-- The two's-complement int64 bits of `v`. -/
def int64Bits (v : Int) : Except String UInt64 :=
  if -2 ^ 63 ≤ v ∧ v < 2 ^ 63 then .ok (v % 2 ^ 64).toNat.toUInt64
  else .error s!"{v} does not fit in int64"

/-- Little-endian int64 words. -/
def pack (xs : List Int) : Except String ByteArray := do
  let mut out := ByteArray.empty
  for x in xs do
    let u ← int64Bits x
    for k in [0:8] do
      out := out.push (u >>> (8 * k).toUInt64).toUInt8
  return out

def unpack (bytes : ByteArray) : Array Int := Id.run do
  let mut out := #[]
  for i in [0:bytes.size / 8] do
    let mut u : Nat := 0
    for k in [0:8] do
      u := u + bytes[8 * i + k]!.toNat <<< (8 * k)
    out := out.push (if u < 2 ^ 63 then (u : Int) else (u : Int) - 2 ^ 64)
  return out

/-- `w1.flatten ++ b1 ++ w2.flatten ++ b2`, the order of the step's output and of `rawOfModel`. -/
def flatModel (m : Model) : List Int := (m.w1.flatten ++ m.b1 ++ m.w2.flatten ++ m.b2).map (·.raw)

def modelOfFlat (s : Shape) (v : List Int) : Model :=
  let fx := v.map Fx.ofRaw
  let b1At := s.nHidden * s.nIn
  let w2At := b1At + s.nHidden
  let b2At := w2At + s.nOut * s.nHidden
  { w1 := reshape s.nIn s.nHidden (fx.take b1At)
    b1 := (fx.drop b1At).take s.nHidden
    w2 := reshape s.nHidden s.nOut ((fx.drop w2At).take (s.nOut * s.nHidden))
    b2 := fx.drop b2At }

/-- First occurrences in order, as `List.eraseDups`, in linear time. -/
def eraseDupsHashed (xs : Array Int) : List Int := Id.run do
  let mut seen : Std.HashSet Int := {}
  let mut out := #[]
  for x in xs do
    unless seen.contains x do
      seen := seen.insert x
      out := out.push x
  return out.toList

/-- A device context and its shape. -/
structure Gpu where
  ctx : Context
  shape : Shape
  maxBatch : Nat

def Gpu.new (s : Shape) (maxBatch : Nat) : IO Gpu := do
  unless [s.nIn, s.nHidden, s.nOut, maxBatch].all (· < 2 ^ 31) do
    throw (IO.userError "model shape out of range")
  return ⟨← Context.create s.nIn.toUInt32 s.nHidden.toUInt32 s.nOut.toUInt32 maxBatch.toUInt32, s, maxBatch⟩

def Gpu.setModel (g : Gpu) (m : Model) : IO Unit := do
  unless g.shape.fits m do throw (IO.userError "model does not have the context's shape")
  g.ctx.setModel (← IO.ofExcept (pack (flatModel m)))

def Gpu.model (g : Gpu) : IO Model := do
  return modelOfFlat g.shape (unpack (← g.ctx.model)).toList

/-- One `Model.step` on the device's model. `false` when the kernels' fixed-width bounds refused
it. -/
def Gpu.step (g : Gpu) (b : Batch) (lr : Fx) : IO Bool := do
  unless b.length ≤ g.maxBatch && b.all (fun (x, t) => x.length == g.shape.nIn && t.length == g.shape.nOut) do
    throw (IO.userError "batch does not have the context's shape")
  let x ← IO.ofExcept (pack ((b.map (·.1)).flatten.map (·.raw)))
  let t ← IO.ofExcept (pack ((b.map (·.2)).flatten.map (·.raw)))
  g.ctx.step x t b.length.toUInt32 (← IO.ofExcept (int64Bits lr.raw))

/-- A step that must succeed. -/
def Gpu.step! (g : Gpu) (b : Batch) (lr : Fx) (i : Nat) : IO Unit := do
  unless ← g.step b lr do
    throw (IO.userError s!"step {i}: an intermediate value left the fixed width of the exact kernels")

/-- The last step's `fx.shr8` and `fx.sign` keys, for a batch of `batch` examples, in the order
of `IxAIGpu.gpuStepHintKeys` (and so of `IxAIAiur.stepHintKeys`, the host's hint table): per
example its `dot8`, `dot16` and `dot11` sums; the `w1` and `w2` gradient sums; the products
`lr · g` of `w1`, `b1`, `w2`, `b2`; first occurrences only. -/
def Gpu.hintKeys (g : Gpu) (batch : Nat) : IO (List Int × List Int) := do
  let v := unpack (← g.ctx.keys)
  let (i, h, o, b) := (g.shape.nIn, g.shape.nHidden, g.shape.nOut, batch)
  let oAt := b * h
  let dzAt := oAt + b * o
  let zAt := dzAt + b * h
  let gw1At := zAt + b * h
  let finish := gw1At + 2 * h * i + 2 * o * h + h + o
  unless v.size == finish do throw (IO.userError "hint key buffers do not have the step's shape")
  let perExample := (List.range b).foldl (init := #[]) fun acc k =>
    acc ++ v.extract (k * h) ((k + 1) * h) ++ v.extract (oAt + k * o) (oAt + (k + 1) * o) ++
      v.extract (dzAt + k * h) (dzAt + (k + 1) * h)
  -- gw1, gw2 and the four product buffers follow one another, in that order.
  return (eraseDupsHashed (perExample ++ v.extract gw1At finish), eraseDupsHashed (v.extract zAt gw1At))

/-- The triage spec's training run under `c`: initial model, learning rate, gathered batches. -/
def problemOf (c : Config) : Model × Fx × List Batch :=
  let s := Triage.spec
  (c.init s, ⟨c.lrRaw⟩, gather ((c.data s).map s.example) c.schedule (s.example default))

def largestBatch (bs : List Batch) : Nat := max 1 (bs.foldl (fun a b => max a b.length) 0)

def Gpu.forModel (m : Model) (bs : List Batch) : IO Gpu := do
  let g ← Gpu.new ⟨(getD m.w1 0 []).length, m.b1.length, m.b2.length⟩ (largestBatch bs)
  g.setModel m
  return g

def joinInts (xs : List Int) : String := " ".intercalate (xs.map toString)

def modelLines (m : Model) : List String :=
  [s!"w1 {joinInts (m.w1.flatten.map (·.raw))}", s!"b1 {joinInts (m.b1.map (·.raw))}",
   s!"w2 {joinInts (m.w2.flatten.map (·.raw))}", s!"b2 {joinInts (m.b2.map (·.raw))}"]

/-- Train on the GPU and print the final weights. -/
def train (c : Config) : IO Unit := do
  let (m0, lr, bs) := problemOf c
  let g ← Gpu.forModel m0 bs
  let t0 ← IO.monoNanosNow
  for (b, i) in bs.zip (List.range bs.length) do
    g.step! b lr i
  let m ← g.model
  let ms := (Float.ofNat ((← IO.monoNanosNow) - t0)) / 1e6
  IO.eprintln s!"{bs.length} steps on the GPU in {ms} ms"
  for l in modelLines m do IO.println l

/-- Train on the GPU and print every step's hint keys. -/
def keys (c : Config) : IO Unit := do
  let (m0, lr, bs) := problemOf c
  let g ← Gpu.forModel m0 bs
  let out ← IO.getStdout
  for (b, i) in bs.zip (List.range bs.length) do
    g.step! b lr i
    let (shr, sign) ← g.hintKeys b.length
    out.putStrLn s!"keys {i}"
    out.putStrLn s!"shr {joinInts shr}"
    out.putStrLn s!"sign {joinInts sign}"

/-- The first `count` steps of the full run as `Fixed::step` execution packages in `dir`, from the
GPU's hint keys and weights. -/
def package (dir : String) (count : Nat) : IO Unit := do
  let (m0, lr, bs) := problemOf IxAIAiur.fullConfig
  let bs := bs.take count
  let g ← Gpu.forModel m0 bs
  let counter ← IO.mkRef 0
  IxAIAiur.exportWith dir m0 lr bs fun _ b => do
    let i ← counter.modifyGet fun i => (i, i + 1)
    g.step! b lr i
    return (← g.hintKeys b.length, ← g.model)

/-! ## Random single-step cases -/

structure Case where
  shape : Shape
  lr : Fx
  model : Model
  batch : Batch
  expect : Model

/-- The lines of `ixai-gpu-export random`, read one record at a time. -/
structure Reader where
  lines : Array String
  pos : Nat := 0

def Reader.record (r : Reader) (tag : String) : Except String (List Int × Reader) := do
  let some line := r.lines[r.pos]? | throw s!"line {r.pos + 1}: missing `{tag}` record"
  let words := (line.splitOn " ").filter (!·.isEmpty)
  let tagWords := (tag.splitOn " ").filter (!·.isEmpty)
  unless words.take tagWords.length == tagWords do
    throw s!"line {r.pos + 1}: expected `{tag}`"
  let values ← (words.drop tagWords.length).mapM fun w =>
    match w.toInt? with
    | some v => pure v
    | none => throw s!"line {r.pos + 1}: `{w}` is not an integer"
  return (values, { r with pos := r.pos + 1 })

def Reader.sized (r : Reader) (tag : String) (n : Nat) : Except String (List Int × Reader) := do
  let (v, r) ← r.record tag
  unless v.length == n do throw s!"line {r.pos}: `{tag}` has {v.length} values, expected {n}"
  return (v, r)

def Reader.model (r : Reader) (s : Shape) (pre : String) : Except String (Model × Reader) := do
  let (w1, r) ← r.sized (pre ++ "w1") (s.nHidden * s.nIn)
  let (b1, r) ← r.sized (pre ++ "b1") s.nHidden
  let (w2, r) ← r.sized (pre ++ "w2") (s.nOut * s.nHidden)
  let (b2, r) ← r.sized (pre ++ "b2") s.nOut
  return (modelOfFlat s (w1 ++ b1 ++ w2 ++ b2), r)

def Reader.case (r : Reader) : Except String (Case × Reader) := do
  let (h, r) ← r.sized "case" 4
  let [i, hidden, o, lr] := h | throw "unreachable"
  let shape : Shape := ⟨i.toNat, hidden.toNat, o.toNat⟩
  let (model, r) ← r.model shape ""
  let (bn, r) ← r.sized "batch" 1
  let b := (bn.headD 0).toNat
  let (x, r) ← r.sized "x" (b * shape.nIn)
  let (t, r) ← r.sized "t" (b * shape.nOut)
  let (expect, r) ← r.model shape "expect "
  let fx := fun (l : List Int) => l.map Fx.ofRaw
  let batch := (List.range b).map fun k =>
    (fx ((x.drop (k * shape.nIn)).take shape.nIn), fx ((t.drop (k * shape.nOut)).take shape.nOut))
  return (⟨shape, ⟨lr⟩, model, batch, expect⟩, r)

def readCases (text : String) : Except String (List Case) := do
  let lines := ((text.splitOn "\n").filter (!·.all Char.isWhitespace)).toArray
  let mut r : Reader := { lines }
  let mut cases := #[]
  while r.pos < lines.size do
    let (c, r') ← r.case
    cases := cases.push c
    r := r'
  return cases.toList

/-- Run every case on the GPU with GEMM path `gemmPath` (`Context.setPath`): each step either
equals `Model.step` or is refused by the fixed-width bounds. -/
def check (path : String) (gemmPath : Nat := 0) : IO Unit := do
  let cases ← IO.ofExcept (readCases (← IO.FS.readFile path))
  let mut equal := 0
  let mut rejected := 0
  for (c, i) in cases.zip (List.range cases.length) do
    let g ← Gpu.new c.shape (max 1 c.batch.length)
    g.ctx.setPath gemmPath.toUInt32
    g.setModel c.model
    if ← g.step c.batch c.lr then
      unless (← g.model) == c.expect do
        throw (IO.userError s!"case {i} ({repr c.shape}, batch {c.batch.length}): GPU step differs from Model.step")
      equal := equal + 1
    else
      rejected := rejected + 1
  IO.println s!"{equal} of {cases.length} cases bit-identical to Model.step; {rejected} refused by the fixed-width bounds"

/-! ## Benchmark -/

/-- `n` little-endian int64 words, uniform in `[-bound, bound]`, from a xorshift64 stream. -/
def randomWords (seed : UInt64) (n bound : Nat) : ByteArray × UInt64 := Id.run do
  let mut s := seed
  let mut out := ByteArray.emptyWithCapacity (8 * n)
  let span := (2 * bound + 1).toUInt64
  for _ in [0:n] do
    s := s ^^^ (s <<< 13)
    s := s ^^^ (s >>> 7)
    s := s ^^^ (s <<< 17)
    let u := s % span - bound.toUInt64
    for k in [0:8] do
      out := out.push (u >>> (8 * k).toUInt64).toUInt8
  return (out, s)

/-- The fastest of a path's runs, and what its last run left on the device. -/
structure BenchRun where
  wallMs : Float
  deviceMs : Float
  tensorGemms : Nat
  model : ByteArray
  keys : ByteArray

/-- `reps` steps from the same model on GEMM path `path`; `none` if the bounds refuse the step. -/
def benchPath (ctx : Context) (model x t : ByteArray) (batch : Nat) (lr : UInt64) (path reps : Nat) :
    IO (Option BenchRun) := do
  ctx.setPath path.toUInt32
  let mut wall : Float := 0
  let mut device : Float := 0
  for r in [0:reps] do
    ctx.setModel model
    let t0 ← IO.monoNanosNow
    unless ← ctx.step x t batch.toUInt32 lr do return none
    let ms := Float.ofNat ((← IO.monoNanosNow) - t0) / 1e6
    let d ← ctx.kernelMs
    wall := if r == 0 || ms < wall then ms else wall
    device := if r == 0 || d < device then d else device
  return some ⟨wall, device, (← ctx.tensorGemms).toNat, ← ctx.model, ← ctx.keys⟩

/-- One step at `nIn × nHidden × nOut` with a batch of `batch`, best of `reps`, on CUDA cores and
on the default path (tensor cores for large GEMMs). Weights and biases are uniform in
`[-128, 128]`, inputs and targets in `[-256, 256]` (raw values, 8 fractional bits), and the raw
learning rate is 1. The two paths' models and hint keys must be bit-identical. -/
def bench (s : Shape) (batch reps : Nat) : IO Bool := do
  let g ← Gpu.new s (max 1 batch)
  let (model, r) := randomWords 0x9E3779B97F4A7C15 s.modelLength 128
  let (x, r) := randomWords r (batch * s.nIn) 256
  let (t, _) := randomWords r (batch * s.nOut) 256
  IO.println s!"step at nIn {s.nIn}, nHidden {s.nHidden}, nOut {s.nOut}, batch {batch}; best of {reps}"
  let some cuda ← benchPath g.ctx model x t batch 1 1 reps
    | IO.println "refused by the fixed-width bounds"; return false
  let some auto ← benchPath g.ctx model x t batch 1 0 reps
    | IO.println "refused by the fixed-width bounds on the default path"; return false
  for (name, b) in [("CUDA cores", cuda), ("default", auto)] do
    IO.println s!"{name}: {b.wallMs} ms per step ({b.deviceMs} ms on the device), {b.tensorGemms} of 5 GEMMs on tensor cores"
  let same := cuda.model == auto.model && cuda.keys == auto.keys
  IO.println s!"model and hint keys {if same then "bit-identical" else "DIFFER"} between the paths"
  return same

end IxAIGpuHost
