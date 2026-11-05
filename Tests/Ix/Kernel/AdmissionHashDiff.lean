import Ix.Address
import Ix.Address.Pure
import Ix.Address.Admission
import Ix.Ixon
import Tests.Ix.Kernel.ReaderRoundtrip
import Tests.Ix.InitStd

/-! # The hash substitution, differentially (`admission-hash-diff`)

`Address.admissionHash` is pure BLAKE3 (`Address.blake3Pure`) in the logic and
executes as the Rust BLAKE3 (`Address.blake3`), through the one approved
`@[implemented_by]` substitution. Every theorem about the compiler's
addresses and the certified entries is about pure BLAKE3; what runs is the
Rust one. `Tests.Ix.Kernel.AddressPure` compares the two on a few fixture
inputs at elaboration time. This runner compares them across:

* **generated inputs**: every length from 0 to 2049 (the 64-byte block and
  1024-byte chunk boundaries, twice), lengths around every chunk-count power
  of two up to 1024 chunks (1 MiB + 1), odd chunk counts, and pseudo-random
  lengths up to 200,000, each in four byte patterns (zeros, `0xff`,
  `i % 251`, and a linear congruential stream);
* **every record and blob of a compiled Ixon artifact** (`$IX_HASH_DIFF_IXE`
  when set, or the compiled closure of `ReaderFidelityDefs` by default): each
  record's stored bytes (`Ixon.LazyConstant.rawBytes`), each blob's bytes,
  and the role binding's bytes when the artifact has one.

Each input is hashed with `Address.blake3` (Rust), `Address.blake3Pure`
(Lean) and `Address.admissionHash` (as executed), and the three must agree.
On the artifact, each record, blob and binding must also sit at its own
address, the pure BLAKE3 of its bytes. The pure hashes run on parallel tasks,
the inputs dealt out largest first.

`admission-hash-diff-initstd`, in the merge queue's Init+Std partition, runs
the artifact comparison on the Init+Std artifact `initstd-reference` compiles. -/

namespace Tests.Ix.Kernel.AdmissionHashDiff

/-- `n` bytes of a pattern: 0 zeros, 1 `0xff`, 2 `i % 251`, 3 a linear
congruential stream seeded by the length. -/
def pattern (kind n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity n
  let mut x : UInt64 := (n.toUInt64 * 0x9E3779B97F4A7C15) ^^^ 0x2545F4914F6CDD1D
  for i in [0:n] do
    if kind ≥ 3 then
      x := x * 6364136223846793005 + 1442695040888963407
    let b : UInt8 := match kind with
      | 0 => 0
      | 1 => 0xff
      | 2 => (i % 251).toUInt8
      | _ => (x >>> 56).toUInt8
    out := out.push b
  return out

/-- The generated lengths: every length to 2049, around each power-of-two
chunk count up to 1024 chunks, odd chunk counts, and pseudo-random lengths. -/
def lengths : Array Nat := Id.run do
  let mut out : Array Nat := (List.range 2050).toArray
  for k in [1:11] do
    let c := 1024 * 2 ^ k
    out := out ++ #[c - 65, c - 64, c - 63, c - 1, c, c + 1, c + 63, c + 64, c + 65]
  for c in [3, 5, 7, 9, 15, 17, 31, 33, 63, 65, 127, 129, 255, 257, 511, 513, 1023, 1025] do
    out := out ++ #[1024 * c - 1, 1024 * c, 1024 * c + 1]
  let mut x : UInt64 := 0x853C49E6748FEA9B
  for _ in [0:120] do
    x := x * 6364136223846793005 + 1442695040888963407
    out := out.push ((x >>> 33).toNat % 200001)
  return out

/-- An input whose hashes disagree, or which does not sit at its address. -/
structure Mismatch where
  what : String
  rust : Address
  lean : Address
  admission : Address

/-- The indices of the inputs, given by their sizes, that each of `workers`
tasks hashes: ranked by size, largest first, and dealt out round-robin, so
every task gets its share of the largest. (The generated inputs come grouped
by kind of length, with the long ones together at the end; contiguous slices
left one task most of the bytes.) -/
def deal (sizes : Array Nat) (workers : Nat) : Array (Array Nat) :=
  let order := (Array.range sizes.size).qsort fun i j => sizes[i]! > sizes[j]!
  (Array.range workers).map fun t =>
    (Array.range ((order.size + workers - 1 - t) / workers)).map fun k => order[t + k * workers]!

/-- The pure hashes of `inputs`, on `workers` parallel tasks, in order. -/
def pureHashes (inputs : Array ByteArray) (workers : Nat) : Array Address :=
  let tasks := (deal (inputs.map (·.size)) (max workers 1)).map fun share =>
    Task.spawn fun _ => share.map fun i => (i, Address.blake3Pure inputs[i]!)
  let hashed := tasks.foldl (init := #[]) fun acc task => acc ++ task.get
  (hashed.qsort fun a b => a.1 < b.1).map (·.2)

-- every index once, whatever the sizes and the worker count
#guard [1, 2, 3, 7, 10].all fun w =>
  ((deal #[1, 9, 0, 4, 4, 7, 2] w).toList.flatMap (·.toList)).mergeSort == List.range 7
-- the largest inputs go to different tasks
#guard (deal #[1, 9, 0, 8, 4, 7, 2] 3).toList.map (·.toList) == [[1, 4, 2], [3, 6], [5, 0]]

/-- The times of one comparison, in milliseconds. -/
structure Times where
  rust : Nat
  admission : Nat
  lean : Nat

/-- Hash `inputs` (named by `label i`) three ways and compare. `expected`, if
given, is each input's address, which the pure hash must equal. Returns the
mismatches, the times (Rust and admission sequential, pure on parallel
tasks) and the bytes hashed. -/
def compare (inputs : Array ByteArray) (label : Nat → String)
    (expected : Option (Array Address)) (workers : Nat) :
    IO (Array Mismatch × Times × Nat) := do
  let t0 ← IO.monoMsNow
  let rust ← IO.lazyPure fun _ => inputs.map Address.blake3
  let t1 ← IO.monoMsNow
  let admission ← IO.lazyPure fun _ => inputs.map Address.admissionHash
  let t2 ← IO.monoMsNow
  let leanH ← IO.lazyPure fun _ => pureHashes inputs workers
  let t3 ← IO.monoMsNow
  let mut bad : Array Mismatch := #[]
  for i in [0:inputs.size] do
    let r := rust[i]!
    let p := leanH[i]!
    let a := admission[i]!
    let atAddress := match expected with
      | some addrs => addrs[i]! == p
      | none => true
    unless r == p && a == p && atAddress do
      bad := bad.push { what := label i, rust := r, lean := p, admission := a }
  let bytes := inputs.foldl (init := 0) fun n b => n + b.size
  return (bad, { rust := t1 - t0, admission := t2 - t1, lean := t3 - t2 }, bytes)

/-- `$IX_HASH_DIFF_IXE`, when set and not empty. -/
def overridePath : IO (Option System.FilePath) := do
  return (← IO.getEnv "IX_HASH_DIFF_IXE").bind fun p => if p.isEmpty then none else some p

/-- Read and decode an `.ixe` file. -/
def readArtifact (path : System.FilePath) : IO Ixon.Env := do
  IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))

/-- Load `$IX_HASH_DIFF_IXE` when set, otherwise compile the `ReaderFidelityDefs`
fixture closure in-process. -/
def loadArtifact : IO (String × Ixon.Env) := do
  if let some path ← overridePath then
    return (path.toString, ← readArtifact path)
  let (_, inp) ← Tests.Ix.Kernel.ReaderRoundtrip.input
  return ("ReaderFidelityDefs", inp.ixon)

def report (label : String) (bad : Array Mismatch) : IO Unit := do
  for m in bad.toList.take 20 do
    IO.eprintln s!"[admission-hash-diff] {label} MISMATCH {m.what}: Rust {m.rust}, \
      pure {m.lean}, admission {m.admission}"

def timesText (t : Times) (workers : Nat) : String :=
  s!"Rust {t.rust} ms, admission {t.admission} ms, pure {t.lean} ms ({workers} tasks)"

/-- The pure hashes run on this many tasks. -/
def workers : Nat := 32

/-- The generated inputs, compared; whether all agree. -/
def generatedLeg : IO Bool := do
  let gen : Array (Nat × Nat) := lengths.foldl (init := #[]) fun acc n =>
    acc ++ #[(0, n), (1, n), (2, n), (3, n)]
  let genInputs := gen.map fun (k, n) => pattern k n
  let (bad, times, bytes) ← compare genInputs
    (fun i => s!"pattern {gen[i]!.1}, length {gen[i]!.2}") none workers
  IO.println s!"[admission-hash-diff] generated: {genInputs.size} inputs ({lengths.size} lengths \
    × 4 patterns, longest {lengths.foldl max 0} bytes), {bytes} bytes: {timesText times workers}; \
    {bad.size} mismatches"
  unless bad.isEmpty do report "generated" bad
  return bad.isEmpty

/-- Every record and blob of `ixe`, and its role binding if it has one,
compared, each also at its own address; whether all agree. `loadMs` is the
time it took to load. -/
def artifactLeg (source : String) (ixe : Ixon.Env) (loadMs : Nat) : IO Bool := do
  let records := ixe.consts.toArray
  let blobs := ixe.blobs.toArray
  let binding := ixe.roleBinding.toArray
  let inputs := records.map (·.2.rawBytes) ++ blobs.map (·.2) ++ binding.map (·.bytes)
  let addrs := records.map (·.1) ++ blobs.map (·.1) ++ binding.map (·.address)
  let label (i : Nat) : String :=
    if i < records.size then s!"record {addrs[i]!}"
    else if i < records.size + blobs.size then s!"blob {addrs[i]!}"
    else s!"role binding {addrs[i]!}"
  let (bad, times, bytes) ← compare inputs label (some addrs) workers
  IO.println s!"[admission-hash-diff] artifact {source}: \
    {records.size} records, {blobs.size} blobs and {binding.size} role binding(s) \
    ({bytes} bytes hashed; load {loadMs} ms): \
    {timesText times workers}; {bad.size} mismatches (disagreeing hashes, or an input not at \
    its address)"
  unless bad.isEmpty do report "artifact" bad
  return bad.isEmpty

def verdict (ok : Bool) : IO UInt32 := do
  unless ok do
    IO.eprintln "[admission-hash-diff] FAILED"
    return 1
  IO.println "[admission-hash-diff] OK: Address.blake3, Address.blake3Pure and \
    Address.admissionHash agree on every input"
  return 0

/-- `admission-hash-diff` (primary): the generated inputs and the artifact
(`$IX_HASH_DIFF_IXE`, or the fixture closure). -/
def run : IO UInt32 := do
  let generated ← generatedLeg
  let t0 ← IO.monoMsNow
  let (source, ixe) ← loadArtifact
  let artifact ← artifactLeg source ixe ((← IO.monoMsNow) - t0)
  verdict (generated && artifact)

/-- `admission-hash-diff-initstd` (the merge queue's Init+Std partition): the
artifact comparison alone, on the Init+Std artifact that `initstd-reference`
leaves at `Tests.Ix.InitStd.keptArtifact` (or `$IX_HASH_DIFF_IXE`, when
set). The generated inputs are the primary entry's. -/
def runInitStd : IO UInt32 := do
  let path := (← overridePath).getD Tests.Ix.InitStd.keptArtifact
  unless ← path.pathExists do
    IO.eprintln s!"[admission-hash-diff] {path} is missing: run `initstd-reference` first, \
      or set IX_HASH_DIFF_IXE to an .ixe"
    return 1
  let t0 ← IO.monoMsNow
  let ixe ← readArtifact path
  verdict (← artifactLeg path.toString ixe ((← IO.monoMsNow) - t0))

end Tests.Ix.Kernel.AdmissionHashDiff
