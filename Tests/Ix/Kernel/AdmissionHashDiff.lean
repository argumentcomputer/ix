import Ix.Address
import Ix.Address.Pure
import Ix.Address.Admission
import Ix.Ixon

/-! # The hash substitution, differentially (ignored runner `admission-hash-diff`)

`Address.admissionHash` is pure BLAKE3 (`Address.blake3Pure`) in the logic and
executes as the Rust BLAKE3 (`Address.blake3`), through the one approved
`@[implemented_by]` (owner, 2026-10-13). Every theorem about the compiler's
addresses and the certified entries is about pure BLAKE3; what runs is the
Rust one. `Tests.Ix.Kernel.AddressPure` compares the two on a few fixture
inputs at elaboration time. This runner compares them broadly (compiler
queue CQ2.28):

* **every record and blob of the Init+Std artifact**: each record's stored
  bytes (`Ixon.LazyConstant.rawBytes`, the bytes its address is computed
  over) and each blob's bytes;
* **generated inputs**: every length from 0 to 2049 (the 64-byte block and
  1024-byte chunk boundaries, twice), lengths around every chunk-count power
  of two up to 1024 chunks (1 MiB + 1), odd chunk counts, and pseudo-random
  lengths up to 200,000, each in four byte patterns (zeros, `0xff`,
  `i % 251`, and a linear congruential stream).

Each input is hashed with `Address.blake3` (Rust), `Address.blake3Pure`
(Lean) and `Address.admissionHash` (as executed), and the three must agree.
On the artifact, each record and blob must also sit at its own address, the
pure BLAKE3 of its bytes. The pure hashes run on parallel tasks.

The artifact is `$IX_HASH_DIFF_IXE` when set; otherwise the runner compiles
`Benchmarks/Compile/CompileInitStd.lean` with `ix compile`
(`.lake/build/bin/ix`, which `IxTests` builds) into a temporary directory. -/

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

/-- The pure hashes of `inputs`, on about `workers` parallel tasks, in order. -/
def pureHashes (inputs : Array ByteArray) (workers : Nat) : Array Address :=
  let size := max ((inputs.size + workers - 1) / max workers 1) 1
  let tasks := (List.range ((inputs.size + size - 1) / size)).toArray.map fun i =>
    Task.spawn fun _ => (inputs.extract (i * size) ((i + 1) * size)).map Address.blake3Pure
  tasks.foldl (init := #[]) fun acc t => acc ++ t.get

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

/-- The Init+Std artifact's path, and a temporary directory to remove. -/
def artifact : IO (System.FilePath × Option System.FilePath) := do
  if let some path := (← IO.getEnv "IX_HASH_DIFF_IXE") then return (path, none)
  let ix : System.FilePath := ".lake" / "build" / "bin" / "ix"
  unless (← ix.pathExists) do
    throw (IO.userError s!"{ix} missing: run `lake build ix`, or set IX_HASH_DIFF_IXE")
  let dir ← IO.FS.createTempDir
  let out := dir / "initstd.ixe"
  let exe ← IO.FS.realPath ix
  IO.println s!"[admission-hash-diff] compiling Benchmarks/Compile/CompileInitStd.lean with {exe}"
  let args := #["compile", "Benchmarks/Compile/CompileInitStd.lean", "--out", out.toString]
  let r ← IO.Process.output { cmd := exe.toString, args }
  unless r.exitCode == 0 do
    IO.FS.removeDirAll dir
    throw (IO.userError s!"ix compile exited {r.exitCode}: {r.stderr.takeEnd 600}")
  return (out, some dir)

def report (label : String) (bad : Array Mismatch) : IO Unit := do
  for m in bad.toList.take 20 do
    IO.eprintln s!"[admission-hash-diff] {label} MISMATCH {m.what}: Rust {m.rust}, \
      pure {m.lean}, admission {m.admission}"

def timesText (t : Times) (workers : Nat) : String :=
  s!"Rust {t.rust} ms, admission {t.admission} ms, pure {t.lean} ms ({workers} tasks)"

def run : IO UInt32 := do
  let workers := 32
  let mut failed := false
  -- generated inputs
  let gen : Array (Nat × Nat) := lengths.foldl (init := #[]) fun acc n =>
    acc ++ #[(0, n), (1, n), (2, n), (3, n)]
  let genInputs := gen.map fun (k, n) => pattern k n
  let (bad, times, bytes) ← compare genInputs
    (fun i => s!"pattern {gen[i]!.1}, length {gen[i]!.2}") none workers
  IO.println s!"[admission-hash-diff] generated: {genInputs.size} inputs ({lengths.size} lengths \
    × 4 patterns, longest {lengths.foldl max 0} bytes), {bytes} bytes: {timesText times workers}; \
    {bad.size} mismatches"
  unless bad.isEmpty do
    report "generated" bad
    failed := true
  -- the Init+Std artifact
  let (path, tmp) ← artifact
  try
    let t0 ← IO.monoMsNow
    let file ← IO.FS.readBinFile path
    let ixe ← IO.ofExcept (Ixon.deEnv file)
    let records := ixe.consts.toArray
    let blobs := ixe.blobs.toArray
    let inputs := records.map (·.2.rawBytes) ++ blobs.map (·.2)
    let addrs := records.map (·.1) ++ blobs.map (·.1)
    let t1 ← IO.monoMsNow
    let label (i : Nat) : String :=
      if i < records.size then s!"record {addrs[i]!}" else s!"blob {addrs[i]!}"
    let (bad, times, bytes) ← compare inputs label (some addrs) workers
    IO.println s!"[admission-hash-diff] Init+Std artifact {path}: {file.size} bytes, \
      {records.size} records and {blobs.size} blobs ({bytes} bytes hashed; load {t1 - t0} ms): \
      {timesText times workers}; {bad.size} mismatches (disagreeing hashes, or an input not at \
      its address)"
    unless bad.isEmpty do
      report "Init+Std" bad
      failed := true
  finally
    if let some dir := tmp then IO.FS.removeDirAll dir
  if failed then
    IO.eprintln "[admission-hash-diff] FAILED"
    return 1
  IO.println "[admission-hash-diff] OK: Address.blake3, Address.blake3Pure and \
    Address.admissionHash agree on every input"
  return 0

end Tests.Ix.Kernel.AdmissionHashDiff
