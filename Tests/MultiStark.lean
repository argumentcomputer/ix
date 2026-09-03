module

public import LSpec
public import Ix.Aiur.Meta
public import Ix.Aiur.Protocol
public import Ix.Aiur.Compiler
public import Ix.MultiStark
public import Ix.Aiur.Hypercube
public import Ix.Aiur.Statistics
public import Ix.MultiStark.Field.GoldilocksBytes
public import Blake3.Rust

/-!
# Tests for the Multi-STARK recursive verifier

These exercise `Ix/MultiStark.lean` (the in-circuit verifier) the way the former
standalone `RecursiveVerifier.lean` executable did, split into two primary
runners (registered in `Tests/Main.lean`, both wired into `ci.yml`):

* **`multi-stark`** — `selfTestSuite`. Executes the verifier's primitive
  `*_test` entrypoints (`Ix/MultiStark/Tests.lean`), each of which validates one
  primitive (Blake3 MMCS leaf/compress, Merkle `verify_batch`, the challenger,
  FRI fold + reduced openings, non-native Goldilocks/ExtGoldilocks arithmetic)
  against the Rust reference values from `multi-stark` (`gen_pcs_refs`). Cheap: just
  bytecode execution, no proving. The in-circuit `assert_eq!`s do the checking;
  every entrypoint returns `1` on success.

* **`recursive-verifier`** — `endToEndSuite`. The full pipeline (a few
  seconds, dominated by proving + the verifier executions):
  1. prove `factorial(5) = 120` with the Multi-STARK backend,
  2. feed that proof as non-deterministic advice (IO channel 0; vk on 1, claims
     on 2) and run `verify_multi_stark_proof` over it — it must accept,
  3. two negative tests: a tampered proof byte and a tampered claim must both be
     rejected by the verifier's own checks (Fiat-Shamir / Merkle / OOD / FRI).

The verifier toplevel is compiled separately from the test toplevel
(`MultiStark.multiStark` vs `MultiStark.multiStarkTests`) so the `*_test`
circuits never widen the production verifier — see `Ix/MultiStark.lean`.
-/

public section

open LSpec Aiur

namespace Tests.MultiStark

/-- A passing test iff `e` is `.ok`; on `.error` the message is surfaced. -/
def expectOk [ToString ε] (descr : String) (e : Except ε α) : TestSeq :=
  match e with
  | .ok _ => test descr true
  | .error msg => test s!"{descr} — unexpected error: {msg}" false

/-- A passing test iff `e` is `.error` (i.e. the verifier rejected the input). -/
def expectErr (descr : String) (e : Except ε α) : TestSeq :=
  match e with
  | .error _ => test descr true
  | .ok _ => test s!"{descr} — expected a rejection but it was accepted" false

-- ════════════════════════════════════════════════════════════════════════════
-- `multi-stark`: verifier primitive self-tests (execution-only, no proving)
-- ════════════════════════════════════════════════════════════════════════════

/-- The verifier's primitive self-test entrypoints (`Ix/MultiStark/Tests.lean`)
and a one-line description of what each validates against the Rust reference. -/
def selfTests : List (Lean.Name × String) := [
  (`pcs_hash_test, "Blake3 MMCS leaf/compress match reference"),
  (`pcs_merkle_test, "Merkle verify_batch matches reference (root + tamper)"),
  (`lane_hash_test, "lane-granular leaf blake3 matches byte blake3 (blocks/chunks/fold)"),
  (`io_hash_test, "IO-slice blake3 matches byte blake3 (blocks/chunks/fold)"),
  (`rows_hash_test, "rows-walking leaf hash matches concat+canon reference"),
  (`sample_bits_test, "challenger sample_bits matches reference"),
  (`pcs_challenger4_test, "PCS challenger continuation (α_pcs/α_fri/β/index) matches reference"),
  (`fri_fold_test, "FRI arity-2 fold_row matches reference"),
  (`ro_fold_test, "open_input reduced-opening math matches reference"),
  (`val_addsub_test, "non-native Goldilocks add/sub match reference"),
  (`val_muldiv_test, "non-native Goldilocks mul/inverse/div match reference"),
  (`ext_ops_test, "non-native ExtGoldilocks add/mul/inverse/div match reference"),
]

/-- Self-test entrypoints of the FOREIGN (byte-limb) Goldilocks module
(`Ix/MultiStark/GoldilocksBytes.lean`). Same reference vectors as the
native form's suite — the interface contract is identical semantics. The
module compiles as its own toplevel: it is the ALTERNATIVE to
`goldilocksNative` (same names by design), so it can never merge into the
verifier toplevel alongside it. -/
def bytesSelfTests : List (Lean.Name × String) := [
  (`gb_addsub_test, "byte-limb Goldilocks add/sub match reference"),
  (`gb_muldiv_test, "byte-limb Goldilocks mul/inverse match reference"),
  (`gb_ext_ops_test, "byte-limb ExtGoldilocks ops match reference"),
  (`gb_boundary_test, "byte-limb val_from_bytes/val_to_bytes/bytes_lt_modulus/two-adic root"),
]

/-- Compile the verifier-plus-tests toplevel (and the standalone byte-form
Goldilocks module) once, then execute each `*_test` entrypoint and assert it
returns `1`. -/
def selfTestSuite : IO UInt32 := do
  IO.println "multi-stark"
  let top ← match MultiStark.multiStarkTests with
    | .error e => IO.eprintln s!"verifier-tests toplevel merge failed: {e}"; return 1
    | .ok t => pure t
  let compiled ← match top.compile with
    | .error e => IO.eprintln s!"verifier-tests compilation failed: {e}"; return 1
    | .ok c => pure c
  let bytesCompiled ← match MultiStark.goldilocksBytes.compile with
    | .error e => IO.eprintln s!"goldilocks-bytes compilation failed: {e}"; return 1
    | .ok c => pure c
  let cases := selfTests.map (compiled, ·) ++ bytesSelfTests.map (bytesCompiled, ·)
  lspecEachIO cases fun (unit, (name, desc)) => pure <|
    match unit.getFuncIdx name with
    | none => test s!"{name}: {desc} — entrypoint not found" false
    | some idx =>
      match unit.bytecode.execute idx #[] default with
      | .error e => test s!"{name}: {desc} — execution failed: {e}" false
      | .ok (output, _, _) => test s!"{name}: {desc}" (output == #[Aiur.G.ofNat 1])

-- ════════════════════════════════════════════════════════════════════════════
-- `recursive-verifier`: prove factorial(5)=120, verify it, reject tampering
-- ════════════════════════════════════════════════════════════════════════════

/-- A tiny Aiur program: a BRANCHLESS entrypoint (single selector, no match)
that routes its argument through store/load before calling `factorial`. Its
circuit has 4 lookups (return, store, load, call) with raw degree-1
arguments, so synthesis groups them 2 per chained-accumulator step
(`lookup_group_size = 2`) — the recursive verifier's grouped logUp fold is
exercised end-to-end alongside the k = 1 branching/memory circuits. -/
def factorialProgram : Source.Toplevel := ⟦
  pub fn factorial(n: G) -> G {
    match n {
      0 => 1,
      _ => n * factorial(n - 1),
    }
  }

  pub fn fact_entry(n: G) -> G {
    factorial(load(store(n)))
  }
⟧

/-- Inner-proof commitment/FRI parameters. A tractable subset of production
(`numQueries := 3`, standard PoW regime: commit 0 / query 20); the verifier
code itself is blowup/query-count agnostic, and `pcs_check_witness` is shared
by both PoW phases, so the query-phase grinding exercises the commit-phase
code path too. -/
def recCommitParams : Aiur.CommitmentParameters :=
  { logBlowup := 2, capHeight := 0 }
def innerFri : Aiur.FriParameters :=
  { logFinalPolyLen := 0, maxLogArity := 1, numQueries := 3,
    commitProofOfWorkBits := 0, queryProofOfWorkBits := 20 }

/-- 8 little-endian bytes of a `Nat` (taken mod 2^64). -/
def u64le (n : Nat) : Array UInt8 :=
  (Array.range 8).map (fun i => UInt8.ofNat ((n >>> (8 * i)) % 256))

/-- Serialize the public claims for the verifier's IO channel, matching the
in-circuit `read_claims` wire format: u64 `num_claims`, then per claim a u64
`num_vals` followed by the `Val`s as canonical 8-byte little-endian `u64`s. -/
def serializeClaims (claims : Array (Array Aiur.G)) : ByteArray := Id.run do
  let mut out : Array UInt8 := u64le claims.size
  for c in claims do
    out := out ++ u64le c.size
    for g in c do
      out := out ++ u64le g.val.toNat
  return ⟨out⟩

def endToEndSuite : IO UInt32 := do
  -- ── factorial system ──────────────────────────────────────────────────────
  let facCompiled ← match factorialProgram.compile with
    | .error e => IO.eprintln s!"factorial compilation failed: {e}"; return 1
    | .ok c => pure c
  let facSystem := AiurSystem.build facCompiled.bytecode recCommitParams innerFri
  let facIdx ← match facCompiled.getFuncIdx `fact_entry with
    | some i => pure i
    | none => IO.eprintln "fact_entry entrypoint not found"; return 1

  -- ── prove factorial(5) = 120 (`G` is a reserved DSL token, spell it qualified)
  let input := #[Aiur.G.ofNat 5]
  let (claim, proof, _) ← match facSystem.prove facIdx input default with
    | .ok result => pure result
    | .error e => IO.eprintln s!"factorial prove failed: {e}"; return 1
  let expectedClaim := buildClaim facIdx input #[Aiur.G.ofNat 120]
  let proofBytes := proof.toBytes

  -- ── serialize proof (advice) + vk + claims, with public Blake3 digests ──
  let proofGs : Array Aiur.G := proofBytes.data.map .ofUInt8
  let vkBytes := facSystem.vkBytes
  let vkGs : Array Aiur.G := vkBytes.data.map .ofUInt8
  let claimBytes := serializeClaims #[claim]
  let claimGs : Array Aiur.G := claimBytes.data.map .ofUInt8
  -- Public input = vk digest ++ claims digest as packed-4-byte field
  -- elements (the FRI parameters are read in-circuit from the digest-bound
  -- vk, not passed publicly). `verifierPubInput` is the single home of the
  -- packing recipe.
  let pubInput : Array Aiur.G := MultiStark.verifierPubInput vkBytes claimBytes
  -- IO advice buffer: proof on channel 0, vk on 1, claims on 2 (each keyed `[0]`).
  let mkIO := fun (pGs cGs : Array Aiur.G) =>
    (((default : IOBuffer).extend 0 #[Aiur.G.ofNat 0] pGs).extend 1 #[Aiur.G.ofNat 0] vkGs).extend
      2 #[Aiur.G.ofNat 0] cGs

  -- ── verifier system (the PRODUCTION toplevel — no test circuits) ────────────
  let vTop ← match MultiStark.multiStark with
    | .error e => IO.eprintln s!"verifier toplevel merge failed: {e}"; return 1
    | .ok t => pure t
  let vCompiled ← match vTop.compile with
    | .error e => IO.eprintln s!"verifier compilation failed: {e}"; return 1
    | .ok c => pure c
  let vIdx ← match vCompiled.getFuncIdx `verify_multi_stark_proof with
    | some i => pure i
    | none => IO.eprintln "verify_multi_stark_proof entrypoint not found"; return 1

  -- ── negative-test inputs ────────────────────────────────────────────────────
  -- Tampered proof advice: flip byte 0 (the first stage_1-commitment limb) so the
  -- replayed Fiat-Shamir transcript diverges from the one the proof was made under.
  let badProofBytes :=
    proofBytes.set! 0 (UInt8.ofNat ((proofBytes.data[0]!.toNat + 1) % 256))
  -- Tampered claim (with a matching keccak digest): 120 → 121. Feeds a different
  -- value into Fiat-Shamir (→ different ζ) and the lookup accumulator, so the
  -- composition/quotient identity no longer holds even though the binding passes.
  let badClaim : Array Aiur.G := claim.set! (claim.size - 1) (Aiur.G.ofNat 121)
  let badClaimBytes := serializeClaims #[badClaim]
  let badClaimInput : Array Aiur.G :=
    MultiStark.verifierPubInput vkBytes badClaimBytes

  -- ── run the (expensive) checks, then assert ─────────────────────────────────
  IO.println "recursive-verifier (proving + recursive verification, ~1.5 min)…"
  let innerVerify := facSystem.verify claim (.ofBytes proofBytes)
  -- Native path: Rust-built advice buffer + codegen'd verifier
  -- (`crates/ixvm-codegen/src/aiur_multi_stark.rs`).
  let honest :=
    vCompiled.bytecode.executeMultiStark vIdx pubInput proofBytes vkBytes claimBytes
  -- Interpreter over the Lean-built buffer: the parity reference for the
  -- codegen'd verifier — same output, same per-circuit query counts.
  let honestInterp := vCompiled.bytecode.execute vIdx pubInput (mkIO proofGs claimGs)
  let parity : Bool := match honest, honestInterp with
    | .ok (out, qc), .ok (outI, _, qcI) =>
      out == outI && qc.size == qcI.size &&
        (qc.zip qcI).all fun (a, b) =>
          a.uniqueRows == b.uniqueRows && a.totalHits == b.totalHits
    | _, _ => false
  let tamperedProof :=
    vCompiled.bytecode.executeMultiStark vIdx pubInput badProofBytes vkBytes claimBytes
  let tamperedClaim :=
    vCompiled.bytecode.executeMultiStark vIdx badClaimInput proofBytes vkBytes badClaimBytes
  lspecIO (.ofList [("recursive-verifier", [
    test "factorial(5) claim = #[functionChannel, facIdx, 5, 120]" (claim == expectedClaim),
    expectOk "inner factorial proof verifies" innerVerify,
    expectOk "verifier accepts honest proof (vk digest bound + OOD + FRI)" honest,
    test "codegen'd verifier matches interpreter (output + query counts)" parity,
    expectErr "tampered proof advice rejected (verification checks)" tamperedProof,
    expectErr "tampered claim rejected (OOD/accumulator mismatch)" tamperedClaim,
  ])]) []

-- ════════════════════════════════════════════════════════════════════════════
-- `bytes-verifier`: the SAME pipeline over `multiStarkBytes` — the
-- byte-limb (outer-field-independent) verifier toplevel
-- ════════════════════════════════════════════════════════════════════════════

/-- The byte-limb Goldilocks verifier toplevel, executed under the existing
Goldilocks interpreter against the same factorial stage-2 vectors the native
verifier passes. The byte module's semantics are outer-field-independent
(byte gadgets and carry chains), so acceptance here validates the exact
program a smaller-field backend (KoalaBear/Hypercube) would prove — before
any such machinery is wired. Interpreter only: the byte toplevel has no
codegen'd runner. -/
def bytesEndToEndSuite : IO UInt32 := do
  -- ── factorial system + proof (same recipe as `endToEndSuite`) ─────────────
  let facCompiled ← match factorialProgram.compile with
    | .error e => IO.eprintln s!"factorial compilation failed: {e}"; return 1
    | .ok c => pure c
  let facSystem := AiurSystem.build facCompiled.bytecode recCommitParams innerFri
  let facIdx ← match facCompiled.getFuncIdx `fact_entry with
    | some i => pure i
    | none => IO.eprintln "fact_entry entrypoint not found"; return 1
  let (claim, proof, _) ← match facSystem.prove facIdx #[Aiur.G.ofNat 5] default with
    | .ok result => pure result
    | .error e => IO.eprintln s!"factorial prove failed: {e}"; return 1
  let proofBytes := proof.toBytes
  let proofGs : Array Aiur.G := proofBytes.data.map .ofUInt8
  let vkBytes := facSystem.vkBytes
  let vkGs : Array Aiur.G := vkBytes.data.map .ofUInt8
  let claimBytes := serializeClaims #[claim]
  let claimGs : Array Aiur.G := claimBytes.data.map .ofUInt8
  let pubInput : Array Aiur.G := MultiStark.verifierPubInput vkBytes claimBytes
  let mkIO := fun (pGs cGs : Array Aiur.G) =>
    (((default : IOBuffer).extend 0 #[Aiur.G.ofNat 0] pGs).extend 1 #[Aiur.G.ofNat 0] vkGs).extend
      2 #[Aiur.G.ofNat 0] cGs

  -- ── the FOREIGN production toplevel ───────────────────────────────────────
  let vTop ← match MultiStark.multiStarkBytes with
    | .error e => IO.eprintln s!"byte toplevel merge failed: {e}"; return 1
    | .ok t => pure t
  let vCompiled ← match vTop.compile with
    | .error e => IO.eprintln s!"byte-form compilation failed: {e}"; return 1
    | .ok c => pure c
  let vIdx ← match vCompiled.getFuncIdx `verify_multi_stark_proof with
    | some i => pure i
    | none => IO.eprintln "verify_multi_stark_proof entrypoint not found"; return 1

  -- ── tampered inputs (same tampering as the native suite) ──────────────────
  let badProofBytes :=
    proofBytes.set! 0 (UInt8.ofNat ((proofBytes.data[0]!.toNat + 1) % 256))
  let badProofGs : Array Aiur.G := badProofBytes.data.map .ofUInt8
  let badClaim : Array Aiur.G := claim.set! (claim.size - 1) (Aiur.G.ofNat 121)
  let badClaimBytes := serializeClaims #[badClaim]
  let badClaimGs : Array Aiur.G := badClaimBytes.data.map .ofUInt8
  let badClaimInput : Array Aiur.G :=
    MultiStark.verifierPubInput vkBytes badClaimBytes

  IO.println "bytes-verifier (byte-limb Goldilocks, interpreted; slow)…"
  let honest := vCompiled.bytecode.execute vIdx pubInput (mkIO proofGs claimGs)
  let tamperedProof := vCompiled.bytecode.execute vIdx pubInput (mkIO badProofGs claimGs)
  let tamperedClaim :=
    vCompiled.bytecode.execute vIdx badClaimInput (mkIO proofGs badClaimGs)
  lspecIO (.ofList [("bytes-verifier", [
    expectOk "byte-form verifier accepts honest proof (byte-limb Goldilocks)" honest,
    expectErr "tampered proof advice rejected (byte-form)" tamperedProof,
    expectErr "tampered claim rejected (byte-form)" tamperedClaim,
  ])]) []


/-- Stage 2 on Hypercube: the byte-form verifier over the KOALABEAR
profiles (`multiStarkKoalaBear`) verifying a real stage-1 proof, proven by
the Hypercube backend. Gates in order: the compiled toplevel's constants
fit KoalaBear's modulus; the interpreter accepts the honest proof and
rejects a tampered one (2-byte public digests); then the FFT-model stats
and the Hypercube prove/verify with wall times and peak RSS. -/
def stage2HypercubeSuite : IO UInt32 := do
  let hwm : IO String := do
    let s ← IO.FS.readFile "/proc/self/status"
    pure <| (((s.splitOn "\n").find? (·.startsWith "VmHWM")).getD "VmHWM: ?").trimAscii.toString
  IO.println "stage2-hypercube (byte verifier over KoalaBear, proved by Hypercube)…"
  -- Stage 1 at PRODUCTION parameters by default (`defaultFriParameters`:
  -- 100 queries, 20 PoW bits — identical to `innerFri` except query count);
  -- `IX_S2_QUERIES` overrides for quick runs.
  let queries := ((← IO.getEnv "IX_S2_QUERIES").bind (·.toNat?)).getD
    Aiur.defaultFriParameters.numQueries
  let s1Fri := { innerFri with numQueries := queries }
  IO.println s!"  stage-1 FRI queries: {queries}"
  let facCompiled ← match factorialProgram.compile with
    | .error e => IO.eprintln s!"factorial compilation failed: {e}"; return 1
    | .ok c => pure c
  let facSystem := AiurSystem.build facCompiled.bytecode recCommitParams s1Fri
  let facIdx ← match facCompiled.getFuncIdx `fact_entry with
    | some i => pure i
    | none => IO.eprintln "fact_entry entrypoint not found"; return 1
  let (claim, proof, _) ← match facSystem.prove facIdx #[Aiur.G.ofNat 5] default with
    | .ok result => pure result
    | .error e => IO.eprintln s!"factorial prove failed: {e}"; return 1
  let proofBytes := proof.toBytes
  let proofGs : Array Aiur.G := proofBytes.data.map .ofUInt8
  let vkBytes := facSystem.vkBytes
  let vkGs : Array Aiur.G := vkBytes.data.map .ofUInt8
  let claimBytes := serializeClaims #[claim]
  let claimGs : Array Aiur.G := claimBytes.data.map .ofUInt8
  let pubInput : Array Aiur.G := MultiStark.verifierPubInput2 vkBytes claimBytes
  let mkIO := fun (pGs : Array Aiur.G) =>
    (((default : IOBuffer).extend 0 #[Aiur.G.ofNat 0] pGs).extend 1 #[Aiur.G.ofNat 0] vkGs).extend
      2 #[Aiur.G.ofNat 0] claimGs
  IO.println s!"  stage-1 proof: {proofBytes.size} bytes (vk {vkBytes.size} bytes)"

  let vTop ← match MultiStark.multiStarkKoalaBear with
    | .error e => IO.eprintln s!"koalabear verifier merge failed: {e}"; return 1
    | .ok t => pure t
  let vCompiled ← match vTop.compile with
    | .error e => IO.eprintln s!"koalabear verifier compilation failed: {e}"; return 1
    | .ok c => pure c
  match vCompiled.bytecode.checkConstants 2130706433 with
    | .error e => IO.eprintln s!"checkConstants(koalabear): {e}"; return 1
    | .ok _ => IO.println "  constants fit KoalaBear's modulus"
  let vIdx ← match vCompiled.getFuncIdx `verify_multi_stark_proof with
    | some i => pure i
    | none => IO.eprintln "verify_multi_stark_proof entrypoint not found"; return 1

  match vCompiled.bytecode.execute vIdx pubInput (mkIO proofGs) with
  | .error e => IO.eprintln s!"interpreter rejected the honest proof: {e}"; return 1
  | .ok (_, _, queryCounts) =>
    IO.println "  interpreter accepts the honest proof"
    let badProofBytes :=
      proofBytes.set! 0 (UInt8.ofNat ((proofBytes.data[0]!.toNat + 1) % 256))
    let badProofGs : Array Aiur.G := badProofBytes.data.map .ofUInt8
    match vCompiled.bytecode.execute vIdx pubInput (mkIO badProofGs) with
    | .ok _ => IO.eprintln "tampered proof was ACCEPTED"; return 1
    | .error _ => IO.println "  interpreter rejects a tampered proof"
    let sys := AiurSystem.build vCompiled.bytecode recCommitParams innerFri
    let stats := Aiur.computeStats vCompiled queryCounts sys.circuitShapes
    let live := stats.circuits.filter (·.height > 0)
    let pow2 (n : Nat) : Nat := if n ≤ 1 then n else Nat.nextPowerOfTwo n
    let area := live.foldl (fun a c => a + c.width * pow2 c.height) 0
    let tallest := live.foldl (fun a c => max a c.height) 0
    IO.println s!"  stats: totalFftCost {stats.totalFftCost}, live circuits {live.size}, \
      Σ width·2^⌈h⌉ = {area}, tallest height {tallest}"
    for c in (live.qsort (fun a b => a.fftCost > b.fftCost)).extract 0 6 do
      IO.println s!"    {c.name}: w {c.width}, h {c.height}, fft {c.fftCost}"
    -- The jagged PCS bounds each round's area below 2^30 (slop-jagged
    -- `AreaOutOfBounds`); don't burn minutes proving a shard the verifier
    -- must reject. `IX_S2_FORCE=1` attempts it anyway.
    if area ≥ 2 ^ 30 && (← IO.getEnv "IX_S2_FORCE").isNone then
      IO.println s!"  area {area} ≥ 2^30: single-shard hypercube IMPOSSIBLE \
        (jagged PCS AreaOutOfBounds); skipping prove — sharding required"
      return 0
    IO.println s!"  {← hwm} (before hypercube)"
    let t0 ← IO.monoMsNow
    let hSys ← match Aiur.HypercubeSystem.build vCompiled.bytecode vIdx with
      | .error e => IO.eprintln s!"hypercube build failed: {e}"; return 1
      | .ok s => pure s
    let t1 ← IO.monoMsNow
    let (hClaim, blob) ← match hSys.prove pubInput (mkIO proofGs) with
      | .error e => IO.eprintln s!"hypercube prove failed: {e}"; return 1
      | .ok r => pure r
    let t2 ← IO.monoMsNow
    IO.println "── hypercube (KoalaBear, env-overridable ProverParams)"
    IO.println s!"  machine build {t1 - t0} ms"
    IO.println s!"  prove         {t2 - t1} ms"
    IO.println s!"  blob          {blob.size} bytes (vk + proof)"
    IO.println s!"  {← hwm} (process peak)"
    match Aiur.HypercubeSystem.verify hSys hClaim blob with
      | .error e => IO.eprintln s!"hypercube verify failed: {e}"; return 1
      | .ok _ => pure ()
    let t3 ← IO.monoMsNow
    IO.println s!"  verify        {t3 - t2} ms"
    let expected := #[Aiur.G.ofNat 0, Aiur.G.ofNat vIdx] ++ pubInput
    IO.println s!"  claim ok: {hClaim == expected}"
    pure 0

/-- Exercises the Hypercube sharding path: prove factorial and verify,
also checking that a tampered blob and a wrong claim are rejected. The
per-shard cell budget comes from the environment (`IX_HC_SHARD_CELLS`,
read by the FFI at system build); run with a tiny budget to force several
shards — cutting function memoization, memory pointer chains and byte
lookups across them, all rebalanced by the septic-digest adapter chips —
and without one for the degenerate single-shard path. -/
def hypercubeShardSuite : IO UInt32 := do
  let cells := (← IO.getEnv "IX_HC_SHARD_CELLS").getD "∞ (single shard)"
  IO.println s!"hypercube-shard (factorial, shard budget: {cells} cells)…"
  let facCompiled ← match factorialProgram.compile with
    | .error e => IO.eprintln s!"factorial compilation failed: {e}"; return 1
    | .ok c => pure c
  let facIdx ← match facCompiled.getFuncIdx `fact_entry with
    | some i => pure i
    | none => IO.eprintln "fact_entry entrypoint not found"; return 1
  let sys ← match Aiur.HypercubeSystem.build facCompiled.bytecode facIdx with
    | .error e => IO.eprintln s!"hypercube build failed: {e}"; return 1
    | .ok s => pure s
  let (claim, blob) ← match sys.prove #[Aiur.G.ofNat 5] default with
    | .error e => IO.eprintln s!"hypercube prove failed: {e}"; return 1
    | .ok r => pure r
  match Aiur.HypercubeSystem.verify sys claim blob with
    | .error e => IO.eprintln s!"hypercube verify failed: {e}"; return 1
    | .ok _ => IO.println s!"  verified, blob {blob.size} bytes"
  -- A tampered blob must not verify.
  let bad := blob.set! 0 (blob.get! 0 + 1)
  match Aiur.HypercubeSystem.verify sys claim bad with
    | .ok _ => IO.eprintln "tampered blob was ACCEPTED"; return 1
    | .error _ => IO.println "  tampered blob rejected"
  -- A wrong claim must not verify.
  let wrong := claim.set! 0 (Aiur.G.ofNat 1)
  match Aiur.HypercubeSystem.verify sys wrong blob with
    | .ok _ => IO.eprintln "wrong claim was ACCEPTED"; return 1
    | .error _ => IO.println "  wrong claim rejected"
  let expected := #[Aiur.G.ofNat 0, Aiur.G.ofNat facIdx, Aiur.G.ofNat 5,
    Aiur.G.ofNat 120]
  IO.println s!"  claim ok: {claim == expected}"
  if claim != expected then return 1
  pure 0

end Tests.MultiStark

end
