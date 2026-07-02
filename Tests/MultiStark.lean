module

public import LSpec
public import Ix.Aiur.Meta
public import Ix.Aiur.Protocol
public import Ix.Aiur.Compiler
public import Ix.MultiStark
public import Blake3.Rust

/-!
# Tests for the Multi-STARK recursive verifier

These exercise `Ix/MultiStark.lean` (the in-circuit verifier) the way the former
standalone `RecursiveVerifier.lean` executable did, split into two ignored
runners (registered in `Tests/Main.lean`, both wired into `ci.yml`):

* **`multi-stark`** — `selfTestSuite`. Executes the verifier's primitive
  `*_test` entrypoints (`Ix/MultiStark/Tests.lean`), each of which validates one
  primitive (Blake3 MMCS leaf/compress, Merkle `verify_batch`, the challenger,
  FRI fold + reduced openings, non-native Goldilocks/ExtGoldilocks arithmetic)
  against the Rust reference values from `multi-stark` (`gen_pcs_refs`). Cheap: just
  bytecode execution, no proving. The in-circuit `assert_eq!`s do the checking;
  every entrypoint returns `1` on success.

* **`recursive-verifier`** — `endToEndSuite`. The full pipeline (~1.5 min,
  dominated by proving + the verifier executions):
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
  (`sample_bits_test, "challenger sample_bits matches reference"),
  (`pcs_challenger4_test, "PCS challenger continuation (α_pcs/α_fri/β/index) matches reference"),
  (`fri_fold_test, "FRI arity-2 fold_row matches reference"),
  (`ro_fold_test, "open_input reduced-opening math matches reference"),
  (`gl_addsub_test, "non-native Goldilocks add/sub match reference"),
  (`gl_muldiv_test, "non-native Goldilocks mul/inverse/div match reference"),
  (`eg_ops_test, "non-native ExtGoldilocks add/mul/inverse/div match reference"),
]

/-- Compile the verifier-plus-tests toplevel once, then execute each `*_test`
entrypoint and assert it returns `1`. -/
def selfTestSuite : IO UInt32 := do
  IO.println "multi-stark"
  let top ← match MultiStark.multiStarkTests with
    | .error e => IO.eprintln s!"verifier-tests toplevel merge failed: {e}"; return 1
    | .ok t => pure t
  let compiled ← match top.compile with
    | .error e => IO.eprintln s!"verifier-tests compilation failed: {e}"; return 1
    | .ok c => pure c
  lspecEachIO selfTests fun (name, desc) => pure <|
    match compiled.getFuncIdx name with
    | none => test s!"{name}: {desc} — entrypoint not found" false
    | some idx =>
      match compiled.bytecode.execute idx #[] default with
      | .error e => test s!"{name}: {desc} — execution failed: {e}" false
      | .ok (output, _, _) => test s!"{name}: {desc}" (output == #[Aiur.G.ofNat 1])

-- ════════════════════════════════════════════════════════════════════════════
-- `recursive-verifier`: prove factorial(5)=120, verify it, reject tampering
-- ════════════════════════════════════════════════════════════════════════════

/-- A tiny Aiur program: `factorial` as the proving entrypoint. -/
def factorialProgram : Source.Toplevel := ⟦
  pub fn factorial(n: G) -> G {
    match n {
      0 => 1,
      _ => n * factorial(n - 1),
    }
  }
⟧

/-- Inner-proof commitment/FRI parameters. A tractable subset of production
(`numQueries := 3`) that still drives every generalized verifier path; the
verifier code itself is blowup/query-count agnostic. -/
def recCommitParams : Aiur.CommitmentParameters :=
  { logBlowup := 2, capHeight := 0 }
def innerFri : Aiur.FriParameters :=
  { logFinalPolyLen := 0, maxLogArity := 1, numQueries := 3,
    commitProofOfWorkBits := 20, queryProofOfWorkBits := 0 }

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
  let facSystem := AiurSystem.build facCompiled.bytecode recCommitParams
  let facIdx ← match facCompiled.getFuncIdx `factorial with
    | some i => pure i
    | none => IO.eprintln "factorial entrypoint not found"; return 1

  -- ── prove factorial(5) = 120 (`G` is a reserved DSL token, spell it qualified)
  let input := #[Aiur.G.ofNat 5]
  let (claim, proof, _) := facSystem.prove innerFri facIdx input default
  let expectedClaim := buildClaim facIdx input #[Aiur.G.ofNat 120]
  let proofBytes := proof.toBytes

  -- ── serialize proof (advice) + vk + claims, with public Blake3 digests ──
  let proofGs : Array Aiur.G := proofBytes.data.map .ofUInt8
  let vkBytes := facSystem.vkBytes
  let sysDigestInput : Array Aiur.G := (Blake3.Rust.hash vkBytes).val.data.map .ofUInt8
  let vkGs : Array Aiur.G := vkBytes.data.map .ofUInt8
  let claimBytes := serializeClaims #[claim]
  let claimsDigestInput : Array Aiur.G := (Blake3.Rust.hash claimBytes).val.data.map .ofUInt8
  let claimGs : Array Aiur.G := claimBytes.data.map .ofUInt8
  -- Public input = vk digest ++ claims digest ++ (num_queries, commit_pow, log_blowup).
  let friParamInput : Array Aiur.G :=
    #[Aiur.G.ofNat innerFri.numQueries, Aiur.G.ofNat innerFri.commitProofOfWorkBits,
      Aiur.G.ofNat recCommitParams.logBlowup]
  let pubInput : Array Aiur.G := sysDigestInput ++ claimsDigestInput ++ friParamInput
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
  let badProofGs := proofGs.set! 0 (Aiur.G.ofNat ((proofBytes.data[0]!.toNat + 1) % 256))
  -- Tampered claim (with a matching keccak digest): 120 → 121. Feeds a different
  -- value into Fiat-Shamir (→ different ζ) and the lookup accumulator, so the
  -- composition/quotient identity no longer holds even though the binding passes.
  let badClaim : Array Aiur.G := claim.set! (claim.size - 1) (Aiur.G.ofNat 121)
  let badClaimBytes := serializeClaims #[badClaim]
  let badClaimInput : Array Aiur.G :=
    sysDigestInput ++ ((Blake3.Rust.hash badClaimBytes).val.data.map .ofUInt8) ++ friParamInput

  -- ── run the (expensive) checks, then assert ─────────────────────────────────
  IO.println "recursive-verifier (proving + recursive verification, ~1.5 min)…"
  let innerVerify := facSystem.verify innerFri claim (.ofBytes proofBytes)
  let honest := vCompiled.bytecode.execute vIdx pubInput (mkIO proofGs claimGs)
  let tamperedProof := vCompiled.bytecode.execute vIdx pubInput (mkIO badProofGs claimGs)
  let tamperedClaim :=
    vCompiled.bytecode.execute vIdx badClaimInput (mkIO proofGs (badClaimBytes.data.map .ofUInt8))
  lspecIO (.ofList [("recursive-verifier", [
    test "factorial(5) claim = #[functionChannel, facIdx, 5, 120]" (claim == expectedClaim),
    expectOk "inner factorial proof verifies" innerVerify,
    expectOk "verifier accepts honest proof (vk digest bound + OOD + FRI)" honest,
    expectErr "tampered proof advice rejected (verification checks)" tamperedProof,
    expectErr "tampered claim rejected (OOD/accumulator mismatch)" tamperedClaim,
  ])]) []

end Tests.MultiStark

end
