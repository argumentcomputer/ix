module

public import Tests.ProofHelpers
public import Tests.MultiStarkCircuits
public import Ix.Aiur.Meta
public import Ix.Aiur.Protocol
public import Ix.Aiur.Compiler
public import Ix.MultiStark
public import Blake3.Rust

/-!
# Tests for the Multi-STARK recursive verifier

These exercise `Ix/MultiStark.lean` (the in-circuit verifier) the way the former
standalone `RecursiveVerifier.lean` executable did, split into two primary
runners (registered in `Tests/Main.lean`, both wired into `ci.yml`):

* **`multi-stark`** — `selfTestSuite`. Executes the verifier's primitive
  `*_test` entrypoints (`Tests/MultiStarkCircuits.lean`), each of which validates one
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
circuits never widen the production verifier — see `Tests/MultiStarkCircuits.lean`.
-/

public section

open LSpec Aiur

namespace Tests.MultiStark
open Tests.ProofHelpers

-- ════════════════════════════════════════════════════════════════════════════
-- `multi-stark`: verifier primitive self-tests (execution-only, no proving)
-- ════════════════════════════════════════════════════════════════════════════

/-- The verifier's primitive self-test entrypoints (`Tests/MultiStarkCircuits.lean`)
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

/-- A branching entrypoint with eighteen gated store/load/call/return lookups for
synthesis to choose two messages per accumulator at quotient degree four.
The smaller factorial and memory circuits retain quotient degree two, so
recursive verification exercises both degrees within the same proof. -/
def factorialProgram : Source.Toplevel := ⟦
  pub fn factorial(n: G) -> G {
    match n {
      0 => 1,
      _ => n * factorial(n - 1),
    }
  }

  pub fn fact_entry(n: G) -> G {
    match n {
      0 => 1,
      _ =>
        let a = load(store(n));
        let b = load(store(n + 1));
        let c = load(store(n + 2));
        let d = load(store(n + 3));
        let e = load(store(n + 4));
        let f = load(store(n + 5));
        let g = load(store(n + 6));
        let h = load(store(n + 7));
        assert_eq!(b, a + 1);
        assert_eq!(c, a + 2);
        assert_eq!(d, a + 3);
        assert_eq!(e, a + 4);
        assert_eq!(f, a + 5);
        assert_eq!(g, a + 6);
        assert_eq!(h, a + 7);
        factorial(a),
    }
  }
⟧

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
  let mixedQuotients := facSystem.circuitShapes.any (·.quotientDegree == 4) &&
    facSystem.circuitShapes.any (·.quotientDegree == 2)
  -- Verify and serialize the proof transport consumed in-circuit.
  let proofBytes ← match facSystem.proofToAdviceBytes claim proof with
    | .ok bytes => pure bytes
    | .error e => IO.eprintln s!"advice re-encoding failed: {e}"; return 1

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
  let vCompiled ← match vTop.compileWithGroups MultiStark.verifierFunctionGroups with
    | .error e => IO.eprintln s!"verifier compilation failed: {e}"; return 1
    | .ok c => pure c
  let vIdx ← match vCompiled.getFuncIdx `verify_multi_stark_proof with
    | some i => pure i
    | none => IO.eprintln "verify_multi_stark_proof entrypoint not found"; return 1

  -- ── negative-test inputs ────────────────────────────────────────────────────
  -- Tampered proof advice: locate the first stage-1 commitment byte after the
  -- native proof's `Vec<bool>` activation bitmap and cap-length prefix. This
  -- keeps the proof structurally parseable while forcing Fiat-Shamir and the
  -- Merkle checks away from the proof that was actually produced.
  let activeLen := (List.range 8).foldl (fun n i =>
    n ||| (proofBytes.data[i]!.toUInt64 <<< (i * 8).toUInt64)) 0
  let firstCommitByte := 8 + activeLen.toNat + 8
  let badProofBytes :=
    proofBytes.set! firstCommitByte
      (UInt8.ofNat ((proofBytes.data[firstCommitByte]!.toNat + 1) % 256))
  -- Tampered claim (with a matching keccak digest): 120 → 121. Feeds a different
  -- value into Fiat-Shamir (→ different ζ) and the lookup accumulator, so the
  -- composition/quotient identity no longer holds even though the binding passes.
  let badClaim : Array Aiur.G := claim.set! (claim.size - 1) (Aiur.G.ofNat 121)
  let badClaimBytes := serializeClaims #[badClaim]
  let badClaimInput : Array Aiur.G :=
    MultiStark.verifierPubInput vkBytes badClaimBytes

  -- ── run the (expensive) checks, then assert ─────────────────────────────────
  IO.println "recursive-verifier (proving + recursive verification, ~1.5 min)…"
  -- Native wire-format roundtrip before exercising the in-circuit path.
  let innerVerify := facSystem.verify claim (.ofBytes proof.toBytes)
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
    test s!"inner proof exercises quotient degrees two and four (main/stage2/quotient: {facSystem.circuitShapes.map fun s => (s.mainWidth, s.stage2Width, s.quotientDegree)})" mixedQuotients,
    expectOk "inner factorial proof verifies" innerVerify,
    expectOk "verifier accepts honest proof (vk digest bound + OOD + FRI)" honest,
    test "codegen'd verifier matches interpreter (output + query counts)" parity,
    expectErr "tampered proof advice rejected (verification checks)" tamperedProof,
    expectErr "tampered claim rejected (OOD/accumulator mismatch)" tamperedClaim,
  ])]) []


end Tests.MultiStark

end
