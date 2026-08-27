module

public import LSpec
public import Ix.Aiur.Meta
public import Ix.Aiur.Protocol
public import Ix.Aiur.Compiler
public import Ix.MultiStark
public import Ix.Cli.CheckCmd
public import Ix.Claim
public import Ix.AssumptionTree
public import Ix.Merkle
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
  let (claim, proof, _) := facSystem.prove facIdx input default
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
-- `aggregate-first`: execute a real two-child canonical set-discharge join
-- ═════════════════════════════════════════════════════════════════════════════

/-- A tiny stand-in recursion system used to exercise `join_two` without first
proving the full recursive verifier (the production lift needs tens of GiB).
The join still verifies two real Multi-STARK proofs and enforces their vk,
entrypoint, public-input, and nested-claim bindings. -/
def joinChildProgram : Source.Toplevel := ⟦
  pub fn fake_verify_claim(_digest: [G; 8]) { () }
  pub fn fake_lift(_system_digest: [G; 8], _claims_digest: [G; 8]) { () }
  pub fn fake_join(allowed_digest: [G; 8], _out_claim_digest: [G; 8]) {
    assert_eq!(load(store(allowed_digest[0])), allowed_digest[0]);
    ()
  }
⟧

private def bytesAsGs (bytes : ByteArray) : Array Aiur.G :=
  bytes.data.map .ofUInt8

private def u32le4 (n : Nat) : Array UInt8 :=
  (Array.range 4).map fun i => UInt8.ofNat ((n >>> (8 * i)) % 256)

private def minimalIxes (treeTail : Array UInt8) : ByteArray :=
  let shard := fun id => u32le4 id ++ Array.replicate 24 0 ++ #[0] ++
    u32le4 0 ++ u32le4 0
  ⟨#[0x49, 0x58, 0x45, 0x53, 0, 0, 0, 0] ++ Array.replicate 16 0 ++
    u32le4 2 ++ shard 0 ++ shard 1 ++ treeTail⟩

private def canonicalTree (leaves : Array Address) : Ix.AssumptionTree :=
  (Ix.AssumptionTree.canonical leaves).get!

private def seedJoinTree (io : IOBuffer) (tree : Ix.AssumptionTree) : IOBuffer :=
  io.extend 5 (bytesAsGs tree.root.hash)
    (bytesAsGs (Ix.AssumptionTree.ser tree))

private def seedJoinTrees (io : IOBuffer)
    (trees : Array Ix.AssumptionTree) : IOBuffer :=
  trees.foldl seedJoinTree io

def joinSmokeSuite : IO UInt32 := do
  let childCompiled ← match joinChildProgram.compile with
    | .error e => IO.eprintln s!"join child compilation failed: {e}"; return 1
    | .ok c => pure c
  let childSystem := AiurSystem.build childCompiled.bytecode recCommitParams innerFri
  let verifyIdx := childCompiled.getFuncIdx `fake_verify_claim |>.get!
  let liftIdx := childCompiled.getFuncIdx `fake_lift |>.get!
  let childJoinIdx := childCompiled.getFuncIdx `fake_join |>.get!

  -- Two conditional shard statements whose assumptions cross the subject
  -- boundary.  The join must compute
  --   subjects    = {a,b} ∪ {c}       = {a,b,c}
  --   assumptions = ({c,d} ∪ {a}) ∖ {a,b,c} = {d}.
  let a := Address.blake3 "aggregate-a".toUTF8
  let b := Address.blake3 "aggregate-b".toUTF8
  let c := Address.blake3 "aggregate-c".toUTF8
  let d := Address.blake3 "aggregate-d".toUTF8
  let e := Address.blake3 "aggregate-extra".toUTF8
  let leftSubjects := canonicalTree #[a, b]
  let leftAssumptions := canonicalTree #[c, d]
  let rightSubjects := canonicalTree #[c]
  let rightAssumptions := canonicalTree #[a]
  let leftStatement : MultiStark.CheckEnvTrees :=
    { subjects := leftSubjects, assumptions := some leftAssumptions }
  let rightStatement : MultiStark.CheckEnvTrees :=
    { subjects := rightSubjects, assumptions := some rightAssumptions }
  let outputStatement := leftStatement.join rightStatement
  let outputSubjects := outputStatement.subjects
  let outputAssumptions := outputStatement.assumptions.get!
  let adviceTrees := MultiStark.CheckEnvTrees.adviceTrees
    leftStatement rightStatement outputStatement
  let leftClaimBytes := Ix.Claim.ser leftStatement.claim
  let rightClaimBytes := Ix.Claim.ser rightStatement.claim

  -- A lift's outer claim commits to serialized IxVM claims. Build those
  -- nested preimages exactly as production does, then prove two cheap stand-in
  -- lift executions under one vk.
  let mkLift (claimBytes : ByteArray) :=
    let innerInput := MultiStark.digestGs claimBytes
    let innerClaim := Aiur.buildClaim verifyIdx innerInput #[]
    let innerClaimsBytes := MultiStark.serializeClaims #[innerClaim]
    let fakeIxvmVk : ByteArray := ⟨#[0x49, 0x58, 0x56, 0x4d]⟩
    let liftInput := MultiStark.verifierPubInput fakeIxvmVk innerClaimsBytes
    let (outerClaim, proof, _) := childSystem.prove liftIdx liftInput default
    (fakeIxvmVk, innerClaimsBytes, outerClaim, proof)
  let (fakeIxvmVk, leftInnerClaims, leftOuter, leftProof) := mkLift leftClaimBytes
  let (_, rightInnerClaims, rightOuter, rightProof) := mkLift rightClaimBytes

  let recursionVk := childSystem.vkBytes
  let allowed := MultiStark.allowedBlob fakeIxvmVk verifyIdx recursionVk
    liftIdx childJoinIdx
  let outputClaimBytes := Ix.Claim.ser outputStatement.claim
  let pubInput := MultiStark.joinPubInput allowed outputClaimBytes

  let leftOuterBytes := MultiStark.serializeClaims #[leftOuter]
  let rightOuterBytes := MultiStark.serializeClaims #[rightOuter]
  let leftInnerDigest := MultiStark.digestGs leftInnerClaims
  let rightInnerDigest := MultiStark.digestGs rightInnerClaims
  let leftClaimDigest := MultiStark.digestGs leftClaimBytes
  let rightClaimDigest := MultiStark.digestGs rightClaimBytes
  let preimagesBlob := MultiStark.joinPreimagesBlob
    #[leftInnerClaims, rightInnerClaims, leftClaimBytes, rightClaimBytes]
  let treesBlob := MultiStark.joinTreesBlob
    adviceTrees
  let zeroKey := #[Aiur.G.ofNat 0]
  let oneKey := #[Aiur.G.ofNat 1]
  let twoKey := #[Aiur.G.ofNat 2]
  let io := seedJoinTrees ((default : IOBuffer)
    |>.extend 0 zeroKey (bytesAsGs leftProof.toBytes)
    |>.extend 0 oneKey (bytesAsGs rightProof.toBytes)
    |>.extend 1 zeroKey (bytesAsGs recursionVk)
    |>.extend 2 zeroKey (bytesAsGs leftOuterBytes)
    |>.extend 2 oneKey (bytesAsGs rightOuterBytes)
    |>.extend 2 twoKey (bytesAsGs outputClaimBytes)
    |>.extend 3 zeroKey (bytesAsGs allowed)
    |>.extend 4 leftInnerDigest (bytesAsGs leftInnerClaims)
    |>.extend 4 rightInnerDigest (bytesAsGs rightInnerClaims)
    |>.extend 4 leftClaimDigest (bytesAsGs leftClaimBytes)
    |>.extend 4 rightClaimDigest (bytesAsGs rightClaimBytes))
    adviceTrees

  let top ← match MultiStark.multiStark with
    | .error e => IO.eprintln s!"aggregate toplevel merge failed: {e}"; return 1
    | .ok t => pure t
  let compiled ← match top.compile with
    | .error e => IO.eprintln s!"aggregate compilation failed: {e}"; return 1
    | .ok c => pure c
  let joinIdx := compiled.getFuncIdx `join_two |>.get!
  let honestInterp := compiled.bytecode.execute joinIdx pubInput io
  let honest := compiled.bytecode.executeMultiStarkJoin joinIdx pubInput
    leftProof.toBytes rightProof.toBytes recursionVk leftOuterBytes rightOuterBytes
    outputClaimBytes allowed preimagesBlob treesBlob
  let nativeParity : Bool := match honest, honestInterp with
    | .ok (out, qc), .ok (outI, _, qcI) =>
      out == outI && qc.size == qcI.size &&
        (qc.zip qcI).all fun (x, y) =>
          x.uniqueRows == y.uniqueRows && x.totalHits == y.totalHits
    | _, _ => false

  let malformedFraming := compiled.bytecode.executeMultiStarkJoin joinIdx pubInput
    leftProof.toBytes rightProof.toBytes recursionVk leftOuterBytes rightOuterBytes
    outputClaimBytes allowed ⟨#[]⟩ treesBlob

  -- Exercise the other child decoder arm: an aggregate child must expose the
  -- same allowed digest transitively, while its output-claim preimage replaces
  -- a lift's two nested preimages.
  let joinChildInput := MultiStark.joinPubInput allowed leftClaimBytes
  let (joinChildOuter, joinChildProof, _) :=
    childSystem.prove childJoinIdx joinChildInput default
  let joinChildOuterBytes := MultiStark.serializeClaims #[joinChildOuter]
  let joinChildLayout :=
    joinChildOuter.extract 2 10 == MultiStark.digestGs allowed &&
    joinChildOuter.extract 10 18 == MultiStark.digestGs leftClaimBytes
  let joinChildNativeVerify := childSystem.verify joinChildOuter joinChildProof
  let joinChildIo := io
    |>.extend 0 zeroKey (bytesAsGs joinChildProof.toBytes)
    |>.extend 2 zeroKey (bytesAsGs joinChildOuterBytes)
  let transitiveJoin := compiled.bytecode.execute joinIdx pubInput joinChildIo

  let wrongAllowed := allowed.set! 0
    (UInt8.ofNat ((allowed.data[0]!.toNat + 1) % 256))
  let wrongJoinChildInput := MultiStark.joinPubInput wrongAllowed leftClaimBytes
  let (wrongJoinOuter, wrongJoinProof, _) :=
    childSystem.prove childJoinIdx wrongJoinChildInput default
  let wrongJoinOuterBytes := MultiStark.serializeClaims #[wrongJoinOuter]
  let wrongJoinIo := io
    |>.extend 0 zeroKey (bytesAsGs wrongJoinProof.toBytes)
    |>.extend 2 zeroKey (bytesAsGs wrongJoinOuterBytes)
  let wrongTransitiveAllowed :=
    compiled.bytecode.execute joinIdx pubInput wrongJoinIo

  -- Digest-consistent semantic failures exercise the set checks rather than
  -- merely failing the public output-claim hash binding.
  let omittedAsmBytes := Ix.Claim.ser (.checkEnv outputSubjects.root none)
  let omittedAsmInput := MultiStark.joinPubInput allowed omittedAsmBytes
  let omittedAsmIo := io.extend 2 twoKey (bytesAsGs omittedAsmBytes)
  let omittedAsm := compiled.bytecode.execute joinIdx omittedAsmInput omittedAsmIo

  let extraSubjects := canonicalTree #[a, b, c, e]
  let extraSubjectBytes := Ix.Claim.ser
    (.checkEnv extraSubjects.root (some outputAssumptions.root))
  let extraSubjectInput := MultiStark.joinPubInput allowed extraSubjectBytes
  let extraSubjectIo := seedJoinTree
    (io.extend 2 twoKey (bytesAsGs extraSubjectBytes)) extraSubjects
  let extraSubject :=
    compiled.bytecode.execute joinIdx extraSubjectInput extraSubjectIo

  -- A free-form tree with the expected leaves in descending order has a
  -- self-consistent serialization/root pair, but is not a canonical set tree.
  let sortedOutputLeaves :=
    (#[a, b, c]).qsort fun x y => compare x y == .lt
  let unsortedSubjects : Ix.AssumptionTree :=
    .node (.node (.leaf sortedOutputLeaves[2]!) (.leaf sortedOutputLeaves[1]!))
      (.leaf sortedOutputLeaves[0]!)
  let unsortedBytes := Ix.Claim.ser
    (.checkEnv unsortedSubjects.root (some outputAssumptions.root))
  let unsortedInput := MultiStark.joinPubInput allowed unsortedBytes
  let unsortedIo := seedJoinTree
    (io.extend 2 twoKey (bytesAsGs unsortedBytes)) unsortedSubjects
  let unsorted := compiled.bytecode.execute joinIdx unsortedInput unsortedIo

  let badLeftProofBytes := leftProof.toBytes.set! 0
    (UInt8.ofNat ((leftProof.toBytes.data[0]!.toNat + 1) % 256))
  let badProofIo := io.extend 0 zeroKey (bytesAsGs badLeftProofBytes)
  let badProof := compiled.bytecode.execute joinIdx pubInput badProofIo

  let hostFoldCorrect :=
    outputSubjects.leaves == (canonicalTree #[a, b, c]).leaves &&
    outputStatement.assumptions.map (·.leaves) == some (canonicalTree #[d]).leaves
  let manifestPlan :=
    (Ix.Cli.CheckCmd.AggregationTree.node
      (.node (.leaf 0) (.leaf 1)) (.leaf 2)).foldPlan
  let expectedPlan : Array Ix.Cli.CheckCmd.AggregationTree.FoldOp :=
    #[.leaf 0, .leaf 1, .join 0 1, .leaf 2, .join 2 3]
  let parsedManifestPlan : Bool :=
    let valid := minimalIxes (#[1, 1, 0] ++ u32le4 0 ++ #[0] ++ u32le4 1)
    match Ix.Cli.CheckCmd.parseIxesManifest valid with
    | .ok view => view.aggregationTree.foldPlan ==
      (#[.leaf 0, .leaf 1, .join 0 1] :
        Array Ix.Cli.CheckCmd.AggregationTree.FoldOp)
    | .error _ => false
  let malformedManifestRejected : Bool :=
    let duplicate := minimalIxes (#[1, 1, 0] ++ u32le4 0 ++ #[0] ++ u32le4 0)
    match Ix.Cli.CheckCmd.parseIxesManifest duplicate with
    | .error _ => true
    | .ok _ => false

  lspecIO (.ofList [("aggregate-first", [
    test "host fold constructs canonical union/discharge trees" hostFoldCorrect,
    test "manifest tree lowers to post-order binary slots" (manifestPlan == expectedPlan),
    test "manifest parser exposes its validated bisection tree" parsedManifestPlan,
    test "manifest parser rejects repeated aggregation leaves" malformedManifestRejected,
    test "stand-in lift/join entrypoints survive compiler dedup separately"
      (liftIdx != childJoinIdx),
    expectOk "join accepts canonical union and cross-child discharge" honest,
    test "join child outer claim carries allowed/output digests" joinChildLayout,
    expectOk "stand-in join child proof verifies natively" joinChildNativeVerify,
    expectOk "join accepts a transitively pinned join child" transitiveJoin,
    expectErr "join rejects a join child with a different allowed digest"
      wrongTransitiveAllowed,
    test "codegen'd join matches interpreter (output + query counts)" nativeParity,
    expectErr "native join rejects malformed keyed-blob framing" malformedFraming,
    expectErr "join rejects an omitted undischarged assumption" omittedAsm,
    expectErr "join rejects an extra output subject" extraSubject,
    expectErr "join rejects an unsorted output subject tree" unsorted,
    expectErr "join rejects a tampered child proof" badProof,
  ])]) []

end Tests.MultiStark

end
