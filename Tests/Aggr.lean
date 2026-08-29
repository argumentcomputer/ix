module

public import LSpec
public import Ix.Aggr
public import Ix.Claim
public import Ix.AssumptionTree
public import Tests.MultiStark

/-!
# Tests for the heterogeneous `ix_aggr` circuit

`ix-aggr` — `smokeSuite`. Executes the production `ix_aggr` entrypoint (the
pure-Lean interpreter over a Lean-built IO buffer) across all five shapes, with
real Multi-STARK child proofs from two cheap stand-in systems:

* a "fake IxVM" system whose `fake_verify_claim` reproduces `verify_claim`'s
  10-word claim layout, and
* a "fake self" system (same bytecode, different FRI parameters, hence a
  different verifying key) whose `fake_aggr` reproduces `ix_aggr`'s 18-word
  claim layout.

The circuit under test still verifies real proofs and enforces every binding:
per-kind vk digests, entrypoint indices, the transitive allowed digest of self
children, wrap digest pass-through, and the canonical union/difference fold.
The negative cases each break exactly one of those bindings.

Proving the real `ix_aggr` system recursively (self children that are actual
`ix_aggr` proofs) needs the native prover and tens of GiB; that path belongs to
the CLI/benchmark layer, not this suite.
-/

public section

open LSpec Aiur

namespace Tests.Aggr

open Tests.MultiStark (expectOk expectErr recCommitParams innerFri)

/-- Cheap stand-in children. `fake_verify_claim` mirrors the IxVM
`verify_claim` claim shape (10 words), `fake_aggr` mirrors the `ix_aggr` claim
shape (18 words). Bodies touch memory so the proofs have a non-trivial trace. -/
def childProgram : Source.Toplevel := ⟦
  pub fn fake_verify_claim(digest: [G; 8]) {
    assert_eq!(load(store(digest[0])), digest[0]);
    ()
  }
  pub fn fake_aggr(allowed_digest: [G; 8], _out_claim_digest: [G; 8]) {
    assert_eq!(load(store(allowed_digest[0])), allowed_digest[0]);
    ()
  }
⟧

private def canonicalTree (leaves : Array Address) : Ix.AssumptionTree :=
  (Ix.AssumptionTree.canonical leaves).get!

/-- One child slot: expanded proof advice on channel 0, serialized claims on
channel 2. Compact proof wire bytes are never an in-circuit input. -/
private structure ChildSlot where
  proofAdviceBytes : ByteArray
  claimsBytes : ByteArray

/-- Assemble the full advice buffer the way the native FFI will: identity blob
and shape byte, per-kind vks, child slots in key order, then the optional
output claim, `CheckEnv` preimages, and canonical trees. -/
private def mkIO (allowed : ByteArray) (shape : Nat)
    (ixvmVk aggrVk : ByteArray) (children : Array ChildSlot)
    (outClaim? : Option ByteArray := none)
    (preimages : Array ByteArray := #[])
    (trees : Array Ix.AssumptionTree := #[]) : IOBuffer := Id.run do
  let mut io := Aggr.extendIdentity default allowed shape
  io := Aggr.extendVk io .ixvm ixvmVk
  io := Aggr.extendVk io .aggr aggrVk
  for (child, key) in children.mapIdx (fun key child => (child, key)) do
    io := Aggr.extendChild io key child.proofAdviceBytes child.claimsBytes
  if let some bytes := outClaim? then
    io := Aggr.extendOutputClaim io bytes
  for bytes in preimages do
    io := Aggr.extendPreimage io bytes
  for tree in trees do
    io := Aggr.extendTree io tree
  return io

def smokeSuite : IO UInt32 := do
  let childCompiled ← match childProgram.compile with
    | .error e => IO.eprintln s!"aggr child compilation failed: {e}"; return 1
    | .ok c => pure c
  let fakeVerifyIdx := childCompiled.getFuncIdx `fake_verify_claim |>.get!
  let fakeAggrIdx := childCompiled.getFuncIdx `fake_aggr |>.get!
  -- Two DIFFERENT verifying keys from one bytecode: the "self" system tunes
  -- the query count, so a child proof only verifies under its own kind's vk
  -- and the per-kind digest binding is meaningfully exercised.
  let ixvmSystem := AiurSystem.build childCompiled.bytecode recCommitParams innerFri
  let aggrSystem := AiurSystem.build childCompiled.bytecode recCommitParams
    { innerFri with numQueries := 4 }
  let ixvmVk := ixvmSystem.vkBytes
  let aggrVk := aggrSystem.vkBytes
  let allowed := Aggr.allowedBlob ixvmVk fakeVerifyIdx aggrVk fakeAggrIdx

  -- ── the production system under test ────────────────────────────────────
  let aggrTop ← match Aggr.ixAggr with
    | .error e => IO.eprintln s!"ixAggr toplevel merge failed: {e}"; return 1
    | .ok t => pure t
  let aggrCompiled ← match aggrTop.compile with
    | .error e => IO.eprintln s!"ixAggr compilation failed: {e}"; return 1
    | .ok c => pure c
  let some ixAggrIdx := aggrCompiled.getFuncIdx `ix_aggr
    | IO.eprintln "ix_aggr entrypoint not found"; return 1
  -- The Ix-agnostic lift entrypoint must NOT survive the ixAggr prune.
  let liftPruned := aggrCompiled.getFuncIdx `verify_multi_stark_proof |>.isNone

  -- ── two shard statements whose assumptions cross the subject boundary ───
  --   subjects    = {a,b} ∪ {c}             = {a,b,c}
  --   assumptions = ({c,d} ∪ {a}) ∖ {a,b,c} = {d}
  let a := Address.blake3 "aggr-a".toUTF8
  let b := Address.blake3 "aggr-b".toUTF8
  let c := Address.blake3 "aggr-c".toUTF8
  let d := Address.blake3 "aggr-d".toUTF8
  let e := Address.blake3 "aggr-extra".toUTF8
  let leftStatement : Aggr.CheckEnvTrees :=
    { subjects := canonicalTree #[a, b]
      assumptions := some (canonicalTree #[c, d]) }
  let rightStatement : Aggr.CheckEnvTrees :=
    { subjects := canonicalTree #[c]
      assumptions := some (canonicalTree #[a]) }
  let outputStatement := leftStatement.join rightStatement
  let adviceTrees := Aggr.CheckEnvTrees.adviceTrees
    leftStatement rightStatement outputStatement
  let leftClaimBytes := Ix.Claim.ser leftStatement.claim
  let rightClaimBytes := Ix.Claim.ser rightStatement.claim
  let outputClaimBytes := Ix.Claim.ser outputStatement.claim

  -- ── child proofs ────────────────────────────────────────────────────────
  -- Kind 0 ("IxVM"): claim = [0, fake_verify_claim, digest(CheckEnv bytes)].
  let mkIxvmChild (claimBytes : ByteArray) : Except String ChildSlot := do
    let (claim, proof, _) :=
      ixvmSystem.prove fakeVerifyIdx (Aggr.digestGs claimBytes) default
    let proofAdviceBytes ← ixvmSystem.proofToAdviceBytes claim proof
    pure ⟨proofAdviceBytes, MultiStark.serializeClaims #[claim]⟩
  -- Kind 1 ("self"): claim = [0, fake_aggr, digest(allowed), digest(CheckEnv)].
  let mkSelfChild (blob claimBytes : ByteArray) : Except String ChildSlot := do
    let (claim, proof, _) :=
      aggrSystem.prove fakeAggrIdx (Aggr.pubInput blob claimBytes) default
    let proofAdviceBytes ← aggrSystem.proofToAdviceBytes claim proof
    pure ⟨proofAdviceBytes, MultiStark.serializeClaims #[claim]⟩
  let leftIxvm ← match mkIxvmChild leftClaimBytes with
    | .error e => IO.eprintln s!"left IxVM proof advice encoding failed: {e}"; return 1
    | .ok child => pure child
  let rightIxvm ← match mkIxvmChild rightClaimBytes with
    | .error e => IO.eprintln s!"right IxVM proof advice encoding failed: {e}"; return 1
    | .ok child => pure child
  let leftSelf ← match mkSelfChild allowed leftClaimBytes with
    | .error e => IO.eprintln s!"left self proof advice encoding failed: {e}"; return 1
    | .ok child => pure child
  let rightSelf ← match mkSelfChild allowed rightClaimBytes with
    | .error e => IO.eprintln s!"right self proof advice encoding failed: {e}"; return 1
    | .ok child => pure child

  let run (shape : Nat) (children : Array ChildSlot) (outBytes : ByteArray)
      (outClaim? : Option ByteArray := none)
      (preimages : Array ByteArray := #[])
      (trees : Array Ix.AssumptionTree := #[]) :=
    aggrCompiled.bytecode.execute ixAggrIdx (Aggr.pubInput allowed outBytes)
      (mkIO allowed shape ixvmVk aggrVk children outClaim? preimages trees)
  let pairShape (l r : Aggr.ChildKind) := Aggr.shapeCode (l, some r)
  let runPair (l r : Aggr.ChildKind) (leftChild rightChild : ChildSlot) :=
    run (pairShape l r) #[leftChild, rightChild] outputClaimBytes
      (outClaim? := some outputClaimBytes)
      (preimages := #[leftClaimBytes, rightClaimBytes])
      (trees := adviceTrees)

  IO.println "ix-aggr (proving stand-in children + interpreting all shapes)…"
  (← IO.getStdout).flush

  -- ── positive shapes ─────────────────────────────────────────────────────
  let wrapIxvm := run (Aggr.shapeCode (.ixvm, none)) #[leftIxvm] leftClaimBytes
  let wrapSelf := run (Aggr.shapeCode (.aggr, none)) #[leftSelf] leftClaimBytes
  let pairII := runPair .ixvm .ixvm leftIxvm rightIxvm
  let pairIA := runPair .ixvm .aggr leftIxvm rightSelf
  let pairAI := runPair .aggr .ixvm leftSelf rightIxvm
  let pairAA := runPair .aggr .aggr leftSelf rightSelf

  -- ── codegen/native parity ───────────────────────────────────────────────
  -- The generated Rust aggregator (`crates/ixvm-codegen/src/aiur_ix_aggr.rs`)
  -- plus the native advice builder must reproduce the interpreter's output
  -- and per-circuit query counts exactly — the standing parity invariant.
  let sameCounts (native : Except String (Array Aiur.G × Array QueryCount))
      (interp : Except String (Array Aiur.G × IOBuffer × Array QueryCount)) :
      Bool :=
    match native, interp with
    | .ok (out, qc), .ok (outI, _, qcI) =>
      out == outI && qc.size == qcI.size &&
        (qc.zip qcI).all fun (a, b) =>
          a.uniqueRows == b.uniqueRows && a.totalHits == b.totalHits
    | _, _ => false
  let nativePair := aggrCompiled.bytecode.executeIxAggr ixAggrIdx
    (Aggr.pubInput allowed outputClaimBytes) (pairShape .ixvm .ixvm)
    leftIxvm.proofAdviceBytes rightIxvm.proofAdviceBytes ixvmVk aggrVk
    leftIxvm.claimsBytes rightIxvm.claimsBytes outputClaimBytes allowed
    (Aggr.preimagesBlob #[leftClaimBytes, rightClaimBytes])
    (Aggr.treesBlob adviceTrees)
  let nativeWrap := aggrCompiled.bytecode.executeIxAggr ixAggrIdx
    (Aggr.pubInput allowed leftClaimBytes) (Aggr.shapeCode (.ixvm, none))
    leftIxvm.proofAdviceBytes ByteArray.empty ixvmVk aggrVk
    leftIxvm.claimsBytes ByteArray.empty leftClaimBytes allowed
    (Aggr.preimagesBlob #[]) (Aggr.treesBlob #[])

  -- ── negative cases — one broken binding each ────────────────────────────
  -- Shape hint lies about the child's system: a self proof cannot verify
  -- against the IxVM vk the hinted kind binds.
  let shapeLie := run (Aggr.shapeCode (.ixvm, none)) #[leftSelf] leftClaimBytes
  -- Tampered proof advice.
  let tamperedBytes := leftIxvm.proofAdviceBytes.set! 0
    (UInt8.ofNat ((leftIxvm.proofAdviceBytes.data[0]!.toNat + 1) % 256))
  let tampered := run (Aggr.shapeCode (.ixvm, none))
    #[{ leftIxvm with proofAdviceBytes := tamperedBytes }] leftClaimBytes
  -- A self child minted under a FOREIGN aggregation identity (different
  -- entrypoint index) must not be joinable under this one.
  let foreignAllowed := Aggr.allowedBlob ixvmVk fakeVerifyIdx aggrVk
    (fakeAggrIdx + 1)
  let foreignSelf ← match mkSelfChild foreignAllowed leftClaimBytes with
    | .error e => IO.eprintln s!"foreign self proof advice encoding failed: {e}"; return 1
    | .ok child => pure child
  let foreignIdentity := run (Aggr.shapeCode (.aggr, none)) #[foreignSelf]
    leftClaimBytes
  -- Wrap must pass the child statement through unchanged.
  let wrapMismatch := run (Aggr.shapeCode (.ixvm, none)) #[leftIxvm]
    rightClaimBytes
  -- A pair fold that drops the outstanding assumption {d}.
  let droppedStatement : Aggr.CheckEnvTrees :=
    { outputStatement with assumptions := none }
  let droppedBytes := Ix.Claim.ser droppedStatement.claim
  let droppedAssumption := run (pairShape .ixvm .ixvm) #[leftIxvm, rightIxvm]
    droppedBytes (outClaim? := some droppedBytes)
    (preimages := #[leftClaimBytes, rightClaimBytes])
    (trees := Aggr.CheckEnvTrees.adviceTrees
      leftStatement rightStatement droppedStatement)
  -- A pair fold whose output subjects contain an extra address {e}.
  let paddedStatement : Aggr.CheckEnvTrees :=
    { subjects := canonicalTree #[a, b, c, e]
      assumptions := outputStatement.assumptions }
  let paddedBytes := Ix.Claim.ser paddedStatement.claim
  let extraSubject := run (pairShape .ixvm .ixvm) #[leftIxvm, rightIxvm]
    paddedBytes (outClaim? := some paddedBytes)
    (preimages := #[leftClaimBytes, rightClaimBytes])
    (trees := Aggr.CheckEnvTrees.adviceTrees
      leftStatement rightStatement paddedStatement)
  -- Tree advice whose leaves do not reproduce the keyed root: seed the
  -- output-subject slot with the padded tree's serialization under the honest
  -- root's key. The circuit recomputes the canonical root from the leaves.
  let mismatchedIO := Id.run do
    let mut io := mkIO allowed (pairShape .ixvm .ixvm) ixvmVk aggrVk
      #[leftIxvm, rightIxvm] (outClaim? := some outputClaimBytes)
      (preimages := #[leftClaimBytes, rightClaimBytes])
      (trees := #[leftStatement.subjects, leftStatement.assumptions.get!,
        rightStatement.subjects, rightStatement.assumptions.get!,
        outputStatement.assumptions.get!])
    io := io.extend 5 (Aggr.byteGs outputStatement.subjects.root.hash)
      (Aggr.byteGs (Ix.AssumptionTree.ser paddedStatement.subjects))
    return io
  let mismatchedTree := aggrCompiled.bytecode.execute ixAggrIdx
    (Aggr.pubInput allowed outputClaimBytes) mismatchedIO

  lspecIO (.ofList [("ix-aggr", [
    test "ixAggr prunes the Ix-agnostic lift entrypoint" liftPruned,
    test "pair fold leaves exactly one outstanding assumption"
      (outputStatement.assumptions.map (·.leaves) == some #[d]),
    expectOk "wrap of an IxVM child accepts" wrapIxvm,
    expectOk "wrap of a self child accepts" wrapSelf,
    expectOk "pair (IxVM, IxVM) accepts" pairII,
    expectOk "pair (IxVM, self) accepts" pairIA,
    expectOk "pair (self, IxVM) accepts" pairAI,
    expectOk "pair (self, self) accepts" pairAA,
    test "codegen'd pair matches interpreter (output + query counts)"
      (sameCounts nativePair pairII),
    test "codegen'd wrap matches interpreter (output + query counts)"
      (sameCounts nativeWrap wrapIxvm),
    expectErr "shape hint lying about the child system is rejected" shapeLie,
    expectErr "tampered proof advice is rejected" tampered,
    expectErr "self child under a foreign identity is rejected" foreignIdentity,
    expectErr "wrap output differing from the child statement is rejected"
      wrapMismatch,
    expectErr "pair output dropping an assumption is rejected" droppedAssumption,
    expectErr "pair output with an extra subject is rejected" extraSubject,
    expectErr "tree advice not reproducing its keyed root is rejected"
      mismatchedTree,
  ])]) []

end Tests.Aggr

end
