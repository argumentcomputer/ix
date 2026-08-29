module

public import LSpec
public import Ix.Aggr
public import Ix.Claim
public import Ix.AssumptionTree
public import Ix.Cli.AggregateCmd
public import Tests.MultiStark

/-!
# Tests for the heterogeneous `ix_aggr` circuit

`ix-aggr` — `smokeSuite`. Executes the production `ix_aggr` entrypoint (the
pure-Lean interpreter over a Lean-built IO buffer) across all ten shapes, with
real Multi-STARK child proofs from two cheap stand-in systems:

* a "fake IxVM" system whose `fake_verify_claim` reproduces `verify_claim`'s
  10-word claim layout, and
* a "fake self" system (same bytecode, different FRI parameters, hence a
  different verifying key) whose `fake_aggr` reproduces `ix_aggr`'s 18-word
  claim layout.

The circuit under test still verifies real proofs and enforces every binding:
per-kind vk digests, entrypoint indices, the transitive allowed digest of self
children, wrap digest pass-through, canonical union/difference folding, and
structural root/path folding. The negative cases each break exactly one of
those bindings.

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
    (trees : Array Ix.AssumptionTree := #[])
    (paths : Array (Address × Option Ix.Merkle.MerklePath) := #[]) :
    IOBuffer := Id.run do
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
  for (candidate, path?) in paths do
    io := Aggr.extendPath io candidate path?
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
  let structuralOutput := leftStatement.joinStructural rightStatement
  let structuralClaimBytes := Ix.Claim.ser structuralOutput.claim
  let structuralTrees := Aggr.CheckEnvTrees.structuralAdviceTrees
    leftStatement rightStatement structuralOutput
  let structuralPathAdvice := Aggr.CheckEnvTrees.structuralPathAdvice
    leftStatement rightStatement structuralOutput

  -- ── M1-d production policy / claim derivation ──────────────────────────
  -- Three leaves make the direct policy exercise both the IxVM+IxVM and
  -- aggregate+IxVM pair shapes. The threshold keeps the lower fold flat and
  -- the root structural.
  let driverOps : Array Ix.Cli.CheckCmd.AggregationTree.FoldOp :=
    #[.leaf 0, .leaf 1, .join 0 1, .leaf 2, .join 2 3]
  let defaultDriverPlan := Ix.Cli.AggregateCmd.schedulePlan
    driverOps #[2, 1, 1] 3
  let directDriverPlan := Ix.Cli.AggregateCmd.schedulePlan
    driverOps #[2, 1, 1] 3 true
  let singletonDirectPlan := Ix.Cli.AggregateCmd.schedulePlan
    #[.leaf 0] #[2] 0 true
  let wrapFirstShapes : Bool := match defaultDriverPlan with
    | .ok plan =>
      plan.map (·.shape?) == #[some 0, some 0, some 5, some 0, some 9] &&
        plan.all (·.kind == .aggr)
    | .error _ => false
  let directShapes : Bool := match directDriverPlan with
    | .ok plan =>
      plan.map (·.shape?) == #[none, none, some 2, none, some 8] &&
        plan.map (·.kind) == #[.ixvm, .ixvm, .aggr, .ixvm, .aggr]
    | .error _ => false
  let singletonStillWraps : Bool := match singletonDirectPlan with
    | .ok #[slot] => slot.kind == .aggr && slot.shape? == some 0
    | _ => false
  let shapeWeightsBounded : Bool := match defaultDriverPlan, directDriverPlan with
    | .ok wraps, .ok direct =>
      Ix.Cli.AggregateCmd.aggregateSlotRamWeights wraps == #[
        Ix.Cli.AggregateCmd.aggregateWrapRamBytes,
        Ix.Cli.AggregateCmd.aggregateWrapRamBytes,
        Ix.Cli.AggregateCmd.aggregateStructuralJoinRamBytes +
          3 * Ix.Cli.AggregateCmd.aggregateFlatJoinRamPerSubjectBytes,
        Ix.Cli.AggregateCmd.aggregateWrapRamBytes,
        Ix.Cli.AggregateCmd.aggregateStructuralJoinRamBytes] &&
      Ix.Cli.AggregateCmd.aggregateSlotRamWeights direct == #[
        Ix.Cli.AggregateCmd.aggregateRawShardRamBytes,
        Ix.Cli.AggregateCmd.aggregateRawShardRamBytes,
        Ix.Cli.AggregateCmd.aggregateDirectJoinRamBytes,
        Ix.Cli.AggregateCmd.aggregateRawShardRamBytes,
        Ix.Cli.AggregateCmd.aggregateMixedJoinRamBytes]
    | _, _ => false
  let driverPrepared : Array Ix.Cli.AggregateCmd.PreparedShard := #[
    { claim := leftStatement.claim
      statement := Ix.Cli.AggregateCmd.fromAggrCheckEnvTrees leftStatement },
    { claim := rightStatement.claim
      statement := Ix.Cli.AggregateCmd.fromAggrCheckEnvTrees rightStatement },
    { claim := rightStatement.claim
      statement := Ix.Cli.AggregateCmd.fromAggrCheckEnvTrees rightStatement }
  ]
  let driverParameters : MultiStark.RecursionParameters := {
    commitment := recCommitParams, fri := innerFri
  }
  let defaultDriverSpecs := defaultDriverPlan.bind fun plan =>
    Ix.Cli.AggregateCmd.buildAggrSlotSpecs plan driverPrepared aggrVk allowed
      fakeVerifyIdx fakeAggrIdx driverParameters
  let directDriverSpecs := directDriverPlan.bind fun plan =>
    Ix.Cli.AggregateCmd.buildAggrSlotSpecs plan driverPrepared aggrVk allowed
      fakeVerifyIdx fakeAggrIdx driverParameters
  let uniformDriverClaims : Bool := match defaultDriverSpecs, directDriverSpecs with
    | .ok wraps, .ok direct => match wraps[0]?, wraps.back?, direct[0]?, direct.back? with
      | some wrappedLeaf, some wrappedRoot, some rawLeaf, some directRoot =>
        wrappedLeaf.outerClaim == Ix.Cli.AggregateCmd.aggregateOuterClaim
          allowed fakeAggrIdx leftStatement.claim &&
        rawLeaf.kind == .ixvm && directRoot.kind == .aggr &&
        wrappedRoot.outerClaim == directRoot.outerClaim &&
        Ix.Cli.AggregateCmd.aggregateCacheVersion == 2 &&
        wrappedLeaf.cacheKey != Ix.Cli.AggregateCmd.aggregateCacheKey
          aggrVk driverParameters wrappedLeaf.outerClaim 1
      | _, _, _, _ => false
    | _, _ => false

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
  let structuralSelf ← match mkSelfChild allowed structuralClaimBytes with
    | .error e => IO.eprintln s!"structural self proof advice encoding failed: {e}"; return 1
    | .ok child => pure child

  let run (shape : Nat) (children : Array ChildSlot) (outBytes : ByteArray)
      (outClaim? : Option ByteArray := none)
      (preimages : Array ByteArray := #[])
      (trees : Array Ix.AssumptionTree := #[])
      (paths : Array (Address × Option Ix.Merkle.MerklePath) := #[]) :=
    aggrCompiled.bytecode.execute ixAggrIdx (Aggr.pubInput allowed outBytes)
      (mkIO allowed shape ixvmVk aggrVk children outClaim? preimages trees paths)
  let pairShape (l r : Aggr.ChildKind) := Aggr.shapeCode (l, some r)
  let runPair (l r : Aggr.ChildKind) (leftChild rightChild : ChildSlot) :=
    run (pairShape l r) #[leftChild, rightChild] outputClaimBytes
      (outClaim? := some outputClaimBytes)
      (preimages := #[leftClaimBytes, rightClaimBytes])
      (trees := adviceTrees)
  let runStructural (l r : Aggr.ChildKind)
      (leftChild rightChild : ChildSlot)
      (paths := structuralPathAdvice) :=
    run (Aggr.structuralShapeCode l r) #[leftChild, rightChild]
      structuralClaimBytes (outClaim? := some structuralClaimBytes)
      (preimages := #[leftClaimBytes, rightClaimBytes])
      (trees := structuralTrees) (paths := paths)

  IO.println "ix-aggr (proving stand-in children + interpreting all shapes)…"
  (← IO.getStdout).flush

  -- ── positive shapes ─────────────────────────────────────────────────────
  let wrapIxvm := run (Aggr.shapeCode (.ixvm, none)) #[leftIxvm] leftClaimBytes
  let wrapSelf := run (Aggr.shapeCode (.aggr, none)) #[leftSelf] leftClaimBytes
  let pairII := runPair .ixvm .ixvm leftIxvm rightIxvm
  let pairIA := runPair .ixvm .aggr leftIxvm rightSelf
  let pairAI := runPair .aggr .ixvm leftSelf rightIxvm
  let pairAA := runPair .aggr .aggr leftSelf rightSelf
  let structuralII := runStructural .ixvm .ixvm leftIxvm rightIxvm
  let structuralIA := runStructural .ixvm .aggr leftIxvm rightSelf
  let structuralAI := runStructural .aggr .ixvm leftSelf rightIxvm
  let structuralAA := runStructural .aggr .aggr leftSelf rightSelf

  -- A structural parent consumes a structural child's free-form subject root
  -- opaquely. This is the monotone composition path used above the scheduler
  -- threshold: once structural, all ancestors remain structural.
  let nestedStructuralOutput := structuralOutput.joinStructural rightStatement
  let nestedStructuralBytes := Ix.Claim.ser nestedStructuralOutput.claim
  let nestedStructural := run (Aggr.structuralShapeCode .aggr .ixvm)
    #[structuralSelf, rightIxvm] nestedStructuralBytes
    (outClaim? := some nestedStructuralBytes)
    (preimages := #[structuralClaimBytes, rightClaimBytes])
    (trees := Aggr.CheckEnvTrees.structuralAdviceTrees
      structuralOutput rightStatement nestedStructuralOutput)
    (paths := Aggr.CheckEnvTrees.structuralPathAdvice
      structuralOutput rightStatement nestedStructuralOutput)

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
    (Aggr.treesBlob adviceTrees) (Aggr.pathsBlob #[])
  let nativeWrap := aggrCompiled.bytecode.executeIxAggr ixAggrIdx
    (Aggr.pubInput allowed leftClaimBytes) (Aggr.shapeCode (.ixvm, none))
    leftIxvm.proofAdviceBytes ByteArray.empty ixvmVk aggrVk
    leftIxvm.claimsBytes ByteArray.empty leftClaimBytes allowed
    (Aggr.preimagesBlob #[]) (Aggr.treesBlob #[]) (Aggr.pathsBlob #[])
  let nativeStructural := aggrCompiled.bytecode.executeIxAggr ixAggrIdx
    (Aggr.pubInput allowed structuralClaimBytes)
    (Aggr.structuralShapeCode .ixvm .ixvm)
    leftIxvm.proofAdviceBytes rightIxvm.proofAdviceBytes ixvmVk aggrVk
    leftIxvm.claimsBytes rightIxvm.claimsBytes structuralClaimBytes allowed
    (Aggr.preimagesBlob #[leftClaimBytes, rightClaimBytes])
    (Aggr.treesBlob structuralTrees) (Aggr.pathsBlob structuralPathAdvice)

  -- Native keyed-blob framing is strict: even an otherwise honest pair must
  -- reject a preimage blob that omits its u32 entry count.
  let malformedNativeFraming := aggrCompiled.bytecode.executeIxAggr ixAggrIdx
    (Aggr.pubInput allowed outputClaimBytes) (pairShape .ixvm .ixvm)
    leftIxvm.proofAdviceBytes rightIxvm.proofAdviceBytes ixvmVk aggrVk
    leftIxvm.claimsBytes rightIxvm.claimsBytes outputClaimBytes allowed
    ⟨#[]⟩ (Aggr.treesBlob adviceTrees) (Aggr.pathsBlob #[])

  let structuralHostCorrect :=
    structuralOutput.subjects.root ==
      Ix.Merkle.nodeHash leftStatement.subjects.root rightStatement.subjects.root &&
    structuralOutput.assumptions.map (·.leaves) == some #[d] &&
    structuralPathAdvice.size == 3

  -- A path that stops at the left child root never reaches the structural
  -- output root.
  let wrongRootPathAdvice := structuralPathAdvice.map fun (candidate, path?) =>
    if candidate == a then
      (candidate, leftStatement.subjects.merkleProof candidate)
    else (candidate, path?)
  let wrongRootPath := runStructural .ixvm .ixvm leftIxvm rightIxvm
    (paths := wrongRootPathAdvice)

  -- Alter one sibling while retaining a syntactically valid path.
  let tamperedPathAdvice := structuralPathAdvice.map fun (candidate, path?) =>
    if candidate == a then
      match path? with
      | some path => match path[0]? with
        | some (_, side) => (candidate, some (path.set! 0 (e, side)))
        | none => (candidate, path?)
      | none => (candidate, path?)
    else (candidate, path?)
  let tamperedPath := runStructural .ixvm .ixvm leftIxvm rightIxvm
    (paths := tamperedPathAdvice)

  -- Every candidate requires an explicit keyed choice; there is no implicit
  -- carry default.
  let droppedPathAdvice := structuralPathAdvice.filter fun (candidate, _) =>
    candidate != d
  let droppedPath := runStructural .ixvm .ixvm leftIxvm rightIxvm
    (paths := droppedPathAdvice)

  -- Candidate d chooses carry, but this output omits it.
  let missingCarriedOutput : Aggr.CheckEnvTrees :=
    { subjects := structuralOutput.subjects, assumptions := none }
  let missingCarriedBytes := Ix.Claim.ser missingCarriedOutput.claim
  let missingCarried := run (Aggr.structuralShapeCode .ixvm .ixvm)
    #[leftIxvm, rightIxvm] missingCarriedBytes
    (outClaim? := some missingCarriedBytes)
    (preimages := #[leftClaimBytes, rightClaimBytes])
    (trees := Aggr.CheckEnvTrees.structuralAdviceTrees
      leftStatement rightStatement missingCarriedOutput)
    (paths := Aggr.CheckEnvTrees.structuralPathAdvice
      leftStatement rightStatement missingCarriedOutput)

  -- The same child statements cannot switch between flat and structural
  -- semantics merely by changing the shape hint: each arm binds a different
  -- output root equation.
  let structuralHintOnFlatOutput := run
    (Aggr.structuralShapeCode .ixvm .ixvm) #[leftIxvm, rightIxvm]
    outputClaimBytes (outClaim? := some outputClaimBytes)
    (preimages := #[leftClaimBytes, rightClaimBytes])
    (trees := structuralTrees) (paths := structuralPathAdvice)
  let flatHintOnStructuralOutput := run (pairShape .ixvm .ixvm)
    #[leftIxvm, rightIxvm] structuralClaimBytes
    (outClaim? := some structuralClaimBytes)
    (preimages := #[leftClaimBytes, rightClaimBytes])
    (trees := Aggr.CheckEnvTrees.adviceTrees
      leftStatement rightStatement structuralOutput)

  -- A flat parent must reopen every subject as a canonical tree. Feeding it
  -- a genuinely structural child therefore rejects, while the structural
  -- parent above accepts the same child root opaquely.
  let flatAfterStructuralOutput := structuralOutput.join rightStatement
  let flatAfterStructuralBytes := Ix.Claim.ser flatAfterStructuralOutput.claim
  let flatFedStructuralChild := run (pairShape .aggr .ixvm)
    #[structuralSelf, rightIxvm] flatAfterStructuralBytes
    (outClaim? := some flatAfterStructuralBytes)
    (preimages := #[structuralClaimBytes, rightClaimBytes])
    (trees := Aggr.CheckEnvTrees.adviceTrees
      structuralOutput rightStatement flatAfterStructuralOutput)

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

  -- A self-consistent free-form tree with descending leaves is not a
  -- canonical set tree, even when its root matches the public output claim.
  let sortedOutputLeaves := (#[a, b, c]).qsort fun x y => compare x y == .lt
  let unsortedSubjects : Ix.AssumptionTree :=
    .node (.node (.leaf sortedOutputLeaves[2]!) (.leaf sortedOutputLeaves[1]!))
      (.leaf sortedOutputLeaves[0]!)
  let unsortedStatement : Aggr.CheckEnvTrees := {
    subjects := unsortedSubjects
    assumptions := outputStatement.assumptions
  }
  let unsortedBytes := Ix.Claim.ser unsortedStatement.claim
  let unsorted := run (pairShape .ixvm .ixvm) #[leftIxvm, rightIxvm]
    unsortedBytes (outClaim? := some unsortedBytes)
    (preimages := #[leftClaimBytes, rightClaimBytes])
    (trees := Aggr.CheckEnvTrees.adviceTrees
      leftStatement rightStatement unsortedStatement)

  -- Identity framing and shape dispatch are closed: shortened blobs and
  -- out-of-range shape bytes cannot select a permissive arm.
  let shortAllowed := allowed.extract 0 72
  let shortIdentity := aggrCompiled.bytecode.execute ixAggrIdx
    (Aggr.pubInput shortAllowed leftClaimBytes)
    (mkIO shortAllowed (Aggr.shapeCode (.ixvm, none)) ixvmVk aggrVk
      #[leftIxvm])
  let invalidShape := run 10 #[leftIxvm] leftClaimBytes

  lspecIO (.ofList [("ix-aggr", [
    test "ixAggr prunes the Ix-agnostic lift entrypoint" liftPruned,
    test "pair fold leaves exactly one outstanding assumption"
      (outputStatement.assumptions.map (·.leaves) == some #[d]),
    test "structural fold is nodeHash(left,right) with one carried assumption"
      structuralHostCorrect,
    test "production wrap-first policy selects shapes 0, 5, and 9"
      wrapFirstShapes,
    test "direct-join policy selects raw leaves plus shapes 2 and 8"
      directShapes,
    test "direct mode still wraps a singleton root" singletonStillWraps,
    test "scheduler RAM weights follow the selected ix_aggr shapes"
      shapeWeightsBounded,
    test "driver specs use uniform aggregate claims and cache version 2"
      uniformDriverClaims,
    expectOk "wrap of an IxVM child accepts" wrapIxvm,
    expectOk "wrap of a self child accepts" wrapSelf,
    expectOk "pair (IxVM, IxVM) accepts" pairII,
    expectOk "pair (IxVM, self) accepts" pairIA,
    expectOk "pair (self, IxVM) accepts" pairAI,
    expectOk "pair (self, self) accepts" pairAA,
    expectOk "structural pair (IxVM, IxVM) accepts" structuralII,
    expectOk "structural pair (IxVM, self) accepts" structuralIA,
    expectOk "structural pair (self, IxVM) accepts" structuralAI,
    expectOk "structural pair (self, self) accepts" structuralAA,
    expectOk "structural parent accepts a structural self child"
      nestedStructural,
    test "codegen'd pair matches interpreter (output + query counts)"
      (sameCounts nativePair pairII),
    test "codegen'd wrap matches interpreter (output + query counts)"
      (sameCounts nativeWrap wrapIxvm),
    test "codegen'd structural pair matches interpreter (output + query counts)"
      (sameCounts nativeStructural structuralII),
    expectErr "shape hint lying about the child system is rejected" shapeLie,
    expectErr "tampered proof advice is rejected" tampered,
    expectErr "self child under a foreign identity is rejected" foreignIdentity,
    expectErr "wrap output differing from the child statement is rejected"
      wrapMismatch,
    expectErr "pair output dropping an assumption is rejected" droppedAssumption,
    expectErr "pair output with an extra subject is rejected" extraSubject,
    expectErr "tree advice not reproducing its keyed root is rejected"
      mismatchedTree,
    expectErr "flat pair rejects a self-consistent unsorted subject tree"
      unsorted,
    expectErr "native pair rejects malformed keyed-blob framing"
      malformedNativeFraming,
    expectErr "ix_aggr rejects a shortened identity blob" shortIdentity,
    expectErr "ix_aggr rejects an out-of-range shape hint" invalidShape,
    expectErr "structural pair rejects a path to the wrong root" wrongRootPath,
    expectErr "structural pair rejects a tampered path sibling" tamperedPath,
    expectErr "structural pair rejects a missing path choice" droppedPath,
    expectErr "structural pair rejects an omitted carried assumption"
      missingCarried,
    expectErr "structural shape hint rejects a flat output root"
      structuralHintOnFlatOutput,
    expectErr "flat shape hint rejects a structural output root"
      flatHintOnStructuralOutput,
    expectErr "flat pair rejects a genuinely structural child subject root"
      flatFedStructuralChild,
  ])]) []

end Tests.Aggr

end
