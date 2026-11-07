import Ix.Cli.FormalAggregate
import Ix.Aggr.CatalogPlan

/-! Execute every aggregation shape, 0 to 16 (wraps, flat and structural pairs,
range sums, binding discharge, cross-binding joins and catalog joins), and the
invalid shape 17, against small real STARK children, with negative cases for
each binding the shapes check. The stand-in keys deliberately accept arbitrary
digests; only the production aggregator's bindings and fold relation are under
test. -/
open Lean Aggr Ix.Cli Ix.Cli.FormalAggregate

private def fixture (dir : System.FilePath) (args : Array Aiur.G) : IO Unit := do
  IO.FS.withTempFile fun h path => do
    h.putStr (toJson (args.map (·.n))).compress
    h.flush
    FormalAiur.command "target/release/examples/claim_fixture" #[path.toString, dir.toString]

private def node (ctx : Context) (dir : System.FilePath) (kind : ChildKind)
    (statement : CheckEnvTrees) : IO Node := do
  let input := (outerClaim ctx kind statement.claim).extract 2 18
  fixture dir input
  let magic := (if kind == .ixvm then "IXAIUR2\x00" else "IXAGGR2\x00").toUTF8
  let proof ← IO.FS.readBinFile (dir / "proof.bin")
  return { kind, statement, wrapper := { claim := statement.claim, proof := magic ++ proof } }

/-- The failure a rejected case is rejected by, where it is pinned: the
aggregator's assertion message, or the function that refuses. -/
private def rejectionReasons : List (String × String) := [
  ("pair refuses a claim preimage byte out of range", "StarkIO::read_byte_stream"),
  ("pair refuses a verifying-key byte out of range", "StarkIO::read_byte_stream"),
  ("shape 13 rejects a child that validates its binding",
    "aggr discharge: the claim does not assume its binding"),
  ("shape 13 rejects a binding claim for another binding",
    "aggr discharge: the binding claim is for another binding"),
  ("shape 13 rejects an output that still assumes the binding",
    "aggr: claims differ in whether they assume their binding"),
  ("shape 13 rejects an output for other subjects",
    "aggr discharge: output subject root differs from the child's"),
  ("shape 15 rejects a member of another literal class",
    "aggr cross-binding: the bindings' literal classes differ"),
  ("shape 15 rejects a member with an incomplete binding",
    "aggr cross-binding: the binding does not bind every role"),
  ("shape 15 rejects a member that assumes its binding",
    "aggr cross-binding: the claim assumes its binding"),
  ("shape 15 rejects an output under another class", "aggr: claims differ in binding hash"),
  ("shape 15 rejects an output that drops the literal class validator",
    "aggr: claims differ in whether they assume their binding"),
  ("flat pair rejects claims under two bindings", "aggr: claims differ in binding hash"),
  ("shape 16 rejects an output missing a member", "aggr: subject union mismatch"),
  ("shape 16 rejects a conditional member claim", "aggr catalog: a member claim has assumptions"),
  ("shape 16 rejects a member that assumes its binding",
    "aggr catalog: a member claim assumes its binding"),
  ("shape 16 rejects a binding claim as a member", "aggr: claim is not Catalog"),
  ("shape 16 rejects a catalog child without its members tree",
    "Aggregation::aggr_load_canonical_tree")]

private def test (ctx : Context) (label : String) (bytes : ByteArray) (io : Aiur.IOBuffer)
    (accept : Bool := true) : Json :=
  let reason := if accept then none else rejectionReasons.lookup label
  Json.mkObj ([("label", toJson label), ("accept", toJson accept),
    ("invocation", FormalAiur.invocation (pubInput ctx.allowed bytes) io "MultiStark::ix_aggr")]
    ++ reason.toList.map fun r => ("rejects_with", toJson r))

/-- `bytes` as elements, with the first four-byte word whose second byte is
nonzero shifted out of byte range: its first element raised by 256 and its
second lowered by one, which keeps the word's packed value. -/
private def shiftedGs (bytes : ByteArray) : Array Aiur.G := Id.run do
  let gs := byteGs bytes
  for i in (List.range (bytes.size / 4)).map (4 * ·) do
    if bytes[i + 1]! > 0 then
      return (gs.set! i (.ofNat (bytes[i]!.toNat + 256))).set! (i + 1)
        (.ofNat (bytes[i + 1]!.toNat - 1))
  return gs

/-- A child proving `claim`, which need not be a `CheckEnv` claim (a binding or
a catalog claim). Advice reads only a node's kind and wrapper, so `statement`
is a placeholder. -/
private def claimNode (ctx : Context) (dir : System.FilePath) (kind : ChildKind)
    (claim : Ix.Claim) (statement : CheckEnvTrees) : IO Node := do
  fixture dir ((outerClaim ctx kind claim).extract 2 18)
  let magic := (if kind == .ixvm then "IXAIUR2\x00" else "IXAGGR2\x00").toUTF8
  let proof ← IO.FS.readBinFile (dir / "proof.bin")
  return { kind, statement, wrapper := { claim, proof := magic ++ proof } }

/-- A two-child witness for `shape`: the children, the output claim, the
channel-4 preimages and the channel-5 trees. -/
private def pairAdvice (ctx : Context) (shape : Nat) (l r : Node) (output : Ix.Claim)
    (preimages : Array ByteArray) (trees : Array Ix.AssumptionTree := #[]) :
    IO Aiur.IOBuffer := do
  let io ← childAdvice ctx (extendIdentity default ctx.allowed shape) 0 l
  let io ← childAdvice ctx io 1 r
  let io := extendOutputClaim io (Ix.Claim.ser output)
  let io := preimages.foldl extendPreimage io
  return trees.foldl extendTree io

/-- A complete role table binding every role to a placeholder address, with
the roles of `rebind` bound elsewhere (`tag`). Rebinding `Nat.land` keeps the
literal class; rebinding `Char.ofNat`, a class role, changes it. -/
private def tableOf (rebind : List Ix.Kernel.Role) (tag : String) (drop : Bool := false) :
    ByteArray :=
  let bound := Ix.Kernel.Role.all.toArray.map fun r =>
    (r, Address.blake3 (if rebind.contains r then s!"{tag} {r.leanName}"
      else s!"bound {r.leanName}").toUTF8)
  Ix.Kernel.RoleTable.toBytes { version := Ix.Kernel.specVersion, evidence := #[]
                                bound := if drop then bound.pop else bound }

/-- Shapes 13 to 16: binding discharge, cross-binding joins and catalog joins,
each with the negative cases of the bindings it checks. -/
private def bindingShapeCases (ctx : Context) (dir : System.FilePath)
    (claimCtx : Ix.ClaimContext) (left right : CheckEnvTrees) (li : Node) :
    IO (Array Json) := do
  let mut tests : Array Json := #[]
  -- ── binding discharge (shapes 13–14) ──
  -- Children that assume their binding (validator 4), and one proof of the
  -- binding claim for their context: the same binding proof discharges two
  -- claim sets, each to its claim validating the binding (validator 3).
  let assumedCtx := { claimCtx with bindingAssumed := true }
  let assumedLeft : CheckEnvTrees := { left with ctx := assumedCtx }
  let assumedRight : CheckEnvTrees := { right with ctx := assumedCtx }
  let binding := (← claimNode ctx (dir / "binding") .ixvm
    (.binding claimCtx.spec claimCtx.binding) left).wrapper
  let otherBinding := (← claimNode ctx (dir / "other-binding") .ixvm
    (.binding claimCtx.spec (Address.blake3 "another binding".toUTF8)) left).wrapper
  let ali ← node ctx (dir / "ali") .ixvm assumedLeft
  let ari ← node ctx (dir / "ari") .ixvm assumedRight
  let ala ← node ctx (dir / "ala") .aggr assumedLeft
  let discharges : Array (String × Node × Ixon.Proof × CheckEnvTrees × Bool) := #[
    ("shape 13 discharges an IxVM child's binding", ali, binding, left, true),
    ("shape 13 discharges another claim set with the same binding proof", ari, binding, right, true),
    ("shape 14 discharges an ix_aggr child's binding", ala, binding, left, true),
    ("shape 13 rejects a child that validates its binding", li, binding, left, false),
    ("shape 13 rejects a binding claim for another binding", ali, otherBinding, left, false),
    ("shape 13 rejects an output that still assumes the binding", ali, binding, assumedLeft, false),
    ("shape 13 rejects an output for other subjects", ali, binding, right, false)]
  for (label, child, proof, output, accept) in discharges do
    tests := tests.push (test ctx label (Ix.Claim.ser output.claim)
      (← dischargeAdvice ctx child proof output) accept)
  -- ── claims under different role bindings (shapes 15–16) ──
  -- `tableA` and `tableB` bind every role and differ only in `Nat.land`, so
  -- they have one literal class; `tableC` also rebinds `Char.ofNat`, a class
  -- role, so its class differs; `incomplete` leaves a role unbound.
  let tableA := tableOf [] "a"
  let tableB := tableOf [.natLand] "b"
  let tableC := tableOf [.natLand, .charOfNat] "c"
  let incomplete := tableOf [] "a" (drop := true)
  let klass ← IO.ofExcept (Ix.ClaimContext.literalClassOfBytes tableA)
  let classC ← IO.ofExcept (Ix.ClaimContext.literalClassOfBytes tableC)
  unless klass == (← IO.ofExcept (Ix.ClaimContext.literalClassOfBytes tableB)) && klass != classC do
    throw (IO.userError "the fixture tables' literal classes are not as intended")
  let under (table : ByteArray) (statement : CheckEnvTrees) : CheckEnvTrees :=
    { statement with ctx := { claimCtx with binding := Address.blake3 table }, assumptions := none }
  let memberA := under tableA left
  let memberB := under tableB right
  let memberC := under tableC right
  let memberIncomplete := under incomplete right
  let assumedA := { memberA with ctx := { memberA.ctx with bindingAssumed := true } }
  let conditionalA := { memberA with assumptions := left.assumptions }
  let ser (s : CheckEnvTrees) := Ix.Claim.ser s.claim
  let childA ← node ctx (dir / "member-a") .aggr memberA
  let childB ← node ctx (dir / "member-b") .aggr memberB
  let childC ← node ctx (dir / "member-c") .aggr memberC
  let childIncomplete ← node ctx (dir / "member-incomplete") .aggr memberIncomplete
  let childAssumedA ← node ctx (dir / "member-assumed") .aggr assumedA
  let childConditional ← node ctx (dir / "member-conditional") .aggr conditionalA
  let crossAB := memberA.joinCrossBinding klass memberB
  let childCross ← node ctx (dir / "cross") .aggr crossAB
  let crossCases : Array (String × Node × Node × Array ByteArray × Ix.Claim × Bool) := #[
    ("shape 15 joins two claims of one literal class", childA, childB,
      #[ser memberA, ser memberB, tableA, tableB], crossAB.claim, true),
    ("shape 15 joins a member to a claim already under its class", childA, childCross,
      #[ser memberA, ser crossAB, tableA], (memberA.joinCrossBinding klass crossAB).claim, true),
    ("shape 15 rejects a member of another literal class", childA, childC,
      #[ser memberA, ser memberC, tableA, tableC], (memberA.joinCrossBinding klass memberC).claim,
      false),
    ("shape 15 rejects a member with an incomplete binding", childA, childIncomplete,
      #[ser memberA, ser memberIncomplete, tableA, incomplete],
      (memberA.joinCrossBinding klass memberIncomplete).claim, false),
    ("shape 15 rejects a member that assumes its binding", childAssumedA, childB,
      #[ser assumedA, ser memberB, tableA, tableB], crossAB.claim, false),
    ("shape 15 rejects an output under another class", childA, childB,
      #[ser memberA, ser memberB, tableA, tableB],
      { crossAB with ctx := { crossAB.ctx with binding := classC } }.claim, false),
    ("shape 15 rejects an output that drops the literal class validator", childA, childB,
      #[ser memberA, ser memberB, tableA, tableB],
      { crossAB with ctx := { crossAB.ctx with literalClass := false } }.claim, false)]
  for (label, l, r, preimages, output, accept) in crossCases do
    tests := tests.push (test ctx label (Ix.Claim.ser output)
      (← pairAdvice ctx crossBindingShapeCode l r output preimages) accept)
  -- A fold that requires one context still refuses the two bindings.
  let joined := memberA.join memberB
  tests := tests.push (test ctx "flat pair rejects claims under two bindings" (ser joined)
    (← pairAdvice ctx (shapeCode (.aggr, some .aggr)) childA childB joined.claim
      #[ser memberA, ser memberB] (memberA.adviceTrees memberB joined)) false)
  -- Catalog joins: two member claims, a member with an incomplete binding,
  -- then a catalog and a class claim.
  let catalogAC := CatalogTrees.join (.inl memberA.claim) (.inl memberC.claim)
  let catalogPartial := CatalogTrees.join (.inl memberA.claim) (.inl memberIncomplete.claim)
  let catalogACB := CatalogTrees.join (.inr catalogAC) (.inl crossAB.claim)
  let childCatalog ← claimNode ctx (dir / "catalog") .aggr catalogAC.claim memberA
  let bindingMember : Ix.Claim := .binding claimCtx.spec (Address.blake3 tableA)
  let childBindingMember ← claimNode ctx (dir / "binding-member") .aggr bindingMember memberA
  let catalogOf (claims : Array Ix.Claim) : Ix.AssumptionTree :=
    (Ix.AssumptionTree.canonical (claims.map Ix.Claim.commit)).get!
  let catalogCases :
      Array (String × Node × Node × Array ByteArray × Array Ix.AssumptionTree × Ix.Claim × Bool) := #[
    ("shape 16 joins two member claims into a catalog", childA, childC,
      #[ser memberA, ser memberC], #[catalogAC.members], catalogAC.claim, true),
    ("shape 16 keeps a member with an incomplete binding", childA, childIncomplete,
      #[ser memberA, ser memberIncomplete], #[catalogPartial.members], catalogPartial.claim, true),
    ("shape 16 joins a catalog and a class claim", childCatalog, childCross,
      #[Ix.Claim.ser catalogAC.claim, ser crossAB], #[catalogAC.members, catalogACB.members],
      catalogACB.claim, true),
    ("shape 16 rejects an output missing a member", childA, childC,
      #[ser memberA, ser memberC], #[catalogOf #[memberA.claim]],
      .catalog (catalogOf #[memberA.claim]).root, false),
    ("shape 16 rejects a conditional member claim", childConditional, childC,
      #[ser conditionalA, ser memberC], #[catalogOf #[conditionalA.claim, memberC.claim]],
      .catalog (catalogOf #[conditionalA.claim, memberC.claim]).root, false),
    ("shape 16 rejects a member that assumes its binding", childAssumedA, childC,
      #[ser assumedA, ser memberC], #[catalogOf #[assumedA.claim, memberC.claim]],
      .catalog (catalogOf #[assumedA.claim, memberC.claim]).root, false),
    ("shape 16 rejects a binding claim as a member", childBindingMember, childC,
      #[Ix.Claim.ser bindingMember, ser memberC], #[catalogOf #[bindingMember, memberC.claim]],
      .catalog (catalogOf #[bindingMember, memberC.claim]).root, false),
    ("shape 16 rejects a catalog child without its members tree", childCatalog, childCross,
      #[Ix.Claim.ser catalogAC.claim, ser crossAB], #[catalogACB.members], catalogACB.claim, false)]
  for (label, l, r, preimages, trees, output, accept) in catalogCases do
    tests := tests.push (test ctx label (Ix.Claim.ser output)
      (← pairAdvice ctx catalogShapeCode l r output preimages trees) accept)
  -- Catalog plans keep a member with an incomplete binding out of the class
  -- folds, and join it only through a catalog join.
  let member (label : String) (claim : Ix.Claim) (table : ByteArray) (klass : Option Address) :
      CatalogMember :=
    { label, toolchain := "fixture", claim, bindingSection := table, literalClass := klass }
  let partialMember := member "partial" memberIncomplete.claim incomplete none
  let mixed ← IO.ofExcept (catalogPlan #[member "left" memberA.claim tableA (some klass),
    partialMember, member "right" memberB.claim tableB (some klass)])
  let anotherPartial := (under incomplete left).claim
  let partials ← IO.ofExcept (catalogPlan #[partialMember,
    { partialMember with label := "another partial", claim := anotherPartial }])
  unless mixed.nodes.size == 5 &&
      mixed.nodes.any (fun | .crossBinding k 0 2 => k == klass | _ => false) &&
      partials.nodes.size == 3 &&
      (match partials.nodes[partials.root]! with | .catalogJoin 0 1 => true | _ => false) &&
      partials.statements[partials.root]!.claim ==
        (CatalogTrees.join (.inl partialMember.claim) (.inl anotherPartial)).claim do
    throw (IO.userError "catalog plans do not keep incomplete bindings out of the class folds")
  return tests

def main (args : List String) : IO Unit := do
  let started ← IO.mkRef false
  let completed ← IO.mkRef false
  let failed ← try
      let _ ← FormalAiur.boundedMap 2 #[false, true] fun _ sibling => do
        if sibling then
          started.set true
          IO.sleep 30
          completed.set true
        else
          while !(← started.get) do IO.sleep 1
          throw (IO.userError "intentional scheduler failure")
      pure false
    catch _ => pure true
  unless failed && (← completed.get) do
    throw (IO.userError "failed scheduler returned before its admitted peer finished")
  let reservation : FormalAiur.HostOptions := { ram := 1024, threads := 4 }
  unless (reservation.forWave 2 1).ram == 2048 && (reservation.forWave 2 2).threads == 4 do
    throw (IO.userError "partial waves lost their RAM/CPU reservations")
  let schedule ← IO.ofExcept (Reference.schedulePlan
    #[.leaf 0, .leaf 1, .join 0 1, .leaf 2, .join 2 3] #[2, 3, 4] 4096)
  unless (← IO.ofExcept (neededSlots schedule 2)) == #[true, true, true, false, false] do
    throw (IO.userError "subtree scheduling escaped its dependency closure")
  if (neededSlots schedule 5).toOption.isSome then
    throw (IO.userError "out-of-range subtree was accepted")
  let path := args.headD "/tmp/ix-formal-aggregate-cases.json"
  IO.FS.withTempDir fun dir => do
    fixture (dir / "ixvm") (Array.replicate 8 0)
    fixture (dir / "self") (Array.replicate 16 0)
    let ixvmKey ← IO.FS.readBinFile (dir / "ixvm" / "key.bin")
    let aggrKey ← IO.FS.readBinFile (dir / "self" / "key.bin")
    let ctx : Context := {
      ixvmArtifact := ""
      aggrArtifact := ""
      ixvm := ⟨ixvmKey, 0⟩
      aggr := ⟨aggrKey, 0⟩
      allowed := allowedBlob ixvmKey 0 aggrKey 0 }
    let a := Address.blake3 "formal-a".toUTF8
    let b := Address.blake3 "formal-b".toUTF8
    let c := Address.blake3 "formal-c".toUTF8
    let d := Address.blake3 "formal-d".toUTF8
    let tree (xs : Array Address) := (Ix.AssumptionTree.canonical xs).get!
    let claimCtx ← IO.ofExcept Ix.ClaimContext.ofDefaultTable
    let left : CheckEnvTrees := { ctx := claimCtx, subjects := tree #[a, b], assumptions := some (tree #[c, d]) }
    let right : CheckEnvTrees := { ctx := claimCtx, subjects := tree #[c], assumptions := some (tree #[a]) }
    let li ← node ctx (dir / "li") .ixvm left
    let ri ← node ctx (dir / "ri") .ixvm right
    let la ← node ctx (dir / "la") .aggr left
    let ra ← node ctx (dir / "ra") .aggr right
    let bytes := Ix.Claim.ser left.claim
    let mut tests : Array Json := #[]
    for n in #[li, la] do
      tests := tests.push (test ctx s!"wrap {n.kind.code}" bytes (← advice ctx n none left false))
    for l in #[li, la] do
      for r in #[ri, ra] do
        for structural in #[false, true] do
          let output := if structural then left.joinStructural right else left.join right
          let shape := if structural then structuralShapeCode l.kind r.kind else shapeCode (l.kind, some r.kind)
          let io ← advice ctx l (some r) output structural
          tests := tests.push (test ctx s!"pair shape {shape}" (Ix.Claim.ser output.claim) io)
          let dropped := { output with assumptions := none }
          tests := tests.push (test ctx s!"shape {shape} rejects dropped assumption"
            (Ix.Claim.ser dropped.claim) (extendOutputClaim io (Ix.Claim.ser dropped.claim)) false)
    -- No child assumes its own subject, the children's subjects are disjoint,
    -- and a structural join discharges an assumption only against the other
    -- child's subjects. `advice` derives trees and paths without these checks.
    let selfA : CheckEnvTrees := { ctx := claimCtx, subjects := tree #[a], assumptions := some (tree #[a]) }
    let leftB : CheckEnvTrees := { ctx := claimCtx, subjects := tree #[a, b], assumptions := some (tree #[b, c]) }
    let qi ← node ctx (dir / "q") .ixvm selfA
    let lbi ← node ctx (dir / "lb") .ixvm leftB
    let selfJoins : Array (String × Node × Node × CheckEnvTrees × Bool) := #[
      ("flat pair rejects duplicated self-assuming children", qi, qi,
        { ctx := claimCtx, subjects := tree #[a], assumptions := none }, false),
      ("flat pair rejects a child that assumes its own subject", qi, ri,
        { ctx := claimCtx, subjects := tree #[a, c], assumptions := none }, false),
      ("flat pair rejects overlapping subject sets", li, li, left, false),
      ("structural pair rejects duplicated self-assuming children", qi, qi,
        { ctx := claimCtx, subjects := .join selfA.subjects selfA.subjects, assumptions := none }, true),
      ("structural pair rejects discharging an assumption against its own subjects", lbi, ri,
        { ctx := claimCtx, subjects := .join leftB.subjects right.subjects, assumptions := none }, true)]
    for (label, l, r, output, structural) in selfJoins do
      tests := tests.push (test ctx label (Ix.Claim.ser output.claim)
        (← advice ctx l (some r) output structural) false)
    -- IO ingress: a byte out of byte range that keeps its word's packed value
    -- is refused before anything hashes it.
    let joined := left.join right
    let joinedIo ← advice ctx li (some ri) joined false
    tests := tests.push (test ctx "pair reads genuine preimages and keys (ingress control)"
      (Ix.Claim.ser joined.claim) joinedIo)
    tests := tests.push (test ctx "pair refuses a claim preimage byte out of range"
      (Ix.Claim.ser joined.claim) (joinedIo.extend 4 (MultiStark.digestGs bytes) (shiftedGs bytes))
      false)
    tests := tests.push (test ctx "pair refuses a verifying-key byte out of range"
      (Ix.Claim.ser joined.claim) (joinedIo.extend 1 #[.ofNat 0] (shiftedGs ctx.ixvm.key)) false)
    let wrap ← advice ctx li none left false
    tests := tests.push (test ctx "wrong output digest" (Ix.Claim.ser right.claim) wrap false)
    tests := tests.push (test ctx "wrong child kind" bytes (extendIdentity wrap ctx.allowed 1) false)
    tests := tests.push (test ctx "invalid shape" bytes (extendIdentity wrap ctx.allowed 17) false)
    let badIdentity := ctx.allowed.set! 0 (ctx.allowed.data[0]! ^^^ 1)
    tests := tests.push (test ctx "wrong allowed identity" bytes (extendIdentity wrap badIdentity 0) false)
    let corrupt := li.wrapper.proof.extract 8 li.wrapper.proof.size
    let corrupt := corrupt.extract 0 (corrupt.size - 1)
    let io := extendChild wrap 0 corrupt (MultiStark.serializeClaims #[outerClaim ctx .ixvm left.claim])
    tests := tests.push (test ctx "truncated child proof" bytes io false)
    -- Range leaves bind the preamble, exact interval, and residual.
    let preamble ← IO.FS.readBinFile (dir / "li" / "preamble.bin")
    let full ← IO.FS.readBinFile (dir / "li" / "statement-1.bin")
    let empty ← IO.FS.readBinFile (dir / "li" / "statement-0.bin")
    for (hi, statement) in #[(0, empty), (1, full)] do
      let io := extendVk (extendIdentity default ctx.allowed 10) .ixvm ctx.ixvm.key
      let io := extendChild io 0 preamble ByteArray.empty
      let io := extendChild io 1 (← IO.FS.readBinFile (dir / "li" / s!"range-{hi}.bin")) ByteArray.empty
      let io := extendOutputClaim io statement
      tests := tests.push (test ctx s!"range leaf {hi}" statement io)
      let bad := statement.set! 49 (statement.data[49]! ^^^ 1)
      tests := tests.push (test ctx s!"range leaf {hi} rejects false residual" bad (extendOutputClaim io bad) false)
    -- Stand-in self proofs have exactly the public statement a range node emits.
    fixture (dir / "empty") (pubInput ctx.allowed empty)
    fixture (dir / "full") (pubInput ctx.allowed full)
    let addRange (io : Aiur.IOBuffer) (slot : Nat) (name : String) (stmt : ByteArray) : IO Aiur.IOBuffer := do
      let io := extendVk io .aggr ctx.aggr.key
      let io := extendChild io slot (← IO.FS.readBinFile (dir / name / "proof.bin"))
        (← IO.FS.readBinFile (dir / name / "claims.bin"))
      return extendPreimage io stmt
    let io ← addRange (extendIdentity default ctx.allowed 11) 0 "empty" empty
    let io ← addRange io 1 "full" full
    tests := tests.push (test ctx "range join" full (extendOutputClaim io full))
    let bad := full.set! 49 (full.data[49]! ^^^ 1)
    tests := tests.push (test ctx "range join rejects wrong sum" bad (extendOutputClaim io bad) false)
    let io ← addRange (extendIdentity default ctx.allowed 12) 0 "full" full
    let io := extendVk (extendChild io 1 preamble ByteArray.empty) .ixvm ctx.ixvm.key
    tests := tests.push (test ctx "range root" bytes io)
    tests := tests.push (test ctx "range root rejects wrong claim" (Ix.Claim.ser right.claim) io false)
    let io ← addRange (extendIdentity default ctx.allowed 12) 0 "empty" empty
    let io := extendVk (extendChild io 1 preamble ByteArray.empty) .ixvm ctx.ixvm.key
    tests := tests.push (test ctx "range root rejects incomplete batch" bytes io false)
    tests := tests ++ (← bindingShapeCases ctx dir claimCtx left right li)
    IO.FS.writeFile path (toJson tests).compress
    IO.FS.writeFile (path ++ ".wrap.json") (FormalAiur.invocation (pubInput ctx.allowed bytes) wrap "MultiStark::ix_aggr").compress
    IO.println s!"Wrote {tests.size} aggregation cases: shapes 0 to 16, the invalid shape 17, \
      and negative bindings"
