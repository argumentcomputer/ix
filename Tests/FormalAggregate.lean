import Tests.FormalAdvice

/-! Execute the aggregation shapes against small real STARK children, and
dump the Lean reference streams of every shape the aggregate controller
proves (wraps, pairs, binding discharge and catalog joins) for
`streams_parity`. The stand-in keys deliberately accept arbitrary digests;
only the production aggregator's bindings and fold relation are under test.
Catalog joins are dumped for stream parity only: their circuit reads the
literal class from real role binding sections, which these members lack. -/
open Lean Aggr Ix.Cli Ix.Cli.FormalAggregate Ix.Cli.FormalAdvice

private def fixture (dir : System.FilePath) (args : Array Aiur.G) : IO Unit := do
  IO.FS.withTempFile fun h path => do
    h.putStr (toJson (args.map (·.n))).compress
    h.flush
    FormalAiur.command "target/release/examples/claim_fixture" #[path.toString, dir.toString]

/-- A stand-in proof of `claim` as a `kind` child: a `claim_fixture` proof
whose public input is the child's outer claim. -/
private def standIn (ctx : Context) (dir : System.FilePath) (kind : ChildKind)
    (claim : Ix.Claim) : IO Ixon.Proof := do
  fixture dir ((outerClaim ctx kind claim).extract 2 18)
  let magic := (if kind == .ixvm then "IXAIUR2\x00" else "IXAGGR2\x00").toUTF8
  return { claim, proof := magic ++ (← IO.FS.readBinFile (dir / "proof.bin")) }

private def node (ctx : Context) (dir : System.FilePath) (kind : ChildKind)
    (statement : CheckEnvTrees) : IO Node := do
  return { kind, statement, wrapper := ← standIn ctx dir kind statement.claim }

/-- The advice of a wrap or pair as the `IOBuffer` the circuit cases run. -/
private def advice (ctx : Context) (left : Node) (right : Option Node)
    (output : CheckEnvTrees) (structural : Bool) : IO Aiur.IOBuffer :=
  return (← streamsAdvice ctx left right output structural).toIOBuffer

private def test (ctx : Context) (label : String) (bytes : ByteArray) (io : Aiur.IOBuffer)
    (accept : Bool := true) : Json :=
  Json.mkObj [("label", toJson label), ("accept", toJson accept),
    ("invocation", FormalAiur.invocation (pubInput ctx.allowed bytes) io "MultiStark::ix_aggr")]

private def hex (b : ByteArray) : String :=
  b.foldl (init := "") fun s x =>
    let d := Nat.toDigits 16 x.toNat
    s ++ (if d.length == 1 then "0" else "") ++ String.mk d

/-- The ordered streams of an advice, for the Rust encoder's parity check. -/
private def entriesJson (s : Streams) : Json :=
  toJson (s.entries.map fun (e : UInt64 × Array UInt64 × ByteArray) =>
    Json.arr #[toJson e.1.toNat, toJson (e.2.1.map (·.toNat)), toJson (hex e.2.2)])

private def treeJson (t : Ix.AssumptionTree) : Json :=
  toJson (t.leaves.map toString)

/-- A child given by its claim and proof only. -/
private def wrapperJson (kind : ChildKind) (w : Ixon.Proof) : IO Json := do
  return Json.mkObj [("kind", toJson kind.code), ("claim", toJson (hex (Ix.Claim.ser w.claim))),
    ("proof", toJson (hex (← rawProof kind w.proof)))]

private def childJson (n : Node) : IO Json := do
  return Json.mkObj [("kind", toJson n.kind.code), ("subjects", treeJson n.statement.subjects),
    ("assumptions", match n.statement.assumptions with | some t => treeJson t | none => Json.null),
    ("claim", toJson (hex (Ix.Claim.ser n.statement.claim))),
    ("proof", toJson (hex (← rawProof n.kind n.wrapper.proof)))]

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
    let mut streams : Array Json := #[]
    for n in #[li, la] do
      streams := streams.push (Json.mkObj [("label", toJson s!"wrap {n.kind.code}"),
        ("type", toJson "wrap"), ("shape", toJson n.kind.code), ("children", toJson #[← childJson n]),
        ("entries", entriesJson (← streamsAdvice ctx n none left false))])
    -- Shared assumption trees, and two children of one kind, replace streams in place.
    let shared (subjects : Address) : CheckEnvTrees :=
      { ctx := claimCtx, subjects := tree #[subjects], assumptions := some (tree #[c]) }
    let sharedNode (s : CheckEnvTrees) : Node :=
      { kind := .aggr, statement := s, wrapper := { claim := s.claim, proof := la.wrapper.proof } }
    let pairs := (#[li, la].flatMap fun l => #[ri, ra].map fun r => (l, r, left, right)).push
      (sharedNode (shared a), sharedNode (shared b), shared a, shared b)
    for (l, r, ls, rs) in pairs do
      for structural in #[false, true] do
        let output := if structural then ls.joinStructural rs else ls.join rs
        let shape := if structural then structuralShapeCode l.kind r.kind else shapeCode (l.kind, some r.kind)
        streams := streams.push (Json.mkObj [("label", toJson s!"pair shape {shape} over {l.kind.code}{r.kind.code}"),
          ("type", toJson "pair"), ("shape", toJson shape), ("structural", toJson structural),
          ("children", toJson #[← childJson l, ← childJson r]),
          ("output", toJson (hex (Ix.Claim.ser output.claim))),
          ("entries", entriesJson (← streamsAdvice ctx l (some r) output structural))])
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
    -- Binding discharge (shapes 13 and 14): a child that assumes its binding,
    -- and the stand-in IxVM proof of that binding's claim.
    let assumed : CheckEnvTrees := { left with ctx := { claimCtx with bindingAssumed := true } }
    let discharged := dischargedStatement assumed
    let bindingWrapper ← standIn ctx (dir / "binding") .ixvm (.binding claimCtx.spec claimCtx.binding)
    for kind in #[ChildKind.ixvm, .aggr] do
      let child ← node ctx (dir / s!"assumed-{kind.code}") kind assumed
      let s ← streamsDischarge ctx child bindingWrapper discharged
      let shape := dischargeShapeCode kind
      let outBytes := Ix.Claim.ser discharged.claim
      streams := streams.push (Json.mkObj [("label", toJson s!"discharge shape {shape}"),
        ("type", toJson "discharge"), ("shape", toJson shape),
        ("children", toJson #[← childJson child, ← wrapperJson .ixvm bindingWrapper]),
        ("output", toJson (hex outBytes)), ("entries", entriesJson s)])
      tests := tests.push (test ctx s!"discharge shape {shape}" outBytes s.toIOBuffer)
      let still := Ix.Claim.ser assumed.claim
      tests := tests.push (test ctx s!"discharge shape {shape} rejects a claim that still assumes the binding"
        still (extendOutputClaim s.toIOBuffer still) false)
    -- A catalog's plan: two members of one literal class fold with the
    -- cross-binding pair (shape 15), and a member without a class joins
    -- them into a catalog (shape 16).
    let member (label : String) (subjects : Array Address) (klass : Option Address) : CatalogMember :=
      let ctx' := { claimCtx with binding := Address.blake3 (s!"binding-{label}").toUTF8 }
      { label, toolchain := label, claim := .checkEnv ctx' (tree subjects).root none,
        bindingSection := (s!"section-{label}").toUTF8, literalClass := klass }
    let klass := Address.blake3 "formal-class".toUTF8
    let members := #[member "m0" #[a, b] (some klass), member "m1" #[c] (some klass),
      member "m2" #[d] none]
    let plan ← IO.ofExcept (catalogPlan members)
    let mut proofs : Array (Option Ixon.Proof) := #[]
    for i in [:plan.nodes.size] do
      proofs := proofs.push (some (← standIn ctx (dir / s!"catalog-{i}") .aggr plan.statements[i]!.claim))
    let membersJson := members.map fun m => Json.mkObj [("label", toJson m.label),
      ("claim", toJson (hex (Ix.Claim.ser m.claim))), ("binding_section", toJson (hex m.bindingSection)),
      ("literal_class", toJson (m.literalClass.map toString))]
    for i in [:plan.nodes.size] do
      let some (shape, s) ← streamsCatalog ctx plan members proofs i | continue
      let kindLabel := match plan.nodes[i]! with
        | .crossBinding .. => "cross-binding" | _ => "catalog-join"
      let mut children : Array Json := #[]
      for c in plan.nodes[i]!.children do
        children := children.push (← wrapperJson .aggr proofs[c]!.get!)
      streams := streams.push (Json.mkObj [("label", toJson s!"catalog node {i} shape {shape} ({kindLabel})"),
        ("type", toJson kindLabel), ("shape", toJson shape), ("node", toJson i),
        ("members", toJson membersJson), ("children", toJson children),
        ("output", toJson (hex (Ix.Claim.ser plan.statements[i]!.claim))), ("entries", entriesJson s)])
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
    IO.FS.writeFile (path ++ ".streams.json") (Json.mkObj [("allowed", toJson (hex ctx.allowed)),
      ("ixvm_key", toJson (hex ctx.ixvm.key)), ("aggr_key", toJson (hex ctx.aggr.key)),
      ("cases", toJson streams)]).compress
    IO.FS.writeFile path (toJson tests).compress
    IO.FS.writeFile (path ++ ".wrap.json") (FormalAiur.invocation (pubInput ctx.allowed bytes) wrap "MultiStark::ix_aggr").compress
    IO.println s!"Wrote {tests.size} aggregation cases, including every shape and negative bindings"
