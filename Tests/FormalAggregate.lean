import Ix.Cli.FormalAggregate

/-! Execute all thirteen aggregation shapes against small real STARK children.
The stand-in keys deliberately accept arbitrary digests; only the production
aggregator's bindings and fold relation are under test. -/
open Lean Aggr Ix.Cli Ix.Cli.FormalAggregate

private def fixture (dir : System.FilePath) (args : Array LegacyAiur.G) : IO Unit := do
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

private def test (ctx : Context) (label : String) (bytes : ByteArray) (io : LegacyAiur.IOBuffer)
    (accept : Bool := true) : Json :=
  Json.mkObj [("label", toJson label), ("accept", toJson accept),
    ("invocation", FormalAiur.invocation (pubInput ctx.allowed bytes) io "MultiStark::ix_aggr")]

def main (args : List String) : IO Unit := do
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
    let left : CheckEnvTrees := { subjects := tree #[a, b], assumptions := some (tree #[c, d]) }
    let right : CheckEnvTrees := { subjects := tree #[c], assumptions := some (tree #[a]) }
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
    let wrap ← advice ctx li none left false
    tests := tests.push (test ctx "wrong output digest" (Ix.Claim.ser right.claim) wrap false)
    tests := tests.push (test ctx "wrong child kind" bytes (extendIdentity wrap ctx.allowed 1) false)
    tests := tests.push (test ctx "invalid shape" bytes (extendIdentity wrap ctx.allowed 13) false)
    let badIdentity := ctx.allowed.set! 0 (ctx.allowed.data[0]! ^^^ 1)
    tests := tests.push (test ctx "wrong allowed identity" bytes (extendIdentity wrap badIdentity 0) false)
    let corrupt := li.wrapper.proof.extract 8 li.wrapper.proof.size
    let corrupt := corrupt.extract 0 (corrupt.size - 1)
    let io := extendChild wrap 0 corrupt (LegacyMultiStark.serializeClaims #[outerClaim ctx .ixvm left.claim])
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
    let addRange (io : LegacyAiur.IOBuffer) (slot : Nat) (name : String) (stmt : ByteArray) : IO LegacyAiur.IOBuffer := do
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
    IO.FS.writeFile path (toJson tests).compress
    IO.FS.writeFile (path ++ ".wrap.json") (FormalAiur.invocation (pubInput ctx.allowed bytes) wrap "MultiStark::ix_aggr").compress
    IO.println s!"Wrote {tests.size} aggregation cases, including every shape and negative bindings"
