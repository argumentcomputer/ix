module
public import Ix.Ixon
public import Ix.AssumptionTree
public import Ix.Claim
public import Ix.Shard.Manifest
public import IxC.Ixon.Canonical
public import Ix.Cert.Compile
public import LSpec

/-! # Malformed inputs Lean's readers refuse, as Rust's do

The Lean side of the shared fixture `Tests/Fixtures/ixon-v4/reject-parity.txt`,
whose Rust side is `crates/ixon/tests/reject_parity.rs` and
`crates/kernel/tests/reject_parity.rs`: every reader of a case's kind refuses
it, and accepts the kind's controls. The kinds and the readers:

* `record`: the canonical decoder of host admission (`Canonical.deConstant` at
  `check-lean`'s limits), the loaders' bounded decoder (`deConstantLoaded`) and
  the lazy window decoder (`deConstantAt`);
* `noncanonical`: the canonical decoder;
* `env`: the full reader (`deEnv`) and the verified loader
  (`deEnvVerifiedLazy`);
* `ixes`: `parseIxesManifest`;
* `tree`: `AssumptionTree.de`;
* `claim`: `Claim.de`. -/

open LSpec

public section

namespace Tests.Ix.IxonRejectParity

def fixturePath : System.FilePath := "Tests/Fixtures/ixon-v4/reject-parity.txt"

/-- One fixture case. -/
structure Case where
  kind : String
  name : String
  bytes : ByteArray

def hexDigit (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else none

/-- A token's bytes: hex digits, or `XX*N` for `N` copies of them. -/
def tokenBytes (token : String) : Except String ByteArray := do
  let (hex, count) ← match token.splitOn "*" with
    | [hex] => pure (hex, 1)
    | [hex, n] => match n.toNat? with
      | some n => pure (hex, n)
      | none => throw s!"bad repeat count in {token}"
    | _ => throw s!"bad token {token}"
  let digits := hex.toList
  unless digits.length % 2 == 0 do throw s!"odd hex token {token}"
  let mut chunk : ByteArray := .empty
  for i in [0:digits.length / 2] do
    match hexDigit digits[2 * i]!, hexDigit digits[2 * i + 1]! with
    | some hi, some lo => chunk := chunk.push (hi * 16 + lo)
    | _, _ => throw s!"bad hex token {token}"
  let mut out : ByteArray := .empty
  for _ in [0:count] do
    out := out ++ chunk
  return out

def parseCases (text : String) : Except String (Array Case) := do
  let mut cases := #[]
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn " " |>.filter (!·.isEmpty) with
    | kind :: name :: tokens =>
      let mut bytes : ByteArray := .empty
      for token in tokens do
        bytes := bytes ++ (← tokenBytes token)
      cases := cases.push { kind, name, bytes }
    | _ => throw s!"bad fixture line: {line}"
  return cases

/-- Host admission's per-record limits (`check-lean`'s `artifactLimits`). -/
def maxRecordBytes : Nat := 1 <<< 28
def maxRecordUnivNodes : Nat := 1 <<< 26

/-- The readers of a kind, each with whether it accepts `bytes`. -/
def readers (kind : String) (bytes : ByteArray) : Option (List (String × Bool)) :=
  let canonical := ("Canonical.deConstant",
    (Ixon.Canonical.deConstant maxRecordBytes maxRecordUnivNodes bytes).isOk)
  match kind with
  | "record" => some [canonical,
      ("deConstantLoaded", (Ixon.Env.deConstantLoaded bytes).isOk),
      ("deConstantAt", (Ixon.deConstantAt bytes 0 bytes.size).isOk),
      ("refsAt", (Ix.Cert.RecordRefs.refsAt bytes 0 bytes.size).isSome)]
  | "noncanonical" => some [canonical]
  | "env" => some [("deEnv", (Ixon.deEnv bytes).isOk),
      ("deEnvVerifiedLazy", (Ixon.deEnvVerifiedLazy bytes).isOk)]
  | "ixes" => some [("parseIxesManifest", (Ix.Shard.parseIxesManifest bytes).isOk)]
  | "tree" => some [("AssumptionTree.de", (Ix.AssumptionTree.de bytes).isOk)]
  | "claim" => some [("Claim.de", (Ix.Claim.de bytes).isOk)]
  | _ => none

/-- The same small table at its exact aggregate budget and one node below.
The offset control also exercises a record embedded between unrelated bytes. -/
def budgetTests : TestSeq := Id.run do
  let c : Ixon.Constant := {
    info := .axio { isUnsafe := false, lvls := 0, typ := .sort 0 }
    sharing := #[], refs := #[], univs := #[.succ .zero, .zero] }
  let bytes := Ixon.serConstant c
  let window := ByteArray.mk #[255] ++ bytes ++ ByteArray.mk #[255]
  let noUnivs := { c with univs := #[] }
  let noUnivBytes := Ixon.serConstant noUnivs
  let block : Ix.CompileM.BlockResult := {
    block := c, blockBytes := bytes, blockAddr := default }
  let projected : Ix.CompileM.BlockResult :=
    { block with block := noUnivs, projections := #[(Ix.Name.anonymous default, c, .empty)] }
  return test "lazy window accepts the exact aggregate universe budget"
      ((Ixon.deConstantAt window 1 bytes.size 3).toOption == some c) ++
    test "lazy window refuses a universe table one node over budget"
      (!(Ixon.deConstantAt window 1 bytes.size 2).isOk) ++
    test "refs-only reader accepts the exact aggregate universe budget"
      (Ix.Cert.RecordRefs.refsAt window 1 bytes.size 3 == some (#[], none)) ++
    test "refs-only reader shares the budget across universe entries"
      ((Ix.Cert.RecordRefs.refsAt window 1 bytes.size 2).isNone) ++
    test "empty universe tables accept a zero budget"
      ((Ixon.deConstantAt noUnivBytes 0 noUnivBytes.size 0).toOption == some noUnivs) ++
    test "compiler accepts a block at the loader budget"
      (Ix.CompileM.blockUnivsFit block 3) ++
    test "compiler refuses a block above the loader budget"
      (!Ix.CompileM.blockUnivsFit block 2) ++
    test "compiler checks projection records against the loader budget"
      (!Ix.CompileM.blockUnivsFit projected 2)

/-- Every case of the fixture, every reader of its kind: a control accepted,
any other case refused. -/
def suite : IO (List TestSeq) := do
  let cases ← IO.ofExcept (parseCases (← IO.FS.readFile fixturePath))
  let mut tests : TestSeq := budgetTests
  for case in cases do
    let (kind, accepted) := match case.kind.dropSuffix? "-accept" with
      | some kind => (kind.toString, true)
      | none => (case.kind, false)
    match readers kind case.bytes with
    | none => tests := tests ++ test s!"{case.kind} {case.name}: known kind" false
    | some results =>
      for (reader, result) in results do
        let verb := if accepted then "accepts" else "refuses"
        tests := tests ++ test s!"{reader} {verb} {case.kind} {case.name}" (result == accepted)
  return [tests]

end Tests.Ix.IxonRejectParity

end
