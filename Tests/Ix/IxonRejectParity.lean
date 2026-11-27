module
public import Ix.Ixon
public import Ix.AssumptionTree
public import Ix.Claim
public import Ix.Shard.Manifest
public import IxC.Ixon.Canonical
public import Ix.Cert.Compile
public import LSpec

/-! # Malformed inputs Lean's readers refuse, as Rust's do

The Lean side of the shared fixture `Tests/Fixtures/ixon/reject-parity.txt`,
whose Rust side is `crates/ixon/tests/reject_parity.rs` (every kind but
`ixes`): every reader of a case's kind refuses
it, and accepts the kind's controls. The kinds and the readers:

* `record`: the canonical decoder of host admission (`Canonical.deConstant` at
  `check-lean`'s limits), the loaders' bounded decoder (`deConstantLoaded`) and
  the lazy window decoder (`deConstantAt`);
* `noncanonical`: the canonical decoder;
* `canonical-rule`: the canonical decoder; a record rule beyond the codec (a
  theorem with assertions) refuses these bytes, which the codec reads;
* `env`: the full reader (`deEnv`) and the verified loader
  (`deEnvVerifiedLazy`);
* `ixes`: `parseIxesManifest`;
* `tree`: `AssumptionTree.de`;
* `claim`: `Claim.de`. -/

open LSpec

public section

namespace Tests.Ix.IxonRejectParity

def fixturePath : System.FilePath := "Tests/Fixtures/ixon/reject-parity.txt"

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

/-- The readers of a kind, each as `(name, acceptsFn)`. -/
def readerFns (kind : String) : Option (List (String × (ByteArray → Bool))) :=
  let canonical := ("Canonical.deConstant", fun bytes =>
    (Ixon.Canonical.deConstant maxRecordBytes maxRecordUnivNodes bytes).isOk)
  match kind with
  | "record" => some [canonical,
      ("deConstantLoaded", fun bytes => (Ixon.Env.deConstantLoaded bytes).isOk),
      ("deConstantAt", fun bytes => (Ixon.deConstantAt bytes 0 bytes.size).isOk),
      ("refsAt", fun bytes => (Ix.Cert.RecordRefs.refsAt bytes 0 bytes.size).isSome)]
  | "noncanonical" | "canonical-rule" => some [canonical]
  | "env" => some [("deEnv", fun bytes => (Ixon.deEnv bytes).isOk),
      ("deEnvVerifiedLazy", fun bytes => (Ixon.deEnvVerifiedLazy bytes).isOk)]
  | "ixes" => some [("parseIxesManifest", fun bytes => (Ix.Shard.parseIxesManifest bytes).isOk)]
  | "tree" => some [("AssumptionTree.de", fun bytes => (Ix.AssumptionTree.de bytes).isOk)]
  | "claim" => some [("Claim.de", fun bytes => (Ix.Claim.de bytes).isOk)]
  | _ => none

/-- The readers of a kind, each with whether it accepts `bytes`. -/
def readers (kind : String) (bytes : ByteArray) : Option (List (String × Bool)) :=
  (readerFns kind).map fun rs => rs.map fun (name, f) => (name, f bytes)

/-- The same small table at its exact aggregate budget and one node below.
The offset control also exercises a record embedded between unrelated bytes. -/
def budgetTests : LSpec.Spec := do
  let mkFixture := fun () =>
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
    (c, bytes, window, noUnivs, noUnivBytes, block, projected)
  it "lazy window accepts the exact aggregate universe budget" do
    let (c, bytes, window, _, _, _, _) := mkFixture ()
    expect ((Ixon.deConstantAt window 1 bytes.size 3).toOption == some c)
  it "lazy window refuses a universe table one node over budget" do
    let (_, bytes, window, _, _, _, _) := mkFixture ()
    expect (!(Ixon.deConstantAt window 1 bytes.size 2).isOk)
  it "refs-only reader accepts the exact aggregate universe budget" do
    let (_, bytes, window, _, _, _, _) := mkFixture ()
    expect (Ix.Cert.RecordRefs.refsAt window 1 bytes.size 3 == some (#[], none))
  it "refs-only reader shares the budget across universe entries" do
    let (_, bytes, window, _, _, _, _) := mkFixture ()
    expect (Ix.Cert.RecordRefs.refsAt window 1 bytes.size 2).isNone
  it "empty universe tables accept a zero budget" do
    let (_, _, _, noUnivs, noUnivBytes, _, _) := mkFixture ()
    expect ((Ixon.deConstantAt noUnivBytes 0 noUnivBytes.size 0).toOption == some noUnivs)
  it "compiler accepts a block at the loader budget" do
    let (_, _, _, _, _, block, _) := mkFixture ()
    expect (Ix.CompileM.blockUnivsFit block 3)
  it "compiler refuses a block above the loader budget" do
    let (_, _, _, _, _, block, _) := mkFixture ()
    expect (!Ix.CompileM.blockUnivsFit block 2)
  it "compiler checks projection records against the loader budget" do
    let (_, _, _, _, _, _, projected) := mkFixture ()
    expect (!Ix.CompileM.blockUnivsFit projected 2)

/-- Every case of the fixture, every reader of its kind: a control accepted,
any other case refused. -/
def suite : IO Spec := do
  let cases ← IO.ofExcept (parseCases (← IO.FS.readFile fixturePath))
  return do
    budgetTests
    for case in cases do
      let (kind, accepted) := match case.kind.dropSuffix? "-accept" with
        | some kind => (kind.toString, true)
        | none => (case.kind, false)
      match readerFns kind with
      | none => itBool s!"{case.kind} {case.name}: known kind" false
      | some fns =>
        for (reader, check) in fns do
          let verb := if accepted then "accepts" else "refuses"
          itBool s!"{reader} {verb} {case.kind} {case.name}" (check case.bytes == accepted)
        -- a record rule beyond the codec: the codec reads the bytes either way
        if kind == "canonical-rule" then
          itBool s!"the codec reads {case.kind} {case.name}"
            (Ixon.runGetExact Ixon.getConstant case.bytes).isOk

end Tests.Ix.IxonRejectParity

end
