import Ix.Compiler.Ixon.Catalog
import Ix.Compiler.Pipeline

/-! Shared byte-exact production-writer fixture data for runtime tests and the
source-coverage gate. Loading never rewrites or reencodes the captured input. -/

open Ix.Compiler.Ixon

namespace CatalogContactFixture

def directory : String := "Tests/Fixtures/Compiler/ixon-std-contact"

def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\r' || c == '\t'

def hexNibble? (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
  else none

def decodeHex (text : String) : Except String ByteArray := do
  let digits := (text.toList.filter fun c => !isWhitespace c).toArray
  if digits.size % 2 != 0 then
    throw s!"odd hex digit count {digits.size}"
  let mut bytes := ByteArray.empty
  for index in [:digits.size / 2] do
    let some high := hexNibble? digits[2 * index]!
      | throw s!"invalid hex digit at {2 * index}"
    let some low := hexNibble? digits[2 * index + 1]!
      | throw s!"invalid hex digit at {2 * index + 1}"
    bytes := bytes.push (high * 16 + low)
  return bytes

def readHexAt (root : System.FilePath) (filename : String) : IO (Except String ByteArray) := do
  try
    let path := root / filename
    if (← path.metadata).byteSize > 65536 then
      return .error s!"contact hex file exceeds the 64 KiB fixture limit: {filename}"
    return decodeHex (← IO.FS.readFile path)
  catch error =>
    return .error error.toString

def readHex (filename : String) : IO (Except String ByteArray) :=
  readHexAt directory filename

def expectedStats : Catalog.Stats :=
  { manifestBytes := 267
    members := 1
    dependencyEdges := 0
    storageUnits := 1
    pieceBytes := 14600
    constantEntries := 54
    constantBytes := 8828
    blobEntries := 91
    blobBytes := 819
    assumptions := 0
    hints := 30
    expressionUnits := 2143
    expandedExpressionUnits := 3877
    layer1NodeVisits := 34656
    unionConstants := 54 }

def expectedMembersRoot : String :=
  "4585514401609ffa79ea09af28a0e1eb87be6b3306fe357511bc59323e18e18e"

def expectedContentRoot : String :=
  "1bc7e2215a1967d8c937f48526facdc7006cd4c9b7b6ef4f1063bb55c50dee02"

def expectedPieceHash : String :=
  "688985515005111bde0e25969181c649ada8b77d70287a71e18751f36b495988"

def expectedPipelineAddress : String :=
  "131533e96baa7f50ba89d01892243e11a1221c8831e2f394eb14f89e9a54c6c4"

/-- C2 admits the original closed failure slice. The unchanged full catalog
then encounters this later unique-to-shared sink. -/
def expectedRemainingFreezeAddress : String :=
  "a3b83ad0799bcd3d1c70c01df44141d79e7358e1f23d7d7e5cf9e01dbdc73c85"

def load (root : System.FilePath) : IO (Except String Catalog.Loaded) := do
  let manifest ← readHexAt root "manifest.hex"
  let piece ← readHexAt root "CompilatrixStdContact.ixe.hex"
  return do
    let manifest ← manifest
    let piece ← piece
    if manifest.size != 267 || piece.size != 14600 ||
        (Address.blake3 piece).toHex != expectedPieceHash then
      throw "production contact byte sizes or hash drifted"
    let loaded ← (Catalog.load manifest #[piece]).mapError (fun error => reprStr error)
    if loaded.manifest.membersRoot.toHex != expectedMembersRoot ||
        loaded.manifest.contentRoot.toHex != expectedContentRoot ||
        loaded.stats != expectedStats then
      throw "production contact commitments or counters drifted"
    let some member := loaded.manifest.members[0]? | throw "production contact member is absent"
    if member.label != "CompilatrixStdContact" || member.toolchain != "leanprover/lean4:v4.33.1" ||
        member.sourcePin != "git:ix@6f18ea907b78d06f7dc0917c43beb385561c35f4" ||
        member.constCount != 54 then
      throw "production contact provenance drifted"
    return loaded

/-- The dependency closure uses all reference-table entries and projection
block keys. Blob references remain in the loaded catalog; no constant bytes
or references are edited while shrinking the compilation unit. -/
def dependencies (constant : Constant) : List Address :=
  constant.refs.toList ++ match constant.info with
    | .iPrj projection => [projection.block]
    | .cPrj projection => [projection.block]
    | .rPrj projection => [projection.block]
    | .dPrj projection => [projection.block]
    | _ => []

def dependencyClosure (constants : List (Address × Constant)) (root : Address) :
    List (Address × Constant) := Id.run do
  let available := constants.map (·.1)
  let mut reachable := [root]
  for _ in [:constants.length] do
    for entry in constants do
      if reachable.contains entry.1 then
        for address in dependencies entry.2 do
          if available.contains address && !reachable.contains address then
            reachable := reachable ++ [address]
  return constants.filter fun entry => reachable.contains entry.1

def isClosed (available subset : List (Address × Constant)) : Bool :=
  let allKeys := available.map (·.1)
  let subsetKeys := subset.map (·.1)
  subset.all fun entry => (dependencies entry.2).all fun address =>
    !allKeys.contains address || subsetKeys.contains address

def freezesAt (constants : List (Address × Constant)) (root : Address) : Bool :=
  match Ix.Compiler.Pipeline.checkProgram constants with
  | .error (.usage rejected .freezeNeeded) => rejected == root
  | _ => false

end CatalogContactFixture
