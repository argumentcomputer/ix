import Compilatrix.Tools.Check
import Compilatrix.Tools.UniqueCheck
import Compilatrix.Ixon.Hash

/-!
# Independent IxIR₂ snapshot wire oracle

This module imports no IxIR₂ types, encoder, decoder, evaluator or compiler.
Its separate cursor grammar reads canonical primitives directly and rebuilds
complete diagnostic trees. Reviewed roots and full byte/JSON comparison keep
fresh-process agreement from accepting an identically corrupted artifact.
-/

namespace Compilatrix.Tools.IxIR2Check

open Lean Compilatrix.Ixon

structure Limits where
  maxBytes : Nat := 16777216
  maxNatBytes : Nat := 64
  maxSequence : Nat := 65536
  maxBlobBytes : Nat := 1048576

private structure Cursor where
  bytes : ByteArray
  limits : Limits
  position : Nat := 0

private abbrev Parser := StateT Cursor (Except String)

private def readBytes (count : Nat) : Parser ByteArray := do
  let cursor ← get
  if cursor.position + count > cursor.bytes.size then throw "truncated IxIR2 snapshot"
  set { cursor with position := cursor.position + count }
  return cursor.bytes.extract cursor.position (cursor.position + count)

private def readByte : Parser Nat := do
  return (← readBytes 1)[0]!.toNat

private def readNatural : Parser Nat := do
  let width := (← get).limits.maxNatBytes
  let mut value := 0
  let mut factor := 1
  for index in [:width] do
    let byte ← readByte
    let digit := byte % 128
    value := value + digit * factor
    if byte < 128 then
      if index > 0 && digit == 0 then throw "nonminimal IxIR2 natural"
      return value
    factor := factor * 128
  throw "IxIR2 natural width limit"

private def readBlob : Parser ByteArray := do
  let size ← readNatural
  if size > (← get).limits.maxBlobBytes then throw "IxIR2 blob length limit"
  readBytes size

private def bytesHex (bytes : ByteArray) : String :=
  bytes.data.foldl (fun output byte => output ++ hexDigitRepr (byte.toNat / 16) ++
    hexDigitRepr (byte.toNat % 16)) ""

private def readNaturalJson : Parser Json := do return toJson (← readNatural)
private def readBlobJson : Parser Json := do return toJson (bytesHex (← readBlob))
private def readAddressJson : Parser Json := do return toJson (bytesHex (← readBytes 32))
private def readStringJson : Parser Json := do
  let some value := String.fromUTF8? (← readBlob) | throw "invalid IxIR2 UTF-8"
  return toJson value
private def readBoolJson : Parser Json := do
  match ← readByte with
  | 0 => return toJson false
  | 1 => return toJson true
  | _ => throw "invalid IxIR2 Boolean"
private def readOwnedJson : Parser Json := do
  match ← readByte with
  | 0 => return toJson "unique"
  | 1 => return toJson "shared"
  | _ => throw "invalid IxIR2 ownership"

private def readArray (readOne : Parser Json) : Parser Json := do
  let count ← readNatural
  if count > (← get).limits.maxSequence then throw "IxIR2 sequence length limit"
  let mut values := #[]
  for _ in [:count] do values := values.push (← readOne)
  return Json.arr values

private def readLiteral : Parser Json := do
  match ← readByte with
  | 0 =>
      let value0 ← readNaturalJson
      return Json.arr #[toJson "nat", value0]
  | 1 =>
      let value0 ← readStringJson
      return Json.arr #[toJson "str", value0]
  | _ => throw "invalid IxIR2 literal tag"

private def readAtom : Parser Json := do
  match ← readByte with
  | 0 =>
      let value0 ← readNaturalJson
      return Json.arr #[toJson "reg", value0]
  | 1 =>
      let value0 ← readLiteral
      return Json.arr #[toJson "lit", value0]
  | 2 =>
      return Json.arr #[toJson "erased"]
  | _ => throw "invalid IxIR2 atom tag"

private def readParamPassing : Parser Json := do
  match ← readByte with
  | 0 =>
      return Json.arr #[toJson "owned"]
  | 1 =>
      return Json.arr #[toJson "borrowed"]
  | _ => throw "invalid IxIR2 paramPassing tag"

private def readParam : Parser Json := do
  let value0 ← readOwnedJson
  let value1 ← readParamPassing
  return Json.mkObj [
    ("world", value0),
    ("passing", value1)]

private def readParamArray : Parser Json := readArray readParam

private def readSignature : Parser Json := do
  let value0 ← readParamArray
  let value1 ← readOwnedJson
  let value2 ← readBoolJson
  return Json.mkObj [
    ("params", value0),
    ("result", value1),
    ("papSafe", value2)]

private def readBorrowLender : Parser Json := do
  match ← readByte with
  | 0 =>
      return Json.arr #[toJson "caller"]
  | 1 =>
      let value0 ← readNaturalJson
      return Json.arr #[toJson "value", value0]
  | _ => throw "invalid IxIR2 borrowLender tag"

private def readValueCap : Parser Json := do
  match ← readByte with
  | 0 =>
      return Json.arr #[toJson "scalar"]
  | 1 =>
      let value0 ← readOwnedJson
      return Json.arr #[toJson "owned", value0]
  | 2 =>
      let value0 ← readOwnedJson
      let value1 ← readBorrowLender
      return Json.arr #[toJson "borrowed", value0, value1]
  | _ => throw "invalid IxIR2 valueCap tag"

private def readCreditCap : Parser Json := do
  match ← readByte with
  | 0 =>
      let value0 ← readAddressJson
      return Json.arr #[toJson "required", value0]
  | 1 =>
      let value0 ← readAddressJson
      return Json.arr #[toJson "optional", value0]
  | _ => throw "invalid IxIR2 creditCap tag"

private def readCtorId : Parser Json := do
  let value0 ← readAddressJson
  let value1 ← readNaturalJson
  let value2 ← readNaturalJson
  return Json.mkObj [
    ("block", value0),
    ("indIdx", value1),
    ("cidx", value2)]

private def readOwnedArray : Parser Json := readArray readOwnedJson

private def readCtorSchema : Parser Json := do
  let value0 ← readAddressJson
  let value1 ← readOwnedArray
  return Json.mkObj [
    ("layout", value0),
    ("fields", value1)]

private def readAtomArray : Parser Json := readArray readAtom

private def readInstr : Parser Json := do
  match ← readByte with
  | 0 =>
      let value0 ← readAtom
      return Json.arr #[toJson "move", value0]
  | 1 =>
      let value0 ← readOwnedJson
      let value1 ← readCtorId
      let value2 ← readAtomArray
      return Json.arr #[toJson "alloc", value0, value1, value2]
  | 2 =>
      let value0 ← readNaturalJson
      let value1 ← readOwnedJson
      let value2 ← readCtorId
      let value3 ← readAtomArray
      return Json.arr #[toJson "allocWith", value0, value1, value2, value3]
  | 3 =>
      let value0 ← readNaturalJson
      return Json.arr #[toJson "discardCredit", value0]
  | 4 =>
      let value0 ← readAtom
      let value1 ← readCtorId
      return Json.arr #[toJson "takeUnique", value0, value1]
  | 5 =>
      let value0 ← readAtom
      let value1 ← readCtorId
      return Json.arr #[toJson "resetShared", value0, value1]
  | 6 =>
      let value0 ← readAtom
      return Json.arr #[toJson "retainShared", value0]
  | 7 =>
      let value0 ← readAtom
      return Json.arr #[toJson "releaseShared", value0]
  | 8 =>
      let value0 ← readAtom
      return Json.arr #[toJson "dropUnique", value0]
  | 9 =>
      let value0 ← readAtom
      let value1 ← readCtorId
      return Json.arr #[toJson "freeUnique", value0, value1]
  | 10 =>
      let value0 ← readAtom
      let value1 ← readCtorId
      let value2 ← readNaturalJson
      return Json.arr #[toJson "fetch", value0, value1, value2]
  | 11 =>
      let value0 ← readAddressJson
      let value1 ← readAtomArray
      return Json.arr #[toJson "call", value0, value1]
  | 12 =>
      let value0 ← readAtomArray
      return Json.arr #[toJson "callSelf", value0]
  | 13 =>
      let value0 ← readAddressJson
      let value1 ← readAtomArray
      return Json.arr #[toJson "papp", value0, value1]
  | 14 =>
      let value0 ← readAtom
      let value1 ← readAtomArray
      return Json.arr #[toJson "apply", value0, value1]
  | 15 =>
      let value0 ← readAddressJson
      let value1 ← readAtomArray
      return Json.arr #[toJson "extern", value0, value1]
  | _ => throw "invalid IxIR2 instr tag"

private def readNatArray : Parser Json := readArray readNaturalJson

private def readEdge : Parser Json := do
  let value0 ← readNaturalJson
  let value1 ← readAtomArray
  let value2 ← readNatArray
  return Json.mkObj [
    ("target", value0),
    ("values", value1),
    ("credits", value2)]

private def readCtorAlt : Parser Json := do
  let value0 ← readCtorId
  let value1 ← readEdge
  return Json.mkObj [
    ("cid", value0),
    ("edge", value1)]

private def readNatPeel : Parser Json := do
  let value0 ← readEdge
  let value1 ← readEdge
  return Json.mkObj [
    ("zero", value0),
    ("succ", value1)]

private def readPeelOption : Parser Json := do
  match ← readByte with
  | 0 =>
      return Json.arr #[toJson "none"]
  | 1 =>
      let value0 ← readNatPeel
      return Json.arr #[toJson "some", value0]
  | _ => throw "invalid IxIR2 peelOption tag"

private def readCtorAltArray : Parser Json := readArray readCtorAlt

private def readTerminator : Parser Json := do
  match ← readByte with
  | 0 =>
      let value0 ← readEdge
      return Json.arr #[toJson "jump", value0]
  | 1 =>
      let value0 ← readAtom
      let value1 ← readCtorAltArray
      let value2 ← readPeelOption
      return Json.arr #[toJson "switchValue", value0, value1, value2]
  | 2 =>
      let value0 ← readNaturalJson
      let value1 ← readEdge
      let value2 ← readEdge
      return Json.arr #[toJson "branchCredit", value0, value1, value2]
  | 3 =>
      let value0 ← readAtom
      return Json.arr #[toJson "ret", value0]
  | 4 =>
      let value0 ← readAddressJson
      let value1 ← readAtomArray
      return Json.arr #[toJson "tailCall", value0, value1]
  | 5 =>
      let value0 ← readAtomArray
      return Json.arr #[toJson "tailCallSelf", value0]
  | _ => throw "invalid IxIR2 terminator tag"

private def readValueCapArray : Parser Json := readArray readValueCap

private def readCreditCapArray : Parser Json := readArray readCreditCap

private def readInstrArray : Parser Json := readArray readInstr

private def readBlock : Parser Json := do
  let value0 ← readValueCapArray
  let value1 ← readCreditCapArray
  let value2 ← readInstrArray
  let value3 ← readTerminator
  return Json.mkObj [
    ("valueParams", value0),
    ("creditParams", value1),
    ("instructions", value2),
    ("terminator", value3)]

private def readBlockArray : Parser Json := readArray readBlock

private def readFunction : Parser Json := do
  let value0 ← readSignature
  let value1 ← readBlockArray
  return Json.mkObj [
    ("signature", value0),
    ("blocks", value1)]

private def readDecl : Parser Json := do
  match ← readByte with
  | 0 =>
      let value0 ← readFunction
      return Json.arr #[toJson "fn", value0]
  | 1 =>
      let value0 ← readNaturalJson
      return Json.arr #[toJson "extern", value0]
  | _ => throw "invalid IxIR2 decl tag"

private def readDeclEntry : Parser Json := do
  let value0 ← readAddressJson
  let value1 ← readDecl
  return Json.mkObj [
    ("address", value0),
    ("declaration", value1)]

private def readDeclEntryList : Parser Json := readArray readDeclEntry

private def readProgram : Parser Json := do
  let value0 ← readDeclEntryList
  let value1 ← readFunction
  return Json.mkObj [
    ("declarations", value0),
    ("main", value1)]

private def readCreditPolicy : Parser Json := do
  match ← readByte with
  | 0 =>
      return Json.arr #[toJson "callLocalV0"]
  | 1 =>
      return Json.arr #[toJson "suspendedCallsV1"]
  | _ => throw "invalid IxIR2 creditPolicy tag"

private def readOwner : Parser Json := do
  match ← readByte with
  | 0 =>
      return Json.arr #[toJson "main"]
  | 1 =>
      let value0 ← readAddressJson
      return Json.arr #[toJson "declaration", value0]
  | _ => throw "invalid IxIR2 owner tag"

private def readScalarLeaf : Parser Json := do
  let value0 ← readOwner
  let value1 ← readNaturalJson
  let value2 ← readNaturalJson
  let value3 ← readCtorId
  return Json.mkObj [
    ("owner", value0),
    ("block", value1),
    ("value", value2),
    ("cid", value3)]

private def readStrArray : Parser Json := readArray readStringJson

private def readPolicy : Parser Json := do
  let value0 ← readStringJson
  let value1 ← readStringJson
  let value2 ← readStringJson
  let value3 ← readStrArray
  let value4 ← readStringJson
  let value5 ← readCreditPolicy
  let value6 ← readBoolJson
  return Json.mkObj [
    ("semantics", value0),
    ("validator", value1),
    ("lowering", value2),
    ("passes", value3),
    ("layout", value4),
    ("credits", value5),
    ("allowExtern", value6)]

private def readDependency : Parser Json := do
  let value0 ← readStringJson
  let value1 ← readAddressJson
  return Json.mkObj [
    ("role", value0),
    ("root", value1)]

private def readLayout : Parser Json := do
  let value0 ← readAddressJson
  let value1 ← readBlobJson
  return Json.mkObj [
    ("identity", value0),
    ("preimage", value1)]

private def readSchema : Parser Json := do
  let value0 ← readOwnedJson
  let value1 ← readCtorId
  let value2 ← readCtorSchema
  return Json.mkObj [
    ("world", value0),
    ("constructor", value1),
    ("definition", value2)]

private def readDependencyArray : Parser Json := readArray readDependency

private def readLayoutArray : Parser Json := readArray readLayout

private def readSchemaArray : Parser Json := readArray readSchema

private def readScalarLeafArray : Parser Json := readArray readScalarLeaf

private def readArtifact : Parser Json := do
  let value0 ← readPolicy
  let value1 ← readDependencyArray
  let value2 ← readLayoutArray
  let value3 ← readSchemaArray
  let value4 ← readScalarLeafArray
  let value5 ← readProgram
  return Json.mkObj [
    ("policy", value0),
    ("dependencies", value1),
    ("layouts", value2),
    ("schemas", value3),
    ("scalarLeaves", value4),
    ("program", value5)]

/-- Strict independent reader with consumer-selected limits. -/
def decodeWith (limits : Limits) (bytes : ByteArray) : Except String Json := do
  if bytes.size > limits.maxBytes then throw "IxIR2 input byte limit"
  let framing := "compilatrix/ixir2/snapshot/1".toUTF8.push 0
  let reader : Parser Json := do
    if (← readBytes framing.size) != framing then throw "wrong IxIR2 snapshot domain"
    readArtifact
  let (artifact, cursor) ← reader.run { bytes, limits }
  if cursor.position != bytes.size then throw "trailing IxIR2 snapshot bytes"
  return artifact

def decode (bytes : ByteArray) : Except String Json := decodeWith {} bytes

def root (bytes : ByteArray) : String := (Address.blake3 bytes).toHex

open Compilatrix.Tools.Check

private def number (value : Json) (key : String) : IO Nat := do nat (← field value key)
private def boolean (value : Json) (key : String) : IO Bool := checked (value.getObjValAs? Bool key)

private def functions (program : Json) : IO (Array Json) := do
  let mut result := #[← field program "main"]
  for row in ← arrField program "declarations" do
    let declaration ← arrField row "declaration"
    if (← string declaration[0]!) == "fn" then result := result.push declaration[1]!
  return result

private def inspectStats (program stats : Json) : IO Unit := do
  let definitions ← functions program
  let mut blocks := 0
  let mut instructions := 0
  let mut edges := 0
  for fn in definitions do
    for block in ← arrField fn "blocks" do
      blocks := blocks + 1
      instructions := instructions + (← arrField block "instructions").size
      let term ← arrField block "terminator"
      match ← string term[0]! with
      | "jump" => edges := edges + 1
      | "branchCredit" => edges := edges + 2
      | "switchValue" =>
          let peel ← array term[3]!
          edges := edges + (← array term[2]!).size + (if (← string peel[0]!) == "some" then 2 else 0)
      | _ => pure ()
  need ((← number stats "declarations") == (← arrField program "declarations").size) "declaration count mismatch"
  need ((← number stats "functions") == definitions.size) "function count mismatch"
  need ((← number stats "blocks") == blocks) "block count mismatch"
  need ((← number stats "instructions") == instructions) "instruction count mismatch"
  need ((← number stats "edges") == edges) "edge count mismatch"

private def natValue (value : Json) : IO Nat := do
  number (← field (← field (← field value "lit") "l") "nat") "n"

private def node (nodes : Array Json) (value : Json) : IO Json := do
  let location ← number (← field value "loc") "l"
  need (location < nodes.size && nodes[location]! != Json.null) "result points outside the live heap"
  let box := nodes[location]!
  need ((← strField box "world") == "shared" && (← number box "rc") > 0) "result node ownership mismatch"
  field (← field box "node") "ctorN"

private def listValue (nodes : Array Json) (nilId consId : Json) : Nat → Json → IO (Array Nat)
  | 0, _ => throw (IO.userError "result list exceeds its expected length")
  | fuel + 1, value => do
      let cell ← node nodes value
      let cid ← field cell "cid"
      let fields ← arrField cell "fields"
      if cid == nilId then
        need fields.isEmpty "nil has payload fields"
        return #[]
      need (cid == consId && fields.size == 2) "result list constructor mismatch"
      let head ← natValue fields[0]!
      return #[head] ++ (← listValue nodes nilId consId fuel fields[1]!)

private def schemaId (artifact : Json) (tag fields : Nat) : IO Json := do
  let mut candidates := #[]
  for schema in ← arrField artifact "schemas" do
    let cid ← field schema "constructor"
    let definition ← field schema "definition"
    if (← strField schema "world") == "shared" && (← number cid "cidx") == tag &&
        (← arrField definition "fields").size == fields then
      candidates := candidates.push cid
  need (candidates.size == 1) "source fixture constructor is ambiguous"
  return candidates[0]!

private def inspectExecution (row artifact execution : Json) : IO Unit := do
  let original ← field execution "original"
  let decoded ← field execution "decoded"
  need (original == decoded) "physical execution changed after decoding"
  let store ← field decoded "store"
  let heap ← field store "heap"
  let nodes ← arrField heap "nodes"
  let released ← field execution "reclaimed"
  let releasedHeap ← field released "heap"
  let releasedNodes ← arrField releasedHeap "nodes"
  let live := nodes.filter (· != Json.null) |>.size
  need (nodes.size == (← number heap "allocs") && live + (← number heap "frees") == nodes.size)
    "terminal heap accounting mismatch"
  need (releasedNodes.size == nodes.size && releasedNodes.all (· == Json.null) &&
    (← number releasedHeap "allocs") == nodes.size && (← number releasedHeap "frees") == nodes.size)
    "incomplete decoded-result reclamation"
  need ((← number releasedHeap "reuses") == (← number heap "reuses") &&
    (← number releasedHeap "rcops") ≥ (← number heap "rcops")) "release changed allocation history"
  for key in ["resetAttempts", "hotResets", "coldResets", "reusedPayloadUnits", "peakLiveNodes"] do
    need ((← field released key) == (← field store key)) "release changed resource observations"
  let source ← field row "source"
  let value ← field decoded "value"
  let reported ← field execution "source_value"
  match ← strField source "family" with
  | "borrowed-call" =>
      let expected ← number source "number"
      need ((← natValue value) == expected && reported == toJson expected) "borrowed source result mismatch"
  | "recursive-map" =>
      let inputs ← (← arrField source "values").mapM nat
      let replacement ← number source "replacement"
      let expected := Array.replicate inputs.size replacement
      let nilId ← schemaId artifact 0 0
      let consId ← schemaId artifact 1 2
      if ← boolean source "aliased" then
        let pair ← node nodes value
        need ((← field pair "cid") == (← schemaId artifact 0 2)) "result pair constructor mismatch"
        let fields ← arrField pair "fields"
        need (fields.size == 2) "result pair arity mismatch"
        let mapped ← listValue nodes nilId consId (inputs.size + 1) fields[0]!
        let retained ← listValue nodes nilId consId (inputs.size + 1) fields[1]!
        let suffix := inputs.toList.drop (← number source "unique_prefix") |>.toArray
        need (mapped == expected && retained == suffix) "decoded map/pair source result mismatch"
        need (reported == Json.mkObj [("pair", Json.mkObj [("mapped", toJson expected), ("retained", toJson suffix)])])
          "reported map/pair source result mismatch"
      else
        need ((← listValue nodes nilId consId (inputs.size + 1) value) == expected)
          "decoded map source result mismatch"
        need (reported == Json.mkObj [("list", Json.mkObj [("values", toJson expected)])])
          "reported map source result mismatch"
  | _ => throw (IO.userError "unknown source fixture family")

def inspectCase (row : Json) (bytes : ByteArray) (snapshot : Json) : IO Unit := do
  need ((← strField snapshot "format") == "ixir2-snapshot/1") "wrong snapshot view format"
  need ((← field snapshot "summary") == row) "snapshot summary mismatch"
  need (bytes.size == (← number row "bytes")) "snapshot byte count mismatch"
  need (root bytes == (← strField row "root")) "snapshot root mismatch"
  let artifact ← checked (decode bytes)
  need (artifact == (← field snapshot "artifact")) "complete decoded snapshot differs from its view"
  let validation ← field snapshot "validation"
  if ← boolean row "checked" then
    need ((← strField validation "status") == "checked") "missing ownership validation"
    inspectStats (← field artifact "program") (← field validation "stats")
    for layout in ← arrField artifact "layouts" do
      let preimage ← checked (unhex (← strField layout "preimage"))
      need (root preimage == (← strField layout "identity")) "layout preimage mismatch"
  else need ((← strField validation "status") == "syntax-only") "wrong syntax-vector validation scope"
  if ← boolean row "execution" then
    inspectExecution row artifact (← field snapshot "execution")
  else need ((← field snapshot "execution") == Json.null) "unexpected execution claim"

def inspectReport (expected report : Json) : IO Unit := do
  need (report == expected) "reviewed IxIR2 artifact matrix drifted"
  need ((← strField report "format") == "ixir2-snapshot/1") "wrong report format"

def regressionChecks (row : Json) (bytes : ByteArray) (snapshot report : Json) : IO Nat := do
  let mut count := 0
  for (name, path, replacement) in [
      ("policy", ["artifact", "policy", "credits"], toJson ["callLocalV0"]),
      ("passes", ["artifact", "policy", "passes"], Json.arr #[]),
      ("dependencies", ["artifact", "dependencies"], Json.arr #[]),
      ("schemas", ["artifact", "schemas"], Json.arr #[]),
      ("layouts", ["artifact", "layouts"], Json.arr #[]),
      ("scalar facts", ["artifact", "scalarLeaves"], Json.arr #[Json.null]),
      ("declarations", ["artifact", "program", "declarations"], Json.arr #[]),
      ("blocks", ["artifact", "program", "main", "blocks"], Json.arr #[])] do
    let changed ← UniqueCheck.replaceAt snapshot path replacement
    UniqueCheck.rejects name "complete decoded snapshot" (inspectCase row bytes changed)
    count := count + 1
  for (name, path, replacement, fragment) in [
      ("execution", ["execution", "decoded", "value"], Json.null, "physical execution"),
      ("release slots", ["execution", "reclaimed", "heap", "nodes"], Json.arr #[], "reclamation"),
      ("release frees", ["execution", "reclaimed", "heap", "frees"], toJson (0 : Nat), "reclamation"),
      ("source value", ["execution", "source_value"], Json.null, "source result"),
      ("validator counts", ["validation", "stats", "instructions"], toJson (0 : Nat), "instruction count")] do
    let changed ← UniqueCheck.replaceAt snapshot path replacement
    UniqueCheck.rejects name fragment (inspectCase row bytes changed)
    count := count + 1
  let changedBytes := bytes.set! (bytes.size - 1) (bytes[bytes.size - 1]! ^^^ 1)
  UniqueCheck.rejects "changed bytes" "root" (inspectCase row changedBytes snapshot)
  let changedRows ← (← arrField report "cases").mapM fun old =>
    if old == row then UniqueCheck.replaceAt old ["root"] (toJson (root changedBytes)) else pure old
  let changedReport ← UniqueCheck.replaceAt report ["cases"] (Json.arr changedRows)
  UniqueCheck.rejects "identical producer corruption" "reviewed" (inspectReport report changedReport)
  return count + 2

end Compilatrix.Tools.IxIR2Check
