import Compilatrix.IxIR2.Wire
import Lean

/-! Human-readable, complete snapshot views for independent artifact checks.
JSON is diagnostic; the versioned binary snapshot alone defines identity. -/

namespace Compilatrix.IxIR2.Wire

open Lean Compilatrix.Ixon

def bytesHex (value : ByteArray) : String :=
  value.data.foldl (fun output byte => output ++ hexDigitRepr (byte.toNat / 16) ++
    hexDigitRepr (byte.toNat % 16)) ""

def blobJson (value : ByteArray) : Json := toJson (bytesHex value)
def addressJson (value : Address) : Json := toJson value.toHex
def ownedJson : Owned → Json | .unique => toJson "unique" | .shared => toJson "shared"

def literalJson : IxIR0.Literal → Json
  | .nat v0 => Json.arr #[toJson "nat", toJson v0]
  | .str v0 => Json.arr #[toJson "str", toJson v0]

def atomJson : Atom → Json
  | .reg v0 => Json.arr #[toJson "reg", toJson v0]
  | .lit v0 => Json.arr #[toJson "lit", literalJson v0]
  | .erased => Json.arr #[toJson "erased"]

def paramPassingJson : ParamPassing → Json
  | .owned => Json.arr #[toJson "owned"]
  | .borrowed => Json.arr #[toJson "borrowed"]

def paramJson (value : Param) : Json :=
  Json.mkObj [
    ("world", ownedJson value.world),
    ("passing", paramPassingJson value.passing)]

def paramArrayJson (value : Array Param) : Json := Json.arr (value.map paramJson)

def signatureJson (value : Signature) : Json :=
  Json.mkObj [
    ("params", paramArrayJson value.params),
    ("result", ownedJson value.result),
    ("papSafe", toJson value.papSafe)]

def borrowLenderJson : BorrowLender → Json
  | .caller => Json.arr #[toJson "caller"]
  | .value v0 => Json.arr #[toJson "value", toJson v0]

def valueCapJson : ValueCap → Json
  | .scalar => Json.arr #[toJson "scalar"]
  | .owned v0 => Json.arr #[toJson "owned", ownedJson v0]
  | .borrowed v0 v1 => Json.arr #[toJson "borrowed", ownedJson v0, borrowLenderJson v1]

def creditCapJson : CreditCap → Json
  | .required v0 => Json.arr #[toJson "required", addressJson v0]
  | .optional v0 => Json.arr #[toJson "optional", addressJson v0]

def ctorIdJson (value : CtorId) : Json :=
  Json.mkObj [
    ("block", addressJson value.block),
    ("indIdx", toJson value.indIdx),
    ("cidx", toJson value.cidx)]

def ownedArrayJson (value : Array Owned) : Json := Json.arr (value.map ownedJson)

def ctorSchemaJson (value : CtorSchema) : Json :=
  Json.mkObj [
    ("layout", addressJson value.layout),
    ("fields", ownedArrayJson value.fields)]

def atomArrayJson (value : Array Atom) : Json := Json.arr (value.map atomJson)

def instrJson : Instr → Json
  | .move v0 => Json.arr #[toJson "move", atomJson v0]
  | .alloc v0 v1 v2 => Json.arr #[toJson "alloc", ownedJson v0, ctorIdJson v1, atomArrayJson v2]
  | .allocWith v0 v1 v2 v3 => Json.arr #[toJson "allocWith", toJson v0, ownedJson v1, ctorIdJson v2, atomArrayJson v3]
  | .discardCredit v0 => Json.arr #[toJson "discardCredit", toJson v0]
  | .takeUnique v0 v1 => Json.arr #[toJson "takeUnique", atomJson v0, ctorIdJson v1]
  | .resetShared v0 v1 => Json.arr #[toJson "resetShared", atomJson v0, ctorIdJson v1]
  | .retainShared v0 => Json.arr #[toJson "retainShared", atomJson v0]
  | .releaseShared v0 => Json.arr #[toJson "releaseShared", atomJson v0]
  | .dropUnique v0 => Json.arr #[toJson "dropUnique", atomJson v0]
  | .freeUnique v0 v1 => Json.arr #[toJson "freeUnique", atomJson v0, ctorIdJson v1]
  | .fetch v0 v1 v2 => Json.arr #[toJson "fetch", atomJson v0, ctorIdJson v1, toJson v2]
  | .call v0 v1 => Json.arr #[toJson "call", addressJson v0, atomArrayJson v1]
  | .callSelf v0 => Json.arr #[toJson "callSelf", atomArrayJson v0]
  | .papp v0 v1 => Json.arr #[toJson "papp", addressJson v0, atomArrayJson v1]
  | .apply v0 v1 => Json.arr #[toJson "apply", atomJson v0, atomArrayJson v1]
  | .extern v0 v1 => Json.arr #[toJson "extern", addressJson v0, atomArrayJson v1]

def natArrayJson (value : Array Nat) : Json := Json.arr (value.map toJson)

def edgeJson (value : Edge) : Json :=
  Json.mkObj [
    ("target", toJson value.target),
    ("values", atomArrayJson value.values),
    ("credits", natArrayJson value.credits)]

def ctorAltJson (value : CtorAlt) : Json :=
  Json.mkObj [
    ("cid", ctorIdJson value.cid),
    ("edge", edgeJson value.edge)]

def natPeelJson (value : NatPeel) : Json :=
  Json.mkObj [
    ("zero", edgeJson value.zero),
    ("succ", edgeJson value.succ)]

def peelOptionJson : Option NatPeel → Json
  | .none => Json.arr #[toJson "none"]
  | .some v0 => Json.arr #[toJson "some", natPeelJson v0]

def ctorAltArrayJson (value : Array CtorAlt) : Json := Json.arr (value.map ctorAltJson)

def terminatorJson : Terminator → Json
  | .jump v0 => Json.arr #[toJson "jump", edgeJson v0]
  | .switchValue v0 v1 v2 => Json.arr #[toJson "switchValue", atomJson v0, ctorAltArrayJson v1, peelOptionJson v2]
  | .branchCredit v0 v1 v2 => Json.arr #[toJson "branchCredit", toJson v0, edgeJson v1, edgeJson v2]
  | .ret v0 => Json.arr #[toJson "ret", atomJson v0]
  | .tailCall v0 v1 => Json.arr #[toJson "tailCall", addressJson v0, atomArrayJson v1]
  | .tailCallSelf v0 => Json.arr #[toJson "tailCallSelf", atomArrayJson v0]

def valueCapArrayJson (value : Array ValueCap) : Json := Json.arr (value.map valueCapJson)

def creditCapArrayJson (value : Array CreditCap) : Json := Json.arr (value.map creditCapJson)

def instrArrayJson (value : Array Instr) : Json := Json.arr (value.map instrJson)

def blockJson (value : Block) : Json :=
  Json.mkObj [
    ("valueParams", valueCapArrayJson value.valueParams),
    ("creditParams", creditCapArrayJson value.creditParams),
    ("instructions", instrArrayJson value.instructions),
    ("terminator", terminatorJson value.terminator)]

def blockArrayJson (value : Array Block) : Json := Json.arr (value.map blockJson)

def functionJson (value : Function) : Json :=
  Json.mkObj [
    ("signature", signatureJson value.signature),
    ("blocks", blockArrayJson value.blocks)]

def declJson : Decl → Json
  | .fn v0 => Json.arr #[toJson "fn", functionJson v0]
  | .extern v0 => Json.arr #[toJson "extern", toJson v0]

def declEntryJson (value : Address × Decl) : Json :=
  Json.mkObj [
    ("address", addressJson value.1),
    ("declaration", declJson value.2)]

def declEntryListJson (value : List (Address × Decl)) : Json := Json.arr (value.map declEntryJson).toArray

def programJson (value : Program) : Json :=
  Json.mkObj [
    ("declarations", declEntryListJson value.declarations),
    ("main", functionJson value.main)]

def creditPolicyJson : CreditPolicy → Json
  | .callLocalV0 => Json.arr #[toJson "callLocalV0"]
  | .suspendedCallsV1 => Json.arr #[toJson "suspendedCallsV1"]

def ownerJson : Validate.Owner → Json
  | .main => Json.arr #[toJson "main"]
  | .declaration v0 => Json.arr #[toJson "declaration", addressJson v0]

def scalarLeafJson (value : Validate.ScalarLeafFact) : Json :=
  Json.mkObj [
    ("owner", ownerJson value.owner),
    ("block", toJson value.block),
    ("value", toJson value.value),
    ("cid", ctorIdJson value.cid)]

def strArrayJson (value : Array String) : Json := Json.arr (value.map toJson)

def policyJson (value : Policy) : Json :=
  Json.mkObj [
    ("semantics", toJson value.semantics),
    ("validator", toJson value.validator),
    ("lowering", toJson value.lowering),
    ("passes", strArrayJson value.passes),
    ("layout", toJson value.layout),
    ("credits", creditPolicyJson value.credits),
    ("allowExtern", toJson value.allowExtern)]

def dependencyJson (value : Dependency) : Json :=
  Json.mkObj [
    ("role", toJson value.role),
    ("root", addressJson value.root)]

def layoutJson (value : Layout) : Json :=
  Json.mkObj [
    ("identity", addressJson value.identity),
    ("preimage", blobJson value.preimage)]

def schemaJson (value : Schema) : Json :=
  Json.mkObj [
    ("world", ownedJson value.world),
    ("constructor", ctorIdJson value.constructor),
    ("definition", ctorSchemaJson value.definition)]

def dependencyArrayJson (value : Array Dependency) : Json := Json.arr (value.map dependencyJson)

def layoutArrayJson (value : Array Layout) : Json := Json.arr (value.map layoutJson)

def schemaArrayJson (value : Array Schema) : Json := Json.arr (value.map schemaJson)

def scalarLeafArrayJson (value : Array Validate.ScalarLeafFact) : Json := Json.arr (value.map scalarLeafJson)

def artifactJson (value : Artifact) : Json :=
  Json.mkObj [
    ("policy", policyJson value.policy),
    ("dependencies", dependencyArrayJson value.dependencies),
    ("layouts", layoutArrayJson value.layouts),
    ("schemas", schemaArrayJson value.schemas),
    ("scalarLeaves", scalarLeafArrayJson value.scalarLeaves),
    ("program", programJson value.program)]

end Compilatrix.IxIR2.Wire
