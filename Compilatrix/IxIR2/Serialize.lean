import Compilatrix.IxIR2.Wire
import Compilatrix.IxIR.Encoding

/-!
# Canonical IxIR₂ snapshot bytes, version 1

All sum tags and product fields below are normative. Arrays, declaration
rows and blocks preserve their given order. Hashing commits to the actual
IxIR₂ bodies and finite environment, including provenance and policy inputs.
-/

namespace Compilatrix.IxIR2.Wire

open Compilatrix.Ixon (Address Owned)
open Compilatrix.IxIR

def ownedBytes (value : Owned) : ByteArray := Encoding.tag value.toBits

def literalBytes : IxIR0.Literal → ByteArray
  | .nat v0 => Encoding.tag 0 ++ Encoding.nat v0
  | .str v0 => Encoding.tag 1 ++ Encoding.string v0

def atomBytes : Atom → ByteArray
  | .reg v0 => Encoding.tag 0 ++ Encoding.nat v0
  | .lit v0 => Encoding.tag 1 ++ literalBytes v0
  | .erased => Encoding.tag 2

def paramPassingBytes : ParamPassing → ByteArray
  | .owned => Encoding.tag 0
  | .borrowed => Encoding.tag 1

def paramBytes (value : Param) : ByteArray :=
  ownedBytes value.world ++
    paramPassingBytes value.passing

def paramArrayBytes (value : Array Param) : ByteArray :=
  Encoding.array paramBytes value

def signatureBytes (value : Signature) : ByteArray :=
  paramArrayBytes value.params ++
    ownedBytes value.result ++
    Encoding.bool value.papSafe

def borrowLenderBytes : BorrowLender → ByteArray
  | .caller => Encoding.tag 0
  | .value v0 => Encoding.tag 1 ++ Encoding.nat v0

def valueCapBytes : ValueCap → ByteArray
  | .scalar => Encoding.tag 0
  | .owned v0 => Encoding.tag 1 ++ ownedBytes v0
  | .borrowed v0 v1 => Encoding.tag 2 ++ ownedBytes v0 ++ borrowLenderBytes v1

def creditCapBytes : CreditCap → ByteArray
  | .required v0 => Encoding.tag 0 ++ Encoding.address v0
  | .optional v0 => Encoding.tag 1 ++ Encoding.address v0

def ctorIdBytes (value : CtorId) : ByteArray :=
  Encoding.address value.block ++
    Encoding.nat value.indIdx ++
    Encoding.nat value.cidx

def ownedArrayBytes (value : Array Owned) : ByteArray :=
  Encoding.array ownedBytes value

def ctorSchemaBytes (value : CtorSchema) : ByteArray :=
  Encoding.address value.layout ++
    ownedArrayBytes value.fields

def atomArrayBytes (value : Array Atom) : ByteArray :=
  Encoding.array atomBytes value

def instrBytes : Instr → ByteArray
  | .move v0 => Encoding.tag 0 ++ atomBytes v0
  | .alloc v0 v1 v2 => Encoding.tag 1 ++ ownedBytes v0 ++ ctorIdBytes v1 ++ atomArrayBytes v2
  | .allocWith v0 v1 v2 v3 => Encoding.tag 2 ++ Encoding.nat v0 ++ ownedBytes v1 ++ ctorIdBytes v2 ++ atomArrayBytes v3
  | .discardCredit v0 => Encoding.tag 3 ++ Encoding.nat v0
  | .takeUnique v0 v1 => Encoding.tag 4 ++ atomBytes v0 ++ ctorIdBytes v1
  | .resetShared v0 v1 => Encoding.tag 5 ++ atomBytes v0 ++ ctorIdBytes v1
  | .retainShared v0 => Encoding.tag 6 ++ atomBytes v0
  | .releaseShared v0 => Encoding.tag 7 ++ atomBytes v0
  | .dropUnique v0 => Encoding.tag 8 ++ atomBytes v0
  | .freeUnique v0 v1 => Encoding.tag 9 ++ atomBytes v0 ++ ctorIdBytes v1
  | .fetch v0 v1 v2 => Encoding.tag 10 ++ atomBytes v0 ++ ctorIdBytes v1 ++ Encoding.nat v2
  | .call v0 v1 => Encoding.tag 11 ++ Encoding.address v0 ++ atomArrayBytes v1
  | .callSelf v0 => Encoding.tag 12 ++ atomArrayBytes v0
  | .papp v0 v1 => Encoding.tag 13 ++ Encoding.address v0 ++ atomArrayBytes v1
  | .apply v0 v1 => Encoding.tag 14 ++ atomBytes v0 ++ atomArrayBytes v1
  | .extern v0 v1 => Encoding.tag 15 ++ Encoding.address v0 ++ atomArrayBytes v1

def natArrayBytes (value : Array Nat) : ByteArray :=
  Encoding.array Encoding.nat value

def edgeBytes (value : Edge) : ByteArray :=
  Encoding.nat value.target ++
    atomArrayBytes value.values ++
    natArrayBytes value.credits

def ctorAltBytes (value : CtorAlt) : ByteArray :=
  ctorIdBytes value.cid ++
    edgeBytes value.edge

def natPeelBytes (value : NatPeel) : ByteArray :=
  edgeBytes value.zero ++
    edgeBytes value.succ

def peelOptionBytes : Option NatPeel → ByteArray
  | .none => Encoding.tag 0
  | .some v0 => Encoding.tag 1 ++ natPeelBytes v0

def ctorAltArrayBytes (value : Array CtorAlt) : ByteArray :=
  Encoding.array ctorAltBytes value

def terminatorBytes : Terminator → ByteArray
  | .jump v0 => Encoding.tag 0 ++ edgeBytes v0
  | .switchValue v0 v1 v2 => Encoding.tag 1 ++ atomBytes v0 ++ ctorAltArrayBytes v1 ++ peelOptionBytes v2
  | .branchCredit v0 v1 v2 => Encoding.tag 2 ++ Encoding.nat v0 ++ edgeBytes v1 ++ edgeBytes v2
  | .ret v0 => Encoding.tag 3 ++ atomBytes v0
  | .tailCall v0 v1 => Encoding.tag 4 ++ Encoding.address v0 ++ atomArrayBytes v1
  | .tailCallSelf v0 => Encoding.tag 5 ++ atomArrayBytes v0

def valueCapArrayBytes (value : Array ValueCap) : ByteArray :=
  Encoding.array valueCapBytes value

def creditCapArrayBytes (value : Array CreditCap) : ByteArray :=
  Encoding.array creditCapBytes value

def instrArrayBytes (value : Array Instr) : ByteArray :=
  Encoding.array instrBytes value

def blockBytes (value : Block) : ByteArray :=
  valueCapArrayBytes value.valueParams ++
    creditCapArrayBytes value.creditParams ++
    instrArrayBytes value.instructions ++
    terminatorBytes value.terminator

def blockArrayBytes (value : Array Block) : ByteArray :=
  Encoding.array blockBytes value

def functionBytes (value : Function) : ByteArray :=
  signatureBytes value.signature ++
    blockArrayBytes value.blocks

def declBytes : Decl → ByteArray
  | .fn v0 => Encoding.tag 0 ++ functionBytes v0
  | .extern v0 => Encoding.tag 1 ++ Encoding.nat v0

def declEntryBytes (value : Address × Decl) : ByteArray :=
  Encoding.address value.1 ++
    declBytes value.2

def declEntryListBytes (value : List (Address × Decl)) : ByteArray :=
  Encoding.list declEntryBytes value

def programBytes (value : Program) : ByteArray :=
  declEntryListBytes value.declarations ++
    functionBytes value.main

def creditPolicyBytes : CreditPolicy → ByteArray
  | .callLocalV0 => Encoding.tag 0
  | .suspendedCallsV1 => Encoding.tag 1

def ownerBytes : Validate.Owner → ByteArray
  | .main => Encoding.tag 0
  | .declaration v0 => Encoding.tag 1 ++ Encoding.address v0

def scalarLeafBytes (value : Validate.ScalarLeafFact) : ByteArray :=
  ownerBytes value.owner ++
    Encoding.nat value.block ++
    Encoding.nat value.value ++
    ctorIdBytes value.cid

def strArrayBytes (value : Array String) : ByteArray :=
  Encoding.array Encoding.string value

def policyBytes (value : Policy) : ByteArray :=
  Encoding.string value.semantics ++
    Encoding.string value.validator ++
    Encoding.string value.lowering ++
    strArrayBytes value.passes ++
    Encoding.string value.layout ++
    creditPolicyBytes value.credits ++
    Encoding.bool value.allowExtern

def dependencyBytes (value : Dependency) : ByteArray :=
  Encoding.string value.role ++
    Encoding.address value.root

def layoutBytes (value : Layout) : ByteArray :=
  Encoding.address value.identity ++
    Encoding.blob value.preimage

def schemaBytes (value : Schema) : ByteArray :=
  ownedBytes value.world ++
    ctorIdBytes value.constructor ++
    ctorSchemaBytes value.definition

def dependencyArrayBytes (value : Array Dependency) : ByteArray :=
  Encoding.array dependencyBytes value

def layoutArrayBytes (value : Array Layout) : ByteArray :=
  Encoding.array layoutBytes value

def schemaArrayBytes (value : Array Schema) : ByteArray :=
  Encoding.array schemaBytes value

def scalarLeafArrayBytes (value : Array Validate.ScalarLeafFact) : ByteArray :=
  Encoding.array scalarLeafBytes value

def artifactBytes (value : Artifact) : ByteArray :=
  policyBytes value.policy ++
    dependencyArrayBytes value.dependencies ++
    layoutArrayBytes value.layouts ++
    schemaArrayBytes value.schemas ++
    scalarLeafArrayBytes value.scalarLeaves ++
    programBytes value.program

def Artifact.addressDomain : ByteArray :=
  Encoding.domain "compilatrix/ixir2/snapshot/1" ++ Encoding.tag 0

/-- Public format name, separate from the in-memory v0 syntax and credit policies. -/
def formatId : String := "ixir2-snapshot/1"

def Artifact.preimage (artifact : Artifact) : ByteArray :=
  Artifact.addressDomain ++ artifactBytes artifact

def Artifact.address (artifact : Artifact) : Address :=
  Address.blake3 artifact.preimage

theorem Artifact.address_eq_iff_preimage_eq (left right : Artifact)
    (collision : Address.Blake3NoCollision left.preimage right.preimage) :
    left.address = right.address ↔ left.preimage = right.preimage :=
  ⟨collision, fun equal => congrArg Address.blake3 equal⟩

end Compilatrix.IxIR2.Wire
