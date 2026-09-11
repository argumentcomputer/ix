import Ix.Compiler.IxIR1.Decode
import Ix.Compiler.IxIR1.Readdress

/-!
# Cycle-safe IxIR₁ block identities

Ordinary IxIR₁ declaration hashes can be computed only after every addressed
dependency is known.  A source-backed function and one of its generated
closures may instead form a genuine address cycle.  This module gives such a
strongly connected component a finite canonical spelling: edges within the
ordered block use local indices, external edges retain full addresses, the
symbolic block is hashed once, and executable member keys are independently
derived from that block identity and member index.

The module is deliberately independent of SCC discovery.  It is the checked
artifact boundary consumed by a later whole-program pass: strict canonical
decoding, scope validation, collision checks, materialization, and an erased
semantic audit.  Native BLAKE3 calls remain confined to compiled producers,
ingress, and tests.
-/

namespace Ix.Compiler.IxIR1

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR

namespace MutualBlock

/-! ## Symbolic block syntax -/

/-- An address-bearing edge in a canonical block. -/
inductive Ref where
  | local (index : Nat)
  | external (address : Address)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Constructor identity with a symbolic block edge. -/
structure CtorId where
  block : Ref
  indIdx : Nat
  cidx : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- IxIR₁ operations with every static address represented symbolically. -/
inductive Op where
  | pure (atom : Atom)
  | alloc (world : Owned) (cid : CtorId) (args : Array Atom)
  | reuse (target : Atom) (cid : CtorId) (args : Array Atom)
  | free (target : Atom)
  | dup (target : Atom)
  | drop (target : Atom)
  | dropU (target : Atom)
  | fetch (target : Atom) (field : Nat)
  | call (function : Ref) (args : Array Atom)
  | callSelf (args : Array Atom)
  | papp (function : Ref) (args : Array Atom)
  | apply (function : Atom) (args : Array Atom)
  | extern (function : Ref) (args : Array Atom)

mutual

/-- A symbolic case alternative. -/
inductive Alt where
  | mk (cidx fields : Nat) (body : Code)

/-- Symbolic IxIR₁ code. -/
inductive Code where
  | ret (atom : Atom)
  | letOp (operation : Op) (rest : Code)
  | case (scrutinee : Atom) (peelNat : Bool) (alternatives : Array Alt)

end

/-- A saturated symbolic function. -/
structure FnDef where
  arity : Nat
  result : Owned
  papSafe : Bool
  body : Code

/-- A declaration in a symbolic IxIR₁ block. -/
inductive Decl where
  | fn (definition : FnDef)
  | extern (arity : Nat)

/-! ## Temporary-name abstraction and materialization -/

/-- First zero-based position of an address in an ordered key list. -/
def localIndex? (keys : List Address) (address : Address) : Option Nat :=
  let rec loop : Nat → List Address → Option Nat
    | _, [] => none
    | index, key :: rest =>
        if key == address then some index else loop (index + 1) rest
  loop 0 keys

namespace Ref

def abstract (keys : List Address) (address : Address) : Ref :=
  match localIndex? keys address with
  | some index => .local index
  | none => .external address

def externalReferences : Ref → List Address
  | .local _ => []
  | .external address => [address]

def wellScoped (memberCount : Nat) : Ref → Bool
  | .local index => index < memberCount
  | .external _ => true

def materialize (memberKeys : Array Address) : Ref → Except String Address
  | .local index =>
      match memberKeys[index]? with
      | some address => .ok address
      | none => .error s!"IxIR1 block local reference {index} is out of range"
  | .external address => .ok address

end Ref

namespace CtorId

def abstract (keys : List Address) (cid : IxIR1.CtorId) : CtorId :=
  { block := Ref.abstract keys cid.block
    indIdx := cid.indIdx
    cidx := cid.cidx }

def materialize (memberKeys : Array Address)
    (cid : CtorId) : Except String IxIR1.CtorId :=
  return ⟨← cid.block.materialize memberKeys, cid.indIdx, cid.cidx⟩

def externalReferences (cid : CtorId) : List Address :=
  cid.block.externalReferences

def wellScoped (memberCount : Nat) (cid : CtorId) : Bool :=
  cid.block.wellScoped memberCount

end CtorId

namespace Op

def abstract (keys : List Address) : IxIR1.Op → Op
  | .pure atom => .pure atom
  | .alloc world cid args => .alloc world (CtorId.abstract keys cid) args
  | .reuse target cid args => .reuse target (CtorId.abstract keys cid) args
  | .free target => .free target
  | .dup target => .dup target
  | .drop target => .drop target
  | .dropU target => .dropU target
  | .fetch target field => .fetch target field
  | .call function args => .call (Ref.abstract keys function) args
  | .callSelf args => .callSelf args
  | .papp function args => .papp (Ref.abstract keys function) args
  | .apply function args => .apply function args
  | .extern function args => .extern (Ref.abstract keys function) args

def materialize (memberKeys : Array Address) : Op → Except String IxIR1.Op
  | .pure atom => .ok (.pure atom)
  | .alloc world cid args =>
      return .alloc world (← cid.materialize memberKeys) args
  | .reuse target cid args =>
      return .reuse target (← cid.materialize memberKeys) args
  | .free target => .ok (.free target)
  | .dup target => .ok (.dup target)
  | .drop target => .ok (.drop target)
  | .dropU target => .ok (.dropU target)
  | .fetch target field => .ok (.fetch target field)
  | .call function args =>
      return .call (← function.materialize memberKeys) args
  | .callSelf args => .ok (.callSelf args)
  | .papp function args =>
      return .papp (← function.materialize memberKeys) args
  | .apply function args => .ok (.apply function args)
  | .extern function args =>
      return .extern (← function.materialize memberKeys) args

def externalReferences : Op → List Address
  | .alloc _ cid _ | .reuse _ cid _ => cid.externalReferences
  | .call function _ | .papp function _ | .extern function _ =>
      function.externalReferences
  | _ => []

def wellScoped (memberCount : Nat) : Op → Bool
  | .alloc _ cid _ | .reuse _ cid _ => cid.wellScoped memberCount
  | .call function _ | .papp function _ | .extern function _ =>
      function.wellScoped memberCount
  | _ => true

end Op

mutual

def Code.abstract (keys : List Address) : IxIR1.Code → Code
  | .ret atom => .ret atom
  | .letOp operation rest =>
      .letOp (Op.abstract keys operation) (Code.abstract keys rest)
  | .case scrutinee peelNat alternatives =>
      .case scrutinee peelNat (alternatives.map (Alt.abstract keys))

def Alt.abstract (keys : List Address) : IxIR1.Alt → Alt
  | .mk cidx fields body => .mk cidx fields (Code.abstract keys body)

end

mutual

def Code.materialize (memberKeys : Array Address) :
    Code → Except String IxIR1.Code
  | .ret atom => .ok (.ret atom)
  | .letOp operation rest =>
      return .letOp (← operation.materialize memberKeys)
        (← Code.materialize memberKeys rest)
  | .case scrutinee peelNat alternatives =>
      return .case scrutinee peelNat
        (← alternatives.mapM (Alt.materialize memberKeys))

def Alt.materialize (memberKeys : Array Address) :
    Alt → Except String IxIR1.Alt
  | .mk cidx fields body =>
      return .mk cidx fields (← Code.materialize memberKeys body)

end

mutual

def Code.externalReferences : Code → List Address
  | .ret _ => []
  | .letOp operation rest =>
      operation.externalReferences ++ Code.externalReferences rest
  | .case _ _ alternatives =>
      AltList.externalReferences alternatives.toList

def Alt.externalReferences : Alt → List Address
  | .mk _ _ body => Code.externalReferences body

def AltList.externalReferences : List Alt → List Address
  | [] => []
  | alternative :: rest =>
      Alt.externalReferences alternative ++ AltList.externalReferences rest

end

mutual

def Code.wellScoped (memberCount : Nat) : Code → Bool
  | .ret _ => true
  | .letOp operation rest =>
      operation.wellScoped memberCount && Code.wellScoped memberCount rest
  | .case _ _ alternatives =>
      AltList.wellScoped memberCount alternatives.toList

def Alt.wellScoped (memberCount : Nat) : Alt → Bool
  | .mk _ _ body => Code.wellScoped memberCount body

def AltList.wellScoped (memberCount : Nat) : List Alt → Bool
  | [] => true
  | alternative :: rest =>
      Alt.wellScoped memberCount alternative &&
        AltList.wellScoped memberCount rest

end

namespace FnDef

def abstract (keys : List Address) (definition : IxIR1.FnDef) : FnDef :=
  { arity := definition.arity
    result := definition.result
    papSafe := definition.papSafe
    body := Code.abstract keys definition.body }

def materialize (memberKeys : Array Address)
    (definition : FnDef) : Except String IxIR1.FnDef :=
  return ⟨definition.arity, definition.result, definition.papSafe,
    ← definition.body.materialize memberKeys⟩

def externalReferences (definition : FnDef) : List Address :=
  definition.body.externalReferences

def wellScoped (memberCount : Nat) (definition : FnDef) : Bool :=
  definition.body.wellScoped memberCount

end FnDef

namespace Decl

def abstract (keys : List Address) : IxIR1.Decl → Decl
  | .fn definition => .fn (FnDef.abstract keys definition)
  | .extern arity => .extern arity

def materialize (memberKeys : Array Address) :
    Decl → Except String IxIR1.Decl
  | .fn definition => return .fn (← definition.materialize memberKeys)
  | .extern arity => .ok (.extern arity)

def externalReferences : Decl → List Address
  | .fn definition => definition.externalReferences
  | .extern _ => []

def wellScoped (memberCount : Nat) : Decl → Bool
  | .fn definition => definition.wellScoped memberCount
  | .extern _ => true

end Decl

/-- Abstract a transiently keyed ordered block. Keys affect only local-edge
classification and never enter the canonical bytes. -/
def abstractMembers (members : List (Address × IxIR1.Decl)) : List Decl :=
  let keys := members.map (·.1)
  members.map fun member => Decl.abstract keys member.2

/-! ## Executable structural equality -/

namespace Op

def structurallyEq : Op → Op → Bool
  | .pure left, .pure right => left == right
  | .alloc lw lc la, .alloc rw rc ra =>
      lw == rw && lc == rc && la == ra
  | .reuse lt lc la, .reuse rt rc ra =>
      lt == rt && lc == rc && la == ra
  | .free left, .free right
  | .dup left, .dup right
  | .drop left, .drop right
  | .dropU left, .dropU right => left == right
  | .fetch lt lf, .fetch rt rf => lt == rt && lf == rf
  | .call lf la, .call rf ra
  | .papp lf la, .papp rf ra
  | .extern lf la, .extern rf ra => lf == rf && la == ra
  | .callSelf left, .callSelf right => left == right
  | .apply lf la, .apply rf ra => lf == rf && la == ra
  | _, _ => false

theorem structurallyEq_eq_true_iff (left right : Op) :
    structurallyEq left right = true ↔ left = right := by
  cases left <;> cases right <;>
    simp [structurallyEq, beq_iff_eq, and_assoc]

end Op

mutual

def Code.structurallyEq : Code → Code → Bool
  | .ret left, .ret right => left == right
  | .letOp leftOp leftRest, .letOp rightOp rightRest =>
      Op.structurallyEq leftOp rightOp &&
        Code.structurallyEq leftRest rightRest
  | .case ls lp la, .case rs rp ra =>
      ls == rs && lp == rp &&
        AltList.structurallyEq la.toList ra.toList
  | _, _ => false

def Alt.structurallyEq : Alt → Alt → Bool
  | .mk lc lf lb, .mk rc rf rb =>
      lc == rc && lf == rf && Code.structurallyEq lb rb

def AltList.structurallyEq : List Alt → List Alt → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      Alt.structurallyEq left right &&
        AltList.structurallyEq leftRest rightRest
  | _, _ => false

end


mutual

theorem Code.structurallyEq_eq_true_iff (left right : Code) :
    Code.structurallyEq left right = true ↔ left = right := by
  cases left <;> cases right <;>
    simp [Code.structurallyEq, Op.structurallyEq_eq_true_iff,
      Code.structurallyEq_eq_true_iff,
      AltList.structurallyEq_eq_true_iff, beq_iff_eq, and_assoc]

theorem Alt.structurallyEq_eq_true_iff (left right : Alt) :
    Alt.structurallyEq left right = true ↔ left = right := by
  cases left
  cases right
  simp [Alt.structurallyEq, Code.structurallyEq_eq_true_iff,
    beq_iff_eq, and_assoc]

theorem AltList.structurallyEq_eq_true_iff (left right : List Alt) :
    AltList.structurallyEq left right = true ↔ left = right := by
  cases left with
  | nil => cases right <;> simp [AltList.structurallyEq]
  | cons left leftRest =>
      cases right with
      | nil => simp [AltList.structurallyEq]
      | cons right rightRest =>
          simp [AltList.structurallyEq,
            Alt.structurallyEq_eq_true_iff,
            AltList.structurallyEq_eq_true_iff]

end


namespace FnDef

def structurallyEq (left right : FnDef) : Bool :=
  left.arity == right.arity && left.result == right.result &&
    left.papSafe == right.papSafe &&
    Code.structurallyEq left.body right.body

theorem structurallyEq_eq_true_iff (left right : FnDef) :
    structurallyEq left right = true ↔ left = right := by
  cases left
  cases right
  simp [structurallyEq, Code.structurallyEq_eq_true_iff,
    beq_iff_eq, and_assoc]

end FnDef

namespace Decl

def structurallyEq : Decl → Decl → Bool
  | .fn left, .fn right => FnDef.structurallyEq left right
  | .extern left, .extern right => left == right
  | _, _ => false

theorem structurallyEq_eq_true_iff (left right : Decl) :
    structurallyEq left right = true ↔ left = right := by
  cases left <;> cases right <;>
    simp [structurallyEq, FnDef.structurallyEq_eq_true_iff,
      beq_iff_eq]

end Decl

/-! ## Canonical bytes and identities -/

namespace Ref

def bytes : Ref → ByteArray
  | .local index => Encoding.tag 0 ++ Encoding.nat index
  | .external address => Encoding.tag 1 ++ Encoding.address address

end Ref

namespace CtorId

def bytes (cid : CtorId) : ByteArray :=
  cid.block.bytes ++ Encoding.nat cid.indIdx ++ Encoding.nat cid.cidx

end CtorId

namespace Op

def bytes : Op → ByteArray
  | .pure atom => Encoding.tag 0 ++ IxIR1.Atom.bytes atom
  | .alloc world cid args =>
      Encoding.tag 1 ++ Encoding.tag world.toBits ++ cid.bytes ++
        Encoding.array IxIR1.Atom.bytes args
  | .reuse target cid args =>
      Encoding.tag 2 ++ IxIR1.Atom.bytes target ++ cid.bytes ++
        Encoding.array IxIR1.Atom.bytes args
  | .free target => Encoding.tag 3 ++ IxIR1.Atom.bytes target
  | .dup target => Encoding.tag 4 ++ IxIR1.Atom.bytes target
  | .drop target => Encoding.tag 5 ++ IxIR1.Atom.bytes target
  | .dropU target => Encoding.tag 6 ++ IxIR1.Atom.bytes target
  | .fetch target field =>
      Encoding.tag 7 ++ IxIR1.Atom.bytes target ++ Encoding.nat field
  | .call function args =>
      Encoding.tag 8 ++ function.bytes ++
        Encoding.array IxIR1.Atom.bytes args
  | .callSelf args =>
      Encoding.tag 9 ++ Encoding.array IxIR1.Atom.bytes args
  | .papp function args =>
      Encoding.tag 10 ++ function.bytes ++
        Encoding.array IxIR1.Atom.bytes args
  | .apply function args =>
      Encoding.tag 11 ++ IxIR1.Atom.bytes function ++
        Encoding.array IxIR1.Atom.bytes args
  | .extern function args =>
      Encoding.tag 12 ++ function.bytes ++
        Encoding.array IxIR1.Atom.bytes args

end Op

mutual

def Code.bytes : Code → ByteArray
  | .ret atom => Encoding.tag 0 ++ IxIR1.Atom.bytes atom
  | .letOp operation rest => Encoding.tag 1 ++ operation.bytes ++ rest.bytes
  | .case scrutinee peelNat alternatives =>
      Encoding.tag 2 ++ IxIR1.Atom.bytes scrutinee ++
        Encoding.bool peelNat ++ Encoding.nat alternatives.size ++
        AltList.bytes alternatives.toList

def Alt.bytes : Alt → ByteArray
  | .mk cidx fields body =>
      Encoding.nat cidx ++ Encoding.nat fields ++ body.bytes

def AltList.bytes : List Alt → ByteArray
  | [] => ByteArray.empty
  | head :: tail => head.bytes ++ AltList.bytes tail

end


namespace FnDef

def bytes (definition : FnDef) : ByteArray :=
  Encoding.nat definition.arity ++ Encoding.tag definition.result.toBits ++
    Encoding.bool definition.papSafe ++ definition.body.bytes

end FnDef

namespace Decl

def bytes : Decl → ByteArray
  | .fn definition => Encoding.tag 0 ++ definition.bytes
  | .extern arity => Encoding.tag 1 ++ Encoding.nat arity

end Decl

namespace Block

def addressDomain : ByteArray :=
  Encoding.domain "compilatrix/ixir1/mutual-block/2" ++ Encoding.tag 0

def preimage (members : List Decl) : ByteArray :=
  addressDomain ++ Encoding.list Decl.bytes members

def address (members : List Decl) : Address :=
  Address.blake3 (preimage members)

theorem address_eq_iff_preimage_eq (left right : List Decl)
    (hcollision : Address.Blake3NoCollision (preimage left) (preimage right)) :
    address left = address right ↔ preimage left = preimage right := by
  constructor
  · exact hcollision
  · intro h
    simp only [address]
    rw [h]

end Block

namespace Member

def addressDomain : ByteArray :=
  Encoding.domain "compilatrix/ixir1/mutual-member/1" ++ Encoding.tag 0

def preimage (block : Address) (index : Nat) : ByteArray :=
  addressDomain ++ Encoding.address block ++ Encoding.nat index

def address (block : Address) (index : Nat) : Address :=
  Address.blake3 (preimage block index)

theorem address_eq_iff_preimage_eq (leftBlock rightBlock : Address)
    (leftIndex rightIndex : Nat)
    (hcollision : Address.Blake3NoCollision
      (preimage leftBlock leftIndex) (preimage rightBlock rightIndex)) :
    address leftBlock leftIndex = address rightBlock rightIndex ↔
      preimage leftBlock leftIndex = preimage rightBlock rightIndex := by
  constructor
  · exact hcollision
  · intro h
    simp only [address]
    rw [h]

end Member

/-! ## Strict block decoder -/

open Ix.Compiler.IxIR.Decode
open Ix.Compiler.Ixon

def getRefTag : UInt8 → GetM Ref
  | 0 => do return .local (← Decode.getNat)
  | 1 => do return .external (← Decode.getAddress)
  | tag => throw s!"IxIR1 block reference: invalid tag {tag}"

def getRef : GetM Ref := do
  getRefTag (← getU8)

def getCtorId : GetM CtorId := do
  return ⟨← getRef, ← Decode.getNat, ← Decode.getNat⟩

def getOpTag : UInt8 → GetM Op
  | 0 => do return .pure (← IxIR1.getAtom)
  | 1 => do
      let world ← IxIR0.getOwned
      let cid ← getCtorId
      return .alloc world cid (← Decode.getArray IxIR1.getAtom)
  | 2 => do
      let target ← IxIR1.getAtom
      let cid ← getCtorId
      return .reuse target cid (← Decode.getArray IxIR1.getAtom)
  | 3 => do return .free (← IxIR1.getAtom)
  | 4 => do return .dup (← IxIR1.getAtom)
  | 5 => do return .drop (← IxIR1.getAtom)
  | 6 => do return .dropU (← IxIR1.getAtom)
  | 7 => do return .fetch (← IxIR1.getAtom) (← Decode.getNat)
  | 8 => do return .call (← getRef) (← Decode.getArray IxIR1.getAtom)
  | 9 => do return .callSelf (← Decode.getArray IxIR1.getAtom)
  | 10 => do return .papp (← getRef) (← Decode.getArray IxIR1.getAtom)
  | 11 => do return .apply (← IxIR1.getAtom) (← Decode.getArray IxIR1.getAtom)
  | 12 => do return .extern (← getRef) (← Decode.getArray IxIR1.getAtom)
  | tag => throw s!"IxIR1 block operation: invalid tag {tag}"

def getOp : GetM Op := do
  getOpTag (← getU8)

def getAlt (recur : GetM Code) : GetM Alt := do
  return .mk (← Decode.getNat) (← Decode.getNat) (← recur)

def getCodeTag (recur : GetM Code) : UInt8 → GetM Code
  | 0 => do return .ret (← IxIR1.getAtom)
  | 1 => do return .letOp (← getOp) (← recur)
  | 2 => do
      let scrutinee ← IxIR1.getAtom
      let peelNat ← Decode.getBool
      return .case scrutinee peelNat (← Decode.getArray (getAlt recur))
  | tag => throw s!"IxIR1 block code: invalid tag {tag}"

def getCodeFuel : Nat → GetM Code
  | 0 => throw "IxIR1 block code: recursion limit"
  | fuel + 1 => do
      getCodeTag (getCodeFuel fuel) (← getU8)

def getCode : GetM Code := do
  let state ← get
  getCodeFuel (state.bytes.size + 1)

def getFnDef : GetM FnDef := do
  return ⟨← Decode.getNat, ← IxIR0.getOwned, ← Decode.getBool,
    ← getCode⟩

def getDeclTag : UInt8 → GetM Decl
  | 0 => do return .fn (← getFnDef)
  | 1 => do return .extern (← Decode.getNat)
  | tag => throw s!"IxIR1 block declaration: invalid tag {tag}"

def getDecl : GetM Decl := do
  getDeclTag (← getU8)

def getBlockPreimage : GetM (List Decl) := do
  Decode.expectBytes Block.addressDomain
  Decode.getList getDecl

def Block.decodePreimage (bytes : ByteArray) : Except String (List Decl) :=
  Decode.runCanonical getBlockPreimage Block.preimage bytes

def Block.decodeArtifact (bytes : ByteArray) : Except String (List Decl) := do
  let members ← Block.decodePreimage bytes
  if members.isEmpty then
    throw "IxIR1 mutual block must contain at least one member"
  unless members.all (Decl.wellScoped members.length) do
    throw "IxIR1 mutual block contains an out-of-range local reference"
  return members

/-! ### Cursor-relative decoder proofs -/

theorem getRef_spec : ∀ target : Ref, GetSpec getRef target.bytes target
  | .local index => by
      have hpayload := Decode.getSpecMap (Decode.getNat_spec index) Ref.local
      have htotal := GetSpec.bind (next := getRefTag)
        (Decode.getU8_tag_spec 0) hpayload
      simpa only [getRef, Ref.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .external address => by
      have hpayload := Decode.getSpecMap
        (Decode.getAddress_spec address) Ref.external
      have htotal := GetSpec.bind (next := getRefTag)
        (Decode.getU8_tag_spec 1) hpayload
      simpa only [getRef, Ref.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal

theorem getCtorId_spec (cid : CtorId) :
    GetSpec getCtorId cid.bytes cid := by
  have hspec := Decode.getSpecMap3 (getRef_spec cid.block)
    (Decode.getNat_spec cid.indIdx) (Decode.getNat_spec cid.cidx) CtorId.mk
  simpa [getCtorId, CtorId.bytes] using hspec

private theorem getAtomArray_spec (atoms : Array Atom) :
    GetSpec (Decode.getArray IxIR1.getAtom)
      (Encoding.array IxIR1.Atom.bytes atoms) atoms :=
  Decode.getArray_spec IxIR1.getAtom IxIR1.Atom.bytes
    IxIR1.getAtom_spec atoms

theorem getOp_spec : ∀ operation : Op,
    GetSpec getOp operation.bytes operation
  | .pure atom => by
      have hpayload := Decode.getSpecMap (IxIR1.getAtom_spec atom) Op.pure
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 0) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .alloc world cid args => by
      have hpayload := Decode.getSpecMap3 (IxIR0.getOwned_spec world)
        (getCtorId_spec cid) (getAtomArray_spec args) Op.alloc
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 1) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .reuse target cid args => by
      have hpayload := Decode.getSpecMap3 (IxIR1.getAtom_spec target)
        (getCtorId_spec cid) (getAtomArray_spec args) Op.reuse
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 2) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .free target => by
      have hpayload := Decode.getSpecMap (IxIR1.getAtom_spec target) Op.free
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 3) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .dup target => by
      have hpayload := Decode.getSpecMap (IxIR1.getAtom_spec target) Op.dup
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 4) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .drop target => by
      have hpayload := Decode.getSpecMap (IxIR1.getAtom_spec target) Op.drop
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 5) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .dropU target => by
      have hpayload := Decode.getSpecMap (IxIR1.getAtom_spec target) Op.dropU
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 6) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .fetch target field => by
      have hpayload := Decode.getSpecMap2 (IxIR1.getAtom_spec target)
        (Decode.getNat_spec field) Op.fetch
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 7) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .call function args => by
      have hpayload := Decode.getSpecMap2 (getRef_spec function)
        (getAtomArray_spec args) Op.call
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 8) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .callSelf args => by
      have hpayload := Decode.getSpecMap (getAtomArray_spec args) Op.callSelf
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 9) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .papp function args => by
      have hpayload := Decode.getSpecMap2 (getRef_spec function)
        (getAtomArray_spec args) Op.papp
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 10) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .apply function args => by
      have hpayload := Decode.getSpecMap2 (IxIR1.getAtom_spec function)
        (getAtomArray_spec args) Op.apply
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 11) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .extern function args => by
      have hpayload := Decode.getSpecMap2 (getRef_spec function)
        (getAtomArray_spec args) Op.extern
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 12) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal

theorem AltList.bytes_eq_listBytes (alternatives : List Alt) :
    AltList.bytes alternatives = Decode.listBytes Alt.bytes alternatives := by
  induction alternatives with
  | nil => rfl
  | cons head tail ih => simp [AltList.bytes, Decode.listBytes, ih]

theorem AltList.member_size_le {alternative : Alt}
    {alternatives : List Alt} (hmember : alternative ∈ alternatives) :
    alternative.bytes.size ≤ (AltList.bytes alternatives).size := by
  induction alternatives with
  | nil => simp at hmember
  | cons head tail ih =>
      simp only [List.mem_cons] at hmember
      simp only [AltList.bytes, ByteArray.size_append]
      rcases hmember with rfl | hmember
      · omega
      · have htail := ih hmember
        omega

theorem Alt.body_size_lt_bytes (cidx fields : Nat) (body : Code) :
    body.bytes.size < (Alt.mk cidx fields body).bytes.size := by
  simp only [Alt.bytes, ByteArray.size_append]
  have hcidx := Decode.nat_size_pos cidx
  have hfields := Decode.nat_size_pos fields
  omega

/-- Structural induction exposing every code body nested in an alternative
array. -/
theorem Code.nested_induction (property : Code → Prop)
    (hret : ∀ atom, property (.ret atom))
    (hlet : ∀ operation rest, property rest →
      property (.letOp operation rest))
    (hcase : ∀ scrutinee peelNat alternatives,
      (∀ cidx fields body,
        Alt.mk cidx fields body ∈ alternatives.toList → property body) →
      property (.case scrutinee peelNat alternatives))
    (code : Code) : property code := by
  apply Code.rec
    (motive_1 := fun alternative => match alternative with
      | .mk _ _ body => property body)
    (motive_2 := property)
    (motive_3 := fun alternatives => ∀ cidx fields body,
      Alt.mk cidx fields body ∈ alternatives.toList → property body)
    (motive_4 := fun alternatives => ∀ cidx fields body,
      Alt.mk cidx fields body ∈ alternatives → property body)
    (mk := by intro cidx fields body hbody; exact hbody)
    (ret := hret)
    (letOp := by
      intro operation rest hrest
      exact hlet operation rest hrest)
    (case := hcase)
    (by intro alternatives halternatives; exact halternatives)
    (by simp)
    (by
      intro head tail hhead htail cidx fields body hmember
      simp only [List.mem_cons] at hmember
      rcases hmember with hheadEq | htailMem
      · cases hheadEq
        exact hhead
      · exact htail cidx fields body htailMem)

theorem getCodeFuel_spec (code : Code) (fuel : Nat)
    (hfuel : code.bytes.size < fuel) :
    GetSpec (getCodeFuel fuel) code.bytes code := by
  apply Code.nested_induction
    (property := fun code => ∀ fuel, code.bytes.size < fuel →
      GetSpec (getCodeFuel fuel) code.bytes code)
    (code := code)
  · intro atom fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        have hpayload := Decode.getSpecMap
          (IxIR1.getAtom_spec atom) Code.ret
        have htotal := GetSpec.bind
          (next := getCodeTag (getCodeFuel fuel))
          (Decode.getU8_tag_spec 0) hpayload
        simpa only [getCodeFuel, Code.bytes, ByteArray.append_assoc,
          ByteArray.append_empty] using htotal
  · intro operation rest hrest fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        have hrestFuel : rest.bytes.size < fuel := by
          simp only [Code.bytes, ByteArray.size_append,
            Decode.tag_size] at hfuel
          omega
        have hpayload := Decode.getSpecMap2 (getOp_spec operation)
          (hrest fuel hrestFuel) Code.letOp
        have htotal := GetSpec.bind
          (next := getCodeTag (getCodeFuel fuel))
          (Decode.getU8_tag_spec 1) hpayload
        simpa only [getCodeFuel, Code.bytes, ByteArray.append_assoc,
          ByteArray.append_empty] using htotal
  · intro scrutinee peelNat alternatives hchildren fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        let admissible : Alt → Prop := fun alternative =>
          alternative ∈ alternatives.toList ∧
            match alternative with
            | .mk _ _ body => body.bytes.size < fuel
        have hadmissible : ∀ alternative ∈ alternatives.toList,
            admissible alternative := by
          intro alternative hmember
          cases alternative with
          | mk cidx fields body =>
              refine ⟨hmember, ?_⟩
              have hbody := Alt.body_size_lt_bytes cidx fields body
              have halternative := AltList.member_size_le hmember
              simp only [Code.bytes, ByteArray.size_append,
                Decode.tag_size] at hfuel
              omega
        have hone : ∀ alternative, admissible alternative →
            GetSpec (getAlt (getCodeFuel fuel))
              alternative.bytes alternative := by
          intro alternative halternative
          rcases halternative with ⟨hmember, hbodyFuel⟩
          cases alternative with
          | mk cidx fields body =>
              have hspec := Decode.getSpecMap3
                (Decode.getNat_spec cidx) (Decode.getNat_spec fields)
                (hchildren cidx fields body hmember fuel hbodyFuel) Alt.mk
              simpa [getAlt, Alt.bytes] using hspec
        have harray := Decode.getArray_spec_of
          (getAlt (getCodeFuel fuel)) Alt.bytes admissible hone
          alternatives hadmissible
        rw [Decode.array_eq_counted,
          ← AltList.bytes_eq_listBytes alternatives.toList] at harray
        have hpayload := Decode.getSpecMap3
          (IxIR1.getAtom_spec scrutinee)
          (Decode.getBool_spec peelNat) harray Code.case
        have htotal := GetSpec.bind
          (next := getCodeTag (getCodeFuel fuel))
          (Decode.getU8_tag_spec 2) hpayload
        simpa only [getCodeFuel, Code.bytes, ByteArray.append_assoc,
          ByteArray.append_empty] using htotal
  · exact hfuel

theorem getCode_spec (code : Code) :
    GetSpec getCode code.bytes code := by
  intro pre suffix
  let fuel := (pre ++ code.bytes ++ suffix).size + 1
  have hfuel : code.bytes.size < fuel := by
    dsimp [fuel]
    simp only [ByteArray.size_append]
    omega
  have hspec := getCodeFuel_spec code fuel hfuel pre suffix
  simpa [getCode, fuel] using hspec

theorem getFnDef_spec (definition : FnDef) :
    GetSpec getFnDef definition.bytes definition := by
  have hspec := Decode.getSpecMap4 (Decode.getNat_spec definition.arity)
    (IxIR0.getOwned_spec definition.result)
    (Decode.getBool_spec definition.papSafe) (getCode_spec definition.body)
    FnDef.mk
  simpa [getFnDef, FnDef.bytes] using hspec

theorem getDecl_spec : ∀ declaration : Decl,
    GetSpec getDecl declaration.bytes declaration
  | .fn definition => by
      have hpayload := Decode.getSpecMap (getFnDef_spec definition) Decl.fn
      have htotal := GetSpec.bind (next := getDeclTag)
        (Decode.getU8_tag_spec 0) hpayload
      simpa only [getDecl, Decl.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .extern arity => by
      have hpayload := Decode.getSpecMap (Decode.getNat_spec arity) Decl.extern
      have htotal := GetSpec.bind (next := getDeclTag)
        (Decode.getU8_tag_spec 1) hpayload
      simpa only [getDecl, Decl.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal

theorem getBlockPreimage_spec (members : List Decl) :
    GetSpec getBlockPreimage (Block.preimage members) members := by
  let next : Unit → GetM (List Decl) := fun _ => Decode.getList getDecl
  have htotal := GetSpec.bind (next := next)
    (Decode.expectBytes_spec Block.addressDomain)
    (Decode.getList_spec getDecl Decl.bytes getDecl_spec members)
  simpa [getBlockPreimage, Block.preimage, next] using htotal

/-! ### Strict top-level codec laws -/

theorem Block.decodePreimage_roundtrip (members : List Decl) :
    Block.decodePreimage (Block.preimage members) = .ok members := by
  exact Decode.runCanonical_of_spec getBlockPreimage Block.preimage members
    (getBlockPreimage_spec members)

theorem Block.decodePreimage_canonical {bytes : ByteArray}
    {members : List Decl}
    (hdecode : Block.decodePreimage bytes = .ok members) :
    Block.preimage members = bytes := by
  exact Decode.runCanonical_canonical getBlockPreimage Block.preimage hdecode

theorem Block.preimage_injective : Function.Injective Block.preimage := by
  intro left right hbytes
  have hok : (Except.ok left : Except String (List Decl)) = .ok right := by
    calc
      .ok left = Block.decodePreimage (Block.preimage left) :=
        (Block.decodePreimage_roundtrip left).symm
      _ = Block.decodePreimage (Block.preimage right) :=
        congrArg Block.decodePreimage hbytes
      _ = .ok right := Block.decodePreimage_roundtrip right
  exact Except.ok.inj hok

/-! ## Collision-checked construction and ingress materialization -/

namespace DeclList

def structurallyEq : List Decl → List Decl → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      Decl.structurallyEq left right && structurallyEq leftRest rightRest
  | _, _ => false

theorem structurallyEq_eq_true_iff (left right : List Decl) :
    structurallyEq left right = true ↔ left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [structurallyEq]
  | cons left rest ih =>
      cases right with
      | nil => simp [structurallyEq]
      | cons right rightRest =>
          simp [structurallyEq, Decl.structurallyEq_eq_true_iff, ih]

end DeclList

/-- Old block-member key to its final derived key. -/
abbrev Renaming := Readdress.Renaming

/-- A completely materialized cycle-safe block. -/
structure Result where
  blockAddress : Address
  blockMembers : List Decl
  members : List (Address × IxIR1.Decl)
  addressMap : Renaming

namespace Result

def transientAddresses (result : Result) : List Address :=
  result.addressMap.map (·.1)

def derivedAddresses (result : Result) : List Address :=
  result.addressMap.map (·.2)

def memberKeysDerived (result : Result) : Bool :=
  let rec loop : Nat → Renaming → Bool
    | _, [] => true
    | index, entry :: rest =>
        entry.2 == Member.address result.blockAddress index &&
          loop (index + 1) rest
  loop 0 result.addressMap &&
    result.members.map (·.1) == result.derivedAddresses

def blockStable (result : Result) : Bool :=
  DeclList.structurallyEq
    (abstractMembers result.members) result.blockMembers

def noTransientKeys (result : Result) : Bool :=
  !(result.members.map (·.1)).any result.transientAddresses.contains

def noTransientReferences (result : Result) : Bool :=
  let references := result.members.flatMap fun member =>
    Readdress.Decl.references member.2
  !references.any result.transientAddresses.contains

/-- Executable certificate that materialization is exactly the completed
address image of the transient block and that re-abstraction recovers the
canonical symbolic artifact. -/
def semanticAudit (result : Result)
    (raw : List (Address × IxIR1.Decl)) : Bool :=
  let rename := Readdress.Renaming.apply result.addressMap
  let original := IxIR1.Env.ofList raw
  let emitted := IxIR1.Env.ofList result.members
  DeclList.structurallyEq result.blockMembers (abstractMembers raw) &&
    result.blockAddress == Block.address result.blockMembers &&
    result.memberKeysDerived && result.blockStable &&
    result.noTransientKeys && result.noTransientReferences &&
    raw.all (fun entry =>
      match original entry.1, emitted (rename entry.1) with
      | some before, some after =>
          Readdress.Decl.structurallyEq after
            (Readdress.Decl.mapAddresses rename before)
      | _, _ => false) &&
    result.members.all (fun entry =>
      match emitted entry.1 with
      | some declaration =>
          Readdress.Decl.structurallyEq
            (Readdress.Decl.mapAddresses rename declaration) declaration
      | none => false)

end Result

abbrev CertifiedResult (raw : List (Address × IxIR1.Decl)) :=
  { result : Result // result.semanticAudit raw = true }

private def firstDuplicate? : List Address → Option Address
  | [] => none
  | address :: rest =>
      if rest.contains address then some address else firstDuplicate? rest

private def firstOverlap? (left right : List Address) : Option Address :=
  left.find? right.contains

private def deriveMap (block : Address) :
    Nat → List (Address × IxIR1.Decl) → Renaming
  | _, [] => []
  | index, member :: rest =>
      (member.1, Member.address block index) ::
        deriveMap block (index + 1) rest

/-- Materialized stored block, independent of transient producer names. -/
structure Artifact where
  blockAddress : Address
  blockMembers : List Decl
  members : List (Address × IxIR1.Decl)

namespace Artifact

def memberKeysDerived (artifact : Artifact) : Bool :=
  let rec loop : Nat → List (Address × IxIR1.Decl) → Bool
    | _, [] => true
    | index, member :: rest =>
        member.1 == Member.address artifact.blockAddress index &&
          loop (index + 1) rest
  loop 0 artifact.members

def stable (artifact : Artifact) : Bool :=
  DeclList.structurallyEq
    (abstractMembers artifact.members) artifact.blockMembers

def audit (artifact : Artifact) : Bool :=
  artifact.blockAddress == Block.address artifact.blockMembers &&
    artifact.members.length == artifact.blockMembers.length &&
    artifact.blockMembers.all
      (Decl.wellScoped artifact.blockMembers.length) &&
    artifact.memberKeysDerived && artifact.stable

end Artifact

private def deriveKeys (block : Address) : Nat → Nat → List Address
  | _, 0 => []
  | index, count + 1 =>
      Member.address block index :: deriveKeys block (index + 1) count

/-- Validate and materialize a decoded symbolic block. -/
def Block.materializeArtifact (reserved : List Address)
    (blockMembers : List Decl) : Except String Artifact := do
  if blockMembers.isEmpty then
    throw "IxIR1 mutual block must contain at least one member"
  unless blockMembers.all (Decl.wellScoped blockMembers.length) do
    throw "IxIR1 mutual block contains an out-of-range local reference"
  let blockAddress := Block.address blockMembers
  if reserved.contains blockAddress then
    throw s!"IxIR1 mutual-block identity collides with reserved identity {Address.toHex blockAddress}"
  let external := blockMembers.flatMap Decl.externalReferences
  if external.contains blockAddress then
    throw s!"IxIR1 mutual-block identity collides with an external reference {Address.toHex blockAddress}"
  let derived := deriveKeys blockAddress 0 blockMembers.length
  if let some duplicate := firstDuplicate? derived then
    throw s!"BLAKE3 collision between IxIR1 mutual-block member keys {Address.toHex duplicate}"
  if derived.contains blockAddress then
    throw s!"IxIR1 mutual-block member key collides with its block identity {Address.toHex blockAddress}"
  if let some overlap := firstOverlap? derived reserved then
    throw s!"IxIR1 mutual-block member key collides with reserved identity {Address.toHex overlap}"
  if let some overlap := firstOverlap? derived external then
    throw s!"IxIR1 mutual-block member key captures an external reference {Address.toHex overlap}"
  let declarations ← blockMembers.mapM
    (Decl.materialize derived.toArray)
  let artifact : Artifact :=
    { blockAddress, blockMembers, members := derived.zip declarations }
  unless artifact.audit do
    throw "internal: decoded IxIR1 mutual block failed materialization audit"
  return artifact

def Block.decodeMaterialized (reserved : List Address)
    (bytes : ByteArray) : Except String Artifact := do
  Block.materializeArtifact reserved (← Block.decodeArtifact bytes)

private def certify (raw : List (Address × IxIR1.Decl))
    (result : Result) : Except String (CertifiedResult raw) :=
  if haudit : result.semanticAudit raw then .ok ⟨result, haudit⟩
  else .error "internal: IxIR1 mutual-block materialization failed semantic audit"

/-- Construct and certify one ordered cycle-safe block while protecting every
caller-owned external identity. -/
def runCertified (reserved : List Address)
    (raw : List (Address × IxIR1.Decl)) :
    Except String (CertifiedResult raw) := do
  if raw.isEmpty then
    throw "IxIR1 mutual block must contain at least one member"
  let transient := raw.map (·.1)
  if let some duplicate := firstDuplicate? transient then
    throw s!"duplicate IxIR1 mutual-block temporary address {Address.toHex duplicate}"
  if let some overlap := firstOverlap? transient reserved then
    throw s!"IxIR1 mutual-block temporary address overlaps reserved identity {Address.toHex overlap}"
  let blockMembers := abstractMembers raw
  unless blockMembers.all (Decl.wellScoped blockMembers.length) do
    throw "internal: abstracted IxIR1 mutual block contains an out-of-range local reference"
  let blockAddress := Block.address blockMembers
  if transient.contains blockAddress then
    throw s!"IxIR1 mutual-block identity overlaps temporary namespace {Address.toHex blockAddress}"
  if reserved.contains blockAddress then
    throw s!"IxIR1 mutual-block identity collides with reserved identity {Address.toHex blockAddress}"
  let external := blockMembers.flatMap Decl.externalReferences
  if external.contains blockAddress then
    throw s!"IxIR1 mutual-block identity collides with an external reference {Address.toHex blockAddress}"
  let addressMap := deriveMap blockAddress 0 raw
  let derived := addressMap.map (·.2)
  if let some duplicate := firstDuplicate? derived then
    throw s!"BLAKE3 collision between IxIR1 mutual-block member keys {Address.toHex duplicate}"
  if derived.contains blockAddress then
    throw s!"IxIR1 mutual-block member key collides with its block identity {Address.toHex blockAddress}"
  if let some overlap := firstOverlap? derived transient then
    throw s!"IxIR1 mutual-block member key overlaps temporary namespace {Address.toHex overlap}"
  if let some overlap := firstOverlap? derived reserved then
    throw s!"IxIR1 mutual-block member key collides with reserved identity {Address.toHex overlap}"
  if let some overlap := firstOverlap? derived external then
    throw s!"IxIR1 mutual-block member key captures an external reference {Address.toHex overlap}"
  let memberKeys := derived.toArray
  let materialized ← blockMembers.mapM (Decl.materialize memberKeys)
  let result : Result :=
    { blockAddress
      blockMembers
      members := derived.zip materialized
      addressMap }
  certify raw result

def run (reserved : List Address)
    (raw : List (Address × IxIR1.Decl)) : Except String Result := do
  return (← runCertified reserved raw).1

theorem semanticAudit_of_run_eq_ok
    {reserved : List Address} {raw : List (Address × IxIR1.Decl)}
    {result : Result} (hrun : run reserved raw = .ok result) :
    result.semanticAudit raw = true := by
  unfold run at hrun
  cases hcertified : runCertified reserved raw with
  | error message =>
      rw [hcertified] at hrun
      contradiction
  | ok certified =>
      rw [hcertified] at hrun
      have hvalue : certified.1 = result := by injection hrun
      subst result
      exact certified.2

/-! Pure structural format guards. Digest fixtures live in `Tests.lean`. -/

private def fixtureA : Address := Address.replicate 0xfa
private def fixtureB : Address := Address.replicate 0xfb
private def fixtureExternal : Address := Address.replicate 0xee

#guard Ref.bytes (.local 128) == ByteArray.mk #[0, 128, 1]
#guard (Ref.bytes (.external fixtureExternal)).size == 33
#guard Op.bytes (.call (.local 1) #[]) == ByteArray.mk #[8, 0, 1, 0]
#guard Decl.bytes (.fn ⟨0, .shared, true,
  .letOp (.call (.local 1) #[]) (.ret .erased)⟩) ==
    ByteArray.mk #[0, 0, 1, 1, 1, 8, 0, 1, 0, 0, 2]
#guard
  DeclList.structurallyEq
    (abstractMembers
      [(fixtureA, .fn ⟨0, .shared, true,
          .letOp (.call fixtureB #[]) (.ret .erased)⟩),
       (fixtureB, .fn ⟨0, .shared, true,
          .letOp (.papp fixtureA #[]) (.ret .erased)⟩)])
    [.fn ⟨0, .shared, true,
        .letOp (.call (.local 1) #[]) (.ret .erased)⟩,
     .fn ⟨0, .shared, true,
        .letOp (.papp (.local 0) #[]) (.ret .erased)⟩]

end MutualBlock

end Ix.Compiler.IxIR1
