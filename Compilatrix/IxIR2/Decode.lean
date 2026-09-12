import Compilatrix.IxIR2.Serialize
import Compilatrix.IxIR.Bounded
import Compilatrix.IxIR0.Decode

/-!
# Strict bounded IxIR₂ snapshot decoding

The same bounded reader used at ingress is proved to roundtrip every value
in its explicit representable domain. Arrays/lists use bounded tail-recursive
readers; the grammar has no recursively nested code. Public acceptance also
requires full consumption and exact re-encoding of the complete domain frame.
-/

namespace Compilatrix.IxIR2.Wire

open Compilatrix.Ixon
open Compilatrix.IxIR

private theorem getOwned_spec (value : Owned) :
    GetSpec IxIR0.getOwned (ownedBytes value) value := IxIR0.getOwned_spec value

def literalFits (limits : Bounded.Limits) : IxIR0.Literal → Bool
  | .nat v0 => Bounded.natFits limits v0
  | .str v0 => Bounded.stringFits limits v0

def getLiteralTag (limits : Bounded.Limits) : UInt8 → GetM (IxIR0.Literal)
  | 0 => do return .nat (← Bounded.getNat limits)
  | 1 => do return .str (← Bounded.getString limits)
  | tag => throw s!"IxIR2 literal: invalid tag {tag}"

def getLiteral (limits : Bounded.Limits) : GetM (IxIR0.Literal) := do
  getLiteralTag limits (← getU8)

theorem getLiteral_spec (limits : Bounded.Limits) : ∀ value : IxIR0.Literal,
    literalFits limits value = true → GetSpec (getLiteral limits) (literalBytes value) value
  | .nat v0, admitted => by
      change (Bounded.natFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (Bounded.getNat_spec limits v0 h0) IxIR0.Literal.nat
      have total := GetSpec.bind (next := getLiteralTag limits)
        (Decode.getU8_tag_spec 0) payload
      simpa only [getLiteral, literalBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .str v0, admitted => by
      change (Bounded.stringFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (Bounded.getString_spec limits v0 h0) IxIR0.Literal.str
      have total := GetSpec.bind (next := getLiteralTag limits)
        (Decode.getU8_tag_spec 1) payload
      simpa only [getLiteral, literalBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total

def atomFits (limits : Bounded.Limits) : Atom → Bool
  | .reg v0 => Bounded.natFits limits v0
  | .lit v0 => literalFits limits v0
  | .erased => true

def getAtomTag (limits : Bounded.Limits) : UInt8 → GetM (Atom)
  | 0 => do return .reg (← Bounded.getNat limits)
  | 1 => do return .lit (← getLiteral limits)
  | 2 => pure .erased
  | tag => throw s!"IxIR2 atom: invalid tag {tag}"

def getAtom (limits : Bounded.Limits) : GetM (Atom) := do
  getAtomTag limits (← getU8)

theorem getAtom_spec (limits : Bounded.Limits) : ∀ value : Atom,
    atomFits limits value = true → GetSpec (getAtom limits) (atomBytes value) value
  | .reg v0, admitted => by
      change (Bounded.natFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (Bounded.getNat_spec limits v0 h0) Atom.reg
      have total := GetSpec.bind (next := getAtomTag limits)
        (Decode.getU8_tag_spec 0) payload
      simpa only [getAtom, atomBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .lit v0, admitted => by
      change (literalFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (getLiteral_spec limits v0 h0) Atom.lit
      have total := GetSpec.bind (next := getAtomTag limits)
        (Decode.getU8_tag_spec 1) payload
      simpa only [getAtom, atomBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .erased, admitted => by
      have payload : GetSpec (getAtomTag limits 2) ByteArray.empty (.erased : Atom) :=
        GetSpec.pure (.erased : Atom)
      have total := GetSpec.bind (next := getAtomTag limits)
        (Decode.getU8_tag_spec 2) payload
      simpa only [getAtom, atomBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total

def getParamPassingTag : UInt8 → GetM (ParamPassing)
  | 0 => pure .owned
  | 1 => pure .borrowed
  | tag => throw s!"IxIR2 paramPassing: invalid tag {tag}"

def getParamPassing : GetM (ParamPassing) := do
  getParamPassingTag (← getU8)

theorem getParamPassing_spec : ∀ value : ParamPassing,
    GetSpec (getParamPassing) (paramPassingBytes value) value
  | .owned => by
      have payload : GetSpec (getParamPassingTag 0) ByteArray.empty (.owned : ParamPassing) :=
        GetSpec.pure (.owned : ParamPassing)
      have total := GetSpec.bind (next := getParamPassingTag)
        (Decode.getU8_tag_spec 0) payload
      simpa only [getParamPassing, paramPassingBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .borrowed => by
      have payload : GetSpec (getParamPassingTag 1) ByteArray.empty (.borrowed : ParamPassing) :=
        GetSpec.pure (.borrowed : ParamPassing)
      have total := GetSpec.bind (next := getParamPassingTag)
        (Decode.getU8_tag_spec 1) payload
      simpa only [getParamPassing, paramPassingBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total

def getParam : GetM (Param) := do
  return Param.mk (← IxIR0.getOwned) (← getParamPassing)

theorem getParam_spec (value : Param) :
    GetSpec (getParam) (paramBytes value) value := by
  have total := Decode.getSpecMap2 (getOwned_spec value.world) (getParamPassing_spec value.passing) Param.mk
  simpa only [getParam, paramBytes] using total

def paramArrayFits (limits : Bounded.Limits) (value : Array Param) : Bool :=
  Bounded.arrayFits limits (fun _ => true) value

def getParamArray (limits : Bounded.Limits) : GetM (Array Param) :=
  Bounded.getArray limits (getParam)

theorem getParamArray_spec (limits : Bounded.Limits) (value : Array Param)
    (admitted : paramArrayFits limits value = true) :
    GetSpec (getParamArray limits) (paramArrayBytes value) value := by
  exact Bounded.getArray_spec limits (getParam) paramBytes (fun _ => true)
    (fun value _ => getParam_spec value) value admitted

def signatureFits (limits : Bounded.Limits) (value : Signature) : Bool :=
  paramArrayFits limits value.params

def getSignature (limits : Bounded.Limits) : GetM (Signature) := do
  return Signature.mk (← getParamArray limits) (← IxIR0.getOwned) (← Decode.getBool)

theorem getSignature_spec (limits : Bounded.Limits) (value : Signature)
    (admitted : signatureFits limits value = true) :
    GetSpec (getSignature limits) (signatureBytes value) value := by
  unfold signatureFits at admitted
  have h0 := admitted
  have total := Decode.getSpecMap3 (getParamArray_spec limits value.params h0) (getOwned_spec value.result) (Decode.getBool_spec value.papSafe) Signature.mk
  simpa only [getSignature, signatureBytes] using total

def borrowLenderFits (limits : Bounded.Limits) : BorrowLender → Bool
  | .caller => true
  | .value v0 => Bounded.natFits limits v0

def getBorrowLenderTag (limits : Bounded.Limits) : UInt8 → GetM (BorrowLender)
  | 0 => pure .caller
  | 1 => do return .value (← Bounded.getNat limits)
  | tag => throw s!"IxIR2 borrowLender: invalid tag {tag}"

def getBorrowLender (limits : Bounded.Limits) : GetM (BorrowLender) := do
  getBorrowLenderTag limits (← getU8)

theorem getBorrowLender_spec (limits : Bounded.Limits) : ∀ value : BorrowLender,
    borrowLenderFits limits value = true → GetSpec (getBorrowLender limits) (borrowLenderBytes value) value
  | .caller, admitted => by
      have payload : GetSpec (getBorrowLenderTag limits 0) ByteArray.empty (.caller : BorrowLender) :=
        GetSpec.pure (.caller : BorrowLender)
      have total := GetSpec.bind (next := getBorrowLenderTag limits)
        (Decode.getU8_tag_spec 0) payload
      simpa only [getBorrowLender, borrowLenderBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .value v0, admitted => by
      change (Bounded.natFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (Bounded.getNat_spec limits v0 h0) BorrowLender.value
      have total := GetSpec.bind (next := getBorrowLenderTag limits)
        (Decode.getU8_tag_spec 1) payload
      simpa only [getBorrowLender, borrowLenderBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total

def valueCapFits (limits : Bounded.Limits) : ValueCap → Bool
  | .scalar => true
  | .owned _ => true
  | .borrowed _ v1 => borrowLenderFits limits v1

def getValueCapTag (limits : Bounded.Limits) : UInt8 → GetM (ValueCap)
  | 0 => pure .scalar
  | 1 => do return .owned (← IxIR0.getOwned)
  | 2 => do return .borrowed (← IxIR0.getOwned) (← getBorrowLender limits)
  | tag => throw s!"IxIR2 valueCap: invalid tag {tag}"

def getValueCap (limits : Bounded.Limits) : GetM (ValueCap) := do
  getValueCapTag limits (← getU8)

theorem getValueCap_spec (limits : Bounded.Limits) : ∀ value : ValueCap,
    valueCapFits limits value = true → GetSpec (getValueCap limits) (valueCapBytes value) value
  | .scalar, admitted => by
      have payload : GetSpec (getValueCapTag limits 0) ByteArray.empty (.scalar : ValueCap) :=
        GetSpec.pure (.scalar : ValueCap)
      have total := GetSpec.bind (next := getValueCapTag limits)
        (Decode.getU8_tag_spec 0) payload
      simpa only [getValueCap, valueCapBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .owned v0, admitted => by
      have payload := Decode.getSpecMap (getOwned_spec v0) ValueCap.owned
      have total := GetSpec.bind (next := getValueCapTag limits)
        (Decode.getU8_tag_spec 1) payload
      simpa only [getValueCap, valueCapBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .borrowed v0 v1, admitted => by
      change (borrowLenderFits limits v1) = true at admitted
      have h1 := admitted
      have payload := Decode.getSpecMap2 (getOwned_spec v0) (getBorrowLender_spec limits v1 h1) ValueCap.borrowed
      have total := GetSpec.bind (next := getValueCapTag limits)
        (Decode.getU8_tag_spec 2) payload
      simpa only [getValueCap, valueCapBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total

def getCreditCapTag : UInt8 → GetM (CreditCap)
  | 0 => do return .required (← Decode.getAddress)
  | 1 => do return .optional (← Decode.getAddress)
  | tag => throw s!"IxIR2 creditCap: invalid tag {tag}"

def getCreditCap : GetM (CreditCap) := do
  getCreditCapTag (← getU8)

theorem getCreditCap_spec : ∀ value : CreditCap,
    GetSpec (getCreditCap) (creditCapBytes value) value
  | .required v0 => by
      have payload := Decode.getSpecMap (Decode.getAddress_spec v0) CreditCap.required
      have total := GetSpec.bind (next := getCreditCapTag)
        (Decode.getU8_tag_spec 0) payload
      simpa only [getCreditCap, creditCapBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .optional v0 => by
      have payload := Decode.getSpecMap (Decode.getAddress_spec v0) CreditCap.optional
      have total := GetSpec.bind (next := getCreditCapTag)
        (Decode.getU8_tag_spec 1) payload
      simpa only [getCreditCap, creditCapBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total

def ctorIdFits (limits : Bounded.Limits) (value : CtorId) : Bool :=
  Bounded.natFits limits value.indIdx && (Bounded.natFits limits value.cidx)

def getCtorId (limits : Bounded.Limits) : GetM (CtorId) := do
  return IxIR1.CtorId.mk (← Decode.getAddress) (← Bounded.getNat limits) (← Bounded.getNat limits)

theorem getCtorId_spec (limits : Bounded.Limits) (value : CtorId)
    (admitted : ctorIdFits limits value = true) :
    GetSpec (getCtorId limits) (ctorIdBytes value) value := by
  unfold ctorIdFits at admitted
  simp only [Bool.and_eq_true] at admitted
  rcases admitted with ⟨h1, h2⟩
  have total := Decode.getSpecMap3 (Decode.getAddress_spec value.block) (Bounded.getNat_spec limits value.indIdx h1) (Bounded.getNat_spec limits value.cidx h2) IxIR1.CtorId.mk
  simpa only [getCtorId, ctorIdBytes] using total

def ownedArrayFits (limits : Bounded.Limits) (value : Array Owned) : Bool :=
  Bounded.arrayFits limits (fun _ => true) value

def getOwnedArray (limits : Bounded.Limits) : GetM (Array Owned) :=
  Bounded.getArray limits (IxIR0.getOwned)

theorem getOwnedArray_spec (limits : Bounded.Limits) (value : Array Owned)
    (admitted : ownedArrayFits limits value = true) :
    GetSpec (getOwnedArray limits) (ownedArrayBytes value) value := by
  exact Bounded.getArray_spec limits (IxIR0.getOwned) ownedBytes (fun _ => true)
    (fun value _ => getOwned_spec value) value admitted

def ctorSchemaFits (limits : Bounded.Limits) (value : CtorSchema) : Bool :=
  ownedArrayFits limits value.fields

def getCtorSchema (limits : Bounded.Limits) : GetM (CtorSchema) := do
  return CtorSchema.mk (← Decode.getAddress) (← getOwnedArray limits)

theorem getCtorSchema_spec (limits : Bounded.Limits) (value : CtorSchema)
    (admitted : ctorSchemaFits limits value = true) :
    GetSpec (getCtorSchema limits) (ctorSchemaBytes value) value := by
  unfold ctorSchemaFits at admitted
  have h1 := admitted
  have total := Decode.getSpecMap2 (Decode.getAddress_spec value.layout) (getOwnedArray_spec limits value.fields h1) CtorSchema.mk
  simpa only [getCtorSchema, ctorSchemaBytes] using total

def atomArrayFits (limits : Bounded.Limits) (value : Array Atom) : Bool :=
  Bounded.arrayFits limits (atomFits limits) value

def getAtomArray (limits : Bounded.Limits) : GetM (Array Atom) :=
  Bounded.getArray limits (getAtom limits)

theorem getAtomArray_spec (limits : Bounded.Limits) (value : Array Atom)
    (admitted : atomArrayFits limits value = true) :
    GetSpec (getAtomArray limits) (atomArrayBytes value) value := by
  exact Bounded.getArray_spec limits (getAtom limits) atomBytes (atomFits limits)
    (fun value h => getAtom_spec limits value h) value admitted

def instrFits (limits : Bounded.Limits) : Instr → Bool
  | .move v0 => atomFits limits v0
  | .alloc _ v1 v2 => ctorIdFits limits v1 && (atomArrayFits limits v2)
  | .allocWith v0 _ v2 v3 => Bounded.natFits limits v0 && (ctorIdFits limits v2 && (atomArrayFits limits v3))
  | .discardCredit v0 => Bounded.natFits limits v0
  | .takeUnique v0 v1 => atomFits limits v0 && (ctorIdFits limits v1)
  | .resetShared v0 v1 => atomFits limits v0 && (ctorIdFits limits v1)
  | .retainShared v0 => atomFits limits v0
  | .releaseShared v0 => atomFits limits v0
  | .dropUnique v0 => atomFits limits v0
  | .freeUnique v0 v1 => atomFits limits v0 && (ctorIdFits limits v1)
  | .fetch v0 v1 v2 => atomFits limits v0 && (ctorIdFits limits v1 && (Bounded.natFits limits v2))
  | .call _ v1 => atomArrayFits limits v1
  | .callSelf v0 => atomArrayFits limits v0
  | .papp _ v1 => atomArrayFits limits v1
  | .apply v0 v1 => atomFits limits v0 && (atomArrayFits limits v1)
  | .extern _ v1 => atomArrayFits limits v1

def getInstrTag (limits : Bounded.Limits) : UInt8 → GetM (Instr)
  | 0 => do return .move (← getAtom limits)
  | 1 => do return .alloc (← IxIR0.getOwned) (← getCtorId limits) (← getAtomArray limits)
  | 2 => do return .allocWith (← Bounded.getNat limits) (← IxIR0.getOwned) (← getCtorId limits) (← getAtomArray limits)
  | 3 => do return .discardCredit (← Bounded.getNat limits)
  | 4 => do return .takeUnique (← getAtom limits) (← getCtorId limits)
  | 5 => do return .resetShared (← getAtom limits) (← getCtorId limits)
  | 6 => do return .retainShared (← getAtom limits)
  | 7 => do return .releaseShared (← getAtom limits)
  | 8 => do return .dropUnique (← getAtom limits)
  | 9 => do return .freeUnique (← getAtom limits) (← getCtorId limits)
  | 10 => do return .fetch (← getAtom limits) (← getCtorId limits) (← Bounded.getNat limits)
  | 11 => do return .call (← Decode.getAddress) (← getAtomArray limits)
  | 12 => do return .callSelf (← getAtomArray limits)
  | 13 => do return .papp (← Decode.getAddress) (← getAtomArray limits)
  | 14 => do return .apply (← getAtom limits) (← getAtomArray limits)
  | 15 => do return .extern (← Decode.getAddress) (← getAtomArray limits)
  | tag => throw s!"IxIR2 instr: invalid tag {tag}"

def getInstr (limits : Bounded.Limits) : GetM (Instr) := do
  getInstrTag limits (← getU8)

theorem getInstr_spec (limits : Bounded.Limits) : ∀ value : Instr,
    instrFits limits value = true → GetSpec (getInstr limits) (instrBytes value) value
  | .move v0, admitted => by
      change (atomFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (getAtom_spec limits v0 h0) Instr.move
      have total := GetSpec.bind (next := getInstrTag limits)
        (Decode.getU8_tag_spec 0) payload
      simpa only [getInstr, instrBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .alloc v0 v1 v2, admitted => by
      change (ctorIdFits limits v1 && (atomArrayFits limits v2)) = true at admitted
      simp only [Bool.and_eq_true] at admitted
      rcases admitted with ⟨h1, h2⟩
      have payload := Decode.getSpecMap3 (getOwned_spec v0) (getCtorId_spec limits v1 h1) (getAtomArray_spec limits v2 h2) Instr.alloc
      have total := GetSpec.bind (next := getInstrTag limits)
        (Decode.getU8_tag_spec 1) payload
      simpa only [getInstr, instrBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .allocWith v0 v1 v2 v3, admitted => by
      change (Bounded.natFits limits v0 && (ctorIdFits limits v2 && (atomArrayFits limits v3))) = true at admitted
      simp only [Bool.and_eq_true] at admitted
      rcases admitted with ⟨h0, h2, h3⟩
      have payload := Decode.getSpecMap4 (Bounded.getNat_spec limits v0 h0) (getOwned_spec v1) (getCtorId_spec limits v2 h2) (getAtomArray_spec limits v3 h3) Instr.allocWith
      have total := GetSpec.bind (next := getInstrTag limits)
        (Decode.getU8_tag_spec 2) payload
      simpa only [getInstr, instrBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .discardCredit v0, admitted => by
      change (Bounded.natFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (Bounded.getNat_spec limits v0 h0) Instr.discardCredit
      have total := GetSpec.bind (next := getInstrTag limits)
        (Decode.getU8_tag_spec 3) payload
      simpa only [getInstr, instrBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .takeUnique v0 v1, admitted => by
      change (atomFits limits v0 && (ctorIdFits limits v1)) = true at admitted
      simp only [Bool.and_eq_true] at admitted
      rcases admitted with ⟨h0, h1⟩
      have payload := Decode.getSpecMap2 (getAtom_spec limits v0 h0) (getCtorId_spec limits v1 h1) Instr.takeUnique
      have total := GetSpec.bind (next := getInstrTag limits)
        (Decode.getU8_tag_spec 4) payload
      simpa only [getInstr, instrBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .resetShared v0 v1, admitted => by
      change (atomFits limits v0 && (ctorIdFits limits v1)) = true at admitted
      simp only [Bool.and_eq_true] at admitted
      rcases admitted with ⟨h0, h1⟩
      have payload := Decode.getSpecMap2 (getAtom_spec limits v0 h0) (getCtorId_spec limits v1 h1) Instr.resetShared
      have total := GetSpec.bind (next := getInstrTag limits)
        (Decode.getU8_tag_spec 5) payload
      simpa only [getInstr, instrBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .retainShared v0, admitted => by
      change (atomFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (getAtom_spec limits v0 h0) Instr.retainShared
      have total := GetSpec.bind (next := getInstrTag limits)
        (Decode.getU8_tag_spec 6) payload
      simpa only [getInstr, instrBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .releaseShared v0, admitted => by
      change (atomFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (getAtom_spec limits v0 h0) Instr.releaseShared
      have total := GetSpec.bind (next := getInstrTag limits)
        (Decode.getU8_tag_spec 7) payload
      simpa only [getInstr, instrBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .dropUnique v0, admitted => by
      change (atomFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (getAtom_spec limits v0 h0) Instr.dropUnique
      have total := GetSpec.bind (next := getInstrTag limits)
        (Decode.getU8_tag_spec 8) payload
      simpa only [getInstr, instrBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .freeUnique v0 v1, admitted => by
      change (atomFits limits v0 && (ctorIdFits limits v1)) = true at admitted
      simp only [Bool.and_eq_true] at admitted
      rcases admitted with ⟨h0, h1⟩
      have payload := Decode.getSpecMap2 (getAtom_spec limits v0 h0) (getCtorId_spec limits v1 h1) Instr.freeUnique
      have total := GetSpec.bind (next := getInstrTag limits)
        (Decode.getU8_tag_spec 9) payload
      simpa only [getInstr, instrBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .fetch v0 v1 v2, admitted => by
      change (atomFits limits v0 && (ctorIdFits limits v1 && (Bounded.natFits limits v2))) = true at admitted
      simp only [Bool.and_eq_true] at admitted
      rcases admitted with ⟨h0, h1, h2⟩
      have payload := Decode.getSpecMap3 (getAtom_spec limits v0 h0) (getCtorId_spec limits v1 h1) (Bounded.getNat_spec limits v2 h2) Instr.fetch
      have total := GetSpec.bind (next := getInstrTag limits)
        (Decode.getU8_tag_spec 10) payload
      simpa only [getInstr, instrBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .call v0 v1, admitted => by
      change (atomArrayFits limits v1) = true at admitted
      have h1 := admitted
      have payload := Decode.getSpecMap2 (Decode.getAddress_spec v0) (getAtomArray_spec limits v1 h1) Instr.call
      have total := GetSpec.bind (next := getInstrTag limits)
        (Decode.getU8_tag_spec 11) payload
      simpa only [getInstr, instrBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .callSelf v0, admitted => by
      change (atomArrayFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (getAtomArray_spec limits v0 h0) Instr.callSelf
      have total := GetSpec.bind (next := getInstrTag limits)
        (Decode.getU8_tag_spec 12) payload
      simpa only [getInstr, instrBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .papp v0 v1, admitted => by
      change (atomArrayFits limits v1) = true at admitted
      have h1 := admitted
      have payload := Decode.getSpecMap2 (Decode.getAddress_spec v0) (getAtomArray_spec limits v1 h1) Instr.papp
      have total := GetSpec.bind (next := getInstrTag limits)
        (Decode.getU8_tag_spec 13) payload
      simpa only [getInstr, instrBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .apply v0 v1, admitted => by
      change (atomFits limits v0 && (atomArrayFits limits v1)) = true at admitted
      simp only [Bool.and_eq_true] at admitted
      rcases admitted with ⟨h0, h1⟩
      have payload := Decode.getSpecMap2 (getAtom_spec limits v0 h0) (getAtomArray_spec limits v1 h1) Instr.apply
      have total := GetSpec.bind (next := getInstrTag limits)
        (Decode.getU8_tag_spec 14) payload
      simpa only [getInstr, instrBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .extern v0 v1, admitted => by
      change (atomArrayFits limits v1) = true at admitted
      have h1 := admitted
      have payload := Decode.getSpecMap2 (Decode.getAddress_spec v0) (getAtomArray_spec limits v1 h1) Instr.extern
      have total := GetSpec.bind (next := getInstrTag limits)
        (Decode.getU8_tag_spec 15) payload
      simpa only [getInstr, instrBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total

def natArrayFits (limits : Bounded.Limits) (value : Array Nat) : Bool :=
  Bounded.arrayFits limits (Bounded.natFits limits) value

def getNatArray (limits : Bounded.Limits) : GetM (Array Nat) :=
  Bounded.getArray limits (Bounded.getNat limits)

theorem getNatArray_spec (limits : Bounded.Limits) (value : Array Nat)
    (admitted : natArrayFits limits value = true) :
    GetSpec (getNatArray limits) (natArrayBytes value) value := by
  exact Bounded.getArray_spec limits (Bounded.getNat limits) Encoding.nat (Bounded.natFits limits)
    (fun value h => Bounded.getNat_spec limits value h) value admitted

def edgeFits (limits : Bounded.Limits) (value : Edge) : Bool :=
  Bounded.natFits limits value.target && (atomArrayFits limits value.values && (natArrayFits limits value.credits))

def getEdge (limits : Bounded.Limits) : GetM (Edge) := do
  return Edge.mk (← Bounded.getNat limits) (← getAtomArray limits) (← getNatArray limits)

theorem getEdge_spec (limits : Bounded.Limits) (value : Edge)
    (admitted : edgeFits limits value = true) :
    GetSpec (getEdge limits) (edgeBytes value) value := by
  unfold edgeFits at admitted
  simp only [Bool.and_eq_true] at admitted
  rcases admitted with ⟨h0, h1, h2⟩
  have total := Decode.getSpecMap3 (Bounded.getNat_spec limits value.target h0) (getAtomArray_spec limits value.values h1) (getNatArray_spec limits value.credits h2) Edge.mk
  simpa only [getEdge, edgeBytes] using total

def ctorAltFits (limits : Bounded.Limits) (value : CtorAlt) : Bool :=
  ctorIdFits limits value.cid && (edgeFits limits value.edge)

def getCtorAlt (limits : Bounded.Limits) : GetM (CtorAlt) := do
  return CtorAlt.mk (← getCtorId limits) (← getEdge limits)

theorem getCtorAlt_spec (limits : Bounded.Limits) (value : CtorAlt)
    (admitted : ctorAltFits limits value = true) :
    GetSpec (getCtorAlt limits) (ctorAltBytes value) value := by
  unfold ctorAltFits at admitted
  simp only [Bool.and_eq_true] at admitted
  rcases admitted with ⟨h0, h1⟩
  have total := Decode.getSpecMap2 (getCtorId_spec limits value.cid h0) (getEdge_spec limits value.edge h1) CtorAlt.mk
  simpa only [getCtorAlt, ctorAltBytes] using total

def natPeelFits (limits : Bounded.Limits) (value : NatPeel) : Bool :=
  edgeFits limits value.zero && (edgeFits limits value.succ)

def getNatPeel (limits : Bounded.Limits) : GetM (NatPeel) := do
  return NatPeel.mk (← getEdge limits) (← getEdge limits)

theorem getNatPeel_spec (limits : Bounded.Limits) (value : NatPeel)
    (admitted : natPeelFits limits value = true) :
    GetSpec (getNatPeel limits) (natPeelBytes value) value := by
  unfold natPeelFits at admitted
  simp only [Bool.and_eq_true] at admitted
  rcases admitted with ⟨h0, h1⟩
  have total := Decode.getSpecMap2 (getEdge_spec limits value.zero h0) (getEdge_spec limits value.succ h1) NatPeel.mk
  simpa only [getNatPeel, natPeelBytes] using total

def peelOptionFits (limits : Bounded.Limits) : Option NatPeel → Bool
  | .none => true
  | .some v0 => natPeelFits limits v0

def getPeelOptionTag (limits : Bounded.Limits) : UInt8 → GetM (Option NatPeel)
  | 0 => pure .none
  | 1 => do return .some (← getNatPeel limits)
  | tag => throw s!"IxIR2 peelOption: invalid tag {tag}"

def getPeelOption (limits : Bounded.Limits) : GetM (Option NatPeel) := do
  getPeelOptionTag limits (← getU8)

theorem getPeelOption_spec (limits : Bounded.Limits) : ∀ value : Option NatPeel,
    peelOptionFits limits value = true → GetSpec (getPeelOption limits) (peelOptionBytes value) value
  | .none, admitted => by
      have payload : GetSpec (getPeelOptionTag limits 0) ByteArray.empty (.none : Option NatPeel) :=
        GetSpec.pure (.none : Option NatPeel)
      have total := GetSpec.bind (next := getPeelOptionTag limits)
        (Decode.getU8_tag_spec 0) payload
      simpa only [getPeelOption, peelOptionBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .some v0, admitted => by
      change (natPeelFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (getNatPeel_spec limits v0 h0) Option.some
      have total := GetSpec.bind (next := getPeelOptionTag limits)
        (Decode.getU8_tag_spec 1) payload
      simpa only [getPeelOption, peelOptionBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total

def ctorAltArrayFits (limits : Bounded.Limits) (value : Array CtorAlt) : Bool :=
  Bounded.arrayFits limits (ctorAltFits limits) value

def getCtorAltArray (limits : Bounded.Limits) : GetM (Array CtorAlt) :=
  Bounded.getArray limits (getCtorAlt limits)

theorem getCtorAltArray_spec (limits : Bounded.Limits) (value : Array CtorAlt)
    (admitted : ctorAltArrayFits limits value = true) :
    GetSpec (getCtorAltArray limits) (ctorAltArrayBytes value) value := by
  exact Bounded.getArray_spec limits (getCtorAlt limits) ctorAltBytes (ctorAltFits limits)
    (fun value h => getCtorAlt_spec limits value h) value admitted

def terminatorFits (limits : Bounded.Limits) : Terminator → Bool
  | .jump v0 => edgeFits limits v0
  | .switchValue v0 v1 v2 => atomFits limits v0 && (ctorAltArrayFits limits v1 && (peelOptionFits limits v2))
  | .branchCredit v0 v1 v2 => Bounded.natFits limits v0 && (edgeFits limits v1 && (edgeFits limits v2))
  | .ret v0 => atomFits limits v0
  | .tailCall _ v1 => atomArrayFits limits v1
  | .tailCallSelf v0 => atomArrayFits limits v0

def getTerminatorTag (limits : Bounded.Limits) : UInt8 → GetM (Terminator)
  | 0 => do return .jump (← getEdge limits)
  | 1 => do return .switchValue (← getAtom limits) (← getCtorAltArray limits) (← getPeelOption limits)
  | 2 => do return .branchCredit (← Bounded.getNat limits) (← getEdge limits) (← getEdge limits)
  | 3 => do return .ret (← getAtom limits)
  | 4 => do return .tailCall (← Decode.getAddress) (← getAtomArray limits)
  | 5 => do return .tailCallSelf (← getAtomArray limits)
  | tag => throw s!"IxIR2 terminator: invalid tag {tag}"

def getTerminator (limits : Bounded.Limits) : GetM (Terminator) := do
  getTerminatorTag limits (← getU8)

theorem getTerminator_spec (limits : Bounded.Limits) : ∀ value : Terminator,
    terminatorFits limits value = true → GetSpec (getTerminator limits) (terminatorBytes value) value
  | .jump v0, admitted => by
      change (edgeFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (getEdge_spec limits v0 h0) Terminator.jump
      have total := GetSpec.bind (next := getTerminatorTag limits)
        (Decode.getU8_tag_spec 0) payload
      simpa only [getTerminator, terminatorBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .switchValue v0 v1 v2, admitted => by
      change (atomFits limits v0 && (ctorAltArrayFits limits v1 && (peelOptionFits limits v2))) = true at admitted
      simp only [Bool.and_eq_true] at admitted
      rcases admitted with ⟨h0, h1, h2⟩
      have payload := Decode.getSpecMap3 (getAtom_spec limits v0 h0) (getCtorAltArray_spec limits v1 h1) (getPeelOption_spec limits v2 h2) Terminator.switchValue
      have total := GetSpec.bind (next := getTerminatorTag limits)
        (Decode.getU8_tag_spec 1) payload
      simpa only [getTerminator, terminatorBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .branchCredit v0 v1 v2, admitted => by
      change (Bounded.natFits limits v0 && (edgeFits limits v1 && (edgeFits limits v2))) = true at admitted
      simp only [Bool.and_eq_true] at admitted
      rcases admitted with ⟨h0, h1, h2⟩
      have payload := Decode.getSpecMap3 (Bounded.getNat_spec limits v0 h0) (getEdge_spec limits v1 h1) (getEdge_spec limits v2 h2) Terminator.branchCredit
      have total := GetSpec.bind (next := getTerminatorTag limits)
        (Decode.getU8_tag_spec 2) payload
      simpa only [getTerminator, terminatorBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .ret v0, admitted => by
      change (atomFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (getAtom_spec limits v0 h0) Terminator.ret
      have total := GetSpec.bind (next := getTerminatorTag limits)
        (Decode.getU8_tag_spec 3) payload
      simpa only [getTerminator, terminatorBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .tailCall v0 v1, admitted => by
      change (atomArrayFits limits v1) = true at admitted
      have h1 := admitted
      have payload := Decode.getSpecMap2 (Decode.getAddress_spec v0) (getAtomArray_spec limits v1 h1) Terminator.tailCall
      have total := GetSpec.bind (next := getTerminatorTag limits)
        (Decode.getU8_tag_spec 4) payload
      simpa only [getTerminator, terminatorBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .tailCallSelf v0, admitted => by
      change (atomArrayFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (getAtomArray_spec limits v0 h0) Terminator.tailCallSelf
      have total := GetSpec.bind (next := getTerminatorTag limits)
        (Decode.getU8_tag_spec 5) payload
      simpa only [getTerminator, terminatorBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total

def valueCapArrayFits (limits : Bounded.Limits) (value : Array ValueCap) : Bool :=
  Bounded.arrayFits limits (valueCapFits limits) value

def getValueCapArray (limits : Bounded.Limits) : GetM (Array ValueCap) :=
  Bounded.getArray limits (getValueCap limits)

theorem getValueCapArray_spec (limits : Bounded.Limits) (value : Array ValueCap)
    (admitted : valueCapArrayFits limits value = true) :
    GetSpec (getValueCapArray limits) (valueCapArrayBytes value) value := by
  exact Bounded.getArray_spec limits (getValueCap limits) valueCapBytes (valueCapFits limits)
    (fun value h => getValueCap_spec limits value h) value admitted

def creditCapArrayFits (limits : Bounded.Limits) (value : Array CreditCap) : Bool :=
  Bounded.arrayFits limits (fun _ => true) value

def getCreditCapArray (limits : Bounded.Limits) : GetM (Array CreditCap) :=
  Bounded.getArray limits (getCreditCap)

theorem getCreditCapArray_spec (limits : Bounded.Limits) (value : Array CreditCap)
    (admitted : creditCapArrayFits limits value = true) :
    GetSpec (getCreditCapArray limits) (creditCapArrayBytes value) value := by
  exact Bounded.getArray_spec limits (getCreditCap) creditCapBytes (fun _ => true)
    (fun value _ => getCreditCap_spec value) value admitted

def instrArrayFits (limits : Bounded.Limits) (value : Array Instr) : Bool :=
  Bounded.arrayFits limits (instrFits limits) value

def getInstrArray (limits : Bounded.Limits) : GetM (Array Instr) :=
  Bounded.getArray limits (getInstr limits)

theorem getInstrArray_spec (limits : Bounded.Limits) (value : Array Instr)
    (admitted : instrArrayFits limits value = true) :
    GetSpec (getInstrArray limits) (instrArrayBytes value) value := by
  exact Bounded.getArray_spec limits (getInstr limits) instrBytes (instrFits limits)
    (fun value h => getInstr_spec limits value h) value admitted

def blockFits (limits : Bounded.Limits) (value : Block) : Bool :=
  valueCapArrayFits limits value.valueParams && (creditCapArrayFits limits value.creditParams && (instrArrayFits limits value.instructions && (terminatorFits limits value.terminator)))

def getBlock (limits : Bounded.Limits) : GetM (Block) := do
  return Block.mk (← getValueCapArray limits) (← getCreditCapArray limits) (← getInstrArray limits) (← getTerminator limits)

theorem getBlock_spec (limits : Bounded.Limits) (value : Block)
    (admitted : blockFits limits value = true) :
    GetSpec (getBlock limits) (blockBytes value) value := by
  unfold blockFits at admitted
  simp only [Bool.and_eq_true] at admitted
  rcases admitted with ⟨h0, h1, h2, h3⟩
  have total := Decode.getSpecMap4 (getValueCapArray_spec limits value.valueParams h0) (getCreditCapArray_spec limits value.creditParams h1) (getInstrArray_spec limits value.instructions h2) (getTerminator_spec limits value.terminator h3) Block.mk
  simpa only [getBlock, blockBytes] using total

def blockArrayFits (limits : Bounded.Limits) (value : Array Block) : Bool :=
  Bounded.arrayFits limits (blockFits limits) value

def getBlockArray (limits : Bounded.Limits) : GetM (Array Block) :=
  Bounded.getArray limits (getBlock limits)

theorem getBlockArray_spec (limits : Bounded.Limits) (value : Array Block)
    (admitted : blockArrayFits limits value = true) :
    GetSpec (getBlockArray limits) (blockArrayBytes value) value := by
  exact Bounded.getArray_spec limits (getBlock limits) blockBytes (blockFits limits)
    (fun value h => getBlock_spec limits value h) value admitted

def functionFits (limits : Bounded.Limits) (value : Function) : Bool :=
  signatureFits limits value.signature && (blockArrayFits limits value.blocks)

def getFunction (limits : Bounded.Limits) : GetM (Function) := do
  return Function.mk (← getSignature limits) (← getBlockArray limits)

theorem getFunction_spec (limits : Bounded.Limits) (value : Function)
    (admitted : functionFits limits value = true) :
    GetSpec (getFunction limits) (functionBytes value) value := by
  unfold functionFits at admitted
  simp only [Bool.and_eq_true] at admitted
  rcases admitted with ⟨h0, h1⟩
  have total := Decode.getSpecMap2 (getSignature_spec limits value.signature h0) (getBlockArray_spec limits value.blocks h1) Function.mk
  simpa only [getFunction, functionBytes] using total

def declFits (limits : Bounded.Limits) : Decl → Bool
  | .fn v0 => functionFits limits v0
  | .extern v0 => Bounded.natFits limits v0

def getDeclTag (limits : Bounded.Limits) : UInt8 → GetM (Decl)
  | 0 => do return .fn (← getFunction limits)
  | 1 => do return .extern (← Bounded.getNat limits)
  | tag => throw s!"IxIR2 decl: invalid tag {tag}"

def getDecl (limits : Bounded.Limits) : GetM (Decl) := do
  getDeclTag limits (← getU8)

theorem getDecl_spec (limits : Bounded.Limits) : ∀ value : Decl,
    declFits limits value = true → GetSpec (getDecl limits) (declBytes value) value
  | .fn v0, admitted => by
      change (functionFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (getFunction_spec limits v0 h0) Decl.fn
      have total := GetSpec.bind (next := getDeclTag limits)
        (Decode.getU8_tag_spec 0) payload
      simpa only [getDecl, declBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .extern v0, admitted => by
      change (Bounded.natFits limits v0) = true at admitted
      have h0 := admitted
      have payload := Decode.getSpecMap (Bounded.getNat_spec limits v0 h0) Decl.extern
      have total := GetSpec.bind (next := getDeclTag limits)
        (Decode.getU8_tag_spec 1) payload
      simpa only [getDecl, declBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total

def declEntryFits (limits : Bounded.Limits) (value : Address × Decl) : Bool :=
  declFits limits value.2

def getDeclEntry (limits : Bounded.Limits) : GetM (Address × Decl) := do
  return Prod.mk (← Decode.getAddress) (← getDecl limits)

theorem getDeclEntry_spec (limits : Bounded.Limits) (value : Address × Decl)
    (admitted : declEntryFits limits value = true) :
    GetSpec (getDeclEntry limits) (declEntryBytes value) value := by
  unfold declEntryFits at admitted
  have h1 := admitted
  have total := Decode.getSpecMap2 (Decode.getAddress_spec value.1) (getDecl_spec limits value.2 h1) Prod.mk
  simpa only [getDeclEntry, declEntryBytes] using total

def declEntryListFits (limits : Bounded.Limits) (value : List (Address × Decl)) : Bool :=
  Bounded.listFits limits (declEntryFits limits) value

def getDeclEntryList (limits : Bounded.Limits) : GetM (List (Address × Decl)) :=
  Bounded.getList limits (getDeclEntry limits)

theorem getDeclEntryList_spec (limits : Bounded.Limits) (value : List (Address × Decl))
    (admitted : declEntryListFits limits value = true) :
    GetSpec (getDeclEntryList limits) (declEntryListBytes value) value := by
  exact Bounded.getList_spec limits (getDeclEntry limits) declEntryBytes (declEntryFits limits)
    (fun value h => getDeclEntry_spec limits value h) value admitted

def programFits (limits : Bounded.Limits) (value : Program) : Bool :=
  declEntryListFits limits value.declarations && (functionFits limits value.main)

def getProgram (limits : Bounded.Limits) : GetM (Program) := do
  return Program.mk (← getDeclEntryList limits) (← getFunction limits)

theorem getProgram_spec (limits : Bounded.Limits) (value : Program)
    (admitted : programFits limits value = true) :
    GetSpec (getProgram limits) (programBytes value) value := by
  unfold programFits at admitted
  simp only [Bool.and_eq_true] at admitted
  rcases admitted with ⟨h0, h1⟩
  have total := Decode.getSpecMap2 (getDeclEntryList_spec limits value.declarations h0) (getFunction_spec limits value.main h1) Program.mk
  simpa only [getProgram, programBytes] using total

def getCreditPolicyTag : UInt8 → GetM (CreditPolicy)
  | 0 => pure .callLocalV0
  | 1 => pure .suspendedCallsV1
  | tag => throw s!"IxIR2 creditPolicy: invalid tag {tag}"

def getCreditPolicy : GetM (CreditPolicy) := do
  getCreditPolicyTag (← getU8)

theorem getCreditPolicy_spec : ∀ value : CreditPolicy,
    GetSpec (getCreditPolicy) (creditPolicyBytes value) value
  | .callLocalV0 => by
      have payload : GetSpec (getCreditPolicyTag 0) ByteArray.empty (.callLocalV0 : CreditPolicy) :=
        GetSpec.pure (.callLocalV0 : CreditPolicy)
      have total := GetSpec.bind (next := getCreditPolicyTag)
        (Decode.getU8_tag_spec 0) payload
      simpa only [getCreditPolicy, creditPolicyBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .suspendedCallsV1 => by
      have payload : GetSpec (getCreditPolicyTag 1) ByteArray.empty (.suspendedCallsV1 : CreditPolicy) :=
        GetSpec.pure (.suspendedCallsV1 : CreditPolicy)
      have total := GetSpec.bind (next := getCreditPolicyTag)
        (Decode.getU8_tag_spec 1) payload
      simpa only [getCreditPolicy, creditPolicyBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total

def getOwnerTag : UInt8 → GetM (Validate.Owner)
  | 0 => pure .main
  | 1 => do return .declaration (← Decode.getAddress)
  | tag => throw s!"IxIR2 owner: invalid tag {tag}"

def getOwner : GetM (Validate.Owner) := do
  getOwnerTag (← getU8)

theorem getOwner_spec : ∀ value : Validate.Owner,
    GetSpec (getOwner) (ownerBytes value) value
  | .main => by
      have payload : GetSpec (getOwnerTag 0) ByteArray.empty (.main : Validate.Owner) :=
        GetSpec.pure (.main : Validate.Owner)
      have total := GetSpec.bind (next := getOwnerTag)
        (Decode.getU8_tag_spec 0) payload
      simpa only [getOwner, ownerBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total
  | .declaration v0 => by
      have payload := Decode.getSpecMap (Decode.getAddress_spec v0) Validate.Owner.declaration
      have total := GetSpec.bind (next := getOwnerTag)
        (Decode.getU8_tag_spec 1) payload
      simpa only [getOwner, ownerBytes, ByteArray.append_assoc,
        ByteArray.append_empty] using total

def scalarLeafFits (limits : Bounded.Limits) (value : Validate.ScalarLeafFact) : Bool :=
  Bounded.natFits limits value.block && (Bounded.natFits limits value.value && (ctorIdFits limits value.cid))

def getScalarLeaf (limits : Bounded.Limits) : GetM (Validate.ScalarLeafFact) := do
  return Validate.ScalarLeafFact.mk (← getOwner) (← Bounded.getNat limits) (← Bounded.getNat limits) (← getCtorId limits)

theorem getScalarLeaf_spec (limits : Bounded.Limits) (value : Validate.ScalarLeafFact)
    (admitted : scalarLeafFits limits value = true) :
    GetSpec (getScalarLeaf limits) (scalarLeafBytes value) value := by
  unfold scalarLeafFits at admitted
  simp only [Bool.and_eq_true] at admitted
  rcases admitted with ⟨h1, h2, h3⟩
  have total := Decode.getSpecMap4 (getOwner_spec value.owner) (Bounded.getNat_spec limits value.block h1) (Bounded.getNat_spec limits value.value h2) (getCtorId_spec limits value.cid h3) Validate.ScalarLeafFact.mk
  simpa only [getScalarLeaf, scalarLeafBytes] using total

def strArrayFits (limits : Bounded.Limits) (value : Array String) : Bool :=
  Bounded.arrayFits limits (Bounded.stringFits limits) value

def getStrArray (limits : Bounded.Limits) : GetM (Array String) :=
  Bounded.getArray limits (Bounded.getString limits)

theorem getStrArray_spec (limits : Bounded.Limits) (value : Array String)
    (admitted : strArrayFits limits value = true) :
    GetSpec (getStrArray limits) (strArrayBytes value) value := by
  exact Bounded.getArray_spec limits (Bounded.getString limits) Encoding.string (Bounded.stringFits limits)
    (fun value h => Bounded.getString_spec limits value h) value admitted

def policyFits (limits : Bounded.Limits) (value : Policy) : Bool :=
  Bounded.stringFits limits value.semantics && (Bounded.stringFits limits value.validator && (Bounded.stringFits limits value.lowering && (strArrayFits limits value.passes && (Bounded.stringFits limits value.layout))))

def getPolicy (limits : Bounded.Limits) : GetM (Policy) := do
  return Policy.mk (← Bounded.getString limits) (← Bounded.getString limits) (← Bounded.getString limits) (← getStrArray limits) (← Bounded.getString limits) (← getCreditPolicy) (← Decode.getBool)

theorem getPolicy_spec (limits : Bounded.Limits) (value : Policy)
    (admitted : policyFits limits value = true) :
    GetSpec (getPolicy limits) (policyBytes value) value := by
  unfold policyFits at admitted
  simp only [Bool.and_eq_true] at admitted
  rcases admitted with ⟨h0, h1, h2, h3, h4⟩
  have total := Bounded.getSpecMap7 (Bounded.getString_spec limits value.semantics h0) (Bounded.getString_spec limits value.validator h1) (Bounded.getString_spec limits value.lowering h2) (getStrArray_spec limits value.passes h3) (Bounded.getString_spec limits value.layout h4) (getCreditPolicy_spec value.credits) (Decode.getBool_spec value.allowExtern) Policy.mk
  simpa only [getPolicy, policyBytes] using total

def dependencyFits (limits : Bounded.Limits) (value : Dependency) : Bool :=
  Bounded.stringFits limits value.role

def getDependency (limits : Bounded.Limits) : GetM (Dependency) := do
  return Dependency.mk (← Bounded.getString limits) (← Decode.getAddress)

theorem getDependency_spec (limits : Bounded.Limits) (value : Dependency)
    (admitted : dependencyFits limits value = true) :
    GetSpec (getDependency limits) (dependencyBytes value) value := by
  unfold dependencyFits at admitted
  have h0 := admitted
  have total := Decode.getSpecMap2 (Bounded.getString_spec limits value.role h0) (Decode.getAddress_spec value.root) Dependency.mk
  simpa only [getDependency, dependencyBytes] using total

def layoutFits (limits : Bounded.Limits) (value : Layout) : Bool :=
  Bounded.blobFits limits value.preimage

def getLayout (limits : Bounded.Limits) : GetM (Layout) := do
  return Layout.mk (← Decode.getAddress) (← Bounded.getBlob limits)

theorem getLayout_spec (limits : Bounded.Limits) (value : Layout)
    (admitted : layoutFits limits value = true) :
    GetSpec (getLayout limits) (layoutBytes value) value := by
  unfold layoutFits at admitted
  have h1 := admitted
  have total := Decode.getSpecMap2 (Decode.getAddress_spec value.identity) (Bounded.getBlob_spec limits value.preimage h1) Layout.mk
  simpa only [getLayout, layoutBytes] using total

def schemaFits (limits : Bounded.Limits) (value : Schema) : Bool :=
  ctorIdFits limits value.constructor && (ctorSchemaFits limits value.definition)

def getSchema (limits : Bounded.Limits) : GetM (Schema) := do
  return Schema.mk (← IxIR0.getOwned) (← getCtorId limits) (← getCtorSchema limits)

theorem getSchema_spec (limits : Bounded.Limits) (value : Schema)
    (admitted : schemaFits limits value = true) :
    GetSpec (getSchema limits) (schemaBytes value) value := by
  unfold schemaFits at admitted
  simp only [Bool.and_eq_true] at admitted
  rcases admitted with ⟨h1, h2⟩
  have total := Decode.getSpecMap3 (getOwned_spec value.world) (getCtorId_spec limits value.constructor h1) (getCtorSchema_spec limits value.definition h2) Schema.mk
  simpa only [getSchema, schemaBytes] using total

def dependencyArrayFits (limits : Bounded.Limits) (value : Array Dependency) : Bool :=
  Bounded.arrayFits limits (dependencyFits limits) value

def getDependencyArray (limits : Bounded.Limits) : GetM (Array Dependency) :=
  Bounded.getArray limits (getDependency limits)

theorem getDependencyArray_spec (limits : Bounded.Limits) (value : Array Dependency)
    (admitted : dependencyArrayFits limits value = true) :
    GetSpec (getDependencyArray limits) (dependencyArrayBytes value) value := by
  exact Bounded.getArray_spec limits (getDependency limits) dependencyBytes (dependencyFits limits)
    (fun value h => getDependency_spec limits value h) value admitted

def layoutArrayFits (limits : Bounded.Limits) (value : Array Layout) : Bool :=
  Bounded.arrayFits limits (layoutFits limits) value

def getLayoutArray (limits : Bounded.Limits) : GetM (Array Layout) :=
  Bounded.getArray limits (getLayout limits)

theorem getLayoutArray_spec (limits : Bounded.Limits) (value : Array Layout)
    (admitted : layoutArrayFits limits value = true) :
    GetSpec (getLayoutArray limits) (layoutArrayBytes value) value := by
  exact Bounded.getArray_spec limits (getLayout limits) layoutBytes (layoutFits limits)
    (fun value h => getLayout_spec limits value h) value admitted

def schemaArrayFits (limits : Bounded.Limits) (value : Array Schema) : Bool :=
  Bounded.arrayFits limits (schemaFits limits) value

def getSchemaArray (limits : Bounded.Limits) : GetM (Array Schema) :=
  Bounded.getArray limits (getSchema limits)

theorem getSchemaArray_spec (limits : Bounded.Limits) (value : Array Schema)
    (admitted : schemaArrayFits limits value = true) :
    GetSpec (getSchemaArray limits) (schemaArrayBytes value) value := by
  exact Bounded.getArray_spec limits (getSchema limits) schemaBytes (schemaFits limits)
    (fun value h => getSchema_spec limits value h) value admitted

def scalarLeafArrayFits (limits : Bounded.Limits) (value : Array Validate.ScalarLeafFact) : Bool :=
  Bounded.arrayFits limits (scalarLeafFits limits) value

def getScalarLeafArray (limits : Bounded.Limits) : GetM (Array Validate.ScalarLeafFact) :=
  Bounded.getArray limits (getScalarLeaf limits)

theorem getScalarLeafArray_spec (limits : Bounded.Limits) (value : Array Validate.ScalarLeafFact)
    (admitted : scalarLeafArrayFits limits value = true) :
    GetSpec (getScalarLeafArray limits) (scalarLeafArrayBytes value) value := by
  exact Bounded.getArray_spec limits (getScalarLeaf limits) scalarLeafBytes (scalarLeafFits limits)
    (fun value h => getScalarLeaf_spec limits value h) value admitted

def artifactFits (limits : Bounded.Limits) (value : Artifact) : Bool :=
  policyFits limits value.policy && (dependencyArrayFits limits value.dependencies && (layoutArrayFits limits value.layouts && (schemaArrayFits limits value.schemas && (scalarLeafArrayFits limits value.scalarLeaves && (programFits limits value.program)))))

def getArtifact (limits : Bounded.Limits) : GetM (Artifact) := do
  return Artifact.mk (← getPolicy limits) (← getDependencyArray limits) (← getLayoutArray limits) (← getSchemaArray limits) (← getScalarLeafArray limits) (← getProgram limits)

theorem getArtifact_spec (limits : Bounded.Limits) (value : Artifact)
    (admitted : artifactFits limits value = true) :
    GetSpec (getArtifact limits) (artifactBytes value) value := by
  unfold artifactFits at admitted
  simp only [Bool.and_eq_true] at admitted
  rcases admitted with ⟨h0, h1, h2, h3, h4, h5⟩
  have total := Bounded.getSpecMap6 (getPolicy_spec limits value.policy h0) (getDependencyArray_spec limits value.dependencies h1) (getLayoutArray_spec limits value.layouts h2) (getSchemaArray_spec limits value.schemas h3) (getScalarLeafArray_spec limits value.scalarLeaves h4) (getProgram_spec limits value.program h5) Artifact.mk
  simpa only [getArtifact, artifactBytes] using total

def getPreimage (limits : Bounded.Limits) : GetM Artifact := do
  Decode.expectBytes Artifact.addressDomain
  getArtifact limits

/-- Exact representable domain for this caller's ingress limits. -/
def Artifact.Fits (limits : Bounded.Limits) (artifact : Artifact) : Prop :=
  artifact.preimage.size ≤ limits.maxBytes ∧ artifactFits limits artifact = true

def Artifact.decodePreimage (limits : Bounded.Limits) (bytes : ByteArray) : Except String Artifact :=
  Bounded.run limits (getPreimage limits) Artifact.preimage (artifactFits limits) bytes

theorem getPreimage_spec (limits : Bounded.Limits) (artifact : Artifact)
    (fits : artifactFits limits artifact = true) :
    GetSpec (getPreimage limits) artifact.preimage artifact := by
  exact GetSpec.bind (Decode.expectBytes_spec Artifact.addressDomain)
    (getArtifact_spec limits artifact fits)

theorem Artifact.decodePreimage_roundtrip (limits : Bounded.Limits) (artifact : Artifact)
    (fits : artifact.Fits limits) :
    decodePreimage limits artifact.preimage = .ok artifact :=
  Bounded.run_roundtrip limits _ _ _ artifact fits.1 fits.2
    (getPreimage_spec limits artifact fits.2)

theorem Artifact.decodePreimage_canonical (limits : Bounded.Limits)
    {bytes : ByteArray} {artifact : Artifact}
    (accepted : decodePreimage limits bytes = .ok artifact) : artifact.preimage = bytes :=
  (Bounded.run_spec limits _ _ _ accepted).1

theorem Artifact.decodePreimage_fits (limits : Bounded.Limits)
    {bytes : ByteArray} {artifact : Artifact}
    (accepted : decodePreimage limits bytes = .ok artifact) : artifact.Fits limits := by
  have spec := Bounded.run_spec limits _ _ _ accepted
  exact ⟨spec.1 ▸ spec.2.1, spec.2.2⟩

theorem Artifact.preimage_injective (limits : Bounded.Limits)
    {left right : Artifact} (leftFits : left.Fits limits) (rightFits : right.Fits limits)
    (equal : left.preimage = right.preimage) : left = right := by
  have lhs := left.decodePreimage_roundtrip limits leftFits
  rw [equal, right.decodePreimage_roundtrip limits rightFits] at lhs
  exact (Except.ok.inj lhs).symm

end Compilatrix.IxIR2.Wire
