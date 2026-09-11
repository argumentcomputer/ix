import Ix.Compiler.IxIR0.Decode
import Ix.Compiler.IxIR1.Serialize

/-!
# Strict IxIR₁ declaration decoding

The public reader consumes a complete versioned declaration preimage and
accepts only bytes reproduced exactly by the canonical encoder. Recursive
code bodies are input-fueled; case alternatives reuse the strictly smaller
fuel supplied to their enclosing `case` node.
-/

namespace Ix.Compiler.IxIR1

open Ix.Compiler.Ixon
open Ix.Compiler.IxIR
open Ix.Compiler.IxIR.Decode

def getAtomTag : UInt8 → GetM Atom
  | 0 => do return .var (← Decode.getNat)
  | 1 => do return .lit (← IxIR0.getLiteral)
  | 2 => pure .erased
  | tag => throw s!"IxIR1 atom: invalid tag {tag}"

def getAtom : GetM Atom := do
  getAtomTag (← getU8)

def getCtorId : GetM CtorId := do
  return ⟨← Decode.getAddress, ← Decode.getNat, ← Decode.getNat⟩

def getOpTag : UInt8 → GetM Op
  | 0 => do return .pure (← getAtom)
  | 1 => do
      let world ← IxIR0.getOwned
      let cid ← getCtorId
      return .alloc world cid (← Decode.getArray getAtom)
  | 2 => do
      let target ← getAtom
      let cid ← getCtorId
      return .reuse target cid (← Decode.getArray getAtom)
  | 3 => do return .free (← getAtom)
  | 4 => do return .dup (← getAtom)
  | 5 => do return .drop (← getAtom)
  | 6 => do return .dropU (← getAtom)
  | 7 => do return .fetch (← getAtom) (← Decode.getNat)
  | 8 => do
      return .call (← Decode.getAddress) (← Decode.getArray getAtom)
  | 9 => do return .callSelf (← Decode.getArray getAtom)
  | 10 => do
      return .papp (← Decode.getAddress) (← Decode.getArray getAtom)
  | 11 => do return .apply (← getAtom) (← Decode.getArray getAtom)
  | 12 => do
      return .extern (← Decode.getAddress) (← Decode.getArray getAtom)
  | tag => throw s!"IxIR1 operation: invalid tag {tag}"

def getOp : GetM Op := do
  getOpTag (← getU8)

def getAlt (recur : GetM Code) : GetM Alt := do
  return .mk (← Decode.getNat) (← Decode.getNat) (← recur)

def getCodeTag (recur : GetM Code) : UInt8 → GetM Code
  | 0 => do return .ret (← getAtom)
  | 1 => do return .letOp (← getOp) (← recur)
  | 2 => do
      let scrut ← getAtom
      let peelNat ← Decode.getBool
      return .case scrut peelNat (← Decode.getArray (getAlt recur))
  | tag => throw s!"IxIR1 code: invalid tag {tag}"

def getCodeFuel : Nat → GetM Code
  | 0 => throw "IxIR1 code: recursion limit"
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
  | tag => throw s!"IxIR1 declaration: invalid tag {tag}"

def getDeclPayload : GetM Decl := do
  getDeclTag (← getU8)

def getDeclPreimage : GetM Decl := do
  Decode.expectBytes Decl.addressDomain
  getDeclPayload

/-- Decode one complete canonical IxIR₁ declaration preimage. -/
def Decl.decodePreimage (bytes : ByteArray) : Except String Decl :=
  Decode.runCanonical getDeclPreimage Decl.preimage bytes

/-! ## Nonrecursive cursor-relative specifications -/

theorem getAtom_spec : ∀ atom : Atom, GetSpec getAtom atom.bytes atom
  | .var index => by
      have hpayload := Decode.getSpecMap (Decode.getNat_spec index) Atom.var
      have htotal := GetSpec.bind (next := getAtomTag)
        (Decode.getU8_tag_spec 0) hpayload
      simpa only [getAtom, Atom.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .lit literal => by
      have hpayload := Decode.getSpecMap
        (IxIR0.getLiteral_spec literal) Atom.lit
      have htotal := GetSpec.bind (next := getAtomTag)
        (Decode.getU8_tag_spec 1) hpayload
      simpa only [getAtom, Atom.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .erased => by
      have hpayload : GetSpec (getAtomTag 2) ByteArray.empty Atom.erased :=
        GetSpec.pure Atom.erased
      have htotal := GetSpec.bind (next := getAtomTag)
        (Decode.getU8_tag_spec 2) hpayload
      simpa only [getAtom, Atom.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal

theorem getCtorId_spec (cid : CtorId) :
    GetSpec getCtorId cid.bytes cid := by
  have hspec := Decode.getSpecMap3 (Decode.getAddress_spec cid.block)
    (Decode.getNat_spec cid.indIdx) (Decode.getNat_spec cid.cidx) CtorId.mk
  simpa [getCtorId, CtorId.bytes] using hspec

private theorem getAtomArray_spec (atoms : Array Atom) :
    GetSpec (Decode.getArray getAtom) (Encoding.array Atom.bytes atoms) atoms :=
  Decode.getArray_spec getAtom Atom.bytes getAtom_spec atoms

theorem getOp_spec : ∀ operation : Op, GetSpec getOp operation.bytes operation
  | .pure atom => by
      have hpayload := Decode.getSpecMap (getAtom_spec atom) Op.pure
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
      have hpayload := Decode.getSpecMap3 (getAtom_spec target)
        (getCtorId_spec cid) (getAtomArray_spec args) Op.reuse
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 2) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .free target => by
      have hpayload := Decode.getSpecMap (getAtom_spec target) Op.free
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 3) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .dup target => by
      have hpayload := Decode.getSpecMap (getAtom_spec target) Op.dup
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 4) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .drop target => by
      have hpayload := Decode.getSpecMap (getAtom_spec target) Op.drop
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 5) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .dropU target => by
      have hpayload := Decode.getSpecMap (getAtom_spec target) Op.dropU
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 6) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .fetch target field => by
      have hpayload := Decode.getSpecMap2 (getAtom_spec target)
        (Decode.getNat_spec field) Op.fetch
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 7) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .call function args => by
      have hpayload := Decode.getSpecMap2 (Decode.getAddress_spec function)
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
      have hpayload := Decode.getSpecMap2 (Decode.getAddress_spec function)
        (getAtomArray_spec args) Op.papp
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 10) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .apply function args => by
      have hpayload := Decode.getSpecMap2 (getAtom_spec function)
        (getAtomArray_spec args) Op.apply
      have htotal := GetSpec.bind (next := getOpTag)
        (Decode.getU8_tag_spec 11) hpayload
      simpa only [getOp, Op.bytes, ByteArray.append_assoc,
        ByteArray.append_empty] using htotal
  | .extern function args => by
      have hpayload := Decode.getSpecMap2 (Decode.getAddress_spec function)
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

theorem AltList.member_size_le {alternative : Alt} {alternatives : List Alt}
    (hmember : alternative ∈ alternatives) :
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

/-- Structural induction for code that exposes hypotheses for every case body
stored beneath an alternative array. -/
theorem Code.nested_induction (property : Code → Prop)
    (hret : ∀ atom, property (.ret atom))
    (hlet : ∀ operation rest, property rest →
      property (.letOp operation rest))
    (hcase : ∀ scrut peelNat alternatives,
      (∀ cidx fields body,
        Alt.mk cidx fields body ∈ alternatives.toList → property body) →
      property (.case scrut peelNat alternatives))
    (code : Code) : property code := by
  apply Code.rec
    (motive_1 := fun _ => True)
    (motive_2 := fun alternative => match alternative with
      | .mk _ _ body => property body)
    (motive_3 := property)
    (motive_4 := fun alternatives => ∀ cidx fields body,
      Alt.mk cidx fields body ∈ alternatives.toList → property body)
    (motive_5 := fun alternatives => ∀ cidx fields body,
      Alt.mk cidx fields body ∈ alternatives → property body)
    (pure := by intros; trivial)
    (alloc := by intros; trivial)
    (reuse := by intros; trivial)
    (free := by intros; trivial)
    (dup := by intros; trivial)
    (drop := by intros; trivial)
    (dropU := by intros; trivial)
    (fetch := by intros; trivial)
    (call := by intros; trivial)
    (callSelf := by intros; trivial)
    (papp := by intros; trivial)
    (apply := by intros; trivial)
    (extern := by intros; trivial)
    (mk := by intro cidx fields body hbody; exact hbody)
    (ret := hret)
    (letOp := by
      intro operation rest _ hrest
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

/-! ## Input-fueled recursive code specification -/

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
        have hpayload := Decode.getSpecMap (getAtom_spec atom) Code.ret
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
  · intro scrut peelNat alternatives hchildren fuel hfuel
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
        have hpayload := Decode.getSpecMap3 (getAtom_spec scrut)
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

theorem getDeclPayload_spec : ∀ declaration : Decl,
    GetSpec getDeclPayload declaration.payloadBytes declaration
  | .fn definition => by
      have hpayload := Decode.getSpecMap (getFnDef_spec definition) Decl.fn
      have htotal := GetSpec.bind (next := getDeclTag)
        (Decode.getU8_tag_spec 0) hpayload
      simpa only [getDeclPayload, Decl.payloadBytes,
        ByteArray.append_assoc, ByteArray.append_empty] using htotal
  | .extern arity => by
      have hpayload := Decode.getSpecMap (Decode.getNat_spec arity) Decl.extern
      have htotal := GetSpec.bind (next := getDeclTag)
        (Decode.getU8_tag_spec 1) hpayload
      simpa only [getDeclPayload, Decl.payloadBytes,
        ByteArray.append_assoc, ByteArray.append_empty] using htotal

theorem getDeclPreimage_spec (declaration : Decl) :
    GetSpec getDeclPreimage declaration.preimage declaration := by
  let next : Unit → GetM Decl := fun _ => getDeclPayload
  have htotal := GetSpec.bind (next := next)
    (Decode.expectBytes_spec Decl.addressDomain)
    (getDeclPayload_spec declaration)
  simpa [getDeclPreimage, Decl.preimage, next] using htotal

/-! ## Strict top-level laws -/

/-- Every declaration decodes from its canonical framed preimage. -/
theorem Decl.decodePreimage_roundtrip (declaration : Decl) :
    Decl.decodePreimage declaration.preimage = .ok declaration := by
  exact Decode.runCanonical_of_spec getDeclPreimage Decl.preimage declaration
    (getDeclPreimage_spec declaration)

/-- Every accepted byte string is the canonical preimage of its result. -/
theorem Decl.decodePreimage_canonical {bytes : ByteArray} {declaration : Decl}
    (hdecode : Decl.decodePreimage bytes = .ok declaration) :
    declaration.preimage = bytes := by
  exact Decode.runCanonical_canonical getDeclPreimage Decl.preimage hdecode

/-- Canonical declaration preimages are injective. -/
theorem Decl.preimage_injective : Function.Injective Decl.preimage := by
  intro left right hbytes
  have hok : (Except.ok left : Except String Decl) = .ok right := by
    calc
      .ok left = Decl.decodePreimage left.preimage :=
        (Decl.decodePreimage_roundtrip left).symm
      _ = Decl.decodePreimage right.preimage := congrArg Decl.decodePreimage hbytes
      _ = .ok right := Decl.decodePreimage_roundtrip right
  exact Except.ok.inj hok

end Ix.Compiler.IxIR1
