import Ix.Compiler.IxIR.Decode
import Ix.Compiler.IxIR0.Serialize

/-!
# Strict IxIR₀ declaration decoding

The public entry point consumes the complete versioned declaration preimage,
requires full input consumption, and re-encodes the result before accepting it.
The raw recursive expression reader is input-fueled; the proofs below show the
fuel is sufficient for every encoded declaration.
-/

namespace Ix.Compiler.IxIR0

open Ix.Compiler.Ixon
open Ix.Compiler.IxIR
open Ix.Compiler.IxIR.Decode

def getLiteralTag : UInt8 → GetM Literal
  | 0 => do return .nat (← Decode.getNat)
  | 1 => do return .str (← Decode.getString)
  | tag => throw s!"IxIR0 literal: invalid tag {tag}"

def getLiteral : GetM Literal := do
  getLiteralTag (← getU8)

def getUses : GetM Uses :=
  getDecodedU8 "IxIR0 uses" Uses.ofBits?

def getOwned : GetM Owned :=
  getDecodedU8 "IxIR0 ownership" Owned.ofBits?

def getExprTag (recur : GetM Expr) : UInt8 → GetM Expr
  | 0 => do return .var (← Decode.getNat)
  | 1 => do return .ref (← Decode.getAddress)
  | 2 => do return .app (← recur) (← recur)
  | 3 => do return .lam (← getUses) (← recur)
  | 4 => do
      let uses ← getUses
      let value ← recur
      return .letE uses value (← recur)
  | 5 => do return .proj (← Decode.getNat) (← recur)
  | 6 => do return .lit (← getLiteral)
  | 7 => pure .erased
  | tag => throw s!"IxIR0 expression: invalid tag {tag}"

def getExprFuel : Nat → GetM Expr
  | 0 => throw "IxIR0 expression: recursion limit"
  | fuel + 1 => do
      getExprTag (getExprFuel fuel) (← getU8)

def getExpr : GetM Expr := do
  let state ← get
  getExprFuel (state.bytes.size + 1)

def getRecRule : GetM RecRule := do
  return ⟨← Decode.getNat, ← getExpr⟩

def getDeclTag : UInt8 → GetM Decl
  | 0 => do return .defn (← getOwned) (← getExpr)
  | 1 => do return .ctor (← Decode.getNat) (← Decode.getNat)
  | 2 => do
      let numArgs ← Decode.getNat
      let natLit ← Decode.getBool
      return .recursor numArgs natLit (← Decode.getArray getRecRule)
  | 3 => do return .extern (← Decode.getNat)
  | tag => throw s!"IxIR0 declaration: invalid tag {tag}"

def getDeclPayload : GetM Decl := do
  getDeclTag (← getU8)

def getDeclPreimage : GetM Decl := do
  Decode.expectBytes Decl.addressDomain
  getDeclPayload

/-- Decode one complete canonical IxIR₀ declaration preimage. -/
def Decl.decodePreimage (bytes : ByteArray) : Except String Decl :=
  Decode.runCanonical getDeclPreimage Decl.preimage bytes

/-! ## Cursor-relative roundtrip proofs -/

theorem getLiteral_spec : ∀ value : Literal,
    GetSpec getLiteral value.bytes value
  | .nat number => by
      have hpayload := Decode.getSpecMap (Decode.getNat_spec number) Literal.nat
      have htotal := GetSpec.bind (next := getLiteralTag)
        (Decode.getU8_tag_spec 0) hpayload
      simpa only [getLiteral, Literal.bytes] using htotal
  | .str string => by
      have hpayload := Decode.getSpecMap (Decode.getString_spec string) Literal.str
      have htotal := GetSpec.bind (next := getLiteralTag)
        (Decode.getU8_tag_spec 1) hpayload
      simpa only [getLiteral, Literal.bytes] using htotal

theorem getUses_spec (value : Uses) :
    GetSpec getUses (Encoding.tag value.toBits) value := by
  rw [Decode.tag_eq_u8Bytes]
  exact Ixon.ConstLaws.getDecodedU8_spec "IxIR0 uses" Uses.ofBits?
    Uses.toBits Uses.ofBits?_toBits value

theorem getOwned_spec (value : Owned) :
    GetSpec getOwned (Encoding.tag value.toBits) value := by
  rw [Decode.tag_eq_u8Bytes]
  exact Ixon.ConstLaws.getDecodedU8_spec "IxIR0 ownership" Owned.ofBits?
    Owned.toBits Owned.ofBits?_toBits value

/-- Recursive parser depth; every encoded expression has at least this many
constructor-tag bytes along its deepest branch. -/
def Expr.decodeDepth : Expr → Nat
  | .var _ | .ref _ | .lit _ | .erased => 1
  | .app function argument =>
      1 + Nat.max function.decodeDepth argument.decodeDepth
  | .lam _ body => 1 + body.decodeDepth
  | .letE _ value body =>
      1 + Nat.max value.decodeDepth body.decodeDepth
  | .proj _ target => 1 + target.decodeDepth

theorem Expr.decodeDepth_pos (expression : Expr) :
    0 < expression.decodeDepth := by
  cases expression <;> simp only [Expr.decodeDepth] <;> omega

theorem Expr.decodeDepth_le_bytes (expression : Expr) :
    expression.decodeDepth ≤ expression.bytes.size := by
  induction expression with
  | var index => simp [Expr.decodeDepth, Expr.bytes]
  | ref address => simp [Expr.decodeDepth, Expr.bytes]
  | app function argument hfunction hargument =>
      simp only [Expr.decodeDepth, Expr.bytes, ByteArray.size_append,
        Decode.tag_size]
      have hleft : function.decodeDepth ≤
          function.bytes.size + argument.bytes.size := by omega
      have hright : argument.decodeDepth ≤
          function.bytes.size + argument.bytes.size := by omega
      have hmax : Nat.max function.decodeDepth argument.decodeDepth ≤
          function.bytes.size + argument.bytes.size :=
        Nat.max_le.mpr ⟨hleft, hright⟩
      omega
  | lam uses body hbody =>
      simp only [Expr.decodeDepth, Expr.bytes, ByteArray.size_append,
        Decode.tag_size]
      omega
  | letE uses value body hvalue hbody =>
      simp only [Expr.decodeDepth, Expr.bytes, ByteArray.size_append,
        Decode.tag_size]
      have hleft : value.decodeDepth ≤ value.bytes.size + body.bytes.size := by
        omega
      have hright : body.decodeDepth ≤ value.bytes.size + body.bytes.size := by
        omega
      have hmax : Nat.max value.decodeDepth body.decodeDepth ≤
          value.bytes.size + body.bytes.size :=
        Nat.max_le.mpr ⟨hleft, hright⟩
      omega
  | proj index target htarget =>
      simp only [Expr.decodeDepth, Expr.bytes, ByteArray.size_append,
        Decode.tag_size]
      omega
  | lit literal =>
      simp only [Expr.decodeDepth, Expr.bytes, ByteArray.size_append,
        Decode.tag_size]
      omega
  | erased => simp [Expr.decodeDepth, Expr.bytes]

theorem getExprFuel_spec (expression : Expr) (fuel : Nat)
    (hfuel : expression.decodeDepth < fuel) :
    GetSpec (getExprFuel fuel) expression.bytes expression := by
  induction expression generalizing fuel with
  | var index =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hpayload := Decode.getSpecMap (Decode.getNat_spec index) Expr.var
          have htotal := GetSpec.bind
            (next := getExprTag (getExprFuel fuel))
            (Decode.getU8_tag_spec 0) hpayload
          simpa only [getExprFuel, Expr.bytes, ByteArray.append_assoc,
            ByteArray.append_empty] using htotal
  | ref address =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hpayload := Decode.getSpecMap
            (Decode.getAddress_spec address) Expr.ref
          have htotal := GetSpec.bind
            (next := getExprTag (getExprFuel fuel))
            (Decode.getU8_tag_spec 1) hpayload
          simpa only [getExprFuel, Expr.bytes, ByteArray.append_assoc,
            ByteArray.append_empty] using htotal
  | app function argument hfunction hargument =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [Expr.decodeDepth] at hfuel
          have hmax : Nat.max function.decodeDepth argument.decodeDepth < fuel := by
            omega
          have hfunctionFuel : function.decodeDepth < fuel :=
            Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax
          have hargumentFuel : argument.decodeDepth < fuel :=
            Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax
          have hpayload := Decode.getSpecMap2
            (hfunction fuel hfunctionFuel) (hargument fuel hargumentFuel)
            Expr.app
          have htotal := GetSpec.bind
            (next := getExprTag (getExprFuel fuel))
            (Decode.getU8_tag_spec 2) hpayload
          simpa only [getExprFuel, Expr.bytes, ByteArray.append_assoc,
            ByteArray.append_empty] using htotal
  | lam uses body hbody =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [Expr.decodeDepth] at hfuel
          have hbodyFuel : body.decodeDepth < fuel := by omega
          have hpayload := Decode.getSpecMap2 (getUses_spec uses)
            (hbody fuel hbodyFuel) Expr.lam
          have htotal := GetSpec.bind
            (next := getExprTag (getExprFuel fuel))
            (Decode.getU8_tag_spec 3) hpayload
          simpa only [getExprFuel, Expr.bytes, ByteArray.append_assoc,
            ByteArray.append_empty] using htotal
  | letE uses value body hvalue hbody =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [Expr.decodeDepth] at hfuel
          have hmax : Nat.max value.decodeDepth body.decodeDepth < fuel := by
            omega
          have hvalueFuel : value.decodeDepth < fuel :=
            Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax
          have hbodyFuel : body.decodeDepth < fuel :=
            Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax
          have hpayload := Decode.getSpecMap3 (getUses_spec uses)
            (hvalue fuel hvalueFuel) (hbody fuel hbodyFuel) Expr.letE
          have htotal := GetSpec.bind
            (next := getExprTag (getExprFuel fuel))
            (Decode.getU8_tag_spec 4) hpayload
          simpa only [getExprFuel, Expr.bytes, ByteArray.append_assoc,
            ByteArray.append_empty] using htotal
  | proj index target htarget =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [Expr.decodeDepth] at hfuel
          have htargetFuel : target.decodeDepth < fuel := by omega
          have hpayload := Decode.getSpecMap2 (Decode.getNat_spec index)
            (htarget fuel htargetFuel) Expr.proj
          have htotal := GetSpec.bind
            (next := getExprTag (getExprFuel fuel))
            (Decode.getU8_tag_spec 5) hpayload
          simpa only [getExprFuel, Expr.bytes, ByteArray.append_assoc,
            ByteArray.append_empty] using htotal
  | lit literal =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hpayload := Decode.getSpecMap (getLiteral_spec literal) Expr.lit
          have htotal := GetSpec.bind
            (next := getExprTag (getExprFuel fuel))
            (Decode.getU8_tag_spec 6) hpayload
          simpa only [getExprFuel, Expr.bytes, ByteArray.append_assoc,
            ByteArray.append_empty] using htotal
  | erased =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hpayload : GetSpec (getExprTag (getExprFuel fuel) 7)
              ByteArray.empty Expr.erased := by
            exact GetSpec.pure Expr.erased
          have htotal := GetSpec.bind
            (next := getExprTag (getExprFuel fuel))
            (Decode.getU8_tag_spec 7) hpayload
          simpa only [getExprFuel, Expr.bytes, ByteArray.append_assoc,
            ByteArray.append_empty] using htotal

theorem getExpr_spec (expression : Expr) :
    GetSpec getExpr expression.bytes expression := by
  intro pre suffix
  let fuel := (pre ++ expression.bytes ++ suffix).size + 1
  have hfuel : expression.decodeDepth < fuel := by
    have hdepth := expression.decodeDepth_le_bytes
    dsimp [fuel]
    simp only [ByteArray.size_append]
    omega
  have hspec := getExprFuel_spec expression fuel hfuel pre suffix
  simpa [getExpr, fuel] using hspec

theorem getRecRule_spec (rule : RecRule) :
    GetSpec getRecRule rule.bytes rule := by
  have hspec := Decode.getSpecMap2 (Decode.getNat_spec rule.fields)
    (getExpr_spec rule.rhs) RecRule.mk
  simpa [getRecRule, RecRule.bytes] using hspec

theorem getDeclPayload_spec : ∀ declaration : Decl,
    GetSpec getDeclPayload declaration.payloadBytes declaration
  | .defn result body => by
      have hpayload := Decode.getSpecMap2 (getOwned_spec result)
        (getExpr_spec body) Decl.defn
      have htotal := GetSpec.bind (next := getDeclTag)
        (Decode.getU8_tag_spec 0) hpayload
      simpa only [getDeclPayload, Decl.payloadBytes,
        ByteArray.append_assoc, ByteArray.append_empty] using htotal
  | .ctor tag arity => by
      have hpayload := Decode.getSpecMap2 (Decode.getNat_spec tag)
        (Decode.getNat_spec arity) Decl.ctor
      have htotal := GetSpec.bind (next := getDeclTag)
        (Decode.getU8_tag_spec 1) hpayload
      simpa only [getDeclPayload, Decl.payloadBytes,
        ByteArray.append_assoc, ByteArray.append_empty] using htotal
  | .recursor numArgs natLit rules => by
      have hpayload := Decode.getSpecMap3 (Decode.getNat_spec numArgs)
        (Decode.getBool_spec natLit)
        (Decode.getArray_spec getRecRule RecRule.bytes getRecRule_spec rules)
        Decl.recursor
      have htotal := GetSpec.bind (next := getDeclTag)
        (Decode.getU8_tag_spec 2) hpayload
      simpa only [getDeclPayload, Decl.payloadBytes,
        ByteArray.append_assoc, ByteArray.append_empty] using htotal
  | .extern arity => by
      have hpayload := Decode.getSpecMap (Decode.getNat_spec arity) Decl.extern
      have htotal := GetSpec.bind (next := getDeclTag)
        (Decode.getU8_tag_spec 3) hpayload
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

end Ix.Compiler.IxIR0
