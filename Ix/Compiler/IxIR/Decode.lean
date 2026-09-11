import Ix.Compiler.IxIR.Encoding

/-!
# Strict readers for the addressed IxIR grammar

These readers are the inverse-facing half of `IxIR.Encoding`. Recursive and
counted inputs are fueled by the enclosing byte array, so malformed input
cannot create a logical nontermination. The raw readers deliberately accept a
slightly wider LEB128 language; declaration entry points call `runCanonical`,
which re-encodes the parsed value and rejects every noncanonical spelling.
-/

namespace Ix.Compiler.IxIR.Decode

open Ix.Compiler.Ixon
open Ix.Compiler.Ixon (Address)

/-- Decode one arbitrary-precision unsigned LEB128 value. The fuel is supplied
by the enclosing byte array and decreases for every consumed chunk. -/
def getNatFuel : Nat → GetM Nat
  | 0 => throw "natural: recursion limit"
  | fuel + 1 => do
      let byte ← getU8
      let low := byte.toNat % 128
      if byte.toNat < 128 then
        return low
      return low + 128 * (← getNatFuel fuel)

/-- Input-fueled arbitrary-precision unsigned LEB128 reader. -/
def getNat : GetM Nat := do
  let state ← get
  getNatFuel (state.bytes.size + 1)

/-- Decode a one-byte Boolean, rejecting every value other than zero or one. -/
def getBool : GetM Bool :=
  getDecodedU8 "boolean" boolOfByte?

/-- Decode a length-prefixed byte string. -/
def getBlob : GetM ByteArray := do
  let size ← getNat
  getBytes size

/-- Decode canonical UTF-8 beneath the length-prefixed byte grammar. -/
def getString : GetM String := do
  let bytes ← getBlob
  match String.fromUTF8? bytes with
  | some value => return value
  | none => throw "string: invalid UTF-8"

/-- Decode one fixed-width content address. -/
def getAddress : GetM Address :=
  Serialize.get

/-- Decode exactly `count` values. -/
def getListN (getOne : GetM α) : Nat → GetM (List α)
  | 0 => pure []
  | count + 1 => do
      let head ← getOne
      return head :: (← getListN getOne count)

/-- Decode a LEB128-counted list in source order. -/
def getList (getOne : GetM α) : GetM (List α) := do
  let count ← getNat
  getListN getOne count

/-- Decode a LEB128-counted array in source order. -/
def getArray (getOne : GetM α) : GetM (Array α) := do
  let count ← getNat
  return (← getListN getOne count).toArray

/-- Consume an exact fixed byte sequence. -/
def expectBytes (expected : ByteArray) : GetM Unit := do
  let actual ← getBytes expected.size
  if actual = expected then
    return ()
  throw "unexpected framing bytes"

/-- Strict top-level decoder wrapper. Besides full consumption from `runGet`,
successful values must reproduce the complete input byte-for-byte. -/
def runCanonical (getValue : GetM α) (encode : α → ByteArray)
    (bytes : ByteArray) : Except String α := do
  let value ← runGet getValue bytes
  if encode value = bytes then
    return value
  throw "noncanonical encoding"

/-! ## Generic proof layer -/

theorem tag_eq_u8Bytes (value : UInt8) :
    Encoding.tag value = u8Bytes value := by
  apply ByteArray.ext
  simp [Encoding.tag, u8Bytes]

theorem getU8_tag_spec (value : UInt8) :
    GetSpec getU8 (Encoding.tag value) value := by
  rw [tag_eq_u8Bytes]
  exact getU8_spec value

@[simp] theorem tag_size (value : UInt8) :
    (Encoding.tag value).size = 1 := by
  rw [tag_eq_u8Bytes]
  simp [u8Bytes]

theorem nat_size_pos (value : Nat) : 0 < (Encoding.nat value).size := by
  rw [Encoding.nat]
  split
  · simp
  · simp only [ByteArray.size_append, tag_size]
    omega

theorem getNatFuel_spec (value fuel : Nat)
    (hfuel : (Encoding.nat value).size < fuel) :
    GetSpec (getNatFuel fuel) (Encoding.nat value) value := by
  induction value using Nat.strongRecOn generalizing fuel with
  | ind value ih =>
      by_cases hsmall : value < 128
      · rw [Encoding.nat, dif_pos hsmall] at hfuel ⊢
        cases fuel with
        | zero => simp at hfuel
        | succ fuel =>
            let byte := UInt8.ofNat value
            let next : UInt8 → GetM Nat := fun decoded =>
              let low := decoded.toNat % 128
              if decoded.toNat < 128 then pure low
              else do return low + 128 * (← getNatFuel fuel)
            have hbyte : byte.toNat = value := by
              exact UInt8.toNat_ofNat_of_lt'
                (show value < 256 by omega)
            have hnext : GetSpec (next byte) ByteArray.empty value := by
              simp [next, byte, hbyte, hsmall, Nat.mod_eq_of_lt]
              exact GetSpec.pure value
            have htotal := GetSpec.bind (next := next)
              (getU8_tag_spec byte) hnext
            simpa [getNatFuel, byte, next] using htotal
      · have hlarge : 128 ≤ value := Nat.le_of_not_gt hsmall
        rw [Encoding.nat, dif_neg hsmall] at hfuel ⊢
        cases fuel with
        | zero => simp at hfuel
        | succ fuel =>
            let quotient := value / 128
            let byte := UInt8.ofNat (128 + value % 128)
            have hquotient : quotient < value := by
              dsimp [quotient]
              exact Nat.div_lt_self (by omega) (by omega)
            have hchildFuel : (Encoding.nat quotient).size < fuel := by
              dsimp [quotient]
              simp only [ByteArray.size_append, tag_size] at hfuel
              omega
            have hrecursive := ih quotient hquotient fuel hchildFuel
            have hbyte : byte.toNat = 128 + value % 128 := by
              exact UInt8.toNat_ofNat_of_lt' (show
                128 + value % 128 < 256 by
                have := Nat.mod_lt value (by omega : 0 < 128)
                omega)
            let next : UInt8 → GetM Nat := fun decoded =>
              let low := decoded.toNat % 128
              if decoded.toNat < 128 then pure low
              else do return low + 128 * (← getNatFuel fuel)
            have hmapped :
                GetSpec
                  ((fun high => value % 128 + 128 * high) <$>
                    getNatFuel fuel)
                  (Encoding.nat quotient) value := by
              have hmap := Ixon.ExprLaws.GetSpec.map hrecursive
                (fun high => value % 128 + 128 * high)
              have hdecompose : value % 128 + 128 * quotient = value := by
                exact Nat.mod_add_div value 128
              simpa [hdecompose] using hmap
            have hnext :
                GetSpec (next byte) (Encoding.nat quotient) value := by
              have hnotSmall : ¬byte.toNat < 128 := by
                rw [hbyte]
                omega
              have hlow : byte.toNat % 128 = value % 128 := by
                rw [hbyte]
                omega
              simpa [next, hnotSmall, hlow] using hmapped
            have htotal := GetSpec.bind (next := next)
              (getU8_tag_spec byte) hnext
            simpa [getNatFuel, byte, quotient, next] using htotal

theorem getNat_spec (value : Nat) :
    GetSpec getNat (Encoding.nat value) value := by
  intro pre suffix
  let fuel := (pre ++ Encoding.nat value ++ suffix).size + 1
  have hfuel : (Encoding.nat value).size < fuel := by
    dsimp [fuel]
    simp only [ByteArray.size_append]
    omega
  have hspec := getNatFuel_spec value fuel hfuel pre suffix
  simpa [getNat, fuel] using hspec

theorem getBlob_spec (value : ByteArray) :
    GetSpec getBlob (Encoding.blob value) value := by
  have htotal := GetSpec.bind (next := getBytes)
    (getNat_spec value.size) (getBytes_spec value)
  simpa [getBlob, Encoding.blob] using htotal

theorem string_fromUTF8_toUTF8 (value : String) :
    String.fromUTF8? value.toUTF8 = some value := by
  unfold String.fromUTF8?
  have hvalid : value.toUTF8.IsValidUTF8 := by
    simpa using value.isValidUTF8
  rw [dif_pos hvalid]
  congr

theorem toUTF8_of_fromUTF8 {bytes : ByteArray} {value : String}
    (hdecode : String.fromUTF8? bytes = some value) :
    value.toUTF8 = bytes := by
  unfold String.fromUTF8? at hdecode
  split at hdecode
  · cases hdecode
    rfl
  · contradiction

theorem getString_spec (value : String) :
    GetSpec getString (Encoding.string value) value := by
  let finish : ByteArray → GetM String := fun bytes =>
    match String.fromUTF8? bytes with
    | some decoded => pure decoded
    | none => throw "string: invalid UTF-8"
  have hfinish : GetSpec (finish value.toUTF8) ByteArray.empty value := by
    unfold finish
    rw [string_fromUTF8_toUTF8]
    exact GetSpec.pure value
  have htotal := GetSpec.bind (next := finish)
    (getBlob_spec value.toUTF8) hfinish
  simpa [getString, Encoding.string, finish] using htotal

theorem expectBytes_spec (expected : ByteArray) :
    GetSpec (expectBytes expected) expected () := by
  intro pre suffix
  simp only [expectBytes, StateT.run_bind]
  rw [getBytes_spec expected pre suffix]
  simp only [bind, Except.bind]
  simp
  change (Except.ok ((),
    (⟨pre ++ expected ++ suffix, pre.size + expected.size⟩ : GetState)) :
      Except String (Unit × GetState)) = _
  rfl

theorem getBool_spec (value : Bool) :
    GetSpec getBool (Encoding.bool value) value := by
  cases value with
  | false =>
      simpa [getBool, Encoding.bool, tag_eq_u8Bytes, boolOfByte?] using
        (Ixon.ConstLaws.getDecodedU8_spec "boolean" boolOfByte?
          (fun value : Bool => if value then 1 else 0)
          (by intro value; cases value <;> rfl) false)
  | true =>
      simpa [getBool, Encoding.bool, tag_eq_u8Bytes, boolOfByte?] using
        (Ixon.ConstLaws.getDecodedU8_spec "boolean" boolOfByte?
          (fun value : Bool => if value then 1 else 0)
          (by intro value; cases value <;> rfl) true)

theorem getAddress_spec (value : Address) :
    GetSpec getAddress (Encoding.address value) value := by
  simpa [getAddress, Encoding.address] using Address.get_spec value

theorem getSpecMap {getValue : GetM α} {input : ByteArray} {value : α}
    (hspec : GetSpec getValue input value) (map : α → β) :
    GetSpec (map <$> getValue) input (map value) :=
  Ixon.ExprLaws.GetSpec.map hspec map

theorem getSpecMap2 {getLeft : GetM α} {getRight : GetM β}
    {leftBytes rightBytes : ByteArray} {left : α} {right : β}
    (hleft : GetSpec getLeft leftBytes left)
    (hright : GetSpec getRight rightBytes right) (map : α → β → γ) :
    GetSpec (do
      let decodedLeft ← getLeft
      let decodedRight ← getRight
      return map decodedLeft decodedRight)
      (leftBytes ++ rightBytes) (map left right) := by
  let next : α → GetM γ := fun decodedLeft =>
    map decodedLeft <$> getRight
  have hnext := getSpecMap hright (map left)
  have htotal := GetSpec.bind (next := next) hleft hnext
  simpa [next] using htotal

theorem getSpecMap3 {getFirst : GetM α} {getSecond : GetM β}
    {getThird : GetM γ} {firstBytes secondBytes thirdBytes : ByteArray}
    {first : α} {second : β} {third : γ}
    (hfirst : GetSpec getFirst firstBytes first)
    (hsecond : GetSpec getSecond secondBytes second)
    (hthird : GetSpec getThird thirdBytes third)
    (map : α → β → γ → δ) :
    GetSpec (do
      let decodedFirst ← getFirst
      let decodedSecond ← getSecond
      let decodedThird ← getThird
      return map decodedFirst decodedSecond decodedThird)
      (firstBytes ++ secondBytes ++ thirdBytes)
      (map first second third) := by
  let afterFirst : α → GetM δ := fun decodedFirst => do
    let decodedSecond ← getSecond
    let decodedThird ← getThird
    return map decodedFirst decodedSecond decodedThird
  have htail := getSpecMap2 hsecond hthird (map first)
  have htotal := GetSpec.bind (next := afterFirst) hfirst htail
  simpa [afterFirst, ByteArray.append_assoc] using htotal

theorem getSpecMap4 {getFirst : GetM α} {getSecond : GetM β}
    {getThird : GetM γ} {getFourth : GetM δ}
    {firstBytes secondBytes thirdBytes fourthBytes : ByteArray}
    {first : α} {second : β} {third : γ} {fourth : δ}
    (hfirst : GetSpec getFirst firstBytes first)
    (hsecond : GetSpec getSecond secondBytes second)
    (hthird : GetSpec getThird thirdBytes third)
    (hfourth : GetSpec getFourth fourthBytes fourth)
    (map : α → β → γ → δ → ε) :
    GetSpec (do
      let decodedFirst ← getFirst
      let decodedSecond ← getSecond
      let decodedThird ← getThird
      let decodedFourth ← getFourth
      return map decodedFirst decodedSecond decodedThird decodedFourth)
      (firstBytes ++ secondBytes ++ thirdBytes ++ fourthBytes)
      (map first second third fourth) := by
  let afterFirst : α → GetM ε := fun decodedFirst => do
    let decodedSecond ← getSecond
    let decodedThird ← getThird
    let decodedFourth ← getFourth
    return map decodedFirst decodedSecond decodedThird decodedFourth
  have htail := getSpecMap3 hsecond hthird hfourth (map first)
  have htotal := GetSpec.bind (next := afterFirst) hfirst htail
  simpa [afterFirst, ByteArray.append_assoc] using htotal

/-- Concatenated element payload beneath a counted sequence. -/
def listBytes (encode : α → ByteArray) : List α → ByteArray
  | [] => ByteArray.empty
  | head :: tail => encode head ++ listBytes encode tail

theorem foldl_append_eq (encode : α → ByteArray) (values : List α)
    (initial : ByteArray) :
    values.foldl (fun output value => output ++ encode value) initial =
      initial ++ listBytes encode values := by
  induction values generalizing initial with
  | nil => simp [listBytes]
  | cons head tail ih =>
      simp only [List.foldl_cons, listBytes]
      rw [ih]
      simp [ByteArray.append_assoc]

theorem listBytes_eq_foldl (encode : α → ByteArray) (values : List α) :
    listBytes encode values =
      values.foldl (fun output value => output ++ encode value)
        ByteArray.empty := by
  rw [foldl_append_eq]
  simp

theorem getListN_spec (getOne : GetM α) (encode : α → ByteArray)
    (hone : ∀ value, GetSpec getOne (encode value) value)
    (values : List α) :
    GetSpec (getListN getOne values.length)
      (listBytes encode values) values := by
  induction values with
  | nil => exact GetSpec.pure []
  | cons head tail ih =>
      have htail := Ixon.ExprLaws.GetSpec.map ih (head :: ·)
      let next : α → GetM (List α) := fun decoded =>
        (decoded :: ·) <$> getListN getOne tail.length
      have htotal := GetSpec.bind (next := next) (hone head) htail
      simpa [next, getListN, listBytes] using htotal

theorem getListN_spec_of (getOne : GetM α) (encode : α → ByteArray)
    (property : α → Prop)
    (hone : ∀ value, property value → GetSpec getOne (encode value) value)
    (values : List α) (hvalues : ∀ value ∈ values, property value) :
    GetSpec (getListN getOne values.length)
      (listBytes encode values) values := by
  induction values with
  | nil => exact GetSpec.pure []
  | cons head tail ih =>
      have hhead : property head := hvalues head (by simp)
      have htailProperty : ∀ value ∈ tail, property value := by
        intro value hvalue
        exact hvalues value (by simp [hvalue])
      have htail := Ixon.ExprLaws.GetSpec.map (ih htailProperty) (head :: ·)
      let next : α → GetM (List α) := fun decoded =>
        (decoded :: ·) <$> getListN getOne tail.length
      have htotal := GetSpec.bind (next := next) (hone head hhead) htail
      simpa [next, getListN, listBytes] using htotal

theorem list_eq_counted (encode : α → ByteArray) (values : List α) :
    Encoding.list encode values =
      Encoding.nat values.length ++ listBytes encode values := by
  simp only [Encoding.list]
  rw [listBytes_eq_foldl]

theorem getList_spec (getOne : GetM α) (encode : α → ByteArray)
    (hone : ∀ value, GetSpec getOne (encode value) value)
    (values : List α) :
    GetSpec (getList getOne) (Encoding.list encode values) values := by
  have hlist := getListN_spec getOne encode hone values
  let next : Nat → GetM (List α) := fun count => getListN getOne count
  have htotal := GetSpec.bind (next := next)
    (getNat_spec values.length) hlist
  simpa [getList, list_eq_counted, next] using htotal

theorem getList_spec_of (getOne : GetM α) (encode : α → ByteArray)
    (property : α → Prop)
    (hone : ∀ value, property value → GetSpec getOne (encode value) value)
    (values : List α) (hvalues : ∀ value ∈ values, property value) :
    GetSpec (getList getOne) (Encoding.list encode values) values := by
  have hlist := getListN_spec_of getOne encode property hone values hvalues
  let next : Nat → GetM (List α) := fun count => getListN getOne count
  have htotal := GetSpec.bind (next := next)
    (getNat_spec values.length) hlist
  simpa [getList, list_eq_counted, next] using htotal

theorem array_eq_counted (encode : α → ByteArray) (values : Array α) :
    Encoding.array encode values =
      Encoding.nat values.size ++ listBytes encode values.toList := by
  simp only [Encoding.array]
  rw [listBytes_eq_foldl]
  rw [Array.foldl_toList]

theorem getArray_spec (getOne : GetM α) (encode : α → ByteArray)
    (hone : ∀ value, GetSpec getOne (encode value) value)
    (values : Array α) :
    GetSpec (getArray getOne) (Encoding.array encode values) values := by
  have hlist := getListN_spec getOne encode hone values.toList
  have harray := Ixon.ExprLaws.GetSpec.map hlist List.toArray
  let next : Nat → GetM (Array α) := fun count =>
    List.toArray <$> getListN getOne count
  have htotal := GetSpec.bind (next := next)
    (getNat_spec values.size) harray
  simpa [getArray, array_eq_counted, next] using htotal

theorem getArray_spec_of (getOne : GetM α) (encode : α → ByteArray)
    (property : α → Prop)
    (hone : ∀ value, property value → GetSpec getOne (encode value) value)
    (values : Array α)
    (hvalues : ∀ value ∈ values.toList, property value) :
    GetSpec (getArray getOne) (Encoding.array encode values) values := by
  have hlist := getListN_spec_of getOne encode property hone values.toList hvalues
  have harray := Ixon.ExprLaws.GetSpec.map hlist List.toArray
  let next : Nat → GetM (Array α) := fun count =>
    List.toArray <$> getListN getOne count
  have htotal := GetSpec.bind (next := next)
    (getNat_spec values.size) harray
  simpa [getArray, array_eq_counted, next] using htotal

theorem runCanonical_of_spec (getValue : GetM α) (encode : α → ByteArray)
    (value : α) (hspec : GetSpec getValue (encode value) value) :
    runCanonical getValue encode (encode value) = .ok value := by
  unfold runCanonical
  rw [runGet_eq_ok_of_spec hspec]
  simp only [bind, Except.bind]
  simp
  change (Except.ok value : Except String α) = .ok value
  rfl

theorem runCanonical_canonical (getValue : GetM α)
    (encode : α → ByteArray) {bytes : ByteArray} {value : α}
    (hdecode : runCanonical getValue encode bytes = .ok value) :
    encode value = bytes := by
  simp only [runCanonical] at hdecode
  cases hrun : runGet getValue bytes with
  | error error => rw [hrun] at hdecode; contradiction
  | ok decoded =>
      rw [hrun] at hdecode
      simp only [bind, Except.bind] at hdecode
      split at hdecode
      · rename_i heq
        cases hdecode
        exact heq
      · contradiction

end Ix.Compiler.IxIR.Decode
