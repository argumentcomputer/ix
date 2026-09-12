import Compilatrix.IxIR.Decode

/-!
# Bounded readers for finite IR snapshots

Limits belong to the reader, not the identity. Sequence lengths and blob
lengths are checked before traversal/allocation; arbitrary-precision naturals
consume at most `maxNatBytes` bytes. Counted lists use a tail-recursive
accumulator. The enclosing format also checks `maxBytes` before parsing.
-/

namespace Compilatrix.IxIR.Bounded

open Compilatrix.Ixon
open Compilatrix.IxIR.Decode

structure Limits where
  maxBytes : Nat := 16777216
  maxNatBytes : Nat := 64
  maxSequence : Nat := 65536
  maxBlobBytes : Nat := 1048576
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def natFits (limits : Limits) (value : Nat) : Bool :=
  (Encoding.nat value).size ≤ limits.maxNatBytes

def getNat (limits : Limits) : GetM Nat :=
  Decode.getNatFuel limits.maxNatBytes

def countFits (limits : Limits) (count : Nat) : Bool :=
  natFits limits count && count ≤ limits.maxSequence

def listFits (limits : Limits) (fits : α → Bool) (values : List α) : Bool :=
  countFits limits values.length && values.all fits

def arrayFits (limits : Limits) (fits : α → Bool) (values : Array α) : Bool :=
  listFits limits fits values.toList

def getListAcc (getOne : GetM α) : Nat → List α → GetM (List α)
  | 0, accumulated => pure accumulated.reverse
  | count + 1, accumulated => do
      let value ← getOne
      getListAcc getOne count (value :: accumulated)

def getList (limits : Limits) (getOne : GetM α) : GetM (List α) := do
  let count ← getNat limits
  if count ≤ limits.maxSequence then getListAcc getOne count []
  else throw "IR sequence length limit"

def getArray (limits : Limits) (getOne : GetM α) : GetM (Array α) :=
  List.toArray <$> getList limits getOne

def blobFits (limits : Limits) (value : ByteArray) : Bool :=
  natFits limits value.size && value.size ≤ limits.maxBlobBytes

def getBlob (limits : Limits) : GetM ByteArray := do
  let count ← getNat limits
  if count ≤ limits.maxBlobBytes then getBytes count
  else throw "IR blob length limit"

def stringFits (limits : Limits) (value : String) : Bool :=
  blobFits limits value.toUTF8

def getString (limits : Limits) : GetM String := do
  let bytes ← getBlob limits
  match String.fromUTF8? bytes with
  | some value => return value
  | none => throw "IR string: invalid UTF-8"

/-! Cursor-relative specifications for the actual bounded readers. -/

theorem getNatFuel_spec_le (value fuel : Nat)
    (hfuel : (Encoding.nat value).size ≤ fuel) :
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
            have hchildFuel : (Encoding.nat quotient).size ≤ fuel := by
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


theorem getNat_spec (limits : Limits) (value : Nat)
    (fits : natFits limits value = true) :
    GetSpec (getNat limits) (Encoding.nat value) value :=
  getNatFuel_spec_le value limits.maxNatBytes (of_decide_eq_true fits)

theorem getListAcc_spec (getOne : GetM α) (encode : α → ByteArray)
    (fits : α → Bool)
    (spec : ∀ value, fits value = true → GetSpec getOne (encode value) value)
    (values accumulated : List α) (admitted : values.all fits = true) :
    GetSpec (getListAcc getOne values.length accumulated)
      (Decode.listBytes encode values) (accumulated.reverse ++ values) := by
  induction values generalizing accumulated with
  | nil => simpa [getListAcc, Decode.listBytes] using GetSpec.pure accumulated.reverse
  | cons head tail ih =>
      simp only [List.all_cons, Bool.and_eq_true] at admitted
      let next : α → GetM (List α) := fun value =>
        getListAcc getOne tail.length (value :: accumulated)
      have total := GetSpec.bind (next := next) (spec head admitted.1)
        (ih (head :: accumulated) admitted.2)
      simpa [getListAcc, Decode.listBytes, next, List.append_assoc] using total

theorem getList_spec (limits : Limits) (getOne : GetM α) (encode : α → ByteArray)
    (fits : α → Bool)
    (spec : ∀ value, fits value = true → GetSpec getOne (encode value) value)
    (values : List α) (admitted : listFits limits fits values = true) :
    GetSpec (getList limits getOne) (Encoding.list encode values) values := by
  simp only [listFits, countFits, Bool.and_eq_true, decide_eq_true_eq] at admitted
  have body := getListAcc_spec getOne encode fits spec values [] admitted.2
  let next : Nat → GetM (List α) := fun count =>
    if count ≤ limits.maxSequence then getListAcc getOne count []
    else throw "IR sequence length limit"
  have tail : GetSpec (next values.length) (Decode.listBytes encode values) values := by
    simpa [next, admitted.1.2] using body
  have total := GetSpec.bind (next := next)
    (getNat_spec limits values.length admitted.1.1) tail
  simpa [getList, next, Decode.list_eq_counted] using total

theorem getArray_spec (limits : Limits) (getOne : GetM α) (encode : α → ByteArray)
    (fits : α → Bool)
    (spec : ∀ value, fits value = true → GetSpec getOne (encode value) value)
    (values : Array α) (admitted : arrayFits limits fits values = true) :
    GetSpec (getArray limits getOne) (Encoding.array encode values) values := by
  have total := Decode.getSpecMap
    (getList_spec limits getOne encode fits spec values.toList admitted) List.toArray
  simpa [getArray, Decode.array_eq_counted, Decode.list_eq_counted] using total

theorem getBlob_spec (limits : Limits) (value : ByteArray)
    (fits : blobFits limits value = true) :
    GetSpec (getBlob limits) (Encoding.blob value) value := by
  simp only [blobFits, Bool.and_eq_true, decide_eq_true_eq] at fits
  let next : Nat → GetM ByteArray := fun count =>
    if count ≤ limits.maxBlobBytes then getBytes count
    else throw "IR blob length limit"
  have tail : GetSpec (next value.size) value value := by
    simpa [next, fits.2] using getBytes_spec value
  have total := GetSpec.bind (next := next) (getNat_spec limits value.size fits.1) tail
  simpa [getBlob, Encoding.blob, next] using total

theorem getString_spec (limits : Limits) (value : String)
    (fits : stringFits limits value = true) :
    GetSpec (getString limits) (Encoding.string value) value := by
  let next : ByteArray → GetM String := fun bytes =>
    match String.fromUTF8? bytes with
    | some value => pure value
    | none => throw "IR string: invalid UTF-8"
  have tail : GetSpec (next value.toUTF8) ByteArray.empty value := by
    simp only [next, Decode.string_fromUTF8_toUTF8]
    exact GetSpec.pure value
  have total := GetSpec.bind (next := next) (getBlob_spec limits value.toUTF8 fits) tail
  simpa [getString, Encoding.string, next] using total

/-- Shared entry gate: cap input first, consume it fully, require exact
re-encoding, and retain the representability check on every accepted value. -/
def run (limits : Limits) (getValue : GetM α) (encode : α → ByteArray)
    (fits : α → Bool) (bytes : ByteArray) : Except String α := do
  if bytes.size > limits.maxBytes then throw "IR input byte limit"
  let value ← Decode.runCanonical getValue encode bytes
  if fits value then return value
  else throw "IR representation limit"

theorem run_roundtrip (limits : Limits) (getValue : GetM α) (encode : α → ByteArray)
    (fits : α → Bool) (value : α)
    (size : (encode value).size ≤ limits.maxBytes) (admitted : fits value = true)
    (spec : GetSpec getValue (encode value) value) :
    run limits getValue encode fits (encode value) = .ok value := by
  simp only [run, Nat.not_lt_of_ge size, ↓reduceIte, Decode.runCanonical_of_spec _ _ _ spec,
    bind, Except.bind, admitted, pure]
  rfl

theorem run_spec (limits : Limits) (getValue : GetM α) (encode : α → ByteArray)
    (fits : α → Bool) {bytes : ByteArray} {value : α}
    (accepted : run limits getValue encode fits bytes = .ok value) :
    encode value = bytes ∧ bytes.size ≤ limits.maxBytes ∧ fits value = true := by
  unfold run at accepted
  split at accepted
  · contradiction
  · rename_i size
    simp only [pure, bind, Except.bind] at accepted
    cases parsed : Decode.runCanonical getValue encode bytes with
    | error error => simp [parsed] at accepted
    | ok decoded =>
      simp only [parsed] at accepted
      split at accepted
      · rename_i admitted
        cases accepted
        exact ⟨Decode.runCanonical_canonical _ _ parsed, Nat.le_of_not_gt size, admitted⟩
      · contradiction

/-! Product combinators for complete snapshot records. -/

theorem getSpecMap5 {α0 : Type} {α1 : Type} {α2 : Type} {α3 : Type} {α4 : Type} {β : Type}
    {g0 : GetM α0} {b0 : ByteArray} {v0 : α0}
    {g1 : GetM α1} {b1 : ByteArray} {v1 : α1}
    {g2 : GetM α2} {b2 : ByteArray} {v2 : α2}
    {g3 : GetM α3} {b3 : ByteArray} {v3 : α3}
    {g4 : GetM α4} {b4 : ByteArray} {v4 : α4}
    (h0 : GetSpec g0 b0 v0)
    (h1 : GetSpec g1 b1 v1)
    (h2 : GetSpec g2 b2 v2)
    (h3 : GetSpec g3 b3 v3)
    (h4 : GetSpec g4 b4 v4)
    (f : α0 → α1 → α2 → α3 → α4 → β) :
    GetSpec (do
      let x0 ← g0
      let x1 ← g1
      let x2 ← g2
      let x3 ← g3
      let x4 ← g4
      return f x0 x1 x2 x3 x4)
      (b0 ++ b1 ++ b2 ++ b3 ++ b4) (f v0 v1 v2 v3 v4) := by
  let next : α0 → GetM β := fun x0 => do
    let x1 ← g1
    let x2 ← g2
    let x3 ← g3
    let x4 ← g4
    return f x0 x1 x2 x3 x4
  have tail := Decode.getSpecMap4 h1 h2 h3 h4 (f v0)
  have total := GetSpec.bind (next := next) h0 tail
  simpa [next, ByteArray.append_assoc] using total

theorem getSpecMap6 {α0 : Type} {α1 : Type} {α2 : Type} {α3 : Type} {α4 : Type} {α5 : Type} {β : Type}
    {g0 : GetM α0} {b0 : ByteArray} {v0 : α0}
    {g1 : GetM α1} {b1 : ByteArray} {v1 : α1}
    {g2 : GetM α2} {b2 : ByteArray} {v2 : α2}
    {g3 : GetM α3} {b3 : ByteArray} {v3 : α3}
    {g4 : GetM α4} {b4 : ByteArray} {v4 : α4}
    {g5 : GetM α5} {b5 : ByteArray} {v5 : α5}
    (h0 : GetSpec g0 b0 v0)
    (h1 : GetSpec g1 b1 v1)
    (h2 : GetSpec g2 b2 v2)
    (h3 : GetSpec g3 b3 v3)
    (h4 : GetSpec g4 b4 v4)
    (h5 : GetSpec g5 b5 v5)
    (f : α0 → α1 → α2 → α3 → α4 → α5 → β) :
    GetSpec (do
      let x0 ← g0
      let x1 ← g1
      let x2 ← g2
      let x3 ← g3
      let x4 ← g4
      let x5 ← g5
      return f x0 x1 x2 x3 x4 x5)
      (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5) (f v0 v1 v2 v3 v4 v5) := by
  let next : α0 → GetM β := fun x0 => do
    let x1 ← g1
    let x2 ← g2
    let x3 ← g3
    let x4 ← g4
    let x5 ← g5
    return f x0 x1 x2 x3 x4 x5
  have tail := getSpecMap5 h1 h2 h3 h4 h5 (f v0)
  have total := GetSpec.bind (next := next) h0 tail
  simpa [next, ByteArray.append_assoc] using total

theorem getSpecMap7 {α0 : Type} {α1 : Type} {α2 : Type} {α3 : Type} {α4 : Type} {α5 : Type} {α6 : Type} {β : Type}
    {g0 : GetM α0} {b0 : ByteArray} {v0 : α0}
    {g1 : GetM α1} {b1 : ByteArray} {v1 : α1}
    {g2 : GetM α2} {b2 : ByteArray} {v2 : α2}
    {g3 : GetM α3} {b3 : ByteArray} {v3 : α3}
    {g4 : GetM α4} {b4 : ByteArray} {v4 : α4}
    {g5 : GetM α5} {b5 : ByteArray} {v5 : α5}
    {g6 : GetM α6} {b6 : ByteArray} {v6 : α6}
    (h0 : GetSpec g0 b0 v0)
    (h1 : GetSpec g1 b1 v1)
    (h2 : GetSpec g2 b2 v2)
    (h3 : GetSpec g3 b3 v3)
    (h4 : GetSpec g4 b4 v4)
    (h5 : GetSpec g5 b5 v5)
    (h6 : GetSpec g6 b6 v6)
    (f : α0 → α1 → α2 → α3 → α4 → α5 → α6 → β) :
    GetSpec (do
      let x0 ← g0
      let x1 ← g1
      let x2 ← g2
      let x3 ← g3
      let x4 ← g4
      let x5 ← g5
      let x6 ← g6
      return f x0 x1 x2 x3 x4 x5 x6)
      (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6) (f v0 v1 v2 v3 v4 v5 v6) := by
  let next : α0 → GetM β := fun x0 => do
    let x1 ← g1
    let x2 ← g2
    let x3 ← g3
    let x4 ← g4
    let x5 ← g5
    let x6 ← g6
    return f x0 x1 x2 x3 x4 x5 x6
  have tail := getSpecMap6 h1 h2 h3 h4 h5 h6 (f v0)
  have total := GetSpec.bind (next := next) h0 tail
  simpa [next, ByteArray.append_assoc] using total

end Compilatrix.IxIR.Bounded
