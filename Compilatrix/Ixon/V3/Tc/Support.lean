import Compilatrix.Ixon.V3.Env
import Lean.Declaration
import Std.Data.TreeMap

/-! Pure representation helpers for the pinned anonymous typechecker.
No ix native integer-conversion or frontend FFI is imported. -/

namespace Compilatrix.Ixon

def Address.cmpBytes (a b : Address) : Ordering :=
  compare a.hash.data.toList b.hash.data.toList

instance : Ord Address := ⟨Address.cmpBytes⟩

def Address.fromString (s : String) : Option Address := do
  let bytes ← go s.toList
  Address.ofBytes? ⟨bytes.toArray⟩
where
  digit (c : Char) : Option Nat :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  go : List Char → Option (List UInt8)
    | [] => some []
    | a :: b :: rest => do
      let a ← digit a
      let b ← digit b
      return (a * 16 + b).toUInt8 :: (← go rest)
    | _ => none

namespace V3.Tc

def finishHash (h : Blake3.Rust.Hasher) : Address :=
  let digest := h.finalizeWithLength 32 (by
    cases System.Platform.numBits_eq with
    | inl h32 => rw [h32]; decide
    | inr h64 => rw [h64]; decide)
  ⟨digest.val, digest.property⟩

def tcUInt64BytesLE (x : UInt64) : ByteArray :=
  ⟨(Array.range 8).map fun i => (x >>> (8 * i).toUInt64).toUInt8⟩

def tcNatBytesLE (x : Nat) : Array UInt8 :=
  if x == 0 then #[0] else (go x x).toArray
where
  go : Nat → Nat → List UInt8
    | _, 0 => []
    | 0, _ => []
    | fuel + 1, n => n.toUInt8 :: go fuel (n / 256)

def natFromBytesLE (xs : Array UInt8) : Nat :=
  xs.foldr (fun b n => n * 256 + b.toNat) 0

end V3.Tc
end Compilatrix.Ixon
