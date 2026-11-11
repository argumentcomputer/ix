import IxCC.Ixon.Address

/-! # Representation helpers of the decoded environment

The byte order of addresses (`Address.cmpBytes` and the `Ord` instance), the
reading of an address from hexadecimal (`Address.fromString`), and the
little-endian bytes of a `Nat` literal's blob (`V3.natFromBytesLE` and its
inverse on the canonical encoding, `V3.natBytesLE`). None of them is typing:
they were kept with the erased type checker (`IxCC.Ixon.V3.Tc`), and moved
here because ingress (`Src.Ingress`), the pinned identities (`Src.Pinned`),
the sidecar's reader (`Src.Hints`), the primitive table (`V3.PrimAddrs`) and
the resource profile (`V3.Validate`) use them
(`docs/kernel-front-end-design.md`, "The switch", step 2). -/

namespace IxCC.Ixon

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

namespace V3

/-- The little-endian bytes of `x`, least significant first, with no trailing
zero byte except for zero itself (`#[0]`). -/
def natBytesLE (x : Nat) : Array UInt8 :=
  if x == 0 then #[0] else (go x x).toArray
where
  go : Nat → Nat → List UInt8
    | _, 0 => []
    | 0, _ => []
    | fuel + 1, n => n.toUInt8 :: go fuel (n / 256)

/-- The natural number a little-endian `Nat` literal blob denotes. -/
def natFromBytesLE (xs : Array UInt8) : Nat :=
  xs.foldr (fun b n => n * 256 + b.toNat) 0

end V3
end IxCC.Ixon
