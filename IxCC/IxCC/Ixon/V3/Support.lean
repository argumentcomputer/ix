import IxCC.Ixon.Address

/-! # Representation helpers of the decoded environment

The byte order of addresses (`Address.cmpBytes` and the `Ord` instance), the
reading of an address from hexadecimal (`Address.fromString`), and the
little-endian bytes of a `Nat` literal's blob (`V3.natFromBytesLE`,
`V3.canonicalNatBytes`, `V3.decodeNatBlob`, and `V3.natBytesLE`). None of them
is typing: they were kept with IxCC's erased type checker (deleted by the switch
to the certified kernel), and moved here because ingress (`Src.Ingress`), the
pinned identities (`Src.Pinned`), the sidecar's reader (`Src.Hints`), and the
primitive table (`V3.PrimAddrs`) use them (`docs/kernel-front-end-design.md`,
"The switch", step 2). -/

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

/-- Whether `bytes` is a canonical little-endian `Nat` literal blob (matching
`IxC/Kernel/Ixon/Reader.lean`'s `canonicalNatural`): non-empty, and either a
single byte (`#[0]` for zero) or ending in a non-zero byte. -/
def canonicalNatBytes (bytes : ByteArray) : Bool :=
  match bytes.data.back? with
  | none => false
  | some last => last != 0 || bytes.size == 1

/-- Decode a canonical `Nat` literal blob, refusing empty blobs and blobs with
redundant trailing zero bytes. -/
def decodeNatBlob (bytes : ByteArray) : Except String Nat :=
  if canonicalNatBytes bytes then
    .ok (natFromBytesLE bytes.data)
  else
    .error "ixon-v5: noncanonical Nat literal blob"

end V3
end IxCC.Ixon
