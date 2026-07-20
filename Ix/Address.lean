module
public import Lean.ToExpr
public import Ix.ByteArray
public import Ix.Common
public import Blake3.Rust

public section

deriving instance Lean.ToExpr for ByteArray
deriving instance Repr for ByteArray

/-- A 32-byte Blake3 content hash used as a content address for Ix objects. -/
structure Address where
  hash : ByteArray
  deriving Lean.ToExpr, BEq

/-- Blake3 output is uniformly distributed, so the first 8 bytes are
    already a full-quality 64-bit hash. The derived instance instead
    folds all 32 bytes through the generic `ByteArray` hash on every
    probe of every Address-keyed map (the kernel's whnf/defeq/infer
    caches and the intern table are all keyed this way).

    Adversarial collisions: `Hashable` is 64-bit regardless, so ANY
    instance (this one or the derived 32-byte `mixHash` fold — both
    unseeded, public functions) admits birthday bucket collisions at
    ~2^32 blake3 evaluations per colliding pair, ~2^57 for a 10-deep
    bucket; a blake3-prefix collision additionally costs real blake3
    preimage work, whereas `mixHash` folds may have cheaper analytic
    shortcuts (and the Rust mirror's `FxHashMap` is weaker still). Deep
    buckets degrade probes to linear scans — a complexity-DoS lever,
    never unsoundness: equality is always the full 32-byte `BEq`, and
    kernel work per constant is fuel-bounded. If HashDoS hardening is
    ever required for hostile envs, the fix is seeded hashing or
    Ord-tree maps at the ingress-facing tables, not a different
    unseeded 64-bit function. -/
instance : Hashable Address where
  hash a :=
    let h := a.hash
    (h.get! 0).toUInt64
    ||| ((h.get! 1).toUInt64 <<< 8)
    ||| ((h.get! 2).toUInt64 <<< 16)
    ||| ((h.get! 3).toUInt64 <<< 24)
    ||| ((h.get! 4).toUInt64 <<< 32)
    ||| ((h.get! 5).toUInt64 <<< 40)
    ||| ((h.get! 6).toUInt64 <<< 48)
    ||| ((h.get! 7).toUInt64 <<< 56)

/-- Compute the Blake3 hash of a `ByteArray`, returning an `Address`. -/
def Address.blake3 (x: ByteArray) : Address := ⟨(Blake3.Rust.hash x).val⟩

/-- Convert a nibble (0--15) to its lowercase hexadecimal character. -/
def hexOfNat : Nat -> Option Char
| 0 => .some '0'
| 1 => .some '1'
| 2 => .some '2'
| 3 => .some '3'
| 4 => .some '4'
| 5 => .some '5'
| 6 => .some '6'
| 7 => .some '7'
| 8 => .some '8'
| 9 => .some '9'
| 10 => .some 'a'
| 11 => .some 'b'
| 12 => .some 'c'
| 13 => .some 'd'
| 14 => .some 'e'
| 15 => .some 'f'
|  _ => .none

/-- Parse a hexadecimal character (case-insensitive) into a nibble value 0--15. -/
def natOfHex : Char -> Option Nat
| '0' => .some 0
| '1' => .some 1
| '2' => .some 2
| '3' => .some 3
| '4' => .some 4
| '5' => .some 5
| '6' => .some 6
| '7' => .some 7
| '8' => .some 8
| '9' => .some 9
| 'a' => .some 10
| 'b' => .some 11
| 'c' => .some 12
| 'd' => .some 13
| 'e' => .some 14
| 'f' => .some 15
| 'A' => .some 10
| 'B' => .some 11
| 'C' => .some 12
| 'D' => .some 13
| 'E' => .some 14
| 'F' => .some 15
|  _ => .none

/-- Convert a byte (UInt8) to a two‐digit big-endian hexadecimal string. -/
def hexOfByte (b : UInt8) : String :=
  let hi := hexOfNat (UInt8.toNat (b >>> 4))
  let lo := hexOfNat (UInt8.toNat (b &&& 0xF))
  String.ofList [hi.get!, lo.get!]

/-- Convert a ByteArray to a big-endian hexadecimal string. -/
def hexOfBytes (ba : ByteArray) : String :=
  (ba.toList.map hexOfByte).foldl (· ++ ·) ""

instance : ToString Address where
  toString adr := hexOfBytes adr.hash

instance : Repr Address where
  reprPrec a _ := "#" ++ (toString a).toFormat

instance : Ord Address where
  compare a b := compare a.hash.data.toList b.hash.data.toList

/-- Byte-loop lexicographic comparison. Agrees with the `Ord Address` instance
    (and with Rust's derived `Ord` on `Address([u8; 32])`) but avoids the
    per-compare `List` conversion; use this on hot paths. -/
def Address.cmpBytes (a b : Address) : Ordering := Id.run do
  let x := a.hash
  let y := b.hash
  let n := min x.size y.size
  for i in [0:n] do
    let xi := x[i]!
    let yi := y[i]!
    if xi < yi then return .lt
    if yi < xi then return .gt
  return compare x.size y.size

instance : Inhabited Address where
  default := Address.blake3 ⟨#[]⟩

/-- Decode two hex characters (high nibble, low nibble) into a single byte. -/
def byteOfHex : Char -> Char -> Option UInt8
| hi, lo => do
  let hi <- natOfHex hi
  let lo <- natOfHex lo
  UInt8.ofNat (hi <<< 4 + lo)

/-- Parse a hexadecimal string into a `ByteArray`. Returns `none` on odd length or invalid chars. -/
def bytesOfHex (s: String) : Option ByteArray := do
  let bs <- go s.toList
  return ⟨bs.toArray⟩
  where
    go : List Char -> Option (List UInt8)
    | hi::lo::rest => do
      let b <- byteOfHex hi lo
      let bs <- go rest
      b :: bs
    | [] => return []
    | _ => .none

/-- Parse a 64-character hex string into an `Address`. Returns `none` if the string is not a valid 32-byte hex encoding. -/
def Address.fromString (s: String) : Option Address := do
  let ba <- bytesOfHex s
  if ba.size == 32 then .some ⟨ba⟩ else .none

/-- Encode an `Address` as a hierarchical `Lean.Name` under the `Ix._#` namespace. -/
def Address.toUniqueName (addr: Address): Lean.Name :=
  .str (.str (.str .anonymous "Ix") "_#") (hexOfBytes addr.hash)

/-- Decode an `Address` from a `Lean.Name` previously created by `Address.toUniqueName`. -/
def Address.fromUniqueName (name: Lean.Name) : Option Address :=
  match name with
  | .str (.str (.str .anonymous "Ix") "_#") s => Address.fromString s
  | _ => .none

end
