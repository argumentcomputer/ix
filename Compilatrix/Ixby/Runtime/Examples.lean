import Ix.Ixby.Blake3
import Ix.MultiStark.Verify.Codec.Wire

namespace Compilatrix.Ixby.Runtime.Examples

def choose (n : Nat) : Nat :=
  if h : n < 7 then (⟨n + 1, by omega⟩ : Fin 8).val else n - 3

def sumMapped (offset : Nat) (values : List Nat) : Nat :=
  (values.map (fun n => n + offset)).foldl (· + ·) 0

def arrayEdits (values : List Nat) : Nat := Id.run do
  let original := values.toArray
  let changed := ((original.push 19).set! 0 37).pop
  return original.foldl (· + ·) 0 + changed.foldl (· + ·) 0

def byteSum (values : Array UInt8) : Nat :=
  values.foldl (fun n b => n + b.toNat) 0

def byteHash (values : Array UInt8) : Nat :=
  byteSum (Ix.Ixby.Blake3.hash values)

def byteSlices (values : Array UInt8) (start stop : Nat) : Nat :=
  byteSum (values.extract start stop ++ values.extract stop (stop + 5))

def widenBytes (values : Array UInt8) : Nat :=
  let values := values.map UInt8.toNat
  ((values.push 1000).set! 0 300).foldl (· + ·) 0

def boxBytes (values : Array UInt8) : Nat :=
  (values.map fun n => some n).foldl (fun sum b => sum + (b.getD 7).toNat) 0

def concatLeft (values : Array UInt8) (count : Nat) : Array UInt8 :=
  (List.range count).foldl (fun acc i =>
    let start := i % (values.size + 1)
    acc ++ values.extract start (start + 9)) #[]

def concatRight (values : Array UInt8) (count : Nat) : Array UInt8 :=
  (List.range count).foldr (fun i acc =>
    let start := i % (values.size + 1)
    values.extract start (start + 9) ++ acc) #[]

def concatMixed (values : Array UInt8) (count : Nat) : Array UInt8 :=
  (List.range count).foldl (fun acc i =>
    let chunk := values.extract (i % (values.size + 1)) (i % (values.size + 1) + 9)
    if i % 2 == 0 then acc ++ chunk else chunk ++ acc) #[]

def ropeEdits (values : Array UInt8) (count : Nat) : Nat :=
  let data := concatLeft values count
  byteSum (data.extract 3 (data.size - 1)) + widenBytes data + boxBytes data

def wireWriter (values : Array UInt8) (limit : Nat) : Array UInt8 :=
  (MultiStark.Verify.Codec.Wire.encode { bytes := limit, vector := 65536, items := 65536 }
    (MultiStark.Verify.Codec.Wire.writeList MultiStark.Verify.Codec.Wire.writeByte values.toList)).toOption.getD #[]

def wireCanonical (actual expected : Array UInt8) : Nat :=
  match MultiStark.Verify.Codec.Wire.canonicalize (fun (_ : Unit) => .ok actual) expected () with
  | .ok _ => 1
  | .error _ => 0

def wireFieldRead (values : Array UInt8) (offset : Nat) : Nat :=
  match MultiStark.Verify.Codec.Wire.readField.run
      { bytes := values, offset, vectorLimit := 17, items := 29 } with
  | .error .truncated => 0
  | .error .field => 1
  | .error _ => 2
  | .ok (field, state) =>
    3 + field.val * 2 ^ 128 + state.offset * 2 ^ 64 + state.vectorLimit * 2 ^ 32 +
      state.items + byteSum state.bytes * 2 ^ 192

private def writeFieldResult (value : Ix.Ixby.Goldilocks) (initial : Array UInt8)
    (limit : Nat) : Array UInt8 :=
  match MultiStark.Verify.Codec.Wire.writeField value
      { bytes := initial, limit, vectorLimit := 17, items := 29 } with
  | .error .byteLimit => #[0]
  | .error _ => #[1]
  | .ok (_, state) => #[2, state.vectorLimit.toUInt8, state.items.toUInt8] ++ state.bytes

def wireFieldWrite (n : Nat) (initial : Array UInt8) (limit : Nat) : Array UInt8 :=
  writeFieldResult (Ix.Ixby.Goldilocks.reduce n) initial limit

def wireFieldWriteRaw (n : Nat) (initial : Array UInt8) (limit : Nat) : Array UInt8 :=
  writeFieldResult ⟨n % Ix.Ixby.goldilocksModulus, Nat.mod_lt _ (by decide)⟩ initial limit

def replicate (n : Nat) : Nat :=
  (Array.replicate n 7).foldl (· + ·) 0

def power (a b : Nat) : Nat := a ^ b

def cacheNatural (n : Nat) : Nat := (n / 1).toUInt32.toNat

def deferredArithmetic (a b : Nat) : Nat :=
  let n := (a + a / (b + 1) + a % (b + 1)) * a - b
  n + n.toUInt32.toNat

def fieldArithmetic (a b : Nat) : Nat :=
  let x := Ix.Ixby.Goldilocks.reduce a
  let y := Ix.Ixby.Goldilocks.reduce b
  ((x.add y).mul (x.sub y).inverse).neg.val

def fieldMixed (a b : Nat) : Nat :=
  let n := (Ix.Ixby.Goldilocks.reduce a).val
  deferredArithmetic n b + n.toUInt8.toNat + n.log2 + (n >>> 17)

def fieldPower (a b : Nat) : Nat := (Ix.Ixby.Goldilocks.reduce a).pow b |>.val

def fieldCompare (a b : Nat) : Nat :=
  let x := Ix.Ixby.Goldilocks.reduce a
  let y := Ix.Ixby.Goldilocks.reduce b
  (if x == y then 1 else 0) + (if x.val == b then 2 else 0) + (if a == y.val then 4 else 0)

def extensionArithmetic (a b c d : Nat) : Nat :=
  let x : Ix.Ixby.ExtGoldilocks := ⟨Ix.Ixby.Goldilocks.reduce a, Ix.Ixby.Goldilocks.reduce b⟩
  let y : Ix.Ixby.ExtGoldilocks := ⟨Ix.Ixby.Goldilocks.reduce c, Ix.Ixby.Goldilocks.reduce d⟩
  let z := (x.mul y).add (x.sub y).inverse
  z.c0.val + 2 ^ 64 * z.c1.val + if x == y then 1 else 0

def extensionStorage (a b : Nat) : Nat :=
  let x : Ix.Ixby.ExtGoldilocks := ⟨Ix.Ixby.Goldilocks.reduce a, Ix.Ixby.Goldilocks.reduce b⟩
  let values := #[x, x.inverse, x.add x]
  let z := values.foldl (fun acc y => acc.mul y) x
  match z with
  | ⟨c0, c1⟩ => c0.val + c1.val

@[noinline] def tailSum : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => tailSum n (acc + n)

end Compilatrix.Ixby.Runtime.Examples
