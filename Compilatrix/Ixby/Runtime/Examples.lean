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

def replicate (n : Nat) : Nat :=
  (Array.replicate n 7).foldl (· + ·) 0

def power (a b : Nat) : Nat := a ^ b

def cacheNatural (n : Nat) : Nat := (n / 1).toUInt32.toNat

def deferredArithmetic (a b : Nat) : Nat :=
  let n := (a + a / (b + 1) + a % (b + 1)) * a - b
  n + n.toUInt32.toNat

@[noinline] def tailSum : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => tailSum n (acc + n)

end Compilatrix.Ixby.Runtime.Examples
