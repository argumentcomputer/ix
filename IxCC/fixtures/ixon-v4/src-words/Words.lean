/-! The fixed-width words fixture (`fixtures/ixon-v4/src-words`, stage W1): every operation of
every width, one root per width, so that the closure holds every word operation's reference body
and, compiled with `ix compile --equations`, every primitive operation's stored equation. Its
roots take an operation number and two `Nat`s, convert them to words, and return the result as a
`Nat` (a decision as `0` or `1`). From the data-types plan's probe P17. -/

namespace Words

def u8 (op a b : Nat) : Nat :=
  let x := a.toUInt8; let y := b.toUInt8
  match op with
  | 0 => (x + y).toNat | 1 => (x - y).toNat | 2 => (x * y).toNat | 3 => (x / y).toNat
  | 4 => (x % y).toNat | 5 => (x &&& y).toNat | 6 => (x ||| y).toNat | 7 => (x ^^^ y).toNat
  | 8 => (x <<< y).toNat | 9 => (x >>> y).toNat | 10 => (~~~x).toNat | 11 => (-x).toNat
  | 12 => if x = y then 1 else 0 | 13 => if x < y then 1 else 0 | 14 => if x ≤ y then 1 else 0
  | 15 => x.toUInt16.toNat | 16 => x.toUInt32.toNat | _ => x.toUInt64.toNat

def u16 (op a b : Nat) : Nat :=
  let x := a.toUInt16; let y := b.toUInt16
  match op with
  | 0 => (x + y).toNat | 1 => (x - y).toNat | 2 => (x * y).toNat | 3 => (x / y).toNat
  | 4 => (x % y).toNat | 5 => (x &&& y).toNat | 6 => (x ||| y).toNat | 7 => (x ^^^ y).toNat
  | 8 => (x <<< y).toNat | 9 => (x >>> y).toNat | 10 => (~~~x).toNat | 11 => (-x).toNat
  | 12 => if x = y then 1 else 0 | 13 => if x < y then 1 else 0 | 14 => if x ≤ y then 1 else 0
  | 15 => x.toUInt8.toNat | 16 => x.toUInt32.toNat | _ => x.toUInt64.toNat

def u32 (op a b : Nat) : Nat :=
  let x := a.toUInt32; let y := b.toUInt32
  match op with
  | 0 => (x + y).toNat | 1 => (x - y).toNat | 2 => (x * y).toNat | 3 => (x / y).toNat
  | 4 => (x % y).toNat | 5 => (x &&& y).toNat | 6 => (x ||| y).toNat | 7 => (x ^^^ y).toNat
  | 8 => (x <<< y).toNat | 9 => (x >>> y).toNat | 10 => (~~~x).toNat | 11 => (-x).toNat
  | 12 => if x = y then 1 else 0 | 13 => if x < y then 1 else 0 | 14 => if x ≤ y then 1 else 0
  | 15 => x.toUInt8.toNat | 16 => x.toUInt16.toNat | _ => x.toUInt64.toNat

def u64 (op a b : Nat) : Nat :=
  let x := a.toUInt64; let y := b.toUInt64
  match op with
  | 0 => (x + y).toNat | 1 => (x - y).toNat | 2 => (x * y).toNat | 3 => (x / y).toNat
  | 4 => (x % y).toNat | 5 => (x &&& y).toNat | 6 => (x ||| y).toNat | 7 => (x ^^^ y).toNat
  | 8 => (x <<< y).toNat | 9 => (x >>> y).toNat | 10 => (~~~x).toNat | 11 => (-x).toNat
  | 12 => if x = y then 1 else 0 | 13 => if x < y then 1 else 0 | 14 => if x ≤ y then 1 else 0
  | 15 => x.toUInt8.toNat | 16 => x.toUInt16.toNat | _ => x.toUInt32.toNat

end Words
