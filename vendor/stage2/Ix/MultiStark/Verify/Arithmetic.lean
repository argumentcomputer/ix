module
public import Ix.MultiStark.Verify.Basic

/-! The pure verifier's field operations use the existing IxBy Goldilocks
definitions. Unlike the primitive's total inverse-zero convention, protocol
division explicitly rejects a zero denominator, including a zero extension
norm. It never turns a native panic into a successful zero quotient. -/

public section
@[expose] section

namespace MultiStark.Verify.Arithmetic

inductive Error where
  | zeroDenominator | logDegree
  deriving BEq, DecidableEq, Repr, Inhabited

def zero : Ext := ⟨0, 0⟩
def one : Ext := ⟨1, 0⟩
def basis : Ext := ⟨0, 1⟩
def embed (value : Field) : Ext := ⟨value, 0⟩
def fromNat (value : Nat) : Ext := embed (Ix.Ixby.Goldilocks.reduce value)
def neg (value : Ext) : Ext := ⟨value.c0.neg, value.c1.neg⟩
def scale (value : Ext) (scalar : Field) : Ext := ⟨value.c0.mul scalar, value.c1.mul scalar⟩

def inverseBase (value : Field) : Except Error Field :=
  if value.val == 0 then .error .zeroDenominator else .ok value.inverse

def inverse (value : Ext) : Except Error Ext := do
  let norm := (value.c0.mul value.c0).sub ((Ix.Ixby.Goldilocks.mul 7 value.c1).mul value.c1)
  let inv ← inverseBase norm
  return ⟨value.c0.mul inv, value.c1.neg.mul inv⟩

def divide (left right : Ext) : Except Error Ext := return left.mul (← inverse right)

def pow (value : Ext) (exponent : Nat) : Ext := go (exponent.log2 + 1) exponent where
  go : Nat → Nat → Ext
    | 0, _ => one
    | budget + 1, n =>
      if n == 0 then one else
        let half := go budget (n / 2)
        let square := half.mul half
        if n % 2 == 0 then square else square.mul value

def pow2 (value : Ext) : Nat → Ext
  | 0 => value
  | n + 1 => let previous := pow2 value n; previous.mul previous

/-- Exact native Goldilocks subgroup-generator table (Plonky3 3152b14a),
indexed by log2 subgroup size. Unsupported degrees fail before any shift. -/
def twoAdicGenerator (bits : Nat) : Except Error Field :=
  match (#[
    0x0000000000000001, 0xffffffff00000000, 0x0001000000000000,
    0xfffffffeff000001, 0xefffffff00000001, 0x00003fffffffc000,
    0x0000008000000000, 0xf80007ff08000001, 0xbf79143ce60ca966,
    0x1905d02a5c411f4e, 0x9d8f2ad78bfed972, 0x0653b4801da1c8cf,
    0xf2c35199959dfcb6, 0x1544ef2335d17997, 0xe0ee099310bba1e2,
    0xf6b2cffe2306baac, 0x54df9630bf79450e, 0xabd0a6e8aa3d8a0e,
    0x81281a7b05f9beac, 0xfbd41c6b8caa3302, 0x30ba2ecd5e93e76d,
    0xf502aef532322654, 0x4b2a18ade67246b5, 0xea9d5a1336fbc98b,
    0x86cdcc31c307e171, 0x4bbaf5976ecfefd8, 0xed41d05b78d6e286,
    0x10d78dd8915a171d, 0x59049500004a4485, 0xdfa8c93ba46d2666,
    0x7e9bd009b86a0845, 0x400a7f755588e659, 0x185629dcda58878c] : Array Nat)[bits]? with
  | some value => .ok (Ix.Ixby.Goldilocks.reduce value)
  | none => .error .logDegree

/-- Degree-two coordinate arithmetic over the OOD challenge field. These
coordinates are themselves Ext values, so collapsing them into one Ext would
lose the two separate polynomial identities of native logUp evaluation. -/
structure Coordinates where
  c0 : Ext
  c1 : Ext
  deriving BEq, DecidableEq, Repr

def Coordinates.zero : Coordinates := ⟨Arithmetic.zero, Arithmetic.zero⟩
def Coordinates.one : Coordinates := ⟨Arithmetic.one, Arithmetic.zero⟩
def Coordinates.embed (value : Ext) : Coordinates := ⟨value, Arithmetic.zero⟩
def Coordinates.fromExt (value : Ext) : Coordinates := ⟨Arithmetic.embed value.c0, Arithmetic.embed value.c1⟩
def Coordinates.add (left right : Coordinates) : Coordinates :=
  ⟨left.c0.add right.c0, left.c1.add right.c1⟩
def Coordinates.sub (left right : Coordinates) : Coordinates :=
  ⟨left.c0.sub right.c0, left.c1.sub right.c1⟩
def Coordinates.scale (value : Coordinates) (scalar : Ext) : Coordinates :=
  ⟨value.c0.mul scalar, value.c1.mul scalar⟩
def Coordinates.mul (left right : Coordinates) : Coordinates :=
  ⟨(left.c0.mul right.c0).add (Arithmetic.scale (left.c1.mul right.c1) 7),
    (left.c0.mul right.c1).add (left.c1.mul right.c0)⟩

end MultiStark.Verify.Arithmetic
