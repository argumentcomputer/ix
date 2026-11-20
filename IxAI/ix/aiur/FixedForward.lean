import Aiur.Library.U32.Goldilocks
import Aiur.Library.U8
import IxAICore

/-!
# The triage model's forward pass as a formal Aiur program

`Fixed` implements `IxAICore`'s fixed-point arithmetic over the Goldilocks field:

* `shr8 s` is `⌊s / 256⌋`, the rounding of every product and dot product. The quotient and
  remainder come from a hint and are checked, not trusted: the remainder is one range-checked byte
  and the quotient, offset by 2^47, six range-checked bytes, and `256 q + r = s` must hold. For
  `|s| < 2^55` that admits exactly the integer floor, because both sides are integers far below
  the field's characteristic.
* `sign_split v` gives `v ≥ 0` (bit 55 of `v + 2^55`, decomposed into range-checked bytes) and
  `v ≠ 0` (a hinted inverse, with `v · (1 − nz) = 0` forcing `nz = 1` whenever `v ≠ 0`).
* `relu v = v · [v ≥ 0]` and `pos v = [v ≥ 0] · [v ≠ 0]`, as in `Fx.relu` and `Fx.pos`.

`forward` is `Model.outputs` for 8 features, 16 hidden units and 11 outputs. The tests below run
it with an honest hint provider against `IxAICore`, check that dishonest hints are rejected, and
compile it to a circuit.
-/

namespace IxAIAiur
open Aiur

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def client : Modules.Program Nat := aiur_library% Library.U8.templates ⟦
module Fixed {
    fn shr8(s: Field) -> Field {
        let w = hint::<[Field; 8]>("fx.shr8", s);
        let (r, b0) = UInt8::from_fields(w[0], w[1]);
        let (b1, b2) = UInt8::from_fields(w[2], w[3]);
        let (b3, b4) = UInt8::from_fields(w[4], w[5]);
        let (b5, z) = UInt8::from_fields(w[6], w[7]);
        assert_eq!(UInt8::to_field(z), 0, "fx.shr8 padding");
        let offset = UInt8::to_field(b0) + 256 * UInt8::to_field(b1) + 65536 * UInt8::to_field(b2)
            + 16777216 * UInt8::to_field(b3) + 4294967296 * UInt8::to_field(b4)
            + 1099511627776 * UInt8::to_field(b5);
        let q = offset - 140737488355328;
        assert_eq!(256 * q + UInt8::to_field(r), s, "fx.shr8");
        q
    }
    fn sign_split(v: Field) -> (Field, Field) {
        let w = hint::<[Field; 8]>("fx.sign", v);
        let (b0, b1) = UInt8::from_fields(w[0], w[1]);
        let (b2, b3) = UInt8::from_fields(w[2], w[3]);
        let (b4, b5) = UInt8::from_fields(w[4], w[5]);
        let (b6, z) = UInt8::from_fields(w[6], 0);
        let offset = UInt8::to_field(b0) + 256 * UInt8::to_field(b1) + 65536 * UInt8::to_field(b2)
            + 16777216 * UInt8::to_field(b3) + 4294967296 * UInt8::to_field(b4)
            + 1099511627776 * UInt8::to_field(b5) + 281474976710656 * UInt8::to_field(b6);
        assert_eq!(offset, v + 36028797018963968, "fx.sign range");
        let bits = UInt8::bit_decomposition(b6);
        let nz = v * w[7];
        assert_eq!(v * (1 - nz), 0, "fx.sign zero test");
        (bits[7], nz)
    }
    fn mul(a: Field, b: Field) -> Field { shr8(a * b) }
    fn relu(v: Field) -> Field { let (nonneg, _nz) = sign_split(v); v * nonneg }
    fn pos(v: Field) -> Field { let (nonneg, nz) = sign_split(v); nonneg * nz }
    fn dot8(a: [Field; 8], b: [Field; 8]) -> Field { shr8(a[0] * b[0] + a[1] * b[1] + a[2] * b[2] + a[3] * b[3] + a[4] * b[4] + a[5] * b[5] + a[6] * b[6] + a[7] * b[7]) }
    fn dot16(a: [Field; 16], b: [Field; 16]) -> Field { shr8(a[0] * b[0] + a[1] * b[1] + a[2] * b[2] + a[3] * b[3] + a[4] * b[4] + a[5] * b[5] + a[6] * b[6] + a[7] * b[7] + a[8] * b[8] + a[9] * b[9] + a[10] * b[10] + a[11] * b[11] + a[12] * b[12] + a[13] * b[13] + a[14] * b[14] + a[15] * b[15]) }
    fn forward(w1: [[Field; 8]; 16], b1: [Field; 16], w2: [[Field; 16]; 11], b2: [Field; 11],
               x: [Field; 8]) -> [Field; 11] {
        let h0 = relu(dot8(w1[0], x) + b1[0]);
        let h1 = relu(dot8(w1[1], x) + b1[1]);
        let h2 = relu(dot8(w1[2], x) + b1[2]);
        let h3 = relu(dot8(w1[3], x) + b1[3]);
        let h4 = relu(dot8(w1[4], x) + b1[4]);
        let h5 = relu(dot8(w1[5], x) + b1[5]);
        let h6 = relu(dot8(w1[6], x) + b1[6]);
        let h7 = relu(dot8(w1[7], x) + b1[7]);
        let h8 = relu(dot8(w1[8], x) + b1[8]);
        let h9 = relu(dot8(w1[9], x) + b1[9]);
        let h10 = relu(dot8(w1[10], x) + b1[10]);
        let h11 = relu(dot8(w1[11], x) + b1[11]);
        let h12 = relu(dot8(w1[12], x) + b1[12]);
        let h13 = relu(dot8(w1[13], x) + b1[13]);
        let h14 = relu(dot8(w1[14], x) + b1[14]);
        let h15 = relu(dot8(w1[15], x) + b1[15]);
        let hs = [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15];
        [dot16(w2[0], hs) + b2[0], dot16(w2[1], hs) + b2[1], dot16(w2[2], hs) + b2[2], dot16(w2[3], hs) + b2[3], dot16(w2[4], hs) + b2[4], dot16(w2[5], hs) + b2[5], dot16(w2[6], hs) + b2[6], dot16(w2[7], hs) + b2[7], dot16(w2[8], hs) + b2[8], dot16(w2[9], hs) + b2[9], dot16(w2[10], hs) + b2[10]]
    }
}
⟧

def entries : List String := ["Fixed::shr8", "Fixed::mul", "Fixed::relu", "Fixed::pos", "Fixed::dot8", "Fixed::forward"]

def source : Modules.Program Nat := Library.U8.source.append client

abbrev F := Library.U32.Goldilocks.F

def p : Nat := 18446744069414584321

def toInt (x : F) : Int := let v := x.val; if v > p / 2 then (v : Int) - p else v

def ofInt (i : Int) : F := (i : F)

def bytesOf (n : Nat) (k : Nat) : List F := (List.range k).map fun i => (((n / 256 ^ i) % 256 : Nat) : F)

/-- The honest host. Its answers are checked by the program, so it is not trusted. -/
def hints : HintDispatcher F := fun channel key =>
  match channel, key with
  | "fx.shr8", .field s =>
    let v := toInt s
    let q := v >>> 8
    let r := v - 256 * q
    .ok (.tuple ((bytesOf r.toNat 1 ++ bytesOf (q + 140737488355328).toNat 6 ++ [0]).map .field))
  | "fx.sign", .field v =>
    let i := toInt v
    let inv : F := if i == 0 then 0 else v⁻¹
    .ok (.tuple ((bytesOf (i + 36028797018963968).toNat 7 ++ [inv]).map .field))
  | _, _ => .error .unavailable

def fx (x : IxAICore.Fx) : SourceValue F := .field (ofInt x.raw)
def vec (xs : List IxAICore.Fx) : SourceValue F := .tuple (xs.map fx)
def mat (xss : List (List IxAICore.Fx)) : SourceValue F := .tuple (xss.map vec)

def get {α : Type} : Except String α → IO α := IO.ofExcept

def run : IO Unit := do
  let prepared ← get <| Modules.prepare (source.toField F) entries
  let honest := prepared.environment.source.checkedHints hints
  let call (name : String) (args : List (SourceValue F)) : IO (SourceValue F) := do
    let (v, _) ← get <| prepared.run ("Fixed::" ++ name) args (fuel := 10000000) (hints := honest)
    pure v
  -- Scalar operations agree with IxAICore.Fx.
  let samples : List Int := [0, 1, -1, 255, 256, -256, 257, -257, 70000, -70000, 123456789, -987654321]
  for a in samples do
    for b in [0, 1, -1, 3, -300, 4096, -65536] do
      let expected := IxAICore.Fx.mul ⟨a⟩ ⟨b⟩
      let actual ← call "mul" [.field (ofInt a), .field (ofInt b)]
      unless actual == .field (ofInt expected.raw) do
        throw (IO.userError s!"mul {a} {b}: got {repr actual}, expected {expected.raw}")
    let r ← call "relu" [.field (ofInt a)]
    unless r == .field (ofInt (IxAICore.Fx.relu ⟨a⟩).raw) do throw (IO.userError s!"relu {a}")
    let ps ← call "pos" [.field (ofInt a)]
    unless ps == .field (if IxAICore.Fx.pos ⟨a⟩ then 1 else 0) do throw (IO.userError s!"pos {a}")
  -- The forward pass agrees with Model.outputs, for initial and trained weights, on held-out data.
  let cfg : IxAICore.Config :=
    { seed := 42, hidden := 16, lrRaw := 2, epochs := 1, batch := 20, trainSize := 40, testSize := 12 }
  let models := [cfg.init IxAICore.Triage.spec, IxAICore.train IxAICore.Triage.spec cfg]
  let mut checked := 0
  for m in models do
    for f in cfg.test IxAICore.Triage.spec do
      let x := IxAICore.Triage.spec.inputs f
      let expected := m.outputs x
      let actual ← call "forward" [mat m.w1, vec m.b1, mat m.w2, vec m.b2, vec x]
      unless actual == vec expected do throw (IO.userError s!"forward mismatch")
      checked := checked + 1
  IO.println s!"forward pass: {checked} examples agree with IxAICore.Model.outputs"
  -- Dishonest hints are rejected: a remainder off by one, a sign flipped, a forged zero test.
  let bad (name : String) (dispatcher : HintDispatcher F) (args : List (SourceValue F)) : IO Unit := do
    let h := prepared.environment.source.checkedHints dispatcher
    unless (prepared.run ("Fixed::" ++ name) args (fuel := 10000000) (hints := h)).toOption.isNone do
      throw (IO.userError s!"dishonest hint accepted in {name}")
  let shifted : HintDispatcher F := fun c k => match c, k with
    | "fx.shr8", .field s =>
      let v := toInt s; let q := (v >>> 8) + 1; let r := v - 256 * q
      .ok (.tuple ((bytesOf r.toNat 1 ++ bytesOf (q + 140737488355328).toNat 6 ++ [0]).map .field))
    | c, k => hints c k
  bad "mul" shifted [.field (ofInt 1000), .field (ofInt 3)]
  let wrapped : HintDispatcher F := fun c k => match c, k with
    | "fx.shr8", .field s =>
      -- A quotient differing by a multiple of p/256 also satisfies 256 q + r = s in the field;
      -- the six-byte range check is what rules it out.
      let v := toInt s; let q := (v >>> 8) + ((p : Int) / 256 + 1); let r := v - 256 * q
      .ok (.tuple ((bytesOf (r % 256).toNat 1 ++ bytesOf ((q + 140737488355328) % (2 ^ 64)).toNat 6 ++ [0]).map .field))
    | c, k => hints c k
  bad "mul" wrapped [.field (ofInt 1000), .field (ofInt 3)]
  let flipped : HintDispatcher F := fun c k => match c, k with
    | "fx.sign", .field v =>
      let i := toInt v
      .ok (.tuple ((bytesOf (-i + 36028797018963968).toNat 7 ++ [0]).map .field))
    | c, k => hints c k
  bad "relu" flipped [.field (ofInt 500)]
  let forged : HintDispatcher F := fun c k => match c, k with
    | "fx.sign", .field v =>
      let i := toInt v
      .ok (.tuple ((bytesOf (i + 36028797018963968).toNat 7 ++ [0]).map .field))
    | c, k => hints c k
  bad "pos" forged [.field (ofInt 500)]
  IO.println "dishonest hints rejected: shifted quotient, wrapped quotient, flipped sign, forged zero test"
  let compiled ← get prepared.compileOptimized
  let chips := compiled.circuit.system.chips
  IO.println s!"circuit: {chips.length} chips"

end IxAIAiur

def main : IO Unit := IxAIAiur.run
