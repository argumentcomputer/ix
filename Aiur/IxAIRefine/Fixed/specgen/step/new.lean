import Aiur.Library.U32.Goldilocks
import Aiur.Library.U8
import Aiur.Artifact
import Aiur.Trace.Export
import Aiur.Execution.Hints
import Aiur.Execution.Interface
import IxAICore

/-!
# SGD training of the triage model as a formal Aiur program

`Fixed` implements `IxAICore`'s fixed-point arithmetic over the Goldilocks field:

* `shr8 s` is `⌊s / 256⌋`, the rounding of every product and dot product. The quotient and
  remainder come from a hint and are checked, not trusted: the remainder is one range-checked byte
  and the quotient, offset by 2^47, six range-checked bytes, and `256 q + r = s` must hold. For
  `|s| < 2^55` that admits exactly the integer floor, because both sides are integers far below
  the field's characteristic.
* `sign_split v` gives `v ≥ 0` (bit 55 of `v + 2^55`, decomposed into range-checked bytes) and
  `v ≠ 0` (a hinted inverse, with `v · (1 − nz) = 0` forcing `nz = 1` whenever `v ≠ 0`).
* `relu v = v · [v ≥ 0]` and `pos v = [v ≥ 0] · [v ≠ 0]`, as in `Fx.relu` and `Fx.pos`.

The sizes are fixed: 8 features, 16 hidden units, 11 outputs, batches of 20, 400 training
examples and 600 steps. Each function computes one piece of `IxAICore.Decision`:

| Aiur | `IxAICore` |
|---|---|
| `mul a b` | `Fx.mul a b` |
| `dot8`, `dot11`, `dot16`, `dot20` | `Fx.dot` (one `shr8` of the exact `Fx.dotRaw`) |
| `sum20` | `Fx.sumRaw` (`Fx.sum`, not rounded) |
| `hidden_unit row b x` | `Fx.add (Fx.dot row x) b`, the function zipped in `Model.hidden` |
| `hidden w1 b1 x` | `Model.hidden`: `(z, z.map Fx.relu)` |
| `output_unit row b h` | `Fx.add (Fx.dot row h) b`, the function zipped in `Model.outputs` |
| `outputs w2 b2 h` | `o` in `Model.delta` (`Model.outputs` from `h`) |
| `sub11 o t` | `List.zipWith Fx.sub o t` |
| `back_unit z col dout` | `if Fx.pos z then Fx.dot col dout else Fx.zero` |
| `delta … w2t x t` | `Model.delta m w2T x t`, as `(h, dz, dout)` |
| `deltas … w2t xs ts` | `ds` in `Model.step`, as `(ds.map (·.h), ds.map (·.dz), ds.map (·.dout))` |
| `transpose11x16`, `transpose20x16`, `transpose20x8`, `transpose20x11` | `transposeN` |
| `upd w lr g` | `upd` in `Model.step`: `Fx.sub w (Fx.mul lr g)` |
| `update_row8`, `update_row16` | the row function of `w1` and `w2` in `Model.step` |
| `update_w1`, `update_w2` | the fields `w1` and `w2` of `Model.step` |
| `update_bias16`, `update_bias11` | the fields `b1` and `b2` of `Model.step` |
| `step w1 b1 w2 b2 xs ts lr` | `Model.step lr m batch` for a batch of 20 |
| `example_table xs ts`, `push_block` | the example list `examples`, from 20 blocks of 20 |
| `lookup_example data i` | `getD examples i _` |
| `batch data idx` | `idx.map fun i => getD examples i _` |
| `step_at … lr data idx` | `Config.stepFn` |
| `train_block`, `train` | `train`: `List.foldl` of `Config.stepFn` over the schedule |

`train` takes the schedule as 30 groups of 20 batches (`Config.schedule` in order) and folds
`step_at` over it, 20 steps in each `train_block`. Entry arguments carry no pointers, so `train`
takes the examples as arrays and builds the linked list `Examples` itself. An index outside the
table has no example; `IxAICore` would substitute a default, so `train` agrees with `IxAICore.train`
on schedules whose indices are all below 400, as `Config.schedule`'s are.

Where `IxAICore` rounds, `Fixed` rounds once with `shr8`, at the same place: every dot product
after its exact sum, every product `lr · g`, and nowhere else. Sums, `Fx.add` and `Fx.sub` are
field operations: they agree with `IxAICore`'s integer operations while the integers involved
stay below half the field's characteristic in magnitude. Every value that is rounded or
sign-tested is range-checked below 2^55 by `shr8` or `sign_split`.

The tests below run `step` and `train` with an honest hint provider against `IxAICore`, check
that dishonest hints are rejected, and compile `step` to a circuit.
-/

namespace IxAIAiur
open Aiur

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def client : Modules.Program Nat := aiur_library% Library.U8.templates ⟦
module Fixed {
    enum Examples { Nil, Cons([Field; 8], [Field; 11], &Examples) }
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
    fn dot11(a: [Field; 11], b: [Field; 11]) -> Field { shr8(a[0] * b[0] + a[1] * b[1] + a[2] * b[2] + a[3] * b[3] + a[4] * b[4] + a[5] * b[5] + a[6] * b[6] + a[7] * b[7] + a[8] * b[8] + a[9] * b[9] + a[10] * b[10]) }
    fn dot20(a: [Field; 20], b: [Field; 20]) -> Field { shr8(a[0] * b[0] + a[1] * b[1] + a[2] * b[2] + a[3] * b[3] + a[4] * b[4] + a[5] * b[5] + a[6] * b[6] + a[7] * b[7] + a[8] * b[8] + a[9] * b[9] + a[10] * b[10] + a[11] * b[11] + a[12] * b[12] + a[13] * b[13] + a[14] * b[14] + a[15] * b[15] + a[16] * b[16] + a[17] * b[17] + a[18] * b[18] + a[19] * b[19]) }
    fn sum20(a: [Field; 20]) -> Field { a[0] + a[1] + a[2] + a[3] + a[4] + a[5] + a[6] + a[7] + a[8] + a[9] + a[10] + a[11] + a[12] + a[13] + a[14] + a[15] + a[16] + a[17] + a[18] + a[19] }
    fn hidden_unit(row: [Field; 8], b: Field, x: [Field; 8]) -> Field { dot8(row, x) + b }
    fn hidden(w1: [[Field; 8]; 16], b1: [Field; 16], x: [Field; 8]) -> ([Field; 16], [Field; 16]) {
        let [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15] = w1;
        let [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] = b1;
        let z0 = hidden_unit(r0, c0, x);
        let z1 = hidden_unit(r1, c1, x);
        let z2 = hidden_unit(r2, c2, x);
        let z3 = hidden_unit(r3, c3, x);
        let z4 = hidden_unit(r4, c4, x);
        let z5 = hidden_unit(r5, c5, x);
        let z6 = hidden_unit(r6, c6, x);
        let z7 = hidden_unit(r7, c7, x);
        let z8 = hidden_unit(r8, c8, x);
        let z9 = hidden_unit(r9, c9, x);
        let z10 = hidden_unit(r10, c10, x);
        let z11 = hidden_unit(r11, c11, x);
        let z12 = hidden_unit(r12, c12, x);
        let z13 = hidden_unit(r13, c13, x);
        let z14 = hidden_unit(r14, c14, x);
        let z15 = hidden_unit(r15, c15, x);
        ([z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15], [relu(z0), relu(z1), relu(z2), relu(z3), relu(z4), relu(z5), relu(z6), relu(z7), relu(z8), relu(z9), relu(z10), relu(z11), relu(z12), relu(z13), relu(z14), relu(z15)])
    }
    fn output_unit(row: [Field; 16], b: Field, h: [Field; 16]) -> Field { dot16(row, h) + b }
    fn outputs(w2: [[Field; 16]; 11], b2: [Field; 11], h: [Field; 16]) -> [Field; 11] {
        let [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10] = w2;
        let [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10] = b2;
        [output_unit(r0, c0, h), output_unit(r1, c1, h), output_unit(r2, c2, h), output_unit(r3, c3, h), output_unit(r4, c4, h), output_unit(r5, c5, h), output_unit(r6, c6, h), output_unit(r7, c7, h), output_unit(r8, c8, h), output_unit(r9, c9, h), output_unit(r10, c10, h)]
    }
    fn sub11(a: [Field; 11], b: [Field; 11]) -> [Field; 11] {
        let [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] = a;
        let [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] = b;
        [a0 - b0, a1 - b1, a2 - b2, a3 - b3, a4 - b4, a5 - b5, a6 - b6, a7 - b7, a8 - b8, a9 - b9, a10 - b10]
    }
    fn back_unit(z: Field, col: [Field; 11], dout: [Field; 11]) -> Field { pos(z) * dot11(col, dout) }
    fn delta(w1: [[Field; 8]; 16], b1: [Field; 16], w2: [[Field; 16]; 11], b2: [Field; 11],
             w2t: [[Field; 11]; 16], x: [Field; 8], t: [Field; 11]) -> ([Field; 16], [Field; 16], [Field; 11]) {
        let (z, h) = hidden(w1, b1, x);
        let dout = sub11(outputs(w2, b2, h), t);
        let [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15] = z;
        let [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] = w2t;
        (h, [back_unit(z0, c0, dout), back_unit(z1, c1, dout), back_unit(z2, c2, dout), back_unit(z3, c3, dout), back_unit(z4, c4, dout), back_unit(z5, c5, dout), back_unit(z6, c6, dout), back_unit(z7, c7, dout), back_unit(z8, c8, dout), back_unit(z9, c9, dout), back_unit(z10, c10, dout), back_unit(z11, c11, dout), back_unit(z12, c12, dout), back_unit(z13, c13, dout), back_unit(z14, c14, dout), back_unit(z15, c15, dout)], dout)
    }
    fn deltas(w1: [[Field; 8]; 16], b1: [Field; 16], w2: [[Field; 16]; 11], b2: [Field; 11],
              w2t: [[Field; 11]; 16], xs: [[Field; 8]; 20], ts: [[Field; 11]; 20])
              -> ([[Field; 16]; 20], [[Field; 16]; 20], [[Field; 11]; 20]) {
        let [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19] = xs;
        let [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19] = ts;
        let (h0, dz0, dout0) = delta(w1, b1, w2, b2, w2t, x0, t0);
        let (h1, dz1, dout1) = delta(w1, b1, w2, b2, w2t, x1, t1);
        let (h2, dz2, dout2) = delta(w1, b1, w2, b2, w2t, x2, t2);
        let (h3, dz3, dout3) = delta(w1, b1, w2, b2, w2t, x3, t3);
        let (h4, dz4, dout4) = delta(w1, b1, w2, b2, w2t, x4, t4);
        let (h5, dz5, dout5) = delta(w1, b1, w2, b2, w2t, x5, t5);
        let (h6, dz6, dout6) = delta(w1, b1, w2, b2, w2t, x6, t6);
        let (h7, dz7, dout7) = delta(w1, b1, w2, b2, w2t, x7, t7);
        let (h8, dz8, dout8) = delta(w1, b1, w2, b2, w2t, x8, t8);
        let (h9, dz9, dout9) = delta(w1, b1, w2, b2, w2t, x9, t9);
        let (h10, dz10, dout10) = delta(w1, b1, w2, b2, w2t, x10, t10);
        let (h11, dz11, dout11) = delta(w1, b1, w2, b2, w2t, x11, t11);
        let (h12, dz12, dout12) = delta(w1, b1, w2, b2, w2t, x12, t12);
        let (h13, dz13, dout13) = delta(w1, b1, w2, b2, w2t, x13, t13);
        let (h14, dz14, dout14) = delta(w1, b1, w2, b2, w2t, x14, t14);
        let (h15, dz15, dout15) = delta(w1, b1, w2, b2, w2t, x15, t15);
        let (h16, dz16, dout16) = delta(w1, b1, w2, b2, w2t, x16, t16);
        let (h17, dz17, dout17) = delta(w1, b1, w2, b2, w2t, x17, t17);
        let (h18, dz18, dout18) = delta(w1, b1, w2, b2, w2t, x18, t18);
        let (h19, dz19, dout19) = delta(w1, b1, w2, b2, w2t, x19, t19);
        ([h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19], [dz0, dz1, dz2, dz3, dz4, dz5, dz6, dz7, dz8, dz9, dz10, dz11, dz12, dz13, dz14, dz15, dz16, dz17, dz18, dz19], [dout0, dout1, dout2, dout3, dout4, dout5, dout6, dout7, dout8, dout9, dout10, dout11, dout12, dout13, dout14, dout15, dout16, dout17, dout18, dout19])
    }
    fn transpose11x16(m: [[Field; 16]; 11]) -> [[Field; 11]; 16] {
        let [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10] = m;
        let [a0_0, a0_1, a0_2, a0_3, a0_4, a0_5, a0_6, a0_7, a0_8, a0_9, a0_10, a0_11, a0_12, a0_13, a0_14, a0_15] = r0;
        let [a1_0, a1_1, a1_2, a1_3, a1_4, a1_5, a1_6, a1_7, a1_8, a1_9, a1_10, a1_11, a1_12, a1_13, a1_14, a1_15] = r1;
        let [a2_0, a2_1, a2_2, a2_3, a2_4, a2_5, a2_6, a2_7, a2_8, a2_9, a2_10, a2_11, a2_12, a2_13, a2_14, a2_15] = r2;
        let [a3_0, a3_1, a3_2, a3_3, a3_4, a3_5, a3_6, a3_7, a3_8, a3_9, a3_10, a3_11, a3_12, a3_13, a3_14, a3_15] = r3;
        let [a4_0, a4_1, a4_2, a4_3, a4_4, a4_5, a4_6, a4_7, a4_8, a4_9, a4_10, a4_11, a4_12, a4_13, a4_14, a4_15] = r4;
        let [a5_0, a5_1, a5_2, a5_3, a5_4, a5_5, a5_6, a5_7, a5_8, a5_9, a5_10, a5_11, a5_12, a5_13, a5_14, a5_15] = r5;
        let [a6_0, a6_1, a6_2, a6_3, a6_4, a6_5, a6_6, a6_7, a6_8, a6_9, a6_10, a6_11, a6_12, a6_13, a6_14, a6_15] = r6;
        let [a7_0, a7_1, a7_2, a7_3, a7_4, a7_5, a7_6, a7_7, a7_8, a7_9, a7_10, a7_11, a7_12, a7_13, a7_14, a7_15] = r7;
        let [a8_0, a8_1, a8_2, a8_3, a8_4, a8_5, a8_6, a8_7, a8_8, a8_9, a8_10, a8_11, a8_12, a8_13, a8_14, a8_15] = r8;
        let [a9_0, a9_1, a9_2, a9_3, a9_4, a9_5, a9_6, a9_7, a9_8, a9_9, a9_10, a9_11, a9_12, a9_13, a9_14, a9_15] = r9;
        let [a10_0, a10_1, a10_2, a10_3, a10_4, a10_5, a10_6, a10_7, a10_8, a10_9, a10_10, a10_11, a10_12, a10_13, a10_14, a10_15] = r10;
        [[a0_0, a1_0, a2_0, a3_0, a4_0, a5_0, a6_0, a7_0, a8_0, a9_0, a10_0], [a0_1, a1_1, a2_1, a3_1, a4_1, a5_1, a6_1, a7_1, a8_1, a9_1, a10_1], [a0_2, a1_2, a2_2, a3_2, a4_2, a5_2, a6_2, a7_2, a8_2, a9_2, a10_2], [a0_3, a1_3, a2_3, a3_3, a4_3, a5_3, a6_3, a7_3, a8_3, a9_3, a10_3], [a0_4, a1_4, a2_4, a3_4, a4_4, a5_4, a6_4, a7_4, a8_4, a9_4, a10_4], [a0_5, a1_5, a2_5, a3_5, a4_5, a5_5, a6_5, a7_5, a8_5, a9_5, a10_5], [a0_6, a1_6, a2_6, a3_6, a4_6, a5_6, a6_6, a7_6, a8_6, a9_6, a10_6], [a0_7, a1_7, a2_7, a3_7, a4_7, a5_7, a6_7, a7_7, a8_7, a9_7, a10_7], [a0_8, a1_8, a2_8, a3_8, a4_8, a5_8, a6_8, a7_8, a8_8, a9_8, a10_8], [a0_9, a1_9, a2_9, a3_9, a4_9, a5_9, a6_9, a7_9, a8_9, a9_9, a10_9], [a0_10, a1_10, a2_10, a3_10, a4_10, a5_10, a6_10, a7_10, a8_10, a9_10, a10_10], [a0_11, a1_11, a2_11, a3_11, a4_11, a5_11, a6_11, a7_11, a8_11, a9_11, a10_11], [a0_12, a1_12, a2_12, a3_12, a4_12, a5_12, a6_12, a7_12, a8_12, a9_12, a10_12], [a0_13, a1_13, a2_13, a3_13, a4_13, a5_13, a6_13, a7_13, a8_13, a9_13, a10_13], [a0_14, a1_14, a2_14, a3_14, a4_14, a5_14, a6_14, a7_14, a8_14, a9_14, a10_14], [a0_15, a1_15, a2_15, a3_15, a4_15, a5_15, a6_15, a7_15, a8_15, a9_15, a10_15]]
    }
    fn transpose20x16(m: [[Field; 16]; 20]) -> [[Field; 20]; 16] {
        let [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19] = m;
        let [a0_0, a0_1, a0_2, a0_3, a0_4, a0_5, a0_6, a0_7, a0_8, a0_9, a0_10, a0_11, a0_12, a0_13, a0_14, a0_15] = r0;
        let [a1_0, a1_1, a1_2, a1_3, a1_4, a1_5, a1_6, a1_7, a1_8, a1_9, a1_10, a1_11, a1_12, a1_13, a1_14, a1_15] = r1;
        let [a2_0, a2_1, a2_2, a2_3, a2_4, a2_5, a2_6, a2_7, a2_8, a2_9, a2_10, a2_11, a2_12, a2_13, a2_14, a2_15] = r2;
        let [a3_0, a3_1, a3_2, a3_3, a3_4, a3_5, a3_6, a3_7, a3_8, a3_9, a3_10, a3_11, a3_12, a3_13, a3_14, a3_15] = r3;
        let [a4_0, a4_1, a4_2, a4_3, a4_4, a4_5, a4_6, a4_7, a4_8, a4_9, a4_10, a4_11, a4_12, a4_13, a4_14, a4_15] = r4;
        let [a5_0, a5_1, a5_2, a5_3, a5_4, a5_5, a5_6, a5_7, a5_8, a5_9, a5_10, a5_11, a5_12, a5_13, a5_14, a5_15] = r5;
        let [a6_0, a6_1, a6_2, a6_3, a6_4, a6_5, a6_6, a6_7, a6_8, a6_9, a6_10, a6_11, a6_12, a6_13, a6_14, a6_15] = r6;
        let [a7_0, a7_1, a7_2, a7_3, a7_4, a7_5, a7_6, a7_7, a7_8, a7_9, a7_10, a7_11, a7_12, a7_13, a7_14, a7_15] = r7;
        let [a8_0, a8_1, a8_2, a8_3, a8_4, a8_5, a8_6, a8_7, a8_8, a8_9, a8_10, a8_11, a8_12, a8_13, a8_14, a8_15] = r8;
        let [a9_0, a9_1, a9_2, a9_3, a9_4, a9_5, a9_6, a9_7, a9_8, a9_9, a9_10, a9_11, a9_12, a9_13, a9_14, a9_15] = r9;
        let [a10_0, a10_1, a10_2, a10_3, a10_4, a10_5, a10_6, a10_7, a10_8, a10_9, a10_10, a10_11, a10_12, a10_13, a10_14, a10_15] = r10;
        let [a11_0, a11_1, a11_2, a11_3, a11_4, a11_5, a11_6, a11_7, a11_8, a11_9, a11_10, a11_11, a11_12, a11_13, a11_14, a11_15] = r11;
        let [a12_0, a12_1, a12_2, a12_3, a12_4, a12_5, a12_6, a12_7, a12_8, a12_9, a12_10, a12_11, a12_12, a12_13, a12_14, a12_15] = r12;
        let [a13_0, a13_1, a13_2, a13_3, a13_4, a13_5, a13_6, a13_7, a13_8, a13_9, a13_10, a13_11, a13_12, a13_13, a13_14, a13_15] = r13;
        let [a14_0, a14_1, a14_2, a14_3, a14_4, a14_5, a14_6, a14_7, a14_8, a14_9, a14_10, a14_11, a14_12, a14_13, a14_14, a14_15] = r14;
        let [a15_0, a15_1, a15_2, a15_3, a15_4, a15_5, a15_6, a15_7, a15_8, a15_9, a15_10, a15_11, a15_12, a15_13, a15_14, a15_15] = r15;
        let [a16_0, a16_1, a16_2, a16_3, a16_4, a16_5, a16_6, a16_7, a16_8, a16_9, a16_10, a16_11, a16_12, a16_13, a16_14, a16_15] = r16;
        let [a17_0, a17_1, a17_2, a17_3, a17_4, a17_5, a17_6, a17_7, a17_8, a17_9, a17_10, a17_11, a17_12, a17_13, a17_14, a17_15] = r17;
        let [a18_0, a18_1, a18_2, a18_3, a18_4, a18_5, a18_6, a18_7, a18_8, a18_9, a18_10, a18_11, a18_12, a18_13, a18_14, a18_15] = r18;
        let [a19_0, a19_1, a19_2, a19_3, a19_4, a19_5, a19_6, a19_7, a19_8, a19_9, a19_10, a19_11, a19_12, a19_13, a19_14, a19_15] = r19;
        [[a0_0, a1_0, a2_0, a3_0, a4_0, a5_0, a6_0, a7_0, a8_0, a9_0, a10_0, a11_0, a12_0, a13_0, a14_0, a15_0, a16_0, a17_0, a18_0, a19_0], [a0_1, a1_1, a2_1, a3_1, a4_1, a5_1, a6_1, a7_1, a8_1, a9_1, a10_1, a11_1, a12_1, a13_1, a14_1, a15_1, a16_1, a17_1, a18_1, a19_1], [a0_2, a1_2, a2_2, a3_2, a4_2, a5_2, a6_2, a7_2, a8_2, a9_2, a10_2, a11_2, a12_2, a13_2, a14_2, a15_2, a16_2, a17_2, a18_2, a19_2], [a0_3, a1_3, a2_3, a3_3, a4_3, a5_3, a6_3, a7_3, a8_3, a9_3, a10_3, a11_3, a12_3, a13_3, a14_3, a15_3, a16_3, a17_3, a18_3, a19_3], [a0_4, a1_4, a2_4, a3_4, a4_4, a5_4, a6_4, a7_4, a8_4, a9_4, a10_4, a11_4, a12_4, a13_4, a14_4, a15_4, a16_4, a17_4, a18_4, a19_4], [a0_5, a1_5, a2_5, a3_5, a4_5, a5_5, a6_5, a7_5, a8_5, a9_5, a10_5, a11_5, a12_5, a13_5, a14_5, a15_5, a16_5, a17_5, a18_5, a19_5], [a0_6, a1_6, a2_6, a3_6, a4_6, a5_6, a6_6, a7_6, a8_6, a9_6, a10_6, a11_6, a12_6, a13_6, a14_6, a15_6, a16_6, a17_6, a18_6, a19_6], [a0_7, a1_7, a2_7, a3_7, a4_7, a5_7, a6_7, a7_7, a8_7, a9_7, a10_7, a11_7, a12_7, a13_7, a14_7, a15_7, a16_7, a17_7, a18_7, a19_7], [a0_8, a1_8, a2_8, a3_8, a4_8, a5_8, a6_8, a7_8, a8_8, a9_8, a10_8, a11_8, a12_8, a13_8, a14_8, a15_8, a16_8, a17_8, a18_8, a19_8], [a0_9, a1_9, a2_9, a3_9, a4_9, a5_9, a6_9, a7_9, a8_9, a9_9, a10_9, a11_9, a12_9, a13_9, a14_9, a15_9, a16_9, a17_9, a18_9, a19_9], [a0_10, a1_10, a2_10, a3_10, a4_10, a5_10, a6_10, a7_10, a8_10, a9_10, a10_10, a11_10, a12_10, a13_10, a14_10, a15_10, a16_10, a17_10, a18_10, a19_10], [a0_11, a1_11, a2_11, a3_11, a4_11, a5_11, a6_11, a7_11, a8_11, a9_11, a10_11, a11_11, a12_11, a13_11, a14_11, a15_11, a16_11, a17_11, a18_11, a19_11], [a0_12, a1_12, a2_12, a3_12, a4_12, a5_12, a6_12, a7_12, a8_12, a9_12, a10_12, a11_12, a12_12, a13_12, a14_12, a15_12, a16_12, a17_12, a18_12, a19_12], [a0_13, a1_13, a2_13, a3_13, a4_13, a5_13, a6_13, a7_13, a8_13, a9_13, a10_13, a11_13, a12_13, a13_13, a14_13, a15_13, a16_13, a17_13, a18_13, a19_13], [a0_14, a1_14, a2_14, a3_14, a4_14, a5_14, a6_14, a7_14, a8_14, a9_14, a10_14, a11_14, a12_14, a13_14, a14_14, a15_14, a16_14, a17_14, a18_14, a19_14], [a0_15, a1_15, a2_15, a3_15, a4_15, a5_15, a6_15, a7_15, a8_15, a9_15, a10_15, a11_15, a12_15, a13_15, a14_15, a15_15, a16_15, a17_15, a18_15, a19_15]]
    }
    fn transpose20x8(m: [[Field; 8]; 20]) -> [[Field; 20]; 8] {
        let [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19] = m;
        let [a0_0, a0_1, a0_2, a0_3, a0_4, a0_5, a0_6, a0_7] = r0;
        let [a1_0, a1_1, a1_2, a1_3, a1_4, a1_5, a1_6, a1_7] = r1;
        let [a2_0, a2_1, a2_2, a2_3, a2_4, a2_5, a2_6, a2_7] = r2;
        let [a3_0, a3_1, a3_2, a3_3, a3_4, a3_5, a3_6, a3_7] = r3;
        let [a4_0, a4_1, a4_2, a4_3, a4_4, a4_5, a4_6, a4_7] = r4;
        let [a5_0, a5_1, a5_2, a5_3, a5_4, a5_5, a5_6, a5_7] = r5;
        let [a6_0, a6_1, a6_2, a6_3, a6_4, a6_5, a6_6, a6_7] = r6;
        let [a7_0, a7_1, a7_2, a7_3, a7_4, a7_5, a7_6, a7_7] = r7;
        let [a8_0, a8_1, a8_2, a8_3, a8_4, a8_5, a8_6, a8_7] = r8;
        let [a9_0, a9_1, a9_2, a9_3, a9_4, a9_5, a9_6, a9_7] = r9;
        let [a10_0, a10_1, a10_2, a10_3, a10_4, a10_5, a10_6, a10_7] = r10;
        let [a11_0, a11_1, a11_2, a11_3, a11_4, a11_5, a11_6, a11_7] = r11;
        let [a12_0, a12_1, a12_2, a12_3, a12_4, a12_5, a12_6, a12_7] = r12;
        let [a13_0, a13_1, a13_2, a13_3, a13_4, a13_5, a13_6, a13_7] = r13;
        let [a14_0, a14_1, a14_2, a14_3, a14_4, a14_5, a14_6, a14_7] = r14;
        let [a15_0, a15_1, a15_2, a15_3, a15_4, a15_5, a15_6, a15_7] = r15;
        let [a16_0, a16_1, a16_2, a16_3, a16_4, a16_5, a16_6, a16_7] = r16;
        let [a17_0, a17_1, a17_2, a17_3, a17_4, a17_5, a17_6, a17_7] = r17;
        let [a18_0, a18_1, a18_2, a18_3, a18_4, a18_5, a18_6, a18_7] = r18;
        let [a19_0, a19_1, a19_2, a19_3, a19_4, a19_5, a19_6, a19_7] = r19;
        [[a0_0, a1_0, a2_0, a3_0, a4_0, a5_0, a6_0, a7_0, a8_0, a9_0, a10_0, a11_0, a12_0, a13_0, a14_0, a15_0, a16_0, a17_0, a18_0, a19_0], [a0_1, a1_1, a2_1, a3_1, a4_1, a5_1, a6_1, a7_1, a8_1, a9_1, a10_1, a11_1, a12_1, a13_1, a14_1, a15_1, a16_1, a17_1, a18_1, a19_1], [a0_2, a1_2, a2_2, a3_2, a4_2, a5_2, a6_2, a7_2, a8_2, a9_2, a10_2, a11_2, a12_2, a13_2, a14_2, a15_2, a16_2, a17_2, a18_2, a19_2], [a0_3, a1_3, a2_3, a3_3, a4_3, a5_3, a6_3, a7_3, a8_3, a9_3, a10_3, a11_3, a12_3, a13_3, a14_3, a15_3, a16_3, a17_3, a18_3, a19_3], [a0_4, a1_4, a2_4, a3_4, a4_4, a5_4, a6_4, a7_4, a8_4, a9_4, a10_4, a11_4, a12_4, a13_4, a14_4, a15_4, a16_4, a17_4, a18_4, a19_4], [a0_5, a1_5, a2_5, a3_5, a4_5, a5_5, a6_5, a7_5, a8_5, a9_5, a10_5, a11_5, a12_5, a13_5, a14_5, a15_5, a16_5, a17_5, a18_5, a19_5], [a0_6, a1_6, a2_6, a3_6, a4_6, a5_6, a6_6, a7_6, a8_6, a9_6, a10_6, a11_6, a12_6, a13_6, a14_6, a15_6, a16_6, a17_6, a18_6, a19_6], [a0_7, a1_7, a2_7, a3_7, a4_7, a5_7, a6_7, a7_7, a8_7, a9_7, a10_7, a11_7, a12_7, a13_7, a14_7, a15_7, a16_7, a17_7, a18_7, a19_7]]
    }
    fn transpose20x11(m: [[Field; 11]; 20]) -> [[Field; 20]; 11] {
        let [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19] = m;
        let [a0_0, a0_1, a0_2, a0_3, a0_4, a0_5, a0_6, a0_7, a0_8, a0_9, a0_10] = r0;
        let [a1_0, a1_1, a1_2, a1_3, a1_4, a1_5, a1_6, a1_7, a1_8, a1_9, a1_10] = r1;
        let [a2_0, a2_1, a2_2, a2_3, a2_4, a2_5, a2_6, a2_7, a2_8, a2_9, a2_10] = r2;
        let [a3_0, a3_1, a3_2, a3_3, a3_4, a3_5, a3_6, a3_7, a3_8, a3_9, a3_10] = r3;
        let [a4_0, a4_1, a4_2, a4_3, a4_4, a4_5, a4_6, a4_7, a4_8, a4_9, a4_10] = r4;
        let [a5_0, a5_1, a5_2, a5_3, a5_4, a5_5, a5_6, a5_7, a5_8, a5_9, a5_10] = r5;
        let [a6_0, a6_1, a6_2, a6_3, a6_4, a6_5, a6_6, a6_7, a6_8, a6_9, a6_10] = r6;
        let [a7_0, a7_1, a7_2, a7_3, a7_4, a7_5, a7_6, a7_7, a7_8, a7_9, a7_10] = r7;
        let [a8_0, a8_1, a8_2, a8_3, a8_4, a8_5, a8_6, a8_7, a8_8, a8_9, a8_10] = r8;
        let [a9_0, a9_1, a9_2, a9_3, a9_4, a9_5, a9_6, a9_7, a9_8, a9_9, a9_10] = r9;
        let [a10_0, a10_1, a10_2, a10_3, a10_4, a10_5, a10_6, a10_7, a10_8, a10_9, a10_10] = r10;
        let [a11_0, a11_1, a11_2, a11_3, a11_4, a11_5, a11_6, a11_7, a11_8, a11_9, a11_10] = r11;
        let [a12_0, a12_1, a12_2, a12_3, a12_4, a12_5, a12_6, a12_7, a12_8, a12_9, a12_10] = r12;
        let [a13_0, a13_1, a13_2, a13_3, a13_4, a13_5, a13_6, a13_7, a13_8, a13_9, a13_10] = r13;
        let [a14_0, a14_1, a14_2, a14_3, a14_4, a14_5, a14_6, a14_7, a14_8, a14_9, a14_10] = r14;
        let [a15_0, a15_1, a15_2, a15_3, a15_4, a15_5, a15_6, a15_7, a15_8, a15_9, a15_10] = r15;
        let [a16_0, a16_1, a16_2, a16_3, a16_4, a16_5, a16_6, a16_7, a16_8, a16_9, a16_10] = r16;
        let [a17_0, a17_1, a17_2, a17_3, a17_4, a17_5, a17_6, a17_7, a17_8, a17_9, a17_10] = r17;
        let [a18_0, a18_1, a18_2, a18_3, a18_4, a18_5, a18_6, a18_7, a18_8, a18_9, a18_10] = r18;
        let [a19_0, a19_1, a19_2, a19_3, a19_4, a19_5, a19_6, a19_7, a19_8, a19_9, a19_10] = r19;
        [[a0_0, a1_0, a2_0, a3_0, a4_0, a5_0, a6_0, a7_0, a8_0, a9_0, a10_0, a11_0, a12_0, a13_0, a14_0, a15_0, a16_0, a17_0, a18_0, a19_0], [a0_1, a1_1, a2_1, a3_1, a4_1, a5_1, a6_1, a7_1, a8_1, a9_1, a10_1, a11_1, a12_1, a13_1, a14_1, a15_1, a16_1, a17_1, a18_1, a19_1], [a0_2, a1_2, a2_2, a3_2, a4_2, a5_2, a6_2, a7_2, a8_2, a9_2, a10_2, a11_2, a12_2, a13_2, a14_2, a15_2, a16_2, a17_2, a18_2, a19_2], [a0_3, a1_3, a2_3, a3_3, a4_3, a5_3, a6_3, a7_3, a8_3, a9_3, a10_3, a11_3, a12_3, a13_3, a14_3, a15_3, a16_3, a17_3, a18_3, a19_3], [a0_4, a1_4, a2_4, a3_4, a4_4, a5_4, a6_4, a7_4, a8_4, a9_4, a10_4, a11_4, a12_4, a13_4, a14_4, a15_4, a16_4, a17_4, a18_4, a19_4], [a0_5, a1_5, a2_5, a3_5, a4_5, a5_5, a6_5, a7_5, a8_5, a9_5, a10_5, a11_5, a12_5, a13_5, a14_5, a15_5, a16_5, a17_5, a18_5, a19_5], [a0_6, a1_6, a2_6, a3_6, a4_6, a5_6, a6_6, a7_6, a8_6, a9_6, a10_6, a11_6, a12_6, a13_6, a14_6, a15_6, a16_6, a17_6, a18_6, a19_6], [a0_7, a1_7, a2_7, a3_7, a4_7, a5_7, a6_7, a7_7, a8_7, a9_7, a10_7, a11_7, a12_7, a13_7, a14_7, a15_7, a16_7, a17_7, a18_7, a19_7], [a0_8, a1_8, a2_8, a3_8, a4_8, a5_8, a6_8, a7_8, a8_8, a9_8, a10_8, a11_8, a12_8, a13_8, a14_8, a15_8, a16_8, a17_8, a18_8, a19_8], [a0_9, a1_9, a2_9, a3_9, a4_9, a5_9, a6_9, a7_9, a8_9, a9_9, a10_9, a11_9, a12_9, a13_9, a14_9, a15_9, a16_9, a17_9, a18_9, a19_9], [a0_10, a1_10, a2_10, a3_10, a4_10, a5_10, a6_10, a7_10, a8_10, a9_10, a10_10, a11_10, a12_10, a13_10, a14_10, a15_10, a16_10, a17_10, a18_10, a19_10]]
    }
    fn upd(w: Field, lr: Field, g: Field) -> Field { w - mul(lr, g) }
    fn update_row8(row: [Field; 8], d: [Field; 20], cols: [[Field; 20]; 8], lr: Field) -> [Field; 8] {
        let [w0, w1, w2, w3, w4, w5, w6, w7] = row;
        let [c0, c1, c2, c3, c4, c5, c6, c7] = cols;
        [upd(w0, lr, dot20(d, c0)), upd(w1, lr, dot20(d, c1)), upd(w2, lr, dot20(d, c2)), upd(w3, lr, dot20(d, c3)), upd(w4, lr, dot20(d, c4)), upd(w5, lr, dot20(d, c5)), upd(w6, lr, dot20(d, c6)), upd(w7, lr, dot20(d, c7))]
    }
    fn update_row16(row: [Field; 16], d: [Field; 20], cols: [[Field; 20]; 16], lr: Field) -> [Field; 16] {
        let [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] = row;
        let [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] = cols;
        [upd(w0, lr, dot20(d, c0)), upd(w1, lr, dot20(d, c1)), upd(w2, lr, dot20(d, c2)), upd(w3, lr, dot20(d, c3)), upd(w4, lr, dot20(d, c4)), upd(w5, lr, dot20(d, c5)), upd(w6, lr, dot20(d, c6)), upd(w7, lr, dot20(d, c7)), upd(w8, lr, dot20(d, c8)), upd(w9, lr, dot20(d, c9)), upd(w10, lr, dot20(d, c10)), upd(w11, lr, dot20(d, c11)), upd(w12, lr, dot20(d, c12)), upd(w13, lr, dot20(d, c13)), upd(w14, lr, dot20(d, c14)), upd(w15, lr, dot20(d, c15))]
    }
    fn update_w1(w1: [[Field; 8]; 16], dzt: [[Field; 20]; 16], xt: [[Field; 20]; 8], lr: Field) -> [[Field; 8]; 16] {
        let [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15] = w1;
        let [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15] = dzt;
        [update_row8(r0, d0, xt, lr), update_row8(r1, d1, xt, lr), update_row8(r2, d2, xt, lr), update_row8(r3, d3, xt, lr), update_row8(r4, d4, xt, lr), update_row8(r5, d5, xt, lr), update_row8(r6, d6, xt, lr), update_row8(r7, d7, xt, lr), update_row8(r8, d8, xt, lr), update_row8(r9, d9, xt, lr), update_row8(r10, d10, xt, lr), update_row8(r11, d11, xt, lr), update_row8(r12, d12, xt, lr), update_row8(r13, d13, xt, lr), update_row8(r14, d14, xt, lr), update_row8(r15, d15, xt, lr)]
    }
    fn update_w2(w2: [[Field; 16]; 11], doutt: [[Field; 20]; 11], ht: [[Field; 20]; 16], lr: Field) -> [[Field; 16]; 11] {
        let [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10] = w2;
        let [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10] = doutt;
        [update_row16(r0, d0, ht, lr), update_row16(r1, d1, ht, lr), update_row16(r2, d2, ht, lr), update_row16(r3, d3, ht, lr), update_row16(r4, d4, ht, lr), update_row16(r5, d5, ht, lr), update_row16(r6, d6, ht, lr), update_row16(r7, d7, ht, lr), update_row16(r8, d8, ht, lr), update_row16(r9, d9, ht, lr), update_row16(r10, d10, ht, lr)]
    }
    fn update_bias16(b: [Field; 16], dt: [[Field; 20]; 16], lr: Field) -> [Field; 16] {
        let [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] = b;
        let [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15] = dt;
        [upd(b0, lr, sum20(d0)), upd(b1, lr, sum20(d1)), upd(b2, lr, sum20(d2)), upd(b3, lr, sum20(d3)), upd(b4, lr, sum20(d4)), upd(b5, lr, sum20(d5)), upd(b6, lr, sum20(d6)), upd(b7, lr, sum20(d7)), upd(b8, lr, sum20(d8)), upd(b9, lr, sum20(d9)), upd(b10, lr, sum20(d10)), upd(b11, lr, sum20(d11)), upd(b12, lr, sum20(d12)), upd(b13, lr, sum20(d13)), upd(b14, lr, sum20(d14)), upd(b15, lr, sum20(d15))]
    }
    fn update_bias11(b: [Field; 11], dt: [[Field; 20]; 11], lr: Field) -> [Field; 11] {
        let [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] = b;
        let [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10] = dt;
        [upd(b0, lr, sum20(d0)), upd(b1, lr, sum20(d1)), upd(b2, lr, sum20(d2)), upd(b3, lr, sum20(d3)), upd(b4, lr, sum20(d4)), upd(b5, lr, sum20(d5)), upd(b6, lr, sum20(d6)), upd(b7, lr, sum20(d7)), upd(b8, lr, sum20(d8)), upd(b9, lr, sum20(d9)), upd(b10, lr, sum20(d10))]
    }
    fn step(w1: [[Field; 8]; 16], b1: [Field; 16], w2: [[Field; 16]; 11], b2: [Field; 11],
            xs: [[Field; 8]; 20], ts: [[Field; 11]; 20], lr: Field) -> ([[Field; 8]; 16], [Field; 16], [[Field; 16]; 11], [Field; 11]) {
        let w2t = transpose11x16(w2);
        let (hs, dzs, douts) = deltas(w1, b1, w2, b2, w2t, xs, ts);
        let dzt = transpose20x16(dzs);
        let xt = transpose20x8(xs);
        let ht = transpose20x16(hs);
        let doutt = transpose20x11(douts);
        (update_w1(w1, dzt, xt, lr), update_bias16(b1, dzt, lr), update_w2(w2, doutt, ht, lr),
            update_bias11(b2, doutt, lr))
    }
    fn push_block(xs: [[Field; 8]; 20], ts: [[Field; 11]; 20], rest: &Examples) -> &Examples {
        let [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19] = xs;
        let [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19] = ts;
        &(Examples::Cons(x0, t0, &(Examples::Cons(x1, t1, &(Examples::Cons(x2, t2, &(Examples::Cons(x3, t3,
        &(Examples::Cons(x4, t4, &(Examples::Cons(x5, t5, &(Examples::Cons(x6, t6, &(Examples::Cons(x7, t7,
        &(Examples::Cons(x8, t8, &(Examples::Cons(x9, t9, &(Examples::Cons(x10, t10, &(Examples::Cons(x11, t11,
        &(Examples::Cons(x12, t12, &(Examples::Cons(x13, t13, &(Examples::Cons(x14, t14, &(Examples::Cons(x15, t15,
        &(Examples::Cons(x16, t16, &(Examples::Cons(x17, t17, &(Examples::Cons(x18, t18, &(Examples::Cons(x19, t19,
        rest))))))))))))))))))))))))))))))))))))))))
    }
    fn example_table(xs: [[[Field; 8]; 20]; 20], ts: [[[Field; 11]; 20]; 20]) -> &Examples {
        let [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19] = xs;
        let [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19] = ts;
        let l19 = push_block(x19, t19, &(Examples::Nil));
        let l18 = push_block(x18, t18, l19);
        let l17 = push_block(x17, t17, l18);
        let l16 = push_block(x16, t16, l17);
        let l15 = push_block(x15, t15, l16);
        let l14 = push_block(x14, t14, l15);
        let l13 = push_block(x13, t13, l14);
        let l12 = push_block(x12, t12, l13);
        let l11 = push_block(x11, t11, l12);
        let l10 = push_block(x10, t10, l11);
        let l9 = push_block(x9, t9, l10);
        let l8 = push_block(x8, t8, l9);
        let l7 = push_block(x7, t7, l8);
        let l6 = push_block(x6, t6, l7);
        let l5 = push_block(x5, t5, l6);
        let l4 = push_block(x4, t4, l5);
        let l3 = push_block(x3, t3, l4);
        let l2 = push_block(x2, t2, l3);
        let l1 = push_block(x1, t1, l2);
        push_block(x0, t0, l1)
    }
    fn lookup_example(data: &Examples, i: Field) -> ([Field; 8], [Field; 11]) {
        let Examples::Cons(x, t, rest) = *data;
        match i {
            0 => { (x, t) },
            _ => { lookup_example(rest, i - 1) },
        }
    }
    fn batch(data: &Examples, idx: [Field; 20]) -> ([[Field; 8]; 20], [[Field; 11]; 20]) {
        let [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19] = idx;
        let (x0, t0) = lookup_example(data, i0);
        let (x1, t1) = lookup_example(data, i1);
        let (x2, t2) = lookup_example(data, i2);
        let (x3, t3) = lookup_example(data, i3);
        let (x4, t4) = lookup_example(data, i4);
        let (x5, t5) = lookup_example(data, i5);
        let (x6, t6) = lookup_example(data, i6);
        let (x7, t7) = lookup_example(data, i7);
        let (x8, t8) = lookup_example(data, i8);
        let (x9, t9) = lookup_example(data, i9);
        let (x10, t10) = lookup_example(data, i10);
        let (x11, t11) = lookup_example(data, i11);
        let (x12, t12) = lookup_example(data, i12);
        let (x13, t13) = lookup_example(data, i13);
        let (x14, t14) = lookup_example(data, i14);
        let (x15, t15) = lookup_example(data, i15);
        let (x16, t16) = lookup_example(data, i16);
        let (x17, t17) = lookup_example(data, i17);
        let (x18, t18) = lookup_example(data, i18);
        let (x19, t19) = lookup_example(data, i19);
        ([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19], [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19])
    }
    fn step_at(w1: [[Field; 8]; 16], b1: [Field; 16], w2: [[Field; 16]; 11], b2: [Field; 11], lr: Field,
               data: &Examples, idx: [Field; 20]) -> ([[Field; 8]; 16], [Field; 16], [[Field; 16]; 11], [Field; 11]) {
        let (xs, ts) = batch(data, idx);
        step(w1, b1, w2, b2, xs, ts, lr)
    }
    fn train_block(w1: [[Field; 8]; 16], b1: [Field; 16], w2: [[Field; 16]; 11], b2: [Field; 11], lr: Field,
                   data: &Examples, batches: [[Field; 20]; 20]) -> ([[Field; 8]; 16], [Field; 16], [[Field; 16]; 11], [Field; 11]) {
        let [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19] = batches;
        let (w1_0, b1_0, w2_0, b2_0) = step_at(w1, b1, w2, b2, lr, data, s0);
        let (w1_1, b1_1, w2_1, b2_1) = step_at(w1_0, b1_0, w2_0, b2_0, lr, data, s1);
        let (w1_2, b1_2, w2_2, b2_2) = step_at(w1_1, b1_1, w2_1, b2_1, lr, data, s2);
        let (w1_3, b1_3, w2_3, b2_3) = step_at(w1_2, b1_2, w2_2, b2_2, lr, data, s3);
        let (w1_4, b1_4, w2_4, b2_4) = step_at(w1_3, b1_3, w2_3, b2_3, lr, data, s4);
        let (w1_5, b1_5, w2_5, b2_5) = step_at(w1_4, b1_4, w2_4, b2_4, lr, data, s5);
        let (w1_6, b1_6, w2_6, b2_6) = step_at(w1_5, b1_5, w2_5, b2_5, lr, data, s6);
        let (w1_7, b1_7, w2_7, b2_7) = step_at(w1_6, b1_6, w2_6, b2_6, lr, data, s7);
        let (w1_8, b1_8, w2_8, b2_8) = step_at(w1_7, b1_7, w2_7, b2_7, lr, data, s8);
        let (w1_9, b1_9, w2_9, b2_9) = step_at(w1_8, b1_8, w2_8, b2_8, lr, data, s9);
        let (w1_10, b1_10, w2_10, b2_10) = step_at(w1_9, b1_9, w2_9, b2_9, lr, data, s10);
        let (w1_11, b1_11, w2_11, b2_11) = step_at(w1_10, b1_10, w2_10, b2_10, lr, data, s11);
        let (w1_12, b1_12, w2_12, b2_12) = step_at(w1_11, b1_11, w2_11, b2_11, lr, data, s12);
        let (w1_13, b1_13, w2_13, b2_13) = step_at(w1_12, b1_12, w2_12, b2_12, lr, data, s13);
        let (w1_14, b1_14, w2_14, b2_14) = step_at(w1_13, b1_13, w2_13, b2_13, lr, data, s14);
        let (w1_15, b1_15, w2_15, b2_15) = step_at(w1_14, b1_14, w2_14, b2_14, lr, data, s15);
        let (w1_16, b1_16, w2_16, b2_16) = step_at(w1_15, b1_15, w2_15, b2_15, lr, data, s16);
        let (w1_17, b1_17, w2_17, b2_17) = step_at(w1_16, b1_16, w2_16, b2_16, lr, data, s17);
        let (w1_18, b1_18, w2_18, b2_18) = step_at(w1_17, b1_17, w2_17, b2_17, lr, data, s18);
        step_at(w1_18, b1_18, w2_18, b2_18, lr, data, s19)
    }
    fn train(w1: [[Field; 8]; 16], b1: [Field; 16], w2: [[Field; 16]; 11], b2: [Field; 11], lr: Field,
             xs: [[[Field; 8]; 20]; 20], ts: [[[Field; 11]; 20]; 20], schedule: [[[Field; 20]; 20]; 30]) -> ([[Field; 8]; 16], [Field; 16], [[Field; 16]; 11], [Field; 11]) {
        let data = example_table(xs, ts);
        let [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29] = schedule;
        let (w1_0, b1_0, w2_0, b2_0) = train_block(w1, b1, w2, b2, lr, data, e0);
        let (w1_1, b1_1, w2_1, b2_1) = train_block(w1_0, b1_0, w2_0, b2_0, lr, data, e1);
        let (w1_2, b1_2, w2_2, b2_2) = train_block(w1_1, b1_1, w2_1, b2_1, lr, data, e2);
        let (w1_3, b1_3, w2_3, b2_3) = train_block(w1_2, b1_2, w2_2, b2_2, lr, data, e3);
        let (w1_4, b1_4, w2_4, b2_4) = train_block(w1_3, b1_3, w2_3, b2_3, lr, data, e4);
        let (w1_5, b1_5, w2_5, b2_5) = train_block(w1_4, b1_4, w2_4, b2_4, lr, data, e5);
        let (w1_6, b1_6, w2_6, b2_6) = train_block(w1_5, b1_5, w2_5, b2_5, lr, data, e6);
        let (w1_7, b1_7, w2_7, b2_7) = train_block(w1_6, b1_6, w2_6, b2_6, lr, data, e7);
        let (w1_8, b1_8, w2_8, b2_8) = train_block(w1_7, b1_7, w2_7, b2_7, lr, data, e8);
        let (w1_9, b1_9, w2_9, b2_9) = train_block(w1_8, b1_8, w2_8, b2_8, lr, data, e9);
        let (w1_10, b1_10, w2_10, b2_10) = train_block(w1_9, b1_9, w2_9, b2_9, lr, data, e10);
        let (w1_11, b1_11, w2_11, b2_11) = train_block(w1_10, b1_10, w2_10, b2_10, lr, data, e11);
        let (w1_12, b1_12, w2_12, b2_12) = train_block(w1_11, b1_11, w2_11, b2_11, lr, data, e12);
        let (w1_13, b1_13, w2_13, b2_13) = train_block(w1_12, b1_12, w2_12, b2_12, lr, data, e13);
        let (w1_14, b1_14, w2_14, b2_14) = train_block(w1_13, b1_13, w2_13, b2_13, lr, data, e14);
        let (w1_15, b1_15, w2_15, b2_15) = train_block(w1_14, b1_14, w2_14, b2_14, lr, data, e15);
        let (w1_16, b1_16, w2_16, b2_16) = train_block(w1_15, b1_15, w2_15, b2_15, lr, data, e16);
        let (w1_17, b1_17, w2_17, b2_17) = train_block(w1_16, b1_16, w2_16, b2_16, lr, data, e17);
        let (w1_18, b1_18, w2_18, b2_18) = train_block(w1_17, b1_17, w2_17, b2_17, lr, data, e18);
        let (w1_19, b1_19, w2_19, b2_19) = train_block(w1_18, b1_18, w2_18, b2_18, lr, data, e19);
        let (w1_20, b1_20, w2_20, b2_20) = train_block(w1_19, b1_19, w2_19, b2_19, lr, data, e20);
        let (w1_21, b1_21, w2_21, b2_21) = train_block(w1_20, b1_20, w2_20, b2_20, lr, data, e21);
        let (w1_22, b1_22, w2_22, b2_22) = train_block(w1_21, b1_21, w2_21, b2_21, lr, data, e22);
        let (w1_23, b1_23, w2_23, b2_23) = train_block(w1_22, b1_22, w2_22, b2_22, lr, data, e23);
        let (w1_24, b1_24, w2_24, b2_24) = train_block(w1_23, b1_23, w2_23, b2_23, lr, data, e24);
        let (w1_25, b1_25, w2_25, b2_25) = train_block(w1_24, b1_24, w2_24, b2_24, lr, data, e25);
        let (w1_26, b1_26, w2_26, b2_26) = train_block(w1_25, b1_25, w2_25, b2_25, lr, data, e26);
        let (w1_27, b1_27, w2_27, b2_27) = train_block(w1_26, b1_26, w2_26, b2_26, lr, data, e27);
        let (w1_28, b1_28, w2_28, b2_28) = train_block(w1_27, b1_27, w2_27, b2_27, lr, data, e28);
        train_block(w1_28, b1_28, w2_28, b2_28, lr, data, e29)
    }
}
⟧

def entries : List String := ["Fixed::mul", "Fixed::relu", "Fixed::pos", "Fixed::step"]

def source : Modules.Program Nat := Library.U8.source.append client

abbrev F := Library.U32.Goldilocks.F

def p : Nat := 18446744069414584321

def toInt (x : F) : Int := let v := x.val; if v > p / 2 then (v : Int) - p else v

def ofInt (i : Int) : F := (i : F)

def bytesOf (n : Nat) (k : Nat) : List F := (List.range k).map fun i => (((n / 256 ^ i) % 256 : Nat) : F)

/-- The words `fx.shr8` answers for `s`: the remainder byte, six bytes of the quotient offset by
2^47, and a zero pad. -/
def shr8Words (v : Int) : List F :=
  let q := v >>> 8
  bytesOf (v - 256 * q).toNat 1 ++ bytesOf (q + 140737488355328).toNat 6 ++ [0]

/-- The words `fx.sign` answers for `v`: seven bytes of `v + 2^55`, then `1/v` (or 0). -/
def signWords (i : Int) : List F :=
  let v := ofInt i
  bytesOf (i + 36028797018963968).toNat 7 ++ [if i == 0 then 0 else v⁻¹]

/-- The honest host. Its answers are checked by the program, so it is not trusted. -/
def hints : HintDispatcher F := fun channel key =>
  match channel, key with
  | "fx.shr8", .field s => .ok (.tuple ((shr8Words (toInt s)).map .field))
  | "fx.sign", .field v => .ok (.tuple ((signWords (toInt v)).map .field))
  | _, _ => .error .unavailable

def fx (x : IxAICore.Fx) : SourceValue F := .field (ofInt x.raw)
def vec (xs : List IxAICore.Fx) : SourceValue F := .tuple (xs.map fx)
def mat (xss : List (List IxAICore.Fx)) : SourceValue F := .tuple (xss.map vec)

def get {α : Type} : Except String α → IO α := IO.ofExcept

open IxAICore in
/-- Every hint key `Fixed::step` requests, from IxAICore's intermediate values: the pre-rounding
sums (`fx.shr8`) and the hidden pre-activations (`fx.sign`). -/
def stepHintKeys (m : Model) (batch : List (List Fx × List Fx)) (lr : Fx) : List Int × List Int :=
  let hidden := m.b1.length
  let w2T := transposeN hidden m.w2
  let perExample : List (List Int × List Int) := batch.map fun (x, t) =>
    let (z, h) := m.hidden x
    let o := List.zipWith (fun row b => Fx.add (Fx.dot row h) b) m.w2 m.b2
    let dout := List.zipWith Fx.sub o t
    (m.w1.map (Fx.dotRaw · x) ++ m.w2.map (Fx.dotRaw · h) ++ w2T.map (Fx.dotRaw · dout),
     z.map (·.raw))
  let ds : List Delta := batch.map fun (x, t) => m.delta w2T x t
  let dzT := transposeN hidden (ds.map (·.dz))
  let xT := transposeN 8 (ds.map (·.x))
  let hT := transposeN hidden (ds.map (·.h))
  let doutT := transposeN m.b2.length (ds.map (·.dout))
  let gw1 : List Int := dzT.flatMap fun dz => xT.map fun x => Fx.dotRaw dz x
  let gw2 : List Int := doutT.flatMap fun d => hT.map fun h => Fx.dotRaw d h
  let shift : Int → Int := fun v => v >>> (8 : Nat)
  let grads : List Int := gw1.map shift ++ dzT.map Fx.sumRaw ++ gw2.map shift ++ doutT.map Fx.sumRaw
  let shr : List Int := perExample.flatMap (·.1) ++ gw1 ++ gw2 ++ grads.map fun g => lr.raw * g
  (shr.eraseDups, (perExample.flatMap (·.2)).eraseDups)

def hintTable (keys : List Int × List Int) : Array (Execution.HintEntry F) :=
  (keys.1.map fun v => (⟨.array .field 8, .field (ofInt v), .array .field ((shr8Words v).map .field), "fx.shr8"⟩ : Execution.HintEntry F)) ++
  (keys.2.map fun v => (⟨.array .field 8, .field (ofInt v), .array .field ((signWords v).map .field), "fx.sign"⟩ : Execution.HintEntry F))
  |>.toArray

def stepArgs (m : IxAICore.Model) (batch : List (List IxAICore.Fx × List IxAICore.Fx)) (lr : IxAICore.Fx) :
    List (SourceValue F) :=
  [mat m.w1, vec m.b1, mat m.w2, vec m.b2, mat (batch.map (·.1)), mat (batch.map (·.2)), fx lr]

def flat (m : IxAICore.Model) (batch : List (List IxAICore.Fx × List IxAICore.Fx)) (lr : IxAICore.Fx) : List Nat :=
  let enc := fun (x : IxAICore.Fx) => (ofInt x.raw).val
  (m.w1.flatten ++ m.b1 ++ m.w2.flatten ++ m.b2 ++ (batch.map (·.1)).flatten ++ (batch.map (·.2)).flatten ++ [lr]).map enc

def modelValue (m : IxAICore.Model) : SourceValue F := .tuple [mat m.w1, vec m.b1, mat m.w2, vec m.b2]

def run (out : String) : IO Unit := do
  let start ← IO.monoMsNow
  let prepared ← get <| Modules.prepare (source.toField F) entries
  IO.println s!"prepared in {(← IO.monoMsNow) - start} ms"
  let honest := prepared.environment.source.checkedHints hints
  -- The full-size configuration: 16 hidden units, batches of 20.
  let cfg : IxAICore.Config :=
    { seed := 42, hidden := 16, lrRaw := 2, epochs := 30, batch := 20, trainSize := 400, testSize := 200 }
  let s := IxAICore.Triage.spec
  let examples := (cfg.data s).map s.example
  let sched := cfg.schedule
  let batchOf := fun (idx : List Nat) => idx.map fun i => IxAICore.getD examples i (s.example default)
  let lr : IxAICore.Fx := ⟨cfg.lrRaw⟩
  -- Steps 0 and 1 of the real run, from the specified initial weights.
  let m0 := cfg.init s
  let m1 := m0.step lr (batchOf (sched.getD 0 []))
  for (m, idx, label) in [(m0, sched.getD 0 [], "step 0"), (m1, sched.getD 1 [], "step 1")] do
    let b := batchOf idx
    let t0 ← IO.monoMsNow
    let (actual, _) ← get <| prepared.run "Fixed::step" (stepArgs m b lr) (fuel := 100000000) (hints := honest)
    let expected := m.step lr b
    unless actual == modelValue expected do throw (IO.userError s!"{label}: Aiur step differs from Model.step")
    IO.println s!"{label}: Aiur step equals IxAICore Model.step ({(← IO.monoMsNow) - t0} ms semantic evaluation)"
  -- A dishonest rounding hint anywhere in the step is rejected.
  let shifted : HintDispatcher F := fun c k => match c, k with
    | "fx.shr8", .field v => .ok (.tuple ((shr8Words (toInt v + 256)).map .field))
    | c, k => hints c k
  let bad := prepared.environment.source.checkedHints shifted
  unless (prepared.run "Fixed::step" (stepArgs m0 (batchOf (sched.getD 0 [])) lr) (fuel := 100000000) (hints := bad)).toOption.isNone do
    throw (IO.userError "dishonest rounding hint accepted")
  IO.println "dishonest rounding hints rejected"
  -- Export step 0 as an execution package for the prover, with `Fixed::step` as its only entry.
  let stepOnly ← get <| Modules.prepare (source.toField F) ["Fixed::step"]
  let execution ← get stepOnly.exportExecution
  let compiled ← get (stepOnly.compileOptimized {})
  let (execution, trace) ← get (Trace.exportPlan p ZMod.val compiled.circuit.inlined.program compiled.circuit.artifact execution)
  let b0 := batchOf (sched.getD 0 [])
  let table ← get (execution.prepareHints (hintTable (stepHintKeys m0 b0 lr)))
  Artifact.write out (← get (Artifact.execution execution p ZMod.val (some trace) (flat m0 b0 lr) [] table))
  IO.println s!"exported step 0 to {out}: {table.size} hint entries, {compiled.circuit.system.chips.length} chips"

/-- Export every step of the full run as an execution package `DIR/step-NNN.ixa`. The circuit is
compiled once; each package carries that step's weights, batch, learning rate and hint table.
`DIR/expected.txt` lists, per step, the parameters `Model.step` produces, for the chain checker. -/
def exportAll (dir : String) (count : Nat) : IO Unit := do
  let cfg : IxAICore.Config :=
    { seed := 42, hidden := 16, lrRaw := 2, epochs := 30, batch := 20, trainSize := 400, testSize := 200 }
  let s := IxAICore.Triage.spec
  let examples := (cfg.data s).map s.example
  let sched := cfg.schedule
  let batchOf := fun (idx : List Nat) => idx.map fun i => IxAICore.getD examples i (s.example default)
  let lr : IxAICore.Fx := ⟨cfg.lrRaw⟩
  let t0 ← IO.monoMsNow
  let stepOnly ← get <| Modules.prepare (source.toField F) ["Fixed::step"]
  let execution ← get stepOnly.exportExecution
  let compiled ← get (stepOnly.compileOptimized {})
  let (execution, trace) ← get (Trace.exportPlan p ZMod.val compiled.circuit.inlined.program compiled.circuit.artifact execution)
  IO.println s!"compiled the step circuit once in {(← IO.monoMsNow) - t0} ms"
  IO.FS.createDirAll dir
  let mut m := cfg.init s
  let mut expected : Array String := #[]
  for (idx, i) in (sched.take count).zip (List.range count) do
    let b := batchOf idx
    let table ← get (execution.prepareHints (hintTable (stepHintKeys m b lr)))
    let name := s!"{dir}/step-{(toString (1000 + i)).drop 1}.ixa"
    Artifact.write name (← get (Artifact.execution execution p ZMod.val (some trace) (flat m b lr) [] table))
    m := m.step lr b
    expected := expected.push (" ".intercalate ((m.w1.flatten ++ m.b1 ++ m.w2.flatten ++ m.b2).map (toString ·.raw)))
  IO.FS.writeFile s!"{dir}/expected.txt" ("\n".intercalate expected.toList ++ "\n")
  IO.println s!"exported {count} steps to {dir} in {(← IO.monoMsNow) - t0} ms"

end IxAIAiur

def main (args : List String) : IO Unit :=
  match args with
  | ["all", dir, n] => IxAIAiur.exportAll dir n.toNat!
  | _ => IxAIAiur.run (args.headD "step0.ixa")
