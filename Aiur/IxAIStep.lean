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
* `bound v` returns `v` after checking `v + 4096 = lo + 32 hi` for two range-checked bytes, so
  `-4096 ≤ v < 4320`. `upd` bounds every parameter it produces this way, so the weights of every
  step stay small no matter how many steps run.

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
| `upd w lr g` | `upd` in `Model.step`: `Fx.sub w (Fx.mul lr g)`, checked by `bound` |
| `update_row8`, `update_row16` | the row function of `w1` and `w2` in `Model.step` |
| `update_w1`, `update_w2` | the fields `w1` and `w2` of `Model.step` |
| `update_bias16`, `update_bias11` | the fields `b1` and `b2` of `Model.step` |
| `step w1 b1 w2 b2 xs ts lr` | `Model.step lr m batch` for a batch of 20 |
| `train_block`, `train` | `List.foldl (Model.step lr)` over the gathered batches |

`train` takes the 600 batches already gathered, as 30 groups of 20, each batch as its inputs `xs`
and targets `ts`, and folds `step` over them in order, 20 steps in each `train_block`. Gathering
is the host's job: `IxAICore.train_eq_foldl_gather` shows that `IxAICore.train` is this fold over
`gather examples schedule`, so the claim "`train` on the gathered batches gives `W`" binds the
dataset through the statement rather than through the circuit. The grouping keeps every function
at 30 calls or fewer, within what the path-lemma generator (`IxAIRefine.ObsGen`) unfolds.

Where `IxAICore` rounds, `Fixed` rounds once with `shr8`, at the same place: every dot product
after its exact sum, every product `lr · g`, and nowhere else. Sums, `Fx.add` and `Fx.sub` are
field operations: they agree with `IxAICore`'s integer operations while the integers involved
stay below half the field's characteristic in magnitude. Every value that is rounded or
sign-tested is range-checked below 2^55 by `shr8` or `sign_split`, and every parameter a step
returns is range-checked below 2^13 by `bound`. With inputs and targets below 2^12 and `lr` at
most 2^8, those parameter bounds keep every intermediate integer of the next step below 2^55, so
no field operation wraps.

The tests below run `step` and `train` with an honest hint provider against `IxAICore`, check
that dishonest hints are rejected, and compile `step` to a circuit.
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
        [[r0[0], r1[0], r2[0], r3[0], r4[0], r5[0], r6[0], r7[0], r8[0], r9[0], r10[0]], [r0[1], r1[1], r2[1], r3[1], r4[1], r5[1], r6[1], r7[1], r8[1], r9[1], r10[1]], [r0[2], r1[2], r2[2], r3[2], r4[2], r5[2], r6[2], r7[2], r8[2], r9[2], r10[2]], [r0[3], r1[3], r2[3], r3[3], r4[3], r5[3], r6[3], r7[3], r8[3], r9[3], r10[3]], [r0[4], r1[4], r2[4], r3[4], r4[4], r5[4], r6[4], r7[4], r8[4], r9[4], r10[4]], [r0[5], r1[5], r2[5], r3[5], r4[5], r5[5], r6[5], r7[5], r8[5], r9[5], r10[5]], [r0[6], r1[6], r2[6], r3[6], r4[6], r5[6], r6[6], r7[6], r8[6], r9[6], r10[6]], [r0[7], r1[7], r2[7], r3[7], r4[7], r5[7], r6[7], r7[7], r8[7], r9[7], r10[7]], [r0[8], r1[8], r2[8], r3[8], r4[8], r5[8], r6[8], r7[8], r8[8], r9[8], r10[8]], [r0[9], r1[9], r2[9], r3[9], r4[9], r5[9], r6[9], r7[9], r8[9], r9[9], r10[9]], [r0[10], r1[10], r2[10], r3[10], r4[10], r5[10], r6[10], r7[10], r8[10], r9[10], r10[10]], [r0[11], r1[11], r2[11], r3[11], r4[11], r5[11], r6[11], r7[11], r8[11], r9[11], r10[11]], [r0[12], r1[12], r2[12], r3[12], r4[12], r5[12], r6[12], r7[12], r8[12], r9[12], r10[12]], [r0[13], r1[13], r2[13], r3[13], r4[13], r5[13], r6[13], r7[13], r8[13], r9[13], r10[13]], [r0[14], r1[14], r2[14], r3[14], r4[14], r5[14], r6[14], r7[14], r8[14], r9[14], r10[14]], [r0[15], r1[15], r2[15], r3[15], r4[15], r5[15], r6[15], r7[15], r8[15], r9[15], r10[15]]]
    }
    fn transpose20x16(m: [[Field; 16]; 20]) -> [[Field; 20]; 16] {
        let [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19] = m;
        [[r0[0], r1[0], r2[0], r3[0], r4[0], r5[0], r6[0], r7[0], r8[0], r9[0], r10[0], r11[0], r12[0], r13[0], r14[0], r15[0], r16[0], r17[0], r18[0], r19[0]], [r0[1], r1[1], r2[1], r3[1], r4[1], r5[1], r6[1], r7[1], r8[1], r9[1], r10[1], r11[1], r12[1], r13[1], r14[1], r15[1], r16[1], r17[1], r18[1], r19[1]], [r0[2], r1[2], r2[2], r3[2], r4[2], r5[2], r6[2], r7[2], r8[2], r9[2], r10[2], r11[2], r12[2], r13[2], r14[2], r15[2], r16[2], r17[2], r18[2], r19[2]], [r0[3], r1[3], r2[3], r3[3], r4[3], r5[3], r6[3], r7[3], r8[3], r9[3], r10[3], r11[3], r12[3], r13[3], r14[3], r15[3], r16[3], r17[3], r18[3], r19[3]], [r0[4], r1[4], r2[4], r3[4], r4[4], r5[4], r6[4], r7[4], r8[4], r9[4], r10[4], r11[4], r12[4], r13[4], r14[4], r15[4], r16[4], r17[4], r18[4], r19[4]], [r0[5], r1[5], r2[5], r3[5], r4[5], r5[5], r6[5], r7[5], r8[5], r9[5], r10[5], r11[5], r12[5], r13[5], r14[5], r15[5], r16[5], r17[5], r18[5], r19[5]], [r0[6], r1[6], r2[6], r3[6], r4[6], r5[6], r6[6], r7[6], r8[6], r9[6], r10[6], r11[6], r12[6], r13[6], r14[6], r15[6], r16[6], r17[6], r18[6], r19[6]], [r0[7], r1[7], r2[7], r3[7], r4[7], r5[7], r6[7], r7[7], r8[7], r9[7], r10[7], r11[7], r12[7], r13[7], r14[7], r15[7], r16[7], r17[7], r18[7], r19[7]], [r0[8], r1[8], r2[8], r3[8], r4[8], r5[8], r6[8], r7[8], r8[8], r9[8], r10[8], r11[8], r12[8], r13[8], r14[8], r15[8], r16[8], r17[8], r18[8], r19[8]], [r0[9], r1[9], r2[9], r3[9], r4[9], r5[9], r6[9], r7[9], r8[9], r9[9], r10[9], r11[9], r12[9], r13[9], r14[9], r15[9], r16[9], r17[9], r18[9], r19[9]], [r0[10], r1[10], r2[10], r3[10], r4[10], r5[10], r6[10], r7[10], r8[10], r9[10], r10[10], r11[10], r12[10], r13[10], r14[10], r15[10], r16[10], r17[10], r18[10], r19[10]], [r0[11], r1[11], r2[11], r3[11], r4[11], r5[11], r6[11], r7[11], r8[11], r9[11], r10[11], r11[11], r12[11], r13[11], r14[11], r15[11], r16[11], r17[11], r18[11], r19[11]], [r0[12], r1[12], r2[12], r3[12], r4[12], r5[12], r6[12], r7[12], r8[12], r9[12], r10[12], r11[12], r12[12], r13[12], r14[12], r15[12], r16[12], r17[12], r18[12], r19[12]], [r0[13], r1[13], r2[13], r3[13], r4[13], r5[13], r6[13], r7[13], r8[13], r9[13], r10[13], r11[13], r12[13], r13[13], r14[13], r15[13], r16[13], r17[13], r18[13], r19[13]], [r0[14], r1[14], r2[14], r3[14], r4[14], r5[14], r6[14], r7[14], r8[14], r9[14], r10[14], r11[14], r12[14], r13[14], r14[14], r15[14], r16[14], r17[14], r18[14], r19[14]], [r0[15], r1[15], r2[15], r3[15], r4[15], r5[15], r6[15], r7[15], r8[15], r9[15], r10[15], r11[15], r12[15], r13[15], r14[15], r15[15], r16[15], r17[15], r18[15], r19[15]]]
    }
    fn transpose20x8(m: [[Field; 8]; 20]) -> [[Field; 20]; 8] {
        let [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19] = m;
        [[r0[0], r1[0], r2[0], r3[0], r4[0], r5[0], r6[0], r7[0], r8[0], r9[0], r10[0], r11[0], r12[0], r13[0], r14[0], r15[0], r16[0], r17[0], r18[0], r19[0]], [r0[1], r1[1], r2[1], r3[1], r4[1], r5[1], r6[1], r7[1], r8[1], r9[1], r10[1], r11[1], r12[1], r13[1], r14[1], r15[1], r16[1], r17[1], r18[1], r19[1]], [r0[2], r1[2], r2[2], r3[2], r4[2], r5[2], r6[2], r7[2], r8[2], r9[2], r10[2], r11[2], r12[2], r13[2], r14[2], r15[2], r16[2], r17[2], r18[2], r19[2]], [r0[3], r1[3], r2[3], r3[3], r4[3], r5[3], r6[3], r7[3], r8[3], r9[3], r10[3], r11[3], r12[3], r13[3], r14[3], r15[3], r16[3], r17[3], r18[3], r19[3]], [r0[4], r1[4], r2[4], r3[4], r4[4], r5[4], r6[4], r7[4], r8[4], r9[4], r10[4], r11[4], r12[4], r13[4], r14[4], r15[4], r16[4], r17[4], r18[4], r19[4]], [r0[5], r1[5], r2[5], r3[5], r4[5], r5[5], r6[5], r7[5], r8[5], r9[5], r10[5], r11[5], r12[5], r13[5], r14[5], r15[5], r16[5], r17[5], r18[5], r19[5]], [r0[6], r1[6], r2[6], r3[6], r4[6], r5[6], r6[6], r7[6], r8[6], r9[6], r10[6], r11[6], r12[6], r13[6], r14[6], r15[6], r16[6], r17[6], r18[6], r19[6]], [r0[7], r1[7], r2[7], r3[7], r4[7], r5[7], r6[7], r7[7], r8[7], r9[7], r10[7], r11[7], r12[7], r13[7], r14[7], r15[7], r16[7], r17[7], r18[7], r19[7]]]
    }
    fn transpose20x11(m: [[Field; 11]; 20]) -> [[Field; 20]; 11] {
        let [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19] = m;
        [[r0[0], r1[0], r2[0], r3[0], r4[0], r5[0], r6[0], r7[0], r8[0], r9[0], r10[0], r11[0], r12[0], r13[0], r14[0], r15[0], r16[0], r17[0], r18[0], r19[0]], [r0[1], r1[1], r2[1], r3[1], r4[1], r5[1], r6[1], r7[1], r8[1], r9[1], r10[1], r11[1], r12[1], r13[1], r14[1], r15[1], r16[1], r17[1], r18[1], r19[1]], [r0[2], r1[2], r2[2], r3[2], r4[2], r5[2], r6[2], r7[2], r8[2], r9[2], r10[2], r11[2], r12[2], r13[2], r14[2], r15[2], r16[2], r17[2], r18[2], r19[2]], [r0[3], r1[3], r2[3], r3[3], r4[3], r5[3], r6[3], r7[3], r8[3], r9[3], r10[3], r11[3], r12[3], r13[3], r14[3], r15[3], r16[3], r17[3], r18[3], r19[3]], [r0[4], r1[4], r2[4], r3[4], r4[4], r5[4], r6[4], r7[4], r8[4], r9[4], r10[4], r11[4], r12[4], r13[4], r14[4], r15[4], r16[4], r17[4], r18[4], r19[4]], [r0[5], r1[5], r2[5], r3[5], r4[5], r5[5], r6[5], r7[5], r8[5], r9[5], r10[5], r11[5], r12[5], r13[5], r14[5], r15[5], r16[5], r17[5], r18[5], r19[5]], [r0[6], r1[6], r2[6], r3[6], r4[6], r5[6], r6[6], r7[6], r8[6], r9[6], r10[6], r11[6], r12[6], r13[6], r14[6], r15[6], r16[6], r17[6], r18[6], r19[6]], [r0[7], r1[7], r2[7], r3[7], r4[7], r5[7], r6[7], r7[7], r8[7], r9[7], r10[7], r11[7], r12[7], r13[7], r14[7], r15[7], r16[7], r17[7], r18[7], r19[7]], [r0[8], r1[8], r2[8], r3[8], r4[8], r5[8], r6[8], r7[8], r8[8], r9[8], r10[8], r11[8], r12[8], r13[8], r14[8], r15[8], r16[8], r17[8], r18[8], r19[8]], [r0[9], r1[9], r2[9], r3[9], r4[9], r5[9], r6[9], r7[9], r8[9], r9[9], r10[9], r11[9], r12[9], r13[9], r14[9], r15[9], r16[9], r17[9], r18[9], r19[9]], [r0[10], r1[10], r2[10], r3[10], r4[10], r5[10], r6[10], r7[10], r8[10], r9[10], r10[10], r11[10], r12[10], r13[10], r14[10], r15[10], r16[10], r17[10], r18[10], r19[10]]]
    }
    fn bound(v: Field) -> Field {
        let w = hint::<[Field; 2]>("fx.bound", v);
        let (lo, hi) = UInt8::from_fields(w[0], w[1]);
        assert_eq!(UInt8::to_field(lo) + 32 * UInt8::to_field(hi), v + 4096, "fx.bound");
        v
    }
    fn upd(w: Field, lr: Field, g: Field) -> Field { bound(w - mul(lr, g)) }
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
    fn train_block(w1: [[Field; 8]; 16], b1: [Field; 16], w2: [[Field; 16]; 11], b2: [Field; 11], lr: Field,
                   xs: [[[Field; 8]; 20]; 20], ts: [[[Field; 11]; 20]; 20]) -> ([[Field; 8]; 16], [Field; 16], [[Field; 16]; 11], [Field; 11]) {
        let [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19] = xs;
        let [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19] = ts;
        let (w1_0, b1_0, w2_0, b2_0) = step(w1, b1, w2, b2, x0, t0, lr);
        let (w1_1, b1_1, w2_1, b2_1) = step(w1_0, b1_0, w2_0, b2_0, x1, t1, lr);
        let (w1_2, b1_2, w2_2, b2_2) = step(w1_1, b1_1, w2_1, b2_1, x2, t2, lr);
        let (w1_3, b1_3, w2_3, b2_3) = step(w1_2, b1_2, w2_2, b2_2, x3, t3, lr);
        let (w1_4, b1_4, w2_4, b2_4) = step(w1_3, b1_3, w2_3, b2_3, x4, t4, lr);
        let (w1_5, b1_5, w2_5, b2_5) = step(w1_4, b1_4, w2_4, b2_4, x5, t5, lr);
        let (w1_6, b1_6, w2_6, b2_6) = step(w1_5, b1_5, w2_5, b2_5, x6, t6, lr);
        let (w1_7, b1_7, w2_7, b2_7) = step(w1_6, b1_6, w2_6, b2_6, x7, t7, lr);
        let (w1_8, b1_8, w2_8, b2_8) = step(w1_7, b1_7, w2_7, b2_7, x8, t8, lr);
        let (w1_9, b1_9, w2_9, b2_9) = step(w1_8, b1_8, w2_8, b2_8, x9, t9, lr);
        let (w1_10, b1_10, w2_10, b2_10) = step(w1_9, b1_9, w2_9, b2_9, x10, t10, lr);
        let (w1_11, b1_11, w2_11, b2_11) = step(w1_10, b1_10, w2_10, b2_10, x11, t11, lr);
        let (w1_12, b1_12, w2_12, b2_12) = step(w1_11, b1_11, w2_11, b2_11, x12, t12, lr);
        let (w1_13, b1_13, w2_13, b2_13) = step(w1_12, b1_12, w2_12, b2_12, x13, t13, lr);
        let (w1_14, b1_14, w2_14, b2_14) = step(w1_13, b1_13, w2_13, b2_13, x14, t14, lr);
        let (w1_15, b1_15, w2_15, b2_15) = step(w1_14, b1_14, w2_14, b2_14, x15, t15, lr);
        let (w1_16, b1_16, w2_16, b2_16) = step(w1_15, b1_15, w2_15, b2_15, x16, t16, lr);
        let (w1_17, b1_17, w2_17, b2_17) = step(w1_16, b1_16, w2_16, b2_16, x17, t17, lr);
        let (w1_18, b1_18, w2_18, b2_18) = step(w1_17, b1_17, w2_17, b2_17, x18, t18, lr);
        step(w1_18, b1_18, w2_18, b2_18, x19, t19, lr)
    }
    fn train(w1: [[Field; 8]; 16], b1: [Field; 16], w2: [[Field; 16]; 11], b2: [Field; 11], lr: Field,
             xs: [[[[Field; 8]; 20]; 20]; 30], ts: [[[[Field; 11]; 20]; 20]; 30]) -> ([[Field; 8]; 16], [Field; 16], [[Field; 16]; 11], [Field; 11]) {
        let [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29] = xs;
        let [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29] = ts;
        let (w1_0, b1_0, w2_0, b2_0) = train_block(w1, b1, w2, b2, lr, x0, t0);
        let (w1_1, b1_1, w2_1, b2_1) = train_block(w1_0, b1_0, w2_0, b2_0, lr, x1, t1);
        let (w1_2, b1_2, w2_2, b2_2) = train_block(w1_1, b1_1, w2_1, b2_1, lr, x2, t2);
        let (w1_3, b1_3, w2_3, b2_3) = train_block(w1_2, b1_2, w2_2, b2_2, lr, x3, t3);
        let (w1_4, b1_4, w2_4, b2_4) = train_block(w1_3, b1_3, w2_3, b2_3, lr, x4, t4);
        let (w1_5, b1_5, w2_5, b2_5) = train_block(w1_4, b1_4, w2_4, b2_4, lr, x5, t5);
        let (w1_6, b1_6, w2_6, b2_6) = train_block(w1_5, b1_5, w2_5, b2_5, lr, x6, t6);
        let (w1_7, b1_7, w2_7, b2_7) = train_block(w1_6, b1_6, w2_6, b2_6, lr, x7, t7);
        let (w1_8, b1_8, w2_8, b2_8) = train_block(w1_7, b1_7, w2_7, b2_7, lr, x8, t8);
        let (w1_9, b1_9, w2_9, b2_9) = train_block(w1_8, b1_8, w2_8, b2_8, lr, x9, t9);
        let (w1_10, b1_10, w2_10, b2_10) = train_block(w1_9, b1_9, w2_9, b2_9, lr, x10, t10);
        let (w1_11, b1_11, w2_11, b2_11) = train_block(w1_10, b1_10, w2_10, b2_10, lr, x11, t11);
        let (w1_12, b1_12, w2_12, b2_12) = train_block(w1_11, b1_11, w2_11, b2_11, lr, x12, t12);
        let (w1_13, b1_13, w2_13, b2_13) = train_block(w1_12, b1_12, w2_12, b2_12, lr, x13, t13);
        let (w1_14, b1_14, w2_14, b2_14) = train_block(w1_13, b1_13, w2_13, b2_13, lr, x14, t14);
        let (w1_15, b1_15, w2_15, b2_15) = train_block(w1_14, b1_14, w2_14, b2_14, lr, x15, t15);
        let (w1_16, b1_16, w2_16, b2_16) = train_block(w1_15, b1_15, w2_15, b2_15, lr, x16, t16);
        let (w1_17, b1_17, w2_17, b2_17) = train_block(w1_16, b1_16, w2_16, b2_16, lr, x17, t17);
        let (w1_18, b1_18, w2_18, b2_18) = train_block(w1_17, b1_17, w2_17, b2_17, lr, x18, t18);
        let (w1_19, b1_19, w2_19, b2_19) = train_block(w1_18, b1_18, w2_18, b2_18, lr, x19, t19);
        let (w1_20, b1_20, w2_20, b2_20) = train_block(w1_19, b1_19, w2_19, b2_19, lr, x20, t20);
        let (w1_21, b1_21, w2_21, b2_21) = train_block(w1_20, b1_20, w2_20, b2_20, lr, x21, t21);
        let (w1_22, b1_22, w2_22, b2_22) = train_block(w1_21, b1_21, w2_21, b2_21, lr, x22, t22);
        let (w1_23, b1_23, w2_23, b2_23) = train_block(w1_22, b1_22, w2_22, b2_22, lr, x23, t23);
        let (w1_24, b1_24, w2_24, b2_24) = train_block(w1_23, b1_23, w2_23, b2_23, lr, x24, t24);
        let (w1_25, b1_25, w2_25, b2_25) = train_block(w1_24, b1_24, w2_24, b2_24, lr, x25, t25);
        let (w1_26, b1_26, w2_26, b2_26) = train_block(w1_25, b1_25, w2_25, b2_25, lr, x26, t26);
        let (w1_27, b1_27, w2_27, b2_27) = train_block(w1_26, b1_26, w2_26, b2_26, lr, x27, t27);
        let (w1_28, b1_28, w2_28, b2_28) = train_block(w1_27, b1_27, w2_27, b2_27, lr, x28, t28);
        train_block(w1_28, b1_28, w2_28, b2_28, lr, x29, t29)
    }
}
⟧

def entries : List String := ["Fixed::mul", "Fixed::relu", "Fixed::pos", "Fixed::step", "Fixed::train"]

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

/-- The words `fx.bound` answers for `v`: `v + 4096` in base 32, low digit first. -/
def boundWords (i : Int) : List F :=
  let n := (i + 4096).toNat
  [((n % 32 : Nat) : F), ((n / 32 : Nat) : F)]

/-- The honest host. Its answers are checked by the program, so it is not trusted. -/
def hints : HintDispatcher F := fun channel key =>
  match channel, key with
  | "fx.shr8", .field s => .ok (.tuple ((shr8Words (toInt s)).map .field))
  | "fx.sign", .field v => .ok (.tuple ((signWords (toInt v)).map .field))
  | "fx.bound", .field v => .ok (.tuple ((boundWords (toInt v)).map .field))
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

/-- The `fx.bound` entries of a step that returns `next`: one per distinct parameter value, since
`upd` bounds every parameter it produces. -/
def boundTable (next : IxAICore.Model) : Array (Execution.HintEntry F) :=
  let keys := ((next.w1.flatten ++ next.b1 ++ next.w2.flatten ++ next.b2).map (·.raw)).eraseDups
  (keys.map fun v => (⟨.array .field 2, .field (ofInt v), .array .field ((boundWords v).map .field), "fx.bound"⟩ : Execution.HintEntry F))
  |>.toArray

def stepArgs (m : IxAICore.Model) (batch : List (List IxAICore.Fx × List IxAICore.Fx)) (lr : IxAICore.Fx) :
    List (SourceValue F) :=
  [mat m.w1, vec m.b1, mat m.w2, vec m.b2, mat (batch.map (·.1)), mat (batch.map (·.2)), fx lr]

def flat (m : IxAICore.Model) (batch : List (List IxAICore.Fx × List IxAICore.Fx)) (lr : IxAICore.Fx) : List Nat :=
  let enc := fun (x : IxAICore.Fx) => (ofInt x.raw).val
  (m.w1.flatten ++ m.b1 ++ m.w2.flatten ++ m.b2 ++ (batch.map (·.1)).flatten ++ (batch.map (·.2)).flatten ++ [lr]).map enc

def modelValue (m : IxAICore.Model) : SourceValue F := .tuple [mat m.w1, vec m.b1, mat m.w2, vec m.b2]

/-- The full-size configuration: 16 hidden units, batches of 20, 400 examples, 30 epochs of 20
steps. -/
def fullConfig : IxAICore.Config :=
  { seed := 42, hidden := 16, lrRaw := 2, epochs := 30, batch := 20, trainSize := 400, testSize := 200 }

def blocks20 {α : Type} (l : List α) : List (List α) := IxAICore.chunk 20 l l.length

/-- The arguments of `Fixed::train`: the initial model, `lr`, and the 600 gathered batches as 30
groups of 20, in order: first every batch's inputs, then every batch's targets. -/
def trainArgs (m : IxAICore.Model) (lr : IxAICore.Fx)
    (batches : List (List (List IxAICore.Fx × List IxAICore.Fx))) :
    Except String (List (SourceValue F)) := do
  unless batches.length == 600 && batches.all (·.length == 20) do
    throw "Fixed::train takes 600 batches of 20"
  unless batches.all (·.all fun (x, t) => x.length == 8 && t.length == 11) do
    throw "Fixed::train takes examples of 8 inputs and 11 targets"
  let groups := blocks20 batches
  return [mat m.w1, vec m.b1, mat m.w2, vec m.b2, fx lr,
    .tuple (groups.map fun g => .tuple (g.map fun b => mat (b.map (·.1)))),
    .tuple (groups.map fun g => .tuple (g.map fun b => mat (b.map (·.2))))]

def run (out : String) : IO Unit := do
  let start ← IO.monoMsNow
  let prepared ← get <| Modules.prepare (source.toField F) entries
  IO.println s!"prepared in {(← IO.monoMsNow) - start} ms"
  let honest := prepared.environment.source.checkedHints hints
  let cfg := fullConfig
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
  let table ← get (execution.prepareHints (hintTable (stepHintKeys m0 b0 lr) ++ boundTable (m0.step lr b0)))
  Artifact.write out (← get (Artifact.execution execution p ZMod.val (some trace) (flat m0 b0 lr) [] table))
  IO.println s!"exported step 0 to {out}: {table.size} hint entries, {compiled.circuit.system.chips.length} chips"

/-- Export steps as execution packages `DIR/step-NNN.ixa`, one per batch, from the initial model
`m0`. `step` gives each step's hint keys and the parameters it produces; those parameters are the
next step's weights and the step's `fx.bound` keys. The circuit is compiled once; each package carries that step's weights,
batch, learning rate and hint table. `DIR/expected.txt` lists, per step, the parameters `step`
returns, for the chain checker. -/
def exportWith (dir : String) (m0 : IxAICore.Model) (lr : IxAICore.Fx)
    (batches : List (List (List IxAICore.Fx × List IxAICore.Fx)))
    (step : IxAICore.Model → List (List IxAICore.Fx × List IxAICore.Fx) →
      IO ((List Int × List Int) × IxAICore.Model)) : IO Unit := do
  let t0 ← IO.monoMsNow
  let stepOnly ← get <| Modules.prepare (source.toField F) ["Fixed::step"]
  let execution ← get stepOnly.exportExecution
  let compiled ← get (stepOnly.compileOptimized {})
  let (execution, trace) ← get (Trace.exportPlan p ZMod.val compiled.circuit.inlined.program compiled.circuit.artifact execution)
  IO.println s!"compiled the step circuit once in {(← IO.monoMsNow) - t0} ms"
  IO.FS.createDirAll dir
  let mut m := m0
  let mut expected : Array String := #[]
  for (b, i) in batches.zip (List.range batches.length) do
    let (keys, next) ← step m b
    let table ← get (execution.prepareHints (hintTable keys ++ boundTable next))
    let name := s!"{dir}/step-{(toString (1000 + i)).drop 1}.ixa"
    Artifact.write name (← get (Artifact.execution execution p ZMod.val (some trace) (flat m b lr) [] table))
    m := next
    expected := expected.push (" ".intercalate ((m.w1.flatten ++ m.b1 ++ m.w2.flatten ++ m.b2).map (toString ·.raw)))
  IO.FS.writeFile s!"{dir}/expected.txt" ("\n".intercalate expected.toList ++ "\n")
  IO.println s!"exported {batches.length} steps to {dir} in {(← IO.monoMsNow) - t0} ms"

/-- Export the first `count` steps of the full run, with the host's hint keys and `Model.step`. -/
def exportAll (dir : String) (count : Nat) : IO Unit := do
  let cfg := fullConfig
  let s := IxAICore.Triage.spec
  let examples := (cfg.data s).map s.example
  let batchOf := fun (idx : List Nat) => idx.map fun i => IxAICore.getD examples i (s.example default)
  let lr : IxAICore.Fx := ⟨cfg.lrRaw⟩
  exportWith dir (cfg.init s) lr ((cfg.schedule.take count).map batchOf) fun m b =>
    pure (stepHintKeys m b lr, m.step lr b)

/-- Run `Fixed::train` on the gathered batches of the full schedule and check the trained model
against `IxAICore.train`. -/
def checkTrain : IO Unit := do
  let prepared ← get <| Modules.prepare (source.toField F) entries
  let honest := prepared.environment.source.checkedHints hints
  let cfg := fullConfig
  let s := IxAICore.Triage.spec
  let examples := (cfg.data s).map s.example
  let batches := IxAICore.gather examples cfg.schedule (s.example default)
  let args ← get (trainArgs (cfg.init s) ⟨cfg.lrRaw⟩ batches)
  let t0 ← IO.monoMsNow
  let (actual, _) ← get <| prepared.run "Fixed::train" args (fuel := 100000000) (hints := honest)
  unless actual == modelValue (IxAICore.train s cfg) do
    throw (IO.userError "Aiur train differs from IxAICore.train")
  IO.println s!"Aiur train equals IxAICore.train over {cfg.schedule.length} steps ({(← IO.monoMsNow) - t0} ms semantic evaluation)"

end IxAIAiur
