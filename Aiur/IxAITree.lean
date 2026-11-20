import IxAIStep
import Aiur.Library.Blake3

/-!
# The whole training run as one Aiur execution

`FixedTree::train_tree` runs the 600 SGD steps of the full configuration in one execution.
Its claim is narrow: the initial model and the learning rate in, a 32-byte root and the trained
model out (`[1, entry, m₀ (331), lr, root (32), m₆₀₀ (331)]`, 697 words). The batches are not
arguments: `read_batch i` takes batch `i` from the hint channels `fx.xs` and `fx.ts`, as
two little-endian bytes per word (`v + 32768`), each range-checked, so a word is determined by
its bytes. Step `i` then runs `Fixed::step` unchanged.

The root is a BLAKE3 Merkle tree over the steps. Leaf `i` is
`BLAKE3(enc(mᵢ₊₁) ‖ enc(batchᵢ))`, 1,422 bytes: the model after the step (`w1` rows, `b1`,
`w2` rows, `b2`) and the batch (20 inputs of 8, then 20 targets of 11), both in the same
two-byte encoding. A node over `n` steps from step `i` is `BLAKE3(left ‖ right)` over its
first `⌊n/2⌋` and remaining `⌈n/2⌉` steps (`half`), 64 bytes. Leaf and node preimages
have different lengths. The root therefore binds every batch, every intermediate model and the
order of the steps; any single step can be opened with its leaf and a Merkle path.

`range` folds `step` left to right, so the trained model is `List.foldl (Model.step lr)` over
the batches in order, as for `Fixed::train`, and each execution row is narrow: `Fixed::step`
is called 600 times instead of being unrolled into one entry row.

`FixedTree` is its own module, so `Fixed` and every circuit compiled from `IxAIStep.source`
(the step and block packages and their keys) are unchanged.
-/

namespace IxAIAiur
open Aiur

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def treeClient : Modules.Program Nat := aiur_library% (Library.Blake3.templates.append client) ⟦
module FixedTree {
    fn enc(v: Field, tail: Bytes::Stream) -> Bytes::Stream {
        let w = hint::<[Field; 2]>("fx.enc", v);
        let (b0, b1) = UInt8::from_fields(w[0], w[1]);
        assert_eq!(UInt8::to_field(b0) + 256 * UInt8::to_field(b1), v + 32768, "fx.enc");
        &(Lists::Node::Cons(b0, &(Lists::Node::Cons(b1, tail))))
    }
    fn dec(lo: Field, hi: Field, tail: Bytes::Stream) -> (Field, Bytes::Stream) {
        let (b0, b1) = UInt8::from_fields(lo, hi);
        (UInt8::to_field(b0) + 256 * UInt8::to_field(b1) - 32768, &(Lists::Node::Cons(b0, &(Lists::Node::Cons(b1, tail)))))
    }
    fn enc_row8(row: [Field; 8], tail: Bytes::Stream) -> Bytes::Stream {
        let t8 = tail;
        let t7 = enc(row[7], t8);
        let t6 = enc(row[6], t7);
        let t5 = enc(row[5], t6);
        let t4 = enc(row[4], t5);
        let t3 = enc(row[3], t4);
        let t2 = enc(row[2], t3);
        let t1 = enc(row[1], t2);
        let t0 = enc(row[0], t1);
        t0
    }
    fn enc_row11(row: [Field; 11], tail: Bytes::Stream) -> Bytes::Stream {
        let t11 = tail;
        let t10 = enc(row[10], t11);
        let t9 = enc(row[9], t10);
        let t8 = enc(row[8], t9);
        let t7 = enc(row[7], t8);
        let t6 = enc(row[6], t7);
        let t5 = enc(row[5], t6);
        let t4 = enc(row[4], t5);
        let t3 = enc(row[3], t4);
        let t2 = enc(row[2], t3);
        let t1 = enc(row[1], t2);
        let t0 = enc(row[0], t1);
        t0
    }
    fn enc_row16(row: [Field; 16], tail: Bytes::Stream) -> Bytes::Stream {
        let t16 = tail;
        let t15 = enc(row[15], t16);
        let t14 = enc(row[14], t15);
        let t13 = enc(row[13], t14);
        let t12 = enc(row[12], t13);
        let t11 = enc(row[11], t12);
        let t10 = enc(row[10], t11);
        let t9 = enc(row[9], t10);
        let t8 = enc(row[8], t9);
        let t7 = enc(row[7], t8);
        let t6 = enc(row[6], t7);
        let t5 = enc(row[5], t6);
        let t4 = enc(row[4], t5);
        let t3 = enc(row[3], t4);
        let t2 = enc(row[2], t3);
        let t1 = enc(row[1], t2);
        let t0 = enc(row[0], t1);
        t0
    }
    fn dec_row8(raw: [Field; 16], tail: Bytes::Stream) -> ([Field; 8], Bytes::Stream) {
        let t8 = tail;
        let (v7, t7) = dec(raw[14], raw[15], t8);
        let (v6, t6) = dec(raw[12], raw[13], t7);
        let (v5, t5) = dec(raw[10], raw[11], t6);
        let (v4, t4) = dec(raw[8], raw[9], t5);
        let (v3, t3) = dec(raw[6], raw[7], t4);
        let (v2, t2) = dec(raw[4], raw[5], t3);
        let (v1, t1) = dec(raw[2], raw[3], t2);
        let (v0, t0) = dec(raw[0], raw[1], t1);
        ([v0, v1, v2, v3, v4, v5, v6, v7], t0)
    }
    fn dec_row11(raw: [Field; 22], tail: Bytes::Stream) -> ([Field; 11], Bytes::Stream) {
        let t11 = tail;
        let (v10, t10) = dec(raw[20], raw[21], t11);
        let (v9, t9) = dec(raw[18], raw[19], t10);
        let (v8, t8) = dec(raw[16], raw[17], t9);
        let (v7, t7) = dec(raw[14], raw[15], t8);
        let (v6, t6) = dec(raw[12], raw[13], t7);
        let (v5, t5) = dec(raw[10], raw[11], t6);
        let (v4, t4) = dec(raw[8], raw[9], t5);
        let (v3, t3) = dec(raw[6], raw[7], t4);
        let (v2, t2) = dec(raw[4], raw[5], t3);
        let (v1, t1) = dec(raw[2], raw[3], t2);
        let (v0, t0) = dec(raw[0], raw[1], t1);
        ([v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10], t0)
    }
    fn enc_model(w1: [[Field; 8]; 16], b1: [Field; 16], w2: [[Field; 16]; 11], b2: [Field; 11], tail: Bytes::Stream) -> Bytes::Stream {
        let s = enc_row11(b2, tail);
        let s = enc_row16(w2[10], s);
        let s = enc_row16(w2[9], s);
        let s = enc_row16(w2[8], s);
        let s = enc_row16(w2[7], s);
        let s = enc_row16(w2[6], s);
        let s = enc_row16(w2[5], s);
        let s = enc_row16(w2[4], s);
        let s = enc_row16(w2[3], s);
        let s = enc_row16(w2[2], s);
        let s = enc_row16(w2[1], s);
        let s = enc_row16(w2[0], s);
        let s = enc_row16(b1, s);
        let s = enc_row8(w1[15], s);
        let s = enc_row8(w1[14], s);
        let s = enc_row8(w1[13], s);
        let s = enc_row8(w1[12], s);
        let s = enc_row8(w1[11], s);
        let s = enc_row8(w1[10], s);
        let s = enc_row8(w1[9], s);
        let s = enc_row8(w1[8], s);
        let s = enc_row8(w1[7], s);
        let s = enc_row8(w1[6], s);
        let s = enc_row8(w1[5], s);
        let s = enc_row8(w1[4], s);
        let s = enc_row8(w1[3], s);
        let s = enc_row8(w1[2], s);
        let s = enc_row8(w1[1], s);
        let s = enc_row8(w1[0], s);
        s
    }
    fn read_batch(i: Field) -> ([[Field; 8]; 20], [[Field; 11]; 20], Bytes::Stream) {
        let xr = hint::<[[Field; 16]; 20]>("fx.xs", i);
        let tr = hint::<[[Field; 22]; 20]>("fx.ts", i);
        let s = &(Lists::Node::Nil);
        let (t19, s) = dec_row11(tr[19], s);
        let (t18, s) = dec_row11(tr[18], s);
        let (t17, s) = dec_row11(tr[17], s);
        let (t16, s) = dec_row11(tr[16], s);
        let (t15, s) = dec_row11(tr[15], s);
        let (t14, s) = dec_row11(tr[14], s);
        let (t13, s) = dec_row11(tr[13], s);
        let (t12, s) = dec_row11(tr[12], s);
        let (t11, s) = dec_row11(tr[11], s);
        let (t10, s) = dec_row11(tr[10], s);
        let (t9, s) = dec_row11(tr[9], s);
        let (t8, s) = dec_row11(tr[8], s);
        let (t7, s) = dec_row11(tr[7], s);
        let (t6, s) = dec_row11(tr[6], s);
        let (t5, s) = dec_row11(tr[5], s);
        let (t4, s) = dec_row11(tr[4], s);
        let (t3, s) = dec_row11(tr[3], s);
        let (t2, s) = dec_row11(tr[2], s);
        let (t1, s) = dec_row11(tr[1], s);
        let (t0, s) = dec_row11(tr[0], s);
        let (x19, s) = dec_row8(xr[19], s);
        let (x18, s) = dec_row8(xr[18], s);
        let (x17, s) = dec_row8(xr[17], s);
        let (x16, s) = dec_row8(xr[16], s);
        let (x15, s) = dec_row8(xr[15], s);
        let (x14, s) = dec_row8(xr[14], s);
        let (x13, s) = dec_row8(xr[13], s);
        let (x12, s) = dec_row8(xr[12], s);
        let (x11, s) = dec_row8(xr[11], s);
        let (x10, s) = dec_row8(xr[10], s);
        let (x9, s) = dec_row8(xr[9], s);
        let (x8, s) = dec_row8(xr[8], s);
        let (x7, s) = dec_row8(xr[7], s);
        let (x6, s) = dec_row8(xr[6], s);
        let (x5, s) = dec_row8(xr[5], s);
        let (x4, s) = dec_row8(xr[4], s);
        let (x3, s) = dec_row8(xr[3], s);
        let (x2, s) = dec_row8(xr[2], s);
        let (x1, s) = dec_row8(xr[1], s);
        let (x0, s) = dec_row8(xr[0], s);
        ([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19], [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19], s)
    }
    fn node(l: [UInt8::U8; 32], r: [UInt8::U8; 32]) -> [UInt8::U8; 32] {
        let s = &(Lists::Node::Nil);
        let s = &(Lists::Node::Cons(r[31], s));
        let s = &(Lists::Node::Cons(r[30], s));
        let s = &(Lists::Node::Cons(r[29], s));
        let s = &(Lists::Node::Cons(r[28], s));
        let s = &(Lists::Node::Cons(r[27], s));
        let s = &(Lists::Node::Cons(r[26], s));
        let s = &(Lists::Node::Cons(r[25], s));
        let s = &(Lists::Node::Cons(r[24], s));
        let s = &(Lists::Node::Cons(r[23], s));
        let s = &(Lists::Node::Cons(r[22], s));
        let s = &(Lists::Node::Cons(r[21], s));
        let s = &(Lists::Node::Cons(r[20], s));
        let s = &(Lists::Node::Cons(r[19], s));
        let s = &(Lists::Node::Cons(r[18], s));
        let s = &(Lists::Node::Cons(r[17], s));
        let s = &(Lists::Node::Cons(r[16], s));
        let s = &(Lists::Node::Cons(r[15], s));
        let s = &(Lists::Node::Cons(r[14], s));
        let s = &(Lists::Node::Cons(r[13], s));
        let s = &(Lists::Node::Cons(r[12], s));
        let s = &(Lists::Node::Cons(r[11], s));
        let s = &(Lists::Node::Cons(r[10], s));
        let s = &(Lists::Node::Cons(r[9], s));
        let s = &(Lists::Node::Cons(r[8], s));
        let s = &(Lists::Node::Cons(r[7], s));
        let s = &(Lists::Node::Cons(r[6], s));
        let s = &(Lists::Node::Cons(r[5], s));
        let s = &(Lists::Node::Cons(r[4], s));
        let s = &(Lists::Node::Cons(r[3], s));
        let s = &(Lists::Node::Cons(r[2], s));
        let s = &(Lists::Node::Cons(r[1], s));
        let s = &(Lists::Node::Cons(r[0], s));
        let s = &(Lists::Node::Cons(l[31], s));
        let s = &(Lists::Node::Cons(l[30], s));
        let s = &(Lists::Node::Cons(l[29], s));
        let s = &(Lists::Node::Cons(l[28], s));
        let s = &(Lists::Node::Cons(l[27], s));
        let s = &(Lists::Node::Cons(l[26], s));
        let s = &(Lists::Node::Cons(l[25], s));
        let s = &(Lists::Node::Cons(l[24], s));
        let s = &(Lists::Node::Cons(l[23], s));
        let s = &(Lists::Node::Cons(l[22], s));
        let s = &(Lists::Node::Cons(l[21], s));
        let s = &(Lists::Node::Cons(l[20], s));
        let s = &(Lists::Node::Cons(l[19], s));
        let s = &(Lists::Node::Cons(l[18], s));
        let s = &(Lists::Node::Cons(l[17], s));
        let s = &(Lists::Node::Cons(l[16], s));
        let s = &(Lists::Node::Cons(l[15], s));
        let s = &(Lists::Node::Cons(l[14], s));
        let s = &(Lists::Node::Cons(l[13], s));
        let s = &(Lists::Node::Cons(l[12], s));
        let s = &(Lists::Node::Cons(l[11], s));
        let s = &(Lists::Node::Cons(l[10], s));
        let s = &(Lists::Node::Cons(l[9], s));
        let s = &(Lists::Node::Cons(l[8], s));
        let s = &(Lists::Node::Cons(l[7], s));
        let s = &(Lists::Node::Cons(l[6], s));
        let s = &(Lists::Node::Cons(l[5], s));
        let s = &(Lists::Node::Cons(l[4], s));
        let s = &(Lists::Node::Cons(l[3], s));
        let s = &(Lists::Node::Cons(l[2], s));
        let s = &(Lists::Node::Cons(l[1], s));
        let s = &(Lists::Node::Cons(l[0], s));
        Blake3::digest_bytes(Blake3::hash(s))
    }
    fn leaf(w1: [[Field; 8]; 16], b1: [Field; 16], w2: [[Field; 16]; 11], b2: [Field; 11], lr: Field, i: Field)
            -> ([[Field; 8]; 16], [Field; 16], [[Field; 16]; 11], [Field; 11], [UInt8::U8; 32]) {
        let (xs, ts, batch) = read_batch(i);
        let (nw1, nb1, nw2, nb2) = Fixed::step(w1, b1, w2, b2, xs, ts, lr);
        let bytes = enc_model(nw1, nb1, nw2, nb2, batch);
        (nw1, nb1, nw2, nb2, Blake3::digest_bytes(Blake3::hash(bytes)))
    }
    fn half(n: Field) -> Field {
        match n {
            600 => { 300 },
            300 => { 150 },
            150 => { 75 },
            75 => { 37 },
            38 => { 19 },
            37 => { 18 },
            19 => { 9 },
            18 => { 9 },
            10 => { 5 },
            9 => { 4 },
            5 => { 2 },
            4 => { 2 },
            3 => { 1 },
            2 => { 1 },
        }
    }
    fn range(w1: [[Field; 8]; 16], b1: [Field; 16], w2: [[Field; 16]; 11], b2: [Field; 11], lr: Field, i: Field, n: Field)
            -> ([[Field; 8]; 16], [Field; 16], [[Field; 16]; 11], [Field; 11], [UInt8::U8; 32]) {
        match n {
            1 => { leaf(w1, b1, w2, b2, lr, i) },
            _ => {
                let k = half(n);
                let (lw1, lb1, lw2, lb2, l) = range(w1, b1, w2, b2, lr, i, k);
                let (rw1, rb1, rw2, rb2, r) = range(lw1, lb1, lw2, lb2, lr, i + k, n - k);
                (rw1, rb1, rw2, rb2, node(l, r))
            },
        }
    }
    fn train_tree(w1: [[Field; 8]; 16], b1: [Field; 16], w2: [[Field; 16]; 11], b2: [Field; 11], lr: Field)
            -> ([UInt8::U8; 32], [[Field; 8]; 16], [Field; 16], [[Field; 16]; 11], [Field; 11]) {
        let (nw1, nb1, nw2, nb2, root) = range(w1, b1, w2, b2, lr, 0, 600);
        (root, nw1, nb1, nw2, nb2)
    }

}
⟧

def treeSource : Modules.Program Nat := (Library.Blake3.source.append client).append treeClient

end IxAIAiur
