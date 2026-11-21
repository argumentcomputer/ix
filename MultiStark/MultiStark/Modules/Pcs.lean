import Aiur.Modules.Frontend

/-! # MultiStark module `Pcs`

The polynomial commitment scheme (FRI) verifier.

Formal Aiur source, written as Lean syntax (`aiur⟦ … ⟧`). `MultiStark.recursionSource`
and `MultiStark.aggregateSource` (`MultiStark/MultiStark/Program.lean`) compose the modules. -/

namespace MultiStark.Source

def pcs : Aiur.Modules.Program Nat := aiur⟦
module Pcs {
  enum FrontierNode { Mk(Field, Lists::List<Field>, Lists::List<Lists::List<UInt64::U64>>, ProofDeserialize::DigestP) }

  enum Bucket { Mk(Field, ProofDeserialize::Ext, ProofDeserialize::Ext, ProofDeserialize::Ext) }

  enum RollBucket { Mk(Field, ProofDeserialize::Ext) }

  enum HeightInfo { Mk(Field, ProofDeserialize::Ext, Goldilocks::Goldilocks) }

  fn compress_ordered(bit: Field, d: ProofDeserialize::DigestP, s: ProofDeserialize::DigestP) -> ProofDeserialize::DigestP {
      match bit {
        0 => {  Mmcs::mmcs_compress(d, s) } ,
        _ => {  Mmcs::mmcs_compress(s, d) } ,
      }
    }

  fn has_height(lhs: Lists::List<Field>, target: Field) -> Field {
      match (*(lhs)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(h, rest) => {
          match Fields::is_zero(h - target) {
            1 => {  1 } ,
            _ => {  has_height(rest, target) } ,
          } } ,
      }
    }

  fn select_rows(rows: Lists::List<Lists::List<UInt64::U64>>, lhs: Lists::List<Field>, target: Field) -> Lists::List<Lists::List<UInt64::U64>> {
      match (*(rows)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(r, rrest) => {
          let &Lists::Node::Cons(lh, lrest) = lhs;
          match Fields::is_zero(lh - target) {
            0 => {  select_rows(rrest, lrest, target) } ,
            _ => {  match (*(r)) {
              Lists::Node::Nil => {  select_rows(rrest, lrest, target) } ,
              _ => {  (&(Lists::Node::Cons(r, select_rows(rrest, lrest, target)))) } ,
            } } ,
          } } ,
      }
    }

  fn select_rows_le(rows: Lists::List<Lists::List<UInt64::U64>>, lhs: Lists::List<Field>, target: Field) -> Lists::List<Lists::List<UInt64::U64>> {
      match (*(rows)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(r, rrest) => {
          let &Lists::Node::Cons(lh, lrest) = lhs;
          match UInt32::less_than_fields(target, lh) {
            1 => {  select_rows_le(rrest, lrest, target) } ,
            _ => {  match (*(r)) {
              Lists::Node::Nil => {  select_rows_le(rrest, lrest, target) } ,
              _ => {  (&(Lists::Node::Cons(r, select_rows_le(rrest, lrest, target)))) } ,
            } } ,
          } } ,
      }
    }

  fn rows_pop(cur: Lists::List<UInt64::U64>, rows: Lists::List<Lists::List<UInt64::U64>>) -> (UInt64::U64, Lists::List<UInt64::U64>, Lists::List<Lists::List<UInt64::U64>>, Field) {
      match (*(cur)) {
        Lists::Node::Cons(x, rest) => {
          assert_eq!(Goldilocks::gl_lt_p(x), 1);
          (x, rest, rows, 1) } ,
        Lists::Node::Nil => {  match (*(rows)) {
          Lists::Node::Nil => {  ([UInt8::BYTE_0; 8], cur, rows, 0) } ,
          Lists::Node::Cons(r, rrest) => {  rows_pop(r, rrest) } ,
        } } ,
      }
    }

  fn leaf_hash_at(rows: Lists::List<Lists::List<UInt64::U64>>, lhs: Lists::List<Field>, target: Field) -> ProofDeserialize::DigestP {
      (&(StarkHash::b3_to_digest(StarkHash::b3_rows(select_rows(rows, lhs, target)))))
    }

  fn inject_maybe(rows: Lists::List<Lists::List<UInt64::U64>>, lhs: Lists::List<Field>, lh: Field, d: ProofDeserialize::DigestP) -> ProofDeserialize::DigestP {
      match has_height(lhs, lh) {
        0 => {  d } ,
        _ => {  Mmcs::mmcs_compress(d, leaf_hash_at(rows, lhs, lh)) } ,
      }
    }

  fn bits_to_num(bits: Lists::List<Field>) -> Field {
      match (*(bits)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(b, rest) => {  b + 2 * bits_to_num(rest) } ,
      }
    }

  fn glist_rev(l: Lists::List<Field>, acc: Lists::List<Field>) -> Lists::List<Field> {
      match (*(l)) {
        Lists::Node::Nil => {  acc } ,
        Lists::Node::Cons(b, rest) => {  glist_rev(rest, (&(Lists::Node::Cons(b, acc)))) } ,
      }
    }

  fn exp_by_bits(base: Goldilocks::Goldilocks, bits: Lists::List<Field>) -> Goldilocks::Goldilocks {
      match (*(bits)) {
        Lists::Node::Nil => {  1 } ,
        Lists::Node::Cons(b, rest) => {
          let half = exp_by_bits(base * base, rest);
          match b {
            0 => {  half } ,
            _ => {  base * half } ,
          } } ,
      }
    }

  fn fri_fold2(index_bits: Lists::List<Field>, log_height: Field, beta: ProofDeserialize::Ext, e0: ProofDeserialize::Ext, e1: ProofDeserialize::Ext) -> ProofDeserialize::Ext {
      let g = StarkVerifier::two_adic_gen(log_height + 1);
      let s = exp_by_bits(g, glist_rev(index_bits, (&(Lists::Node::Nil))));
      let inv_2s = Goldilocks::gl_inverse(s + s);
      let t1 = [(e0[0] + e1[0]) * 9223372034707292161, (e0[1] + e1[1]) * 9223372034707292161];
      let diff_div = [(e0[0] - e1[0]) * inv_2s, (e0[1] - e1[1]) * inv_2s];
      Goldilocks::eg_add(t1, Goldilocks::eg_mul(beta, diff_div))
    }

  fn ro_fold_1pt(p_x: Lists::List<UInt64::U64>, p_z: Lists::List<ProofDeserialize::Ext>,
        alpha: ProofDeserialize::Ext) -> (ProofDeserialize::Ext, ProofDeserialize::Ext) {
      match (*(p_x)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(p_z));
          ([0, 0], [1, 0]) } ,
        Lists::Node::Cons(lane, pxr) => {
          let &Lists::Node::Cons(pz, pzr) = p_z;
          let (s, pw) = ro_fold_1pt(pxr, pzr, alpha);
          let v = ProofDeserialize::limb_to_field(lane);
          (Goldilocks::eg_add(Goldilocks::eg_sub(pz, [v, 0]), Goldilocks::eg_mul(alpha, s)),
           Goldilocks::eg_mul(alpha, pw)) } ,
      }
    }

  fn ro_fold_2pt(p_x: Lists::List<UInt64::U64>, pz0: Lists::List<ProofDeserialize::Ext>,
        pz1: Lists::List<ProofDeserialize::Ext>, alpha: ProofDeserialize::Ext)
        -> (ProofDeserialize::Ext, ProofDeserialize::Ext, ProofDeserialize::Ext) {
      match (*(p_x)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(pz0));
          let Lists::Node::Nil = (*(pz1));
          ([0, 0], [0, 0], [1, 0]) } ,
        Lists::Node::Cons(lane, pxr) => {
          let &Lists::Node::Cons(z0, r0) = pz0;
          let &Lists::Node::Cons(z1, r1) = pz1;
          let (s0, s1, pw) = ro_fold_2pt(pxr, r0, r1, alpha);
          let v = ProofDeserialize::limb_to_field(lane);
          (Goldilocks::eg_add(Goldilocks::eg_sub(z0, [v, 0]), Goldilocks::eg_mul(alpha, s0)),
           Goldilocks::eg_add(Goldilocks::eg_sub(z1, [v, 0]), Goldilocks::eg_mul(alpha, s1)),
           Goldilocks::eg_mul(alpha, pw)) } ,
      }
    }

  fn ext_row_onto(row: Lists::List<ProofDeserialize::Ext>, tail: Bytes::Stream) -> Bytes::Stream {
      match (*(row)) {
        Lists::Node::Nil => {  tail } ,
        Lists::Node::Cons(e, rest) => {  StarkVerifier::b8_onto(Goldilocks::gl_to_bytes(e[0]), StarkVerifier::b8_onto(Goldilocks::gl_to_bytes(e[1]), ext_row_onto(rest, tail))) } ,
      }
    }

  fn points_onto(pts: Lists::List<Lists::List<ProofDeserialize::Ext>>, tail: Bytes::Stream) -> Bytes::Stream {
      match (*(pts)) {
        Lists::Node::Nil => {  tail } ,
        Lists::Node::Cons(row, rest) => {  ext_row_onto(row, points_onto(rest, tail)) } ,
      }
    }

  fn round_onto(round: ProofDeserialize::OpenedRound, tail: Bytes::Stream) -> Bytes::Stream {
      match (*(round)) {
        Lists::Node::Nil => {  tail } ,
        Lists::Node::Cons(mat, rest) => {  points_onto(mat, round_onto(rest, tail)) } ,
      }
    }

  inline fn prep_onto(prep_opt: ProofDeserialize::PreprocessedOpt, tail: Bytes::Stream) -> Bytes::Stream {
      match prep_opt {
        ProofDeserialize::PreprocessedOpt::NoPreprocessed => {  tail } ,
        ProofDeserialize::PreprocessedOpt::SomePreprocessed(round) => {  round_onto(round, tail) } ,
      }
    }

  fn obs_log_arities(input: Bytes::Stream, comms: Lists::List<ProofDeserialize::MerkleCap>) -> Bytes::Stream {
      match (*(comms)) {
        Lists::Node::Nil => {  input } ,
        Lists::Node::Cons(_c, rest) => {
          obs_log_arities(StarkVerifier::snoc_b8(input, [UInt8::BYTE_1, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]), rest) } ,
      }
    }

  fn pcs_check_witness(input: Bytes::Stream, witness: UInt64::U64, bits: Field) -> (Bytes::Stream, Bytes::Stream) {
      match bits {
        0 => {  (input, (&(Lists::Node::Nil))) } ,
        _ => {
          let (pbits, i1, o1) = Transcript::ch_sample_bits(StarkVerifier::snoc_b8(input, witness), (&(Lists::Node::Nil)), bits);
          assert_eq!(bits_to_num(pbits), 0);
          (i1, o1) } ,
      }
    }

  fn pcs_betas(input: Bytes::Stream, comms: Lists::List<ProofDeserialize::MerkleCap>, witnesses: Lists::List<UInt64::U64>, bits: Field)
        -> (Lists::List<ProofDeserialize::Ext>, Bytes::Stream) {
      match (*(comms)) {
        Lists::Node::Nil => {  ((&(Lists::Node::Nil)), input) } ,
        Lists::Node::Cons(c, rest) => {
          let &Lists::Node::Cons(w, wrest) = witnesses;
          let (i1, o1) = pcs_check_witness(StarkVerifier::snoc_cap(input, c), w, bits);
          let (b0, b1, i2, _o) = Transcript::ch_sample_ext(i1, o1);
          let (bs, i3) = pcs_betas(i2, rest, wrest, bits);
          ((&(Lists::Node::Cons([Goldilocks::gl_val(b0), Goldilocks::gl_val(b1)], bs))), i3) } ,
      }
    }

  fn heights_fit(log_degrees: Lists::List<UInt8::U8>, log_blowup: Field, log_gmax: Field, rem: Field) -> Field {
      match rem {
        0 => {  1 } ,
        _ => {
          let &Lists::Node::Cons(ld, rest) = log_degrees;
          UInt32::less_than_fields(UInt8::to_field(ld) + log_blowup, log_gmax + 1)
            * heights_fit(rest, log_blowup, log_gmax, rem - 1) } ,
      }
    }

  fn insert_height_desc(hs: Lists::List<Field>, lh: Field) -> Lists::List<Field> {
      match (*(hs)) {
        Lists::Node::Nil => {  (&(Lists::Node::Cons(lh, (&(Lists::Node::Nil))))) } ,
        Lists::Node::Cons(h, rest) => {
          match Fields::is_zero(h - lh) {
            1 => {  hs } ,
            _ => {
              match UInt32::less_than_fields(h, lh) {
                1 => {  (&(Lists::Node::Cons(lh, hs))) } ,
                _ => {  (&(Lists::Node::Cons(h, insert_height_desc(rest, lh)))) } ,
              } } ,
          } } ,
      }
    }

  fn collect_heights_desc(log_degrees: Lists::List<UInt8::U8>, log_blowup: Field, acc: Lists::List<Field>) -> Lists::List<Field> {
      match (*(log_degrees)) {
        Lists::Node::Nil => {  acc } ,
        Lists::Node::Cons(ld, rest) => {
          let lh = UInt8::to_field(ld) + log_blowup;
          collect_heights_desc(rest, log_blowup, insert_height_desc(acc, lh)) } ,
      }
    }

  fn build_init_buckets(hs: Lists::List<Field>) -> Lists::List<Bucket> {
      match (*(hs)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(h, rest) => {
          (&(Lists::Node::Cons(Bucket::Mk(h, [1, 0], [0, 0], [0, 0]), build_init_buckets(rest)))) } ,
      }
    }

  fn build_height_infos(hs: Lists::List<Field>, log_blowup: Field, zeta: ProofDeserialize::Ext) -> Lists::List<HeightInfo> {
      match (*(hs)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(h, rest) => {
          let zn = Goldilocks::eg_mul(zeta, [StarkVerifier::two_adic_gen(h - log_blowup), 0]);
          let g_h = StarkVerifier::two_adic_gen(h);
          (&(Lists::Node::Cons(HeightInfo::Mk(h, zn, g_h), build_height_infos(rest, log_blowup, zeta)))) } ,
      }
    }

  fn bucket_update_2pt(buckets: Lists::List<Bucket>, lh: Field, p_x: Lists::List<UInt64::U64>,
        pz0: Lists::List<ProofDeserialize::Ext>, pz1: Lists::List<ProofDeserialize::Ext>,
        alpha: ProofDeserialize::Ext) -> Lists::List<Bucket> {
      let &Lists::Node::Cons(b, rest) = buckets;
      let Bucket::Mk(h, ap, ro0, ro1) = b;
      match Fields::is_zero(h - lh) {
        1 => {
          let (s0, s1, pw) = ro_fold_2pt(p_x, pz0, pz1, alpha);
          let ro0_2 = Goldilocks::eg_add(ro0, Goldilocks::eg_mul(ap, s0));
          let ap1 = Goldilocks::eg_mul(ap, pw);
          let ro1_2 = Goldilocks::eg_add(ro1, Goldilocks::eg_mul(ap1, s1));
          let ap2 = Goldilocks::eg_mul(ap1, pw);
          (&(Lists::Node::Cons(Bucket::Mk(h, ap2, ro0_2, ro1_2), rest))) } ,
        _ => {  (&(Lists::Node::Cons(b, bucket_update_2pt(rest, lh, p_x, pz0, pz1, alpha)))) } ,
      }
    }

  fn bucket_update_1pt(buckets: Lists::List<Bucket>, lh: Field, p_x: Lists::List<UInt64::U64>,
        pz0: Lists::List<ProofDeserialize::Ext>, alpha: ProofDeserialize::Ext) -> Lists::List<Bucket> {
      let &Lists::Node::Cons(b, rest) = buckets;
      let Bucket::Mk(h, ap, ro0, ro1) = b;
      match Fields::is_zero(h - lh) {
        1 => {
          let (s0, pw) = ro_fold_1pt(p_x, pz0, alpha);
          let ro0_2 = Goldilocks::eg_add(ro0, Goldilocks::eg_mul(ap, s0));
          let ap1 = Goldilocks::eg_mul(ap, pw);
          (&(Lists::Node::Cons(Bucket::Mk(h, ap1, ro0_2, ro1), rest))) } ,
        _ => {  (&(Lists::Node::Cons(b, bucket_update_1pt(rest, lh, p_x, pz0, alpha)))) } ,
      }
    }

  fn finalize_buckets(buckets: Lists::List<Bucket>, infos: Lists::List<HeightInfo>,
        cur_bits: Lists::List<Field>, prev_h: Field, log_blowup: Field,
        zeta: ProofDeserialize::Ext) -> Lists::List<RollBucket> {
      match (*(buckets)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(infos));
          (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(b, brest) => {
          let &Lists::Node::Cons(info, irest) = infos;
          let Bucket::Mk(h, _ap, ro0, ro1) = b;
          let HeightInfo::Mk(_hi_h, zn, g_h) = info;
          let bits_h = Lists::drop(cur_bits, prev_h - h);
          let x = 7 * exp_by_bits(g_h, glist_rev(bits_h, (&(Lists::Node::Nil))));
          let q0 = Goldilocks::eg_inverse(Goldilocks::eg_sub(zeta, [x, 0]));
          let q1 = Goldilocks::eg_inverse(Goldilocks::eg_sub(zn, [x, 0]));
          let ro = Goldilocks::eg_add(Goldilocks::eg_mul(q0, ro0), Goldilocks::eg_mul(q1, ro1));
          let _z = match Fields::is_zero(h - log_blowup) {
            1 => {  assert_eq!(Goldilocks::eg_eq(ro, [0, 0]), 1); 1 } ,
            _ => {  1 } ,
          };
          (&(Lists::Node::Cons(RollBucket::Mk(h, ro),
            finalize_buckets(brest, irest, bits_h, h, log_blowup, zeta)))) } ,
      }
    }

  fn prep_count(prep_opt: ProofDeserialize::PreprocessedOpt) -> Field {
      match prep_opt {
        ProofDeserialize::PreprocessedOpt::NoPreprocessed => {  0 } ,
        ProofDeserialize::PreprocessedOpt::SomePreprocessed(_r) => {  1 } ,
      }
    }

  fn open_batch_2pt(buckets: Lists::List<Bucket>, log_blowup: Field,
        log_degrees: Lists::List<UInt8::U8>, base_rows: Lists::List<Lists::List<UInt64::U64>>,
        opened: ProofDeserialize::OpenedRound, alpha: ProofDeserialize::Ext) -> Lists::List<Bucket> {
      match (*(log_degrees)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(base_rows));
          let Lists::Node::Nil = (*(opened));
          buckets } ,
        Lists::Node::Cons(ld, ld_rest) => {
          let &Lists::Node::Cons(p_x, br_rest) = base_rows;
          let &Lists::Node::Cons(mat, op_rest) = opened;
          let &Lists::Node::Cons(pz0, mat1) = mat;
          let &Lists::Node::Cons(pz1, _mat2) = mat1;
          let b = bucket_update_2pt(buckets, UInt8::to_field(ld) + log_blowup, p_x, pz0, pz1, alpha);
          open_batch_2pt(b, log_blowup, ld_rest, br_rest, op_rest, alpha) } ,
      }
    }

  fn open_quotient(buckets: Lists::List<Bucket>, log_blowup: Field,
        log_degrees: Lists::List<UInt8::U8>, base_rows: Lists::List<Lists::List<UInt64::U64>>,
        q_opened: ProofDeserialize::OpenedRound, alpha: ProofDeserialize::Ext) -> Lists::List<Bucket> {
      match (*(log_degrees)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(base_rows));
          let Lists::Node::Nil = (*(q_opened));
          buckets } ,
        Lists::Node::Cons(ld, ld_rest) => {
          let &Lists::Node::Cons(p_x, br_rest) = base_rows;
          let &Lists::Node::Cons(qmat, qo_rest) = q_opened;
          let &Lists::Node::Cons(pz0, _qmat_rest) = qmat;
          let b = bucket_update_1pt(buckets, UInt8::to_field(ld) + log_blowup, p_x, pz0, alpha);
          open_quotient(b, log_blowup, ld_rest, br_rest, qo_rest, alpha) } ,
      }
    }

  fn open_prep(buckets: Lists::List<Bucket>, log_blowup: Field,
        log_degrees: Lists::List<UInt8::U8>, prep_indices: Lists::List<SystemDeserialize::OptIdx>,
        base_rows: Lists::List<Lists::List<UInt64::U64>>, prep_round: ProofDeserialize::OpenedRound,
        alpha: ProofDeserialize::Ext) -> Lists::List<Bucket> {
      match (*(log_degrees)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(prep_indices));
          let Lists::Node::Nil = (*(base_rows));
          let Lists::Node::Nil = (*(prep_round));
          buckets } ,
        Lists::Node::Cons(ld, ld_rest) => {
          let &Lists::Node::Cons(pi, pi_rest) = prep_indices;
          match pi {
            SystemDeserialize::OptIdx::NoIdx => {
              open_prep(buckets, log_blowup, ld_rest, pi_rest, base_rows, prep_round, alpha) } ,
            SystemDeserialize::OptIdx::SomeIdx(_j) => {
              let &Lists::Node::Cons(p_x, br_rest) = base_rows;
              let &Lists::Node::Cons(mat, pr_rest) = prep_round;
              let &Lists::Node::Cons(pz0, mat1) = mat;
              let &Lists::Node::Cons(pz1, _mat2) = mat1;
              let b = bucket_update_2pt(buckets, UInt8::to_field(ld) + log_blowup, p_x, pz0, pz1, alpha);
              open_prep(b, log_blowup, ld_rest, pi_rest, br_rest, pr_rest, alpha) } ,
          } } ,
      }
    }

  inline fn open_prep_batch(buckets: Lists::List<Bucket>, rows_p: Lists::List<Lists::List<UInt64::U64>>,
        prep_opt: ProofDeserialize::PreprocessedOpt, prep_indices: Lists::List<SystemDeserialize::OptIdx>,
        log_degrees: Lists::List<UInt8::U8>, log_blowup: Field, alpha: ProofDeserialize::Ext) -> Lists::List<Bucket> {
      match prep_opt {
        ProofDeserialize::PreprocessedOpt::NoPreprocessed => {  buckets } ,
        ProofDeserialize::PreprocessedOpt::SomePreprocessed(prep_round) => {
          open_prep(buckets, log_blowup, log_degrees, prep_indices, rows_p, prep_round, alpha) } ,
      }
    }

  fn heights_all(log_degrees: Lists::List<UInt8::U8>, log_blowup: Field) -> Lists::List<Field> {
      match (*(log_degrees)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(ld, rest) => {
          (&(Lists::Node::Cons(UInt8::to_field(ld) + log_blowup, heights_all(rest, log_blowup)))) } ,
      }
    }

  fn heights_max(hs: Lists::List<Field>) -> Field {
      match (*(hs)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(h, rest) => {
          let m = heights_max(rest);
          match UInt32::less_than_fields(m, h) {
            0 => {  m } ,
            _ => {  h } ,
          } } ,
      }
    }

  fn heights_prep(log_degrees: Lists::List<UInt8::U8>, log_blowup: Field,
        prep_indices: Lists::List<SystemDeserialize::OptIdx>) -> Lists::List<Field> {
      match (*(log_degrees)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(prep_indices));
          (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(ld, ld_rest) => {
          let &Lists::Node::Cons(pi, pi_rest) = prep_indices;
          match pi {
            SystemDeserialize::OptIdx::NoIdx => {  heights_prep(ld_rest, log_blowup, pi_rest) } ,
            SystemDeserialize::OptIdx::SomeIdx(_j) => {
              (&(Lists::Node::Cons(UInt8::to_field(ld) + log_blowup, heights_prep(ld_rest, log_blowup, pi_rest)))) } ,
          } } ,
      }
    }

  inline fn recon_evals(bit: Field, folded: ProofDeserialize::Ext, sib: ProofDeserialize::Ext) -> (ProofDeserialize::Ext, ProofDeserialize::Ext) {
      match bit {
        0 => {  (folded, sib) } ,
        _ => {  (sib, folded) } ,
      }
    }

  inline fn flatten2(e0: ProofDeserialize::Ext, e1: ProofDeserialize::Ext) -> Lists::List<UInt64::U64> {
      (&(Lists::Node::Cons(Goldilocks::gl_to_bytes(e0[0]), (&(Lists::Node::Cons(Goldilocks::gl_to_bytes(e0[1]),
        (&(Lists::Node::Cons(Goldilocks::gl_to_bytes(e1[0]), (&(Lists::Node::Cons(Goldilocks::gl_to_bytes(e1[1]), (&(Lists::Node::Nil))))))))))))))
    }

  fn rollin(folded: ProofDeserialize::Ext, log_folded: Field, beta: ProofDeserialize::Ext, ro_rest: Lists::List<RollBucket>) -> (ProofDeserialize::Ext, Lists::List<RollBucket>) {
      match (*(ro_rest)) {
        Lists::Node::Nil => {  (folded, ro_rest) } ,
        Lists::Node::Cons(b, rest) => {
          let RollBucket::Mk(h, ro) = b;
          match Fields::is_zero(h - log_folded) {
            1 => {  (Goldilocks::eg_add(folded, Goldilocks::eg_mul(Goldilocks::eg_mul(beta, beta), ro)), rest) } ,
            _ => {  (folded, ro_rest) } ,
          } } ,
      }
    }

  fn verify_query(folded: ProofDeserialize::Ext, betas: Lists::List<ProofDeserialize::Ext>,
        openings: Lists::List<Lists::List<ProofDeserialize::Ext>>, domidx: Lists::List<Field>, log_cur: Field,
        ro_rest: Lists::List<RollBucket>, log_final: Field) -> (ProofDeserialize::Ext, Lists::List<Lists::List<UInt64::U64>>) {
      match (*(openings)) {
        Lists::Node::Nil => {
          assert_eq!(Fields::is_zero(log_cur - log_final), 1);
          let Lists::Node::Nil = (*(ro_rest));
          (folded, (&(Lists::Node::Nil))) } ,
        Lists::Node::Cons(sibs, op_rest) => {
          let &Lists::Node::Cons(beta, beta_rest) = betas;
          let &Lists::Node::Cons(sib, sib_nil) = sibs;
          let Lists::Node::Nil = (*(sib_nil));
          let &Lists::Node::Cons(ibit, idrest) = domidx;
          let log_folded = log_cur - 1;
          let (e0, e1) = recon_evals(ibit, folded, sib);
          let folded1 = fri_fold2(idrest, log_folded, beta, e0, e1);
          let (folded2, ro_rest2) = rollin(folded1, log_folded, beta, ro_rest);
          let (result, rows) = verify_query(folded2, beta_rest, op_rest, idrest, log_folded, ro_rest2, log_final);
          (result, (&(Lists::Node::Cons(flatten2(e0, e1), rows)))) } ,
      }
    }

  fn verify_one_query(idxbits: Lists::List<Field>, rows_s1: Lists::List<Lists::List<UInt64::U64>>,
        rows_s2: Lists::List<Lists::List<UInt64::U64>>, rows_q: Lists::List<Lists::List<UInt64::U64>>,
        rows_p: Lists::List<Lists::List<UInt64::U64>>, q_sibs: Lists::List<Lists::List<ProofDeserialize::Ext>>,
        init_buckets: Lists::List<Bucket>, height_infos: Lists::List<HeightInfo>,
        alpha: ProofDeserialize::Ext, stage1: ProofDeserialize::OpenedRound, stage2: ProofDeserialize::OpenedRound,
        q_opened: ProofDeserialize::OpenedRound, prep_opt: ProofDeserialize::PreprocessedOpt,
        prep_indices: Lists::List<SystemDeserialize::OptIdx>, log_degrees: Lists::List<UInt8::U8>,
        zeta: ProofDeserialize::Ext, log_blowup: Field, log_gmax: Field,
        betas: Lists::List<ProofDeserialize::Ext>, final_eval: ProofDeserialize::Ext) -> Lists::List<Lists::List<UInt64::U64>> {
      let buckets = open_batch_2pt(init_buckets, log_blowup, log_degrees, rows_s1, stage1, alpha);
      let buckets = open_batch_2pt(buckets, log_blowup, log_degrees, rows_s2, stage2, alpha);
      let buckets = open_quotient(buckets, log_blowup, log_degrees, rows_q, q_opened, alpha);
      let buckets = open_prep_batch(buckets, rows_p, prep_opt, prep_indices, log_degrees, log_blowup, alpha);
      let roll_buckets = finalize_buckets(buckets, height_infos, idxbits, log_gmax, log_blowup, zeta);

      let &Lists::Node::Cons(b0, ro_rest) = roll_buckets;
      let RollBucket::Mk(h0, folded_start) = b0;
      assert_eq!(Fields::is_zero(h0 - log_gmax), 1);
      let (folded, fri_rows) = verify_query(folded_start, betas, q_sibs, idxbits, log_gmax, ro_rest, log_blowup);

      assert_eq!(Goldilocks::eg_eq(final_eval, folded), 1);
      fri_rows
    }

  fn extract_step_sibs(steps: Lists::List<ProofDeserialize::CommitPhaseMultiStep>)
        -> Lists::List<Lists::List<Lists::List<ProofDeserialize::Ext>>> {
      match (*(steps)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(s, rest) => {
          let ProofDeserialize::CommitPhaseMultiStep::Mk(_la, sibs, _proof) = s;
          (&(Lists::Node::Cons(sibs, extract_step_sibs(rest)))) } ,
      }
    }

  fn peel_step_sibs(step_sibs: Lists::List<Lists::List<Lists::List<ProofDeserialize::Ext>>>)
        -> (Lists::List<Lists::List<ProofDeserialize::Ext>>, Lists::List<Lists::List<Lists::List<ProofDeserialize::Ext>>>) {
      match (*(step_sibs)) {
        Lists::Node::Nil => {  ((&(Lists::Node::Nil)), (&(Lists::Node::Nil))) } ,
        Lists::Node::Cons(sibs, rest) => {
          let &Lists::Node::Cons(q_sib, sibs_rest) = sibs;
          let (q_list, rem_list) = peel_step_sibs(rest);
          ((&(Lists::Node::Cons(q_sib, q_list))), (&(Lists::Node::Cons(sibs_rest, rem_list)))) } ,
      }
    }

  fn query_loop(indices: Lists::List<Lists::List<Field>>,
        s1rows: Lists::List<Lists::List<Lists::List<UInt64::U64>>>,
        s2rows: Lists::List<Lists::List<Lists::List<UInt64::U64>>>,
        qrows: Lists::List<Lists::List<Lists::List<UInt64::U64>>>,
        prows: Lists::List<Lists::List<Lists::List<UInt64::U64>>>,
        step_sibs: Lists::List<Lists::List<Lists::List<ProofDeserialize::Ext>>>,
        init_buckets: Lists::List<Bucket>, height_infos: Lists::List<HeightInfo>,
        alpha: ProofDeserialize::Ext, stage1: ProofDeserialize::OpenedRound, stage2: ProofDeserialize::OpenedRound,
        q_opened: ProofDeserialize::OpenedRound, prep_opt: ProofDeserialize::PreprocessedOpt,
        prep_indices: Lists::List<SystemDeserialize::OptIdx>, log_degrees: Lists::List<UInt8::U8>,
        zeta: ProofDeserialize::Ext, log_blowup: Field, log_gmax: Field,
        betas: Lists::List<ProofDeserialize::Ext>, final_eval: ProofDeserialize::Ext)
        -> Lists::List<Lists::List<Lists::List<UInt64::U64>>> {
      match (*(indices)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(s1rows));
          let Lists::Node::Nil = (*(s2rows));
          let Lists::Node::Nil = (*(qrows));
          let Lists::Node::Nil = (*(prows));
          (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(idxbits, irest) => {
          let &Lists::Node::Cons(rows_s1, s1rest) = s1rows;
          let &Lists::Node::Cons(rows_s2, s2rest) = s2rows;
          let &Lists::Node::Cons(rows_q, qrest) = qrows;
          let (rows_p, prest) = match prep_opt {
            ProofDeserialize::PreprocessedOpt::NoPreprocessed => {  ((&(Lists::Node::Nil)), prows) } ,
            ProofDeserialize::PreprocessedOpt::SomePreprocessed(_r) => {
              let &Lists::Node::Cons(rp, rpr) = prows;
              (rp, rpr) } ,
          };
          let (q_sibs, next_step_sibs) = peel_step_sibs(step_sibs);
          let qrows_out = verify_one_query(idxbits, rows_s1, rows_s2, rows_q, rows_p, q_sibs,
            init_buckets, height_infos, alpha, stage1, stage2, q_opened, prep_opt,
            prep_indices, log_degrees, zeta, log_blowup, log_gmax, betas, final_eval);
          (&(Lists::Node::Cons(qrows_out, query_loop(irest, s1rest, s2rest, qrest, prest, next_step_sibs,
            init_buckets, height_infos, alpha, stage1, stage2, q_opened, prep_opt,
            prep_indices, log_degrees, zeta, log_blowup, log_gmax, betas, final_eval)))) } ,
      }
    }

  fn sample_query_indices(input: Bytes::Stream, output: Bytes::Stream, n: Field,
        log_gmax: Field) -> Lists::List<Lists::List<Field>> {
      match n {
        0 => {  (&(Lists::Node::Nil)) } ,
        _ => {
          let (bits, input2, output2) = Transcript::ch_sample_bits(input, output, log_gmax);
          (&(Lists::Node::Cons(bits, sample_query_indices(input2, output2, n - 1, log_gmax)))) } ,
      }
    }

  fn drop_index_bits(indices: Lists::List<Lists::List<Field>>, n: Field) -> Lists::List<Lists::List<Field>> {
      match (*(indices)) {
        Lists::Node::Nil => {  indices } ,
        Lists::Node::Cons(bits, rest) => {
          (&(Lists::Node::Cons(Lists::drop(bits, n), drop_index_bits(rest, n)))) } ,
      }
    }

  fn peel_round_rows(all_rows: Lists::List<Lists::List<Lists::List<UInt64::U64>>>)
        -> (Lists::List<Lists::List<Lists::List<UInt64::U64>>>, Lists::List<Lists::List<Lists::List<UInt64::U64>>>) {
      match (*(all_rows)) {
        Lists::Node::Nil => {  ((&(Lists::Node::Nil)), (&(Lists::Node::Nil))) } ,
        Lists::Node::Cons(qrows, rest) => {
          let &Lists::Node::Cons(r_row, qrest) = qrows;
          let (round_rows, rem_rows) = peel_round_rows(rest);
          ((&(Lists::Node::Cons((&(Lists::Node::Cons(r_row, (&(Lists::Node::Nil))))), round_rows))),
           (&(Lists::Node::Cons(qrest, rem_rows)))) } ,
      }
    }

  fn verify_commit_multi(steps: Lists::List<ProofDeserialize::CommitPhaseMultiStep>, comms: Lists::List<ProofDeserialize::MerkleCap>,
        all_rows: Lists::List<Lists::List<Lists::List<UInt64::U64>>>, indices: Lists::List<Lists::List<Field>>,
        log_cur: Field) -> Field {
      match (*(steps)) {
        Lists::Node::Nil => {  Fields::is_zero(Lists::length(comms)) } ,
        Lists::Node::Cons(s, srest) => {
          let &Lists::Node::Cons(c, crest) = comms;
          let ProofDeserialize::CommitPhaseMultiStep::Mk(la, sibs, proof) = s;
          assert_eq!(UInt8::to_field(la), 1);
          assert_eq!(Lists::length(sibs), Lists::length(indices));
          let next_indices = drop_index_bits(indices, 1);
          let lh = log_cur - 1;
          let (round_rows, rem_rows) = peel_round_rows(all_rows);
          assert_eq!(Mmcs::mmcs_verify_multi(c, round_rows,
            (&(Lists::Node::Cons(lh, (&(Lists::Node::Nil))))), next_indices, proof, lh), 1);
          verify_commit_multi(srest, crest, rem_rows, next_indices, lh) } ,
      }
    }

  inline fn pcs_fri_verify(post_zeta_input: Bytes::Stream, stage1: ProofDeserialize::OpenedRound, stage2: ProofDeserialize::OpenedRound,
        q_opened: ProofDeserialize::OpenedRound, prep_opt: ProofDeserialize::PreprocessedOpt, opening: ProofDeserialize::FriProof,
        s1c: ProofDeserialize::MerkleCap, s2c: ProofDeserialize::MerkleCap, qc: ProofDeserialize::MerkleCap, prep_commit: ProofDeserialize::MerkleCap,
        prep_indices: Lists::List<SystemDeserialize::OptIdx>, log_degrees: Lists::List<UInt8::U8>,
        zeta: ProofDeserialize::Ext, num_circuits: Field, log_blowup: Field, num_queries: Field, commit_pow_bits: Field,
        query_pow_bits: Field) -> Field {
      let ProofDeserialize::FriProof::Mk(commit_phase_commits, pw, input_openings, commit_phase_openings,
        final_poly, qpw) = opening;
      let num_rounds = Lists::length(commit_phase_commits);

      assert_eq!(Fields::is_zero(Lists::length(pw) - num_rounds), 1);
      assert_eq!(Lists::length(input_openings), 3 + prep_count(prep_opt));
      assert_eq!(Fields::is_zero(Lists::length(commit_phase_openings) - num_rounds), 1);
      let &Lists::Node::Cons(final_eval, fp_nil) = final_poly;
      let Lists::Node::Nil = (*(fp_nil));

      let obs = round_onto(stage1, round_onto(stage2, round_onto(q_opened,
        prep_onto(prep_opt, (&(Lists::Node::Nil))))));
      let input = Lists::concat(post_zeta_input, obs);

      let (a0, a1, input, _oa) = Transcript::ch_sample_ext(input, (&(Lists::Node::Nil)));
      let alpha = [Goldilocks::gl_val(a0), Goldilocks::gl_val(a1)];

      let (betas, input) = pcs_betas(input, commit_phase_commits, pw, commit_pow_bits);
      let input = Lists::concat(input, ext_row_onto(final_poly, (&(Lists::Node::Nil))));
      let input = obs_log_arities(input, commit_phase_commits);

      let (input, output) = pcs_check_witness(input, qpw, query_pow_bits);

      let log_gmax = num_rounds + log_blowup;

      assert_eq!(UInt32::less_than_fields(log_gmax, 33), 1);
      assert_eq!(heights_fit(log_degrees, log_blowup, log_gmax, num_circuits), 1);
      let indices = sample_query_indices(input, output, num_queries, log_gmax);
      let &Lists::Node::Cons(bo_s1, io1) = input_openings;
      let &Lists::Node::Cons(bo_s2, io2) = io1;
      let &Lists::Node::Cons(bo_q, io3) = io2;
      let ProofDeserialize::BatchMultiOpening::Mk(s1rows, s1proof) = bo_s1;
      let ProofDeserialize::BatchMultiOpening::Mk(s2rows, s2proof) = bo_s2;
      let ProofDeserialize::BatchMultiOpening::Mk(qrows, qproof) = bo_q;
      let hall = heights_all(log_degrees, log_blowup);
      assert_eq!(Mmcs::mmcs_verify_multi(s1c, s1rows, hall, indices, s1proof, log_gmax), 1);
      assert_eq!(Mmcs::mmcs_verify_multi(s2c, s2rows, hall, indices, s2proof, log_gmax), 1);
      assert_eq!(Mmcs::mmcs_verify_multi(qc, qrows, hall, indices, qproof, log_gmax), 1);
      let prows = match prep_opt {
        ProofDeserialize::PreprocessedOpt::NoPreprocessed => {
          let Lists::Node::Nil = (*(io3));
          (&(Lists::Node::Nil)) } ,
        ProofDeserialize::PreprocessedOpt::SomePreprocessed(_round) => {
          let &Lists::Node::Cons(bo_p, io4) = io3;
          let Lists::Node::Nil = (*(io4));
          let ProofDeserialize::BatchMultiOpening::Mk(pr, pproof) = bo_p;
          let ph = heights_prep(log_degrees, log_blowup, prep_indices);
          let lp = heights_max(ph);
          let pindices = drop_index_bits(indices, log_gmax - lp);
          assert_eq!(Mmcs::mmcs_verify_multi(prep_commit, pr, ph, pindices, pproof, lp), 1);
          pr } ,
      };
      let distinct_hs = collect_heights_desc(log_degrees, log_blowup, (&(Lists::Node::Nil)));
      let init_buckets = build_init_buckets(distinct_hs);
      let height_infos = build_height_infos(distinct_hs, log_blowup, zeta);
      let step_sibs = extract_step_sibs(commit_phase_openings);
      let fri_rows = query_loop(indices, s1rows, s2rows, qrows, prows, step_sibs,
        init_buckets, height_infos, alpha, stage1, stage2, q_opened, prep_opt,
        prep_indices, log_degrees, zeta, log_blowup, log_gmax, betas, final_eval);
      verify_commit_multi(commit_phase_openings, commit_phase_commits, fri_rows, indices, log_gmax)
    }
}
⟧

end MultiStark.Source
