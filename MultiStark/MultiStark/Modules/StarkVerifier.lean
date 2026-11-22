import Aiur.Modules.Frontend

/-! # MultiStark module `StarkVerifier`

The multi-stark verifier: constraints, lookups and openings.

Formal Aiur source, written as Lean syntax (`aiur⟦ … ⟧`). `MultiStark.recursionSource`
and `MultiStark.aggregateSource` (`MultiStark/MultiStark/Program.lean`) compose the modules. -/

namespace MultiStark.Source

def starkVerifier : Aiur.Modules.Program Nat := aiur⟦
module StarkVerifier {
  inline fn ext_is_zero(e: ProofDeserialize::Ext) -> Field {
      Fields::is_zero(e[0]) * Fields::is_zero(e[1])
    }

  fn b8_onto(b: [UInt8::U8; 8], tail: Bytes::Stream) -> Bytes::Stream {
      (&(Lists::Node::Cons(b[0], (&(Lists::Node::Cons(b[1], (&(Lists::Node::Cons(b[2],
      (&(Lists::Node::Cons(b[3], (&(Lists::Node::Cons(b[4], (&(Lists::Node::Cons(b[5],
      (&(Lists::Node::Cons(b[6], (&(Lists::Node::Cons(b[7], tail))))))))))))))))))))))))
    }

  inline fn digest_onto(d: ProofDeserialize::Digest, tail: Bytes::Stream) -> Bytes::Stream {
      b8_onto(d[0], b8_onto(d[1], b8_onto(d[2], b8_onto(d[3], tail))))
    }

  fn cap_onto(cap: ProofDeserialize::MerkleCap, tail: Bytes::Stream) -> Bytes::Stream {
      match (*(cap)) {
        Lists::Node::Nil => {  tail } ,
        Lists::Node::Cons(d, rest) => {
          let Lists::Node::Nil = (*(rest));
          digest_onto((*(d)), tail) } ,
      }
    }

  fn log_degrees_onto(lds: Lists::List<UInt8::U8>, tail: Bytes::Stream) -> Bytes::Stream {
      match (*(lds)) {
        Lists::Node::Nil => {  tail } ,
        Lists::Node::Cons(ld, rest) => {
          b8_onto([ld, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0], log_degrees_onto(rest, tail)) } ,
      }
    }

  fn rev_onto(l: Bytes::Stream, acc: Bytes::Stream) -> Bytes::Stream {
      match (*(l)) {
        Lists::Node::Nil => {  acc } ,
        Lists::Node::Cons(b, rest) => {  rev_onto(rest, (&(Lists::Node::Cons(b, acc)))) } ,
      }
    }

  fn cons8(d: [Field; 8], tail: Lists::List<Field>) -> Lists::List<Field> {
      (&(Lists::Node::Cons(d[0], (&(Lists::Node::Cons(d[1], (&(Lists::Node::Cons(d[2],
      (&(Lists::Node::Cons(d[3], (&(Lists::Node::Cons(d[4], (&(Lists::Node::Cons(d[5],
      (&(Lists::Node::Cons(d[6], (&(Lists::Node::Cons(d[7], tail))))))))))))))))))))))))
    }

  fn take_bits(bits: Lists::List<Field>, n: Field) -> Lists::List<Field> {
      match n {
        0 => {  (&(Lists::Node::Nil)) } ,
        _ => {
          let &Lists::Node::Cons(b, rest) = bits;
          (&(Lists::Node::Cons(b, take_bits(rest, n - 1)))) } ,
      }
    }

  fn snoc_b8(input: Bytes::Stream, b: [UInt8::U8; 8]) -> Bytes::Stream {
      Lists::concat(input, b8_onto(b, (&(Lists::Node::Nil))))
    }

  fn snoc_cap(input: Bytes::Stream, cap: ProofDeserialize::MerkleCap) -> Bytes::Stream {
      let &Lists::Node::Cons(d, cap_rest) = cap;
      let Lists::Node::Nil = (*(cap_rest));
      Lists::concat(input, digest_onto((*(d)), (&(Lists::Node::Nil))))
    }

  fn accs_onto(accs: Lists::List<ProofDeserialize::Ext>, tail: Bytes::Stream) -> Bytes::Stream {
      match (*(accs)) {
        Lists::Node::Nil => {  tail } ,
        Lists::Node::Cons(e, rest) => {  b8_onto(Goldilocks::gl_to_bytes(e[0]), b8_onto(Goldilocks::gl_to_bytes(e[1]), accs_onto(rest, tail))) } ,
      }
    }

  inline fn seed_tag_onto(tail: Bytes::Stream) -> Bytes::Stream {
      (&(Lists::Node::Cons(UInt8::BYTE_109, (&(Lists::Node::Cons(UInt8::BYTE_117, (&(Lists::Node::Cons(UInt8::BYTE_108,
      (&(Lists::Node::Cons(UInt8::BYTE_116, (&(Lists::Node::Cons(UInt8::BYTE_105, (&(Lists::Node::Cons(UInt8::BYTE_45,
      (&(Lists::Node::Cons(UInt8::BYTE_115, (&(Lists::Node::Cons(UInt8::BYTE_116, (&(Lists::Node::Cons(UInt8::BYTE_97,
      (&(Lists::Node::Cons(UInt8::BYTE_114, (&(Lists::Node::Cons(UInt8::BYTE_107, (&(Lists::Node::Cons(UInt8::BYTE_47,
      (&(Lists::Node::Cons(UInt8::BYTE_118, (&(Lists::Node::Cons(UInt8::BYTE_48,
      tail))))))))))))))))))))))))))))))))))))))))))
    }

  fn limbs_onto(ls: Lists::List<UInt64::U64>, tail: Bytes::Stream) -> Bytes::Stream {
      match (*(ls)) {
        Lists::Node::Nil => {  tail } ,
        Lists::Node::Cons(l, rest) => {  b8_onto(l, limbs_onto(rest, tail)) } ,
      }
    }

  inline fn opt_commit_cap(commit: SystemDeserialize::OptCommit) -> ProofDeserialize::MerkleCap {
      match commit {
        SystemDeserialize::OptCommit::NoCommit => {  (&(Lists::Node::Nil)) } ,
        SystemDeserialize::OptCommit::SomeCommit(c) => {  c } ,
      }
    }

  fn active_onto(active: Lists::List<Field>, tail: Bytes::Stream) -> Bytes::Stream {
      match (*(active)) {
        Lists::Node::Nil => {  tail } ,
        Lists::Node::Cons(b, rest) => {
          b8_onto([UInt8::from_field(b), UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0],
                  active_onto(rest, tail)) } ,
      }
    }

  fn ext_exp_pow2(e: ProofDeserialize::Ext, k: Field) -> ProofDeserialize::Ext {
      match k {
        0 => {  e } ,
        _ => {  ext_exp_pow2(Goldilocks::eg_mul(e, e), k - 1) } ,
      }
    }

  fn two_adic_gen(bits: Field) -> Goldilocks::Goldilocks {
      match bits {
        0  => {  1 } ,
        32 => {  1753635133440165772 } ,
        _  => {
          let g = two_adic_gen(bits + 1);
          g * g } ,
      }
    }

  inline fn trace_vanishing(zeta: ProofDeserialize::Ext, l: Field) -> ProofDeserialize::Ext {
      Goldilocks::eg_sub(ext_exp_pow2(zeta, l), [1, 0])
    }

  fn pow2(l: Field) -> Field {
      match l {
        0 => {  1 } ,
        _ => {  2 * pow2(l - 1) } ,
      }
    }

  inline fn trace_selectors(zeta: ProofDeserialize::Ext, l: Field) -> (ProofDeserialize::Ext, ProofDeserialize::Ext, ProofDeserialize::Ext, ProofDeserialize::Ext, Goldilocks::Goldilocks, ProofDeserialize::Ext) {
      let zeta_pow_n = ext_exp_pow2(zeta, l);
      let zh = Goldilocks::eg_sub(zeta_pow_n, [1, 0]);
      let g = two_adic_gen(l);
      let ginv = Goldilocks::gl_inv_nonzero(g);
      let is_first = Goldilocks::eg_div_nonzero(zh, Goldilocks::eg_sub(zeta, [1, 0]));
      let is_last = Goldilocks::eg_div_nonzero(zh, Goldilocks::eg_sub(zeta, [ginv, 0]));
      let is_trans = Goldilocks::eg_sub(zeta, [ginv, 0]);
      let inv_van = Goldilocks::eg_inv_nonzero(zh);
      (is_first, is_last, is_trans, inv_van, g, zeta_pow_n)
    }

  fn ood_fold(acc: ProofDeserialize::Ext, alpha: ProofDeserialize::Ext, x: ProofDeserialize::Ext) -> ProofDeserialize::Ext {
      Goldilocks::eg_add(Goldilocks::eg_mul(acc, alpha), x)
    }

  fn from_ext_basis(c0: ProofDeserialize::Ext, c1: ProofDeserialize::Ext) -> ProofDeserialize::Ext {
      Goldilocks::eg_add(c0, Goldilocks::eg_mul(c1, [0, 1]))
    }

  fn reconstruct_ext_row(raw: Lists::List<ProofDeserialize::Ext>) -> Lists::List<ProofDeserialize::Ext> {
      match (*(raw)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(c0, t1) => {
          let Lists::Node::Cons(c1, t2) = (*(t1));
          (&(Lists::Node::Cons(from_ext_basis(c0, c1), reconstruct_ext_row(t2)))) } ,
      }
    }

  fn eval_at(nodes: Lists::List<SystemDeserialize::SysNode>, i: Field,
        main: Lists::List<ProofDeserialize::Ext>, main_next: Lists::List<ProofDeserialize::Ext>, prep: Lists::List<ProofDeserialize::Ext>, prep_next: Lists::List<ProofDeserialize::Ext>,
        s2: Lists::List<ProofDeserialize::Ext>, s2next: Lists::List<ProofDeserialize::Ext>, publics: Lists::List<ProofDeserialize::Ext>,
        isf: ProofDeserialize::Ext, isl: ProofDeserialize::Ext, ist: ProofDeserialize::Ext) -> ProofDeserialize::Ext {
      let nd = Lists::lookup(nodes, i);
      match nd {
        SystemDeserialize::SysNode::Const(c) => {  [c, 0] } ,
        SystemDeserialize::SysNode::Var(src, off, idx) => {

          let sel = src + src + off;
          match sel {
            0 => {  Lists::lookup(prep, idx) } ,
            1 => {  Lists::lookup(prep_next, idx) } ,
            2 => {  Lists::lookup(main, idx) } ,
            3 => {  Lists::lookup(main_next, idx) } ,
            4 => {  Lists::lookup(s2, idx) } ,
            _ => {  Lists::lookup(s2next, idx) } ,
          } } ,
        SystemDeserialize::SysNode::Public(idx) => {  Lists::lookup(publics, idx) } ,
        SystemDeserialize::SysNode::IsFirstRow => {  isf } ,
        SystemDeserialize::SysNode::IsLastRow => {  isl } ,
        SystemDeserialize::SysNode::IsTransition => {  ist } ,
        SystemDeserialize::SysNode::Add(a, b) => {
          Goldilocks::eg_add(eval_at(nodes, a, main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist),
                 eval_at(nodes, b, main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist)) } ,
        SystemDeserialize::SysNode::Sub(a, b) => {
          Goldilocks::eg_sub(eval_at(nodes, a, main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist),
                 eval_at(nodes, b, main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist)) } ,
        SystemDeserialize::SysNode::Mul(a, b) => {
          Goldilocks::eg_mul(eval_at(nodes, a, main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist),
                 eval_at(nodes, b, main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist)) } ,
        SystemDeserialize::SysNode::Neg(a) => {
          Goldilocks::eg_neg(eval_at(nodes, a, main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist)) } ,
      }
    }

  fn fold_roots(acc: ProofDeserialize::Ext, alpha: ProofDeserialize::Ext, zeros: Lists::List<Field>, nodes: Lists::List<SystemDeserialize::SysNode>,
        main: Lists::List<ProofDeserialize::Ext>, main_next: Lists::List<ProofDeserialize::Ext>, prep: Lists::List<ProofDeserialize::Ext>, prep_next: Lists::List<ProofDeserialize::Ext>,
        s2: Lists::List<ProofDeserialize::Ext>, s2next: Lists::List<ProofDeserialize::Ext>, publics: Lists::List<ProofDeserialize::Ext>,
        isf: ProofDeserialize::Ext, isl: ProofDeserialize::Ext, ist: ProofDeserialize::Ext) -> ProofDeserialize::Ext {
      match (*(zeros)) {
        Lists::Node::Nil => {  acc } ,
        Lists::Node::Cons(z, rest) => {
          let v = eval_at(nodes, z, main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist);
          fold_roots(ood_fold(acc, alpha, v), alpha, rest, nodes,
                     main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist) } ,
      }
    }

  fn pair_mul(a0: ProofDeserialize::Ext, a1: ProofDeserialize::Ext, b0: ProofDeserialize::Ext, b1: ProofDeserialize::Ext) -> (ProofDeserialize::Ext, ProofDeserialize::Ext) {
      (Goldilocks::eg_add(Goldilocks::eg_mul(a0, b0), Goldilocks::eg_mul([7, 0], Goldilocks::eg_mul(a1, b1))),
       Goldilocks::eg_add(Goldilocks::eg_mul(a0, b1), Goldilocks::eg_mul(a1, b0)))
    }

  fn logup_fingerprint(args: Lists::List<Field>, g0: ProofDeserialize::Ext, g1: ProofDeserialize::Ext, nodes: Lists::List<SystemDeserialize::SysNode>,
        main: Lists::List<ProofDeserialize::Ext>, main_next: Lists::List<ProofDeserialize::Ext>, prep: Lists::List<ProofDeserialize::Ext>, prep_next: Lists::List<ProofDeserialize::Ext>,
        s2: Lists::List<ProofDeserialize::Ext>, s2next: Lists::List<ProofDeserialize::Ext>, publics: Lists::List<ProofDeserialize::Ext>,
        isf: ProofDeserialize::Ext, isl: ProofDeserialize::Ext, ist: ProofDeserialize::Ext) -> (ProofDeserialize::Ext, ProofDeserialize::Ext) {
      match (*(args)) {
        Lists::Node::Nil => {  ([0, 0], [0, 0]) } ,
        Lists::Node::Cons(a, rest) => {
          let (f0, f1) = logup_fingerprint(rest, g0, g1, nodes,
            main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist);
          let (m0, m1) = pair_mul(f0, f1, g0, g1);
          let av = eval_at(nodes, a, main, main_next, prep, prep_next, s2, s2next,
                           publics, isf, isl, ist);
          (Goldilocks::eg_add(m0, av), m1) } ,
      }
    }

  fn logup_steps_fold(acc: ProofDeserialize::Ext, alpha: ProofDeserialize::Ext, lks: Lists::List<SystemDeserialize::SysLookup>, j: Field, lcount: Field,
        g: Field, rem: Field, k: Field, p0: ProofDeserialize::Ext, p1: ProofDeserialize::Ext, r0: ProofDeserialize::Ext, r1: ProofDeserialize::Ext,
        inj0: ProofDeserialize::Ext, inj1: ProofDeserialize::Ext, b0: ProofDeserialize::Ext, b1: ProofDeserialize::Ext, g0: ProofDeserialize::Ext, g1: ProofDeserialize::Ext,
        nodes: Lists::List<SystemDeserialize::SysNode>,
        main: Lists::List<ProofDeserialize::Ext>, main_next: Lists::List<ProofDeserialize::Ext>, prep: Lists::List<ProofDeserialize::Ext>, prep_next: Lists::List<ProofDeserialize::Ext>,
        s2: Lists::List<ProofDeserialize::Ext>, s2next: Lists::List<ProofDeserialize::Ext>, publics: Lists::List<ProofDeserialize::Ext>,
        isf: ProofDeserialize::Ext, isl: ProofDeserialize::Ext, ist: ProofDeserialize::Ext) -> ProofDeserialize::Ext {
      match (*(lks)) {
        Lists::Node::Nil => {  acc } ,
        Lists::Node::Cons(lk, rest) => {
          let SystemDeserialize::SysLookup::Mk(mid, args) = lk;
          let (f0, f1) = logup_fingerprint(args, g0, g1, nodes,
            main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist);
          let m0 = Goldilocks::eg_add(f0, b0);
          let m1 = Goldilocks::eg_add(f1, b1);
          let mv = eval_at(nodes, mid, main, main_next, prep, prep_next, s2, s2next,
                           publics, isf, isl, ist);

          let (rm0, rm1) = pair_mul(r0, r1, m0, m1);
          let nr0 = Goldilocks::eg_add(rm0, Goldilocks::eg_mul(mv, p0));
          let nr1 = Goldilocks::eg_add(rm1, Goldilocks::eg_mul(mv, p1));
          let (np0, np1) = pair_mul(p0, p1, m0, m1);
          match (j + 1 - lcount) {
            0 => {

              let s0 = Lists::lookup(s2, g + g);
              let s1 = Lists::lookup(s2, g + g + 1);
              let t0 = Goldilocks::eg_add(Lists::lookup(s2next, 0), inj0);
              let t1 = Goldilocks::eg_add(Lists::lookup(s2next, 1), inj1);
              let (c0, c1) = pair_mul(np0, np1, Goldilocks::eg_sub(t0, s0), Goldilocks::eg_sub(t1, s1));
              ood_fold(ood_fold(acc, alpha, Goldilocks::eg_sub(c0, nr0)), alpha, Goldilocks::eg_sub(c1, nr1)) } ,
            _ => {  match rem - 1 {
              0 => {

                let s0 = Lists::lookup(s2, g + g);
                let s1 = Lists::lookup(s2, g + g + 1);
                let t0 = Lists::lookup(s2, g + g + 2);
                let t1 = Lists::lookup(s2, g + g + 3);
                let (c0, c1) = pair_mul(np0, np1, Goldilocks::eg_sub(t0, s0), Goldilocks::eg_sub(t1, s1));
                let acc1 = ood_fold(ood_fold(acc, alpha, Goldilocks::eg_sub(c0, nr0)), alpha,
                                    Goldilocks::eg_sub(c1, nr1));
                logup_steps_fold(acc1, alpha, rest, j + 1, lcount,
                  g + 1, k, k, [1, 0], [0, 0], [0, 0], [0, 0],
                  inj0, inj1, b0, b1, g0, g1, nodes,
                  main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist) } ,
              _ => {

                logup_steps_fold(acc, alpha, rest, j + 1, lcount,
                  g, rem - 1, k, np0, np1, nr0, nr1,
                  inj0, inj1, b0, b1, g0, g1, nodes,
                  main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist) } ,
            } } ,
          } } ,
      }
    }

  inline fn ood_composition(nodes: Lists::List<SystemDeserialize::SysNode>, zeros: Lists::List<Field>, lks: Lists::List<SystemDeserialize::SysLookup>,
        k: Field,
        main: Lists::List<ProofDeserialize::Ext>, main_next: Lists::List<ProofDeserialize::Ext>, prep: Lists::List<ProofDeserialize::Ext>, prep_next: Lists::List<ProofDeserialize::Ext>,
        s2: Lists::List<ProofDeserialize::Ext>, s2next: Lists::List<ProofDeserialize::Ext>, publics: Lists::List<ProofDeserialize::Ext>,
        lch: ProofDeserialize::Ext, fch: ProofDeserialize::Ext, accp: ProofDeserialize::Ext, naccp: ProofDeserialize::Ext,
        isf: ProofDeserialize::Ext, isl: ProofDeserialize::Ext, ist: ProofDeserialize::Ext, alpha: ProofDeserialize::Ext, inorm: Field) -> ProofDeserialize::Ext {
      let base = fold_roots([0, 0], alpha, zeros, nodes,
                 main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist);

      let b0 = [lch[0], 0]; let b1 = [lch[1], 0];
      let g0 = [fch[0], 0]; let g1 = [fch[1], 0];
      let a0 = [accp[0], 0]; let a1 = [accp[1], 0];
      let na0 = [naccp[0], 0]; let na1 = [naccp[1], 0];

      let inj0 = Goldilocks::eg_mul(isl, Goldilocks::eg_mul(Goldilocks::eg_sub(na0, a0), [inorm, 0]));
      let inj1 = Goldilocks::eg_mul(isl, Goldilocks::eg_mul(Goldilocks::eg_sub(na1, a1), [inorm, 0]));
      match (*(lks)) {

        Lists::Node::Nil => {
          let acc = ood_fold(base, alpha,
            Goldilocks::eg_add(Goldilocks::eg_sub(Lists::lookup(s2next, 0), Lists::lookup(s2, 0)), inj0));
          ood_fold(acc, alpha,
            Goldilocks::eg_add(Goldilocks::eg_sub(Lists::lookup(s2next, 1), Lists::lookup(s2, 1)), inj1)) } ,
        Lists::Node::Cons(_h, _t) => {
          logup_steps_fold(base, alpha, lks, 0, Lists::length(lks),
            0, k, k, [1, 0], [0, 0], [0, 0], [0, 0], inj0, inj1,
            b0, b1, g0, g1, nodes,
            main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist) } ,
      }
    }

  inline fn build_publics(lch: ProofDeserialize::Ext, fch: ProofDeserialize::Ext, accp: ProofDeserialize::Ext, naccp: ProofDeserialize::Ext) -> Lists::List<ProofDeserialize::Ext> {
      (&(Lists::Node::Cons([lch[0], 0], (&(Lists::Node::Cons([lch[1], 0],
      (&(Lists::Node::Cons([fch[0], 0], (&(Lists::Node::Cons([fch[1], 0],
      (&(Lists::Node::Cons([accp[0], 0], (&(Lists::Node::Cons([accp[1], 0],
      (&(Lists::Node::Cons([naccp[0], 0], (&(Lists::Node::Cons([naccp[1], 0],
      (&(Lists::Node::Nil))))))))))))))))))))))))))
    }

  fn quotient_eval(slices: Lists::List<ProofDeserialize::Ext>, zeta_pow_n: ProofDeserialize::Ext, pow: ProofDeserialize::Ext) -> ProofDeserialize::Ext {
      match (*(slices)) {
        Lists::Node::Nil => {  [0, 0] } ,
        Lists::Node::Cons(c, rest) => {
          Goldilocks::eg_add(Goldilocks::eg_mul(pow, c), quotient_eval(rest, zeta_pow_n, Goldilocks::eg_mul(pow, zeta_pow_n))) } ,
      }
    }

  fn quotient_degree_of(md: Field) -> Field {
      match md {
        0 => {  1 } , 1 => {  1 } , 2 => {  1 } ,
        3 => {  2 } ,
        4 => {  4 } , 5 => {  4 } ,
        6 => {  8 } , 7 => {  8 } , 8 => {  8 } , 9 => {  8 } ,
        10 => {  16 } , 11 => {  16 } , 12 => {  16 } , 13 => {  16 } , 14 => {  16 } , 15 => {  16 } , 16 => {  16 } , 17 => {  16 } ,
        _ => {  32 } ,
      }
    }

  inline fn ood_prep_rows(prep_opt: ProofDeserialize::PreprocessedOpt, oi: SystemDeserialize::OptIdx)
        -> (Lists::List<ProofDeserialize::Ext>, Lists::List<ProofDeserialize::Ext>, ProofDeserialize::PreprocessedOpt) {
      match oi {
        SystemDeserialize::OptIdx::NoIdx => {  ((&(Lists::Node::Nil)), (&(Lists::Node::Nil)), prep_opt) } ,
        SystemDeserialize::OptIdx::SomeIdx(_j) => {
          match prep_opt {
            ProofDeserialize::PreprocessedOpt::NoPreprocessed => {  ((&(Lists::Node::Nil)), (&(Lists::Node::Nil)), prep_opt) } ,
            ProofDeserialize::PreprocessedOpt::SomePreprocessed(round) => {
              let &Lists::Node::Cons(pr, round_rest) = round;
              let &Lists::Node::Cons(p0, pr1) = pr;
              let &Lists::Node::Cons(p1, pr2) = pr1;
              let Lists::Node::Nil = (*(pr2));
              (p0, p1, ProofDeserialize::PreprocessedOpt::SomePreprocessed(round_rest)) } ,
          } } ,
      }
    }

  fn ood_loop(circuits: Lists::List<SystemDeserialize::SysCircuit>, prep_indices: Lists::List<SystemDeserialize::OptIdx>,
        log_degrees: Lists::List<UInt8::U8>, accs: Lists::List<ProofDeserialize::Ext>,
        stage1: ProofDeserialize::OpenedRound, stage2: ProofDeserialize::OpenedRound, prep_opt: ProofDeserialize::PreprocessedOpt,
        q_opened: ProofDeserialize::OpenedRound, accp: ProofDeserialize::Ext,
        lch: ProofDeserialize::Ext, fch: ProofDeserialize::Ext, alpha: ProofDeserialize::Ext, zeta: ProofDeserialize::Ext) -> Field {
      match (*(circuits)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(prep_indices));
          let Lists::Node::Nil = (*(log_degrees));
          let Lists::Node::Nil = (*(accs));
          let Lists::Node::Nil = (*(stage1));
          let Lists::Node::Nil = (*(stage2));
          let Lists::Node::Nil = (*(q_opened));
          let _prep_done = match prep_opt {
            ProofDeserialize::PreprocessedOpt::NoPreprocessed => {  1 } ,
            ProofDeserialize::PreprocessedOpt::SomePreprocessed(rem) => {
              let Lists::Node::Nil = (*(rem));
              1 } ,
          };
          1 } ,
        Lists::Node::Cons(circ, rest) => {
          let SystemDeserialize::SysCircuit::Mk(nodes, _node_count, zeros, md, lks, k, mw, pw, ph, s2w) = circ;
          let &Lists::Node::Cons(pi, pi_rest) = prep_indices;
          let &Lists::Node::Cons(ld8, ld_rest) = log_degrees;
          assert_eq!(UInt8::less_than(ld8, UInt8::BYTE_32), 1);
          let l = UInt8::to_field(ld8);
          let qd = quotient_degree_of(md);
          let &Lists::Node::Cons(naccp, acc_rest) = accs;
          let &Lists::Node::Cons(s1, s1_rest) = stage1;
          let &Lists::Node::Cons(main, s1_1) = s1;
          let &Lists::Node::Cons(main_next, s1_2) = s1_1;
          let Lists::Node::Nil = (*(s1_2));
          let &Lists::Node::Cons(s2, s2_rest) = stage2;
          let &Lists::Node::Cons(s2row, s2_1) = s2;
          let &Lists::Node::Cons(s2next, s2_2) = s2_1;
          let Lists::Node::Nil = (*(s2_2));
          let (prep, prep_next, prep_opt2) = ood_prep_rows(prep_opt, pi);

          assert_eq!(Fields::is_zero(Lists::length(main) - mw), 1);
          assert_eq!(Fields::is_zero(Lists::length(main_next) - mw), 1);
          assert_eq!(Fields::is_zero(Lists::length(s2row) - s2w), 1);
          assert_eq!(Fields::is_zero(Lists::length(s2next) - s2w), 1);
          assert_eq!(Fields::is_zero(Lists::length(prep) - pw), 1);
          assert_eq!(Fields::is_zero(Lists::length(prep_next) - pw), 1);
          let (isf, isl, ist, invv, g, zeta_pow_n) = trace_selectors(zeta, l);
          let publics = build_publics(lch, fch, accp, naccp);
          let height = pow2(l);
          assert_eq!((1 - Fields::is_zero(ph)) * (height - ph), 0);
          let inorm = Goldilocks::gl_inv_nonzero(height * g);
          let comp = ood_composition(nodes, zeros, lks, k,
                                     main, main_next, prep, prep_next, s2row, s2next,
                                     publics, lch, fch, accp, naccp,
                                     isf, isl, ist, alpha, inorm);

          let &Lists::Node::Cons(qmat, q_rest) = q_opened;
          let &Lists::Node::Cons(qrow, qmat_rest) = qmat;
          let Lists::Node::Nil = (*(qmat_rest));
          let slices = reconstruct_ext_row(qrow);
          assert_eq!(Fields::is_zero(Lists::length(slices) - qd), 1);
          let quot = quotient_eval(slices, zeta_pow_n, [1, 0]);
          assert_eq!(Goldilocks::eg_eq(Goldilocks::eg_mul(comp, invv), quot), 1);
          ood_loop(rest, pi_rest, ld_rest, acc_rest, s1_rest, s2_rest, prep_opt2,
                   q_rest, naccp, lch, fch, alpha, zeta) } ,
      }
    }

  fn fingerprint_vals(fch: ProofDeserialize::Ext, vals: Lists::List<UInt64::U64>) -> ProofDeserialize::Ext {
      match (*(vals)) {
        Lists::Node::Nil => {  [0, 0] } ,
        Lists::Node::Cons(v, rest) => {
          assert_eq!(Goldilocks::gl_lt_p(v), 1);
          Goldilocks::eg_add([Goldilocks::gl_val(v), 0], Goldilocks::eg_mul(fch, fingerprint_vals(fch, rest))) } ,
      }
    }

  fn claims_acc(acc: ProofDeserialize::Ext, claims: Lists::List<Lists::List<UInt64::U64>>, lch: ProofDeserialize::Ext, fch: ProofDeserialize::Ext) -> ProofDeserialize::Ext {
      match (*(claims)) {
        Lists::Node::Nil => {  acc } ,
        Lists::Node::Cons(c, rest) => {
          let msg = Goldilocks::eg_add(lch, fingerprint_vals(fch, c));
          claims_acc(Goldilocks::eg_add(acc, Goldilocks::eg_inv_nonzero(msg)), rest, lch, fch) } ,
      }
    }

  fn assert_bits(l: Lists::List<Field>) -> Field {
      match (*(l)) {
        Lists::Node::Nil => {  1 } ,
        Lists::Node::Cons(b, rest) => {
          assert_eq!(b * (b - 1), 0);
          assert_bits(rest) } ,
      }
    }

  fn select_active_circuits(circuits: Lists::List<SystemDeserialize::SysCircuit>, active: Lists::List<Field>) -> Lists::List<SystemDeserialize::SysCircuit> {
      match (*(circuits)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(c, crest) => {
          let &Lists::Node::Cons(b, arest) = active;
          match b {
            0 => {
              let SystemDeserialize::SysCircuit::Mk(_nodes, _node_count, _zeros, _md, _lks, _k, _mw, _pw, ph, _s2w) = c;
              assert_eq!(ph, 0);
              select_active_circuits(crest, arest) } ,
            _ => {  (&(Lists::Node::Cons(c, select_active_circuits(crest, arest)))) } ,
          } } ,
      }
    }

  fn select_active_prep(prep_indices: Lists::List<SystemDeserialize::OptIdx>, active: Lists::List<Field>) -> Lists::List<SystemDeserialize::OptIdx> {
      match (*(prep_indices)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(p, prest) => {
          let &Lists::Node::Cons(b, arest) = active;
          match b {
            0 => {
              let SystemDeserialize::OptIdx::NoIdx = p;
              select_active_prep(prest, arest) } ,
            _ => {  (&(Lists::Node::Cons(p, select_active_prep(prest, arest)))) } ,
          } } ,
      }
    }

  fn count_onto(n: Field, tail: Bytes::Stream) -> Bytes::Stream {
      b8_onto(Goldilocks::gl_to_bytes(n), tail)
    }

  fn claims_onto(claims: Lists::List<Lists::List<UInt64::U64>>, tail: Bytes::Stream) -> Bytes::Stream {
      count_onto(Lists::length(claims), claims_onto_each(claims, tail))
    }

  fn claims_onto_each(claims: Lists::List<Lists::List<UInt64::U64>>, tail: Bytes::Stream) -> Bytes::Stream {
      match (*(claims)) {
        Lists::Node::Nil => {  tail } ,
        Lists::Node::Cons(c, rest) => {
          count_onto(Lists::length(c), limbs_onto(c, claims_onto_each(rest, tail))) } ,
      }
    }

  fn header_onto(h: ProofDeserialize::ShardHeader, tail: Bytes::Stream) -> Bytes::Stream {
      let ProofDeserialize::ShardHeader::Mk(active, cap, lds, claims) = h;
      let &Lists::Node::Cons(d, cap_rest) = cap;
      let Lists::Node::Nil = (*(cap_rest));
      active_onto(active,
        digest_onto((*(d)),
          count_onto(Lists::length(lds),
            log_degrees_onto(lds, claims_onto(claims, tail)))))
    }

  fn headers_onto(hs: Lists::List<ProofDeserialize::ShardHeader>, tail: Bytes::Stream) -> Bytes::Stream {
      match (*(hs)) {
        Lists::Node::Nil => {  tail } ,
        Lists::Node::Cons(h, rest) => {  header_onto(h, headers_onto(rest, tail)) } ,
      }
    }

  fn messages_onto(ms: Lists::List<ProofDeserialize::BatchMessage>, tail: Bytes::Stream) -> Bytes::Stream {
      count_onto(Lists::length(ms), messages_onto_each(ms, tail))
    }

  fn messages_onto_each(ms: Lists::List<ProofDeserialize::BatchMessage>, tail: Bytes::Stream) -> Bytes::Stream {
      match (*(ms)) {
        Lists::Node::Nil => {  tail } ,
        Lists::Node::Cons(m, rest) => {
          let ProofDeserialize::BatchMessage::Mk(args, mult) = m;
          count_onto(Lists::length(args),
            limbs_onto(args, b8_onto(mult, messages_onto_each(rest, tail)))) } ,
      }
    }

  fn assert_same_bits(a: Lists::List<Field>, b: Lists::List<Field>) -> Field {
      match (*(a)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(b));
          1 } ,
        Lists::Node::Cons(x, ra) => {
          let Lists::Node::Cons(y, rb) = (*(b));
          assert_eq!(x, y);
          assert_same_bits(ra, rb) } ,
      }
    }

  fn assert_same_u8s(a: Lists::List<UInt8::U8>, b: Lists::List<UInt8::U8>) -> Field {
      match (*(a)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(b));
          1 } ,
        Lists::Node::Cons(x, ra) => {
          let Lists::Node::Cons(y, rb) = (*(b));
          assert_eq!(UInt8::to_field(x), UInt8::to_field(y));
          assert_same_u8s(ra, rb) } ,
      }
    }

  fn assert_same_limbs(a: Lists::List<UInt64::U64>, b: Lists::List<UInt64::U64>) -> Field {
      match (*(a)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(b));
          1 } ,
        Lists::Node::Cons(x, ra) => {
          let Lists::Node::Cons(y, rb) = (*(b));
          assert_eq!(UInt64::eq(x, y), 1);
          assert_same_limbs(ra, rb) } ,
      }
    }

  fn assert_same_claims(a: Lists::List<Lists::List<UInt64::U64>>, b: Lists::List<Lists::List<UInt64::U64>>) -> Field {
      match (*(a)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(b));
          1 } ,
        Lists::Node::Cons(x, ra) => {
          let Lists::Node::Cons(y, rb) = (*(b));
          assert_eq!(assert_same_limbs(x, y), 1);
          assert_same_claims(ra, rb) } ,
      }
    }

  fn assert_same_cap(a: ProofDeserialize::MerkleCap, b: ProofDeserialize::MerkleCap) -> Field {
      match (*(a)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(b));
          1 } ,
        Lists::Node::Cons(d, ra) => {
          let Lists::Node::Cons(e, rb) = (*(b));
          let x = (*(d));
          let y = (*(e));
          assert_eq!(UInt64::eq(x[0], y[0]), 1);
          assert_eq!(UInt64::eq(x[1], y[1]), 1);
          assert_eq!(UInt64::eq(x[2], y[2]), 1);
          assert_eq!(UInt64::eq(x[3], y[3]), 1);
          assert_same_cap(ra, rb) } ,
      }
    }

  fn last_acc(accs: Lists::List<ProofDeserialize::Ext>) -> ProofDeserialize::Ext {
      let Lists::Node::Cons(e, rest) = (*(accs));
      match (*(rest)) {
        Lists::Node::Nil => {  e } ,
        _ => {  last_acc(rest) } ,
      }
    }

  fn messages_acc(acc: ProofDeserialize::Ext, ms: Lists::List<ProofDeserialize::BatchMessage>, lch: ProofDeserialize::Ext, fch: ProofDeserialize::Ext) -> ProofDeserialize::Ext {
      match (*(ms)) {
        Lists::Node::Nil => {  acc } ,
        Lists::Node::Cons(m, rest) => {
          let ProofDeserialize::BatchMessage::Mk(args, mult) = m;
          let msg = Goldilocks::eg_add(lch, fingerprint_vals(fch, args));
          let term = Goldilocks::eg_mul(Goldilocks::eg_inv_nonzero(msg), [Goldilocks::gl_val(mult), 0]);
          messages_acc(Goldilocks::eg_add(acc, term), rest, lch, fch) } ,
      }
    }

  fn log_degree_ok(ld: UInt8::U8) -> Field {
      match UInt8::to_field(ld) {
        0 => {  1 } , 1 => {  1 } , 2 => {  1 } , 3 => {  1 } , 4 => {  1 } , 5 => {  1 } , 6 => {  1 } , 7 => {  1 } , 8 => {  1 } ,
        9 => {  1 } , 10 => {  1 } , 11 => {  1 } , 12 => {  1 } , 13 => {  1 } , 14 => {  1 } , 15 => {  1 } , 16 => {  1 } ,
        17 => {  1 } , 18 => {  1 } , 19 => {  1 } , 20 => {  1 } , 21 => {  1 } , 22 => {  1 } , 23 => {  1 } , 24 => {  1 } ,
        25 => {  1 } , 26 => {  1 } , 27 => {  1 } , 28 => {  1 } , 29 => {  1 } , 30 => {  1 } , 31 => {  1 } , 32 => {  1 } ,
        _ => {  0 } ,
      }
    }

  fn assert_log_degrees_ok(lds: Lists::List<UInt8::U8>) -> Field {
      match (*(lds)) {
        Lists::Node::Nil => {  1 } ,
        Lists::Node::Cons(ld, rest) => {
          assert_eq!(log_degree_ok(ld), 1);
          assert_log_degrees_ok(rest) } ,
      }
    }

  fn count_ones(bits: Lists::List<Field>) -> Field {
      match (*(bits)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(b, rest) => {  b + count_ones(rest) } ,
      }
    }

  fn assert_shard_count_ok(k: Field) -> Field {
      assert_eq!(Fields::is_zero(k), 0);
      let b = Goldilocks::gl_to_bytes(k);
      assert_eq!(UInt8::to_field(b[3]) + UInt8::to_field(b[4]) + UInt8::to_field(b[5]) + UInt8::to_field(b[6]) + UInt8::to_field(b[7]), 0);
      let hi = UInt8::to_field(b[2]);
      assert_eq!(hi * (hi - 1), 0);
      assert_eq!(hi * (UInt8::to_field(b[0]) + UInt8::to_field(b[1])), 0);
      1
    }

  -- `n <= 2^39` for a canonical `n`.
  fn at_most_row_bound(n: Field) -> Field {
      let b = Goldilocks::gl_to_bytes(n);
      let high = UInt8::to_field(b[5]) + UInt8::to_field(b[6]) + UInt8::to_field(b[7]);
      Fields::is_zero(high) * (UInt8::less_than(b[4], UInt8::BYTE_128) + Fields::is_zero(n - 549755813888))
    }

  -- Lanes packed per row under `C6` vectorized ROM (`rom_lanes(w)`).
  fn rom_lanes_of(w: Field) -> Field {
      match w {
        0 => {  8 } , 1 => {  8 } , 2 => {  8 } , 3 => {  8 } , 4 => {  8 } ,
        5 => {  4 } , 6 => {  4 } , 7 => {  4 } , 8 => {  4 } ,
        9 => {  4 } , 10 => {  4 } , 11 => {  4 } , 12 => {  4 } ,
        _ => {  1 } ,
      }
    }

  fn node_const_opt(nodes: Lists::List<SystemDeserialize::SysNode>, id: Field) -> (Field, Field) {
      match Lists::lookup(nodes, id) {
        SystemDeserialize::SysNode::Const(c) => {  (1, c) } ,
        _ => {  (0, 0) } ,
      }
    }

  fn lookup_memseg_width(nodes: Lists::List<SystemDeserialize::SysNode>, lk: SystemDeserialize::SysLookup) -> (Field, Field) {
      let SystemDeserialize::SysLookup::Mk(_mid, args) = lk;
      match (*(args)) {
        Lists::Node::Cons(a0, r1) => {
          match (*(r1)) {
            Lists::Node::Cons(a1, r2) => {
              match (*(r2)) {
                Lists::Node::Cons(_a2, r3) => {
                  match (*(r3)) {
                    Lists::Node::Nil => {
                      let (is_c0, c0) = node_const_opt(nodes, a0);
                      let (is_c1, w) = node_const_opt(nodes, a1);
                      let ok = is_c0 * is_c1 * Fields::is_zero(c0 - 16);
                      (ok, ok * w) } ,
                    _ => {  (0, 0) } ,
                  } } ,
                _ => {  (0, 0) } ,
              } } ,
            _ => {  (0, 0) } ,
          } } ,
        _ => {  (0, 0) } ,
      }
    }

  fn circuit_memseg_width(nodes: Lists::List<SystemDeserialize::SysNode>, lks: Lists::List<SystemDeserialize::SysLookup>) -> (Field, Field) {
      match (*(lks)) {
        Lists::Node::Nil => {  (0, 0) } ,
        Lists::Node::Cons(lk, rest) => {
          let (found, w) = lookup_memseg_width(nodes, lk);
          match found {
            1 => {  (1, w) } ,
            _ => {  circuit_memseg_width(nodes, rest) } ,
          } } ,
      }
    }

  fn circuit_row_weights(circuits: Lists::List<SystemDeserialize::SysCircuit>) -> Lists::List<Field> {
      match (*(circuits)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(circ, rest) => {
          let SystemDeserialize::SysCircuit::Mk(nodes, _nc, _zeros, _md, lks, _k, mw, _pw, _ph, _s2w) = circ;
          let (found, w) = circuit_memseg_width(nodes, lks);
          let wt = match found {
            0 => {  1 } ,
            _ => {
              let k = rom_lanes_of(w);
              match Fields::is_zero(mw - (1 + k * (w + 2))) {
                1 => {  k } ,
                _ => {  1 } ,
              } } ,
          };
          (&(Lists::Node::Cons(wt, circuit_row_weights(rest)))) } ,
      }
    }

  fn field_in_list(xs: Lists::List<Field>, target: Field) -> Field {
      match (*(xs)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(x, rest) => {
          match Fields::is_zero(x - target) {
            1 => {  1 } ,
            _ => {  field_in_list(rest, target) } ,
          } } ,
      }
    }

  fn system_rom_widths(circuits: Lists::List<SystemDeserialize::SysCircuit>) -> Lists::List<Field> {
      match (*(circuits)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(circ, rest) => {
          let SystemDeserialize::SysCircuit::Mk(nodes, _nc, _zeros, _md, lks, _k, _mw, _pw, _ph, _s2w) = circ;
          let (found, w) = circuit_memseg_width(nodes, lks);
          let tail = system_rom_widths(rest);
          match found {
            1 => {
              match field_in_list(tail, w) {
                1 => {  tail } ,
                _ => {  (&(Lists::Node::Cons(w, tail))) } ,
              } } ,
            _ => {  tail } ,
          } } ,
      }
    }

  -- A shard's logical rows: `weight(c) * 2^ld` summed over its active circuits,
  -- weighting `C6` vectorized `<ROM:w>` circuits by their lane count `K` so
  -- `rom.entries.length <= 2^39` holds unconditionally.
  fn shard_rows(weights: Lists::List<Field>, active: Lists::List<Field>, lds: Lists::List<UInt8::U8>) -> Field {
      match (*(weights)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(active));
          let Lists::Node::Nil = (*(lds));
          0 } ,
        Lists::Node::Cons(wt, wrest) => {
          let &Lists::Node::Cons(b, arest) = active;
          assert_eq!(b * (b - 1), 0);
          match b {
            0 => {  shard_rows(wrest, arest, lds) } ,
            _ => {
              let &Lists::Node::Cons(ld, lrest) = lds;
              assert_eq!(log_degree_ok(ld), 1);
              wt * pow2(UInt8::to_field(ld)) + shard_rows(wrest, arest, lrest) } ,
          } } ,
      }
    }

  -- The running total of a batch's weighted rows stays at most 2^39, so that
  -- the next shard's sum (each `wt * 2^ld <= 2^35`) cannot wrap the field.
  fn batch_rows(weights: Lists::List<Field>, headers: Lists::List<ProofDeserialize::ShardHeader>, acc: Field) -> Field {
      match (*(headers)) {
        Lists::Node::Nil => {  acc } ,
        Lists::Node::Cons(h, rest) => {
          let ProofDeserialize::ShardHeader::Mk(active, _cap, lds, _claims) = h;
          let rows = acc + shard_rows(weights, active, lds);
          assert_eq!(at_most_row_bound(rows), 1);
          batch_rows(weights, rest, rows) } ,
      }
    }

  -- Every circuit has fewer than 2^24 lookups (already bounded by u16 lcount in read_sys_circuit).
  fn lookups_ok(circuits: Lists::List<SystemDeserialize::SysCircuit>) -> Field {
      match (*(circuits)) {
        Lists::Node::Nil => {  1 } ,
        Lists::Node::Cons(circ, rest) => {
          let SystemDeserialize::SysCircuit::Mk(_nodes, _node_count, _zeros, _md, lks, _k, _mw, _pw, _ph, _s2w) = circ;
          let b = Goldilocks::gl_to_bytes(Lists::length(lks));
          assert_eq!(UInt8::to_field(b[3]) + UInt8::to_field(b[4]) + UInt8::to_field(b[5]) +
            UInt8::to_field(b[6]) + UInt8::to_field(b[7]), 0);
          lookups_ok(rest) } ,
      }
    }

  -- The bounds every verifier of these proofs enforces, mirroring Rust's
  -- `validate_preamble`. The weighted rows of a batch, summed over shards and
  -- active circuits (with `C6` vectorized ROM circuits weighted by `K` lanes),
  -- are at most 2^39 (`MAX_BATCH_ROWS`): the depth pass (Track A, H1) excludes
  -- memo cycles because a cycle needs `p / 2^24` rows, and `rom.entries.length <= 2^39`
  -- holds unconditionally. With every circuit below 2^24 lookups, the lookup
  -- budget `claims + sum of height * max(lookups, 1)` is below `2^63 + claims < p`.
  fn assert_batch_bounds(sys: SystemDeserialize::Sys, headers: Lists::List<ProofDeserialize::ShardHeader>) -> Field {
      let SystemDeserialize::Sys::Mk(_params, _tlimbs, circuits, _commit, _prep_indices) = sys;
      assert_eq!(lookups_ok(circuits), 1);
      let weights = circuit_row_weights(circuits);
      let _rows = batch_rows(weights, headers, 0);
      1
    }

  fn three_limbs(args: Lists::List<UInt64::U64>) -> (UInt64::U64, UInt64::U64, UInt64::U64) {
      let Lists::Node::Cons(a, r1) = (*(args));
      let Lists::Node::Cons(b, r2) = (*(r1));
      let Lists::Node::Cons(c, r3) = (*(r2));
      let Lists::Node::Nil = (*(r3));
      (a, b, c)
    }

  fn le_step(xi: UInt8::U8, yi: UInt8::U8, rest: Field) -> Field {
      UInt8::less_than(xi, yi) + Fields::is_zero(UInt8::to_field(xi) - UInt8::to_field(yi)) * rest
    }

  fn bytes8_le(x: [UInt8::U8; 8], y: [UInt8::U8; 8]) -> Field {
      le_step(x[7], y[7], le_step(x[6], y[6], le_step(x[5], y[5],
        le_step(x[4], y[4], le_step(x[3], y[3], le_step(x[2], y[2],
          le_step(x[1], y[1], le_step(x[0], y[0], 1))))))))
    }

  fn assert_closure_pairs_n(ms: Lists::List<ProofDeserialize::BatchMessage>, prev_w: Field, prev_b: Field, count: Field) -> Field {
      match (*(ms)) {
        Lists::Node::Nil => {  1 } ,
        Lists::Node::Cons(pull, rest1) => {
          assert_eq!(UInt32::less_than_fields(count, 65536), 1);
          let Lists::Node::Cons(push, rest) = (*(rest1));
          let ProofDeserialize::BatchMessage::Mk(pargs, pmult) = pull;
          let ProofDeserialize::BatchMessage::Mk(qargs, qmult) = push;
          assert_eq!(Goldilocks::gl_lt_p(pmult), 1);
          assert_eq!(Goldilocks::gl_lt_p(qmult), 1);
          assert_eq!(Goldilocks::gl_val(pmult) + 1, 0);
          assert_eq!(Goldilocks::gl_val(qmult), 1);
          let (pc, pw, pa) = three_limbs(pargs);
          let (qc, qw, qb) = three_limbs(qargs);
          assert_eq!(Goldilocks::gl_lt_p(pc), 1);
          assert_eq!(Goldilocks::gl_lt_p(pw), 1);
          assert_eq!(Goldilocks::gl_lt_p(pa), 1);
          assert_eq!(Goldilocks::gl_lt_p(qc), 1);
          assert_eq!(Goldilocks::gl_lt_p(qw), 1);
          assert_eq!(Goldilocks::gl_lt_p(qb), 1);
          assert_eq!(Goldilocks::gl_val(pc), 16);
          assert_eq!(Goldilocks::gl_val(qc), 16);
          let w = Goldilocks::gl_val(pw);
          assert_eq!(Goldilocks::gl_val(qw), w);
          let b = Goldilocks::gl_val(qb);
          -- Strict `a < b`: reject empty `a == b` no-op intervals.
          assert_eq!(bytes8_le(qb, pa), 0);

          let same_w = Fields::is_zero(w - prev_w);
          let w_up = 1 - bytes8_le(pw, Goldilocks::gl_to_bytes(prev_w));
          assert_eq!(
            w_up + same_w * bytes8_le(Goldilocks::gl_to_bytes(prev_b), pa), 1);
          assert_closure_pairs_n(rest, w, b, count + 1) } ,
      }
    }

  fn assert_closure_pairs(ms: Lists::List<ProofDeserialize::BatchMessage>, prev_w: Field, prev_b: Field) -> Field {
      assert_closure_pairs_n(ms, prev_w, prev_b, 0)
    }

  fn assert_closure_widths_loop(ms: Lists::List<ProofDeserialize::BatchMessage>, rom_widths: Lists::List<Field>, pairs: Field) -> Field {
      match (*(ms)) {
        Lists::Node::Nil => {  pairs } ,
        Lists::Node::Cons(pull, rest1) => {
          let Lists::Node::Cons(_push, rest) = (*(rest1));
          let ProofDeserialize::BatchMessage::Mk(pargs, _pmult) = pull;
          let (_pc, pw, _pa) = three_limbs(pargs);
          assert_eq!(field_in_list(rom_widths, Goldilocks::gl_val(pw)), 1);
          assert_closure_widths_loop(rest, rom_widths, pairs + 1) } ,
      }
    }

  fn assert_closure_widths_ok(circuits: Lists::List<SystemDeserialize::SysCircuit>,
        headers: Lists::List<ProofDeserialize::ShardHeader>,
        ms: Lists::List<ProofDeserialize::BatchMessage>) -> Field {
      let rom_widths = system_rom_widths(circuits);
      let pairs = assert_closure_widths_loop(ms, rom_widths, 0);
      let max_pairs = Lists::length(headers) * Lists::length(rom_widths);
      assert_eq!(UInt32::less_than_fields(pairs, max_pairs + 1), 1);
      1
    }

  fn verify_shard(sys: SystemDeserialize::Sys, header: ProofDeserialize::ShardHeader, shard: Field, proof: ProofDeserialize::Proof,
        input: Bytes::Stream, lch: ProofDeserialize::Ext, fch: ProofDeserialize::Ext) -> ProofDeserialize::Ext {
      let SystemDeserialize::Sys::Mk(params, _tlimbs, circuits, commit, prep_indices) = sys;
      let SystemDeserialize::SysParams::Mk(log_blowup, cap_height, log_final_poly_len,
                       max_log_arity, num_queries, commit_pow_bits,
                       query_pow_bits) = params;
      assert_eq!(cap_height, 0);
      assert_eq!(log_final_poly_len, 0);
      assert_eq!(max_log_arity, 1);
      let ProofDeserialize::ShardHeader::Mk(h_active, h_cap, h_lds, h_claims) = header;
      let ProofDeserialize::Proof::Mk(active, commitments, accs, log_degrees, opening,
                   q_opened, prep_opt, stage1, stage2) = proof;
      let num_circuits = Lists::length(accs);
      assert_eq!(Fields::is_zero(num_circuits), 0);
      assert_eq!(Lists::length(stage1), num_circuits);
      assert_eq!(Lists::length(stage2), num_circuits);
      assert_eq!(Lists::length(q_opened), num_circuits);
      assert_eq!(assert_bits(active), 1);
      assert_eq!(Fields::is_zero(Lists::length(active) - Lists::length(circuits)), 1);
      let acirc = select_active_circuits(circuits, active);
      let aprep = select_active_prep(prep_indices, active);
      assert_eq!(Fields::is_zero(Lists::length(acirc) - Lists::length(accs)), 1);
      let ProofDeserialize::Commitments::Mk(s1c, s2c, qc) = commitments;
      assert_eq!(assert_same_bits(h_active, active), 1);
      assert_eq!(assert_same_cap(h_cap, s1c), 1);
      assert_eq!(assert_same_u8s(h_lds, log_degrees), 1);
      assert_eq!(assert_log_degrees_ok(log_degrees), 1);
      assert_eq!(count_ones(active), Lists::length(log_degrees));
      let prep_cap = opt_commit_cap(commit);
      let _prep_match = match commit {
        SystemDeserialize::OptCommit::NoCommit => {
          let ProofDeserialize::PreprocessedOpt::NoPreprocessed = prep_opt;
          1 } ,
        SystemDeserialize::OptCommit::SomeCommit(_c) => {
          let ProofDeserialize::PreprocessedOpt::SomePreprocessed(_r) = prep_opt;
          1 } ,
      };
      let (alpha, zeta, post_zeta_input) = Transcript::shard_fiat_shamir(input, shard, s2c, qc, accs);
      assert_eq!(ext_is_zero(zeta), 0);
      let acc0 = claims_acc([0, 0], h_claims, lch, fch);
      let _ood = ood_loop(acirc, aprep, log_degrees, accs, stage1, stage2,
               prep_opt, q_opened, acc0, lch, fch, alpha, zeta);
      assert_eq!(Pcs::pcs_fri_verify(post_zeta_input, stage1, stage2, q_opened, prep_opt, opening,
        s1c, s2c, qc, prep_cap, aprep, log_degrees, zeta,
        num_circuits, log_blowup, num_queries, commit_pow_bits,
        query_pow_bits), 1);
      last_acc(accs)
    }

  fn verify_shards(sys: SystemDeserialize::Sys, headers: Lists::List<ProofDeserialize::ShardHeader>, proofs: Lists::List<ProofDeserialize::Proof>, shard: Field,
        input: Bytes::Stream, lch: ProofDeserialize::Ext, fch: ProofDeserialize::Ext, acc: ProofDeserialize::Ext) -> ProofDeserialize::Ext {
      match (*(headers)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(proofs));
          acc } ,
        Lists::Node::Cons(h, hrest) => {
          let Lists::Node::Cons(p, prest) = (*(proofs));
          let r = verify_shard(sys, h, shard, p, input, lch, fch);
          verify_shards(sys, hrest, prest, shard + 1, input, lch, fch, Goldilocks::eg_add(acc, r)) } ,
      }
    }

  fn batch_claims(headers: Lists::List<ProofDeserialize::ShardHeader>) -> Lists::List<Lists::List<UInt64::U64>> {
      match (*(headers)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(h, rest) => {
          let ProofDeserialize::ShardHeader::Mk(_active, _cap, _lds, claims) = h;
          Lists::concat(claims, batch_claims(rest)) } ,
      }
    }

  fn verify_batch(sys: SystemDeserialize::Sys, batch: ProofDeserialize::Batch) -> Lists::List<Lists::List<UInt64::U64>> {
      let ProofDeserialize::Batch::Mk(headers, messages, proofs) = batch;
      assert_eq!(assert_shard_count_ok(Lists::length(headers)), 1);
      assert_eq!(assert_batch_bounds(sys, headers), 1);
      assert_eq!(Lists::length(proofs), Lists::length(headers));
      assert_eq!(assert_closure_pairs(messages, 0, 0), 1);
      let SystemDeserialize::Sys::Mk(_params, tlimbs, circuits, commit, _prep_indices) = sys;
      assert_eq!(assert_closure_widths_ok(circuits, headers, messages), 1);
      let prep_cap = opt_commit_cap(commit);
      let (lch, fch, input) = Transcript::batch_fiat_shamir(tlimbs, prep_cap, headers, messages);
      let acc = messages_acc([0, 0], messages, lch, fch);
      let total = verify_shards(sys, headers, proofs, 0, input, lch, fch, acc);
      assert_eq!(ext_is_zero(total), 1);
      batch_claims(headers)
    }

  inline fn verify_batch_at(sys: SystemDeserialize::Sys, idx: Field, len: Field, claims: Lists::List<Lists::List<UInt64::U64>>) -> Field {
      let (batch, stop) = ProofDeserialize::read_batch(idx);
      assert_eq!(stop, idx + len);
      let found = verify_batch(sys, batch);
      assert_eq!(assert_same_claims(found, claims), 1);
      1
    }

  inline fn read_claims(stream: Bytes::Stream) -> (Lists::List<Lists::List<UInt64::U64>>, Bytes::Stream) {
      let (n, s) = ProofDeserialize::read_count(stream);
      read_claims_n(s, n)
    }

  fn read_claims_n(stream: Bytes::Stream, n: Field) -> (Lists::List<Lists::List<UInt64::U64>>, Bytes::Stream) {
      match n {
        0 => {  ((&(Lists::Node::Nil)), stream) } ,
        _ => {
          let (c, s) = read_one_claim(stream);
          let (rest, s2) = read_claims_n(s, n - 1);
          ((&(Lists::Node::Cons(c, rest))), s2) } ,
      }
    }

  inline fn read_one_claim(stream: Bytes::Stream) -> (Lists::List<UInt64::U64>, Bytes::Stream) {
      let (m, s) = ProofDeserialize::read_count(stream);
      read_claim_vals_n(s, m)
    }

  fn read_claim_vals_n(stream: Bytes::Stream, n: Field) -> (Lists::List<UInt64::U64>, Bytes::Stream) {
      match n {
        0 => {  ((&(Lists::Node::Nil)), stream) } ,
        _ => {
          let (x, s) = ProofDeserialize::read_u64(stream);
          assert_eq!(Goldilocks::gl_lt_p(x), 1);
          let (rest, s2) = read_claim_vals_n(s, n - 1);
          ((&(Lists::Node::Cons(x, rest))), s2) } ,
      }
    }
}
⟧

end MultiStark.Source
