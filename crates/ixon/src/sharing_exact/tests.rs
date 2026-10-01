//! Tests for exact minimum sharing: serializer-length helpers, structural
//! IDs, expansion validation, the fixed-dictionary recurrence against
//! enumeration, the width-state search against the tiny exhaustive oracle,
//! the §2 fixtures, representation independence and resource behavior.

#![allow(clippy::cast_possible_truncation)]

use std::collections::HashMap;

use rustc_hash::FxHashMap;
use std::sync::Arc;

use ix_common::address::Address;
use ix_common::env::{DefinitionSafety, QuotKind};

use super::cost::tag4_bytes_cmp;
use super::oracle::{
  bytes_of, oracle_full_product, oracle_ids, oracle_optimum, variant_count,
  variants,
};
use super::search::materialize_sequence;
use super::*;
use crate::constant::{
  Axiom, Constant, ConstantInfo, Constructor, ConstructorProj, DefKind,
  Definition, DefinitionProj, Inductive, InductiveProj, MutConst, Quotient,
  Recursor, RecursorProj, RecursorRule,
};
use crate::contract::{BinderContract, LetContract, ValueContract};
use crate::expr::Expr;
use crate::serialize::put_expr;
use crate::sharing::{analyze_block, build_sharing_vec, decide_sharing};
use crate::tag::{Tag0, Tag4, u64_byte_count};
use crate::univ::Univ;

// ===========================================================================
// Helpers
// ===========================================================================

type E = Arc<Expr>;

fn hex(b: &[u8]) -> String {
  b.iter().map(|x| format!("{x:02x}")).collect()
}

fn put(c: &Constant) -> Vec<u8> {
  let mut b = Vec::new();
  c.put(&mut b);
  b
}

fn roundtrip(c: &Constant) -> Vec<u8> {
  let b = put(c);
  let mut s = b.as_slice();
  let d = Constant::get(&mut s).expect("decode");
  assert!(s.is_empty(), "trailing bytes");
  assert_eq!(&d, c);
  b
}

fn univs(n: usize) -> Vec<Arc<Univ>> {
  let mut out = vec![Univ::zero()];
  for _ in 1..n {
    let last = out.last().unwrap().clone();
    out.push(Univ::succ(last));
  }
  out
}

fn axiom(root: E, univ_count: usize) -> Constant {
  Constant {
    info: ConstantInfo::Axio(Axiom { is_unsafe: false, lvls: 0, typ: root }),
    sharing: vec![],
    refs: vec![],
    univs: univs(univ_count),
  }
}

/// `T_n = Prop -> ... -> Prop` with `n` binders.
fn chain(n: usize) -> E {
  (0..n).fold(Expr::sort(0), |body, _| Expr::all(Expr::sort(0), body))
}

fn limits() -> ExactSharingLimits {
  ExactSharingLimits::default()
}

/// The constant with every root expanded and an empty table.
fn unshared(c: &Constant) -> Constant {
  let dag = SharingDag::from_constant(c, &limits()).unwrap();
  let info = rebuild_constant_info(&c.info, &dag.root_exprs()).unwrap();
  Constant {
    info,
    sharing: vec![],
    refs: c.refs.clone(),
    univs: c.univs.clone(),
  }
}

/// The historical heuristic applied to the expanded roots.
fn heuristic(c: &Constant) -> Constant {
  let dag = SharingDag::from_constant(c, &limits()).unwrap();
  let roots = dag.root_exprs();
  let (info, ptrs, topo) = analyze_block(&roots, false);
  let shared = decide_sharing(&info, &topo);
  let (rewritten, table) =
    build_sharing_vec(&roots, &shared, &ptrs, &info, &topo);
  Constant {
    info: rebuild_constant_info(&c.info, &rewritten).unwrap(),
    sharing: table,
    refs: c.refs.clone(),
    univs: c.univs.clone(),
  }
}

fn normalize(c: &Constant) -> Constant {
  normalize_constant_sharing(c, &limits()).unwrap()
}

/// Rebuild an expression with no pointer sharing at all.
fn deep_clone(e: &E) -> E {
  let kids: Vec<E> = e.children().into_iter().map(deep_clone).collect();
  if kids.is_empty() {
    Arc::new(e.as_ref().clone())
  } else {
    Arc::new(e.with_children(&kids).unwrap())
  }
}

struct Rng(u64);

impl Rng {
  fn next(&mut self) -> u64 {
    self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = self.0;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
  }
  fn below(&mut self, n: u64) -> u64 {
    self.next() % n
  }
  fn pct(&mut self, p: u64) -> bool {
    self.below(100) < p
  }
  fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
    &xs[self.below(xs.len() as u64) as usize]
  }
}

fn small_index(rng: &mut Rng) -> u64 {
  if rng.pct(85) { rng.below(3) } else { *rng.pick(&[7, 8, 200, 300]) }
}

fn value_contract(rng: &mut Rng) -> ValueContract {
  ValueContract::from_bits(rng.below(4) as u8).unwrap()
}

fn binder_contract(rng: &mut Rng) -> BinderContract {
  BinderContract::from_bits(rng.below(16) as u8).unwrap()
}

fn let_contract(rng: &mut Rng) -> LetContract {
  LetContract::from_flags(rng.below(4), binder_contract(rng)).unwrap()
}

/// Random expressions over every constructor, reusing earlier subterms so
/// that sharing matters. Contracts are drawn from a small set per call so
/// equal-shaped binders repeat.
struct ExprGen {
  rng: Rng,
  pool: Vec<E>,
  reuse: u64,
  contracts: Vec<(BinderContract, ValueContract)>,
}

impl ExprGen {
  fn new(seed: u64, reuse: u64) -> Self {
    let mut rng = Rng(seed);
    let contracts =
      (0..2).map(|_| (binder_contract(&mut rng), value_contract(&mut rng)));
    let contracts = contracts.collect();
    ExprGen { rng, pool: vec![], reuse, contracts }
  }

  fn leaf(&mut self) -> E {
    let r = &mut self.rng;
    match r.below(7) {
      0 | 1 => Expr::sort(small_index(r)),
      2 => Expr::var(small_index(r)),
      3 => {
        let us = (0..r.below(3)).map(|_| r.below(2)).collect();
        Expr::reference(small_index(r), us)
      },
      4 => {
        let us = (0..r.below(2)).map(|_| r.below(2)).collect();
        Expr::rec(r.below(2), us)
      },
      5 => Expr::str(small_index(r)),
      _ => Expr::nat(small_index(r)),
    }
  }

  fn expr(&mut self, depth: u32) -> E {
    if !self.pool.is_empty() && self.rng.pct(self.reuse) {
      return self.rng.pick(&self.pool).clone();
    }
    let e = if depth == 0 || self.rng.pct(30) {
      self.leaf()
    } else {
      let (bc, vc) = *self.rng.pick(&self.contracts.clone());
      match self.rng.below(9) {
        0 | 1 => {
          let f = self.expr(depth - 1);
          let a = self.expr(depth - 1);
          Expr::app(f, a)
        },
        2 | 3 => {
          let ty = self.expr(depth - 1);
          let b = self.expr(depth - 1);
          Expr::lam_contract(bc, ty, b)
        },
        4 | 5 => {
          let ty = self.expr(depth - 1);
          let b = self.expr(depth - 1);
          Expr::all_contract(bc, vc, ty, b)
        },
        6 => {
          let lc = let_contract(&mut self.rng);
          let ty = self.expr(depth - 1);
          let v = self.expr(depth - 1);
          let b = self.expr(depth - 1);
          Expr::let_contract(lc, ty, v, b)
        },
        7 => {
          let v = self.expr(depth - 1);
          Expr::prj(small_index(&mut self.rng), self.rng.below(9), v)
        },
        _ => {
          // A same-family spine continuation.
          let f = self.expr(depth - 1);
          let a = self.expr(depth - 1);
          let inner = Expr::app(f, a);
          let b = self.expr(depth - 1);
          Expr::app(inner, b)
        },
      }
    };
    self.pool.push(e.clone());
    e
  }
}

/// Wrap ordered roots in a random ConstantInfo that has exactly that many
/// roots, with random refs/univs tables.
fn wrap(rng: &mut Rng, roots: Vec<E>) -> Constant {
  let n = roots.len();
  let mut it = roots.into_iter();
  let mut take = || it.next().unwrap();
  let lvls = *rng.pick(&[0u64, 1, 3, 200]);
  let def = |take: &mut dyn FnMut() -> E, rng: &mut Rng| Definition {
    kind: *rng.pick(&[DefKind::Definition, DefKind::Opaque, DefKind::Theorem]),
    safety: *rng.pick(&[
      DefinitionSafety::Safe,
      DefinitionSafety::Unsafe,
      DefinitionSafety::Partial,
    ]),
    lvls,
    typ: take(),
    value: take(),
  };
  let rec = |take: &mut dyn FnMut() -> E, rules: usize, rng: &mut Rng| {
    let typ = take();
    Recursor {
      k: rng.pct(50),
      is_unsafe: rng.pct(50),
      lvls,
      params: rng.below(3),
      indices: rng.below(300),
      motives: 1,
      minors: rng.below(3),
      typ,
      rules: (0..rules)
        .map(|_| RecursorRule { fields: rng.below(3), rhs: take() })
        .collect(),
    }
  };
  let ind = |take: &mut dyn FnMut() -> E, ctors: usize, rng: &mut Rng| {
    let typ = take();
    Inductive {
      is_unsafe: rng.pct(50),
      lvls,
      params: rng.below(3),
      indices: rng.below(3),
      typ,
      ctors: (0..ctors)
        .map(|i| Constructor {
          is_unsafe: false,
          lvls,
          cidx: i as u64,
          params: 1,
          fields: rng.below(200),
          typ: take(),
        })
        .collect(),
    }
  };
  let addr = |i: u64| Address::hash(&i.to_le_bytes());
  let info = match (n, rng.below(4)) {
    (0, 0) => {
      ConstantInfo::CPrj(ConstructorProj { idx: 1, cidx: 2, block: addr(1) })
    },
    (0, 1) => ConstantInfo::RPrj(RecursorProj { idx: 0, block: addr(2) }),
    (0, 2) => ConstantInfo::IPrj(InductiveProj { idx: 300, block: addr(3) }),
    (0, _) => ConstantInfo::DPrj(DefinitionProj { idx: 4, block: addr(4) }),
    (1, 0) => {
      ConstantInfo::Axio(Axiom { is_unsafe: rng.pct(50), lvls, typ: take() })
    },
    (1, 1) => {
      ConstantInfo::Quot(Quotient { kind: QuotKind::Lift, lvls, typ: take() })
    },
    (2, 0 | 1) => ConstantInfo::Defn(def(&mut take, rng)),
    (n, 2) => {
      ConstantInfo::Muts(vec![MutConst::Indc(ind(&mut take, n - 1, rng))])
    },
    (n, 3) if n >= 3 => ConstantInfo::Muts(vec![
      MutConst::Defn(def(&mut take, rng)),
      MutConst::Recr(rec(&mut take, n - 3, rng)),
    ]),
    (n, _) => ConstantInfo::Recr(rec(&mut take, n - 1, rng)),
  };
  let refs = (0..rng.below(3)).map(addr).collect();
  let univs = (0..rng.below(3)).map(Univ::var).collect();
  Constant { info, sharing: vec![], refs, univs }
}

/// A random constant whose expanded roots have between `min_n` and `max_n`
/// distinct subterms.
fn gen_constant(seed: u64, min_n: usize, max_n: usize, depth: u32) -> Constant {
  let mut attempt = 0u64;
  loop {
    let mut g =
      ExprGen::new(seed.wrapping_mul(1_000_003).wrapping_add(attempt), 45);
    attempt += 1;
    let nroots = 1 + g.rng.below(3) as usize;
    let roots: Vec<E> = (0..nroots).map(|_| g.expr(depth)).collect();
    let (ids, _) = oracle_ids(&roots);
    if ids.len() < min_n || ids.len() > max_n {
      continue;
    }
    let mut rng = Rng(seed ^ 0xABCD);
    return wrap(&mut rng, roots);
  }
}

// ===========================================================================
// Serializer lengths
// ===========================================================================

fn boundary_sizes() -> Vec<u64> {
  let mut sizes = vec![0u64, 1, 7, 8, 9, 127, 128, 129, u64::MAX - 1, u64::MAX];
  for b in 1..8u32 {
    let x = 1u64 << (8 * b);
    sizes.extend([x - 1, x, x + 1]);
  }
  sizes
}

#[test]
fn tag_lengths_match_encoders() {
  for s in boundary_sizes() {
    assert_eq!(byte_count(s), u64::from(u64_byte_count(s)), "byte_count {s}");
    let mut b = Vec::new();
    Tag4::new(Expr::FLAG_SHARE, s).put(&mut b);
    assert_eq!(tag4_len(s), b.len() as u64, "tag4 {s}");
    assert_eq!(share_width(s), b.len() as u64, "share {s}");
    assert_eq!(expr_len(&Expr::Share(s)), Some(b.len() as u64));
    let mut b = Vec::new();
    Tag0::new(s).put(&mut b);
    assert_eq!(tag0_len(s), b.len() as u64, "tag0 {s}");
  }
  // Pinned header order: Tag4 bytes of one flag, unsigned lexicographic.
  for a in boundary_sizes() {
    for b in boundary_sizes() {
      let (mut x, mut y) = (Vec::new(), Vec::new());
      Tag4::new(Expr::FLAG_APP, a).put(&mut x);
      Tag4::new(Expr::FLAG_APP, b).put(&mut y);
      assert_eq!(tag4_bytes_cmp(a, b), x.cmp(&y), "{a} vs {b}");
    }
  }
  // Share width boundaries named by the plan.
  for (i, w) in
    [(7u64, 1u64), (8, 2), (255, 2), (256, 3), (65535, 3), (65536, 4)]
  {
    assert_eq!(share_width(i), w);
  }
  for (n, w) in [(127u64, 1u64), (128, 2), (255, 2), (256, 3)] {
    assert_eq!(tag0_len(n), w);
  }
}

fn telescope(kind: u8, n: usize, tail: E, rng: &mut Rng) -> E {
  let mut e = tail;
  for i in 0..n {
    let side = if i % 3 == 0 { Expr::var(i as u64) } else { Expr::sort(1) };
    e = match kind {
      0 => Expr::app(e, side),
      1 => Expr::lam_contract(binder_contract(rng), side, e),
      _ => {
        Expr::all_contract(binder_contract(rng), value_contract(rng), side, e)
      },
    };
  }
  e
}

#[test]
fn expr_len_matches_put_expr() {
  let check = |e: &Expr| {
    let mut b = Vec::new();
    put_expr(e, &mut b);
    assert_eq!(expr_len(e), Some(b.len() as u64), "{e:?}");
  };
  let mut rng = Rng(7);
  for kind in 0..3u8 {
    for n in [1usize, 2, 7, 8, 9, 255, 256, 257] {
      for tail in [
        Expr::var(0),
        Expr::share(300),
        telescope((kind + 1) % 3, 2, Expr::sort(0), &mut rng),
      ] {
        check(&telescope(kind, n, tail, &mut rng));
      }
    }
  }
  // Share leaves at every width boundary inside telescopes and heads.
  for s in boundary_sizes() {
    check(&Expr::app(Expr::app(Expr::share(s), Expr::share(s)), Expr::var(0)));
    check(&Expr::lam(Expr::share(s), Expr::share(s)));
    check(&Expr::prj(s, s, Expr::share(s)));
    check(&Expr::reference(s, vec![s, 0, s]));
  }
  // Pointer-shared DAGs.
  let mut e = Expr::var(0);
  for _ in 0..40 {
    e = Expr::app(e.clone(), e);
  }
  let mut b = Vec::new();
  put_expr(&Expr::app(Expr::var(1), Expr::var(2)), &mut b);
  assert!(expr_len(&e).is_some());
  for seed in 0..300 {
    let mut g = ExprGen::new(seed, 30);
    check(&g.expr(6));
  }
  let mut qc = quickcheck::Gen::new(20);
  for _ in 0..300 {
    check(&crate::expr::tests::arbitrary_expr(&mut qc));
  }
  // The 2^40-leaf doubling DAG above is measured without expansion.
  let mut d = Expr::var(0);
  for _ in 0..70 {
    d = Expr::app(d.clone(), d);
  }
  assert_eq!(expr_len(&d), None, "length above u64 must be reported");
}

fn random_table(rng: &mut Rng, n: usize) -> Vec<E> {
  (0..n)
    .map(|i| {
      if i > 0 && rng.pct(50) {
        Expr::app(Expr::share(rng.below(i as u64)), Expr::var(rng.below(9)))
      } else {
        Expr::var(rng.below(300))
      }
    })
    .collect()
}

#[test]
fn constant_len_matches_serializer() {
  let mut checked = 0;
  for seed in 0..400u64 {
    let mut rng = Rng(seed);
    let mut g = ExprGen::new(seed, 30);
    let n = rng.below(5) as usize;
    let roots: Vec<E> = (0..n).map(|_| g.expr(4)).collect();
    let mut c = wrap(&mut rng, roots);
    let table_len = *rng.pick(&[0usize, 1, 5, 127, 128, 255, 256]);
    c.sharing = random_table(&mut rng, table_len);
    c.refs = (0..*rng.pick(&[0u64, 1, 127, 128]))
      .map(|i| Address::hash(&i.to_le_bytes()))
      .collect();
    let b = put(&c);
    assert_eq!(constant_len(&c), Some(b.len() as u64), "seed {seed}");
    let mut parts = constant_fixed_len(&c).unwrap();
    for r in constant_info_root_exprs(&c.info) {
      parts += expr_len(&r).unwrap();
    }
    parts += sharing_table_len(&c.sharing).unwrap();
    assert_eq!(parts, b.len() as u64);
    checked += 1;
  }
  assert_eq!(checked, 400);
}

// ===========================================================================
// Roots
// ===========================================================================

#[test]
fn root_order_mirrors_constant_info_root_exprs() {
  let v = |i: u64| Expr::var(i);
  let def = |a, b| Definition {
    kind: DefKind::Definition,
    safety: DefinitionSafety::Safe,
    lvls: 0,
    typ: v(a),
    value: v(b),
  };
  let rec = |t, rs: &[u64]| Recursor {
    k: false,
    is_unsafe: false,
    lvls: 0,
    params: 0,
    indices: 0,
    motives: 0,
    minors: 0,
    typ: v(t),
    rules: rs.iter().map(|&r| RecursorRule { fields: 0, rhs: v(r) }).collect(),
  };
  let ctor = |t| Constructor {
    is_unsafe: false,
    lvls: 0,
    cidx: 0,
    params: 0,
    fields: 0,
    typ: v(t),
  };
  let cases: Vec<(ConstantInfo, Vec<u64>)> = vec![
    (ConstantInfo::Defn(def(0, 1)), vec![0, 1]),
    (ConstantInfo::Recr(rec(0, &[1, 2, 3])), vec![0, 1, 2, 3]),
    (
      ConstantInfo::Axio(Axiom { is_unsafe: false, lvls: 0, typ: v(0) }),
      vec![0],
    ),
    (
      ConstantInfo::Quot(Quotient { kind: QuotKind::Type, lvls: 0, typ: v(0) }),
      vec![0],
    ),
    (
      ConstantInfo::DPrj(DefinitionProj { idx: 0, block: Address::hash(b"") }),
      vec![],
    ),
    (
      ConstantInfo::Muts(vec![
        MutConst::Defn(def(0, 1)),
        MutConst::Indc(Inductive {
          is_unsafe: false,
          lvls: 0,
          params: 0,
          indices: 0,
          typ: v(2),
          ctors: vec![ctor(3), ctor(4)],
        }),
        MutConst::Recr(rec(5, &[6])),
      ]),
      vec![0, 1, 2, 3, 4, 5, 6],
    ),
  ];
  for (info, want) in cases {
    let roots = constant_info_root_exprs(&info);
    let got: Vec<u64> = roots
      .iter()
      .map(|e| match e.as_ref() {
        Expr::Var(i) => *i,
        _ => unreachable!(),
      })
      .collect();
    assert_eq!(got, want);
    assert_eq!(constant_info_root_count(&info), want.len());
    assert_eq!(rebuild_constant_info(&info, &roots).unwrap(), info);
    let fresh: Vec<E> = (100..100 + want.len() as u64).map(v).collect();
    let rebuilt = rebuild_constant_info(&info, &fresh).unwrap();
    assert_eq!(constant_info_root_exprs(&rebuilt), fresh);
    let mut short = fresh.clone();
    short.pop();
    let mut long = fresh.clone();
    long.push(v(9));
    for bad in [long, short].into_iter().filter(|b| b.len() != want.len()) {
      assert!(matches!(
        rebuild_constant_info(&info, &bad),
        Err(SharingError::Malformed(
          MalformedSharing::RootCountMismatch { .. }
        ))
      ));
    }
  }
}

// ===========================================================================
// Structural IDs and expansion
// ===========================================================================

#[test]
fn structural_ids_follow_height_then_key() {
  let p = Expr::sort(0);
  let t = Expr::sort(1);
  let roots = vec![
    Expr::all(p.clone(), t.clone()),
    Expr::app(Expr::var(0), p.clone()),
    Expr::reference(1, vec![]),
    Expr::reference(1, vec![0]),
    Expr::reference(0, vec![5]),
    Expr::nat(0),
    Expr::rec(0, vec![]),
    Expr::str(0),
  ];
  let dag = SharingDag::from_expanded_roots(&roots, &limits()).unwrap();
  let terms = dag.term_exprs();
  let order: Vec<E> = vec![
    Expr::sort(0),
    Expr::sort(1),
    Expr::var(0),
    Expr::reference(0, vec![5]),
    Expr::reference(1, vec![]),
    Expr::reference(1, vec![0]),
    Expr::rec(0, vec![]),
    Expr::str(0),
    Expr::nat(0),
    Expr::app(Expr::var(0), p.clone()),
    Expr::all(p, t),
  ];
  assert_eq!(terms, order);
  assert_eq!(dag.roots(), &[10, 9, 4, 5, 3, 8, 6, 7]);
  for (i, node) in dag.nodes().iter().enumerate() {
    for &c in node.children().as_slice() {
      assert!((c as usize) < i);
    }
    if i > 0 {
      let (h0, h1) = (dag.heights()[i - 1], dag.heights()[i]);
      assert!(
        h0 < h1 || (h0 == h1 && dag.key(i as u32 - 1) < dag.key(i as u32))
      );
    }
  }
}

#[test]
fn structural_ids_match_independent_oracle_ids() {
  for seed in 0..200 {
    let c = gen_constant(seed, 1, 60, 5);
    let roots = constant_info_root_exprs(&c.info);
    let dag = SharingDag::from_expanded_roots(&roots, &limits()).unwrap();
    let (ids, terms) = oracle_ids(&roots);
    assert_eq!(dag.term_exprs(), terms, "seed {seed}");
    for (r, &id) in roots.iter().zip(dag.roots()) {
      assert_eq!(ids[r.as_ref()], id);
    }
  }
}

#[test]
fn expansion_rejects_bad_tables() {
  let v0 = Expr::var(0);
  let err = |roots: Vec<E>, table: Vec<E>| {
    SharingDag::from_shared(&roots, &table, &limits()).unwrap_err()
  };
  let m = |x: MalformedSharing| SharingError::Malformed(x);
  assert_eq!(
    err(vec![Expr::share(1)], vec![v0.clone()]),
    m(MalformedSharing::ShareOutOfRange {
      location: ShareLocation::Root(0),
      index: 1,
      table_len: 1
    })
  );
  assert_eq!(
    err(
      vec![v0.clone()],
      vec![Expr::app(Expr::share(5), v0.clone()), v0.clone()]
    ),
    m(MalformedSharing::ShareOutOfRange {
      location: ShareLocation::Entry(0),
      index: 5,
      table_len: 2
    })
  );
  assert_eq!(
    err(
      vec![v0.clone()],
      vec![Expr::app(Expr::share(1), v0.clone()), Expr::var(1)]
    ),
    m(MalformedSharing::ForwardShare { entry: 0, index: 1 })
  );
  assert_eq!(
    err(vec![v0.clone()], vec![Expr::app(Expr::share(0), v0.clone())]),
    m(MalformedSharing::CyclicShare { entry: 0, index: 0 })
  );
  assert_eq!(
    err(
      vec![v0.clone()],
      vec![
        Expr::app(Expr::share(2), v0.clone()),
        Expr::var(3),
        Expr::lam(Expr::share(0), v0.clone())
      ]
    ),
    m(MalformedSharing::CyclicShare { entry: 0, index: 2 })
  );
  assert_eq!(
    optimize_sharing(
      &[v0.clone(), Expr::app(v0.clone(), Expr::share(0))],
      &limits()
    )
    .unwrap_err(),
    m(MalformedSharing::UnresolvedShare { root: 1, index: 0 })
  );
  // The same errors surface through the Constant API, including for
  // unreachable entries.
  let mut c = axiom(Expr::sort(0), 1);
  c.sharing = vec![Expr::var(1), Expr::app(Expr::share(1), v0)];
  assert_eq!(
    normalize_constant_sharing(&c, &limits()).unwrap_err(),
    m(MalformedSharing::CyclicShare { entry: 1, index: 1 })
  );
  assert!(matches!(
    check_canonical_sharing(&c, &limits()),
    Err(SharingError::Malformed(_))
  ));
}

#[test]
fn expansion_ignores_unreachable_entries_and_incoming_order() {
  // T2 -> T2 in several valid backward encodings, including a table whose
  // first entry inlines a subterm that a later entry stores, and garbage
  // entries that nothing references.
  let p = || Expr::sort(0);
  let t1 = || Expr::all(p(), p());
  let t2 = Expr::all(p(), t1());
  let base = axiom(Expr::all(t2.clone(), t2.clone()), 1);
  let mut a = base.clone();
  a.sharing = vec![t2.clone(), t1(), Expr::var(77)];
  a.info = ConstantInfo::Axio(Axiom {
    is_unsafe: false,
    lvls: 0,
    typ: Expr::all(Expr::share(0), Expr::share(0)),
  });
  let mut b = base.clone();
  b.sharing = vec![
    p(),
    Expr::all(Expr::share(0), Expr::share(0)),
    Expr::all(Expr::share(0), Expr::share(1)),
  ];
  b.info = ConstantInfo::Axio(Axiom {
    is_unsafe: false,
    lvls: 0,
    typ: Expr::all(Expr::share(2), Expr::all(Expr::share(0), Expr::share(1))),
  });
  let dag = SharingDag::from_constant(&base, &limits()).unwrap();
  for c in [&a, &b, &heuristic(&base)] {
    roundtrip(c);
    assert_eq!(SharingDag::from_constant(c, &limits()).unwrap(), dag);
    assert_eq!(put(&normalize(c)), put(&normalize(&base)));
  }
}

// ===========================================================================
// Fixed-dictionary recurrence (§5) against enumeration
// ===========================================================================

/// Minimum length and least bytes among all variants.
fn brute_best(e: &E, avail: &[(E, u64)]) -> (u64, Vec<u8>) {
  variants(e, avail)
    .iter()
    .map(|v| bytes_of(v))
    .map(|b| (b.len() as u64, b))
    .min()
    .unwrap()
}

#[test]
fn fixed_dictionary_matches_enumeration() {
  let interesting =
    [0u64, 1, 5, 7, 8, 9, 200, 255, 256, 65535, 65536, 1 << 32, 1 << 40];
  let mut cases = 0u64;
  let mut skipped = 0u64;
  let mut with_self_share = 0u64;
  for seed in 0..500u64 {
    let c = gen_constant(seed, 2, 9, 4);
    let roots = constant_info_root_exprs(&c.info);
    let dag = SharingDag::from_expanded_roots(&roots, &limits()).unwrap();
    let terms = dag.term_exprs();
    let mut rng = Rng(seed.wrapping_mul(31));
    for _ in 0..4 {
      // An arbitrary dictionary: random subset, random order, and either
      // consecutive or boundary-straddling indices.
      let mut chosen: Vec<u32> =
        (0..dag.len() as u32).filter(|_| rng.pct(45)).collect();
      for i in (1..chosen.len()).rev() {
        chosen.swap(i, rng.below(i as u64 + 1) as usize);
      }
      let sparse = rng.pct(50);
      let mut pool: Vec<u64> = interesting.to_vec();
      let mut dict = FixedDictionary::new();
      let mut avail: Vec<(E, u64)> = Vec::new();
      for (pos, &t) in chosen.iter().enumerate() {
        let idx = if sparse {
          let k = rng.below(pool.len() as u64) as usize;
          pool.swap_remove(k)
        } else {
          pos as u64
        };
        dict.insert(t, idx);
        avail.push((terms[t as usize].clone(), idx));
      }
      for t in 0..dag.len() as u32 {
        if variant_count(&terms[t as usize], &avail) > 20_000 {
          skipped += 1;
          continue;
        }
        let (len, bytes) = brute_best(&terms[t as usize], &avail);
        assert_eq!(
          dictionary_cost(&dag, &dict, t),
          Len::new(len),
          "seed {seed} term {t}"
        );
        let got = materialize_with_dictionary(&dag, &dict, &[t]).unwrap();
        assert_eq!(bytes_of(&got[0]), bytes, "seed {seed} term {t}");
        if chosen.contains(&t) {
          with_self_share += 1;
        }
        cases += 1;
      }
    }
  }
  eprintln!(
    "fixed-dictionary cases compared with enumeration: {cases} \
     ({with_self_share} with the term itself available, {skipped} skipped \
     above 20000 variants)"
  );
  assert!(cases > 5000 && skipped * 20 < cases);
}

// ===========================================================================
// §2 fixtures
// ===========================================================================

#[test]
fn fixture_t2_witness_is_17_bytes() {
  let t2 = chain(2);
  let c = axiom(Expr::all(t2.clone(), t2), 1);
  let unshared_bytes = roundtrip(&c);
  assert_eq!(hex(&unshared_bytes), "d200009317921700170000170017000000000100");
  let h = roundtrip(&heuristic(&c));
  assert_eq!(hex(&h), "d200009117b1b10291170000911700b0000100");
  let (exact, res) =
    normalize_constant_sharing_with_stats(&c, &limits()).unwrap();
  let bytes = roundtrip(&exact);
  eprintln!(
    "T2->T2: heuristic {} unshared {} exact {} {} Q={:?} stats={:?}",
    h.len(),
    unshared_bytes.len(),
    bytes.len(),
    hex(&bytes),
    res.table_terms,
    res.stats
  );
  assert_eq!(hex(&bytes), "d200009117b0b001921700170000000100");
  let o = oracle_optimum(&c);
  assert_eq!(o.bytes, bytes);
  assert_eq!(o.q, res.table_terms);
  assert_eq!(o.minimal_sequences, vec![res.table_terms.clone()]);
  assert_eq!(put(&o.constant), o.bytes);
  eprintln!("T2->T2 oracle: {} sequences", o.sequences);
  assert_eq!(o.sequences, 65);
}

#[test]
fn fixture_t16_improves_on_store_only_t16() {
  let t16 = chain(16);
  let c = axiom(Expr::all(t16.clone(), t16.clone()), 1);
  let unshared_len = roundtrip(&c).len();
  let heuristic_len = roundtrip(&heuristic(&c)).len();
  let mut store_only = c.clone();
  store_only.sharing = vec![t16];
  store_only.info = ConstantInfo::Axio(Axiom {
    is_unsafe: false,
    lvls: 0,
    typ: Expr::all(Expr::share(0), Expr::share(0)),
  });
  let store_only_len = roundtrip(&store_only).len();
  assert_eq!((heuristic_len, unshared_len, store_only_len), (81, 78, 46));
  let (exact, res) =
    normalize_constant_sharing_with_stats(&c, &limits()).unwrap();
  let bytes = roundtrip(&exact);
  eprintln!(
    "T16->T16: heuristic {heuristic_len} unshared {unshared_len} store-only {store_only_len} exact {} {} Q={:?} stats={:?}",
    bytes.len(),
    hex(&bytes),
    res.table_terms,
    res.stats
  );
  assert!(bytes.len() <= 46);
  // Certification is independent of the heuristic seed and of limits.
  let mut no_h = limits();
  no_h.heuristic_upper_bound = false;
  assert_eq!(put(&normalize_constant_sharing(&c, &no_h).unwrap()), bytes);
  let exact_q_len = sequence_len(
    &SharingDag::from_constant(&c, &limits()).unwrap(),
    &res.table_terms,
  )
  .unwrap();
  assert_eq!(
    exact_q_len.exact().unwrap() + constant_fixed_len(&c).unwrap(),
    bytes.len() as u64
  );
}

/// Nine independent 5-byte Ref atoms; the one with the greatest heuristic
/// hash is used 100 times, the others twice (the production probe fixture).
fn nine_ref_fixture() -> (Constant, E) {
  let mut atoms: Vec<E> =
    (0..9).map(|i| Expr::reference(i, vec![0, 0, 0])).collect();
  atoms.sort_by_key(|e| *crate::sharing::hash_expr(e).as_bytes());
  let hot = atoms.last().unwrap().clone();
  let mut roots: Vec<E> =
    atoms.iter().flat_map(|a| [a.clone(), a.clone()]).collect();
  for _ in 0..98 {
    roots.push(hot.clone());
  }
  let c = Constant {
    info: ConstantInfo::Recr(Recursor {
      k: false,
      is_unsafe: false,
      lvls: 0,
      params: 0,
      indices: 0,
      motives: 0,
      minors: 0,
      typ: roots[0].clone(),
      rules: roots[1..]
        .iter()
        .map(|e| RecursorRule { fields: 0, rhs: e.clone() })
        .collect(),
    }),
    sharing: vec![],
    refs: (0u64..9).map(|i| Address::hash(&i.to_le_bytes())).collect(),
    univs: vec![Univ::zero()],
  };
  (c, hot)
}

#[test]
fn fixture_nine_refs_reorders_676_to_578() {
  let (c, hot) = nine_ref_fixture();
  assert_eq!(hot.as_ref(), &Expr::Ref(2, vec![0, 0, 0]));
  let roots = constant_info_root_exprs(&c.info);
  let (info, ptrs, topo) = analyze_block(&roots, false);
  let shared = decide_sharing(&info, &topo);
  let mut frequency = topo.clone();
  frequency.sort_by_key(|h| std::cmp::Reverse(info[h].usage_count));
  let mut lens = Vec::new();
  for order in [&topo, &frequency] {
    let (rw, table) = build_sharing_vec(&roots, &shared, &ptrs, &info, order);
    let mut h = c.clone();
    h.info = rebuild_constant_info(&c.info, &rw).unwrap();
    h.sharing = table;
    lens.push(roundtrip(&h).len());
  }
  assert_eq!(lens, vec![676, 578]);
  let (exact, res) =
    normalize_constant_sharing_with_stats(&c, &limits()).unwrap();
  let bytes = roundtrip(&exact);
  eprintln!(
    "nine refs: heuristic {} reordered {} exact {} Q={:?} stats={:?}",
    lens[0],
    lens[1],
    bytes.len(),
    res.table_terms,
    res.stats
  );
  assert_eq!(bytes.len(), 578);
  // Ref(i,[0,0,0]) has term ID i; the least tied sequence keeps ID order,
  // which already gives the hot atom (ID 2) a one-byte index.
  assert_eq!(res.table_terms, (0..9).collect::<Vec<u32>>());
  assert_eq!(exact.sharing[2].as_ref(), hot.as_ref());
}

#[test]
fn fixture_two_minima_pins_the_tie() {
  let p = || Expr::sort(0);
  let a = Expr::all(p(), p());
  let b = Expr::all(p(), Expr::sort(1));
  let root =
    Expr::all(a.clone(), Expr::all(a.clone(), Expr::all(b.clone(), b.clone())));
  let c = axiom(root, 2);
  // Both table orders, written out by hand.
  let order = |first: &E, second: &E, sa: u64, sb: u64| {
    let mut x = c.clone();
    x.sharing = vec![first.clone(), second.clone()];
    x.info = ConstantInfo::Axio(Axiom {
      is_unsafe: false,
      lvls: 0,
      typ: Expr::all(
        Expr::share(sa),
        Expr::all(Expr::share(sa), Expr::all(Expr::share(sb), Expr::share(sb))),
      ),
    });
    roundtrip(&x)
  };
  let ab = order(&a, &b, 0, 1);
  let ba = order(&b, &a, 1, 0);
  assert_eq!(hex(&ab), "d200009317b017b017b1b10291170000911700010002000100");
  assert_eq!(hex(&ba), "d200009317b117b117b0b00291170001911700000002000100");
  let (exact, res) =
    normalize_constant_sharing_with_stats(&c, &limits()).unwrap();
  let bytes = roundtrip(&exact);
  let dag = SharingDag::from_constant(&c, &limits()).unwrap();
  let terms = dag.term_exprs();
  let id = |e: &E| terms.iter().position(|t| t == e).unwrap() as u32;
  eprintln!(
    "two minima: exact {} {} Q={:?} (A={}, B={})",
    bytes.len(),
    hex(&bytes),
    res.table_terms,
    id(&a),
    id(&b)
  );
  assert_eq!(bytes, ab, "the pinned tie stores A (lower term ID) first");
  assert_eq!(res.table_terms, vec![id(&a), id(&b)]);
  let o = oracle_optimum(&c);
  assert_eq!(o.bytes, bytes);
  assert_eq!(o.q, res.table_terms);
  assert_eq!(
    o.minimal_sequences,
    vec![vec![id(&a), id(&b)], vec![id(&b), id(&a)]]
  );
  eprintln!(
    "two minima oracle: {} sequences, minimal {:?}",
    o.sequences, o.minimal_sequences
  );
}

#[test]
fn prop_chains_match_probe_and_oracle() {
  // Production-probe measurements: (n, heuristic, unshared, store-only-Tn).
  let probe = [
    (1usize, 15usize, 16usize, 15usize),
    (2, 19, 20, 17),
    (3, 23, 24, 19),
    (4, 27, 28, 21),
    (7, 39, 41, 27),
    (8, 43, 46, 30),
    (9, 45, 50, 32),
    (16, 81, 78, 46),
    (32, 161, 142, 78),
  ];
  for (n, h, u, s) in probe {
    let t = chain(n);
    let c = axiom(Expr::all(t.clone(), t), 1);
    assert_eq!(roundtrip(&heuristic(&c)).len(), h, "heuristic n={n}");
    assert_eq!(roundtrip(&c).len(), u, "unshared n={n}");
    let bytes = roundtrip(&normalize(&c));
    eprintln!("chain {n}: exact {} ({})", bytes.len(), hex(&bytes));
    assert!(bytes.len() <= s, "n={n}");
    if n <= 3 {
      let o = oracle_optimum(&c);
      assert_eq!(o.bytes, bytes, "oracle n={n}");
    }
  }
}

// ===========================================================================
// Width-state search against the exhaustive oracle
// ===========================================================================

#[test]
fn optimizer_matches_exhaustive_oracle() {
  let mut kinds: HashMap<String, u64> = HashMap::new();
  let mut shared = 0u64;
  let mut parent_first = 0u64;
  let cases = 160u64;
  for seed in 0..cases {
    let c = gen_constant(seed, 2, 6, 4);
    let (exact, res) =
      normalize_constant_sharing_with_stats(&c, &limits()).unwrap();
    let bytes = roundtrip(&exact);
    let o = oracle_optimum(&c);
    assert_eq!(
      (o.len, &o.q, &o.bytes),
      (bytes.len() as u64, &res.table_terms, &bytes),
      "seed {seed}: {c:?}"
    );
    // Record coverage.
    let kind = match &c.info {
      ConstantInfo::Muts(_) => "muts".to_string(),
      other => format!("{}", other.variant().unwrap()),
    };
    *kinds.entry(kind).or_default() += 1;
    if !res.table_terms.is_empty() {
      shared += 1;
    }
    let dag = SharingDag::from_constant(&c, &limits()).unwrap();
    let q = &res.table_terms;
    let terms = dag.term_exprs();
    for i in 0..q.len() {
      for j in i + 1..q.len() {
        if contains(&terms[q[i] as usize], &terms[q[j] as usize]) {
          parent_first += 1;
        }
      }
    }
  }
  eprintln!(
    "oracle agreement: {cases} constants, {shared} with a nonempty optimum table, \
     {parent_first} parent-before-descendant pairs, kinds {kinds:?}"
  );
}

fn contains(hay: &E, needle: &E) -> bool {
  hay == needle || hay.children().into_iter().any(|c| contains(c, needle))
}

#[test]
fn oracle_separability_matches_full_product() {
  let t1 = chain(1);
  let mut cases = vec![axiom(Expr::all(t1.clone(), t1), 1)];
  for seed in 0..40 {
    cases.push(gen_constant(seed + 5000, 2, 4, 3));
  }
  let mut complete = 0u64;
  let mut compared = 0u64;
  for c in &cases {
    let Some((len, q, bytes, n)) = oracle_full_product(c, 20_000) else {
      continue;
    };
    let o = oracle_optimum(c);
    assert_eq!((len, &q, &bytes), (o.len, &o.q, &o.bytes));
    let exact = roundtrip(&normalize(c));
    assert_eq!(exact, bytes);
    complete += n;
    compared += 1;
  }
  eprintln!(
    "full-product oracle: {compared} constants, {complete} complete encodings"
  );
  assert!(compared >= 20);
}

// ===========================================================================
// Invariance, idempotence and comparison with other encodings
// ===========================================================================

/// Rebuild with random partial pointer sharing.
fn remix(e: &E, rng: &mut Rng, memo: &mut HashMap<Expr, E>) -> E {
  if rng.pct(50)
    && let Some(x) = memo.get(e.as_ref())
  {
    return x.clone();
  }
  let kids: Vec<E> =
    e.children().into_iter().map(|c| remix(c, rng, memo)).collect();
  let out = if kids.is_empty() {
    Arc::new(e.as_ref().clone())
  } else {
    Arc::new(e.with_children(&kids).unwrap())
  };
  memo.insert(e.as_ref().clone(), out.clone());
  out
}

#[test]
fn representation_independence() {
  // Results (or errors) that do not depend on the input's pointer layout.
  fn outcome(
    r: Result<ExactSharingResult, SharingError>,
  ) -> Result<(Vec<u32>, u64, Vec<u8>), SharingError> {
    r.map(|x| {
      let mut b = Vec::new();
      for e in x.roots.iter().chain(&x.sharing) {
        put_expr(e, &mut b);
      }
      (x.table_terms, x.variable_len, b)
    })
  }
  let mut solved = 0;
  for seed in 0..120 {
    let c = gen_constant(seed + 900, 3, 30, 5);
    let roots = constant_info_root_exprs(&c.info);
    let reference = outcome(optimize_sharing(&roots, &limits()));
    let dag = SharingDag::from_expanded_roots(&roots, &limits()).unwrap();
    let mut rng = Rng(seed);
    let layouts: Vec<Vec<E>> =
      vec![roots.iter().map(deep_clone).collect(), dag.root_exprs(), {
        let mut memo = HashMap::new();
        roots.iter().map(|r| remix(r, &mut rng, &mut memo)).collect()
      }];
    for layout in layouts {
      assert_eq!(
        SharingDag::from_expanded_roots(&layout, &limits()).unwrap(),
        dag
      );
      assert_eq!(
        outcome(optimize_sharing(&layout, &limits())),
        reference,
        "seed {seed}"
      );
    }
    if reference.is_ok() {
      solved += 1;
    }
  }
  eprintln!(
    "representation independence: {solved}/120 solved, all layouts identical"
  );
  assert!(solved >= 110);
}

#[test]
fn exact_is_idempotent_and_never_worse() {
  let mut stats = (0u64, 0u64, 0u64, 0u64);
  let mut most_states = 0u64;
  let mut l = limits();
  l.max_states = 200_000;
  l.max_layer_states = 100_000;
  for seed in 0..150 {
    let c = gen_constant(seed + 20_000, 4, 45, 6);
    let h = heuristic(&c);
    let u = unshared(&c);
    let exact = match normalize_constant_sharing_with_stats(&c, &l) {
      Ok((x, r)) => {
        most_states = most_states.max(r.stats.states_created);
        x
      },
      Err(SharingError::ResourceExhausted(r)) => {
        stats.3 += 1;
        eprintln!("seed {seed}: resource limit {r:?}");
        continue;
      },
      Err(e) => panic!("seed {seed}: {e}"),
    };
    let eb = roundtrip(&exact);
    let hb = roundtrip(&h);
    let ub = roundtrip(&u);
    assert!(eb.len() <= ub.len() && eb.len() <= hb.len(), "seed {seed}");
    stats.0 += 1;
    stats.1 += (hb.len() - eb.len()) as u64;
    stats.2 += (ub.len() - eb.len()) as u64;
    // Expand-then-normalize is a fixpoint, from every incoming encoding.
    for x in [&exact, &h, &u] {
      assert_eq!(put(&normalize(x)), eb, "seed {seed}");
    }
    assert_eq!(
      check_canonical_sharing(&exact, &limits()).unwrap(),
      CanonicalCheck::Canonical
    );
    if hb != eb {
      assert!(matches!(
        check_canonical_sharing(&h, &limits()).unwrap(),
        CanonicalCheck::NonCanonical { .. }
      ));
    }
  }
  eprintln!(
    "never-worse: {} solved, saved {} bytes vs heuristic and {} vs unshared, \
     {} resource errors, most states in a solved case {most_states}",
    stats.0, stats.1, stats.2, stats.3
  );
  assert!(stats.0 >= 140);
}

// ===========================================================================
// Resources, bounds and forced states
// ===========================================================================

#[test]
fn resource_limits_fail_closed() {
  let t16 = chain(16);
  let c = axiom(Expr::all(t16.clone(), t16), 1);
  let want = put(&normalize(&c));
  let cases: Vec<(Resource, Box<dyn Fn(&mut ExactSharingLimits)>)> = vec![
    (Resource::InputNodes, Box::new(|l| l.max_input_nodes = 3)),
    (Resource::DistinctNodes, Box::new(|l| l.max_distinct_nodes = 5)),
    (Resource::Height, Box::new(|l| l.max_height = 4)),
    (Resource::Candidates, Box::new(|l| l.max_candidates = 3)),
    (Resource::States, Box::new(|l| l.max_states = 5)),
    (Resource::LayerStates, Box::new(|l| l.max_layer_states = 2)),
    (Resource::Transitions, Box::new(|l| l.max_transitions = 4)),
    (Resource::Work, Box::new(|l| l.max_work = 50)),
    (Resource::OutputBytes, Box::new(|l| l.max_output_bytes = 45)),
  ];
  for (resource, set) in cases {
    let mut l = limits();
    l.heuristic_upper_bound = false;
    l.greedy_upper_bound = false;
    set(&mut l);
    match normalize_constant_sharing(&c, &l) {
      Err(SharingError::ResourceExhausted(r)) => {
        assert_eq!(r.resource, resource)
      },
      other => panic!("{resource:?}: expected exhaustion, got {other:?}"),
    }
  }
  // Every successful invocation returns the same bytes, whatever the limits.
  let mut tight = limits();
  let res = normalize_constant_sharing_with_stats(&c, &tight).unwrap().1;
  tight.max_states = res.stats.states_created;
  tight.max_transitions = res.stats.transitions;
  tight.max_work = res.stats.work;
  tight.max_output_bytes = want.len() as u64;
  assert_eq!(put(&normalize_constant_sharing(&c, &tight).unwrap()), want);
  let mut unbounded = ExactSharingLimits::unbounded();
  unbounded.heuristic_upper_bound = false;
  unbounded.greedy_upper_bound = false;
  assert_eq!(put(&normalize_constant_sharing(&c, &unbounded).unwrap()), want);
  // Counters are deterministic.
  let again = normalize_constant_sharing_with_stats(&c, &limits()).unwrap().1;
  assert_eq!(again.stats, res.stats);
}

#[test]
fn overflowing_lengths_are_exact_or_errors() {
  // x_{i+1} = App(x_i, x_i): the unshared length exceeds u64.
  let mut x = Expr::var(0);
  for _ in 0..70 {
    x = Expr::app(x.clone(), x);
  }
  let mut l = limits();
  l.max_states = 20_000;
  l.max_transitions = 2_000_000;
  match optimize_sharing(std::slice::from_ref(&x), &l) {
    Ok(r) => {
      eprintln!(
        "doubling-70 solved: {} bytes, Q len {}",
        r.variable_len,
        r.table_terms.len()
      );
      assert_eq!(r.stats.unshared_len, None);
    },
    Err(SharingError::ResourceExhausted(r)) => {
      eprintln!("doubling-70: resource limit {r:?}");
    },
    Err(e) => panic!("unexpected {e}"),
  }
  // A small doubling DAG is solved exactly and beats the unshared form.
  let mut y = Expr::var(0);
  for _ in 0..6 {
    y = Expr::app(y.clone(), y);
  }
  let r = optimize_sharing(std::slice::from_ref(&y), &limits()).unwrap();
  let u = r.stats.unshared_len.unwrap();
  eprintln!(
    "doubling-6: exact {} unshared {u} Q={:?}",
    r.variable_len, r.table_terms
  );
  assert!(r.variable_len < u);
}

#[test]
fn forced_states_cross_tag0_and_share_width_boundaries() {
  // 300 independent atoms, each used twice, as one recursor.
  let atoms: Vec<E> = (0..300).map(|i| Expr::reference(i, vec![])).collect();
  let roots: Vec<E> =
    atoms.iter().flat_map(|a| [a.clone(), a.clone()]).collect();
  let c = Constant {
    info: ConstantInfo::Recr(Recursor {
      k: false,
      is_unsafe: false,
      lvls: 0,
      params: 0,
      indices: 0,
      motives: 0,
      minors: 0,
      typ: roots[0].clone(),
      rules: roots[1..]
        .iter()
        .map(|e| RecursorRule { fields: 0, rhs: e.clone() })
        .collect(),
    }),
    sharing: vec![],
    refs: vec![],
    univs: vec![],
  };
  let dag = SharingDag::from_constant(&c, &limits()).unwrap();
  let fixed = constant_fixed_len(&c).unwrap();
  let lim = limits();
  let mut meter = Meter::new(&lim);
  for k in [0usize, 7, 8, 9, 127, 128, 129, 255, 256, 257, 300] {
    // Store the atoms in reverse ID order so every width class is used.
    let q: Vec<u32> = (0..k as u32).rev().collect();
    let predicted = sequence_len(&dag, &q).unwrap().exact().unwrap();
    let (rw, table) = materialize_sequence(
      &dag,
      &dag.nodes().iter().map(Node::own_len).collect::<Vec<_>>(),
      &q,
      &mut meter,
    )
    .unwrap();
    let mut x = c.clone();
    x.info = rebuild_constant_info(&c.info, &rw).unwrap();
    x.sharing = table;
    let b = roundtrip(&x);
    assert_eq!(fixed + predicted, b.len() as u64, "k={k}");
    assert_eq!(constant_len(&x), Some(b.len() as u64));
    assert_eq!(SharingDag::from_constant(&x, &limits()).unwrap(), dag);
  }
}

#[test]
fn projections_and_empty_roots() {
  let c = Constant {
    info: ConstantInfo::IPrj(InductiveProj {
      idx: 3,
      block: Address::hash(b"b"),
    }),
    sharing: vec![Expr::var(0), Expr::app(Expr::share(0), Expr::share(0))],
    refs: vec![Address::hash(b"r")],
    univs: vec![Univ::zero()],
  };
  let n = normalize(&c);
  assert!(n.sharing.is_empty());
  assert_eq!(n.info, c.info);
  assert_eq!(normalize(&n), n);
  let r = optimize_sharing(&[], &limits()).unwrap();
  assert_eq!((r.roots.len(), r.sharing.len(), r.variable_len), (0, 0, 1));
}

#[test]
fn pruning_never_changes_the_result() {
  // (lower-bound pruning, materialization bound, heuristic seed, greedy seed)
  const MODES: [(bool, bool, bool, bool); 7] = [
    (false, false, false, false),
    (true, false, false, false),
    (true, false, true, false),
    (true, false, false, true),
    (true, true, false, false),
    (true, true, true, false),
    (true, true, true, true),
  ];
  let mut compared = 0u64;
  let mut states = [0u64; MODES.len()];
  for seed in 0..150 {
    let c = gen_constant(seed + 40_000, 4, 18, 5);
    let mut results: Vec<(Vec<u8>, Vec<u32>)> = Vec::new();
    let mut seen = [0u64; MODES.len()];
    let mut complete = true;
    for (i, (p, m, h, g)) in MODES.into_iter().enumerate() {
      let mut l = limits();
      l.lower_bound_pruning = p;
      l.materialization_bound = m;
      l.heuristic_upper_bound = h;
      l.greedy_upper_bound = g;
      l.max_states = 300_000;
      match normalize_constant_sharing_with_stats(&c, &l) {
        Ok((x, r)) => {
          seen[i] = r.stats.states_expanded;
          results.push((put(&x), r.table_terms));
        },
        Err(SharingError::ResourceExhausted(_)) => complete = false,
        Err(e) => panic!("seed {seed}: {e}"),
      }
    }
    assert!(!results.is_empty(), "seed {seed}: every mode exhausted");
    for r in &results[1..] {
      assert_eq!(r, &results[0], "seed {seed}");
    }
    if complete {
      compared += 1;
      for i in 0..MODES.len() {
        states[i] += seen[i];
      }
    }
  }
  eprintln!(
    "pruning modes agree on {compared} constants with every mode complete; \
     states expanded per mode {states:?}"
  );
  assert!(compared >= 100);
}

#[test]
fn ordering_parent_stored_before_its_inlined_descendant() {
  // Seven hot atoms and a hot parent P take the eight one-byte slots; P's
  // descendant D is also stored, but only in slot 8, so P's entry must
  // inline D. Storing D first would push P to a two-byte index.
  let hot: Vec<E> = (0..7).map(|i| Expr::reference(i, vec![0, 0, 0])).collect();
  let d = Expr::reference(20, vec![0, 0, 0, 0, 0]);
  let p = Expr::app(Expr::var(0), d.clone());
  let mut roots: Vec<E> = Vec::new();
  for h in &hot {
    roots.extend(std::iter::repeat_n(h.clone(), 50));
  }
  roots.extend(std::iter::repeat_n(p.clone(), 40));
  roots.extend(std::iter::repeat_n(d.clone(), 3));
  let c = Constant {
    info: ConstantInfo::Recr(Recursor {
      k: false,
      is_unsafe: false,
      lvls: 0,
      params: 0,
      indices: 0,
      motives: 0,
      minors: 0,
      typ: roots[0].clone(),
      rules: roots[1..]
        .iter()
        .map(|e| RecursorRule { fields: 0, rhs: e.clone() })
        .collect(),
    }),
    sharing: vec![],
    refs: vec![],
    univs: vec![Univ::zero()],
  };
  let dag = SharingDag::from_constant(&c, &limits()).unwrap();
  let terms = dag.term_exprs();
  let id = |e: &E| terms.iter().position(|t| t == e).unwrap() as u32;
  let (exact, res) =
    normalize_constant_sharing_with_stats(&c, &limits()).unwrap();
  let bytes = roundtrip(&exact);
  let hot_ids: Vec<u32> = hot.iter().map(id).collect();
  let mut want = hot_ids.clone();
  want.extend([id(&p), id(&d)]);
  eprintln!(
    "parent-first: exact {} bytes Q={:?} (P={}, D={})",
    bytes.len(),
    res.table_terms,
    id(&p),
    id(&d)
  );
  assert_eq!(res.table_terms, want);
  // P's entry inlines D, which is stored separately afterwards.
  assert_eq!(exact.sharing[7].as_ref(), p.as_ref());
  assert_eq!(exact.sharing[8].as_ref(), d.as_ref());
  // Storing D before P is feasible but strictly longer.
  let mut child_first = hot_ids;
  child_first.extend([id(&d), id(&p)]);
  let parent_first = sequence_len(&dag, &res.table_terms).unwrap();
  let child_first = sequence_len(&dag, &child_first).unwrap();
  eprintln!("parent-first {parent_first:?} vs child-first {child_first:?}");
  assert!(parent_first < child_first);
}

#[test]
fn byte_level_normalization() {
  let t2 = chain(2);
  let c = axiom(Expr::all(t2.clone(), t2), 1);
  let heuristic_bytes = put(&heuristic(&c));
  let out = normalize_constant_bytes(&heuristic_bytes, &limits()).unwrap();
  assert_eq!(hex(&out), "d200009117b0b001921700170000000100");
  assert_eq!(normalize_constant_bytes(&out, &limits()).unwrap(), out);
  let mut trailing = out.clone();
  trailing.push(0);
  assert!(matches!(
    normalize_constant_bytes(&trailing, &limits()),
    Err(NormalizeBytesError::Decode(_))
  ));
  assert!(matches!(
    normalize_constant_bytes(&out[..5], &limits()),
    Err(NormalizeBytesError::Decode(_))
  ));
  let mut cyclic = c.clone();
  cyclic.sharing = vec![Expr::app(Expr::share(0), Expr::var(0))];
  assert_eq!(
    normalize_constant_bytes(&put(&cyclic), &limits()).unwrap_err().to_string(),
    "malformed sharing: CyclicShare { entry: 0, index: 0 }"
  );
}

#[test]
fn telescope_cuts_at_header_boundaries_match_enumeration() {
  let mut rng = Rng(99);
  let mut checked = 0u64;
  for kind in 0..3u8 {
    for n in [1usize, 6, 7, 8, 9, 15, 16, 17, 255, 256, 257] {
      // Mixed contracts and side children; the tail is another family.
      let tail = telescope((kind + 1) % 3, 2, Expr::sort(0), &mut rng);
      let e = telescope(kind, n, tail, &mut rng);
      let dag =
        SharingDag::from_expanded_roots(std::slice::from_ref(&e), &limits())
          .unwrap();
      let terms = dag.term_exprs();
      // The spine suffixes of the root, outermost first.
      let mut spine: Vec<u32> = vec![dag.roots()[0]];
      loop {
        let cur = *spine.last().unwrap();
        let next = match dag.node(cur) {
          Node::App(f, _) => *f,
          Node::Lam(_, _, b) | Node::All(_, _, _, b) => *b,
          _ => break,
        };
        if dag.node(next).family() != dag.node(cur).family() {
          break;
        }
        spine.push(next);
      }
      assert_eq!(spine.len(), n);
      for trial in 0..6 {
        let mut dict = FixedDictionary::new();
        let mut avail: Vec<(E, u64)> = Vec::new();
        let indices = [0u64, 7, 8, 255, 256, 65535, 65536];
        for (slot, _) in (0..1 + trial % 3).enumerate() {
          let t = spine[rng.below(spine.len() as u64) as usize];
          if dict.index_of(t).is_some() {
            continue;
          }
          let idx = indices[(slot + trial) % indices.len()];
          dict.insert(t, idx);
          avail.push((terms[t as usize].clone(), idx));
        }
        for &t in &[spine[0], spine[spine.len() / 2]] {
          assert!(variant_count(&terms[t as usize], &avail) <= 64);
          let (len, bytes) = brute_best(&terms[t as usize], &avail);
          assert_eq!(
            dictionary_cost(&dag, &dict, t),
            Len::new(len),
            "{kind} {n}"
          );
          let got = materialize_with_dictionary(&dag, &dict, &[t]).unwrap();
          assert_eq!(bytes_of(&got[0]), bytes, "{kind} {n}");
          checked += 1;
        }
      }
    }
  }
  eprintln!("telescope boundary cases compared with enumeration: {checked}");
}

#[test]
fn every_valid_incoming_encoding_normalizes_identically() {
  let lim = limits();
  let mut encodings = 0u64;
  for seed in 0..80 {
    let c = gen_constant(seed + 60_000, 3, 25, 5);
    let want = put(&normalize(&c));
    let dag = SharingDag::from_constant(&c, &lim).unwrap();
    let own: Vec<Len> = dag.nodes().iter().map(Node::own_len).collect();
    let mut rng = Rng(seed);
    for _ in 0..8 {
      // Any distinct subterms in any order, including non-candidates and
      // entries nothing will reference.
      let mut q: Vec<u32> =
        (0..dag.len() as u32).filter(|_| rng.pct(35)).collect();
      for i in (1..q.len()).rev() {
        q.swap(i, rng.below(i as u64 + 1) as usize);
      }
      let mut meter = Meter::new(&lim);
      let (roots, table) =
        materialize_sequence(&dag, &own, &q, &mut meter).unwrap();
      let mut x = c.clone();
      x.info = rebuild_constant_info(&c.info, &roots).unwrap();
      x.sharing = table;
      let b = roundtrip(&x);
      assert_eq!(
        constant_fixed_len(&c).unwrap()
          + sequence_len(&dag, &q).unwrap().exact().unwrap(),
        b.len() as u64
      );
      assert_eq!(SharingDag::from_constant(&x, &lim).unwrap(), dag);
      assert!(want.len() <= b.len());
      assert_eq!(put(&normalize(&x)), want, "seed {seed} q {q:?}");
      encodings += 1;
    }
  }
  eprintln!("incoming encodings normalized identically: {encodings}");
}

/// Extended oracle agreement; run with
/// `cargo test --release -p ixon oracle_extended -- --ignored --nocapture`.
#[test]
#[ignore = "long-running; run explicitly in release mode"]
fn oracle_extended() {
  let mut tags = [0u64; 11];
  let mut contracts = std::collections::BTreeSet::new();
  let mut cases = 0u64;
  let mut seven = 0u64;
  let mut skipped = 0u64;
  for seed in 0..1500u64 {
    let max_n = if seed % 25 == 0 { 7 } else { 6 };
    let c = gen_constant(seed + 100_000, 2, max_n, 4);
    if !oracle_tractable(&c, 5_000) {
      skipped += 1;
      continue;
    }
    let dag = SharingDag::from_constant(&c, &limits()).unwrap();
    for node in dag.nodes() {
      tags[node.tag() as usize] += 1;
      match node {
        Node::Lam(bc, ..) => {
          contracts.insert((8u8, u64::from(bc.to_bits())));
        },
        Node::All(bc, vc, ..) => {
          contracts.insert((
            9,
            u64::from(crate::contract::pack_all_contract(*bc, *vc)),
          ));
        },
        Node::Let(lc, ..) => {
          contracts
            .insert((10, lc.flags() * 16 + u64::from(lc.binder.to_bits())));
        },
        _ => {},
      }
    }
    let (exact, res) =
      normalize_constant_sharing_with_stats(&c, &limits()).unwrap();
    let bytes = roundtrip(&exact);
    let o = oracle_optimum(&c);
    assert_eq!(
      (o.len, &o.q, &o.bytes),
      (bytes.len() as u64, &res.table_terms, &bytes),
      "seed {seed}"
    );
    cases += 1;
    if dag.len() == 7 {
      seven += 1;
    }
    if seed % 100 == 99 {
      eprintln!("oracle_extended: {} seeds, {cases} compared", seed + 1);
    }
  }
  eprintln!(
    "extended oracle agreement: {cases} constants ({seven} with N = 7, \
     {skipped} skipped as intractable for the oracle), \
     node tags {tags:?}, distinct binder/let contract codes {}",
    contracts.len()
  );
}

/// Independent exhaustive table-order search: every ordered sequence of
/// distinct terms from `pool`, each evaluated exactly, without state
/// merging or pruning. Returns the least `(variable length, Q)`.
fn brute_force_tables(dag: &SharingDag, pool: &[u32]) -> (Len, Vec<u32>, u64) {
  use super::dict::{DenseIndex, all_costs};
  fn go(
    dag: &SharingDag,
    own: &[Len],
    pool: &[u32],
    dict: &mut DenseIndex,
    q: &mut Vec<u32>,
    f: Len,
    best: &mut (Len, Vec<u32>),
    visited: &mut u64,
  ) {
    *visited += 1;
    let mut work = 0;
    let costs = all_costs(dag.nodes(), own, &*dict, &mut work);
    let mut total = f.plus(Len::new(tag0_len(q.len() as u64)));
    for &r in dag.roots() {
      total = total.plus(costs[r as usize]);
    }
    if (total, &*q) < (best.0, &best.1) {
      *best = (total, q.clone());
    }
    for &t in pool {
      if q.contains(&t) {
        continue;
      }
      let nf = f.plus(costs[t as usize]);
      dict.set(t, q.len() as u64);
      q.push(t);
      go(dag, own, pool, dict, q, nf, best, visited);
      q.pop();
      dict.set(t, u64::MAX);
    }
  }
  let own: Vec<Len> = dag.nodes().iter().map(Node::own_len).collect();
  let mut dict = DenseIndex::new(dag.len());
  let mut best = (Len::OVERFLOW, Vec::new());
  let mut visited = 0;
  go(
    dag,
    &own,
    pool,
    &mut dict,
    &mut Vec::new(),
    Len::ZERO,
    &mut best,
    &mut visited,
  );
  (best.0, best.1, visited)
}

fn check_against_brute_force(c: &Constant) -> u64 {
  let dag = SharingDag::from_constant(c, &limits()).unwrap();
  let pool: Vec<u32> = (0..dag.len() as u32).collect();
  let (len, q, visited) = brute_force_tables(&dag, &pool);
  let (exact, res) =
    normalize_constant_sharing_with_stats(c, &limits()).unwrap();
  assert_eq!((Len::new(res.variable_len), &res.table_terms), (len, &q));
  let lim = limits();
  let mut meter = Meter::new(&lim);
  let own: Vec<Len> = dag.nodes().iter().map(Node::own_len).collect();
  let (roots, table) =
    materialize_sequence(&dag, &own, &q, &mut meter).unwrap();
  let mut x = c.clone();
  x.info = rebuild_constant_info(&c.info, &roots).unwrap();
  x.sharing = table;
  assert_eq!(put(&x), put(&exact));
  visited
}

#[test]
fn width_classes_match_exhaustive_table_orders() {
  // Nine independent atoms: every table of 9 entries puts one in slot 8.
  let (c, _) = nine_ref_fixture();
  let visited = check_against_brute_force(&c);
  eprintln!("nine refs: brute force visited {visited} table sequences");
  assert_eq!(visited, 986_410);
}

/// Multi-width agreement on random instances; run with
/// `cargo test --release -p ixon width_classes_extended -- --ignored`.
#[test]
#[ignore = "long-running; run explicitly in release mode"]
fn width_classes_extended() {
  let mut total = 0u64;
  let mut wide = 0u64;
  for seed in 0..60u64 {
    let mut rng = Rng(seed + 7_000);
    // Up to ten distinct terms, all of which may be stored, with skewed
    // use counts so the choice of the one-byte slots matters.
    let n_atoms = 8 + rng.below(2);
    let atoms: Vec<E> = (0..n_atoms)
      .map(|i| Expr::reference(i, vec![0; 1 + rng.below(4) as usize]))
      .collect();
    let mut roots: Vec<E> = Vec::new();
    for a in &atoms {
      for _ in 0..2 + rng.below(12) {
        roots.push(a.clone());
      }
    }
    if n_atoms == 8 {
      let pair = Expr::app(atoms[0].clone(), atoms[1].clone());
      for _ in 0..1 + rng.below(6) {
        roots.push(pair.clone());
      }
    }
    let c = wrap(&mut rng, roots);
    let dag = SharingDag::from_constant(&c, &limits()).unwrap();
    assert!(dag.len() <= 10);
    total += check_against_brute_force(&c);
    let (_, res) =
      normalize_constant_sharing_with_stats(&c, &limits()).unwrap();
    if res.table_terms.len() > 8 {
      wide += 1;
    }
  }
  eprintln!(
    "width classes: 60 instances agree with exhaustive table orders \
     ({wide} optima with more than 8 entries, {total} sequences visited)"
  );
  assert!(wide >= 10);
}

/// T16 -> T16 with every pruning rule and seed disabled: the full
/// width-state space (about 3.3M states) must give the same result. Run with
/// `cargo test --release -p ixon t16_without_pruning -- --ignored`.
#[test]
#[ignore = "long-running; run explicitly in release mode"]
fn t16_without_pruning() {
  let t16 = chain(16);
  let c = axiom(Expr::all(t16.clone(), t16), 1);
  let mut full = ExactSharingLimits::unbounded();
  full.lower_bound_pruning = false;
  full.materialization_bound = false;
  full.heuristic_upper_bound = false;
  full.greedy_upper_bound = false;
  let (a, ra) = normalize_constant_sharing_with_stats(&c, &full).unwrap();
  let (b, rb) = normalize_constant_sharing_with_stats(&c, &limits()).unwrap();
  eprintln!(
    "T16 unpruned: {} bytes, Q={:?}, states {} (pruned search: {} states)",
    put(&a).len(),
    ra.table_terms,
    ra.stats.states_created,
    rb.stats.states_created
  );
  assert_eq!(put(&a), put(&b));
  assert_eq!(ra.table_terms, rb.table_terms);
}

/// Whether the exhaustive oracle stays tractable on `c`: the number of
/// occurrence variants of every root with every subterm available.
fn oracle_tractable(c: &Constant, cap: u128) -> bool {
  let roots = constant_info_root_exprs(&c.info);
  let (_, terms) = oracle_ids(&roots);
  let avail: Vec<(E, u64)> =
    terms.iter().enumerate().map(|(i, t)| (t.clone(), i as u64)).collect();
  roots.iter().all(|r| variant_count(r, &avail) <= cap)
}

#[test]
fn deep_inputs_are_handled_iteratively() {
  // A 3000-binder telescope whose repeated domain is worth sharing. Its
  // height exceeds the heuristic seed's recursion guard.
  let dom = Expr::app(Expr::var(0), Expr::var(1));
  let mut e = Expr::var(0);
  for i in 0..3000 {
    let ty = if i % 2 == 0 { dom.clone() } else { Expr::sort(0) };
    e = Expr::lam(ty, e);
  }
  let c = axiom(e, 1);
  let (exact, res) =
    normalize_constant_sharing_with_stats(&c, &limits()).unwrap();
  let bytes = roundtrip(&exact);
  assert_eq!(res.stats.heuristic_len, None);
  // The innermost binder has height 2 (its domain is an App).
  assert_eq!(res.stats.height, 3001);
  assert_eq!(exact.sharing.len(), 1);
  assert_eq!(exact.sharing[0].as_ref(), dom.as_ref());
  assert_eq!(constant_len(&exact), Some(bytes.len() as u64));
  assert!(bytes.len() < put(&c).len());
}

#[test]
fn candidate_terms_apply_r1_and_r2() {
  // T2 -> T2: Prop is one byte (R2), the root occurs once (R1).
  let t2 = chain(2);
  let c = axiom(Expr::all(t2.clone(), t2), 1);
  let dag = SharingDag::from_constant(&c, &limits()).unwrap();
  assert_eq!(candidate_terms(&dag), vec![1, 2]);
  let (_, res) = normalize_constant_sharing_with_stats(&c, &limits()).unwrap();
  assert_eq!(res.stats.candidates, 2);
}

// ===========================================================================
// Uniform Share width (port of W1's Tests/Ix/SharingUniform.lean)
// ===========================================================================

use super::dict::{Hide, UniformIndex, all_costs, eval_node};
use super::search::uniform_reference_dag;
use super::uniform::set_prec;

fn uni(w: u64, roots: &[E]) -> UniformSharingResult {
  optimize_sharing_uniform(w, roots, &limits()).unwrap()
}

fn uni_reference(w: u64, roots: &[E], deg2: bool) -> (u64, Vec<u32>) {
  let lim = limits();
  let mut meter = Meter::new(&lim);
  let dag = SharingDag::from_expanded_roots(roots, &lim).unwrap();
  uniform_reference_dag(&dag, w as u8, deg2, &mut meter).unwrap()
}

/// Exact uniform-model length of a stored set (entries in any dependency
/// order see every stored descendant).
fn uniform_set_len(dag: &SharingDag, w: u64, set: &[u32]) -> u64 {
  let nodes = dag.nodes();
  let own: Vec<Len> = nodes.iter().map(Node::own_len).collect();
  let mut index = vec![None; nodes.len()];
  for &t in set {
    index[t as usize] = Some(0);
  }
  let dict = UniformIndex { index, width: w };
  let mut work = 0;
  let costs = all_costs(nodes, &own, &dict, &mut work);
  let mut total = Len::new(tag0_len(set.len() as u64));
  for &t in set {
    let hide = Hide { inner: &dict, hidden: t };
    total = total.plus(
      eval_node(
        nodes,
        &own,
        t,
        &hide,
        &|x| costs[x as usize],
        false,
        &mut work,
      )
      .0,
    );
  }
  for &r in dag.roots() {
    total = total.plus(costs[r as usize]);
  }
  total.exact().unwrap()
}

fn in_degrees(dag: &SharingDag) -> Vec<u64> {
  let mut deg = vec![0u64; dag.len()];
  for &r in dag.roots() {
    deg[r as usize] += 1;
  }
  for node in dag.nodes() {
    for &c in node.children().as_slice() {
      deg[c as usize] += 1;
    }
  }
  deg
}

/// Exhaustive canonical uniform optimum over a candidate pool: the least
/// `(model length, set)` with sets ordered by `set_prec`.
fn uniform_brute(dag: &SharingDag, w: u64, pool: &[u32]) -> (u64, Vec<u32>) {
  let mut best: Option<(u64, Vec<u32>)> = None;
  for mask in 0u64..(1u64 << pool.len()) {
    let set: Vec<u32> = (0..pool.len())
      .filter(|&i| mask >> i & 1 == 1)
      .map(|i| pool[i])
      .collect();
    let l = uniform_set_len(dag, w, &set);
    let better = match &best {
      None => true,
      Some((bl, bs)) => l < *bl || (l == *bl && set_prec(&set, bs)),
    };
    if better {
      best = Some((l, set));
    }
  }
  best.unwrap()
}

#[test]
fn uniform_witness_t2() {
  let t2 = chain(2);
  let roots = vec![Expr::all(t2.clone(), t2)];
  let u1 = uni(1, &roots);
  assert_eq!(
    (
      u1.certain_stored.clone(),
      u1.stored.clone(),
      u1.model_len,
      u1.variable_len
    ),
    (vec![2], vec![2], 11, 11)
  );
  let u2 = uni(2, &roots);
  // T2 has gain 1 at w = 2; no count bracket is within reach, so the
  // threshold is 1 and T2 is certain-stored.
  assert_eq!(
    (u2.certain_stored.clone(), u2.stored.clone(), u2.model_len),
    (vec![2], vec![2], 13)
  );
  let u3 = uni(3, &roots);
  assert_eq!(
    (u3.uncertain.clone(), u3.stored.is_empty(), u3.model_len),
    (vec![2], true, 14)
  );
  assert!(u3.certain_excluded.contains(&1));
  for w in 1..=3 {
    assert_eq!(uni(w, &roots).model_len, uni_reference(w, &roots, false).0);
  }
  assert_eq!(
    optimize_sharing_uniform(0, &roots, &limits()).unwrap_err(),
    SharingError::FormatBound(FormatBound::UniformWidth { w: 0 })
  );
  eprintln!(
    "uniform T2: w=1 {} bytes {:?}; w=2 classes cs={:?} unc={:?}; w=3 model {}",
    u1.model_len, u1.table_terms, u2.certain_stored, u2.uncertain, u3.model_len
  );
}

#[test]
fn uniform_brackets_and_atoms() {
  let atoms = |n: u64| -> Vec<E> {
    (0..n).map(|i| Expr::reference(i, vec![0])).collect()
  };
  let roots_of = |n: u64| -> Vec<E> {
    atoms(n).into_iter().flat_map(|a| [a.clone(), a]).collect()
  };
  let u = uni(1, &roots_of(128));
  assert_eq!(u.uncertain.len(), 128);
  assert_eq!(u.stored.len(), 127);
  assert!(!u.stored.contains(&0) && u.lower_bracket);
  assert_eq!(u.model_len, 642);
  let u = uni(1, &roots_of(129));
  assert_eq!(
    (u.stored.len(), u.lower_bracket, u.certain_stored.clone(), u.model_len),
    (129, false, vec![128], 648)
  );
  // Atom brute force with mixed sizes and uses.
  let atoms10: Vec<E> =
    (0..10u64).map(|i| Expr::reference(i, vec![0; (i % 3) as usize])).collect();
  let occs: Vec<u64> = (0..10).map(|i| 1 + i % 4).collect();
  let roots: Vec<E> = (0..10)
    .flat_map(|i| std::iter::repeat_n(atoms10[i].clone(), occs[i] as usize))
    .collect();
  for w in 1..=3u64 {
    let mut best = u64::MAX;
    for mask in 0u64..1024 {
      let ins = |i: usize| mask >> i & 1 == 1;
      let mut cost = tag0_len((0..10).filter(|&i| ins(i)).count() as u64);
      for i in 0..10 {
        let s = expr_len(&atoms10[i]).unwrap();
        cost += if ins(i) { s + occs[i] * w } else { occs[i] * s };
      }
      best = best.min(cost);
    }
    assert_eq!(uni(w, &roots).model_len, best, "w={w}");
  }
}

#[test]
fn uniform_in_degree_one_tie() {
  // t (a 20-byte leaf) has the single parent p = App(Var0, t), which only
  // continues two App telescopes. Storing {t} and {p} tie; the canonical
  // class (in-degree >= 2) stores p.
  let t = Expr::reference(1, vec![0; 18]);
  let p = Expr::app(Expr::var(0), t.clone());
  let roots =
    vec![Expr::app(p.clone(), Expr::var(1)), Expr::app(p, Expr::var(2))];
  let dag = SharingDag::from_expanded_roots(&roots, &limits()).unwrap();
  let id = |e: &E| dag.term_exprs().iter().position(|x| x == e).unwrap() as u32;
  let (tid_, pid) = (id(&t), id(&Expr::app(Expr::var(0), t.clone())));
  let u = uni(1, &roots);
  let len_t = uniform_set_len(&dag, 1, &[tid_]);
  let len_p = uniform_set_len(&dag, 1, &[pid]);
  eprintln!(
    "in-degree-1 tie: {{t}} {len_t} bytes, {{p}} {len_p} bytes, uniform stores {:?}",
    u.stored
  );
  assert_eq!(len_t, len_p);
  assert_eq!(u.model_len, len_p);
  assert_eq!(u.stored, vec![pid]);
  assert_eq!(uni_reference(1, &roots, false).0, u.model_len);
  // Over all R1/R2 candidates the pinned order also leaves out the smaller
  // ID (t), so here the in-degree restriction does not change the result.
  let pool = candidate_terms(&dag);
  assert_eq!(uniform_brute(&dag, 1, &pool), (len_t, vec![pid]));
}

fn gen_uniform_roots(rng: &mut Rng) -> Vec<E> {
  let mut g = ExprGen::new(rng.next(), 30);
  let leaf = |g: &mut ExprGen| g.leaf();
  match rng.below(6) {
    0 => {
      let (f, a, b) = (leaf(&mut g), leaf(&mut g), leaf(&mut g));
      let pre = if rng.pct(50) {
        Expr::app(f, a)
      } else {
        Expr::app(Expr::app(f, a), b)
      };
      (0..2 + rng.below(4))
        .map(|i| {
          let x = Expr::var(i % 3);
          if rng.pct(50) {
            Expr::app(pre.clone(), x)
          } else {
            Expr::app(Expr::app(pre.clone(), x), leaf(&mut g))
          }
        })
        .collect()
    },
    1 => {
      let e = Expr::app(Expr::var(rng.below(2)), Expr::var(1));
      (0..2 + rng.below(5))
        .map(|_| match rng.below(3) {
          0 => Expr::app(Expr::reference(1, vec![]), e.clone()),
          1 => Expr::lam(e.clone(), Expr::var(0)),
          _ => Expr::all(e.clone(), Expr::sort(0)),
        })
        .collect()
    },
    2 => {
      let pool: Vec<E> = (0..3).map(|_| leaf(&mut g)).collect();
      let c = Expr::app(
        pool[rng.below(3) as usize].clone(),
        pool[rng.below(3) as usize].clone(),
      );
      let p = match rng.below(3) {
        0 => Expr::app(c.clone(), pool[0].clone()),
        1 => Expr::all(pool[1].clone(), c.clone()),
        _ => Expr::prj(0, 1, c.clone()),
      };
      let mut roots = Vec::new();
      for _ in 0..1 + rng.below(4) {
        roots.push(Expr::app(Expr::var(2), p.clone()));
      }
      for _ in 0..1 + rng.below(4) {
        roots.push(Expr::lam(c.clone(), Expr::var(0)));
      }
      roots
    },
    3 => {
      let leaves: Vec<E> = (0..3).map(|_| leaf(&mut g)).collect();
      let mut u = Expr::app(leaves[0].clone(), leaves[1].clone());
      let mut roots = Vec::new();
      for _ in 0..3 + rng.below(6) {
        for _ in 0..1 + rng.below(2) {
          roots.push(if rng.pct(50) {
            Expr::app(Expr::var(7), u.clone())
          } else {
            Expr::all(u.clone(), Expr::sort(0))
          });
        }
        u = Expr::app(u, leaves[rng.below(3) as usize].clone());
      }
      roots.push(u);
      roots
    },
    _ => (0..1 + rng.below(3)).map(|_| g.expr(4)).collect(),
  }
}

#[test]
fn uniform_agrees_with_reference_and_brute_force() {
  let mut rng = Rng(61);
  let (mut checked, mut cs, mut ce, mut un, mut max_comp, mut with_unc) =
    (0, 0, 0, 0, 0, 0);
  let mut brute_checked = 0;
  let (mut full_checked, mut restricted_differs) = (0, 0);
  let mut attempts = 0;
  while checked < 400 {
    attempts += 1;
    assert!(attempts < 20_000);
    let roots = gen_uniform_roots(&mut rng);
    let w = [1u64, 2, 3, 5][rng.below(4) as usize];
    let dag = SharingDag::from_expanded_roots(&roots, &limits()).unwrap();
    let cands = candidate_terms(&dag);
    if cands.len() > 11 {
      continue;
    }
    let u = uni(w, &roots);
    let (rm, rq) = uni_reference(w, &roots, false);
    let (rrm, rrq) = uni_reference(w, &roots, true);
    assert_eq!((u.model_len, rrm), (rm, rm), "w={w} roots={roots:?}");
    assert!(
      u.certain_stored.iter().all(|t| rrq.contains(t)),
      "w={w} {roots:?}"
    );
    assert!(
      u.certain_excluded.iter().all(|t| !rq.contains(t) && !rrq.contains(t))
    );
    assert!(u.model_len <= u.unshared_len.unwrap());
    // The full key over the restricted class, by exhaustive subsets.
    let deg = in_degrees(&dag);
    let pool: Vec<u32> =
      cands.iter().copied().filter(|&t| deg[t as usize] >= 2).collect();
    if pool.len() <= 10 {
      assert_eq!(
        uniform_brute(&dag, w, &pool),
        (u.model_len, u.stored.clone()),
        "w={w} {roots:?}"
      );
      brute_checked += 1;
      if cands.len() <= 10 {
        let full = uniform_brute(&dag, w, &cands);
        assert_eq!(full.0, u.model_len);
        if full.1 != u.stored {
          restricted_differs += 1;
          eprintln!(
            "restricted != unrestricted canonical set: w={w} {:?} vs {:?} roots={roots:?}",
            u.stored, full.1
          );
        }
        full_checked += 1;
      }
    }
    checked += 1;
    cs += u.certain_stored.len();
    ce += u.certain_excluded.len();
    un += u.uncertain.len();
    max_comp =
      max_comp.max(u.components.iter().map(Vec::len).max().unwrap_or(0));
    if !u.uncertain.is_empty() {
      with_unc += 1;
    }
  }
  eprintln!(
    "uniform vs reference: {checked} inputs ({brute_checked} also by exhaustive subsets): \
     {cs} certain-stored, {ce} certain-excluded, {un} uncertain; {with_unc} inputs with \
     uncertain terms; largest component {max_comp}; unrestricted subsets checked \
     {full_checked}, canonical set differs from the restricted class {restricted_differs}"
  );
  assert!(with_unc > 50 && brute_checked > 300);
}

#[test]
fn uniform_t16_and_properties() {
  let t16 = chain(16);
  let roots = vec![Expr::all(t16.clone(), t16)];
  let u = uni(1, &roots);
  let (rm, _) = uni_reference(1, &roots, false);
  eprintln!(
    "uniform T16 w=1: model {} = reference {rm}; classes {}/{}/{}; {} states",
    u.model_len,
    u.certain_stored.len(),
    u.uncertain.len(),
    u.certain_excluded.len(),
    u.states_visited
  );
  assert_eq!(u.model_len, rm);
  let mut checked = 0;
  for seed in 0..200u64 {
    let c = gen_constant(seed + 70_000, 6, 16, 4);
    let w = [1u64, 2, 4][(seed % 3) as usize];
    let (n, r) = normalize_constant_sharing_uniform(w, &c, &limits()).unwrap();
    let bytes = roundtrip(&n);
    let (again, _) =
      normalize_constant_sharing_uniform(w, &n, &limits()).unwrap();
    assert_eq!(put(&again), bytes, "seed {seed}");
    let fresh = Constant::get(&mut put(&c).as_slice()).unwrap();
    let (f, _) =
      normalize_constant_sharing_uniform(w, &fresh, &limits()).unwrap();
    assert_eq!(put(&f), bytes);
    assert!(r.model_len <= r.unshared_len.unwrap());
    checked += 1;
  }
  assert_eq!(checked, 200);
}

#[test]
fn uniform_byte_level() {
  let t2 = chain(2);
  let c = axiom(Expr::all(t2.clone(), t2), 1);
  let out = normalize_constant_bytes_uniform(1, &put(&c), &limits()).unwrap();
  // At w = 1 the uniform optimum is the 17-byte exact minimum.
  assert_eq!(hex(&out), "d200009117b0b001921700170000000100");
  let out3 = normalize_constant_bytes_uniform(3, &put(&c), &limits()).unwrap();
  assert_eq!(out3, put(&c));
  assert!(matches!(
    normalize_constant_bytes_uniform(0, &put(&c), &limits()),
    Err(NormalizeBytesError::Sharing(SharingError::FormatBound(_)))
  ));
}

// ===========================================================================
// Tiered construction (port of W1's Tests/Ix/SharingTiered.lean)
// ===========================================================================

const LAYOUTS: [ShareLayout; 2] = [ShareLayout::Tag4, ShareLayout::TagN];

#[test]
fn tiered_layout_widths() {
  let at = [
    7u64,
    8,
    1031,
    1032,
    66567,
    66568,
    66568 + (1 << 32) - 1,
    66568 + (1 << 32),
  ];
  let got: Vec<u64> =
    at.iter().map(|&i| ShareLayout::TagN.width_at(i)).collect();
  assert_eq!(got, vec![1, 2, 2, 3, 3, 5, 5, 9]);
  assert_eq!(
    (TAGN_RUNG2_END, TAGN_RUNG3_END, TAGN_RUNG4_END),
    (1032, 66568, 66568 + (1 << 32))
  );
  assert_eq!(ShareLayout::TagN.width_at(u64::MAX), 9);
  let t4 = ShareLayout::Tag4;
  assert_eq!(
    (t4.uniform_width(8), t4.uniform_width(256), t4.uniform_width(257)),
    (1, 2, 3)
  );
  let tn = ShareLayout::TagN;
  assert_eq!((tn.uniform_width(1032), tn.uniform_width(1033)), (2, 3));
}

#[test]
fn tiered_fixtures() {
  let t2 = chain(2);
  let w2 = axiom(Expr::all(t2.clone(), t2), 1);
  let t16 = chain(16);
  let w16 = axiom(Expr::all(t16.clone(), t16), 1);
  let (nine, hot) = nine_ref_fixture();
  for l in LAYOUTS {
    let (n, _) = normalize_constant_sharing_tiered(l, &w2, &limits()).unwrap();
    assert_eq!(
      hex(&roundtrip(&n)),
      "d200009117b0b001921700170000000100",
      "{l:?}"
    );
    let (n, _) = normalize_constant_sharing_tiered(l, &w16, &limits()).unwrap();
    assert_eq!(roundtrip(&n).len(), 46, "{l:?}");
    let (n, r) =
      normalize_constant_sharing_tiered(l, &nine, &limits()).unwrap();
    let pos = n.sharing.iter().position(|e| e == &hot).unwrap();
    eprintln!(
      "tiered nine refs {l:?}: {} bytes, w={}, first tier {:?}, phase-1 layout {}, final {}, kept phase-1 order {}",
      roundtrip(&n).len(),
      r.stats.w,
      r.stats.first_tier,
      r.stats.phase1_layout_bytes,
      r.stats.phase3_layout_bytes,
      r.stats.kept_phase1_order
    );
    assert_eq!(roundtrip(&n).len(), 578);
    assert_eq!(r.stats.w, 2);
    assert!(r.stats.first_tier.contains(&2) && pos < 8);
  }
}

/// A heavy parent over two lighter children next to more than eight atoms
/// used a few times each (W1's `genHeavyParent`).
fn gen_heavy_parent(rng: &mut Rng) -> Vec<E> {
  let n_atoms = 9 + rng.below(4);
  let atoms: Vec<E> = (0..n_atoms)
    .map(|j| Expr::reference(j + 10, vec![0; (1 + j % 3) as usize]))
    .collect();
  let c1 = Expr::reference(1, vec![0, 0, 0]);
  let c2 = Expr::reference(2, vec![0, 0, 1]);
  let parent = if rng.pct(50) {
    Expr::app(c1.clone(), c2.clone())
  } else {
    Expr::all(c1.clone(), c2.clone())
  };
  let mut roots = Vec::new();
  for a in &atoms {
    for _ in 0..2 + rng.below(3) {
      roots.push(a.clone());
    }
  }
  for _ in 0..8 + rng.below(15) {
    roots.push(Expr::app(Expr::var(1), parent.clone()));
  }
  roots.push(c1);
  roots.push(c2);
  roots
}

#[test]
fn tiered_allocation_properties() {
  let mut rng = Rng(71);
  let (mut checked, mut changed, mut saved, mut kept) = (0, 0, 0, 0);
  for i in 0..120u64 {
    let c = if i % 2 == 0 {
      let roots = gen_heavy_parent(&mut rng);
      wrap(&mut rng, roots)
    } else {
      gen_constant(i + 80_000, 6, 30, 5)
    };
    for l in LAYOUTS {
      let (n, r) = normalize_constant_sharing_tiered(l, &c, &limits()).unwrap();
      let s = &r.stats;
      assert!(s.phase3_layout_bytes <= s.phase1_layout_bytes, "case {i} {l:?}");
      assert!(s.final_ref_cost <= s.phase1_ref_cost, "case {i} {l:?}");
      assert_eq!(
        roundtrip(&n).len() as u64,
        constant_fixed_len(&c).unwrap() + r.variable_len
      );
      if l == ShareLayout::Tag4 {
        assert_eq!(r.model_len, r.variable_len);
      }
      let (again, _) =
        normalize_constant_sharing_tiered(l, &n, &limits()).unwrap();
      assert_eq!(put(&again), put(&n), "case {i} {l:?} not idempotent");
      checked += 1;
      if s.final_ref_cost < s.phase1_ref_cost {
        changed += 1;
      }
      if s.savings > 0 {
        saved += 1;
      }
      if s.kept_phase1_order {
        kept += 1;
      }
    }
  }
  eprintln!(
    "tiered: {checked} runs; allocation lowered the reference cost in {changed}, \
     positive savings in {saved}, phase-1 order kept in {kept}"
  );
  assert!(checked == 240 && changed > 0);
}

/// Brute force over all subsets: dependency-closed, at most `cap` terms,
/// maximum weight, ties by the greatest indicator vector in the order
/// (weight descending, ID ascending).
fn brute_tier(
  n: usize,
  weight: &[u64],
  deps: &[Vec<u32>],
  cap: usize,
) -> Vec<u32> {
  let mut items: Vec<u32> = (0..n as u32).collect();
  items.sort_by(|&a, &b| {
    weight[b as usize].cmp(&weight[a as usize]).then(a.cmp(&b))
  });
  let mut best: Option<(u64, Vec<bool>)> = None;
  for mask in 0u32..(1 << n) {
    let ins = |t: u32| mask >> t & 1 == 1;
    let members: Vec<u32> = (0..n as u32).filter(|&t| ins(t)).collect();
    if members.len() > cap
      || !members.iter().all(|&t| deps[t as usize].iter().all(|&d| ins(d)))
    {
      continue;
    }
    let wsum: u64 = members.iter().map(|&t| weight[t as usize]).sum();
    let vec: Vec<bool> = items.iter().map(|&t| ins(t)).collect();
    let better = match &best {
      None => true,
      Some((bw, bv)) => {
        wsum > *bw
          || (wsum == *bw
            && vec
              .iter()
              .zip(bv)
              .find(|(a, b)| a != b)
              .is_some_and(|(a, _)| *a))
      },
    };
    if better {
      best = Some((wsum, vec));
    }
  }
  let (_, vec) = best.unwrap();
  let mut out: Vec<u32> =
    items.iter().zip(&vec).filter(|(_, b)| **b).map(|(t, _)| *t).collect();
  out.sort_unstable();
  out
}

#[test]
fn tiered_first_tier_matches_brute_force() {
  let mut rng = Rng(73);
  for case in 0..300 {
    let n = 1 + rng.below(12) as usize;
    let mut weight = Vec::new();
    let mut deps: Vec<Vec<u32>> = Vec::new();
    for t in 0..n {
      weight.push(1 + rng.below(4));
      deps.push((0..t as u32).filter(|_| rng.below(4) == 0).collect());
    }
    let cap = 8.min(1 + rng.below(n as u64) as usize);
    let wmap: FxHashMap<u32, u64> =
      (0..n).map(|t| (t as u32, weight[t])).collect();
    let dmap: FxHashMap<u32, Vec<u32>> =
      (0..n).map(|t| (t as u32, deps[t].clone())).collect();
    let stored: Vec<u32> = (0..n as u32).collect();
    let (s, _) = first_tier(&stored, &wmap, &dmap, cap, &limits()).unwrap();
    assert_eq!(
      s,
      brute_tier(n, &weight, &deps, cap),
      "case {case}: n={n} cap={cap} w={weight:?} deps={deps:?}"
    );
  }
}

#[test]
fn tiered_byte_level() {
  let t2 = chain(2);
  let c = axiom(Expr::all(t2.clone(), t2), 1);
  for l in LAYOUTS {
    let out = normalize_constant_bytes_tiered(l, &put(&c), &limits()).unwrap();
    assert_eq!(hex(&out), "d200009117b0b001921700170000000100");
  }
  assert_eq!(
    (
      ShareLayout::from_code(0),
      ShareLayout::from_code(1),
      ShareLayout::from_code(2)
    ),
    (Some(ShareLayout::Tag4), Some(ShareLayout::TagN), None)
  );
}

// ---------------------------------------------------------------------------
// Reclassifying branch and bound vs the subset enumeration
// ---------------------------------------------------------------------------

/// `mk a1 ... an`-style prefix chains: `u_k = u_{k-1} a_k`, each prefix also
/// used once as the head of a longer spine with other arguments, plus a few
/// repeated arguments.
fn gen_prefix_chain(rng: &mut Rng) -> Vec<E> {
  let mut g = ExprGen::new(rng.next(), 0);
  let pool: Vec<E> = (0..4).map(|_| g.leaf()).collect();
  let len = 3 + rng.below(14);
  let mut u = pool[0].clone();
  let mut roots = Vec::new();
  for k in 0..len {
    let a = if rng.below(3) == 0 {
      rng.pick(&pool).clone()
    } else {
      Expr::var(k % 5)
    };
    u = Expr::app(u, a);
    let mut x = Expr::app(u.clone(), Expr::sort(1));
    for _ in 0..rng.below(4) {
      x = Expr::app(x, rng.pick(&pool).clone());
    }
    roots.push(if rng.below(2) == 0 { x } else { Expr::all(x, Expr::sort(0)) });
  }
  roots.push(u);
  roots
}

/// Nested binder telescopes whose prefixes and bodies repeat.
fn gen_telescopes(rng: &mut Rng) -> Vec<E> {
  let mut g = ExprGen::new(rng.next(), 0);
  let pool: Vec<E> = (0..4).map(|_| g.leaf()).collect();
  let mut body = pool[0].clone();
  let mut roots = Vec::new();
  for _ in 0..2 + rng.below(10) {
    let ty = rng.pick(&pool).clone();
    body = match rng.below(3) {
      0 => Expr::lam_contract(binder_contract(rng), ty, body),
      1 => Expr::all(ty, body),
      _ => Expr::app(body, ty),
    };
    if rng.below(2) == 0 {
      roots.push(Expr::app(Expr::var(3), body.clone()));
    }
  }
  roots.push(body);
  roots
}

/// Long App/binder spines, each used twice.
fn gen_spines(rng: &mut Rng) -> Vec<E> {
  let mut g = ExprGen::new(rng.next(), 0);
  let mut roots = Vec::new();
  for _ in 0..1 + rng.below(3) {
    let mut e = g.leaf();
    for _ in 0..5 + rng.below(40) {
      let x = g.leaf();
      e = match rng.below(4) {
        0 | 1 => Expr::app(e, x),
        2 => Expr::lam_contract(binder_contract(rng), x, e),
        _ => Expr::all(x, e),
      };
    }
    roots.push(e.clone());
    roots.push(Expr::app(e.clone(), e));
  }
  roots
}

fn gen_search_roots(rng: &mut Rng) -> Vec<E> {
  match rng.below(7) {
    0 => gen_prefix_chain(rng),
    1 => gen_telescopes(rng),
    2 | 3 => gen_spines(rng),
    4 => gen_uniform_roots(rng),
    _ => {
      let mut g = ExprGen::new(rng.next(), 40);
      (0..1 + rng.below(5)).map(|_| g.expr(5)).collect()
    },
  }
}

fn subset_reference_limits() -> ExactSharingLimits {
  ExactSharingLimits {
    uniform_subset_search: true,
    max_states: 1 << 16,
    ..limits()
  }
}

/// The reclassifying branch and bound returns exactly what the subset
/// enumeration returns (same set, so the same tie-break, and the same
/// output), on inputs with larger uncertain components.
#[test]
fn uniform_branch_and_bound_matches_subset_enumeration() {
  let mut rng = Rng(71);
  let reference = subset_reference_limits();
  let (mut checked, mut skipped, mut max_comp) = (0, 0, 0);
  for i in 0..4000 {
    if checked >= 600 {
      break;
    }
    let roots = gen_search_roots(&mut rng);
    let w = [1u64, 2, 3, 5][rng.below(4) as usize];
    let u = optimize_sharing_uniform(w, &roots, &limits())
      .unwrap_or_else(|e| panic!("case {i} w={w}: {e:?} roots={roots:?}"));
    let comp = u.components.iter().map(Vec::len).max().unwrap_or(0);
    if comp < 2 {
      continue;
    }
    match optimize_sharing_uniform(w, &roots, &reference) {
      Ok(r) => {
        assert_eq!(
          (&u.stored, u.model_len, u.lower_bracket),
          (&r.stored, r.model_len, r.lower_bracket),
          "case {i} w={w} roots={roots:?}"
        );
        assert_eq!(
          (&u.table_terms, &u.sharing, &u.roots),
          (&r.table_terms, &r.sharing, &r.roots)
        );
      },
      Err(SharingError::ResourceExhausted(_)) => skipped += 1,
      Err(e) => panic!("case {i} w={w}: subset enumeration error {e:?}"),
    }
    checked += 1;
    max_comp = max_comp.max(comp);
  }
  eprintln!(
    "uniform branch and bound vs subset enumeration: {checked} inputs with a \
     component of >= 2 uncertain terms, largest component {max_comp}, \
     {skipped} skipped where the enumeration exceeded 2^16 states"
  );
  assert_eq!(checked, 600);
  assert!(checked - skipped >= 400);
}

/// Search agreement across the 128-entry table-count bracket: 120 one-byte
/// atoms used twice (uncertain, gain 1) plus an App prefix chain.
#[test]
fn uniform_branch_and_bound_across_a_bracket() {
  let mut roots = Vec::new();
  for i in 0..120 {
    let a = Expr::reference(i, vec![0]);
    roots.push(a.clone());
    roots.push(a);
  }
  roots.extend(gen_prefix_chain(&mut Rng(5)));
  let reference =
    ExactSharingLimits { uniform_subset_search: true, ..limits() };
  for w in 1..=3 {
    let u = optimize_sharing_uniform(w, &roots, &limits()).unwrap();
    let r = optimize_sharing_uniform(w, &roots, &reference).unwrap();
    assert_eq!((&u.stored, u.model_len), (&r.stored, r.model_len), "w={w}");
  }
}

// ---------------------------------------------------------------------------
// Forced phase-1 width (experiment hook)
// ---------------------------------------------------------------------------

/// The experiment hook at the `K`-based width is the canonical
/// construction; at any other width it is a valid encoding of the same
/// constant, priced and serialized consistently.
#[test]
fn tiered_at_width_hook() {
  let mut rng = Rng(73);
  for i in 0..60u64 {
    let c = if i % 2 == 0 {
      let roots = gen_heavy_parent(&mut rng);
      wrap(&mut rng, roots)
    } else {
      gen_constant(i + 90_000, 6, 30, 5)
    };
    for l in LAYOUTS {
      let (n, r) = normalize_constant_sharing_tiered(l, &c, &limits()).unwrap();
      let wk = l.uniform_width(r.stats.candidate_count);
      for w in 1..=3 {
        let (m, s) =
          normalize_constant_sharing_tiered_at_width(l, &c, &limits(), w)
            .unwrap();
        assert_eq!(s.stats.w, w);
        assert_eq!(
          roundtrip(&m).len() as u64,
          constant_fixed_len(&c).unwrap() + s.variable_len
        );
        assert_eq!(
          put(&unshared(&m)),
          put(&unshared(&c)),
          "case {i} {l:?} w={w}: different constant"
        );
        if w == wk {
          assert_eq!((put(&m), s.model_len), (put(&n), r.model_len));
        }
      }
    }
  }
}

/// The "all candidates" experiment hook stores exactly the `K` candidates
/// and encodes the same constant.
#[test]
fn tiered_all_candidates_hook() {
  let mut rng = Rng(79);
  for i in 0..60u64 {
    let c = if i % 2 == 0 {
      let roots = gen_heavy_parent(&mut rng);
      wrap(&mut rng, roots)
    } else {
      gen_constant(i + 95_000, 6, 30, 5)
    };
    for l in LAYOUTS {
      let (m, s) = normalize_constant_sharing_tiered_with(
        l,
        &c,
        &limits(),
        Phase1Choice::AllCandidates,
      )
      .unwrap();
      assert_eq!(s.stats.w, 0);
      assert_eq!(s.table_terms.len() as u64, s.stats.candidate_count);
      assert_eq!(
        roundtrip(&m).len() as u64,
        constant_fixed_len(&c).unwrap() + s.variable_len
      );
      assert_eq!(put(&unshared(&m)), put(&unshared(&c)), "case {i} {l:?}");
    }
  }
}
