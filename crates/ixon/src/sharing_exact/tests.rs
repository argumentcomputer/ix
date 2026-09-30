//! Tests for exact minimum sharing: serializer-length helpers, structural
//! IDs, expansion validation, the fixed-dictionary recurrence against
//! enumeration, the width-state search against the tiny exhaustive oracle,
//! the §2 fixtures, representation independence and resource behavior.

#![allow(clippy::cast_possible_truncation)]

use std::collections::HashMap;
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
  for seed in 0..150 {
    let c = gen_constant(seed + 20_000, 4, 45, 6);
    let h = heuristic(&c);
    let u = unshared(&c);
    let exact = match normalize_constant_sharing(&c, &limits()) {
      Ok(x) => x,
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
    "never-worse: {} solved, saved {} bytes vs heuristic and {} vs unshared, {} resource errors",
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
