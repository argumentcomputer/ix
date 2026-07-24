//! quickcheck property tests for the Ixon text syntax.
//!
//! Generators produce arbitrary *valid* ASTs (the invariants the parser
//! guarantees: nonempty spines, name-or-hash references, leading `Str`
//! name components, …) and the properties enforce, over the whole AST
//! space:
//!
//! - the canonical-printer fixpoint `print ∘ parse ∘ print = print`
//!   (spans differ across a roundtrip, so equality lives at the text
//!   level);
//! - totality and determinism of parsing on arbitrary and mutated
//!   input (R2: never a panic, always a value or a structured error);
//! - the metering claim documented on [`Limits`]: the grammar has no
//!   ε-productions, so node count is bounded by printed byte length.
//!
//! Shrinking is implemented for real: term shrinkers walk to subterms
//! and minimal replacements (`Prop`), so failures arrive minimized.

// `#[quickcheck]` requires owned arguments (crate convention, cf.
// expr.rs / constant.rs).
#![allow(clippy::needless_pass_by_value)]

use bignat::Nat;
use ix_common::env::{BinderInfo, NameComponent};
use num_bigint::BigUint;
use quickcheck::{Arbitrary, Gen};
use quickcheck_macros::quickcheck;

use crate::syntax::ast::{
  AxiomDecl, BinderGroup, BinderName, ConstRef, CtorDecl, Decl, DefDecl, DefKw,
  File, HashRef, ImportDecl, IndDecl, MainExpr, Modifiers, PrjDecl, PrjKind,
  QuotDecl, QuotKindKw, RecrDecl, RuleDecl, SName, SortKind, Span, Term,
  UParam, UnivExpr, count_term_nodes,
};
use crate::syntax::{Limits, parse_file, parse_term, print_file, print_term};

// ---------------------------------------------------------------------------
// Generators
// ---------------------------------------------------------------------------

fn pick(g: &mut Gen, n: usize) -> usize {
  usize::arbitrary(g) % n
}

fn small_u64(g: &mut Gen, n: u64) -> u64 {
  u64::arbitrary(g) % n
}

/// Component pool: bare identifiers, unicode, primes/`!?`, reserved
/// words and digit-strings (which must print `«…»`-escaped), and a
/// spaced string (ditto).
const STR_POOL: &[&str] = &[
  "x",
  "y",
  "foo",
  "bar'",
  "h!?",
  "α",
  "ℕ",
  "add_comm",
  "Nat",
  "Except",
  "def",
  "weird name",
  "123",
  "max",
];

/// Leading components must be `Str` and are drawn from the same pool
/// (escaping makes even `"123"` legal in leading position).
fn arb_str_component(g: &mut Gen) -> NameComponent {
  NameComponent::Str(STR_POOL[pick(g, STR_POOL.len())].to_string())
}

fn arb_component(g: &mut Gen) -> NameComponent {
  if pick(g, 5) == 0 {
    NameComponent::Num(Nat(BigUint::from(small_u64(g, 1000))))
  } else {
    arb_str_component(g)
  }
}

fn arb_sname(g: &mut Gen) -> SName {
  let mut parts = vec![arb_str_component(g)];
  for _ in 0..pick(g, 3) {
    parts.push(arb_component(g));
  }
  SName { parts, span: Span::default() }
}

const HEX: &[u8] = b"0123456789abcdef";

fn arb_hex(g: &mut Gen, len: usize) -> String {
  (0..len).map(|_| HEX[pick(g, 16)] as char).collect()
}

fn arb_hash(g: &mut Gen) -> HashRef {
  let len = 4 + pick(g, 61);
  HashRef { hex: arb_hex(g, len), span: Span::default() }
}

/// Universe variables: `Str` components only (a `Num` universe
/// variable prints as a numeral and reparses as a literal). The pool
/// includes `"max"`, which must print escaped in universe positions.
fn arb_uvar(g: &mut Gen) -> NameComponent {
  NameComponent::Str(
    ["u", "v", "w", "max", "weird name"][pick(g, 5)].to_string(),
  )
}

fn arb_univ(g: &mut Gen, depth: usize) -> UnivExpr {
  let sp = Span::default();
  if depth == 0 {
    return match pick(g, 2) {
      0 => UnivExpr::Nat(small_u64(g, 4), sp),
      _ => UnivExpr::Var(arb_uvar(g), sp),
    };
  }
  match pick(g, 5) {
    0 => UnivExpr::Nat(small_u64(g, 4), sp),
    1 => UnivExpr::Var(arb_uvar(g), sp),
    2 => {
      UnivExpr::Add(Box::new(arb_univ(g, depth - 1)), 1 + small_u64(g, 3), sp)
    },
    3 => UnivExpr::Max(
      Box::new(arb_univ(g, depth - 1)),
      Box::new(arb_univ(g, depth - 1)),
      sp,
    ),
    _ => UnivExpr::IMax(
      Box::new(arb_univ(g, depth - 1)),
      Box::new(arb_univ(g, depth - 1)),
      sp,
    ),
  }
}

fn arb_cref(g: &mut Gen) -> ConstRef {
  let name = if pick(g, 4) > 0 { Some(arb_sname(g)) } else { None };
  let hash =
    if name.is_none() || pick(g, 4) == 0 { Some(arb_hash(g)) } else { None };
  let levels = if pick(g, 4) == 0 {
    Some((0..1 + pick(g, 2)).map(|_| arb_univ(g, 1)).collect())
  } else {
    None
  };
  ConstRef { name, hash, levels, span: Span::default() }
}

fn arb_binder_name(g: &mut Gen) -> BinderName {
  if pick(g, 6) == 0 {
    BinderName::Anon(Span::default())
  } else {
    BinderName::Ident(arb_str_component(g), Span::default())
  }
}

fn arb_binder(g: &mut Gen, depth: usize) -> BinderGroup {
  let info = BinderInfo::arbitrary(g);
  let names = if info == BinderInfo::InstImplicit && pick(g, 2) == 0 {
    vec![] // unnamed instance binder `[T]`
  } else {
    (0..1 + pick(g, 2)).map(|_| arb_binder_name(g)).collect()
  };
  BinderGroup { info, names, ty: arb_term(g, depth), span: Span::default() }
}

fn arb_sort(g: &mut Gen) -> SortKind {
  match pick(g, 4) {
    0 => SortKind::Prop,
    1 => SortKind::Type(None),
    2 => SortKind::Type(Some(arb_univ(g, 1))),
    _ => SortKind::Sort(arb_univ(g, 1)),
  }
}

fn arb_term(g: &mut Gen, depth: usize) -> Term {
  let sp = Span::default();
  if depth == 0 {
    return match pick(g, 6) {
      0 => Term::NatLit(Nat(BigUint::from(u64::arbitrary(g))), sp),
      1 => Term::StrLit(String::arbitrary(g), sp),
      2 => Term::Sort(arb_sort(g), sp),
      _ => Term::Ref(arb_cref(g)),
    };
  }
  let d = depth - 1;
  match pick(g, 10) {
    0 => Term::Sort(arb_sort(g), sp),
    1 | 2 => Term::App {
      head: Box::new(arb_term(g, d)),
      args: (0..1 + pick(g, 3)).map(|_| arb_term(g, d)).collect(),
      span: sp,
    },
    3 | 4 => Term::Fun {
      binders: (0..1 + pick(g, 2)).map(|_| arb_binder(g, d)).collect(),
      body: Box::new(arb_term(g, d)),
      span: sp,
    },
    5 => Term::Pi {
      binders: (0..1 + pick(g, 2)).map(|_| arb_binder(g, d)).collect(),
      body: Box::new(arb_term(g, d)),
      span: sp,
    },
    6 => Term::Arrow {
      dom: Box::new(arb_term(g, d)),
      cod: Box::new(arb_term(g, d)),
      span: sp,
    },
    7 => Term::Let {
      non_dep: bool::arbitrary(g),
      name: arb_binder_name(g),
      ty: Box::new(arb_term(g, d)),
      val: Box::new(arb_term(g, d)),
      body: Box::new(arb_term(g, d)),
      span: sp,
    },
    8 => Term::Proj {
      type_ref: arb_cref(g),
      idx: small_u64(g, 8),
      val: Box::new(arb_term(g, d)),
      span: sp,
    },
    _ => Term::Ref(arb_cref(g)),
  }
}

fn arb_uparams(g: &mut Gen) -> Vec<UParam> {
  (0..pick(g, 3))
    .map(|_| UParam { name: arb_uvar(g), span: Span::default() })
    .collect()
}

fn arb_modifiers(g: &mut Gen, kw: DefKw) -> Modifiers {
  // The parser rejects `partial` on non-`def` and the unsafe+partial
  // combination.
  match pick(g, 4) {
    0 => Modifiers { unsafe_: true, partial_: false },
    1 if kw == DefKw::Def => Modifiers { unsafe_: false, partial_: true },
    _ => Modifiers::default(),
  }
}

fn arb_def(g: &mut Gen, depth: usize) -> DefDecl {
  let kw = *g.choose(&[DefKw::Def, DefKw::Theorem, DefKw::Opaque]).unwrap();
  DefDecl {
    kw,
    mods: arb_modifiers(g, kw),
    name: if pick(g, 4) > 0 { Some(arb_sname(g)) } else { None },
    uparams: arb_uparams(g),
    ty: arb_term(g, depth),
    value: arb_term(g, depth),
    span: Span::default(),
  }
}

fn arb_ind(g: &mut Gen, depth: usize) -> IndDecl {
  IndDecl {
    unsafe_: bool::arbitrary(g),
    name: if pick(g, 4) > 0 { Some(arb_sname(g)) } else { None },
    uparams: arb_uparams(g),
    params: small_u64(g, 4),
    indices: small_u64(g, 4),
    ty: arb_term(g, depth),
    ctors: (0..pick(g, 3))
      .map(|_| CtorDecl {
        name: if pick(g, 4) > 0 { Some(arb_sname(g)) } else { None },
        params: small_u64(g, 4),
        fields: small_u64(g, 4),
        ty: arb_term(g, depth),
        span: Span::default(),
      })
      .collect(),
    span: Span::default(),
  }
}

fn arb_recr(g: &mut Gen, depth: usize) -> RecrDecl {
  RecrDecl {
    unsafe_: bool::arbitrary(g),
    name: if pick(g, 4) > 0 { Some(arb_sname(g)) } else { None },
    uparams: arb_uparams(g),
    params: small_u64(g, 4),
    indices: small_u64(g, 4),
    motives: 1 + small_u64(g, 2),
    minors: small_u64(g, 4),
    k: bool::arbitrary(g),
    ty: arb_term(g, depth),
    rules: (0..pick(g, 3))
      .map(|_| RuleDecl {
        fields: small_u64(g, 4),
        rhs: arb_term(g, depth),
        span: Span::default(),
      })
      .collect(),
    span: Span::default(),
  }
}

fn arb_decl(g: &mut Gen, depth: usize) -> Decl {
  match pick(g, 8) {
    0 | 1 => Decl::Def(arb_def(g, depth)),
    2 => Decl::Axiom(AxiomDecl {
      unsafe_: bool::arbitrary(g),
      name: if pick(g, 4) > 0 { Some(arb_sname(g)) } else { None },
      uparams: arb_uparams(g),
      ty: arb_term(g, depth),
      span: Span::default(),
    }),
    3 => Decl::Quot(QuotDecl {
      kind: *g
        .choose(&[
          QuotKindKw::Type,
          QuotKindKw::Ctor,
          QuotKindKw::Lift,
          QuotKindKw::Ind,
        ])
        .unwrap(),
      name: if pick(g, 4) > 0 { Some(arb_sname(g)) } else { None },
      uparams: arb_uparams(g),
      ty: arb_term(g, depth),
      span: Span::default(),
    }),
    4 => Decl::Ind(arb_ind(g, depth)),
    5 => Decl::Recr(arb_recr(g, depth)),
    6 => {
      let members = (0..1 + pick(g, 2))
        .map(|_| match pick(g, 3) {
          0 => Decl::Ind(arb_ind(g, depth)),
          1 => Decl::Recr(arb_recr(g, depth)),
          _ => Decl::Def(arb_def(g, depth)),
        })
        .collect();
      Decl::Mutual(members, Span::default())
    },
    _ => {
      let kind = *g
        .choose(&[PrjKind::DPrj, PrjKind::IPrj, PrjKind::CPrj, PrjKind::RPrj])
        .unwrap();
      Decl::Prj(PrjDecl {
        kind,
        name: if pick(g, 4) > 0 { Some(arb_sname(g)) } else { None },
        block: arb_hash(g),
        idx: small_u64(g, 8),
        cidx: (kind == PrjKind::CPrj).then(|| small_u64(g, 8)),
        span: Span::default(),
      })
    },
  }
}

fn arb_import(g: &mut Gen) -> ImportDecl {
  ImportDecl {
    prefix: if pick(g, 2) == 0 { Some(arb_sname(g)) } else { None },
    hash: HashRef { hex: arb_hex(g, 64), span: Span::default() },
    span: Span::default(),
  }
}

fn arb_file(g: &mut Gen) -> File {
  File {
    version: crate::syntax::VERSION,
    imports: (0..pick(g, 3)).map(|_| arb_import(g)).collect(),
    decls: (0..pick(g, 4)).map(|_| arb_decl(g, 2)).collect(),
    main: (pick(g, 3) == 0).then(|| MainExpr {
      value: arb_term(g, 2),
      ty: arb_term(g, 2),
      span: Span::default(),
    }),
    span: Span::default(),
  }
}

// ---------------------------------------------------------------------------
// Shrinking
// ---------------------------------------------------------------------------

fn prop_leaf() -> Term {
  Term::Sort(SortKind::Prop, Span::default())
}

fn is_prop_leaf(t: &Term) -> bool {
  matches!(t, Term::Sort(SortKind::Prop, _))
}

/// Immediate subterms plus minimal replacements — every candidate is
/// strictly smaller by node count or is the `Prop` leaf (which shrinks
/// to nothing), so shrinking terminates.
fn shrink_term(t: &Term) -> Vec<Term> {
  let mut out = Vec::new();
  if !is_prop_leaf(t) {
    out.push(prop_leaf());
  }
  match t {
    Term::App { head, args, .. } => {
      out.push((**head).clone());
      out.extend(args.iter().cloned());
      if args.len() > 1 {
        for i in 0..args.len() {
          let mut a = args.clone();
          a.remove(i);
          out.push(Term::App {
            head: head.clone(),
            args: a,
            span: Span::default(),
          });
        }
      }
    },
    Term::Fun { binders, body, .. } | Term::Pi { binders, body, .. } => {
      out.push((**body).clone());
      out.extend(binders.iter().map(|b| b.ty.clone()));
    },
    Term::Arrow { dom, cod, .. } => {
      out.push((**dom).clone());
      out.push((**cod).clone());
    },
    Term::Let { ty, val, body, .. } => {
      out.push((**ty).clone());
      out.push((**val).clone());
      out.push((**body).clone());
    },
    Term::Proj { val, .. } => out.push((**val).clone()),
    Term::Ref(r) => {
      if r.levels.is_some() {
        out.push(Term::Ref(ConstRef { levels: None, ..r.clone() }));
      }
      if r.name.is_some() && r.hash.is_some() {
        out.push(Term::Ref(ConstRef { hash: None, ..r.clone() }));
      }
    },
    Term::StrLit(s, _) if !s.is_empty() => {
      out.push(Term::StrLit(String::new(), Span::default()));
    },
    _ => {},
  }
  out
}

fn shrink_decl(d: &Decl) -> Vec<Decl> {
  let mut out = Vec::new();
  match d {
    Decl::Def(x) => {
      for ty in shrink_term(&x.ty) {
        out.push(Decl::Def(DefDecl { ty, ..x.clone() }));
      }
      for value in shrink_term(&x.value) {
        out.push(Decl::Def(DefDecl { value, ..x.clone() }));
      }
    },
    Decl::Axiom(x) => {
      for ty in shrink_term(&x.ty) {
        out.push(Decl::Axiom(AxiomDecl { ty, ..x.clone() }));
      }
    },
    Decl::Quot(x) => {
      for ty in shrink_term(&x.ty) {
        out.push(Decl::Quot(QuotDecl { ty, ..x.clone() }));
      }
    },
    Decl::Ind(x) => {
      for i in 0..x.ctors.len() {
        let mut c = x.ctors.clone();
        c.remove(i);
        out.push(Decl::Ind(IndDecl { ctors: c, ..x.clone() }));
      }
      for ty in shrink_term(&x.ty) {
        out.push(Decl::Ind(IndDecl { ty, ..x.clone() }));
      }
    },
    Decl::Recr(x) => {
      for i in 0..x.rules.len() {
        let mut r = x.rules.clone();
        r.remove(i);
        out.push(Decl::Recr(RecrDecl { rules: r, ..x.clone() }));
      }
      for ty in shrink_term(&x.ty) {
        out.push(Decl::Recr(RecrDecl { ty, ..x.clone() }));
      }
    },
    Decl::Mutual(members, _) => {
      out.extend(members.iter().cloned());
      if members.len() > 1 {
        for i in 0..members.len() {
          let mut m = members.clone();
          m.remove(i);
          out.push(Decl::Mutual(m, Span::default()));
        }
      }
      for (i, member) in members.iter().enumerate() {
        for s in shrink_decl(member) {
          if matches!(s, Decl::Def(_) | Decl::Ind(_) | Decl::Recr(_)) {
            let mut m = members.clone();
            m[i] = s;
            out.push(Decl::Mutual(m, Span::default()));
          }
        }
      }
    },
    Decl::Prj(_) => {},
  }
  out
}

#[derive(Debug, Clone)]
struct ArbTerm(Term);

impl Arbitrary for ArbTerm {
  fn arbitrary(g: &mut Gen) -> Self {
    ArbTerm(arb_term(g, 4))
  }

  fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
    Box::new(shrink_term(&self.0).into_iter().map(ArbTerm))
  }
}

#[derive(Debug, Clone)]
struct ArbFile(File);

impl Arbitrary for ArbFile {
  fn arbitrary(g: &mut Gen) -> Self {
    ArbFile(arb_file(g))
  }

  fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
    let f = &self.0;
    let mut out = Vec::new();
    for i in 0..f.imports.len() {
      let mut imports = f.imports.clone();
      imports.remove(i);
      out.push(File { imports, ..f.clone() });
    }
    for i in 0..f.decls.len() {
      let mut decls = f.decls.clone();
      decls.remove(i);
      out.push(File { decls, ..f.clone() });
    }
    if f.main.is_some() {
      out.push(File { main: None, ..f.clone() });
    }
    if let Some(m) = &f.main {
      for v in shrink_term(&m.value) {
        out.push(File {
          main: Some(MainExpr { value: v, ..m.clone() }),
          ..f.clone()
        });
      }
      for t in shrink_term(&m.ty) {
        out.push(File {
          main: Some(MainExpr { ty: t, ..m.clone() }),
          ..f.clone()
        });
      }
    }
    for (i, d) in f.decls.iter().enumerate() {
      for s in shrink_decl(d) {
        let mut decls = f.decls.clone();
        decls[i] = s;
        out.push(File { decls, ..f.clone() });
      }
    }
    Box::new(out.into_iter().map(ArbFile))
  }
}

// ---------------------------------------------------------------------------
// Properties
// ---------------------------------------------------------------------------

fn lims() -> Limits {
  Limits::default()
}

/// `print ∘ parse ∘ print = print` at the term level.
#[quickcheck]
fn prop_term_print_parse_print_fixpoint(t: ArbTerm) -> bool {
  let p1 = print_term(&t.0);
  match parse_term(&p1, &lims()) {
    Ok(t2) => {
      let p2 = print_term(&t2);
      if p1 == p2 {
        true
      } else {
        eprintln!("not a fixpoint:\n--- p1\n{p1}\n--- p2\n{p2}");
        false
      }
    },
    Err(e) => {
      eprintln!("reparse failed: {e}\n---\n{p1}");
      false
    },
  }
}

/// `print ∘ parse ∘ print = print` at the file level (all decl forms,
/// imports included).
#[quickcheck]
fn prop_file_print_parse_print_fixpoint(f: ArbFile) -> bool {
  let p1 = print_file(&f.0);
  match parse_file(&p1, &lims()) {
    Ok(f2) => {
      let p2 = print_file(&f2);
      if p1 == p2 {
        true
      } else {
        eprintln!("not a fixpoint:\n--- p1\n{p1}\n--- p2\n{p2}");
        false
      }
    },
    Err(e) => {
      eprintln!("reparse failed: {e}\n---\n{p1}");
      false
    },
  }
}

/// The metering claim on [`Limits`]: no ε-productions, so the parsed
/// node count is bounded by the printed byte length.
#[quickcheck]
fn prop_node_count_bounded_by_bytes(t: ArbTerm) -> bool {
  let p = print_term(&t.0);
  match parse_term(&p, &lims()) {
    Ok(t2) => count_term_nodes(&t2) <= p.len(),
    Err(_) => false,
  }
}

/// Totality on arbitrary input: a value or a structured error, never a
/// panic (R2). Exercises both entry points.
#[quickcheck]
fn prop_parse_total_on_arbitrary_strings(s: String) -> bool {
  let _ = parse_term(&s, &lims());
  let _ = parse_file(&s, &lims());
  true
}

/// Determinism: parsing the same bytes twice yields identical results
/// (values and errors are `PartialEq`).
#[quickcheck]
fn prop_parse_deterministic(s: String) -> bool {
  parse_file(&s, &lims()) == parse_file(&s, &lims())
    && parse_term(&s, &lims()) == parse_term(&s, &lims())
}

/// Caps are respected and never panic, even when tiny.
#[quickcheck]
fn prop_tiny_limits_total(s: String) -> bool {
  let tiny = Limits { max_bytes: 64, max_nodes: 16, max_depth: 4 };
  let _ = parse_term(&s, &tiny);
  let _ = parse_file(&s, &tiny);
  true
}

/// Near-valid fuzz: mutate bytes of canonical output, reparse
/// (lossy-decoded), and require totality. This walks the interesting
/// boundary between valid and invalid text.
#[quickcheck]
fn prop_mutated_canonical_text_total(
  t: ArbTerm,
  muts: Vec<(usize, u8)>,
) -> bool {
  let mut bytes = print_term(&t.0).into_bytes();
  if bytes.is_empty() {
    return true;
  }
  for (pos, b) in muts {
    let n = bytes.len();
    bytes[pos % n] = b;
  }
  let s = String::from_utf8_lossy(&bytes);
  let _ = parse_term(&s, &lims());
  let _ = parse_file(&s, &lims());
  true
}
