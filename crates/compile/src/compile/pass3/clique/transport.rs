//! The entry point of the clique transport `Φ_σ`, its fallback and the
//! causes it records (a port of `Ix/Compile/Pass/Clique/Transport.lean`).
//!
//! **Input.** One clique as Lean elaborated it: its members in Lean's clique
//! order (`EqnInfo.declNames`, or `all` for a theorem clique), every other
//! constant of its encoding (the packed function and its abstracted proofs
//! for well-founded recursion; the `_f` functionals and the below matchers
//! for structural recursion; the `mutual` fixpoint and its monotonicity
//! proof for `partial_fixpoint`), the permutation `σ` (Lean index ↦
//! canonical position), and the canonical name of the packed constant.
//! Structural recursion also needs the environment, to read the `below`
//! dictionaries' definitions, and the block's authenticated `below`/`brecOn`
//! family ([`Input::family`]).
//!
//! **Output.** The transported constants (canonical names), the renaming of
//! Lean's encoding constants to canonical ones, and the non-canonical
//! causes:
//! * a proof body outside the grammar is kept verbatim under its transported
//!   statement (it proves it by conversion), cause `SHAPE`;
//! * a `partial_fixpoint` monotonicity proof outside the grammar takes the
//!   composition fallback `monotone_compose (mono φ) h`, cause `SHAPE`;
//! * anything else outside the grammar (the packed function, a statement, a
//!   member, a functional) leaves the whole clique in Lean's form (the
//!   baseline), cause `SHAPE` on every constant.
//!
//! The causes carry the transport's free-form reasons, for diagnostics; they
//! are data of the output only, never part of a record (the plan's side-car
//! record carries the constant and the cause tag,
//! [`CliquePlan::record`](super::plan::CliquePlan::record)).
//!
//! The function is total and pure: no kernel, no environment writes.

use rustc_hash::FxHashSet;

use ix_common::env::{ConstantInfo, Name};

use super::basic::{
  Cause, ConstOf, Decl, TState, const_app, is_perm, lam_arity, peel_lams,
};
use super::pf::transport_pf;
use super::plan::Encoding;
use super::structural::{proj_chain, transport_structural};
use super::telescope::id_perm;
use super::wf::{TransportOutput, Transported, transport_wf};
use crate::compile::pass3::expr::{get_app_fn_args, strip_mdata};

/// One clique to transport (`Input`).
pub struct Input<'a> {
  pub encoding: Encoding,
  /// the clique's members, in Lean's clique order
  pub members: Vec<Decl>,
  /// every other constant of the encoding
  pub aux: Vec<Decl>,
  /// Lean index ↦ canonical position
  pub sigma: Vec<usize>,
  /// the canonical name of the packed constant (`f₀._mutual` ↦ this)
  pub new_enc_name: Name,
  /// the environment (structural recursion reads `below`)
  pub const_of: ConstOf<'a>,
  /// equation lemmas carried with the clique, each with its output name: the
  /// members' own lemmas keep their names; the packed function's `eq_def` is
  /// regenerated under the canonical name, retaining its source-domain
  /// indexing through the decoded input adapter
  /// ([`transport_owned_wf_eq_def`](super::wf::transport_owned_wf_eq_def))
  pub lemmas: Vec<(Decl, Name)>,
  /// the block's authenticated `below`/`brecOn` family, for a structural
  /// clique ([`struct_layout`](super::structural::struct_layout)'s
  /// `family`). The caller computes it from the first member's `brecOn`
  /// head: [`family_candidates`](super::structural::family_candidates)
  /// gives the block's `all` and the candidate names, and the names
  /// `crate::compile::aux_gen::source_family::filter_heads` keeps form the
  /// set. The empty set authenticates nothing, so a structural clique
  /// refuses (the baseline); the other encodings do not read it.
  pub family: FxHashSet<Name>,
}

/// The environment of an [`Input`] without one (Lean's default
/// `fun _ => none`).
pub fn no_constant(_: &Name) -> Option<ConstantInfo> {
  None
}

impl Input<'_> {
  /// An input with Lean's defaults: no environment, no carried lemmas, the
  /// empty family.
  pub fn new(
    encoding: Encoding,
    members: Vec<Decl>,
    aux: Vec<Decl>,
    sigma: Vec<usize>,
    new_enc_name: Name,
  ) -> Input<'static> {
    Input {
      encoding,
      members,
      aux,
      sigma,
      new_enc_name,
      const_of: &no_constant,
      lemmas: Vec::new(),
      family: FxHashSet::default(),
    }
  }
}

/// The transport's outcome (`Output`).
#[derive(Clone, Debug)]
pub struct Output {
  pub decls: Vec<Decl>,
  /// Lean's encoding constant ↦ its canonical name
  pub renames: Vec<(Name, Name)>,
  /// constant (canonical name), cause, reason (the reason for diagnostics
  /// only)
  pub causes: Vec<(Name, Cause, String)>,
  /// the clique was left in Lean's form
  pub baseline: bool,
  pub log: Vec<String>,
}

/// `findPacked?`: the packed function of a well-founded clique (or the
/// packed fixpoint of a `partial_fixpoint` one): the constant the first
/// member applies, or projects out of.
pub fn find_packed(members: &[Decl], aux: &[Decl]) -> Option<Decl> {
  let m = members.first()?;
  let (_, body) = peel_lams(lam_arity(&m.value), &m.value);
  let (h, _) = get_app_fn_args(&strip_mdata(&body));
  let (steps, base) = proj_chain(&h);
  let target = if steps.is_empty() { &body } else { &base };
  let (h, _, _) = const_app(target)?;
  aux.iter().find(|d| d.name == h).cloned()
}

impl Output {
  /// `Output.baselineOf`: the baseline: Lean's constants unchanged, every
  /// one recorded.
  pub fn baseline_of(inp: &Input<'_>, why: &str) -> Output {
    let decls: Vec<Decl> =
      inp.aux.iter().chain(&inp.members).cloned().collect();
    let causes = decls
      .iter()
      .map(|d| (d.name.clone(), Cause::Shape, why.to_string()))
      .collect();
    Output {
      decls,
      renames: Vec::new(),
      causes,
      baseline: true,
      log: Vec::new(),
    }
  }
}

/// The causes of the constants that took a local fallback.
fn causes_of(out: &[Transported]) -> Vec<(Name, Cause, String)> {
  out
    .iter()
    .filter_map(|t| {
      t.fallback
        .as_ref()
        .map(|why| (t.decl.name.clone(), Cause::Shape, why.clone()))
    })
    .collect()
}

/// The output of a packed transport (well-founded or `partial_fixpoint`).
fn of_packed(out: TransportOutput, log: Vec<String>) -> Output {
  Output {
    causes: causes_of(&out.decls),
    decls: out.decls.into_iter().map(|t| t.decl).collect(),
    renames: out.renames,
    baseline: false,
    log,
  }
}

/// The abstracted proofs: every other constant of the encoding.
fn proofs_of(inp: &Input<'_>, packed: &Decl) -> Vec<Decl> {
  inp.aux.iter().filter(|d| d.name != packed.name).cloned().collect()
}

/// `transport`: transport a clique (`Φ_σ`), or leave it in Lean's form.
pub fn transport(inp: &Input<'_>) -> Output {
  if inp.sigma.len() != inp.members.len() || !is_perm(&inp.sigma) {
    return Output::baseline_of(
      inp,
      "transport: bad permutation (expected one distinct position for every \
       member)",
    );
  }
  if inp.sigma == id_perm(inp.sigma.len()) {
    // identity: nothing moves
    return Output {
      decls: inp.aux.iter().chain(&inp.members).cloned().collect(),
      renames: Vec::new(),
      causes: Vec::new(),
      baseline: false,
      log: Vec::new(),
    };
  }
  match inp.encoding {
    Encoding::WellFounded => {
      let Some(packed) = find_packed(&inp.members, &inp.aux) else {
        return Output::baseline_of(inp, "no packed function");
      };
      let proofs = proofs_of(inp, &packed);
      let mut tm = TState::default();
      match transport_wf(
        &mut tm,
        &inp.members,
        &packed,
        &proofs,
        &inp.sigma,
        &inp.new_enc_name,
        &inp.lemmas,
        inp.const_of,
      ) {
        Err(e) => Output::baseline_of(inp, &e),
        Ok(out) => of_packed(out, tm.log),
      }
    },
    Encoding::Structural => {
      let mut tm = TState::default();
      match transport_structural(
        &mut tm,
        &inp.members,
        &inp.aux,
        &inp.sigma,
        inp.const_of,
        inp.family.clone(),
        &inp.lemmas,
        false,
      ) {
        Err(e) => Output::baseline_of(inp, &e),
        Ok(out) => Output {
          causes: causes_of(&out),
          decls: out.into_iter().map(|t| t.decl).collect(),
          renames: Vec::new(),
          baseline: false,
          log: tm.log,
        },
      }
    },
    Encoding::PartialFixpoint => {
      let Some(packed) = find_packed(&inp.members, &inp.aux) else {
        return Output::baseline_of(inp, "no packed fixpoint");
      };
      let proofs = proofs_of(inp, &packed);
      let mut tm = TState::default();
      match transport_pf(
        &mut tm,
        &inp.members,
        &packed,
        &proofs,
        &inp.sigma,
        &inp.new_enc_name,
        inp.const_of,
        &inp.lemmas,
      ) {
        Err(e) => Output::baseline_of(inp, &e),
        Ok(out) => of_packed(out, tm.log),
      }
    },
  }
}

/// The hand-built cliques of the transport and recovery tests, one per
/// encoding (the ones the `wf`, `structural` and `pf` tests transport).
#[cfg(test)]
pub(crate) mod tests {
  use std::slice;

  use rustc_hash::FxHashSet;

  use ix_common::env::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, Expr, InductiveVal, Level,
    Name, RecursorVal,
  };

  use super::{Input, Output, find_packed, transport};
  use crate::compile::pass3::clique::basic::{
    Cause, Decl, Local, abstract_fvars, bvar, cnst, dotted, lvl_one, mk_app_n,
    mk_forall, mk_lambda, n_pprod, n_pprod_mk, proj, root_name, sort0,
  };
  use crate::compile::pass3::clique::packing::{
    PackKind, Spine, Tree, apply_projs, mk_inj, mk_tuple,
  };
  use crate::compile::pass3::clique::pf::{
    OrderData, mk_inst_tree, mk_mono_tree, mk_path_app, mk_path_proof,
    n_inst_ccpo_pprod, n_mono_compose, n_monotone, n_order_fix,
  };
  use crate::compile::pass3::clique::plan::Encoding;
  use crate::compile::pass3::expr::nat;

  /// A clique's members and the other constants of its encoding.
  pub(crate) struct Fixture {
    pub(crate) members: Vec<Decl>,
    pub(crate) aux: Vec<Decl>,
  }

  pub(crate) fn c(s: &str) -> Expr {
    cnst(&dotted(s), &[])
  }

  pub(crate) fn one() -> Level {
    Level::succ(Level::zero())
  }

  pub(crate) fn lam(x: &str, t: Expr, b: Expr) -> Expr {
    Expr::lam(root_name(x), t, b, BinderInfo::Default)
  }

  pub(crate) fn pi(x: &str, t: Expr, b: Expr) -> Expr {
    Expr::all(root_name(x), t, b, BinderInfo::Default)
  }

  pub(crate) fn def(name: &str, typ: Expr, value: Expr) -> Decl {
    Decl { name: dotted(name), level_params: vec![], typ, value, is_thm: false }
  }

  fn local(fvar: &str, user: &str, typ: Expr) -> Local {
    Local {
      fvar: dotted(fvar),
      user_name: root_name(user),
      typ,
      bi: BinderInfo::Default,
    }
  }

  // ------------------------------------------------------------------
  // Well-founded: `f : Nat → Nat`, `g : Int → Nat`, each calling the other
  // ------------------------------------------------------------------

  /// `∀ (y : α), InvImage α Nat lt h y x → Nat`, the recursive binder's
  /// type at the point `x`.
  fn rec_type(alpha: &Expr, h: &Expr, x: &Expr) -> Expr {
    let y = local("t.y", "y", alpha.clone());
    let rel = mk_app_n(
      cnst(&dotted("InvImage"), &[one(), one()]),
      &[alpha.clone(), c("Nat"), c("Nat.lt"), h.clone(), y.expr(), x.clone()],
    );
    let hy = local("t.h", "h", rel);
    mk_forall(&[y, hy], &c("Nat"))
  }

  /// The packing `PSum Nat Int`.
  pub(crate) fn wf_spine() -> Spine {
    Spine {
      kind: PackKind::Psum,
      leaves: vec![c("Nat"), c("Int")],
      lvls: vec![one(), one()],
    }
  }

  /// The packed function `f._mutual` (by `WellFounded.Nat.fix` over the
  /// constant measure), its abstracted proof and the members `f`, `g`:
  /// `f`'s leaf calls `g i0` (through the proof), `g`'s calls `f n0`.
  pub(crate) fn wf_clique() -> Fixture {
    let (nat, int) = (c("Nat"), c("Int"));
    let s = wf_spine();
    let Some(alpha) = s.typ() else { panic!("a packing type") };
    let h = lam("x", alpha.clone(), c("Nat.zero"));
    let proof_name = "f._mutual._proof_1";
    let inj = |j: usize, v: &Expr| {
      mk_inj(&s, j, v).unwrap_or_else(|| panic!("an injection"))
    };
    let leaf =
      |i: usize, summand: &Expr, body: &dyn Fn(&Local, &Local) -> Expr| {
        let p = local("t.p", "p", summand.clone());
        let r = local("t.r", "r", rec_type(&alpha, &h, &inj(i, &p.expr())));
        let body = body(&p, &r);
        mk_lambda(&[p, r], &body)
      };
    let to_g = inj(1, &c("i0"));
    let to_f = inj(0, &c("n0"));
    let leaves = vec![
      leaf(0, &nat, &|p, r| {
        mk_app_n(r.expr(), &[to_g.clone(), Expr::app(c(proof_name), p.expr())])
      }),
      leaf(1, &int, &|_, r| mk_app_n(r.expr(), &[to_f.clone(), c("h0")])),
    ];
    let m = local("t.m", "x", alpha.clone());
    let a = local("t.a", "a", rec_type(&alpha, &h, &m.expr()));
    let motive_body =
      abstract_fvars(slice::from_ref(&m.fvar), &mk_forall(&[a], &nat));
    let x = local("t.x", "x", alpha.clone());
    let a = local("t.a", "a", rec_type(&alpha, &h, &x.expr()));
    let Some(tree) = (Tree {
      spine: s.clone(),
      w: one(),
      motive_body,
      motive_name: root_name("x"),
      major: x.expr(),
      leaves,
      extras: vec![a.expr()],
      alt_names: vec![],
    })
    .build() else {
      panic!("a case tree")
    };
    let functional = mk_lambda(&[x, a], &tree);
    let root = mk_app_n(
      cnst(&dotted("WellFounded.Nat.fix"), &[one(), one()]),
      &[
        alpha.clone(),
        lam("x", alpha.clone(), nat.clone()),
        h.clone(),
        functional,
      ],
    );
    let packed = def("f._mutual", pi("x", alpha.clone(), nat.clone()), root);
    let member = |name: &str, i: usize, summand: &Expr| {
      let call = Expr::app(c("f._mutual"), inj(i, &bvar(0)));
      def(
        name,
        pi("n", summand.clone(), nat.clone()),
        lam("n", summand.clone(), call),
      )
    };
    let q = local("t.q", "p", nat.clone());
    let obligation = mk_app_n(
      cnst(&dotted("InvImage"), &[one(), one()]),
      &[alpha, nat.clone(), c("Nat.lt"), h, to_g, inj(0, &q.expr())],
    );
    let proof = def(
      proof_name,
      mk_forall(slice::from_ref(&q), &obligation),
      mk_lambda(&[q], &c("pf0")),
    );
    Fixture {
      members: vec![member("f", 0, &nat), member("g", 1, &int)],
      aux: vec![packed, proof],
    }
  }

  // ------------------------------------------------------------------
  // Structural: `f : T → A`, `g : T → B`, one group over `T`
  // ------------------------------------------------------------------

  fn cval(n: &str, typ: Expr) -> ConstantVal {
    ConstantVal { name: dotted(n), level_params: vec![], typ }
  }

  /// The recursive inductive `T` and its recursor.
  pub(crate) fn struct_env() -> Vec<ConstantInfo> {
    vec![
      ConstantInfo::InductInfo(InductiveVal {
        cnst: cval("T", sort0()),
        num_params: nat(0),
        num_indices: nat(0),
        all: vec![dotted("T")],
        ctors: vec![],
        num_nested: nat(0),
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
      }),
      ConstantInfo::RecInfo(RecursorVal {
        cnst: cval("T.rec", sort0()),
        all: vec![],
        num_params: nat(0),
        num_indices: nat(0),
        num_motives: nat(1),
        num_minors: nat(0),
        rules: vec![],
        k: false,
        is_unsafe: false,
      }),
    ]
  }

  pub(crate) fn lookup(
    env: &[ConstantInfo],
  ) -> impl Fn(&Name) -> Option<ConstantInfo> + '_ {
    move |n| env.iter().find(|ci| ci.get_name() == n).cloned()
  }

  /// `T`'s authenticated family.
  pub(crate) fn struct_family() -> FxHashSet<Name> {
    ["T.below", "T.brecOn"].into_iter().map(dotted).collect()
  }

  fn below(motive: &Expr) -> Expr {
    mk_app_n(c("T.below"), &[motive.clone(), bvar(0)])
  }

  /// The clique `f, g` of one group over `T`, Lean's packing `PProd A B`
  /// (`PProd B A` when `swapped`, `f` then projecting the second
  /// component): the members (`f` first), then the functionals. `f`'s
  /// functional is named `f_fun`; when that is not `f._f`, a decoy `f._f`
  /// (not passed to `brecOn`) is added.
  pub(crate) fn struct_clique(swapped: bool, f_fun: &str) -> Fixture {
    let pprod = |a: Expr, b: Expr| {
      mk_app_n(cnst(&n_pprod(), &[lvl_one(), lvl_one()]), &[a, b])
    };
    let (l, r) = if swapped { ("B", "A") } else { ("A", "B") };
    let (fl, fr) = if swapped { ("g._f", f_fun) } else { (f_fun, "g._f") };
    let motive = lam("x", c("T"), pprod(c(l), c(r)));
    let call = |f: &str| mk_app_n(c(f), &[bvar(1), bvar(0)]);
    let tuple = mk_app_n(
      cnst(&n_pprod_mk(), &[lvl_one(), lvl_one()]),
      &[c(l), c(r), call(fl), call(fr)],
    );
    let functional = lam("x", c("T"), lam("f", below(&motive), tuple));
    let brec_on =
      mk_app_n(c("T.brecOn"), &[motive.clone(), bvar(0), functional]);
    let member = |n: &str, ty: &str, field: usize| {
      def(
        n,
        pi("x", c("T"), c(ty)),
        lam("x", c("T"), proj(&n_pprod(), field, brec_on.clone())),
      )
    };
    let fa = usize::from(swapped);
    let members = vec![member("f", "A", fa), member("g", "B", 1 - fa)];
    let func = |n: &str, ty: &str, v: &str| {
      def(
        n,
        pi("x", c("T"), pi("f", below(&motive), c(ty))),
        lam("x", c("T"), lam("f", below(&motive), c(v))),
      )
    };
    let mut aux = vec![func(f_fun, "A", "a"), func("g._f", "B", "b")];
    if f_fun != "f._f" {
      aux.push(def("f._f", pi("x", c("T"), c("A")), lam("x", c("T"), c("a"))));
    }
    Fixture { members, aux }
  }

  // ------------------------------------------------------------------
  // `partial_fixpoint`: `f : Nat → Nat`, `g : Int → Nat`
  // ------------------------------------------------------------------

  /// The packing `(Nat → Nat) ×' (Int → Nat)`.
  pub(crate) fn pf_spine() -> Spine {
    Spine {
      kind: PackKind::Pprod,
      leaves: vec![pi("n", c("Nat"), c("Nat")), pi("i", c("Int"), c("Nat"))],
      lvls: vec![one(), one()],
    }
  }

  fn monotone(a: &Expr, o: &Expr, b: &Expr, pb: &Expr, f: &Expr) -> Expr {
    mk_app_n(
      cnst(&n_monotone(), &[one(), one()]),
      &[a.clone(), o.clone(), b.clone(), pb.clone(), f.clone()],
    )
  }

  /// `∀ (α : Type) (o : PO α) (f : α → Nat → Nat) (h : monotone o PB f),
  /// monotone o PB f`.
  fn mono_theorem() -> Expr {
    let b = pi("n", c("Nat"), c("Nat"));
    let alpha = local("t.a", "α", Expr::sort(one()));
    let o = local("t.o", "o", Expr::app(c("PO"), alpha.expr()));
    let f = local("t.f", "f", pi("x", alpha.expr(), b.clone()));
    let goal = monotone(&alpha.expr(), &o.expr(), &b, &c("PB"), &f.expr());
    let h = local("t.h0", "h", goal.clone());
    mk_forall(&[alpha, o, f, h], &goal)
  }

  fn axiom(name: &str, level_params: Vec<Name>, typ: Expr) -> ConstantInfo {
    ConstantInfo::AxiomInfo(AxiomVal {
      cnst: ConstantVal { name: dotted(name), level_params, typ },
      is_unsafe: false,
    })
  }

  /// The environment of the `partial_fixpoint` clique.
  pub(crate) fn pf_env(n: &Name) -> Option<ConstantInfo> {
    if *n == dotted("T.mono") {
      Some(axiom("T.mono", vec![], mono_theorem()))
    } else if *n == n_mono_compose() {
      let levels = ["u", "v", "w"].map(dotted).to_vec();
      Some(axiom("Lean.Order.monotone_compose", levels, sort0()))
    } else {
      None
    }
  }

  /// `λ (n : domain). x.π_j arg` under the recursive binder `x`, the path
  /// in projection form (`app` false) or application form.
  pub(crate) fn pf_body(
    s: &Spine,
    j: usize,
    app: bool,
    (x, domain, arg): (&str, &str, &str),
  ) -> Expr {
    let path = if app {
      mk_path_app(s, j, &bvar(1)).unwrap_or_else(|| panic!("a path"))
    } else {
      let steps = s.proj_steps(j).unwrap_or_else(|| panic!("a path"));
      apply_projs(&steps, &bvar(1))
    };
    lam(x, c(domain), Expr::app(path, c(arg)))
  }

  /// The members `f`, `g` projecting `f.mutual`.
  fn pf_members(s: &Spine) -> Vec<Decl> {
    let member = |name: &str, x: &str, domain: &str, j: usize| {
      let call = Expr::app(proj(&n_pprod(), j, c("f.mutual")), bvar(0));
      let typ = s.leaves.get(j).cloned().unwrap_or_else(|| panic!("a leaf"));
      def(name, typ, lam(x, c(domain), call))
    };
    vec![member("f", "n", "Nat", 0), member("g", "i", "Int", 1)]
  }

  /// The clique the `pf` tests transport: `f`'s call in application form,
  /// `g`'s in projection form; one per-function monotonicity proof through
  /// a theorem application, one the transport cannot follow (it takes the
  /// composition fallback).
  pub(crate) fn pf_clique() -> Fixture {
    let s = pf_spine();
    let d = OrderData {
      spine: s.clone(),
      insts: vec![c("inst0"), c("inst1")],
      lattice: false,
      tspine: s.clone(),
    };
    let some = |e: Option<Expr>| e.unwrap_or_else(|| panic!("built"));
    let Some(gamma) = s.typ() else { panic!("a packing type") };
    let po = some(d.packed_po());
    let inst = some(mk_inst_tree(&n_inst_ccpo_pprod(), &s, &d.insts));
    let b0 = pf_body(&s, 1, true, ("n", "Nat", "i0"));
    let b1 = pf_body(&s, 0, false, ("i", "Int", "n0"));
    let functional =
      lam("x", gamma.clone(), some(mk_tuple(&s, &[b0.clone(), b1.clone()])));
    let fs = vec![lam("x", gamma.clone(), b0), lam("x", gamma.clone(), b1)];
    let path = some(mk_path_proof(&d, 1).map(|p| p.0));
    let hs = vec![
      mk_app_n(c("T.mono"), &[gamma.clone(), po.clone(), fs[0].clone(), path]),
      c("h1const"),
    ];
    let proof_name = "f.mutual._proof_1";
    let statement =
      monotone(&gamma, &po, &gamma, &some(d.po_tree(0)), &functional);
    let proof = Decl {
      is_thm: true,
      ..def(proof_name, statement, some(mk_mono_tree(&d, &fs, &hs)))
    };
    let root = mk_app_n(
      cnst(&n_order_fix(), &[one()]),
      &[gamma.clone(), inst, functional, c(proof_name)],
    );
    let packed = def("f.mutual", gamma, root);
    Fixture { members: pf_members(&s), aux: vec![packed, proof] }
  }

  /// A clique of the same members whose calls are both in projection form,
  /// the form the recovery reads; its instance and proof are opaque.
  pub(crate) fn pf_proj_clique() -> Fixture {
    let s = pf_spine();
    let Some(gamma) = s.typ() else { panic!("a packing type") };
    let b0 = pf_body(&s, 1, false, ("n", "Nat", "i0"));
    let b1 = pf_body(&s, 0, false, ("i", "Int", "n0"));
    let tuple = mk_tuple(&s, &[b0, b1]).unwrap_or_else(|| panic!("a tuple"));
    let root = mk_app_n(
      cnst(&n_order_fix(), &[one()]),
      &[gamma.clone(), c("inst"), lam("x", gamma.clone(), tuple), c("prf")],
    );
    Fixture { members: pf_members(&s), aux: vec![def("f.mutual", gamma, root)] }
  }

  fn names(out: &Output) -> Vec<Name> {
    out.decls.iter().map(|d| d.name.clone()).collect()
  }

  fn pairs(xs: &[(&str, &str)]) -> Vec<(Name, Name)> {
    xs.iter().map(|(a, b)| (dotted(a), dotted(b))).collect()
  }

  #[test]
  fn bad_permutations_and_the_identity() {
    let k = wf_clique();
    let lean: Vec<Name> =
      k.aux.iter().chain(&k.members).map(|d| d.name.clone()).collect();
    let run = |sigma: Vec<usize>| {
      transport(&Input::new(
        Encoding::WellFounded,
        k.members.clone(),
        k.aux.clone(),
        sigma,
        dotted("g._mutual"),
      ))
    };
    let why = "transport: bad permutation (expected one distinct position \
               for every member)";
    for sigma in [vec![0, 0], vec![1, 0, 2], vec![1]] {
      let out = run(sigma);
      assert!(out.baseline);
      assert_eq!(names(&out), lean);
      assert!(out.renames.is_empty());
      let causes: Vec<(Name, Cause, String)> = lean
        .iter()
        .map(|n| (n.clone(), Cause::Shape, why.to_string()))
        .collect();
      assert_eq!(out.causes, causes);
    }
    // the identity moves nothing and records nothing
    let out = run(vec![0, 1]);
    assert!(!out.baseline);
    assert_eq!(names(&out), lean);
    assert!(out.causes.is_empty() && out.renames.is_empty());
  }

  #[test]
  fn dispatches_well_founded() {
    let k = wf_clique();
    assert_eq!(
      find_packed(&k.members, &k.aux).map(|d| d.name),
      Some(dotted("f._mutual"))
    );
    let inp = Input::new(
      Encoding::WellFounded,
      k.members.clone(),
      k.aux.clone(),
      vec![1, 0],
      dotted("g._mutual"),
    );
    let out = transport(&inp);
    assert!(!out.baseline);
    assert_eq!(
      out.renames,
      pairs(&[
        ("f._mutual", "g._mutual"),
        ("f._mutual._proof_1", "g._mutual._proof_1")
      ])
    );
    assert_eq!(
      names(&out),
      ["g._mutual", "g._mutual._proof_1", "f", "g"].map(dotted)
    );
    assert!(out.causes.is_empty());
    // no packed function among the encoding's constants
    let inp = Input { aux: vec![], ..inp };
    let out = transport(&inp);
    assert!(out.baseline);
    assert_eq!(names(&out), ["f", "g"].map(dotted));
    assert!(out.causes.iter().all(|x| x.2 == "no packed function"));
  }

  #[test]
  fn dispatches_structural() {
    let env = struct_env();
    let env = lookup(&env);
    let k = struct_clique(false, "f._f");
    let inp = Input {
      const_of: &env,
      family: struct_family(),
      ..Input::new(
        Encoding::Structural,
        k.members.clone(),
        k.aux.clone(),
        vec![1, 0],
        dotted("unused"),
      )
    };
    let out = transport(&inp);
    assert!(!out.baseline);
    assert!(out.renames.is_empty() && out.causes.is_empty());
    // the packing becomes `PProd B A`: the swapped presentation's terms
    let want = struct_clique(true, "f._f");
    let want: Vec<Decl> = want.aux.into_iter().chain(want.members).collect();
    assert_eq!(out.decls.len(), want.len());
    for (g, w) in out.decls.iter().zip(&want) {
      assert_eq!((&g.name, &g.typ, &g.value), (&w.name, &w.typ, &w.value));
    }
    // the empty family authenticates nothing: the baseline
    let out = transport(&Input { family: FxHashSet::default(), ..inp });
    assert!(out.baseline);
    assert_eq!(out.decls.len(), 4);
    assert!(out.causes.iter().all(|x| {
      x.1 == Cause::Shape
        && x.2
          == "T.below: not in the block's authenticated below/brecOn family"
    }));
  }

  #[test]
  fn dispatches_partial_fixpoint() {
    let k = pf_clique();
    let inp = Input {
      const_of: &pf_env,
      ..Input::new(
        Encoding::PartialFixpoint,
        k.members.clone(),
        k.aux.clone(),
        vec![1, 0],
        dotted("g.mutual"),
      )
    };
    let out = transport(&inp);
    assert!(!out.baseline);
    assert_eq!(
      out.renames,
      pairs(&[
        ("f.mutual", "g.mutual"),
        ("f.mutual._proof_1", "g.mutual._proof_1")
      ])
    );
    assert_eq!(
      names(&out),
      ["g.mutual", "g.mutual._proof_1", "f", "g"].map(dotted)
    );
    // the proof the transport cannot follow took the composition fallback
    assert_eq!(
      out.causes,
      vec![(
        dotted("g.mutual._proof_1"),
        Cause::Shape,
        "monotonicity proof 1: PF proof ownership: missing theorem h1const"
          .to_string()
      )]
    );
    // a refusal leaves the whole clique in Lean's form
    let out = transport(&Input { aux: vec![k.aux[0].clone()], ..inp });
    assert!(out.baseline);
    assert!(out.causes.iter().all(|x| x.2
      == "PF ownership: fixpoint proof is not among the owned declarations"));
    let out = transport(&Input::new(
      Encoding::PartialFixpoint,
      k.members,
      vec![],
      vec![1, 0],
      dotted("g.mutual"),
    ));
    assert!(out.baseline);
    assert!(out.causes.iter().all(|x| x.2 == "no packed fixpoint"));
  }
}
