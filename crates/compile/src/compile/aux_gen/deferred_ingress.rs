//! On-demand kernel ingress for aux_gen.
//!
//! # What the eager walk did
//!
//! `compute_is_large_and_k` gives the kernel the constants its target and
//! constructor types mention by draining a work stack
//! (`recursor::drain_ingress_queue`): each popped name is resolved to its
//! `KId`, deduplicated against `KernelCtx::aux_ingress_seen`, ingested
//! (`ensure_full_in_kenv_of` for definitions, inductives and constructors,
//! a type-only `Axio` stub for the rest) and the constants its ingested
//! expressions mention are pushed. Through definition values that closure
//! reaches a large part of the library (519 constants per Mathlib aux_gen
//! call on average), of which the kernel reads well under 1 %.
//!
//! # What this module does instead
//!
//! The walk itself still runs, in the same order, over the same names, with
//! the same `KId` resolution and the same dedup set — but over a cache of
//! each constant's dispatch kind and push list ([`AuxDep`], built once per
//! constant per compile in `CompileState::aux_dep_cache`), and it converts
//! nothing: every insert the eager walk would perform is *registered* with
//! the kernel environment instead (`KEnv::register_deferred`, see
//! `ix_kernel::env::deferred`). A registered constant is converted
//! ([`materialize`]) the first time anything reads it:
//!
//! * the type checker, through the `DeferredSource` (the compile state)
//!   installed on every `TypeChecker` aux_gen builds
//!   (`compute_is_large_and_k`, `TcScope`);
//! * aux_gen's own direct reads of the kernel environment, each of which
//!   materializes first: `ensure_in_kenv_of_inner_env` (all explicit
//!   ingestion), `ensure_prelude_in_kenv_of` (its `PUnit` check),
//!   `TcScope::try_infer_app_sort_level` (via `try_get_const`);
//! * the observers that only ask *whether* a constant is there read the
//!   environment's view, in which a registered constant is present:
//!   `ingress_type_stub`, `TcScope::addr_present`, and
//!   `Primitives::from_env` (the primitive ids are computed once, when the
//!   first checker is built over the block's environment, from the ids
//!   present then; the view reproduces the eager map's ids *and* their
//!   iteration order, which decides between two ids at one address).
//!
//! The kernel environment is therefore, for every reader, the one the eager
//! walk would have built: a registered constant is present wherever the
//! eager one was, converted from the same source with the same fidelity.
//! The emulation decides each insert at the time the eager walk would have
//! performed it, from the environment's view at that time (an eager insert
//! over an already *materialized* entry is performed for real, at once).
//!
//! # Name resolution
//!
//! A registered constant is converted later than the eager walk would have
//! converted it, so the names in it are resolved later. The resolutions
//! that can change while a block runs are those of names first registered
//! in `aux_name_to_addr` by the block's own aux phases (`mutual.rs`
//! registers `.rec`, `.casesOn`, `.recOn`, `.below` and its constructors,
//! `.below.rec`, `.brecOn*` and source aliases); `name_to_addr` entries
//! never change once written (promotion copies the same address). None of
//! those names can be in a closure that is walked before it is registered:
//! the closures walked in the generation phase start from the block's own
//! inductive declarations, and Lean declares everything they reach before
//! the inductive, its auxiliaries after; the closures walked for `.below.rec`
//! (`compile_below_recursors`) also reach the block's `.below` family, which
//! is registered before that walk and not again. Every other name in a
//! closure belongs to a constant the block depends on and is compiled, and
//! resolved for good, before the block starts. [`materialize`] checks the
//! first half of this at each conversion (the constant's own name still
//! resolves to the address it was registered under) and panics otherwise,
//! which fails the block instead of letting the two paths diverge.
//!
//! # What is not reproduced
//!
//! The kernel's intern table and ingress cache are keyed by name-erased
//! content (`expr_key`, `(expr hash, param names)`), so the first interning
//! of a shape fixes its binder names, binder infos, `Var` names and — for a
//! `Const` — which of several constants at one address it names, for every
//! later equal shape. Converting fewer constants, later, changes that
//! history, so the display metadata of converted constants and of kernel
//! results can differ from the eager run's; and since kernel lookups use
//! the `KId` of the interned `Const`, a lookup can ask for a different
//! alias at the same address (on Init: 104 of 17,373 aux_gen lookups, all
//! with the same outcome by address). The eager walk is subject to the same
//! effect; its outcome depends on its own conversion order. Of the kernel
//! results aux_gen emits, only WHNF results that unfold something carry
//! such metadata into generated types (reducible-alias targets, recursive
//! fields under aliases). The output identity checks on Init and Mathlib
//! are the evidence that none of this changes an output there.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use dashmap::DashMap;

use crate::compile::nat_conv::nat_to_u64;
use ix_common::env::{
  ConstantInfo as LCI, ConstructorVal, DefinitionSafety, Env as LeanEnv,
  Expr as LeanExpr, InductiveVal, Name, ReducibilityHints,
};
use ix_kernel::constant::KConst;
use ix_kernel::env::{Deferred, KEnv};
use ix_kernel::expr::KExpr;
use ix_kernel::id::KId;
use ix_kernel::ingress::{
  lean_expr_to_zexpr_cached, param_names_hash, resolve_lean_name_addr,
};
use ix_kernel::mode::Meta;
use ix_kernel::tc::DeferredSource;

/// How the eager ingestion walk treats one Lean constant.
pub struct AuxDep {
  /// `None` when the source environment has no constant of this name (the
  /// walk then neither ingests nor pushes anything).
  kind: Option<DepKind>,
  /// The names the walk pushes after dispatching this constant, in push
  /// order: `collect_const_refs` of its type, then of its value
  /// (definitions) or of each constructor type (inductives).
  pushes: Box<[Name]>,
}

/// The source constant kinds, as far as ingestion distinguishes them.
enum DepKind {
  Defn,
  Thm,
  Opaque,
  Axiom,
  Quot,
  Rec,
  /// `ctors`: the constructors the source environment holds as
  /// constructors, in declaration order (the ones ingestion converts).
  Induct {
    ctors: Box<[Name]>,
  },
  Ctor {
    induct: Name,
  },
}

/// Per-compile cache of [`AuxDep`]s, keyed by constant name. Valid for one
/// source environment: `CompileState::lean_env`, the only one deferred
/// ingestion runs against.
pub type AuxDepCache = DashMap<Name, Arc<AuxDep>, rustc_hash::FxBuildHasher>;

/// Kill switch: `IX_AUX_EAGER_INGRESS=1` keeps the eager walk.
static IX_AUX_EAGER_INGRESS: std::sync::LazyLock<bool> =
  std::sync::LazyLock::new(|| std::env::var("IX_AUX_EAGER_INGRESS").is_ok());

fn dep_of(
  name: &Name,
  lean_env: &LeanEnv,
  stt: &crate::compile::CompileState,
) -> Arc<AuxDep> {
  if let Some(dep) = stt.aux_dep_cache.get(name) {
    return dep.clone();
  }
  let dep = Arc::new(compute_dep(name, lean_env));
  stt.aux_dep_cache.entry(name.clone()).or_insert(dep).clone()
}

/// Mirrors `recursor::ingress_aux_gen_dep`'s pushes and the constructor
/// filter of `ensure_in_kenv_of_inner_env`.
fn compute_dep(name: &Name, lean_env: &LeanEnv) -> AuxDep {
  use super::recursor::collect_const_refs;
  let Some(ci) = lean_env.get(name) else {
    return AuxDep { kind: None, pushes: Box::new([]) };
  };
  let mut pushes = Vec::new();
  let kind = match &*ci {
    LCI::DefnInfo(v) => {
      collect_const_refs(&v.cnst.typ, &mut pushes);
      collect_const_refs(&v.value, &mut pushes);
      DepKind::Defn
    },
    LCI::InductInfo(v) => {
      collect_const_refs(&v.cnst.typ, &mut pushes);
      let mut ctors = Vec::new();
      for ctor_name in &v.ctors {
        if let Some(LCI::CtorInfo(ctor)) = lean_env.get(ctor_name).as_deref() {
          collect_const_refs(&ctor.cnst.typ, &mut pushes);
          ctors.push(ctor_name.clone());
        }
      }
      DepKind::Induct { ctors: ctors.into_boxed_slice() }
    },
    LCI::CtorInfo(v) => {
      collect_const_refs(&v.cnst.typ, &mut pushes);
      DepKind::Ctor { induct: v.induct.clone() }
    },
    LCI::AxiomInfo(v) => {
      collect_const_refs(&v.cnst.typ, &mut pushes);
      DepKind::Axiom
    },
    LCI::ThmInfo(v) => {
      collect_const_refs(&v.cnst.typ, &mut pushes);
      DepKind::Thm
    },
    LCI::OpaqueInfo(v) => {
      collect_const_refs(&v.cnst.typ, &mut pushes);
      DepKind::Opaque
    },
    LCI::RecInfo(v) => {
      collect_const_refs(&v.cnst.typ, &mut pushes);
      DepKind::Rec
    },
    LCI::QuotInfo(v) => {
      collect_const_refs(&v.cnst.typ, &mut pushes);
      DepKind::Quot
    },
  };
  AuxDep { kind: Some(kind), pushes: pushes.into_boxed_slice() }
}

fn resolve(name: &Name, stt: &crate::compile::CompileState) -> KId<Meta> {
  let addr = resolve_lean_name_addr(
    name,
    Some(&stt.name_to_addr),
    Some(&stt.aux_name_to_addr),
  );
  KId::new(addr, name.clone())
}

/// The source environment deferred ingestion runs against, if `lean_env`
/// is it.
fn deferral_env<'s>(
  lean_env: &LeanEnv,
  stt: &'s crate::compile::CompileState,
) -> Option<&'s LeanEnv> {
  stt.lean_env.as_deref().filter(|own| std::ptr::eq(*own, lean_env))
}

/// Switch the block's kernel environment to deferred ingestion. Only an
/// empty environment can be switched, and only when `lean_env` is the
/// compile's own source environment (the [`AuxDepCache`] is keyed by name
/// for that environment alone); otherwise ingestion stays eager.
pub(crate) fn enable(
  lean_env: &LeanEnv,
  stt: &crate::compile::CompileState,
  kctx: &mut crate::compile::KernelCtx,
) {
  if *IX_AUX_EAGER_INGRESS || deferral_env(lean_env, stt).is_none() {
    return;
  }
  kctx.kenv.enable_deferred();
}

/// Whether drains against `lean_env` defer (see [`drain`]).
pub(super) fn defers(
  lean_env: &LeanEnv,
  stt: &crate::compile::CompileState,
  kctx: &crate::compile::KernelCtx,
) -> bool {
  kctx.kenv.is_deferring() && deferral_env(lean_env, stt).is_some()
}

/// The deferred counterpart of `recursor::drain_ingress_queue`: the same
/// walk, registering instead of converting. Requires [`defers`].
pub(super) fn drain(
  queue: &mut Vec<Name>,
  lean_env: &LeanEnv,
  stt: &crate::compile::CompileState,
  kctx: &mut crate::compile::KernelCtx,
) {
  let mut seen = std::mem::take(&mut kctx.aux_ingress_seen);
  while let Some(name) = queue.pop() {
    let zid = resolve(&name, stt);
    if !seen.insert(zid.clone()) {
      continue;
    }
    let dep = dep_of(&name, lean_env, stt);
    match &dep.kind {
      // `ingress_aux_gen_dep`: definitions, inductives and constructors at
      // full fidelity ...
      Some(DepKind::Defn | DepKind::Induct { .. } | DepKind::Ctor { .. }) => {
        defer_full(&name, zid, &dep, lean_env, stt, &mut kctx.kenv);
      },
      // ... everything else as a type-only stub (`ingress_type_stub`,
      // which keeps whatever is already there).
      Some(_) if !kctx.kenv.view_contains(&zid) => {
        kctx.kenv.register_deferred(zid, Deferred::Stub(name.clone()));
      },
      Some(_) | None => {},
    }
    queue.extend(dep.pushes.iter().cloned());
  }
  kctx.aux_ingress_seen = seen;
}

/// Whether the view's entry at `id` is an `Axio` (the entries
/// `ensure_in_kenv_of_inner_env` replaces when upgrading); `None` when
/// absent.
fn view_is_axio(
  kenv: &KEnv<Meta>,
  id: &KId<Meta>,
  lean_env: &LeanEnv,
  stt: &crate::compile::CompileState,
) -> Option<bool> {
  if let Some(c) = kenv.consts.get(id) {
    return Some(matches!(c, KConst::Axio { .. }));
  }
  match kenv.pending(id)? {
    Deferred::Stub(_) => Some(true),
    Deferred::Ctor { .. } => Some(false),
    Deferred::Full(name) => {
      Some(matches!(dep_of(name, lean_env, stt).kind, Some(DepKind::Axiom)))
    },
  }
}

/// Emulates `ensure_in_kenv_of_inner_env(name, replace_axio_stub = true,
/// stub_proof_values = false)` against the view.
fn defer_full(
  name: &Name,
  zid: KId<Meta>,
  dep: &AuxDep,
  lean_env: &LeanEnv,
  stt: &crate::compile::CompileState,
  kenv: &mut KEnv<Meta>,
) {
  if view_is_axio(kenv, &zid, lean_env, stt) == Some(false) {
    return;
  }
  let Some(kind) = &dep.kind else { return };
  match kind {
    DepKind::Induct { ctors } => {
      // Constructors first (each insert unconditional), then the inductive.
      for (cidx, ctor) in ctors.iter().enumerate() {
        let what = Deferred::Ctor {
          induct: name.clone(),
          ctor: ctor.clone(),
          cidx: cidx as u64,
        };
        put(kenv, resolve(ctor, stt), what, stt);
      }
      put(kenv, zid, Deferred::Full(name.clone()), stt);
    },
    DepKind::Ctor { induct } => {
      let parent = dep_of(induct, lean_env, stt);
      defer_full(induct, resolve(induct, stt), &parent, lean_env, stt, kenv);
    },
    DepKind::Rec => {},
    DepKind::Defn
    | DepKind::Thm
    | DepKind::Opaque
    | DepKind::Axiom
    | DepKind::Quot => put(kenv, zid, Deferred::Full(name.clone()), stt),
  }
}

/// An insert of the eager walk: registered, or — when it would overwrite a
/// materialized entry — performed now, as the eager walk would have.
fn put(
  kenv: &mut KEnv<Meta>,
  id: KId<Meta>,
  what: Deferred,
  stt: &crate::compile::CompileState,
) {
  if kenv.consts.contains_key(&id) {
    let lean_env = stt
      .lean_env
      .as_deref()
      .expect("deferred ingestion runs against stt.lean_env");
    let c = convert(&what, &id, lean_env, stt, kenv);
    kenv.insert(id, c);
  } else {
    kenv.register_deferred(id, what);
  }
}

/// Convert and insert the constant registered at `id`, if one is. Every
/// direct reader of a deferring kernel environment calls this (or goes
/// through a `TypeChecker` carrying the compile state as its
/// `DeferredSource`) before reading `id`.
pub(super) fn materialize(
  kenv: &mut KEnv<Meta>,
  id: &KId<Meta>,
  stt: &crate::compile::CompileState,
) -> bool {
  let Some(what) = kenv.take_pending(id) else {
    return false;
  };
  let lean_env = stt
    .lean_env
    .as_deref()
    .expect("deferred ingestion runs against stt.lean_env");
  let own = match &what {
    Deferred::Full(name) | Deferred::Stub(name) => name,
    Deferred::Ctor { ctor, .. } => ctor,
  };
  let now = resolve(own, stt);
  assert!(
    now.addr == id.addr,
    "deferred aux_gen ingress: `{}` was registered at {:.12} but now \
     resolves to {:.12}; its conversion would differ from the eager one",
    own.pretty(),
    id.addr.hex(),
    now.addr.hex(),
  );
  let c = convert(&what, id, lean_env, stt, kenv);
  kenv.insert_materialized(id.clone(), c);
  true
}

/// The compile state owns aux_gen's registrations: every `TypeChecker`
/// aux_gen builds over a block's kernel environment carries it
/// (`with_deferred_source`) to materialize what a lookup misses.
impl DeferredSource<Meta> for crate::compile::CompileState {
  fn materialize(&self, env: &mut KEnv<Meta>, id: &KId<Meta>) {
    materialize(env, id, self);
  }
}

/// Convert the constant `what` stands for at `id`, exactly as the eager
/// ingestion inserts it (`ensure_in_kenv_of_inner_env` with
/// `stub_proof_values = false` for `Full`/`Ctor`, `ingress_type_stub` for
/// `Stub`).
fn convert(
  what: &Deferred,
  id: &KId<Meta>,
  lean_env: &LeanEnv,
  stt: &crate::compile::CompileState,
  kenv: &mut KEnv<Meta>,
) -> KConst<Meta> {
  let get = |name: &Name| {
    lean_env.get(name).unwrap_or_else(|| {
      panic!("deferred aux_gen ingress: `{}` vanished", name.pretty())
    })
  };
  match what {
    Deferred::Full(name) => {
      let ci = get(name);
      match &*ci {
        LCI::InductInfo(ind) => {
          let lp = &ind.cnst.level_params;
          let ty = to_z(&ind.cnst.typ, lp, kenv, stt);
          let ctors = match dep_of(name, lean_env, stt).kind.as_ref() {
            Some(DepKind::Induct { ctors }) => {
              ctors.iter().map(|c| resolve(c, stt)).collect()
            },
            _ => unreachable!("an inductive's dep is Induct"),
          };
          indc_const(name, ind, id.clone(), ctors, ty)
        },
        other => full_const(name, other, id.clone(), kenv, stt, false)
          .unwrap_or_else(|| {
            panic!(
              "deferred aux_gen ingress: `{}` cannot be registered in full",
              name.pretty()
            )
          }),
      }
    },
    Deferred::Ctor { induct, ctor, cidx } => {
      let parent = get(induct);
      let LCI::InductInfo(ind) = &*parent else {
        panic!(
          "deferred aux_gen ingress: `{}` is not an inductive",
          induct.pretty()
        )
      };
      let ci = get(ctor);
      let LCI::CtorInfo(c) = &*ci else {
        panic!(
          "deferred aux_gen ingress: `{}` is not a constructor",
          ctor.pretty()
        )
      };
      let lp = &ind.cnst.level_params;
      let ty = to_z(&c.cnst.typ, lp, kenv, stt);
      ctor_const(ctor, c, lp, resolve(induct, stt), *cidx, ty)
    },
    Deferred::Stub(name) => {
      let ci = get(name);
      let lp = ci.get_level_params();
      let ty = to_z(ci.get_type(), lp, kenv, stt);
      stub_const(name, lp, ty)
    },
  }
}

// ---------------------------------------------------------------------------
// The constant shapes of aux_gen's Lean ingestion, shared by the eager path
// (`expr_utils::ensure_in_kenv_of_inner_env`, `recursor::ingress_type_stub`)
// and [`materialize`], so the two cannot drift apart.
// ---------------------------------------------------------------------------

/// A top-level Lean expression in the kernel, through the environment's
/// ingress cache (an empty binder-name stack: callers are top-level).
pub(super) fn to_z(
  expr: &LeanExpr,
  lp: &[Name],
  kenv: &mut KEnv<Meta>,
  stt: &crate::compile::CompileState,
) -> KExpr<Meta> {
  let pn_h = param_names_hash(lp);
  let mut binder_names: Vec<Name> = Vec::new();
  lean_expr_to_zexpr_cached(
    expr,
    lp,
    &mut binder_names,
    &mut kenv.intern,
    Some(&stt.name_to_addr),
    Some(&stt.aux_name_to_addr),
    Some(&mut kenv.ingress_cache),
    Some(&pn_h),
  )
}

pub(super) fn indc_const(
  name: &Name,
  ind: &InductiveVal,
  zid: KId<Meta>,
  ctors: Vec<KId<Meta>>,
  ty: KExpr<Meta>,
) -> KConst<Meta> {
  let lp = &ind.cnst.level_params;
  KConst::Indc {
    name: name.clone(),
    level_params: lp.clone(),
    lvls: lp.len() as u64,
    params: nat_to_u64(&ind.num_params),
    indices: nat_to_u64(&ind.num_indices),
    is_unsafe: ind.is_unsafe,
    ctors,
    ty,
    block: zid,
    member_idx: 0,
    lean_all: vec![],
  }
}

/// Constructor `ctor_name` ingested with its inductive (`induct`, level
/// parameters `lp`), at position `cidx` among the converted constructors.
pub(super) fn ctor_const(
  ctor_name: &Name,
  ctor: &ConstructorVal,
  lp: &[Name],
  induct: KId<Meta>,
  cidx: u64,
  ty: KExpr<Meta>,
) -> KConst<Meta> {
  KConst::Ctor {
    name: ctor_name.clone(),
    level_params: lp.to_vec(),
    is_unsafe: ctor.is_unsafe,
    lvls: lp.len() as u64,
    induct,
    cidx,
    params: nat_to_u64(&ctor.num_params),
    fields: nat_to_u64(&ctor.num_fields),
    ty,
  }
}

/// A non-inductive, non-constructor constant at full fidelity, converting
/// its type and then its value. `stub_proof_values` keeps only the type of
/// theorems and opaques (the decompiler's pre-warm). `None` for kinds that
/// are not ingested this way (constructors, recursors, inductives).
pub(super) fn full_const(
  name: &Name,
  ci: &LCI,
  zid: KId<Meta>,
  kenv: &mut KEnv<Meta>,
  stt: &crate::compile::CompileState,
  stub_proof_values: bool,
) -> Option<KConst<Meta>> {
  Some(match ci {
    LCI::DefnInfo(d) => {
      let lp = &d.cnst.level_params;
      let ty = to_z(&d.cnst.typ, lp, kenv, stt);
      let val = to_z(&d.value, lp, kenv, stt);
      KConst::Defn {
        name: name.clone(),
        level_params: lp.clone(),
        kind: ixon::constant::DefKind::Definition,
        safety: d.safety,
        hints: d.hints,
        lvls: lp.len() as u64,
        ty,
        val,
        lean_all: vec![],
        block: zid,
      }
    },
    LCI::ThmInfo(d) => {
      let lp = &d.cnst.level_params;
      let ty = to_z(&d.cnst.typ, lp, kenv, stt);
      // Theorem values are never delta-unfolded by kernel TC (Prop defeq
      // short-circuits on proof irrelevance); pre-warm callers keep the
      // type only, the fidelity `ingress_type_stub` gives theorems.
      if stub_proof_values {
        return Some(KConst::Axio {
          name: name.clone(),
          level_params: lp.clone(),
          is_unsafe: false,
          lvls: lp.len() as u64,
          ty,
        });
      }
      let val = to_z(&d.value, lp, kenv, stt);
      KConst::Defn {
        name: name.clone(),
        level_params: lp.clone(),
        kind: ixon::constant::DefKind::Theorem,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Opaque,
        lvls: lp.len() as u64,
        ty,
        val,
        lean_all: vec![],
        block: zid,
      }
    },
    LCI::OpaqueInfo(d) => {
      let lp = &d.cnst.level_params;
      let ty = to_z(&d.cnst.typ, lp, kenv, stt);
      // Opaque values are opaque to kernel defeq by definition.
      if stub_proof_values {
        return Some(KConst::Axio {
          name: name.clone(),
          level_params: lp.clone(),
          is_unsafe: false,
          lvls: lp.len() as u64,
          ty,
        });
      }
      let val = to_z(&d.value, lp, kenv, stt);
      KConst::Defn {
        name: name.clone(),
        level_params: lp.clone(),
        kind: ixon::constant::DefKind::Opaque,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Opaque,
        lvls: lp.len() as u64,
        ty,
        val,
        lean_all: vec![],
        block: zid,
      }
    },
    LCI::AxiomInfo(a) => {
      let lp = &a.cnst.level_params;
      let ty = to_z(&a.cnst.typ, lp, kenv, stt);
      KConst::Axio {
        name: name.clone(),
        level_params: lp.clone(),
        is_unsafe: a.is_unsafe,
        lvls: lp.len() as u64,
        ty,
      }
    },
    LCI::QuotInfo(q) => {
      let lp = &q.cnst.level_params;
      let ty = to_z(&q.cnst.typ, lp, kenv, stt);
      KConst::Quot {
        name: name.clone(),
        level_params: lp.clone(),
        kind: q.kind,
        lvls: lp.len() as u64,
        ty,
      }
    },
    LCI::InductInfo(_) | LCI::CtorInfo(_) | LCI::RecInfo(_) => return None,
  })
}

/// The type-only stub `ingress_type_stub` inserts.
pub(super) fn stub_const(
  name: &Name,
  level_params: &[Name],
  ty: KExpr<Meta>,
) -> KConst<Meta> {
  KConst::Axio {
    name: name.clone(),
    level_params: level_params.to_vec(),
    is_unsafe: false,
    lvls: level_params.len() as u64,
    ty,
  }
}

// ---------------------------------------------------------------------------
// Counters (reported under IX_VERBOSE at the end of the scheduler)
// ---------------------------------------------------------------------------

static BLOCK_CALLS: AtomicU64 = AtomicU64::new(0);
static BLOCK_INGESTED: AtomicU64 = AtomicU64::new(0);
static BLOCK_EAGER_EQUIV: AtomicU64 = AtomicU64::new(0);
static BLOCK_MAX_INGESTED: AtomicU64 = AtomicU64::new(0);
static BLOCK_MAX_EAGER_EQUIV: AtomicU64 = AtomicU64::new(0);
static BLOCK_MATERIALIZED: AtomicU64 = AtomicU64::new(0);
static BLOCK_DEFERRED: AtomicU64 = AtomicU64::new(0);

/// Account one finished aux_gen call against its kernel environment.
pub(crate) fn record(kctx: &crate::compile::KernelCtx) {
  let ingested = kctx.kenv.len() as u64;
  let eager_equiv = kctx.kenv.view_len() as u64;
  BLOCK_CALLS.fetch_add(1, Ordering::Relaxed);
  BLOCK_INGESTED.fetch_add(ingested, Ordering::Relaxed);
  BLOCK_EAGER_EQUIV.fetch_add(eager_equiv, Ordering::Relaxed);
  BLOCK_MAX_INGESTED.fetch_max(ingested, Ordering::Relaxed);
  BLOCK_MAX_EAGER_EQUIV.fetch_max(eager_equiv, Ordering::Relaxed);
  if let Some(s) = kctx.kenv.deferred_stats() {
    BLOCK_MATERIALIZED.fetch_add(s.materialized, Ordering::Relaxed);
    BLOCK_DEFERRED.fetch_add(s.registered, Ordering::Relaxed);
  }
}

/// One summary line of the counters above.
pub fn summary() -> String {
  let calls = BLOCK_CALLS.load(Ordering::Relaxed);
  format!(
    "{calls} calls, {} constants in their kernel envs (max {} in one call; \
     eager walk: {}, max {}), {} registered for deferred ingress of which \
     {} materialized",
    BLOCK_INGESTED.load(Ordering::Relaxed),
    BLOCK_MAX_INGESTED.load(Ordering::Relaxed),
    BLOCK_EAGER_EQUIV.load(Ordering::Relaxed),
    BLOCK_MAX_EAGER_EQUIV.load(Ordering::Relaxed),
    BLOCK_DEFERRED.load(Ordering::Relaxed),
    BLOCK_MATERIALIZED.load(Ordering::Relaxed),
  )
}
