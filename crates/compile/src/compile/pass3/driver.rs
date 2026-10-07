//! Pass 3 in the compile schedule. A port of `Ix/Compile/Pass/Driver.lean`
//! (hooks 1 and 2, image blocks) and of the Pass 3 parts of
//! `Ix/CompileDriver.lean` (`runImageBlock`, the insert-once merges).
//!
//! 1. **After the aux tail of a changed block** (`edit_changed_block`): no
//!    surgery plan; every Ix auxiliary the tail registered under a Lean name
//!    moves to its `_ix` display name; the block records its image-kind
//!    heads, its Lean `all`, Pass 2's canonical recursors and the classes and
//!    nested permutation of the component (what the view reads).
//! 2. **Before a block compiles** (`compile_block`): a block that references
//!    an image-kind head has its members rewritten (Def 3.6) into an overlay,
//!    with the source occurrences as decompile records; an image block (every
//!    member an image-kind head) compiles to the images under the Lean names,
//!    each of Lean's kind (F1), with `Named.original` from Lean's form.
//!
//! The definitional passes O1-O6 and O11a run at every full application of
//! a head (`opt::engine`, slice 2) and record their declines in the
//! non-canonical set. Before the rewrite, the changed-clique hook (slice 3,
//! [`super::clique::hook`]) refuses a caller that unfolds a transported
//! clique's encoding, puts the transported members in the block's overlay
//! and compiles the canonical constants they reach. The proof-justified
//! passes O7-O12 (slice 4, [`super::pj`]) run after the definitional ones;
//! decision 5 (D1): a Lean name keeps its baseline, and the canonical form
//! `c._ix` of a definition where one fires, O11b's `noConfusion` pair
//! (`unitPasses`) and the helpers the rewrites reference are rewritten in
//! place and compiled with the block (`compileCanon`, [`compile_canon`]),
//! a reserved name bound once to the same bytes.

use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::address::Address;
use ix_common::env::{
  ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, Env as LeanEnv,
  Expr, ExprData, Level, Name, ReducibilityHints, TheoremVal,
};
use ixon::CompileError;
use ixon::env::{AuxLayout, Named};

use crate::compile::{
  BlockCache, CompileState, KernelCtx, compile_const, compile_const_no_aux,
  compile_name, compile_single_def_parts, compile_single_definition,
};
use crate::graph::NameSet;
use crate::mutual::{Def, MutConst};

use super::Journal;
use super::clique::hook::{CliquePrep, HookEnv, consts_where, value_of};
use super::expr::{canonicalize_const_names, mk_str};
use super::names::{image_kinds, ix_aux_name, ix_form_name, reserved_input};
use super::opt::{
  Occ, OptBlock, OptEnv, engine_full, is_proof_justified, o11a_decline_cause,
  opt_block_of,
};
use super::pj::{no_confusion_of, o11b_rewrite};
use super::sidecar::{hash_map_of, rename_named};
use super::spec::NestedCanon;
use super::translate::{
  ExpansionLookup, OptHook, RwState, image_decl_with, rewrite_block,
};
use super::view::{
  BlockView, ComponentRecord, Expansion, ViewInput, build_view,
};

fn invalid(reason: String) -> CompileError {
  CompileError::InvalidMutualBlock { reason }
}

/// The out-of-component marker of an aux layout.
const PERM_OUT: usize = crate::compile::aux_gen::nested::PERM_OUT_OF_SCC;

/// D14: the first input name with a reserved component, as a rejection.
pub fn reserved_input_in<'a>(
  names: impl Iterator<Item = &'a Name>,
) -> Option<String> {
  let mut found: Vec<String> = names.filter_map(reserved_input).collect();
  found.sort();
  found.into_iter().next()
}

/// The classes of a compiled block restricted to Lean's `all`.
pub fn plan_classes(
  class_names: &[Vec<Name>],
  original_all: &[Name],
) -> Vec<Vec<Name>> {
  let lookup: FxHashSet<&Name> = original_all.iter().collect();
  class_names
    .iter()
    .filter_map(|c| {
      let ns: Vec<Name> =
        c.iter().filter(|n| lookup.contains(n)).cloned().collect();
      (!ns.is_empty()).then_some(ns)
    })
    .collect()
}

fn layout_perm(layout: Option<&AuxLayout>) -> Vec<Option<usize>> {
  layout
    .map(|l| {
      l.perm
        .iter()
        .map(|p| if *p == PERM_OUT { None } else { Some(*p) })
        .collect()
    })
    .unwrap_or_default()
}

/// Move the tail's registrations selected by `sel` to their display names
/// (`moveToDisplay`, a `SideCarEdit` with nothing kept); returns the moved
/// Lean names.
fn move_to_display(
  stt: &CompileState,
  members: &[Name],
  rep0: &Name,
  perm: &[Option<usize>],
  journal: &Journal,
  sel: &dyn Fn(&Name) -> bool,
) -> Result<FxHashSet<Name>, CompileError> {
  let mut display: Vec<(Name, Name)> = Vec::new();
  let mut seen: FxHashSet<Name> = FxHashSet::default();
  for n in &journal.claimed {
    if !seen.insert(n.clone()) || !sel(n) {
      continue;
    }
    if let Some(d) = ix_aux_name(members, rep0, perm, n) {
      display.push((n.clone(), d));
    }
  }
  let full = hash_map_of(&display);
  let moved: FxHashSet<Name> = display.iter().map(|(n, _)| n.clone()).collect();
  for (n, d) in &display {
    compile_name(d, stt);
    let named = stt.env.named.get(n).map(|r| r.clone());
    let addr = stt.aux_name_to_addr.get(n).map(|r| r.clone());
    stt.env.named.remove(n);
    stt.aux_name_to_addr.remove(n);
    stt.aux_gen_extra_names.remove(n);
    if let Some(named) = named {
      stt.register_named(d.clone(), rename_named(&full, &named));
    }
    if let Some(a) = addr {
      match stt.aux_name_to_addr.entry(d.clone()) {
        dashmap::mapref::entry::Entry::Occupied(e) => {
          if *e.get() != a {
            return Err(crate::compile::name_claim_conflict(d, e.get(), &a));
          }
        },
        dashmap::mapref::entry::Entry::Vacant(e) => {
          e.insert(a);
          crate::compile::block_txn::log_aux(d);
        },
      }
    }
  }
  // the entries that keep their names (synthetic `Muts` entries, names
  // without a display): references to moved names renamed
  if !full.is_empty() {
    let mut keep: Vec<Name> = journal.muts.clone();
    keep
      .extend(journal.claimed.iter().filter(|n| !moved.contains(*n)).cloned());
    for n in keep {
      if let Some(named) = stt.env.named.get(&n).map(|r| r.clone()) {
        stt.register_named(n, rename_named(&full, &named));
      }
    }
  }
  Ok(moved)
}

fn insert_recs(
  stt: &CompileState,
  recs: &[(Name, ix_common::env::RecursorVal)],
) -> Result<(), CompileError> {
  for (n, rv) in recs {
    if let Some(e) = stt.p3.canon_recs.get(n)
      && e.cnst.typ.get_hash() != rv.cnst.typ.get_hash()
    {
      return Err(invalid(format!(
        "Pass 3: conflicting canonical recursor '{}'",
        n.pretty()
      )));
    }
    stt.p3.canon_recs.insert(n.clone(), rv.clone());
  }
  Ok(())
}

/// Hook 1: the side-car edit and the driver records of a changed block
/// (`editChangedBlock`); returns the names to release to the scheduler.
pub fn edit_changed_block(
  stt: &CompileState,
  lean_env: &Arc<LeanEnv>,
  original_all: &[Name],
  class_names: &[Vec<Name>],
  layout: Option<&AuxLayout>,
  journal: Journal,
) -> Result<Vec<Name>, CompileError> {
  let planc = plan_classes(class_names, original_all);
  let (Some(rep0), Some(all0)) = (
    planc.first().and_then(|c| c.first()).cloned(),
    original_all.first().cloned(),
  ) else {
    return Ok(journal.pending);
  };
  let perm = layout_perm(layout);
  let const_of = |n: &Name| lean_env.get(n).map(|e| e.cloned());
  let heads = image_kinds(&const_of, original_all);
  let moved =
    move_to_display(stt, original_all, &rep0, &perm, &journal, &|_| true)?;
  for h in heads {
    insert_once(
      &stt.p3.heads,
      &h,
      all0.clone(),
      "image-kind head",
      crate::compile::block_txn::log_p3_head,
    )?;
  }
  insert_once(
    &stt.p3.blocks,
    &all0,
    original_all.to_vec(),
    "Lean block",
    crate::compile::block_txn::log_p3_block,
  )?;
  insert_recs(stt, &journal.recs)?;
  let nested = layout.map(|l| NestedCanon {
    perm: perm.clone(),
    num_canon: journal.n_canonical_aux,
    evaporated: l.evaporated.clone(),
  });
  let record = ComponentRecord { classes: planc.clone(), nested };
  for c in &planc {
    for m in c {
      stt.p3.components.insert(m.clone(), record.clone());
    }
  }
  Ok(journal.pending.into_iter().filter(|n| !moved.contains(n)).collect())
}

/// Hook 1b (A3V-IPB): an unchanged block whose Lean `IndPredBelow` family is
/// stored permuted is treated as a changed block whose members are Lean's
/// `below` inductives (`editPermutedBelowFamily`); returns the names to
/// release to the scheduler.
pub fn edit_permuted_below_family(
  stt: &CompileState,
  lean_env: &Arc<LeanEnv>,
  original_all: &[Name],
  journal: Journal,
) -> Result<Vec<Name>, CompileError> {
  let const_of = |n: &Name| lean_env.get(n).map(|e| e.cloned());
  let below_all: Vec<Name> = match original_all.first() {
    Some(a0) => match const_of(&mk_str(a0, "below")) {
      Some(ConstantInfo::InductInfo(v)) => v.all.clone(),
      _ => Vec::new(),
    },
    None => Vec::new(),
  };
  let Some(all0) = below_all.first().cloned() else {
    return Ok(journal.pending);
  };
  if below_all.len() < 2 {
    return Ok(journal.pending);
  }
  // the stored positions, in the one inductive block this tail registered
  let claimed: FxHashSet<&Name> = journal.claimed.iter().collect();
  let mut block: Option<Address> = None;
  let mut pos: Vec<usize> = Vec::new();
  for n in &below_all {
    if !claimed.contains(n) {
      return Ok(journal.pending);
    }
    let Some(a) = stt.aux_name_to_addr.get(n).map(|r| r.clone()) else {
      return Ok(journal.pending);
    };
    let Some(c) = stt.env.get_const(&a) else { return Ok(journal.pending) };
    let ixon::constant::ConstantInfo::IPrj(p) = &c.info else {
      return Ok(journal.pending);
    };
    if block.as_ref().is_some_and(|b| *b != p.block) {
      return Ok(journal.pending);
    }
    block = Some(p.block.clone());
    pos.push(p.idx as usize);
  }
  if pos.iter().enumerate().all(|(i, p)| i == *p) {
    return Ok(journal.pending);
  }
  let distinct: FxHashSet<usize> = pos.iter().copied().collect();
  if distinct.len() != pos.len() || journal.below_recs.is_empty() {
    return Ok(journal.pending);
  }
  let Some(k) = pos.iter().position(|p| *p == 0) else {
    return Ok(journal.pending);
  };
  let rep0 = below_all[k].clone();
  let mut ctors: FxHashSet<Name> = FxHashSet::default();
  for b in &below_all {
    if let Some(ConstantInfo::InductInfo(v)) = const_of(b) {
      ctors.extend(v.ctors.iter().cloned());
    }
  }
  let sel = |n: &Name| {
    !below_all.contains(n)
      && !ctors.contains(n)
      && below_all.iter().any(|b| super::expr::strip_prefix(b, n).is_some())
  };
  let moved = move_to_display(stt, &below_all, &rep0, &[], &journal, &sel)?;
  let heads = image_kinds(&const_of, &below_all);
  insert_recs(stt, &journal.below_recs)?;
  for h in heads {
    insert_once(
      &stt.p3.heads,
      &h,
      all0.clone(),
      "image-kind head",
      crate::compile::block_txn::log_p3_head,
    )?;
  }
  insert_once(
    &stt.p3.blocks,
    &all0,
    below_all.clone(),
    "Lean block",
    crate::compile::block_txn::log_p3_block,
  )?;
  // the view reads the family's canonical classes: its stored order
  let mut order: Vec<(usize, Name)> =
    pos.iter().copied().zip(below_all.iter().cloned()).collect();
  order.sort_by_key(|(p, _)| *p);
  let classes: Vec<Vec<Name>> =
    order.into_iter().map(|(_, n)| vec![n]).collect();
  let record = ComponentRecord { classes, nested: None };
  for b in &below_all {
    stt.p3.components.insert(b.clone(), record.clone());
  }
  Ok(journal.pending.into_iter().filter(|n| !moved.contains(n)).collect())
}

/// Insert-once into a Pass 3 record; a new entry is logged for the
/// failed-block rollback (`log`).
fn insert_once<V: PartialEq + Clone>(
  m: &dashmap::DashMap<Name, V>,
  k: &Name,
  v: V,
  what: &str,
  log: fn(&Name),
) -> Result<(), CompileError> {
  match m.entry(k.clone()) {
    dashmap::mapref::entry::Entry::Occupied(e) => {
      if *e.get() != v {
        return Err(invalid(format!(
          "Pass 3: conflicting {what} '{}'",
          k.pretty()
        )));
      }
    },
    dashmap::mapref::entry::Entry::Vacant(e) => {
      e.insert(v);
      log(k);
    },
  }
  Ok(())
}

/// The changed-block predicate (Def 3.1 under the compiler's rules; the
/// plan predicate of `compile_mutual`).
pub fn is_changed(
  class_names: &[Vec<Name>],
  original_all: &[Name],
  layout: Option<&AuxLayout>,
) -> bool {
  let planc = plan_classes(class_names, original_all);
  let user = !original_all.is_empty()
    && (planc.len() < original_all.len()
      || (planc.len() == original_all.len()
        && planc.iter().zip(original_all.iter()).any(|(c, o)| c[0] != *o)));
  let aux = layout.is_some_and(|l| {
    l.evaporated.iter().any(|b| *b)
      || l.perm.iter().enumerate().any(|(j, i)| *i != PERM_OUT && *i != j)
  });
  user || aux
}

// ---------------------------------------------------------------------------
// Hook 2
// ---------------------------------------------------------------------------

/// The view input of the compile state.
struct Ctx<'a> {
  lean_env: &'a Arc<LeanEnv>,
  stt: &'a CompileState,
}

impl Ctx<'_> {
  fn with_input<R>(&self, f: impl FnOnce(&ViewInput<'_>) -> R) -> R {
    let const_of = |n: &Name| self.lean_env.get(n).map(|e| e.cloned());
    let compiled = |n: &Name| self.stt.resolve_addr(n).is_some();
    let component_of =
      |n: &Name| self.stt.p3.components.get(n).map(|r| r.clone());
    let canon_rec = |n: &Name| self.stt.p3.canon_recs.get(n).map(|r| r.clone());
    let inp = ViewInput {
      const_of: &const_of,
      compiled: &compiled,
      component_of: &component_of,
      canon_rec: &canon_rec,
    };
    f(&inp)
  }
}

/// The heads a constant mentions (`headsIn`).
fn heads_in(stt: &CompileState, ci: &ConstantInfo) -> FxHashSet<Name> {
  let mut roots: Vec<Expr> = vec![ci.get_type().clone()];
  match ci {
    ConstantInfo::DefnInfo(v) => roots.push(v.value.clone()),
    ConstantInfo::ThmInfo(v) => roots.push(v.value.clone()),
    ConstantInfo::OpaqueInfo(v) => roots.push(v.value.clone()),
    ConstantInfo::RecInfo(v) => {
      roots.extend(v.rules.iter().map(|r| r.rhs.clone()))
    },
    _ => {},
  }
  let mut seen: FxHashSet<blake3::Hash> = FxHashSet::default();
  let mut out = FxHashSet::default();
  let mut stack = roots;
  while let Some(x) = stack.pop() {
    if !seen.insert(*x.get_hash()) {
      continue;
    }
    match x.as_data() {
      ExprData::Const(n, _, _) => {
        if stt.p3.heads.contains_key(n) {
          out.insert(n.clone());
        }
      },
      ExprData::App(f, a, _) => {
        stack.push(a.clone());
        stack.push(f.clone());
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        stack.push(b.clone());
        stack.push(t.clone());
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        stack.push(b.clone());
        stack.push(v.clone());
        stack.push(t.clone());
      },
      ExprData::Proj(_, _, s, _) | ExprData::Mdata(_, s, _) => {
        stack.push(s.clone())
      },
      _ => {},
    }
  }
  out
}

/// The views of the changed blocks of `heads`, built once per block.
fn views_of(
  ctx: &Ctx<'_>,
  heads: impl Iterator<Item = Name>,
) -> Result<FxHashMap<Name, BlockView>, String> {
  let mut views: FxHashMap<Name, BlockView> = FxHashMap::default();
  for h in heads {
    let Some(key) = ctx.stt.p3.heads.get(&h).map(|r| r.clone()) else {
      continue;
    };
    if views.contains_key(&key) {
      continue;
    }
    let all = ctx
      .stt
      .p3
      .blocks
      .get(&key)
      .map_or_else(|| vec![key.clone()], |r| r.clone());
    let v = ctx.with_input(|inp| build_view(inp, &all))?;
    views.insert(key, v);
  }
  Ok(views)
}

/// The expansion lookup over the views (`expansionLookup`), building a view
/// on demand for a head of a block not yet viewed.
fn expansion_lookup(
  ctx: &Ctx<'_>,
  views: &mut FxHashMap<Name, BlockView>,
  n: &Name,
) -> Result<Option<Expansion>, String> {
  let Some(key) = ctx.stt.p3.heads.get(n).map(|r| r.clone()) else {
    return Ok(None);
  };
  if !views.contains_key(&key) {
    let more = views_of(ctx, std::iter::once(n.clone()))?;
    views.extend(more);
  }
  let v = views.get(&key).ok_or("Pass 3: view missing")?;
  let (x, _) = ctx.with_input(|inp| v.expansion(inp, n))?;
  Ok(Some(x))
}

/// Run `f` on a thread with a large stack: the rewrite and the development
/// recurse on the terms, which are deep proofs on a library.
fn with_big_stack<R: Send>(f: impl FnOnce() -> R + Send) -> R {
  std::thread::scope(|s| {
    std::thread::Builder::new()
      .stack_size(1 << 30)
      .spawn_scoped(s, f)
      .expect("Pass 3: spawn the rewrite thread")
      .join()
      .unwrap_or_else(|p| std::panic::resume_unwind(p))
  })
}

/// What `prepare_block` gives a block: the rewritten members, the decompile
/// sources, the recorded declines, and the block's canonical constants (D1)
/// rewritten in place, each with its decompile sources (`compileCanon`'s
/// first loop; compiled by [`compile_canon`] on the block's thread).
struct Prepared {
  overlay: FxHashMap<Name, ConstantInfo>,
  sources: Vec<Expr>,
  declines: Vec<(Name, String)>,
  canon: Vec<(ConstantInfo, Vec<Expr>)>,
}

/// The canonical `_ix` form of a compiled dependency (decision 5, D1,
/// `Driver.ixFormOf`): `d ↦ d._ix` when `d` is a definition of the input
/// (never an image-kind head) and `d._ix` is compiled. Read only by O10 and
/// O12, which compare handlers through their references' canonical forms
/// (`OptEnv.canonAddrOf`); no reference is renamed to it.
fn ix_form_of(ctx: &Ctx<'_>, d: &Name) -> Option<Name> {
  if !ctx
    .lean_env
    .get(d)
    .is_some_and(|e| matches!(&*e, ConstantInfo::DefnInfo(_)))
  {
    return None;
  }
  if ctx.stt.p3.heads.contains_key(d) {
    return None;
  }
  let c = ix_form_name(d);
  ctx.stt.resolve_addr(&c).map(|_| c)
}

/// The definitional passes' blocks (`optBlocks`) of the given views.
fn opt_blocks(
  ctx: &Ctx<'_>,
  views: &FxHashMap<Name, BlockView>,
) -> FxHashMap<Name, OptBlock> {
  views
    .iter()
    .map(|(k, v)| (k.clone(), ctx.with_input(|inp| opt_block_of(v, inp))))
    .collect()
}

/// The unit passes over a block's members (`Driver.unitPasses`): O11b gives
/// Lean's `noConfusion` pair of a split-off enumeration its enumeration form
/// as the canonical constants `T.noConfusionType._ix`, `T.noConfusion._ix`
/// (D1: the Lean names keep Lean's general form); the type of
/// `T.noConfusion._ix` refers to `T.noConfusionType._ix` (one decision,
/// Lemma O11b.2). `classesOf` reads the views of the block's referenced
/// changed blocks only (`initial`, Lean's `views` of `prepareBlock`).
fn unit_passes(
  ctx: &Ctx<'_>,
  views: &FxHashMap<Name, BlockView>,
  initial: &FxHashSet<Name>,
  members: &[(Name, ConstantInfo)],
) -> Vec<ConstantInfo> {
  let const_of = |n: &Name| ctx.lean_env.get(n).map(|e| e.cloned());
  let classes_of = |t: &Name| -> Option<Vec<Vec<Name>>> {
    let key = ctx.stt.p3.heads.get(&mk_str(t, "casesOn")).map(|r| r.clone())?;
    if !initial.contains(&key) {
      return None;
    }
    let v = views.get(&key)?;
    let c = v.canon.components.iter().find(|c| c.members.contains(t))?;
    Some(c.classes.clone())
  };
  let mut canon = Vec::new();
  for (n, ci) in members {
    let Some(dv) = o11b_rewrite(&const_of, &classes_of, n, ci) else {
      continue;
    };
    let c = ix_form_name(n);
    // the pair is decided together (`O11b.pairApplies`): the canonical
    // `noConfusion` is typed over the canonical `noConfusionType`
    let typ = match no_confusion_of(n) {
      Some((t, false)) => {
        let nct = mk_str(&t, "noConfusionType");
        let mut m: FxHashMap<Name, Name> = FxHashMap::default();
        m.insert(nct.clone(), ix_form_name(&nct));
        canonicalize_const_names(&m, &dv.cnst.typ)
      },
      _ => dv.cnst.typ.clone(),
    };
    canon.push(ConstantInfo::DefnInfo(DefinitionVal {
      cnst: ConstantVal { name: c.clone(), typ, ..dv.cnst.clone() },
      all: vec![c],
      ..dv
    }));
  }
  canon
}

/// `compileCanon`'s first loop: each canonical constant rewritten **in
/// place** (`rewriteBlock` with `inPlace`: the proof-justified passes rewrite
/// a canonical constant itself), whose own helpers join the work list; each
/// name once. No reference is renamed: a canonical constant refers to its
/// dependencies by their Lean names.
fn rewrite_canon<'h>(
  lookup: &mut ExpansionLookup<'_>,
  opt: &'h OptHook<'h>,
  canon: Vec<ConstantInfo>,
) -> Result<Vec<(ConstantInfo, Vec<Expr>)>, String> {
  let mut queue = canon;
  let mut i = 0;
  let mut seen: FxHashSet<Name> = FxHashSet::default();
  let mut done = Vec::new();
  while i < queue.len() {
    let ci = queue[i].clone();
    i += 1;
    let c = ci.get_name().clone();
    if !seen.insert(c.clone()) {
      continue;
    }
    let rw = rewrite_block(lookup, &[(c, ci.clone())], Some(opt), None, true)?;
    let ci2 = rw.overlay.into_iter().next().map_or(ci, |x| x.1);
    queue.extend(rw.canon);
    done.push((ci2, rw.sources));
  }
  Ok(done)
}

/// The overlay, decompile sources and recorded declines of a block
/// (`prepareBlock`, with the optimisation passes `optLookup` and the
/// decline records `declineLookup`), and its canonical constants rewritten
/// in place (`compileCanon`); `None` when the block references no head.
fn prepare_block(
  ctx: &Ctx<'_>,
  all: &NameSet,
  clq_overlay: &FxHashMap<Name, ConstantInfo>,
) -> Result<Option<Prepared>, String> {
  if ctx.stt.p3.heads.is_empty() {
    return Ok(None);
  }
  let mut members: Vec<(Name, ConstantInfo)> = Vec::new();
  let mut used: Vec<Name> = Vec::new();
  let mut sorted: Vec<&Name> = all.iter().collect();
  sorted.sort_by_key(|n| n.pretty());
  for n in sorted {
    // a transported clique member is read from the clique hook's overlay
    // (Lean reads `cenv.env`, which carries it)
    let ci = clq_overlay
      .get(n)
      .cloned()
      .or_else(|| ctx.lean_env.get(n).map(|e| e.cloned()));
    if let Some(ci) = ci {
      for h in heads_in(ctx.stt, &ci) {
        if !used.contains(&h) {
          used.push(h);
        }
      }
      members.push((n.clone(), ci));
    }
  }
  if used.is_empty() {
    return Ok(None);
  }
  // Lean rewrites the members in `Set` iteration order; the placeholder
  // indices follow it. Its order is the order of `all` as the scheduler's
  // set holds it; see the report's documentation gap on this point.
  let mut views = views_of(ctx, used.into_iter())?;
  // the views of the referenced changed blocks (Lean's `views`; the lookup
  // below adds others on demand, which the passes and O11b do not see)
  let initial: FxHashSet<Name> = views.keys().cloned().collect();
  // the passes' blocks of the referenced changed blocks (`optBlocks`, once
  // per rewrite); heads of other blocks keep their baseline
  let blocks = opt_blocks(ctx, &views);
  let resolves = |n: &Name| ctx.stt.resolve_addr(n).is_some();
  let addr_of = |n: &Name| ctx.stt.resolve_addr(n);
  let ix_form = |d: &Name| ix_form_of(ctx, d);
  let block_of = |h: &Name| -> Option<&OptBlock> {
    let key = ctx.stt.p3.heads.get(h).map(|r| r.clone())?;
    blocks.get(&key)
  };
  // `optLookup`'s environment, and `declineLookup`'s (Lean's defaults for
  // the addresses and canonical forms, which O11a does not read)
  let env = OptEnv {
    ienv: ctx.lean_env.as_ref(),
    resolves: &resolves,
    block_of: &block_of,
    addr_of: Some(&addr_of),
    ix_form: Some(&ix_form),
  };
  let denv = OptEnv {
    ienv: ctx.lean_env.as_ref(),
    resolves: &resolves,
    block_of: &block_of,
    addr_of: None,
    ix_form: None,
  };
  let opt = |site: Option<&Name>, n: &Name, us: &[Level], args: &[Expr]| {
    engine_full(&env, &Occ { head: n, us, args, site })
      .map(|(nm, e, cs)| (e, cs, is_proof_justified(nm)))
  };
  let decline = |n: &Name, us: &[Level], args: &[Expr]| {
    o11a_decline_cause(&denv, &Occ { head: n, us, args, site: None })
  };
  let rw = {
    let mut lookup = |n: &Name| expansion_lookup(ctx, &mut views, n);
    rewrite_block(&mut lookup, &members, Some(&opt), Some(&decline), false)?
  };
  // the canonical constants (D1): the `_ix` forms where a proof-justified
  // pass fires, the unit passes' (O11b), the helpers the rewrites reference
  let mut queue = rw.canon;
  queue.extend(unit_passes(ctx, &views, &initial, &members));
  let canon = {
    let mut lookup = |n: &Name| expansion_lookup(ctx, &mut views, n);
    rewrite_canon(&mut lookup, &opt, queue)?
  };
  Ok(Some(Prepared {
    overlay: rw.overlay.into_iter().collect(),
    sources: rw.sources,
    declines: rw.declines,
    canon,
  }))
}

/// Every member of the block is an image-kind head (`isImageBlock`).
fn is_image_block(stt: &CompileState, all: &NameSet) -> bool {
  !all.is_empty() && all.iter().all(|n| stt.p3.heads.contains_key(n))
}

/// The image constant of head `a` with Lean's kind (F1).
fn image_def(
  lean_env: &Arc<LeanEnv>,
  a: &Name,
  x: &Expansion,
  value: Expr,
  typ: Expr,
) -> Def {
  let cnst =
    ConstantVal { name: a.clone(), level_params: x.level_params.clone(), typ };
  match lean_env.get(a).map(|e| e.cloned()) {
    Some(ConstantInfo::ThmInfo(_)) => {
      Def::mk_theo(&TheoremVal { cnst, value, all: vec![a.clone()] })
    },
    other => {
      let safety = match other {
        Some(ConstantInfo::DefnInfo(d)) => d.safety,
        Some(ConstantInfo::RecInfo(r)) => {
          if r.is_unsafe {
            DefinitionSafety::Unsafe
          } else {
            DefinitionSafety::Safe
          }
        },
        _ => DefinitionSafety::Safe,
      };
      Def::mk_defn(&DefinitionVal {
        cnst,
        value,
        hints: ReducibilityHints::Abbrev,
        safety,
        all: vec![a.clone()],
      })
    },
  }
}

/// Compile an image block (`compileImageBlock`, `runImageBlock`).
fn compile_image_block(
  ctx: &Ctx<'_>,
  lo: &Name,
  all: &NameSet,
  kctx: &mut KernelCtx,
) -> Result<Address, CompileError> {
  let stt = ctx.stt;
  let mut pending: Vec<Name> = all.iter().cloned().collect();
  pending.sort_by_key(|n| n.pretty());
  let decls: Vec<(Name, Def)> =
    with_big_stack(|| -> Result<Vec<(Name, Def)>, String> {
      let mut views = views_of(ctx, pending.iter().cloned())?;
      let mut st = RwState::default();
      let mut out = Vec::new();
      for a in &pending {
        let key =
          stt.p3.heads.get(a).map(|r| r.clone()).ok_or("Pass 3: not a head")?;
        let (x, ty) = {
          let v = views.get(&key).ok_or("Pass 3: view missing")?;
          ctx.with_input(|inp| v.expansion(inp, a))?
        };
        let mut lookup = |n: &Name| expansion_lookup(ctx, &mut views, n);
        let (value, typ) = image_decl_with(&mut st, &mut lookup, a, &x, &ty)?;
        out.push((a.clone(), image_def(ctx.lean_env, a, &x, value, typ)));
      }
      Ok(out)
    })
    .map_err(invalid)?;
  // compile, each once the images it references are
  let mut rest: Vec<(Name, Def)> = decls;
  let mut rounds = rest.len() + 1;
  let mut last_err: Option<CompileError> = None;
  let mut compiled: Vec<Name> = Vec::new();
  let mut hints: Vec<(Name, ReducibilityHints)> = Vec::new();
  while !rest.is_empty() && rounds > 0 {
    rounds -= 1;
    let mut next = Vec::new();
    for (a, d) in rest {
      let mut cache = BlockCache::default();
      match compile_single_definition(&a, &d, &mut cache, stt) {
        Ok((addr, _)) => {
          if stt.aux_name_to_addr.insert(a.clone(), addr).is_none() {
            crate::compile::block_txn::log_aux(&a);
          }
          hints.push((a.clone(), d.hints));
          compiled.push(a);
        },
        Err(e) => {
          last_err = Some(invalid(format!(
            "Pass 3: image constant {}: {e}",
            a.pretty()
          )));
          next.push((a, d));
        },
      }
    }
    rest = next;
  }
  if !rest.is_empty() {
    return Err(
      last_err.unwrap_or_else(|| invalid("Pass 3: image block".into())),
    );
  }
  // `Named.original`: Lean's form compiled without any rewrite
  let mut orig_cache = BlockCache::default();
  compile_const_no_aux(lo, all, ctx.lean_env, &mut orig_cache, stt, kctx)?;
  // the image's hints, not the original's (Lean merges only the images'
  // block states' `defHints` in `runImageBlock`)
  for (a, h) in hints {
    stt.def_hints.insert(a, h);
  }
  for a in &compiled {
    if let Some(addr) = stt.aux_name_to_addr.get(a).map(|r| r.clone()) {
      stt.claim_compiled_name(a, &addr)?;
    }
  }
  stt
    .resolve_addr(lo)
    .ok_or_else(|| invalid(format!("Pass 3: no image for {}", lo.pretty())))
}

/// The clique hook's environment over the compile state.
fn with_hook_env<R>(ctx: &Ctx<'_>, f: impl FnOnce(&HookEnv<'_>) -> R) -> R {
  let const_of = |n: &Name| ctx.lean_env.get(n).map(|e| e.cloned());
  let addr = |n: &Name| ctx.stt.resolve_addr(n);
  let env = HookEnv {
    const_of: &const_of,
    addr: &addr,
    table: &ctx.stt.p3.cliques,
    roots: &ctx.stt.p3.clique_roots,
    plans: &ctx.stt.p3.clique_plans,
  };
  f(&env)
}

/// The call-site rewrite of one canonical constant of the clique hook
/// (`cliqueRewrite`: `optLookup`, no decline records, not in place, so no
/// proof-justified pass fires inside a transported clique): the rewritten
/// constant and its decompile sources.
fn clique_rewrite(
  ctx: &Ctx<'_>,
  c: &Name,
  ci: &ConstantInfo,
) -> Result<(ConstantInfo, Vec<Expr>), String> {
  let heads = heads_in(ctx.stt, ci);
  if heads.is_empty() {
    return Ok((ci.clone(), Vec::new()));
  }
  let mut views = views_of(ctx, heads.into_iter())?;
  let blocks = opt_blocks(ctx, &views);
  let resolves = |n: &Name| ctx.stt.resolve_addr(n).is_some();
  let addr_of = |n: &Name| ctx.stt.resolve_addr(n);
  let ix_form = |d: &Name| ix_form_of(ctx, d);
  let block_of = |h: &Name| -> Option<&OptBlock> {
    let key = ctx.stt.p3.heads.get(h).map(|r| r.clone())?;
    blocks.get(&key)
  };
  let env = OptEnv {
    ienv: ctx.lean_env.as_ref(),
    resolves: &resolves,
    block_of: &block_of,
    addr_of: Some(&addr_of),
    ix_form: Some(&ix_form),
  };
  let opt = |site: Option<&Name>, n: &Name, us: &[Level], args: &[Expr]| {
    engine_full(&env, &Occ { head: n, us, args, site })
      .map(|(nm, e, cs)| (e, cs, is_proof_justified(nm)))
  };
  let mut lookup = |n: &Name| expansion_lookup(ctx, &mut views, n);
  let members = vec![(c.clone(), ci.clone())];
  let rw = rewrite_block(&mut lookup, &members, Some(&opt), None, false)?;
  let ci2 = rw.overlay.into_iter().next().map_or_else(|| ci.clone(), |x| x.1);
  Ok((ci2, rw.sources))
}

/// Compile the canonical constants a block's transported members reach
/// (`prepareCliques`' rounds), each once its canonical references are;
/// returns the names this block compiled (Lean's `init.blockNameToAddr`).
fn compile_clique_canon(
  ctx: &Ctx<'_>,
  prep: &CliquePrep,
) -> Result<Vec<Name>, CompileError> {
  let stt = ctx.stt;
  let mut compiled: Vec<Name> = Vec::new();
  let mut pending: Vec<Name> = prep
    .wanted
    .iter()
    .filter(|c| stt.resolve_addr(c).is_none())
    .cloned()
    .collect();
  pending.sort_by_key(|n| n.pretty());
  let mut rounds = pending.len() + 1;
  while !pending.is_empty() && rounds > 0 {
    rounds -= 1;
    let mut rest = Vec::new();
    for c in pending {
      let Some(ci) = prep.canon.get(&c) else {
        return Err(invalid(format!(
          "Pass 3 cliques: no canonical constant {}",
          c.pretty()
        )));
      };
      let p = |r: &Name| prep.canon.contains_key(r) && *r != c;
      let mut refs = consts_where(&p, ci.get_type());
      if let Some(v) = value_of(ci) {
        refs.extend(consts_where(&p, &v));
      }
      if refs.iter().any(|r| stt.resolve_addr(r).is_none()) {
        rest.push(c);
        continue;
      }
      let (ci2, sources) =
        with_big_stack(|| clique_rewrite(ctx, &c, ci)).map_err(invalid)?;
      let def = match &ci2 {
        ConstantInfo::DefnInfo(v) => Def::mk_defn(v),
        ConstantInfo::ThmInfo(v) => Def::mk_theo(v),
        _ => {
          return Err(invalid(format!(
            "Pass 3 cliques: canonical constant {}: not a definition",
            c.pretty()
          )));
        },
      };
      let mut cache = BlockCache {
        p3_sources: sources.into_iter().enumerate().collect(),
        ..Default::default()
      };
      let (addr, _) = compile_single_definition(&c, &def, &mut cache, stt)
        .map_err(|e| {
          invalid(format!(
            "Pass 3 cliques: canonical constant {}: {e}",
            c.pretty()
          ))
        })?;
      if stt.aux_name_to_addr.insert(c.clone(), addr).is_none() {
        crate::compile::block_txn::log_aux(&c);
      }
      compiled.push(c);
    }
    pending = rest;
  }
  if !pending.is_empty() {
    let ns: Vec<String> = pending.iter().map(|n| n.pretty()).collect();
    return Err(invalid(format!(
      "Pass 3 cliques: canonical constants with cyclic references: {}",
      crate::compile::pass3::clique::basic::arr_str(&ns)
    )));
  }
  Ok(compiled)
}

/// Compile the block's canonical constants (reserved `_ix` names,
/// `compileCanon`'s compile rounds), rewritten in place by [`prepare_block`]:
/// each as an ordinary constant once the canonical constants it references
/// are (`bound`: the names this block bound, its clique hook's first). A
/// reserved name already bound (O12's `fg`, emitted by both functions'
/// blocks; a canonical constant of the clique hook) must be bound to the
/// same bytes, which are then not stored again; a different binding fails
/// the compile (a reserved-name clash is refused, never resolved silently).
fn compile_canon(
  stt: &CompileState,
  done: Vec<(ConstantInfo, Vec<Expr>)>,
  bound: &mut FxHashSet<Name>,
) -> Result<(), CompileError> {
  let names: FxHashSet<Name> =
    done.iter().map(|(ci, _)| ci.get_name().clone()).collect();
  let mut pending = done;
  let mut rounds = pending.len() + 1;
  while !pending.is_empty() && rounds > 0 {
    rounds -= 1;
    let mut rest = Vec::new();
    for (ci, srcs) in pending {
      let c = ci.get_name().clone();
      let p = |r: &Name| names.contains(r) && *r != c;
      let mut refs = consts_where(&p, ci.get_type());
      if let Some(v) = value_of(&ci) {
        refs.extend(consts_where(&p, &v));
      }
      if refs.iter().any(|r| !bound.contains(r)) {
        rest.push((ci, srcs));
        continue;
      }
      let def = match &ci {
        ConstantInfo::DefnInfo(v) => Def::mk_defn(v),
        ConstantInfo::ThmInfo(v) => Def::mk_theo(v),
        _ => {
          return Err(invalid(format!(
            "Pass 3 optimisations: canonical constant {}: not a definition",
            c.pretty()
          )));
        },
      };
      let mut cache = BlockCache {
        p3_sources: srcs.into_iter().enumerate().collect(),
        ..Default::default()
      };
      let prev_hints = stt.def_hints.get(&c).map(|r| *r);
      let (addr, meta, constant) =
        compile_single_def_parts(&c, &def, &mut cache, stt).map_err(|e| {
          invalid(format!(
            "Pass 3 optimisations: canonical constant {}: {e}",
            c.pretty()
          ))
        })?;
      let clash = |a: &Address| {
        // the hints this compile recorded belong to no binding
        match prev_hints {
          Some(h) => {
            stt.def_hints.insert(c.clone(), h);
          },
          None => {
            stt.def_hints.remove(&c);
          },
        }
        invalid(format!(
          "Pass 3 optimisations: reserved name {} is already bound to {}, not \
to the canonical constant {}",
          c.pretty(),
          a.hex(),
          addr.hex()
        ))
      };
      match stt.name_to_addr.get(&c).map(|r| r.clone()) {
        Some(a) => {
          if a != addr {
            return Err(clash(&a));
          }
        },
        None => match stt.aux_name_to_addr.entry(c.clone()) {
          dashmap::mapref::entry::Entry::Occupied(e) => {
            if *e.get() != addr {
              let a = e.get().clone();
              drop(e);
              return Err(clash(&a));
            }
          },
          dashmap::mapref::entry::Entry::Vacant(e) => {
            e.insert(addr.clone());
            crate::compile::block_txn::log_aux(&c);
            stt.env.store_const(addr.clone(), constant);
            stt.register_named(c.clone(), Named::new(addr, meta));
          },
        },
      }
      bound.insert(c);
    }
    pending = rest;
  }
  if !pending.is_empty() {
    let ns: Vec<String> =
      pending.iter().map(|(ci, _)| ci.get_name().pretty()).collect();
    return Err(invalid(format!(
      "Pass 3 optimisations: canonical constants with cyclic references: {}",
      crate::compile::pass3::clique::basic::arr_str(&ns)
    )));
  }
  Ok(())
}

/// Compile one scheduled block under Pass 3 (hook 2 and image blocks), the
/// scheduler's only route since M6R slice 6 (the switch-off route, plain
/// `compile_const` with the legacy surgery, is deleted).
pub fn compile_block(
  lo: &Name,
  all: &NameSet,
  lean_env: &Arc<LeanEnv>,
  cache: &mut BlockCache,
  stt: &CompileState,
  kctx: &mut KernelCtx,
) -> Result<Address, CompileError> {
  let ctx = Ctx { lean_env, stt };
  if is_image_block(stt, all) {
    return compile_image_block(&ctx, lo, all, kctx);
  }
  // the changed-clique hook (`prepareCliques`): the callers' refusal, the
  // transported members and the canonical constants they reach
  let prep = if stt.p3.cliques.is_empty() {
    CliquePrep::default()
  } else {
    let mut refs: Vec<Name> =
      stt.p3.clique_refs.get(lo).cloned().unwrap_or_default();
    refs.sort_by_key(|n| n.pretty());
    with_big_stack(|| with_hook_env(&ctx, |h| h.prepare(all, &refs)))
      .map_err(invalid)?
  };
  // the reserved names this block binds (Lean's `init.blockNameToAddr`)
  let mut bound: FxHashSet<Name> = FxHashSet::default();
  if !prep.overlay.is_empty() {
    bound.extend(compile_clique_canon(&ctx, &prep)?);
  }
  let prepared = with_big_stack(|| prepare_block(&ctx, all, &prep.overlay))
    .map_err(invalid)?;
  cache.p3_overlay = prep.overlay.clone();
  cache.p3_sources = prep.sources.iter().cloned().collect();
  if let Some(p) = prepared {
    cache.p3_overlay.extend(p.overlay);
    cache.p3_sources.extend(p.sources.into_iter().enumerate());
    cache.p3_declines = p.declines;
    // the canonical constants (D1), compiled before the members, as Lean's
    // `prepareBlock` compiles them into the block's initial state
    compile_canon(stt, p.canon, &mut bound)?;
  }
  let res = compile_const(lo, all, lean_env, cache, stt, kctx);
  // the recorded declines join the compile's non-canonical set when the
  // block compiles (the Lean driver merges a block's state only then)
  if res.is_ok() {
    for (n, c) in std::mem::take(&mut cache.p3_declines) {
      stt.p3.non_canonical.insert(n, c);
    }
  }
  let _ = Named::with_addr;
  res
}

/// Canonical recursors of a set of aux patches (for the journal).
pub fn patch_recs(
  patches: &FxHashMap<Name, crate::compile::aux_gen::PatchedConstant>,
) -> Vec<(Name, ix_common::env::RecursorVal)> {
  patches
    .iter()
    .filter_map(|(n, p)| match p {
      crate::compile::aux_gen::PatchedConstant::Rec(r) => {
        Some((n.clone(), r.clone()))
      },
      _ => None,
    })
    .collect()
}

#[allow(dead_code)]
fn _unused(_: MutConst) {}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::compile::pass3::expr::dotted;

  fn sort(n: u32) -> Expr {
    let mut l = Level::zero();
    for _ in 0..n {
      l = Level::succ(l);
    }
    Expr::sort(l)
  }

  /// A canonical constant `name : typ := value`.
  fn canon(name: &str, typ: Expr, value: Expr) -> ConstantInfo {
    let n = dotted(name);
    ConstantInfo::DefnInfo(DefinitionVal {
      cnst: ConstantVal { name: n.clone(), level_params: vec![], typ },
      value,
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![n],
    })
  }

  #[test]
  fn reserved_name_bound_once_to_the_same_bytes() {
    let stt = CompileState::new_empty();
    let c = dotted("T.f._ix");
    let first = canon("T.f._ix", sort(1), sort(0));
    let mut bound = FxHashSet::default();
    compile_canon(&stt, vec![(first.clone(), vec![])], &mut bound).unwrap();
    let a = stt.resolve_addr(&c).expect("bound");
    assert!(stt.env.named.contains_key(&c));
    assert!(bound.contains(&c));
    // valid neighbour: another block binds the same name to the same bytes
    let mut bound2 = FxHashSet::default();
    compile_canon(&stt, vec![(first, vec![])], &mut bound2).unwrap();
    assert_eq!(stt.resolve_addr(&c), Some(a.clone()));
    assert!(bound2.contains(&c));
    // a different constant under the same reserved name is refused
    let other = canon("T.f._ix", sort(2), sort(1));
    let err =
      compile_canon(&stt, vec![(other, vec![])], &mut FxHashSet::default())
        .unwrap_err()
        .to_string();
    assert!(err.contains("reserved name T.f._ix is already bound to"), "{err}");
    assert_eq!(stt.resolve_addr(&c), Some(a));
  }

  #[test]
  fn canonical_constants_compile_after_their_references() {
    let stt = CompileState::new_empty();
    // `A._ix` refers to `B._ix`, listed first: compiled in the second round
    let a = canon("A._ix", sort(2), Expr::cnst(dotted("B._ix"), vec![]));
    let b = canon("B._ix", sort(2), sort(1));
    let mut bound = FxHashSet::default();
    compile_canon(&stt, vec![(a, vec![]), (b, vec![])], &mut bound).unwrap();
    assert!(stt.resolve_addr(&dotted("A._ix")).is_some());
    assert!(stt.resolve_addr(&dotted("B._ix")).is_some());
    // two that refer to each other are refused by name
    let c = canon("C._ix", sort(2), Expr::cnst(dotted("D._ix"), vec![]));
    let d = canon("D._ix", sort(2), Expr::cnst(dotted("C._ix"), vec![]));
    let err = compile_canon(&stt, vec![(c, vec![]), (d, vec![])], &mut bound)
      .unwrap_err()
      .to_string();
    assert!(
      err.contains("canonical constants with cyclic references"),
      "{err}"
    );
  }
}
