//! Pass 3 in the compile schedule. A port of `Ix/Compile/Pass/Driver.lean`
//! (the two hooks of the block compile, image blocks) and of the Pass 3 parts
//! of `Ix/CompileDriver.lean` (`runImageBlock`, the insert-once merges).
//!
//! 1. **After the aux tail of a changed block** ([`edit_changed_block`]):
//!    no call-site plan; every Ix auxiliary the tail registered under a Lean
//!    name moves to its `_ix` display name; the block records its image-kind
//!    heads, its Lean `all`, Pass 2's canonical recursors and the classes and
//!    nested permutation of the component (what the view reads). An
//!    unchanged block whose Lean `IndPredBelow` family is stored permuted is
//!    edited the same way, with the family as the block
//!    ([`edit_permuted_below_family`]).
//! 2. **Before a block compiles** ([`compile_block`]): a block that
//!    references an image-kind head has its members rewritten
//!    (`translate`) into an overlay, with the source occurrences as decompile
//!    records (`_ix.inline`, compiled in meta mode by `compile_expr`); an
//!    image block (every member an image-kind head) compiles to the images
//!    under the Lean names, each of Lean's kind, with `Named.original` from
//!    Lean's form.
//!
//! Every record is published into the shared state when it is written and
//! logged for the failed-block rollback (`block_txn`). A record is read only
//! by a block that depends, in the scheduler's graph, on every block that
//! writes it: an image-kind head is a Lean auxiliary of its block, whose
//! recursor mentions every member, so the head's own block and every block
//! that mentions the head wait for every component of the Lean block. The
//! records a block reads are therefore complete and the same in every
//! schedule.

use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::address::Address;
use ix_common::env::{
  ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, Env as LeanEnv,
  Expr, ExprData, Level, Name, RecursorVal, ReducibilityHints, TheoremVal,
};
use ixon::CompileError;
use ixon::env::{AuxLayout, Named};

use crate::compile::aux_gen::{
  PatchedConstant, source_family::filter_heads,
  source_identity::permits_optimization,
};
use crate::compile::{
  BlockCache, CompileState, IX_LOG_AUX_NAMES, KernelCtx, block_txn,
  compile_const, compile_const_no_aux, compile_name, compile_single_def_parts,
  name_claim_conflict,
};
use crate::graph::NameSet;
use crate::mutual::Def;

use super::Journal;
use super::clique::hook::{CliquePrep, HookEnv, prepare_cliques};
use super::clique::plan::CliqueOutcome;
use super::clique::table::encoding_owner;
use super::names::{has_reserved, image_kinds, ix_aux_name, mk_str};
use super::opt::{Occ, OptBlock, OptEnv, engine, opt_block_of};
use super::sidecar::{hash_map_of, rename_named};
use super::spec::NestedCanon;
use super::translate::{RwState, image_decl_with, rewrite_block};
use super::view::{
  BlockView, ComponentRecord, Expansion, ViewInput, build_view,
};

fn invalid(reason: String) -> CompileError {
  CompileError::InvalidMutualBlock { reason }
}

/// The out-of-component marker of an aux layout.
const PERM_OUT: usize = crate::compile::aux_gen::nested::PERM_OUT_OF_SCC;

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

/// The changed-block predicate (Def 3.1 under the compiler's rules): fewer
/// classes than Lean's `all`, a class representative out of `all` order, or
/// a nested auxiliary moved or evaporated. Lean's `isChanged`.
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

/// The refusal of a changed block's aux tail in a state no driver prepared
/// (a hand-built one): its Ix auxiliaries would stay under Lean's names with
/// no caller rewritten for them.
pub fn unprepared_changed_block(name: &Name) -> CompileError {
  invalid(format!(
    "changed block '{}' compiled with its aux tail outside a \
     driver-prepared environment",
    name.pretty()
  ))
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

/// The source-authenticated image-kind heads of a Lean block
/// (`sourceImageHeads`), the same for both hooks.
fn source_image_heads(lean_env: &Arc<LeanEnv>, all: &[Name]) -> Vec<Name> {
  let const_of = |n: &Name| lean_env.get(n).map(|e| e.cloned());
  filter_heads(
    lean_env,
    all,
    image_kinds(&const_of, all)
      .into_iter()
      .filter(|name| permits_optimization(lean_env, name))
      .collect(),
  )
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
    if !seen.insert(n.clone()) || has_reserved(n) || !sel(n) {
      continue;
    }
    if let Some(d) = ix_aux_name(members, rep0, perm, n) {
      display.push((n.clone(), d));
    }
  }
  let full = hash_map_of(&display);
  let moved: FxHashSet<Name> = display.iter().map(|(n, _)| n.clone()).collect();
  for (n, d) in &display {
    compile_name(d, stt)?;
    let named = stt.env.named.get(n).map(|r| r.clone());
    let addr = stt.aux_name_to_addr.get(n).map(|r| r.clone());
    stt.env.named.remove(n);
    stt.aux_name_to_addr.remove(n);
    stt.aux_gen_extra_names.remove(n);
    if *IX_LOG_AUX_NAMES {
      eprintln!(
        "[aux-names] p3-move scc={} {} -> {}",
        rep0.pretty(),
        n.pretty(),
        d.pretty()
      );
    }
    if let Some(named) = named {
      stt.register_named(d.clone(), rename_named(&full, &named));
    }
    if let Some(a) = addr {
      match stt.aux_name_to_addr.entry(d.clone()) {
        dashmap::mapref::entry::Entry::Occupied(e) => {
          if *e.get() != a {
            return Err(name_claim_conflict(d, e.get(), &a));
          }
        },
        dashmap::mapref::entry::Entry::Vacant(e) => {
          e.insert(a);
          block_txn::log_aux(d);
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

/// Insert-once into a Pass 3 record: an equal entry is kept, a different one
/// is the conflict `Pass 3: conflicting {what} '{k}'`. A new entry is logged
/// for the failed-block rollback (`log`); returns whether it is new.
fn insert_once<V: PartialEq + Clone>(
  m: &dashmap::DashMap<Name, V>,
  k: &Name,
  v: V,
  what: &str,
  log: fn(&Name),
) -> Result<bool, CompileError> {
  match m.entry(k.clone()) {
    dashmap::mapref::entry::Entry::Occupied(e) => {
      if *e.get() != v {
        return Err(invalid(format!(
          "Pass 3: conflicting {what} '{}'",
          k.pretty()
        )));
      }
      Ok(false)
    },
    dashmap::mapref::entry::Entry::Vacant(e) => {
      e.insert(v);
      log(k);
      Ok(true)
    },
  }
}

/// Record the canonical recursors, each compared whole with an entry another
/// block recorded (Lean's `checkBlockClaims`).
fn insert_recs(
  stt: &CompileState,
  scc: &Name,
  recs: &[(Name, RecursorVal)],
) -> Result<(), CompileError> {
  for (n, rv) in recs {
    let new = insert_once(
      &stt.p3.canon_recs,
      n,
      rv.clone(),
      "canonical recursor",
      block_txn::log_p3_canon_rec,
    )?;
    if *IX_LOG_AUX_NAMES {
      eprintln!(
        "[aux-names] p3-rec scc={} {} new={new}",
        scc.pretty(),
        n.pretty()
      );
    }
  }
  Ok(())
}

/// Record the image-kind heads and the Lean block of a changed block.
fn insert_heads(
  stt: &CompileState,
  scc: &Name,
  heads: &[Name],
  all0: &Name,
  all: &[Name],
) -> Result<(), CompileError> {
  for h in heads {
    let new = insert_once(
      &stt.p3.heads,
      h,
      all0.clone(),
      "image-kind head",
      block_txn::log_p3_head,
    )?;
    if *IX_LOG_AUX_NAMES {
      eprintln!(
        "[aux-names] p3-head scc={} {} key={} new={new}",
        scc.pretty(),
        h.pretty(),
        all0.pretty()
      );
    }
  }
  insert_once(
    &stt.p3.blocks,
    all0,
    all.to_vec(),
    "Lean block",
    block_txn::log_p3_block,
  )?;
  Ok(())
}

/// Record the component of each member; a new entry is logged for the
/// failed-block rollback.
fn record_components<'a>(
  stt: &CompileState,
  members: impl Iterator<Item = &'a Name>,
  record: &ComponentRecord,
) {
  for m in members {
    if stt.p3.components.insert(m.clone(), record.clone()).is_none() {
      block_txn::log_p3_component(m);
    }
  }
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
  // the heads are decided before any name moves (the family checks read
  // Lean's environment only)
  let heads = source_image_heads(lean_env, original_all);
  if *IX_LOG_AUX_NAMES {
    eprintln!(
      "[aux-names] p3-edit scc={} all0={} claimed={} heads={} recs={}",
      rep0.pretty(),
      all0.pretty(),
      journal.claimed.len(),
      heads.len(),
      journal.recs.len()
    );
  }
  // every Lean name moves off the Ix auxiliaries: the image kinds denote
  // their stored images (compiled when their own block comes up,
  // `compile_image_block`), the rest are Lean's own blocks
  let moved =
    move_to_display(stt, original_all, &rep0, &perm, &journal, &|_| true)?;
  insert_heads(stt, &rep0, &heads, &all0, original_all)?;
  insert_recs(stt, &rep0, &journal.recs)?;
  let nested = layout.map(|l| NestedCanon {
    perm: perm.clone(),
    num_canon: journal.n_canonical_aux,
    evaporated: l.evaporated.clone(),
  });
  let record = ComponentRecord { classes: planc.clone(), nested };
  record_components(stt, planc.iter().flatten(), &record);
  Ok(journal.pending.into_iter().filter(|n| !moved.contains(n)).collect())
}

/// Hook 1 for an unchanged block whose Lean `IndPredBelow` family is stored
/// permuted (`editPermutedBelowFamily`): the family is treated as a changed
/// block whose members are Lean's `below` inductives. Returns the names to
/// release to the scheduler.
pub fn edit_permuted_below_family(
  stt: &CompileState,
  lean_env: &Arc<LeanEnv>,
  original_all: &[Name],
  journal: Journal,
) -> Result<Vec<Name>, CompileError> {
  // no Prop `below` family was built: nothing to edit (checked first, so an
  // unchanged block reads nothing more of the input)
  if journal.below_recs.is_empty() {
    return Ok(journal.pending);
  }
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
    let Ok(idx) = usize::try_from(p.idx) else {
      return Ok(journal.pending);
    };
    pos.push(idx);
  }
  if pos.iter().enumerate().all(|(i, p)| i == *p) {
    return Ok(journal.pending);
  }
  // a permutation only (a collapse inside the family is left as it is)
  let distinct: FxHashSet<usize> = pos.iter().copied().collect();
  if distinct.len() != pos.len() {
    return Ok(journal.pending);
  }
  // the family's first member in canonical (stored) order
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
  // the Ix auxiliaries of the family (not its inductives or constructors)
  let sel = |n: &Name| {
    !below_all.contains(n)
      && !ctors.contains(n)
      && below_all.iter().any(|b| super::names::strip_prefix(b, n).is_some())
  };
  let heads = source_image_heads(lean_env, &below_all);
  if *IX_LOG_AUX_NAMES {
    eprintln!(
      "[aux-names] p3-edit-below scc={} all0={} heads={} recs={}",
      rep0.pretty(),
      all0.pretty(),
      heads.len(),
      journal.below_recs.len()
    );
  }
  let moved = move_to_display(stt, &below_all, &rep0, &[], &journal, &sel)?;
  insert_recs(stt, &rep0, &journal.below_recs)?;
  insert_heads(stt, &rep0, &heads, &all0, &below_all)?;
  // the view reads the family's canonical classes: its stored order
  let mut order: Vec<(usize, Name)> =
    pos.iter().copied().zip(below_all.iter().cloned()).collect();
  order.sort_by_key(|(p, _)| *p);
  let classes: Vec<Vec<Name>> =
    order.into_iter().map(|(_, n)| vec![n]).collect();
  let record = ComponentRecord { classes, nested: None };
  record_components(stt, below_all.iter(), &record);
  Ok(journal.pending.into_iter().filter(|n| !moved.contains(n)).collect())
}

/// Canonical recursors of a set of aux patches (for the journal).
pub fn patch_recs(
  patches: &FxHashMap<Name, PatchedConstant>,
) -> Vec<(Name, RecursorVal)> {
  patches
    .iter()
    .filter_map(|(n, p)| match p {
      PatchedConstant::Rec(r) => Some((n.clone(), r.clone())),
      _ => None,
    })
    .collect()
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

/// The heads a constant mentions (`headsIn`): a walk over distinct nodes.
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
) -> Result<FxHashMap<Name, Arc<BlockView>>, String> {
  let mut views: FxHashMap<Name, Arc<BlockView>> = FxHashMap::default();
  for h in heads {
    let Some(key) = ctx.stt.p3.heads.get(&h).map(|r| r.clone()) else {
      continue;
    };
    if views.contains_key(&key) {
      continue;
    }
    if let Some(view) = ctx.stt.p3.views.get(&key) {
      views.insert(key, view.clone());
      continue;
    }
    let all = ctx
      .stt
      .p3
      .blocks
      .get(&key)
      .map_or_else(|| vec![key.clone()], |r| r.clone());
    // Test before building: observing later completion must not make an
    // earlier partial view eligible for the shared table.
    let memoable = all.iter().all(|n| ctx.stt.resolve_addr(n).is_some());
    let built = Arc::new(ctx.with_input(|inp| build_view(inp, &all))?);
    let view = if memoable {
      ctx.stt.p3.views.entry(key.clone()).or_insert(built).clone()
    } else {
      built
    };
    views.insert(key, view);
  }
  Ok(views)
}

/// A local view may use the cross-block tables only when it is the same
/// stable view admitted by `views_of`. A view built before compilation
/// finished is never promoted merely because time has passed.
fn stable_view(ctx: &Ctx<'_>, key: &Name, view: &Arc<BlockView>) -> bool {
  ctx.stt.p3.views.get(key).is_some_and(|saved| Arc::ptr_eq(&saved, view))
}

/// A recursor image is determined by its stable view and the immutable input.
/// Other auxiliary expansions keep their per-rewrite cache and context.
fn image_expansion(
  ctx: &Ctx<'_>,
  key: &Name,
  view: &Arc<BlockView>,
  name: &Name,
) -> Result<(Expansion, Expr), String> {
  let memoable = stable_view(ctx, key, view)
    && ctx
      .lean_env
      .get(name)
      .is_some_and(|c| matches!(&*c, ConstantInfo::RecInfo(_)));
  if memoable && let Some(image) = ctx.stt.p3.image_exps.get(name) {
    return Ok(image.clone());
  }
  let image = ctx.with_input(|inp| view.expansion(inp, name))?;
  if memoable {
    Ok(ctx.stt.p3.image_exps.entry(name.clone()).or_insert(image).clone())
  } else {
    Ok(image)
  }
}

/// Every view a rewrite has read so far is a stable one (`stable_view`).
fn all_stable(ctx: &Ctx<'_>, views: &FxHashMap<Name, Arc<BlockView>>) -> bool {
  views.iter().all(|(key, view)| stable_view(ctx, key, view))
}

/// The expansion lookup over the views (`expansionLookup`), building a view
/// on demand for a head of a block not yet viewed.
fn expansion_lookup(
  ctx: &Ctx<'_>,
  views: &mut FxHashMap<Name, Arc<BlockView>>,
  n: &Name,
) -> Result<Option<Expansion>, String> {
  let Some(key) = ctx.stt.p3.heads.get(n).map(|r| r.clone()) else {
    return Ok(None);
  };
  // the image memo, while this rewrite has read stable views only: a
  // definitional head's entry was rewritten from stable views, which this
  // rewrite would read too
  if all_stable(ctx, views)
    && let Some(image) = ctx.stt.p3.image_exps.get(n)
  {
    return Ok(Some(image.0.clone()));
  }
  if !views.contains_key(&key) {
    let more = views_of(ctx, std::iter::once(n.clone()))?;
    views.extend(more);
  }
  let v = views.get(&key).ok_or("Pass 3: view missing")?;
  let (x, _) = image_expansion(ctx, &key, v, n)?;
  Ok(Some(x))
}

/// The expansion lookup of a rewrite with the definitional passes (Lean
/// `passExpansionLookup`): a recursor's image from the memo (built, never
/// rewritten, the same under every configuration), any other head's
/// expansion from its view, rewritten here with the passes. The memo's
/// definitional entries were rewritten with the default configuration (the
/// faithful form the image constants keep), so they are not read.
fn pass_expansion_lookup(
  ctx: &Ctx<'_>,
  views: &mut FxHashMap<Name, Arc<BlockView>>,
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
  let (x, _) = image_expansion(ctx, &key, v, n)?;
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

/// What `prepare_block` gives a block: the rewritten members and the source
/// occurrences of the decompile records, placeholder `i` for entry `i`.
struct Prepared {
  overlay: FxHashMap<Name, ConstantInfo>,
  sources: Vec<Expr>,
}

/// The overlay and decompile sources of a block (`prepareBlock`); `None`
/// when the block references no head.
///
/// The early exits (no head in the compile; none among the block's
/// references; none among the members' constants, found by the iterative
/// `heads_in`) run on the calling thread: only the rewrite, which recurses
/// on the terms, runs on a thread with a large stack ([`with_big_stack`]),
/// so a block that references no head spawns no thread.
///
/// The members are read from the clique step's overlay first (`clique`, the
/// transported members and carried lemmas; Lean reads `cenv.env`, which
/// carries them).
fn prepare_block(
  ctx: &Ctx<'_>,
  all: &NameSet,
  refs: Option<&FxHashSet<Name>>,
  clique: &FxHashMap<Name, ConstantInfo>,
) -> Result<Option<Prepared>, String> {
  if ctx.stt.p3.heads.is_empty() {
    return Ok(None);
  }
  // the block's references first (Lean's `p3BlockRefs` prefilter), before
  // walking every member's DAG
  if let Some(refs) = refs
    && !refs.iter().any(|name| ctx.stt.p3.heads.contains_key(name))
  {
    return Ok(None);
  }
  let mut members: Vec<(Name, ConstantInfo)> = Vec::new();
  let mut used: Vec<Name> = Vec::new();
  // a fixed member order: the placeholder indices follow it (they are not
  // stored; each constant numbers its records in first-occurrence order)
  let mut sorted: Vec<&Name> = all.iter().collect();
  sorted.sort_by_cached_key(|n| n.pretty());
  for n in sorted {
    let ci = clique
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
  with_big_stack(|| prepare_block_rewrite(ctx, &members, used)).map(Some)
}

/// The rewrite of [`prepare_block`], for a block that references a head.
fn prepare_block_rewrite(
  ctx: &Ctx<'_>,
  members: &[(Name, ConstantInfo)],
  used: Vec<Name>,
) -> Result<Prepared, String> {
  // the views of the referenced changed blocks (the lookup adds others on
  // demand)
  let mut views = views_of(ctx, used.into_iter())?;
  // the definitional passes over the blocks of these views (Lean
  // `passConfig`, `optBlocks` over `viewsOf`'s views): heads of a block
  // viewed later in the rewrite keep their baseline
  let opt_blocks: FxHashMap<Name, OptBlock> = ctx.with_input(|inp| {
    views.iter().map(|(k, v)| (k.clone(), opt_block_of(v, inp))).collect()
  });
  let resolves = |n: &Name| ctx.stt.resolve_addr(n).is_some();
  let block_of = |h: &Name| {
    let key = ctx.stt.p3.heads.get(h).map(|r| r.clone())?;
    opt_blocks.get(&key)
  };
  let env =
    OptEnv { ienv: ctx.lean_env, resolves: &resolves, block_of: &block_of };
  let opt = |n: &Name, us: &[Level], args: &[Expr]| {
    if !permits_optimization(ctx.lean_env, n) {
      return None;
    }
    engine(&env, &Occ { head: n, us, args }).map(|(_, e)| e)
  };
  let rw = {
    let mut lookup = |n: &Name| pass_expansion_lookup(ctx, &mut views, n);
    rewrite_block(&mut lookup, members, Some(&opt))?
  };
  Ok(Prepared {
    overlay: rw.overlay.into_iter().collect(),
    sources: rw.sources,
  })
}

/// `cliqueInert`: the clique step has nothing to do with the block `all`:
/// the input has no clique, or no member of the block is in the clique table
/// and none of the block's references (`refs`, the condensation's) is one of
/// Lean's encoding constants of a clique ([`encoding_owner`]). The hook would
/// then give the empty preparation; the test decides it on the calling
/// thread, without the hook's large-stack thread.
fn clique_inert(
  stt: &CompileState,
  all: &NameSet,
  refs: Option<&FxHashSet<Name>>,
) -> bool {
  stt.p3.cliques.is_empty()
    || (!all.iter().any(|n| stt.p3.cliques.contains_key(n))
      && !refs.is_some_and(|rs| {
        rs.iter().any(|r| encoding_owner(&stt.p3.clique_roots, r).is_some())
      }))
}

/// The plan table's entries for the cliques the block may plan (its members'
/// and the cliques whose encoding constants it references): the hook's
/// `plans` (Lean `CompileEnv.p3CliquePlans`, the table at the block's
/// start). An entry another block of the wave adds meanwhile is the same
/// plan (the table is a memo, `cliquePlanFor`), so the bytes do not depend
/// on which entries the snapshot holds.
fn plan_snapshot(
  stt: &CompileState,
  all: &NameSet,
  refs: Option<&FxHashSet<Name>>,
) -> FxHashMap<Name, CliqueOutcome> {
  let mut keys: Vec<&Name> = Vec::new();
  for n in all {
    if let Some(k) = stt.p3.cliques.get(n).and_then(|(cl, _)| cl.first()) {
      keys.push(k);
    }
  }
  for r in refs.into_iter().flatten() {
    if let Some(k) =
      encoding_owner(&stt.p3.clique_roots, r).and_then(|cl| cl.first())
    {
      keys.push(k);
    }
  }
  let mut plans = FxHashMap::default();
  for k in keys {
    if !plans.contains_key(k)
      && let Some(o) = stt.p3.clique_plans.get(k)
    {
      plans.insert(k.clone(), o.clone());
    }
  }
  plans
}

/// The clique step's preparation (`cliqueStep`'s `prepareCliques`, well-
/// founded cliques only: `HookEnv::wf_only`), on a thread with a large stack
/// (the planning recurses on the terms). A caller that unfolds a transported
/// clique's encoding is the block's error.
fn clique_step(
  ctx: &Ctx<'_>,
  all: &NameSet,
  refs: Option<&FxHashSet<Name>>,
) -> Result<CliquePrep, CompileError> {
  let plans = plan_snapshot(ctx.stt, all, refs);
  let empty = FxHashSet::default();
  let refs = refs.unwrap_or(&empty);
  with_big_stack(|| {
    let addr = |n: &Name| ctx.stt.resolve_addr(n);
    let h = HookEnv {
      env: ctx.lean_env,
      addr: &addr,
      table: &ctx.stt.p3.cliques,
      roots: &ctx.stt.p3.clique_roots,
      plans: &plans,
      check_plans: false,
      wf_only: true,
    };
    prepare_cliques(&h, all, refs)
  })
  .map_err(invalid)
}

/// The call-site rewrite of a canonical constant `c` of a clique
/// (`rewriteCliqueCanon`): the rewrite a block's members get
/// ([`prepare_block_rewrite`]: the views of the changed blocks it
/// references, the definitional passes). The rewritten constant (itself when
/// nothing changed) and its decompile sources (placeholder `i` for entry
/// `i`).
fn clique_canon_rewrite(
  ctx: &Ctx<'_>,
  c: &Name,
  ci: &ConstantInfo,
) -> Result<(ConstantInfo, Vec<Expr>), String> {
  if ctx.stt.p3.heads.is_empty() {
    return Ok((ci.clone(), Vec::new()));
  }
  let used: Vec<Name> = heads_in(ctx.stt, ci).into_iter().collect();
  if used.is_empty() {
    return Ok((ci.clone(), Vec::new()));
  }
  let members = [(c.clone(), ci.clone())];
  let p = with_big_stack(|| prepare_block_rewrite(ctx, &members, used))?;
  let ci2 = p.overlay.get(c).cloned().unwrap_or_else(|| ci.clone());
  Ok((ci2, p.sources))
}

/// Compile the canonical constants of a block's transported cliques
/// (`compileCliqueCanon`), in the hook's order (each after the canonical
/// constants it references): each from its own rewrite as a lone constant,
/// published under its reserved name in the auxiliary table
/// ([`publish_image`]'s claim rule: insert-once, journaled for the block's
/// rollback), where the block's members and the later canonical constants
/// resolve it.
fn compile_clique_canon(
  ctx: &Ctx<'_>,
  canon: &[(Name, ConstantInfo)],
) -> Result<(), CompileError> {
  let stt = ctx.stt;
  for (c, ci) in canon {
    let err = |e: CompileError| {
      invalid(format!("Pass 3 cliques: canonical constant {}: {e}", c.pretty()))
    };
    let (ci2, sources) =
      clique_canon_rewrite(ctx, c, ci).map_err(|e| err(invalid(e)))?;
    let def = match &ci2 {
      ConstantInfo::DefnInfo(v) => Def::mk_defn(v),
      ConstantInfo::ThmInfo(v) => Def::mk_theo(v),
      _ => {
        return Err(err(invalid("not a definition or theorem".into())));
      },
    };
    let mut cache = BlockCache {
      p3_sources: sources.into_iter().enumerate().collect(),
      ..Default::default()
    };
    let (addr, meta, bytes, constant) =
      compile_single_def_parts(c, &def, &mut cache, stt).map_err(err)?;
    stt.store_const_bytes(addr.clone(), bytes, constant)?;
    publish_image(stt, c, Named::new(addr, meta))?;
  }
  Ok(())
}

/// Every member of the block is an image-kind head (`isImageBlock`).
fn is_image_block(stt: &CompileState, all: &NameSet) -> bool {
  !all.is_empty() && all.iter().all(|n| stt.p3.heads.contains_key(n))
}

/// The image constant of head `a` with Lean's kind: the image of a Lean
/// theorem is a theorem, of anything else a definition (`imageInfo`).
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

/// Publish an image constant under its Lean name in the auxiliary table
/// (insert-once; a name compiled or claimed at another address is the
/// claim conflict). The name is not an aux-gen name: Lean's form is compiled
/// as the original, and the promotion publishes the name at block commit.
/// A clique's canonical constant is published by the same rule, under its
/// reserved name ([`compile_clique_canon`]).
fn publish_image(
  stt: &CompileState,
  a: &Name,
  named: Named,
) -> Result<(), CompileError> {
  if let Some(existing) = stt.name_to_addr.get(a)
    && *existing.value() != named.addr
  {
    return Err(name_claim_conflict(a, existing.value(), &named.addr));
  }
  let owns = match stt.aux_name_to_addr.entry(a.clone()) {
    dashmap::mapref::entry::Entry::Occupied(e) => {
      if *e.get() != named.addr {
        return Err(name_claim_conflict(a, e.get(), &named.addr));
      }
      block_txn::holds_aux_claim(a)
    },
    dashmap::mapref::entry::Entry::Vacant(e) => {
      e.insert(named.addr.clone());
      block_txn::log_aux(a);
      true
    },
  };
  if owns {
    stt.register_named(a.clone(), named);
  }
  Ok(())
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
  pending.sort_by_cached_key(|n| n.pretty());
  let decls: Vec<(Name, Def)> =
    with_big_stack(|| -> Result<Vec<(Name, Def)>, String> {
      let mut views = views_of(ctx, pending.iter().cloned())?;
      let mut st = RwState::default();
      let mut out = Vec::new();
      for a in &pending {
        let key = stt.p3.heads.get(a).map(|r| r.clone()).ok_or_else(|| {
          format!("Pass 3: {} is not an image-kind head", a.pretty())
        })?;
        let (x, ty) = {
          let v = views.get(&key).ok_or("Pass 3: view missing")?;
          image_expansion(ctx, &key, v, a)?
        };
        let mut lookup = |n: &Name| expansion_lookup(ctx, &mut views, n);
        let (value, typ) = image_decl_with(&mut st, &mut lookup, a, &x, &ty)?;
        // a definitional head's rewritten expansion enters the image memo when
        // every view the block's rewrite read is stable (Lean `readsMemoable`):
        // a later block's rewrite reads it instead of rewriting Lean's value
        if x.needs_rewrite && all_stable(ctx, &views) {
          let rewritten = Expansion {
            value: value.clone(),
            needs_rewrite: false,
            ..x.clone()
          };
          stt.p3.image_exps.entry(a.clone()).or_insert((rewritten, ty.clone()));
        }
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
      match compile_single_def_parts(&a, &d, &mut cache, stt) {
        Ok((addr, meta, bytes, constant)) => {
          stt.store_const_bytes(addr.clone(), bytes, constant)?;
          publish_image(stt, &a, Named::new(addr, meta))?;
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
    stt.record_hint(&a, Some(h));
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

/// Compile one scheduled block under Pass 3: an image block to its images,
/// any other block after the clique step (Lean `cliqueStep`: the transported
/// members of a changed clique and the canonical constants they reach) and
/// the call-site rewrite of its members (`refs`, the block's references,
/// prefilter both).
pub fn compile_block(
  lo: &Name,
  all: &NameSet,
  refs: Option<&FxHashSet<Name>>,
  lean_env: &Arc<LeanEnv>,
  cache: &mut BlockCache,
  stt: &CompileState,
  kctx: &mut KernelCtx,
) -> Result<Address, CompileError> {
  let ctx = Ctx { lean_env, stt };
  if is_image_block(stt, all) {
    return compile_image_block(&ctx, lo, all, kctx);
  }
  // the clique step: identity on a block outside every clique (decided on
  // this thread); otherwise the hook's preparation, then the canonical
  // constants, before the members' rewrite reads the transported values
  let prep = if clique_inert(stt, all, refs) {
    CliquePrep::default()
  } else {
    clique_step(&ctx, all, refs)?
  };
  if !prep.overlay.is_empty() {
    compile_clique_canon(&ctx, &prep.canon)?;
  }
  let clique: FxHashMap<Name, ConstantInfo> =
    prep.overlay.iter().cloned().collect();
  let prepared = prepare_block(&ctx, all, refs, &clique).map_err(invalid)?;
  if !clique.is_empty() {
    cache.p3_sources = prep
      .sources
      .iter()
      .map(|(i, e)| {
        usize::try_from(*i).map(|i| (i, e.clone())).map_err(|err| {
          invalid(format!("Pass 3 cliques: record index {i}: {err}"))
        })
      })
      .collect::<Result<_, _>>()?;
    cache.p3_overlay = clique;
  }
  if let Some(p) = prepared {
    cache.p3_overlay.extend(p.overlay);
    cache.p3_sources.extend(p.sources.into_iter().enumerate());
  }
  let res = compile_const(lo, all, lean_env, cache, stt, kctx);
  // the plans the block computed join the plan table when the block
  // compiles (Lean merges a block's state only then); the first plan of a
  // clique stays
  if res.is_ok() {
    for (k, o) in prep.fresh {
      stt.p3.clique_plans.entry(k).or_insert(o);
    }
  }
  res
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::compile::pass3::expr::dotted;
  use ix_common::env::Level;

  fn sort(n: u32) -> Expr {
    let mut l = Level::zero();
    for _ in 0..n {
      l = Level::succ(l);
    }
    Expr::sort(l)
  }

  /// A one-motive recursor `name : Sort 1` of `A` with no rules.
  fn rec_val(name: &Name) -> RecursorVal {
    use bignat::Nat;
    RecursorVal {
      cnst: ConstantVal {
        name: name.clone(),
        level_params: vec![],
        typ: sort(1),
      },
      all: vec![dotted("A")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(0u64),
      rules: vec![],
      k: false,
      is_unsafe: false,
    }
  }

  fn layout(perm: Vec<usize>, evaporated: Vec<bool>) -> AuxLayout {
    let n = perm.len();
    AuxLayout { perm, source_ctor_counts: vec![1; n], evaporated }
  }

  fn names(ss: &[&str]) -> Vec<Name> {
    ss.iter().map(|s| dotted(s)).collect()
  }

  #[test]
  fn changed_blocks_are_split_collapsed_reordered_or_moved() {
    let all = names(&["A", "B"]);
    // Lean's order, one class each, no nested auxiliary: unchanged
    let same = vec![names(&["A"]), names(&["B"])];
    assert!(!is_changed(&same, &all, None));
    // a non-Lean member in the block does not count
    let extra = vec![names(&["A"]), names(&["B"]), names(&["C"])];
    assert!(!is_changed(&extra, &all, None));
    // collapsed, split off, reordered
    assert!(is_changed(&[names(&["A", "B"])], &all, None));
    assert!(is_changed(&[names(&["A"])], &all, None));
    assert!(is_changed(&[names(&["B"]), names(&["A"])], &all, None));
    // a non-inductive block is never changed
    assert!(!is_changed(&same, &[], None));
    // nested auxiliaries: identity, out of component, moved, evaporated
    let id = layout(vec![0, 1], vec![false, false]);
    assert!(!is_changed(&same, &all, Some(&id)));
    let out = layout(vec![PERM_OUT, 1], vec![false, false]);
    assert!(!is_changed(&same, &all, Some(&out)));
    let moved = layout(vec![1, 0], vec![false, false]);
    assert!(is_changed(&same, &all, Some(&moved)));
    let evap = layout(vec![PERM_OUT, 1], vec![true, false]);
    assert!(is_changed(&same, &all, Some(&evap)));
  }

  /// Lean's `checkBlockClaims` compares the whole recursor: a second
  /// canonical recursor of one name with the same type but other fields is
  /// a conflict, and the first one stays.
  #[test]
  fn conflicting_canonical_recursor_is_refused_by_value() {
    let stt = CompileState::new_empty();
    let n = dotted("A.rec");
    let scc = dotted("A");
    let rv = rec_val(&n);
    insert_recs(&stt, &scc, &[(n.clone(), rv.clone())]).unwrap();
    // valid neighbour: the identical recursor again
    insert_recs(&stt, &scc, &[(n.clone(), rv.clone())]).unwrap();
    let other = RecursorVal { k: true, ..rv.clone() };
    let err =
      insert_recs(&stt, &scc, &[(n.clone(), other)]).unwrap_err().to_string();
    assert!(
      err.contains("Pass 3: conflicting canonical recursor 'A.rec'"),
      "{err}"
    );
    assert_eq!(stt.p3.canon_recs.get(&n).map(|r| r.clone()), Some(rv));
  }

  /// Two components of one Lean block record the same heads with the same
  /// key; another key for a recorded head is a conflict.
  #[test]
  fn heads_are_recorded_once_per_lean_block() {
    let stt = CompileState::new_empty();
    let all = names(&["A", "B", "C"]);
    let heads = names(&["A.rec", "A.rec_1"]);
    let (a, b) = (dotted("A"), dotted("B"));
    insert_heads(&stt, &b, &heads, &a, &all).unwrap();
    // valid neighbour: another component of the block, the same records
    insert_heads(&stt, &a, &heads, &a, &all).unwrap();
    assert_eq!(stt.p3.heads.len(), 2);
    assert_eq!(
      stt.p3.heads.get(&dotted("A.rec_1")).map(|r| r.clone()),
      Some(a)
    );
    let err = insert_heads(&stt, &b, &heads, &b, &all).unwrap_err().to_string();
    assert!(
      err.contains("Pass 3: conflicting image-kind head 'A.rec'"),
      "{err}"
    );
    let err = insert_heads(&stt, &b, &[], &dotted("A"), &names(&["A"]))
      .unwrap_err()
      .to_string();
    assert!(err.contains("Pass 3: conflicting Lean block 'A'"), "{err}");
  }

  /// A failed block leaves no record behind (Lean merges a block's Pass 3
  /// state only when the block compiles), and the rollback keeps the
  /// entries another block entered first.
  #[test]
  fn failed_block_rollback_removes_its_records() {
    let stt = CompileState::new_empty();
    let (owner_rec, owner) = (dotted("B.rec"), dotted("B"));
    let record =
      ComponentRecord { classes: vec![vec![owner.clone()]], nested: None };
    insert_recs(&stt, &owner, &[(owner_rec.clone(), rec_val(&owner_rec))])
      .unwrap();
    let owner_all = std::slice::from_ref(&owner);
    insert_heads(
      &stt,
      &owner,
      std::slice::from_ref(&owner_rec),
      &owner,
      owner_all,
    )
    .unwrap();
    record_components(&stt, [&owner].into_iter(), &record);
    let (n, a) = (dotted("A.rec"), dotted("A"));
    block_txn::start();
    insert_recs(
      &stt,
      &a,
      &[(n.clone(), rec_val(&n)), (owner_rec.clone(), rec_val(&owner_rec))],
    )
    .unwrap();
    let both = [n.clone(), owner_rec.clone()];
    insert_heads(&stt, &a, &both, &owner, owner_all).unwrap();
    insert_heads(&stt, &a, &[], &a, std::slice::from_ref(&a)).unwrap();
    let mine = ComponentRecord { classes: vec![vec![a.clone()]], nested: None };
    record_components(&stt, [&a].into_iter(), &mine);
    let txn = block_txn::take().unwrap();
    block_txn::rollback(&stt, &txn);
    assert!(!stt.p3.canon_recs.contains_key(&n));
    assert!(!stt.p3.heads.contains_key(&n));
    assert!(!stt.p3.blocks.contains_key(&a));
    assert!(!stt.p3.components.contains_key(&a));
    assert!(stt.p3.canon_recs.contains_key(&owner_rec));
    assert!(stt.p3.heads.contains_key(&owner_rec));
    assert!(stt.p3.blocks.contains_key(&owner));
    assert!(stt.p3.components.contains_key(&owner));
  }

  /// The side-car edit moves the tail's registrations to their display
  /// names, renames the kept entries' references, and releases only the
  /// names that kept a Lean name.
  #[test]
  fn edit_moves_the_tail_to_display_names() {
    use ixon::metadata::{ConstantMeta, ConstantMetaInfo};
    let stt = CompileState::new_empty();
    let lean_env = Arc::new(LeanEnv::default());
    let all = names(&["A", "B"]);
    let rec = dotted("B.rec");
    let addr = Address::hash(b"B.rec canonical");
    let muts = dotted("Ix.muts.B.rec");
    let muts_meta = ConstantMeta::new(ConstantMetaInfo::Muts {
      all: vec![vec![Address::from_blake3_hash(*rec.get_hash())]],
      aux_layout: None,
    });
    block_txn::start();
    stt.claim_aux_name(&rec, &addr).unwrap();
    stt.register_named(rec.clone(), Named::with_addr(addr.clone()));
    stt.register_named(muts.clone(), Named::new(addr.clone(), muts_meta));
    let journal = Journal {
      claimed: vec![rec.clone()],
      muts: vec![muts.clone()],
      pending: vec![rec.clone(), dotted("B.other")],
      ..Default::default()
    };
    // `B` alone: split off from Lean's `[A, B]`
    let release = edit_changed_block(
      &stt,
      &lean_env,
      &all,
      &[names(&["B"])],
      None,
      journal,
    )
    .unwrap();
    let txn = block_txn::take().unwrap();
    let display = dotted("B._ix.rec");
    assert_eq!(release, names(&["B.other"]));
    assert!(stt.resolve_addr(&rec).is_none());
    assert!(!stt.env.named.contains_key(&rec));
    assert!(!stt.aux_gen_extra_names.contains(&rec));
    assert_eq!(stt.resolve_addr(&display), Some(addr));
    assert!(stt.env.named.contains_key(&display));
    let renamed = stt.env.named.get(&muts).unwrap().meta().clone();
    let ConstantMetaInfo::Muts { all: muts_all, .. } = &renamed.info else {
      panic!("not a Muts entry");
    };
    assert_eq!(
      muts_all,
      &vec![vec![Address::from_blake3_hash(*display.get_hash())]]
    );
    assert!(stt.p3.blocks.contains_key(&dotted("A")));
    assert!(stt.p3.components.contains_key(&dotted("B")));
    // the display name is the block's: its rollback removes it
    assert!(txn.aux.contains(&display));
    block_txn::rollback(&stt, &txn);
    assert!(stt.resolve_addr(&display).is_none());
    assert!(!stt.p3.blocks.contains_key(&dotted("A")));
  }
}
