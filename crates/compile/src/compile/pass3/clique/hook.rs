//! The changed-clique hook's per-block computation, as pure functions over
//! data (a port of `Ix/Compile/Pass/Clique/Hook.lean`).
//!
//! Before a block compiles, the hook gives it:
//! * the callers' refusal ([`clique_callers`]): a block outside a
//!   transported clique's unit that references a member and one of Lean's
//!   encoding constants of the clique fails with a named error;
//! * for every member of a transported clique in the block, and every
//!   carried equation lemma, Lean's constant with the transported value,
//!   whose root carries the decompile record `_ix.inline` of Lean's value
//!   (the overlay entries and their sources);
//! * the canonical constants the transported members reach, as input
//!   constants, in an order where each one's canonical references come
//!   before it (or are already compiled);
//! * the plans computed for the block (for the plan table) and the number
//!   taken from the table.
//!
//! [`HookEnv`] is everything the hook reads of the compile state;
//! [`CliquePrep`] is everything it gives. The rest is the wiring's: the
//! block's compile environment (the overlay over the input, the `_ix.inline`
//! sources), the call-site rewrite and the compile of each canonical
//! constant in [`CliquePrep::canon`]'s order, and the merge of the fresh
//! plans into the plan table (the first entry of a key winning).
//!
//! **The memo caveat, for the wiring.** Nothing here reads or writes Pass
//! 3's rewrite state (`RwState`). The clique records (the `_ix.clique` record
//! and the causes, and later the rows and `_ix.src` copies) are a pure
//! function of the clique's plan, attached to the plan's own constants (its
//! members, its carried lemmas, its canonical constants), never to an image
//! expansion. The canonical constants' call-site rewrite must record nothing
//! (Rust's `rewrite_block` returns no records at all): the wiring
//! (`pass3::driver::compile_block`'s clique step) rewrites them as a block's
//! members are rewritten, with the definitional passes, so it reads the image
//! memo as any block does (a recursor's image only, `pass_expansion_lookup`)
//! and writes no clique data into it. If a wiring ever records
//! clique data in `RwState`, `readsMemoable` (the Rust driver's
//! `all_stable`) must be false for the expansions that recorded it;
//! [`CliquePlan::touches`] is the test of a constant against a plan.
//!
//! **Iteration order.** The block's names and its references are passed as
//! hash sets ([`NameSet`], as the compile loop holds them); everything here
//! that depends on an order reads them in pretty-name order
//! ([`sort_by_pretty`]), so the result does not depend on how the sets were
//! built. Pretty-name sorts are stable here and Lean's `qsort` is not: two
//! distinct names with one pretty form (a string component `"1"` and a
//! number component `1`) may come in another order than Lean's; Lean never
//! generates such a pair (as in [`super::table`]).
//!
//! Total and pure: no I/O, no compile state; the closure over the canonical
//! references is bounded by the number of canonical constants, the compile
//! order by its rounds ([`canon_rounds`]).

use std::hash::Hash;
use std::sync::Arc;

use bignat::Nat;
use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::env::{ConstantInfo, DataValue, Env, Expr, Name};

use super::basic::{
  Cause, ConstOf, R, arr_nat, arr_str, const_occurrences, list_str,
};
use super::order::AddrOf;
use super::plan::{CliqueOutcome, CliquePlan, Encoding};
use super::plan_clique::{
  canon_const, plan_clique, pop_unseen, push_stack, value_of, with_value,
};
use super::row::{row_prereqs, rows_of};
use super::table::{
  CLIQUE_RECORD_BASE, CliqueTable, EncodingRoots, encoding_owner,
  is_encoding_name,
};
use crate::compile::pass3::names::inline_key;
use crate::graph::NameSet;

// ---------------------------------------------------------------------------
// What the hook reads
// ---------------------------------------------------------------------------

/// The hook's read of the compile state (`HookEnv`).
pub struct HookEnv<'a> {
  /// The input constants.
  pub env: &'a Arc<Env>,
  /// The addresses compiled so far (the compiler's resolution map, then its
  /// auxiliary names).
  pub addr: AddrOf<'a>,
  /// The clique table: every member of an input clique, and every carried
  /// equation lemma, ↦ (Lean's `all`, the carried lemmas)
  /// ([`schedule_cliques`](super::table::schedule_cliques)).
  pub table: &'a CliqueTable,
  /// The encoding roots (`all₀._mutual`, `all₀.mutual`, `m._f`) ↦ the
  /// clique ([`schedule_cliques`](super::table::schedule_cliques)).
  pub roots: &'a EncodingRoots,
  /// The plan table: a memo of [`plan_clique`], keyed by the clique's first
  /// member, filled by the blocks that computed a plan (Lean's default: the
  /// empty table).
  pub plans: &'a FxHashMap<Name, CliqueOutcome>,
  /// Recompute every plan the table supplies and fail on a difference
  /// ([`PLAN_CHECK_PREFIX`]; Lean's default: `false`).
  pub check_plans: bool,
  /// Transport well-founded cliques only ([`CliqueOutcome::wf_only`]): the
  /// compile's setting (decision (ii), 2026-10-21: rows have a proof recipe
  /// for well-founded cliques only). Off for the library's own tests, which
  /// exercise all three transports (Lean's default: `false`).
  pub wf_only: bool,
}

/// `sortByPretty`: names in pretty-name order (see the module note on
/// ties).
pub fn sort_by_pretty(mut xs: Vec<Name>) -> Vec<Name> {
  xs.sort_by_cached_key(Name::pretty);
  xs
}

// ---------------------------------------------------------------------------
// The plan table
// ---------------------------------------------------------------------------

/// `memoLookup` (`Ix.Compile.Pass.Memo`): the value of `k`: the table's
/// entry, else `compute()`. With `check`, an entry is computed again and
/// must be `same` as the stored one; a difference is an error prefixed by
/// `what`.
pub fn memo_lookup<K: Eq + Hash, V: Clone>(
  table: &FxHashMap<K, V>,
  check: bool,
  what: &str,
  k: &K,
  same: &dyn Fn(&V, &V) -> bool,
  compute: &dyn Fn() -> R<V>,
) -> R<V> {
  match table.get(k) {
    Some(v) => {
      if check {
        let v2 = compute()?;
        if same(v, &v2) {
          Ok(v.clone())
        } else {
          Err(format!("{what}: the recomputed value differs from the table's"))
        }
      } else {
        Ok(v.clone())
      }
    },
    None => compute(),
  }
}

/// `Rows`: a transported plan's records after the fold ([`rows_of`]): the
/// `_ix.src` copies of its encoding set, then its members' rows.
pub type Rows = (Vec<ConstantInfo>, Vec<ConstantInfo>);

impl CliqueOutcome {
  /// `CliqueOutcome.wfOnlyRows`: the outcome under decision (ii)
  /// (2026-10-21), with the rows it checked: a transport stands only when
  /// its rows apply. A structural or `partial_fixpoint` clique keeps Lean's
  /// form (no row recipe); so does a well-founded clique whose rows do not
  /// apply ([`rows_of`] refuses) or whose rows' prerequisites
  /// ([`row_prereqs`]) are not all in the input (`const_of`), so that every
  /// transported clique gets its rows after the fold
  /// (`pass3::driver::emit_rows`). The kept form's outcome is
  /// `Baseline(enc, Shape, why)`, the outcome of a transport that kept
  /// Lean's form; the reason is for diagnostics, never a byte. Every other
  /// outcome is kept.
  ///
  /// The rows are `rows_of(const_of, plan)` for an outcome that stays
  /// transported, `None` otherwise: computed once, when the plan is made,
  /// and kept for the emission ([`CliquePrep::rows`], the driver's rows
  /// table `Pass3State::clique_rows`).
  pub fn wf_only_rows(
    self,
    const_of: ConstOf<'_>,
  ) -> (CliqueOutcome, Option<Rows>) {
    match self {
      CliqueOutcome::Transported(plan) => {
        let enc = plan.encoding;
        let keep =
          |why: String| (CliqueOutcome::Baseline(enc, Cause::Shape, why), None);
        if enc != Encoding::WellFounded {
          return keep(format!(
            "no row recipe for a {} clique: rows are for well-founded cliques only",
            enc.tag()
          ));
        }
        if let Some(p) =
          row_prereqs().into_iter().find(|p| const_of(p).is_none())
        {
          return keep(format!(
            "the rows' prerequisite {} is not in the input",
            p.pretty()
          ));
        }
        match rows_of(const_of, &plan) {
          Ok(rows) => (CliqueOutcome::Transported(plan), Some(rows)),
          Err(e) => keep(format!("the rows do not apply: {e}")),
        }
      },
      o => (o, None),
    }
  }

  /// `CliqueOutcome.wfOnly`: the outcome under decision (ii)
  /// ([`CliqueOutcome::wf_only_rows`] without the rows).
  pub fn wf_only(self, const_of: ConstOf<'_>) -> CliqueOutcome {
    self.wf_only_rows(const_of).0
  }
}

/// `planCheckPrefix`: the prefix of the plan-table check's error; a driver
/// turns a block failure with this prefix into a failed compile.
pub const PLAN_CHECK_PREFIX: &str = "Pass 3 plan cache check:";

/// `cliquePlanFor`: the plan of a clique for the current block, and whether
/// it came from the plan table ([`HookEnv::plans`]), through
/// [`memo_lookup`].
///
/// **Why a table is allowed.** [`plan_clique`] is a function of the clique
/// (`cl`), its carried lemmas (read from the clique's own unit by
/// [`schedule_cliques`](super::table::schedule_cliques)), the input
/// constants of its unit and its dependencies, and the addresses of those
/// dependencies. Every block that plans the clique (a member's block, a
/// carried lemma's block, a caller's block) is scheduled after all of the
/// members' references (the scheduling edges), so each computes the same
/// plan: the table is a memo of that function (with [`HookEnv::wf_only`]
/// applied), keyed by the clique's first member, filled by the first block that needs a plan and merged by the
/// driver like the other Pass 3 tables. Which block filled an entry, or
/// whether one did, changes no byte and no record. With
/// [`HookEnv::check_plans`], every plan the table supplies is recomputed,
/// and a difference (by [`CliqueOutcome::same`]) is [`memo_lookup`]'s error,
/// prefixed by [`PLAN_CHECK_PREFIX`] and the clique (`<prefix> the plan of
/// the clique #[…]: the recomputed value differs from the table's`). A
/// clique without a first member (never in the table) is planned directly.
///
/// A plan computed here (not taken from the table) comes with its rows when
/// it stays transported ([`CliqueOutcome::wf_only_rows`], which computes
/// them to decide), for the rows table ([`CliquePrep::rows`]); a plan from
/// the table comes without them (they are in the rows table, or the
/// emission computes them).
pub fn clique_plan_for(
  h: &HookEnv<'_>,
  cl: &[Name],
  carried: &[Name],
) -> R<(CliqueOutcome, bool, Option<Rows>)> {
  let compute = || {
    let o = plan_clique(h.env, h.addr, cl, carried);
    let const_of = |n: &Name| h.env.get(n).map(|e| e.cloned());
    if h.wf_only { o.wf_only_rows(&const_of) } else { (o, None) }
  };
  let Some(key) = cl.first() else {
    let (o, rows) = compute();
    return Ok((o, false, rows));
  };
  if !h.plans.contains_key(key) {
    let (o, rows) = compute();
    return Ok((o, false, rows));
  }
  let what = if h.check_plans {
    let names: Vec<String> = cl.iter().map(Name::pretty).collect();
    format!("{PLAN_CHECK_PREFIX} the plan of the clique {}", arr_str(&names))
  } else {
    PLAN_CHECK_PREFIX.to_string()
  };
  let o = memo_lookup(
    h.plans,
    h.check_plans,
    &what,
    key,
    &CliqueOutcome::same,
    &|| Ok(compute().0),
  )?;
  Ok((o, true, None))
}

// ---------------------------------------------------------------------------
// The callers
// ---------------------------------------------------------------------------

/// `callerRefusalPrefix`: the prefix of a caller's refusal
/// ([`clique_callers`]): the named error the driver records as the block's
/// failure, by which the changed-set record tells a refused caller from any
/// other failed block.
pub const CALLER_REFUSAL_PREFIX: &str = "Pass 3 cliques: caller refused";

/// What [`clique_callers`] gives: the refusal, or `None` when the block may
/// compile; the plans it computed, by clique key (for the plan table); the
/// number it took from the table.
pub type Callers = (Option<String>, Vec<(Name, CliqueOutcome)>, usize);

/// `cliqueCallers`: the callers' side of the block rule ("callers adapt").
/// A block outside a clique's unit (no member, no carried lemma, no encoding
/// constant of the clique) that references a member and one of Lean's
/// encoding constants of the clique may rely on the member unfolding to
/// Lean's encoding. When the clique is transported (its plan, a function of
/// the clique, its unit and its dependencies, all compiled before this
/// block: [`clique_plan_for`]), that encoding is no longer what the member
/// unfolds to: the block is refused with a named error
/// ([`CALLER_REFUSAL_PREFIX`]), recorded as a block failure by the driver.
/// The clique is never changed for a caller, and the caller is never
/// silently compiled against Lean's form.
///
/// Returns the refusal, or `None` when the block may compile, with the
/// plans it computed (for the plan table) and the number it took from the
/// table. Reads only the block (`all`, its references `refs`) and the
/// cliques it depends on.
///
/// Order: the references that are encoding constants of a clique
/// ([`encoding_owner`]) are read in pretty-name order, each clique once (at
/// its first such reference); the member named in the refusal is the
/// clique's member among `refs` first in pretty-name order, and the callers
/// are listed in pretty-name order.
pub fn clique_callers(
  h: &HookEnv<'_>,
  all: &NameSet,
  refs: &NameSet,
) -> R<Callers> {
  if h.roots.is_empty() {
    return Ok((None, Vec::new(), 0));
  }
  let mut owned: Vec<(&Name, &Vec<Name>)> = refs
    .iter()
    .filter_map(|r| encoding_owner(h.roots, r).map(|cl| (r, cl)))
    .collect();
  owned.sort_by_cached_key(|(r, _)| r.pretty());
  let mut seen: FxHashSet<Name> = FxHashSet::default();
  let mut fresh: Vec<(Name, CliqueOutcome)> = Vec::new();
  let mut reused = 0usize;
  for (r, cl) in owned {
    let Some(key) = cl.first() else { continue };
    if !seen.insert(key.clone()) {
      continue;
    }
    let carried: &[Name] = h.table.get(key).map_or(&[], |x| x.1.as_slice());
    // a block of the clique's own unit is not a caller
    if all
      .iter()
      .any(|n| cl.contains(n) || carried.contains(n) || is_encoding_name(cl, n))
    {
      continue;
    }
    let members: Vec<Name> =
      refs.iter().filter(|x| cl.contains(x)).cloned().collect();
    let Some(m) = sort_by_pretty(members).into_iter().next() else {
      continue;
    };
    // the members' blocks come before a caller's (it references a member)
    // and plan the clique first: a plan computed here is one whose members
    // did not compile, so there are no rows to keep
    let (outcome, hit, _) = clique_plan_for(h, cl, carried)?;
    if hit {
      reused += 1;
    } else {
      fresh.push((key.clone(), outcome.clone()));
    }
    if let CliqueOutcome::Transported(plan) = &outcome {
      let callers: Vec<String> =
        sort_by_pretty(all.iter().cloned().collect::<Vec<Name>>())
          .iter()
          .map(Name::pretty)
          .collect();
      let s = if callers.len() == 1 { "s" } else { "" };
      let clique: Vec<String> = cl.iter().map(Name::pretty).collect();
      let refusal = format!(
        "{CALLER_REFUSAL_PREFIX} (block rule, callers adapt): {} reference{s} \
         {} and Lean's encoding constant {} of the transported clique {} \
         (sigma {}); a caller may not unfold Lean's encoding of a transported \
         clique",
        list_str(&callers),
        m.pretty(),
        r.pretty(),
        arr_str(&clique),
        arr_nat(&plan.sigma)
      );
      return Ok((Some(refusal), fresh, reused));
    }
  }
  Ok((None, fresh, reused))
}

// ---------------------------------------------------------------------------
// The block's preparation
// ---------------------------------------------------------------------------

/// What the hook gives a block (`CliquePrep`). Empty
/// ([`CliquePrep::is_empty`]) when the block has nothing to do with a
/// changed clique.
#[derive(Clone, Debug, Default)]
pub struct CliquePrep {
  /// The transported members and carried lemmas of the block, in the
  /// block's pretty-name order: Lean's constant (Lean's name and type) with
  /// the transported value under the decompile record
  /// `[(inline_key, OfNat(i))]`, `i = CLIQUE_RECORD_BASE + k` for the `k`-th
  /// entry.
  pub overlay: Vec<(Name, ConstantInfo)>,
  /// The decompile sources of the records: `CLIQUE_RECORD_BASE + k` ↦
  /// Lean's value of the `k`-th overlay entry.
  pub sources: Vec<(u64, Expr)>,
  /// The canonical constants the block compiles ([`canon_const`]: the
  /// functionals carry the side-car record), each after the canonical
  /// constants it references, except those already compiled
  /// ([`HookEnv::addr`]).
  pub canon: Vec<(Name, ConstantInfo)>,
  /// The plans computed for this block, by clique key (for the plan table).
  pub fresh: Vec<(Name, CliqueOutcome)>,
  /// The rows of the transported plans the block's members computed, by
  /// clique key ([`CliqueOutcome::wf_only_rows`]; for the rows table).
  pub rows: Vec<(Name, Rows)>,
  /// The number of plans taken from the plan table.
  pub reused: usize,
}

impl CliquePrep {
  /// `CliquePrep.isEmpty`.
  pub fn is_empty(&self) -> bool {
    self.overlay.is_empty()
      && self.sources.is_empty()
      && self.canon.is_empty()
      && self.fresh.is_empty()
      && self.reused == 0
  }
}

impl CliquePlan {
  /// `CliquePlan.touches`: `n` is a constant the plan attaches records to or
  /// replaces: a member, a carried lemma (a transported constant besides the
  /// members), or a canonical constant.
  pub fn touches(&self, n: &Name) -> bool {
    self.all.contains(n)
      || self.members.contains_key(n)
      || self.canon.iter().any(|(d, _)| d.name == *n)
  }
}

/// The canonical references of a canonical constant's type and value that
/// satisfy `p`, the type's first.
pub fn refs_where(p: &dyn Fn(&Name) -> bool, ci: &ConstantInfo) -> Vec<Name> {
  let mut out = const_occurrences(p, ci.get_type());
  if let Some(v) = value_of(ci) {
    out.extend(const_occurrences(p, v));
  }
  out
}

/// `reachCanon`: the canonical constants reachable from `stack` through the
/// canonical references (`canon_names`) of their types and values, appended
/// to `wanted` (with its membership set `seen`), each once, in the
/// worklist's order. Every name on the stack is in `canon_names` and every
/// name appended is new, so with `fuel = canon_names.len()` no name is still
/// due at fuel `0` (every canonical name is then already wanted): the result
/// is the full closure.
pub fn reach_canon(
  canon: &FxHashMap<Name, ConstantInfo>,
  canon_names: &FxHashSet<Name>,
  fuel: usize,
  mut stack: Vec<Name>,
  wanted: &mut Vec<Name>,
  seen: &mut FxHashSet<Name>,
) {
  let mut fuel = fuel;
  while let Some(c) = pop_unseen(seen, &mut stack) {
    let Some(f) = fuel.checked_sub(1) else { return };
    fuel = f;
    let next = canon.get(&c).map_or_else(Vec::new, |cc| {
      refs_where(&|n: &Name| canon_names.contains(n), cc)
    });
    push_stack(&mut stack, next);
    wanted.push(c.clone());
    seen.insert(c);
  }
}

/// `canonRefs`: the canonical constants (other than `c`) that the canonical
/// constant `c` references in its type and value.
pub fn canon_refs(
  canon: &FxHashMap<Name, ConstantInfo>,
  c: &Name,
  ci: &ConstantInfo,
) -> Vec<Name> {
  refs_where(&|r: &Name| canon.contains_key(r) && r != c, ci)
}

/// `cyclicCanonError`: the error of canonical constants that never become
/// compilable.
pub fn cyclic_canon_error(pending: &[Name]) -> String {
  let names: Vec<String> = pending.iter().map(Name::pretty).collect();
  format!(
    "Pass 3 cliques: canonical constants with cyclic references: {}",
    arr_str(&names)
  )
}

/// `canonRounds`: the compile order of the pending canonical constants, in
/// rounds: each round goes through the pending constants in order and takes
/// every one whose canonical references are known (taken earlier, in this
/// round or a previous one, or already compiled: `addr`); the others wait
/// for the next round, in the same order. At most `fuel` rounds
/// (`pending.len() + 1` suffices for any acyclic set); a round that takes
/// nothing, or pending constants after the last round, are the cyclic
/// error.
pub fn canon_rounds(
  addr: AddrOf<'_>,
  canon: &FxHashMap<Name, ConstantInfo>,
  fuel: usize,
  mut pending: Vec<Name>,
  mut order: Vec<(Name, ConstantInfo)>,
  mut done: FxHashSet<Name>,
) -> R<Vec<(Name, ConstantInfo)>> {
  let mut fuel = fuel;
  loop {
    let Some(f) = fuel.checked_sub(1) else {
      return if pending.is_empty() {
        Ok(order)
      } else {
        Err(cyclic_canon_error(&pending))
      };
    };
    fuel = f;
    if pending.is_empty() {
      return Ok(order);
    }
    let mut rest: Vec<Name> = Vec::new();
    for c in &pending {
      let Some(ci) = canon.get(c) else {
        return Err(format!(
          "Pass 3 cliques: no canonical constant {}",
          c.pretty()
        ));
      };
      if canon_refs(canon, c, ci)
        .iter()
        .any(|r| !done.contains(r) && addr(r).is_none())
      {
        rest.push(c.clone());
      } else {
        order.push((c.clone(), ci.clone()));
        done.insert(c.clone());
      }
    }
    if rest.len() == pending.len() {
      return Err(cyclic_canon_error(&rest));
    }
    pending = rest;
  }
}

/// `prepareCliques`: before a block compiles: for every member of a changed
/// clique in the block, and every equation lemma carried with one, its
/// transported value in the overlay with Lean's value as the decompile
/// record, and the canonical constants it references, in compile order. A
/// block outside a transported clique's unit that unfolds its encoding is
/// refused ([`clique_callers`]; `refs` are the block's references). The
/// empty preparation when the clique table is empty; only the plan
/// statistics when no constant of the block is a transported member or
/// lemma. A clique's plan is taken from the plan table when an earlier block
/// computed it ([`clique_plan_for`]); the plans computed here are returned
/// for the table ([`CliquePrep::fresh`]).
///
/// The block's names in the table are read in pretty-name order. The
/// canonical constants a member reaches are its value's canonical
/// references, closed under the canonical references of their types and
/// values ([`reach_canon`]); those not yet compiled ([`HookEnv::addr`]) are
/// ordered by [`canon_rounds`] from pretty-name order.
pub fn prepare_cliques(
  h: &HookEnv<'_>,
  all: &NameSet,
  refs: &NameSet,
) -> R<CliquePrep> {
  if h.table.is_empty() {
    return Ok(CliquePrep::default());
  }
  let (refusal, fresh0, reused0) = clique_callers(h, all, refs)?;
  if let Some(refusal) = refusal {
    return Err(refusal);
  }
  let const_of = |n: &Name| h.env.get(n).map(|e| e.cloned());
  let mut overlay: Vec<(Name, ConstantInfo)> = Vec::new();
  let mut sources: Vec<(u64, Expr)> = Vec::new();
  let mut canon: FxHashMap<Name, ConstantInfo> = FxHashMap::default();
  let mut wanted: Vec<Name> = Vec::new();
  let mut wanted_set: FxHashSet<Name> = FxHashSet::default();
  let mut plans: FxHashMap<Name, CliqueOutcome> =
    fresh0.iter().cloned().collect();
  let mut fresh = fresh0;
  let mut reused = reused0;
  let mut rows: Vec<(Name, Rows)> = Vec::new();
  let names: Vec<Name> =
    all.iter().filter(|n| h.table.contains_key(*n)).cloned().collect();
  for n in sort_by_pretty(names) {
    let Some((cl, carried)) = h.table.get(&n) else { continue };
    let Some(key) = cl.first() else { continue };
    let outcome = match plans.get(key) {
      Some(o) => o.clone(),
      None => {
        let (o, hit, rows_of_plan) = clique_plan_for(h, cl, carried)?;
        if hit {
          reused += 1;
        } else {
          fresh.push((key.clone(), o.clone()));
        }
        if let Some(r) = rows_of_plan {
          rows.push((key.clone(), r));
        }
        o
      },
    };
    plans.insert(key.clone(), outcome.clone());
    let CliqueOutcome::Transported(plan) = outcome else { continue };
    let Some(md) = plan.members.get(&n) else { continue };
    let Some(ci) = const_of(&n) else { continue };
    let Some(lean_value) = value_of(&ci) else { continue };
    let idx = CLIQUE_RECORD_BASE + overlay.len() as u64;
    let value = Expr::mdata(
      vec![(inline_key(), DataValue::OfNat(Nat::from(idx)))],
      md.value.clone(),
    );
    sources.push((idx, lean_value.clone()));
    overlay.push((n.clone(), with_value(&ci, value)));
    // the canonical constants, and the ones this constant reaches
    let canon_names: FxHashSet<Name> =
      plan.canon.iter().map(|(d, _)| d.name.clone()).collect();
    for (d, src) in &plan.canon {
      if !canon.contains_key(&d.name) {
        let record = plan.functionals.contains(&d.name).then(|| plan.record());
        canon.insert(d.name.clone(), canon_const(&const_of, d, src, record));
      }
    }
    let mut stack = Vec::new();
    push_stack(
      &mut stack,
      const_occurrences(&|x: &Name| canon_names.contains(x), &md.value),
    );
    reach_canon(
      &canon,
      &canon_names,
      canon_names.len(),
      stack,
      &mut wanted,
      &mut wanted_set,
    );
  }
  if overlay.is_empty() {
    return Ok(CliquePrep { fresh, rows, reused, ..CliquePrep::default() });
  }
  let pending: Vec<Name> =
    wanted.into_iter().filter(|c| (h.addr)(c).is_none()).collect();
  let pending = sort_by_pretty(pending);
  let order = canon_rounds(
    h.addr,
    &canon,
    pending.len() + 1,
    pending,
    Vec::new(),
    FxHashSet::default(),
  )?;
  Ok(CliquePrep { overlay, sources, canon: order, fresh, rows, reused })
}

#[cfg(test)]
mod tests {
  use std::sync::Arc;

  use bignat::Nat;
  use rustc_hash::{FxHashMap, FxHashSet};

  use ix_common::address::Address;
  use ix_common::env::{ConstantInfo, DataValue, Env, Expr, Name};

  use super::{
    CliquePrep, HookEnv, canon_rounds, clique_callers, prepare_cliques,
  };
  use crate::compile::pass3::clique::basic::{dotted, mk_str, sort0};
  use crate::compile::pass3::clique::plan::{
    CliqueOutcome, CliquePlan, Encoding, OrderSource,
  };
  use crate::compile::pass3::clique::plan_clique::tests::{
    addr_of, env_of, input_const, names, wf_transported,
  };
  use crate::compile::pass3::clique::plan_clique::{canon_const, value_of};
  use crate::compile::pass3::clique::table::{
    CLIQUE_RECORD_BASE, CliqueTable, EncodingRoots,
  };
  use crate::compile::pass3::clique::transport::tests::{c, def};
  use crate::compile::pass3::names::inline_key;
  use crate::graph::NameSet;

  fn set(xs: &[&str]) -> NameSet {
    xs.iter().map(|x| dotted(x)).collect()
  }

  /// The clique table and the encoding roots of one clique without carried
  /// lemmas.
  fn tables(all: &[Name]) -> (CliqueTable, EncodingRoots) {
    let table: CliqueTable =
      all.iter().map(|m| (m.clone(), (all.to_vec(), vec![]))).collect();
    let mut roots: EncodingRoots = FxHashMap::default();
    if let Some(all0) = all.first() {
      roots.insert(mk_str(all0, "_mutual"), all.to_vec());
      roots.insert(mk_str(all0, "mutual"), all.to_vec());
    }
    for m in all {
      roots.insert(mk_str(m, "_f"), all.to_vec());
    }
    (table, roots)
  }

  fn hook<'a>(
    env: &'a Arc<Env>,
    table: &'a CliqueTable,
    roots: &'a EncodingRoots,
    plans: &'a FxHashMap<Name, CliqueOutcome>,
    check_plans: bool,
  ) -> HookEnv<'a> {
    HookEnv {
      env,
      addr: &addr_of,
      table,
      roots,
      plans,
      check_plans,
      wf_only: false,
    }
  }

  fn overlay_names(p: &CliquePrep) -> Vec<Name> {
    p.overlay.iter().map(|(n, _)| n.clone()).collect()
  }

  #[test]
  fn prepares_a_transported_clique() {
    let ((env, all, k), plan, _) = wf_transported();
    let (table, roots) = tables(&all);
    let plans = FxHashMap::default();
    let h = hook(&env, &table, &roots, &plans, false);
    let block: NameSet = all.iter().cloned().collect();
    let prep = prepare_cliques(&h, &block, &set(&["Nat"])).expect("prepared");
    // the members in pretty-name order, with the records from the base
    assert_eq!(overlay_names(&prep), names(&["f", "g"]));
    for (k_, (n, ci)) in prep.overlay.iter().enumerate() {
      let idx = CLIQUE_RECORD_BASE + k_ as u64;
      let Some(lean) = k.members.iter().find(|d| d.name == *n) else {
        panic!("a member")
      };
      let Some(md) = plan.members.get(n) else { panic!("transported") };
      let want = Expr::mdata(
        vec![(inline_key(), DataValue::OfNat(Nat::from(idx)))],
        md.value.clone(),
      );
      assert_eq!(ci.get_name(), n);
      assert_eq!(ci.get_type(), &lean.typ);
      assert_eq!(value_of(ci), Some(&want));
      assert_eq!(prep.sources.get(k_), Some(&(idx, lean.value.clone())));
    }
    assert_eq!(prep.sources.len(), 2);
    // the canonical constants, each after the ones it references: the
    // abstracted proof, then the packed function with the side-car record
    let Some((enc, _)) = plan.canon.first() else { panic!("canonical") };
    let Some((proof, _)) = plan.canon.get(1) else { panic!("canonical") };
    let canon: Vec<Name> = prep.canon.iter().map(|(n, _)| n.clone()).collect();
    assert_eq!(canon, vec![proof.name.clone(), enc.name.clone()]);
    let const_of = |n: &Name| env.get(n).map(|e| e.cloned());
    for ((n, ci), (d, src)) in
      prep.canon.iter().zip([&plan.canon[1], &plan.canon[0]])
    {
      let record = plan.functionals.contains(n).then(|| plan.record());
      let want = canon_const(&const_of, d, src, record);
      assert_eq!(value_of(ci), value_of(&want));
      assert_eq!(ci.get_type(), want.get_type());
    }
    assert!(plan.functionals.contains(&enc.name));
    // the plan is fresh, keyed by the first member
    assert_eq!(prep.reused, 0);
    let [(key, o)] = prep.fresh.as_slice() else { panic!("one plan") };
    assert_eq!(Some(key), all.first());
    assert!(o.same(&CliqueOutcome::Transported(Box::new(plan.clone()))));
    // one member's block: its own entry, the same canonical constants
    let Some(g) = all.get(1) else { panic!("two members") };
    let one: NameSet = [g.clone()].into_iter().collect();
    let prep1 =
      prepare_cliques(&h, &one, &NameSet::default()).expect("prepared");
    assert_eq!(overlay_names(&prep1), vec![g.clone()]);
    assert_eq!(prep1.sources.first().map(|s| s.0), Some(CLIQUE_RECORD_BASE));
    assert_eq!(prep1.canon.len(), 2);
    // already compiled canonical constants are not compiled again
    let compiled = |n: &Name| {
      if *n == enc.name || *n == proof.name {
        Some(Address::from_blake3_hash(*n.get_hash()))
      } else {
        addr_of(n)
      }
    };
    let h2 =
      HookEnv { addr: &compiled, ..hook(&env, &table, &roots, &plans, false) };
    let prep2 =
      prepare_cliques(&h2, &block, &NameSet::default()).expect("prepared");
    assert!(prep2.canon.is_empty() && prep2.overlay.len() == 2);
    // a block outside every clique: nothing to do
    let prep3 =
      prepare_cliques(&h, &set(&["h"]), &set(&["Nat"])).expect("prepared");
    assert!(prep3.is_empty());
    // the empty table
    let empty = CliqueTable::default();
    let h4 = hook(&env, &empty, &roots, &plans, false);
    assert!(
      prepare_cliques(&h4, &block, &NameSet::default())
        .expect("empty")
        .is_empty()
    );
    // the plan touches its members and canonical constants only
    assert!(
      plan.touches(g) && plan.touches(&enc.name) && plan.touches(&proof.name)
    );
    assert!(
      !plan.touches(&dotted("f._mutual")) && !plan.touches(&dotted("Nat"))
    );
  }

  #[test]
  fn the_plan_table() {
    let ((env, all, _), plan, _) = wf_transported();
    let (table, roots) = tables(&all);
    let Some(key) = all.first() else { panic!("two members") };
    let block: NameSet = all.iter().cloned().collect();
    let transported = CliqueOutcome::Transported(Box::new(plan));
    // a plan from the table: reused once for the block, not fresh
    let plans: FxHashMap<Name, CliqueOutcome> =
      [(key.clone(), transported.clone())].into_iter().collect();
    for check in [false, true] {
      let h = hook(&env, &table, &roots, &plans, check);
      let prep =
        prepare_cliques(&h, &block, &NameSet::default()).expect("prepared");
      assert!(prep.fresh.is_empty());
      assert_eq!(prep.reused, 1);
      assert_eq!(prep.overlay.len(), 2);
    }
    // a stale entry is used as it is, or fails the check
    let stale: FxHashMap<Name, CliqueOutcome> =
      [(key.clone(), CliqueOutcome::NotEncoded("stale".into()))]
        .into_iter()
        .collect();
    let h = hook(&env, &table, &roots, &stale, false);
    let prep =
      prepare_cliques(&h, &block, &NameSet::default()).expect("prepared");
    assert!(
      prep.overlay.is_empty() && prep.fresh.is_empty() && prep.canon.is_empty()
    );
    assert_eq!(prep.reused, 1);
    assert!(!prep.is_empty());
    let h = hook(&env, &table, &roots, &stale, true);
    let names: Vec<String> = all.iter().map(Name::pretty).collect();
    assert_eq!(
      prepare_cliques(&h, &block, &NameSet::default()).err(),
      Some(format!(
        "Pass 3 plan cache check: the plan of the clique #[{}]: the \
         recomputed value differs from the table's",
        names.join(", ")
      ))
    );
  }

  #[test]
  fn refuses_the_callers_of_a_transported_clique() {
    let ((env, all, _), plan, (env_u, all_u)) = wf_transported();
    let (table, roots) = tables(&all);
    let plans = FxHashMap::default();
    let h = hook(&env, &table, &roots, &plans, false);
    let Some(all0) = all.first() else { panic!("two members") };
    let encoding = mk_str(all0, "_mutual");
    let mut refs = set(&["g", "f", "Nat"]);
    refs.insert(encoding.clone());
    let clique: Vec<String> = all.iter().map(Name::pretty).collect();
    let refusal = |callers: &str, s: &str| {
      format!(
        "Pass 3 cliques: caller refused (block rule, callers adapt): {callers} \
         reference{s} f and Lean's encoding constant {} of the transported \
         clique #[{}] (sigma #[1, 0]); a caller may not unfold Lean's \
         encoding of a transported clique",
        encoding.pretty(),
        clique.join(", ")
      )
    };
    assert_eq!(
      prepare_cliques(&h, &set(&["c"]), &refs).err(),
      Some(refusal("[c]", "s"))
    );
    assert_eq!(
      prepare_cliques(&h, &set(&["d", "c"]), &refs).err(),
      Some(refusal("[c, d]", ""))
    );
    let (refused, fresh, reused) =
      clique_callers(&h, &set(&["c"]), &refs).expect("callers");
    assert_eq!(refused, Some(refusal("[c]", "s")));
    assert_eq!(reused, 0);
    let [(key, o)] = fresh.as_slice() else { panic!("one plan") };
    assert_eq!(key, all0);
    assert!(o.same(&CliqueOutcome::Transported(Box::new(plan))));
    // a block of the clique's unit, or one that references no member, is
    // not a caller (and plans nothing)
    for (block, refs) in [
      (set(&["f"]), refs.clone()),
      (set(&["c"]), [encoding.clone()].into_iter().collect()),
    ] {
      let (refused, fresh, reused) =
        clique_callers(&h, &block, &refs).expect("callers");
      assert!(refused.is_none() && fresh.is_empty() && reused == 0);
    }
    // no roots: nothing is read
    let no_roots = EncodingRoots::default();
    let h0 = hook(&env, &table, &no_roots, &plans, false);
    let (refused, fresh, _) =
      clique_callers(&h0, &set(&["c"]), &refs).expect("callers");
    assert!(refused.is_none() && fresh.is_empty());
    // the caller of an unchanged clique compiles; the plan is fresh
    let (table_u, roots_u) = tables(&all_u);
    let h_u = hook(&env_u, &table_u, &roots_u, &plans, false);
    let Some(u0) = all_u.first() else { panic!("two members") };
    let mut refs_u = set(&["f"]);
    refs_u.insert(mk_str(u0, "_mutual"));
    let prep = prepare_cliques(&h_u, &set(&["c"]), &refs_u).expect("compiles");
    let [(key, CliqueOutcome::Unchanged(..))] = prep.fresh.as_slice() else {
      panic!("one unchanged plan")
    };
    assert_eq!(key, u0);
    assert!(prep.overlay.is_empty() && prep.reused == 0);
  }

  /// A plan whose canonical constants `a`, `b` reference each other, the
  /// member `p` reaching `a`.
  fn cyclic_plan() -> CliquePlan {
    let decl = |n: &str, v: &str| def(n, sort0(), c(v));
    CliquePlan {
      all: names(&["p", "q"]),
      encoding: Encoding::WellFounded,
      sigma: vec![1, 0],
      classes: vec![names(&["q"]), names(&["p"])],
      source: OrderSource::Specification,
      members: [(dotted("p"), decl("p", "a"))].into_iter().collect(),
      canon: vec![(decl("a", "b"), dotted("x")), (decl("b", "a"), dotted("y"))],
      functionals: vec![],
      causes: vec![],
      aliases: vec![],
    }
  }

  #[test]
  fn canonical_constants_in_rounds() {
    let all = names(&["p", "q"]);
    let env = env_of(
      ["p", "q"]
        .iter()
        .map(|n| input_const(&def(n, sort0(), c("z")), &all))
        .collect(),
    );
    let (table, _) = tables(&all);
    let no_roots = EncodingRoots::default();
    let plans: FxHashMap<Name, CliqueOutcome> =
      [(dotted("p"), CliqueOutcome::Transported(Box::new(cyclic_plan())))]
        .into_iter()
        .collect();
    let none = |_: &Name| -> Option<Address> { None };
    let h =
      HookEnv { addr: &none, ..hook(&env, &table, &no_roots, &plans, false) };
    assert_eq!(
      prepare_cliques(&h, &set(&["p"]), &NameSet::default()).err().as_deref(),
      Some(
        "Pass 3 cliques: canonical constants with cyclic references: #[a, b]"
      )
    );
    // `b` compiled already: `a` alone, after it
    let b_done = |n: &Name| {
      (*n == dotted("b")).then(|| Address::from_blake3_hash(*n.get_hash()))
    };
    let h = HookEnv { addr: &b_done, ..h };
    let prep =
      prepare_cliques(&h, &set(&["p"]), &NameSet::default()).expect("prepared");
    let canon: Vec<Name> = prep.canon.iter().map(|(n, _)| n.clone()).collect();
    assert_eq!(canon, names(&["a"]));
    // the rounds: a constant waits for the ones it references, taken in the
    // same round when they come first
    let cs: FxHashMap<Name, ConstantInfo> =
      [("a", "b"), ("b", "c"), ("c", "z"), ("d", "c")]
        .iter()
        .map(|(n, v)| {
          (dotted(n), input_const(&def(n, sort0(), c(v)), &names(&[n])))
        })
        .collect();
    let rounds = |fuel: usize, pending: &[&str]| {
      canon_rounds(
        &none,
        &cs,
        fuel,
        names(pending),
        Vec::new(),
        FxHashSet::default(),
      )
      .map(|o| o.into_iter().map(|(n, _)| n).collect::<Vec<_>>())
    };
    assert_eq!(
      rounds(4, &["a", "b", "c", "d"]),
      Ok(names(&["c", "d", "b", "a"]))
    );
    assert_eq!(rounds(1, &["c", "d"]), Ok(names(&["c", "d"])));
    // out of rounds, or an unknown constant
    assert_eq!(
      rounds(1, &["a", "b", "c"]).err().as_deref(),
      Some(
        "Pass 3 cliques: canonical constants with cyclic references: #[a, b]"
      )
    );
    assert_eq!(rounds(0, &[]), Ok(vec![]));
    assert_eq!(
      rounds(2, &["c", "e"]).err().as_deref(),
      Some("Pass 3 cliques: no canonical constant e")
    );
  }
}
