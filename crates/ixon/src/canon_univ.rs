//! Universe-level canonicalization (canonicity §10.6).
//!
//! `canon_univ = linearize ∘ subsumption ∘ normalize_aux` — a total,
//! deterministic canonical representative of a stored level's Géran
//! semantic-equality class, kernel-free and next to the wire type so the
//! compilers, the Tc egress, and probes can all use it (the three kernel
//! `NormLevel` implementations stay untouched and serve as the P4
//! oracle). Mirrors `Ix/IxonUniv.lean`; the Géran machinery is the
//! transliteration of `Ix/Tc/Level.lean:227-472` /
//! `crates/kernel/src/level.rs` onto `ixon::univ::Univ`.
//!
//! The frozen kernel `mk*` rule set (M1–M8 / I1–I6, from Lean's
//! `kernel/level.cpp:81-120` via the three kernel mirrors) is kept with
//! its kernel-rebuild role: [`reduce_univ`] is the stage-1
//! decoration-presence test and the P6 oracle, and P3 (canonical forms
//! are `mk*` fixpoints) is what makes kernel ingress the identity on
//! canonical content.
//!
//! Property set (tested here; Verify-layer proofs are the D7 follow-up):
//! - P0 value preservation: `canon_univ u` and `u` agree at every
//!   valuation of the params (the compiler must not change the universe
//!   a declaration states);
//! - P1 idempotence: `canon_univ (canon_univ u) = canon_univ u`;
//! - P2 roundtrip-fixpoint: `normalize (linearize L) = L` for reachable
//!   `L` — exact on non-empty entries; `subsumption` can leave EMPTY
//!   entries behind (constant 0, no vars) which `linearize` cannot (and
//!   should not) re-express, so the strict form holds modulo empty
//!   entries ([`norm_eq_semantic`]). See the O1 note below.
//! - P3 mk*-fixpoint: `reduce_univ (canon_univ u) = canon_univ u`;
//! - P4 soundness: `univEq u (canon_univ u)` against the kernel oracle
//!   (lives in the kernel/Tc test suites — this crate cannot depend on
//!   the kernels), modulo the same empty-entry caveat;
//! - P5 mirror parity: byte-for-byte agreement with `Ix/IxonUniv.lean`
//!   (FFI cross-check in the Lean test suite);
//! - P6 mk* absorption: `canon_univ (reduce_univ u) = canon_univ u`.
//!
//! O1 empty-entry note: kernel `normLevelEq` compares subsumption output
//! maps INCLUDING empty entries, which makes kernel `univEq` strictly
//! finer than semantic level equality on rare shapes (34 of 3,253,373
//! whole-Mathlib table entries — e.g. `succ (max (u+1) (imax (u+1) v))`
//! keeps an empty `[u,v]` entry that its semantic equal
//! `max (u+2) (v+1)` never creates). `canon_univ` canonicalizes BY
//! SEMANTIC CLASS (empties carry no value), which is the "all the way to
//! Géran" endpoint; aligning the kernels' `normLevelEq` to ignore empty
//! entries (a completeness improvement — `normLevelLe` already ignores
//! them) is the pending kernel-side counterpart decision.

use std::collections::{BTreeMap, HashSet};
use std::sync::Arc;

use super::univ::Univ;

// ============================================================================
// Frozen kernel mk* rule set (M1-M8 / I1-I6)
// ============================================================================

fn is_explicit(u: &Univ) -> bool {
  match u {
    Univ::Zero => true,
    Univ::Succ(i) => is_explicit(i),
    _ => false,
  }
}

fn is_never_zero(u: &Univ) -> bool {
  match u {
    Univ::Succ(_) => true,
    Univ::Max(a, b) => is_never_zero(a) || is_never_zero(b),
    Univ::IMax(_, b) => is_never_zero(b),
    _ => false,
  }
}

/// Peel the outermost succ chain: `(base, n)` with `u = succ^n base`.
fn peel_offset(u: &Arc<Univ>) -> (Arc<Univ>, u64) {
  match u.as_ref() {
    Univ::Succ(i) => {
      let (b, n) = peel_offset(i);
      (b, n + 1)
    },
    _ => (u.clone(), 0),
  }
}

/// `mkMax` (Lean `kernel/level.cpp:81-103`; `Ix/Tc/Level.lean` `mkMax`;
/// `crates/kernel/src/level.rs` `KUniv::max`) transliterated to `Univ`.
/// First applicable rule wins: M1 numerals → the larger (ties → `a`);
/// M2 `max a a = a`; M3/M4 zero sides; M5/M6 absorption; M7 same-base
/// offsets; M8 raw.
pub fn n_max(a: Arc<Univ>, b: Arc<Univ>) -> Arc<Univ> {
  if is_explicit(&a) && is_explicit(&b) {
    let (_, na) = peel_offset(&a);
    let (_, nb) = peel_offset(&b);
    return if na >= nb { a } else { b };
  }
  if a == b {
    return a;
  }
  if matches!(a.as_ref(), Univ::Zero) {
    return b;
  }
  if matches!(b.as_ref(), Univ::Zero) {
    return a;
  }
  if let Univ::Max(bl, br) = b.as_ref()
    && (*bl == a || *br == a)
  {
    return b;
  }
  if let Univ::Max(al, ar) = a.as_ref()
    && (*al == b || *ar == b)
  {
    return a;
  }
  let (base_a, off_a) = peel_offset(&a);
  let (base_b, off_b) = peel_offset(&b);
  if base_a == base_b {
    return if off_a >= off_b { a } else { b };
  }
  Univ::max(a, b)
}

/// `mkIMax` (Lean `kernel/level.cpp:112-120` and kernel mirrors): I1
/// never-zero right → `n_max`; I2 `imax a 0 = 0`; I3 `imax 0 b = b`;
/// I4 `imax 1 b = b`; I5 `imax a a = a`; I6 raw.
pub fn n_imax(a: Arc<Univ>, b: Arc<Univ>) -> Arc<Univ> {
  if is_never_zero(&b) {
    return n_max(a, b);
  }
  if matches!(b.as_ref(), Univ::Zero) {
    return b;
  }
  if matches!(a.as_ref(), Univ::Zero) {
    return b;
  }
  if let Univ::Succ(i) = a.as_ref()
    && matches!(i.as_ref(), Univ::Zero)
  {
    return b;
  }
  if a == b {
    return a;
  }
  Univ::imax(a, b)
}

/// The kernel-rebuild closure on stored trees: bottom-up rebuild through
/// the simplifying constructors — exactly what anon/meta ingress does.
/// Mirrors `Ix.Tc.reduceIxonUniv`. A non-fixpoint entry reaches the
/// kernel changed (the stage-1 decoration-presence test), and P6 pins
/// that this rebuild refines into the Géran classes.
pub fn reduce_univ(u: &Arc<Univ>) -> Arc<Univ> {
  match u.as_ref() {
    Univ::Zero | Univ::Var(_) => u.clone(),
    Univ::Succ(i) => {
      let ri = reduce_univ(i);
      if ri == *i { u.clone() } else { Univ::succ(ri) }
    },
    Univ::Max(a, b) => n_max(reduce_univ(a), reduce_univ(b)),
    Univ::IMax(a, b) => n_imax(reduce_univ(a), reduce_univ(b)),
  }
}

// ============================================================================
// Géran canonical form (Ix/Tc/Level.lean:231-431 on Univ)
// ============================================================================

/// An imax-conditioning chain: sorted param indices.
pub type Path = Vec<u64>;

/// Per-path node: a constant plus variable contributions `(idx, offset)`
/// sorted by ascending idx. Invariant maintained by the normalizer:
/// every var's idx is a member of its own path (self-gating is free).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Node {
  pub constant: u64,
  pub vars: Vec<(u64, u64)>,
}

impl Node {
  pub fn is_empty(&self) -> bool {
    self.constant == 0 && self.vars.is_empty()
  }
}

/// Canonical form: map from imax-paths to nodes (lexicographic order).
pub type NormLevel = BTreeMap<Path, Node>;

/// Insert `(idx, k)` into the sorted var list, max-merging offsets. `k`
/// must be the current succ-accumulator (the classic port bug is
/// dropping it — `Ix/Tc/Level.lean:249-252`).
fn node_add_var(n: &mut Node, idx: u64, k: u64) {
  match n.vars.iter().position(|v| idx <= v.0) {
    Some(p) => {
      if n.vars[p].0 == idx {
        n.vars[p].1 = n.vars[p].1.max(k);
      } else {
        n.vars.insert(p, (idx, k));
      }
    },
    None => n.vars.push((idx, k)),
  }
}

fn add_var(acc: &mut NormLevel, idx: u64, k: u64, path: &Path) {
  node_add_var(acc.entry(path.clone()).or_default(), idx, k);
}

fn add_const(acc: &mut NormLevel, k: u64, path: &Path) {
  if k == 0 || (k == 1 && !path.is_empty()) {
    return;
  }
  let n = acc.entry(path.clone()).or_default();
  n.constant = n.constant.max(k);
}

fn ordered_insert(a: u64, path: &Path) -> Option<Path> {
  match path.binary_search(&a) {
    Ok(_) => None,
    Err(p) => {
      let mut out = path.clone();
      out.insert(p, a);
      Some(out)
    },
  }
}

/// The calls the normalizer already made (Lean's `CanonUniv.NState`).
/// Every contribution of `normalize_aux` and `normalize_imax_dispatch` is a
/// max-merge into one entry of the form (`add_const`, `add_var`), so a call
/// adds the same contributions whatever the form it starts from, and a call
/// made a second time adds nothing: the sets skip repeated calls, and the
/// form is the one the calls without them build. The `imax` distributions
/// repeat calls: on a chain `imax a (imax a (… (imax a u)))` (one `imax` per
/// binder, as Lean's `Meta.getLevel` returns for a long `∀`) the calls
/// without the sets are `2ⁿ`, with them `O(n²)`.
#[derive(Default)]
struct Seen {
  aux: HashSet<(Univ, Path, u64)>,
  dispatch: HashSet<(Univ, Univ, Path, u64)>,
}

fn normalize_aux(
  l: &Univ,
  path: &Path,
  k: u64,
  acc: &mut NormLevel,
  seen: &mut Seen,
) {
  if !seen.aux.insert((l.clone(), path.clone(), k)) {
    return;
  }
  match l {
    Univ::Zero => add_const(acc, k, path),
    Univ::Succ(i) => normalize_aux(i, path, k + 1, acc, seen),
    Univ::Max(a, b) => {
      normalize_aux(a, path, k, acc, seen);
      normalize_aux(b, path, k, acc, seen);
    },
    Univ::IMax(u, b) => normalize_imax_dispatch(u, b, path, k, acc, seen),
    Univ::Var(idx) => match ordered_insert(*idx, path) {
      Some(new_path) => {
        // When param(idx) = 0, imax(u, 0) = 0 — the outer k succs
        // still contribute at the un-extended path.
        add_const(acc, k, path);
        add_var(acc, *idx, k, &new_path);
      },
      None => {
        if k != 0 {
          add_var(acc, *idx, k, path);
        }
      },
    },
  }
}

/// Dispatch `imax(a, b)` on `b`'s shape, including the distributions
/// `imax(a, max(v, w)) = max(imax(a, v), imax(a, w))` and
/// `imax(a, imax(v, w)) = max(imax(a, w), imax(v, w))` (these duplicate
/// calls: without `Seen`, the §3.5 worst-case-exponential compile-time
/// cost).
fn normalize_imax_dispatch(
  a: &Univ,
  b: &Univ,
  path: &Path,
  k: u64,
  acc: &mut NormLevel,
  seen: &mut Seen,
) {
  if !seen.dispatch.insert((a.clone(), b.clone(), path.clone(), k)) {
    return;
  }
  match b {
    Univ::Zero => add_const(acc, k, path),
    Univ::Succ(v) => {
      normalize_aux(a, path, k, acc, seen);
      normalize_aux(v, path, k + 1, acc, seen);
    },
    Univ::Max(v, w) => {
      normalize_imax_dispatch(a, v, path, k, acc, seen);
      normalize_imax_dispatch(a, w, path, k, acc, seen);
    },
    Univ::IMax(v, w) => {
      normalize_imax_dispatch(a, w, path, k, acc, seen);
      normalize_imax_dispatch(v, w, path, k, acc, seen);
    },
    Univ::Var(idx) => match ordered_insert(*idx, path) {
      Some(new_path) => {
        add_const(acc, k, path);
        add_var(acc, *idx, k, &new_path);
        normalize_aux(a, &new_path, k, acc, seen);
      },
      None => {
        if k != 0 {
          add_var(acc, *idx, k, path);
        }
        normalize_aux(a, path, k, acc, seen);
      },
    },
  }
}

fn is_subset(p2: &[u64], p1: &[u64]) -> bool {
  let mut i1 = 0;
  for x in p2 {
    loop {
      if i1 >= p1.len() {
        return false;
      }
      if p1[i1] == *x {
        i1 += 1;
        break;
      }
      if p1[i1] > *x {
        return false;
      }
      i1 += 1;
    }
  }
  true
}

/// Keep only the `xs` entries not dominated by a `ys` entry (merge-walk
/// over sorted var lists). Mirrors `Ix.Tc.Level.subsumeVars`.
fn subsume_vars(xs: &[(u64, u64)], ys: &[(u64, u64)]) -> Vec<(u64, u64)> {
  let mut out = Vec::new();
  let (mut xi, mut yi) = (0, 0);
  while xi < xs.len() {
    if yi >= ys.len() {
      out.extend_from_slice(&xs[xi..]);
      break;
    }
    let x = xs[xi];
    let y = ys[yi];
    if x.0 < y.0 {
      out.push(x);
      xi += 1;
    } else if x.0 == y.0 {
      if x.1 > y.1 {
        out.push(x);
      }
      xi += 1;
      yi += 1;
    } else {
      yi += 1;
    }
  }
  out
}

/// Drop contributions dominated by entries at sub-paths. Iterates
/// entries and the pre-pass snapshot in ascending key order, exactly
/// like the kernel mirrors (in-loop `n1` mutations are order-sensitive).
fn subsumption(acc: NormLevel) -> NormLevel {
  let snapshot: Vec<(Path, Node)> =
    acc.iter().map(|(p, n)| (p.clone(), n.clone())).collect();
  let mut result = acc;
  for (p1, n1_0) in &snapshot {
    let mut n1 = n1_0.clone();
    for (p2, n2) in &snapshot {
      if is_subset(p2, p1) {
        let same = p1.len() == p2.len();
        if n1.constant != 0 {
          let max_var_offset = n1.vars.iter().fold(0, |m, v| m.max(v.1));
          let keep_const = (same || n1.constant > n2.constant)
            && (n2.vars.is_empty() || n1.constant > max_var_offset + 1);
          if !keep_const {
            n1.constant = 0;
          }
        }
        if !same && !n2.vars.is_empty() {
          n1.vars = subsume_vars(&n1.vars, &n2.vars);
        }
      }
    }
    result.insert(p1.clone(), n1);
  }
  result
}

/// Normalize a stored level to Géran's canonical form (the kernel's
/// comparison structure, on `Univ`).
pub fn normalize(u: &Univ) -> NormLevel {
  let mut acc = NormLevel::new();
  acc.insert(Vec::new(), Node::default());
  normalize_aux(u, &Vec::new(), 0, &mut acc, &mut Seen::default());
  subsumption(acc)
}

/// Semantic canonical-form equality: entries compared modulo EMPTY
/// entries (constant 0, no vars — value-free subsumption artifacts).
/// `normLevelLe` in the kernels is already empty-insensitive; strict
/// `normLevelEq` is not (the O1 note in the module doc).
pub fn norm_eq_semantic(a: &NormLevel, b: &NormLevel) -> bool {
  let mut ai = a.iter().filter(|(_, n)| !n.is_empty());
  let mut bi = b.iter().filter(|(_, n)| !n.is_empty());
  loop {
    match (ai.next(), bi.next()) {
      (None, None) => return true,
      (Some(x), Some(y)) if x == y => {},
      _ => return false,
    }
  }
}

// ============================================================================
// Linearization (§3.2 — the O1 construction)
// ============================================================================

fn succs(mut u: Arc<Univ>, n: u64) -> Arc<Univ> {
  for _ in 0..n {
    u = Univ::succ(u);
  }
  u
}

/// Is a `u_i = 0` fallout of `k` dominated under `ctx`? Some entry at a
/// subset path must guarantee ≥ k whenever `ctx` is active: a constant
/// ≥ k, or a var atom `(q, off)` with `off + 1 ≥ k` (its `u_q` is ≥ 1
/// under the context). This is `subsumption`'s own domination logic,
/// read back. Exact: at `u_i = 0`, with the context's params at 1 and
/// every other param at 0, the map's value is the best such guarantee.
fn covered(norm: &NormLevel, k: u64, ctx: &[u64]) -> bool {
  if k == 0 {
    return true;
  }
  norm.iter().any(|(q, n)| {
    q.iter().all(|x| ctx.contains(x))
      && (n.constant >= k || n.vars.iter().any(|(_, off)| off + 1 >= k))
  })
}

/// Gate-nesting order for a context (outermost first), and whether it
/// is leak-free. The greedy pick is the smallest remaining gate `g` with
/// a `(g, ·)` atom at some non-empty map path inside `chosen ∪ {g}`: its
/// creation site, the absorber of its leak. The binary `imax` chain
/// leaks each gate's own value under weaker conditions than the full
/// context (`imax(t, u_g) ≥ u_g` wherever the outer gates are active),
/// and an absorber atom is exactly what dominates that leak.
/// Absorbability only grows with `chosen`, so the greedy finds a full
/// order whenever one exists. Every path of a normalizer-reachable map
/// has one (its gating chain starts at a singleton, and subsumption only
/// removes an atom in favor of a dominator at a sub-path); a
/// self-stripped context `P∖{i}` need not, which the second component
/// reports. When no remaining gate is absorbable, the smallest is taken
/// for totality and the order is reported as leaking (`false`).
fn gate_order(norm: &NormLevel, ctx: &[u64]) -> (Vec<u64>, bool) {
  let mut order: Vec<u64> = Vec::new();
  let mut leak_free = true;
  let mut remaining: Vec<u64> = ctx.to_vec();
  while !remaining.is_empty() {
    let found = remaining.iter().copied().find(|g| {
      norm.iter().any(|(p, n)| {
        !p.is_empty()
          && p.iter().all(|x| *x == *g || order.contains(x))
          && n.vars.iter().any(|(i, _)| i == g)
      })
    });
    let pick = found.unwrap_or_else(|| {
      leak_free = false;
      remaining[0]
    });
    order.push(pick);
    remaining.retain(|x| *x != pick);
  }
  (order, leak_free)
}

/// The canonical representative of a canonical form, by per-atom gate
/// inversion.
///
/// Map semantics: `val = max` over entries `(P, {c, vars})` — active
/// when every `u_p, p ∈ P` is ≥ 1 — of `max(c, max (u_i + k))`. The
/// normalizer maintains two invariants this inversion leans on: every
/// var atom's idx is a member of its own path, and each gating step
/// writes a `(q, k)` atom at the singleton extension of its context
/// plus a fallout constant `addConst(k, path)` (skipped for k ≤ 1 in
/// gated contexts).
///
/// Inversion:
/// 1. explode entries into per-atom items; self-strip each atom
///    `(i, k)@P` to context `P∖{i}` when BOTH
///    - its `u_i = 0` fallout `k` is covered there ([`covered`]: some
///      entry at a sub-path of the context guarantees `≥ k`), and
///    - the context's own gates are leak-free ([`gate_order`] finds an
///      absorber for every gate of `P∖{i}`): the emitted chain
///      `imax(…, u_g)` is `≥ u_g` wherever its outer gates are active,
///      so a gate without an absorber at a path inside its prefix would
///      raise the value. With the first condition alone,
///      `imax (imax (imax u w + 1) u) v` would canonicalize to a level
///      that is `2` at `u = 0, v = 1, w = 2` where it is `1`;
///
///    otherwise it stays fully gated at `P` (every map path is
///    leak-free: its creation chain is a gate order);
/// 2. group items by context; a context group emits
///    `imax(…imax(body, u_o(m-1))…, u_o0)` along the recovered gate order
///    `o` (outermost first), with body = atoms ascending by idx, then the
///    gated constant; each `(o_j, 0)` marker item at the context
///    `{o_0..o_(j-1)}` is consumed (gate `o_j` re-supplies it);
/// 3. unconsumed markers emit as bare vars; the root constant emits
///    last, unless absorbed by a top-level atom with `k ≥ c`.
///
/// Output shape: a right-nested `max` chain — root atoms (ascending
/// idx), then gate groups in lexicographic context order, then the root
/// constant. Everything is inherited from the map's own ordering — no
/// fresh choices — and the result is a `mk*` fixpoint (P3). Every emitted
/// term is at most the map's value, and every map contribution is at most
/// some emitted term, so the value is preserved (P0).
pub fn linearize(norm: &NormLevel) -> Arc<Univ> {
  let const_at = |p: &[u64]| -> u64 { norm.get(p).map_or(0, |n| n.constant) };
  let c_root = const_at(&[]);
  // Context groups: constant + atoms (max-merged per idx).
  #[derive(Default)]
  struct Group {
    constant: u64,
    atoms: BTreeMap<u64, u64>, // idx -> offset
  }
  let mut groups: BTreeMap<Path, Group> = BTreeMap::new();
  for (path, node) in norm {
    if !path.is_empty() && node.constant > 0 {
      let g = groups.entry(path.clone()).or_default();
      g.constant = g.constant.max(node.constant);
    }
    for (i, k) in &node.vars {
      let ctx: Path = path.iter().copied().filter(|p| p != i).collect();
      let home = if covered(norm, *k, &ctx) && gate_order(norm, &ctx).1 {
        ctx
      } else {
        path.clone()
      };
      let g = groups.entry(home).or_default();
      let slot = g.atoms.entry(*i).or_insert(0);
      *slot = (*slot).max(*k);
    }
  }
  // Marker consumption: re-normalizing the emitted chain recreates gate
  // `order[j]`'s `(order[j], 0)` marker at the path `{order[0..=j]}`,
  // which self-strips to the item context `{order[0..j]}` — so a marker
  // item already there is re-supplied by the gate, not re-emitted.
  let mut consumed: HashSet<(Path, u64)> = HashSet::new();
  for (ctx, g) in &groups {
    if ctx.is_empty() || (g.constant == 0 && g.atoms.is_empty()) {
      continue;
    }
    let (order, _) = gate_order(norm, ctx);
    for (j, p) in order.iter().enumerate() {
      let mut mctx: Path = order[..j].to_vec();
      mctx.sort_unstable();
      if groups.get(&mctx).is_some_and(|sg| sg.atoms.get(p) == Some(&0)) {
        consumed.insert((mctx, *p));
      }
    }
  }
  // Emission.
  let mut terms: Vec<Arc<Univ>> = Vec::new();
  let mut root_c_absorbed = false;
  if let Some(top) = groups.get(&Vec::new()) {
    for (i, k) in &top.atoms {
      if *k == 0 && consumed.contains(&(Vec::new(), *i)) {
        continue;
      }
      terms.push(succs(Univ::var(*i), *k));
      if *k >= c_root {
        root_c_absorbed = true;
      }
    }
  }
  for (ctx, g) in &groups {
    if ctx.is_empty() {
      continue;
    }
    let mut atoms: Vec<Arc<Univ>> = Vec::new();
    for (i, k) in &g.atoms {
      if *k == 0 && consumed.contains(&(ctx.clone(), *i)) {
        continue;
      }
      atoms.push(succs(Univ::var(*i), *k));
    }
    if g.constant > 0 {
      atoms.push(succs(Univ::zero(), g.constant));
    }
    let Some(body) = ({
      let mut it = atoms.into_iter().rev();
      it.next().map(|last| it.fold(last, |acc, a| Univ::max(a, acc)))
    }) else {
      continue;
    };
    // Wrap gates innermost-to-outermost following the recovered order.
    let (order, _) = gate_order(norm, ctx);
    let term =
      order.iter().rev().fold(body, |acc, p| Univ::imax(acc, Univ::var(*p)));
    terms.push(term);
  }
  if c_root > 0 && !root_c_absorbed {
    terms.push(succs(Univ::zero(), c_root));
  }
  let mut it = terms.into_iter().rev();
  match it.next() {
    None => Univ::zero(),
    Some(last) => it.fold(last, |acc, t| Univ::max(t, acc)),
  }
}

/// The canonical representative of `u`'s Géran class.
pub fn canon_univ(u: &Arc<Univ>) -> Arc<Univ> {
  linearize(&normalize(u))
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::univ::tests::arbitrary_univ;
  use quickcheck::{Arbitrary, Gen};
  use quickcheck_macros::quickcheck;

  #[derive(Clone, Debug)]
  struct AU(Arc<Univ>);

  impl Arbitrary for AU {
    fn arbitrary(g: &mut Gen) -> Self {
      AU(arbitrary_univ(g))
    }
  }

  fn v(i: u64) -> Arc<Univ> {
    Univ::var(i)
  }
  fn s(u: Arc<Univ>) -> Arc<Univ> {
    Univ::succ(u)
  }
  fn z() -> Arc<Univ> {
    Univ::zero()
  }
  fn m(a: Arc<Univ>, b: Arc<Univ>) -> Arc<Univ> {
    Univ::max(a, b)
  }
  fn im(a: Arc<Univ>, b: Arc<Univ>) -> Arc<Univ> {
    Univ::imax(a, b)
  }

  // ---- fixed vectors: one per mk* rule ----

  #[test]
  fn reduce_univ_rule_table() {
    // M1 numerals → larger.
    assert_eq!(reduce_univ(&m(s(z()), s(s(z())))), s(s(z())));
    // M2 max a a = a.
    assert_eq!(reduce_univ(&m(v(0), v(0))), v(0));
    // M3 / M4 zero sides.
    assert_eq!(reduce_univ(&m(z(), v(0))), v(0));
    assert_eq!(reduce_univ(&m(v(0), z())), v(0));
    // M5 absorption into b.
    assert_eq!(reduce_univ(&m(v(0), m(v(0), v(1)))), m(v(0), v(1)));
    // M6 absorption into a.
    assert_eq!(reduce_univ(&m(m(v(0), v(1)), v(1))), m(v(0), v(1)));
    // M7 same-base offsets.
    assert_eq!(reduce_univ(&m(s(v(0)), s(s(v(0))))), s(s(v(0))));
    // M8 raw survives.
    assert_eq!(reduce_univ(&m(v(0), v(1))), m(v(0), v(1)));
    // I1 never-zero right → max.
    assert_eq!(reduce_univ(&im(v(0), s(v(1)))), m(v(0), s(v(1))));
    // I2 imax a 0 = 0.
    assert_eq!(reduce_univ(&im(v(0), z())), z());
    // I3 imax 0 b = b.
    assert_eq!(reduce_univ(&im(z(), v(0))), v(0));
    // I4 imax 1 b = b.
    assert_eq!(reduce_univ(&im(s(z()), v(0))), v(0));
    // I5 imax a a = a.
    assert_eq!(reduce_univ(&im(v(0), v(0))), v(0));
    // I6 raw survives.
    assert_eq!(reduce_univ(&im(v(0), v(1))), im(v(0), v(1)));
    // The Mathlib WF eq_def shape: imax (imax 1 u) u → u.
    assert_eq!(reduce_univ(&im(im(s(z()), v(0)), v(0))), v(0));
  }

  // ---- fixed vectors: canonical representatives ----

  #[test]
  fn canon_fixpoints() {
    // Common source spellings are their own representatives.
    for u in [
      z(),
      s(z()),
      v(0),
      s(v(0)),
      s(s(v(3))),
      m(v(0), v(1)),
      m(s(v(0)), s(v(1))),
      im(v(0), v(1)),
      im(s(v(1)), v(0)),
      im(im(s(v(0)), v(1)), v(2)),
      m(v(0), m(v(1), v(2))),
    ] {
      assert_eq!(canon_univ(&u), u, "expected fixpoint: {u:?}");
    }
  }

  #[test]
  fn canon_collapses_twins() {
    // Commutative order twins.
    assert_eq!(canon_univ(&m(v(1), v(0))), m(v(0), v(1)));
    // Reassociation.
    assert_eq!(canon_univ(&m(m(v(0), v(1)), v(2))), m(v(0), m(v(1), v(2))));
    // Succ distribution.
    assert_eq!(canon_univ(&s(m(v(0), v(1)))), m(s(v(0)), s(v(1))));
    // mk*-reducible spellings land on the reduced class.
    assert_eq!(canon_univ(&im(im(s(z()), v(0)), v(0))), v(0));
    assert_eq!(canon_univ(&m(v(0), v(0))), v(0));
    // Redundant numeral absorption.
    assert_eq!(
      canon_univ(&m(m(s(v(0)), s(v(1))), s(z()))),
      m(s(v(0)), s(v(1)))
    );
  }

  // ---- properties ----
  // `#[quickcheck]` requires by-value `Arbitrary` arguments; the
  // needless_pass_by_value lint doesn't see through the macro.

  #[quickcheck]
  #[allow(clippy::needless_pass_by_value)]
  fn p1_idempotent(u: AU) -> bool {
    let c = canon_univ(&u.0);
    canon_univ(&c) == c
  }

  #[quickcheck]
  #[allow(clippy::needless_pass_by_value)]
  fn p2_roundtrip_fixpoint(u: AU) -> bool {
    let n = normalize(&u.0);
    norm_eq_semantic(&normalize(&linearize(&n)), &n)
  }

  #[quickcheck]
  #[allow(clippy::needless_pass_by_value)]
  fn p3_mk_fixpoint(u: AU) -> bool {
    let c = canon_univ(&u.0);
    reduce_univ(&c) == c
  }

  #[quickcheck]
  #[allow(clippy::needless_pass_by_value)]
  fn p6_mk_absorption(u: AU) -> bool {
    canon_univ(&reduce_univ(&u.0)) == canon_univ(&u.0)
  }

  /// The linearizer picks a representative of the SEMANTIC class: its
  /// canonical form matches the input's modulo empty entries.
  #[quickcheck]
  #[allow(clippy::needless_pass_by_value)]
  fn canon_stays_in_class(u: AU) -> bool {
    norm_eq_semantic(&normalize(&canon_univ(&u.0)), &normalize(&u.0))
  }

  // ---- P0: value preservation ----

  /// The value of a level at a valuation of its params (`u_i ↦ vals[i]`).
  fn eval(u: &Univ, vals: &[u64]) -> u64 {
    match u {
      Univ::Zero => 0,
      Univ::Succ(i) => eval(i, vals) + 1,
      Univ::Max(a, b) => eval(a, vals).max(eval(b, vals)),
      Univ::IMax(a, b) => {
        let vb = eval(b, vals);
        if vb == 0 { 0 } else { eval(a, vals).max(vb) }
      },
      Univ::Var(i) => vals[usize::try_from(*i).unwrap()],
    }
  }

  /// The largest `succ` nesting.
  fn max_offset(u: &Univ) -> u64 {
    match u {
      Univ::Zero | Univ::Var(_) => 0,
      Univ::Succ(i) => max_offset(i) + 1,
      Univ::Max(a, b) | Univ::IMax(a, b) => max_offset(a).max(max_offset(b)),
    }
  }

  /// The first valuation of params `0..params` at which `a` and `b`
  /// differ, over values `{0, 1, 2, M-1, M}` with `M` four above the
  /// largest offset. Exact: by Géran's decomposition, a sublevel of one
  /// side not dominated by a single sublevel of the other is exposed by
  /// setting its condition params to 1, its variable to `M` and every
  /// other param to 0, so two levels that differ anywhere differ here.
  fn differ_at(a: &Univ, b: &Univ, params: usize) -> Option<Vec<u64>> {
    let m = max_offset(a).max(max_offset(b)) + 4;
    let values = [0, 1, 2, m - 1, m];
    let mut vals = vec![0u64; params];
    let total = values.len().pow(u32::try_from(params).unwrap());
    for code in 0..total {
      let mut c = code;
      for x in &mut vals {
        *x = values[c % values.len()];
        c /= values.len();
      }
      if eval(a, &vals) != eval(b, &vals) {
        return Some(vals);
      }
    }
    None
  }

  /// Does `subsumption` leave a sublevel that a single other sublevel
  /// dominates? A constant `c@P` is dominated by a constant `≥ c` at a
  /// strict sub-path, or by an atom `(y, k)` with `k + 1 ≥ c` at a
  /// sub-path; an atom `(x, k)@P` by an atom `(x, ≥ k)` at a strict
  /// sub-path. `subsumption` mirrors the kernels' normalizers, which
  /// test a constant against the vars of its own node instead of the
  /// dominator's (for example `max (v+1) (imax (imax 2 u) v)`
  /// keeps the constant `2` at `[u, v]`, dominated by `v + 1`). Only
  /// such leftovers make two equal levels' normal forms differ, so a
  /// slip-free normal form is the unique one of its class.
  fn has_slip(n: &NormLevel) -> bool {
    n.iter().any(|(p, node)| {
      let c = node.constant;
      let const_dominated = c > 0
        && n.iter().any(|(q, m)| {
          is_subset(q, p)
            && ((q.len() < p.len() && m.constant >= c)
              || m.vars.iter().any(|(_, k)| k + 1 >= c))
        });
      let var_dominated = node.vars.iter().any(|(x, k)| {
        n.iter().any(|(q, m)| {
          q.len() < p.len()
            && is_subset(q, p)
            && m.vars.iter().any(|(y, k2)| y == x && k2 >= k)
        })
      });
      const_dominated || var_dominated
    })
  }

  /// P0–P3, P6 and class stability of one level over params
  /// `0..params`; failures are appended to `out`. P0 and P3 are checked
  /// unconditionally. With `strict`, so are the rest; otherwise P1, P2
  /// and class stability are checked when neither `u`'s nor its
  /// canonical form's normal form has a subsumption leftover
  /// ([`has_slip`]), and P6 when neither `u`'s nor `reduce_univ u`'s
  /// has; the skipped draws are counted in `slips`.
  fn check_canon(
    u: &Arc<Univ>,
    params: usize,
    strict: bool,
    out: &mut Vec<String>,
    slips: &mut usize,
  ) {
    let n = normalize(u);
    let c = canon_univ(u);
    if let Some(vals) = differ_at(u, &c, params) {
      out.push(format!(
        "P0 {u:?} → {c:?}: {} vs {} at {vals:?}",
        eval(u, &vals),
        eval(&c, &vals)
      ));
    }
    if reduce_univ(&c) != c {
      out.push(format!("P3 {u:?} → {c:?} (reduces to {:?})", reduce_univ(&c)));
    }
    let nc = normalize(&c);
    if strict || !(has_slip(&n) || has_slip(&nc)) {
      if canon_univ(&c) != c {
        out.push(format!("P1 {u:?} → {c:?} → {:?}", canon_univ(&c)));
      }
      if !norm_eq_semantic(&normalize(&linearize(&n)), &n) {
        out.push(format!("P2 {u:?} → {c:?}"));
      }
      if !norm_eq_semantic(&nc, &n) {
        out.push(format!("CLASS {u:?} → {c:?}"));
      }
    } else {
      *slips += 1;
    }
    let r = reduce_univ(u);
    if (strict || !(has_slip(&n) || has_slip(&normalize(&r))))
      && canon_univ(&r) != c
    {
      out.push(format!("P6 {u:?} → {c:?}"));
    }
  }

  /// The smallest level found whose canonical form changes its value
  /// without the leak-free proviso (`imax (imax (imax u w + 1) u) v`):
  /// the self-strip of `u + 1` from `[u, v, w]` to `[v, w]` would leave
  /// gate `w` without an absorber, leaking `w` at `u = 0`.
  /// `imax (a (n-1)) (imax (a (n-2)) (… (imax (a 0) last)))`: one `imax`
  /// per binder, the shape Lean's `Meta.getLevel` returns for a long `∀`.
  fn imax_chain(
    a: &dyn Fn(usize) -> Arc<Univ>,
    last: Arc<Univ>,
    n: usize,
  ) -> Arc<Univ> {
    (0..n).fold(last, |acc, i| im(a(i), acc))
  }

  /// FU item 10 (the Lean mirror tests the same chains): the `imax`
  /// distributions repeat the normalizer's calls (`2ⁿ` on these chains);
  /// `Seen` skips the repeats, so chains of 64 finish, keep their value and
  /// are idempotent.
  #[test]
  fn long_imax_chains() {
    let cutsat = |n| imax_chain(&|_| m(s(z()), v(0)), v(0), n);
    let mixed = |n: usize| {
      imax_chain(
        &|i| match i % 3 {
          0 => m(s(z()), v(0)),
          1 => s(v(1)),
          _ => im(v(1), v(0)),
        },
        v(if n.is_multiple_of(2) { 0 } else { 1 }),
        n,
      )
    };
    assert_eq!(canon_univ(&cutsat(64)), v(0));
    for n in [0, 1, 2, 5, 10, 24, 40, 64] {
      for l in [cutsat(n), mixed(n)] {
        let c = canon_univ(&l);
        assert_eq!(differ_at(&l, &c, 2), None, "P0 n={n}: {c:?}");
        assert_eq!(canon_univ(&c), c, "P1 n={n}");
        assert_eq!(reduce_univ(&c), c, "P3 n={n}");
      }
    }
  }

  #[test]
  fn p0_witness() {
    let (u, vv, w) = (v(0), v(1), v(2));
    let l = im(im(s(im(u.clone(), w.clone())), u.clone()), vv.clone());
    let c = canon_univ(&l);
    assert_eq!(eval(&l, &[0, 1, 2]), 1);
    assert_eq!(eval(&c, &[0, 1, 2]), 1, "canon {c:?}");
    // The representative itself, pinned (the Lean mirror pins the same).
    assert_eq!(
      c,
      m(
        im(im(s(w.clone()), u.clone()), vv.clone()),
        im(im(im(s(u.clone()), w.clone()), u.clone()), vv.clone())
      )
    );
    let (mut failures, mut slips) = (Vec::new(), 0);
    for x in witness_family() {
      check_canon(&x, 4, true, &mut failures, &mut slips);
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
  }

  /// The witness under every renaming of its params (and a fourth),
  /// with deeper offsets, under `max 1`, `succ` and a further gate,
  /// plus one other shrunk counterexample of that linearization.
  fn witness_family() -> Vec<Arc<Univ>> {
    let mut out = Vec::new();
    let perms: [[u64; 3]; 8] = [
      [0, 1, 2],
      [0, 2, 1],
      [1, 0, 2],
      [1, 2, 0],
      [2, 0, 1],
      [2, 1, 0],
      [3, 1, 0],
      [0, 3, 2],
    ];
    for [a, b, c] in perms {
      let (u, vv, w) = (v(a), v(b), v(c));
      for k in 1..=3 {
        let inner = succs(im(u.clone(), w.clone()), k);
        let l = im(im(inner, u.clone()), vv.clone());
        out.push(l.clone());
        out.push(m(s(z()), l.clone()));
        out.push(s(l.clone()));
        out.push(im(l.clone(), w.clone()));
        out.push(m(l.clone(), im(vv.clone(), u.clone())));
      }
    }
    // `imax(imax(imax(imax(0,u0),u2)+1,u0),u1)+1` (canon-shrink kind 0).
    out.push(s(im(im(s(im(im(z(), v(0)), v(2))), v(0)), v(1))));
    out
  }

  /// The pseudo-random generator of the kernel level comparison
  /// (`Tests.Ix.Kernel.LevelComparison.biasedLevel`): levels biased towards `imax` by a parameter,
  /// offsets and `max`. Mirrored by `Tests.Gen.Ixon.biasedUniv`.
  fn lcg_next(seed: u64) -> u64 {
    seed
      .wrapping_mul(6_364_136_223_846_793_005)
      .wrapping_add(1_442_695_040_888_963_407)
  }

  fn biased(params: u64, size: usize, seed: u64) -> (Arc<Univ>, u64) {
    let seed = lcg_next(seed);
    let pick = (seed >> 33) % 10;
    let p = v((seed >> 40) % params);
    if size <= 1 || pick < 2 {
      (if pick == 0 { z() } else { p }, seed)
    } else if pick < 4 {
      let (a, seed) = biased(params, size - 1, seed);
      (s(a), seed)
    } else if pick < 6 {
      let (a, seed) = biased(params, size / 2, seed);
      let (b, seed) = biased(params, size / 2, seed);
      (m(a, b), seed)
    } else if pick < 9 {
      let (a, seed) = biased(params, size - 1, seed);
      (im(a, p), seed)
    } else {
      let (a, seed) = biased(params, size / 2, seed);
      let (b, seed) = biased(params, size / 2, seed);
      (im(a, b), seed)
    }
  }

  /// P0–P3/P6/class over biased random levels and the levels type
  /// inference builds from them (`max 1 a`, `max a b`, `imax a b`,
  /// `succ a`): 20,000 draws over three params at size 10 (the
  /// differential's family; before the gate check, 109 of its levels and
  /// 2,128 of all 125,000 changed value) and 5,000 over four at size 12.
  /// P1/P2/class/P6 are conditional on slip-free normal forms
  /// ([`check_canon`]): 239 of the 125,000 draws have a normal form
  /// with a subsumption leftover, and 173 of those are not idempotent.
  #[test]
  fn p0_biased_random() {
    let (mut failures, mut slips) = (Vec::new(), 0);
    let mut total = 0;
    for (params, size, count, mut seed) in
      [(3u64, 10usize, 20_000usize, 41u64), (4, 12, 5_000, 43)]
    {
      let count = if cfg!(debug_assertions) { count / 10 } else { count };
      let ps = usize::try_from(params).unwrap();
      for _ in 0..count {
        let (a, s1) = biased(params, size, seed);
        let (b, s2) = biased(params, size, s1);
        seed = s2;
        for x in [
          a.clone(),
          m(s(z()), a.clone()),
          m(a.clone(), b.clone()),
          im(a.clone(), b.clone()),
          s(a.clone()),
        ] {
          total += 1;
          check_canon(&x, ps, false, &mut failures, &mut slips);
        }
      }
    }
    assert!(
      failures.is_empty(),
      "{}",
      failures[..failures.len().min(12)].join("\n")
    );
    // The slip is rare; a jump here means the normal forms changed.
    assert!(slips * 200 < total, "{slips} of {total} draws hit the slip");
  }

  /// Exhaustive enumeration of every level term up to `size` constructor
  /// nodes over three params — deterministic minimal counterexamples
  /// where quickcheck only reports failure.
  fn enumerate(size: usize) -> Vec<Arc<Univ>> {
    let mut by_size: Vec<Vec<Arc<Univ>>> = vec![Vec::new(); size + 1];
    if size >= 1 {
      by_size[1] = vec![z(), v(0), v(1), v(2)];
    }
    for n in 2..=size {
      let mut out: Vec<Arc<Univ>> = Vec::new();
      for u in &by_size[n - 1] {
        out.push(s(u.clone()));
      }
      for k in 1..n - 1 {
        for a in &by_size[k].clone() {
          for b in &by_size[n - 1 - k] {
            out.push(m(a.clone(), b.clone()));
            out.push(im(a.clone(), b.clone()));
          }
        }
      }
      by_size[n] = out;
    }
    by_size.into_iter().flatten().collect()
  }

  /// Every term of up to 8 nodes in release (112,000 terms; the witness
  /// has 8), 6 in debug.
  #[test]
  fn exhaustive_small_terms() {
    let (mut failures, mut slips) = (Vec::new(), 0);
    for u in enumerate(if cfg!(debug_assertions) { 6 } else { 8 }) {
      check_canon(&u, 3, true, &mut failures, &mut slips);
      if failures.len() >= 12 {
        break;
      }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
  }
}
