//! Builds a reference graph from a Lean environment.
//!
//! The graph tracks which constants reference which other constants, maintaining
//! both forward (`out_refs`) and reverse (`in_refs`) edges. This is used to
//! compute SCCs (strongly connected components) for mutual block detection.
//! Construction is parallelized via rayon.

use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::hash_map::Entry;

use ix_common::env::{ConstantInfo, Env, Expr, ExprData, Name, NameData};

/// A set of [`Name`]s, used to represent the neighbors of a node in the reference graph.
pub type NameSet = FxHashSet<Name>;

/// Absorbs the elements of the smaller [`NameSet`] into the bigger one and returns
/// the merged set.
pub fn merge_name_sets(mut a: NameSet, mut b: NameSet) -> NameSet {
  if a.len() < b.len() {
    b.extend(a);
    b
  } else {
    a.extend(b);
    a
  }
}

/// Maps each [`Name`] to the set of [`Name`]s it is associated with.
pub type RefMap = FxHashMap<Name, NameSet>;

/// A bidirectional reference graph over [`Name`]s, storing both forward and reverse edges.
/// ```ignored
/// A ──> B ──> C <── D ──> E
/// out_refs: [(A, [B]), (B, [C]), (C, []), (D, [C, E]), (E, [])]
/// in_refs:  [(A, []), (B, [A]), (C, [B, D]), (D, []), (E, [D])]
/// ```
#[derive(Default)]
pub struct RefGraph {
  /// Maps names to the names they reference
  pub out_refs: RefMap,
  /// Maps names to the names that reference them
  pub in_refs: RefMap,
}

/// Builds a [`RefGraph`] from a Lean [`Env`] by collecting all constant references in parallel.
///
/// For each constant, extracts the set of names it references (from types, values, constructors,
/// and recursor rules), then assembles both the forward and reverse edge maps.
/// Everything the compile-env setup needs from a whole-env pass: the
/// reference graph, the immediately-ungrounded set (before transitive
/// proliferation), and the inductive mutual-block groups
/// (`all[0] → all`, for flag validation).
pub struct SetupScan {
  pub graph: RefGraph,
  pub immediate_ungrounded: FxHashMap<Name, crate::ground::GroundError>,
  pub ind_groups: FxHashMap<Name, Vec<Name>>,
  /// Source contracts that the current conservative emitter cannot preserve.
  pub source_contracts: Vec<Name>,
  /// Semantic declarations validated during the same lazy decode as the graph.
  pub semantic_sources: Result<Vec<Name>, ixon::CompileError>,
}

/// Fused whole-env setup pass: one decode per constant feeding the ref
/// graph, the groundedness check, and inductive-group collection.
/// The compile path's lazy environment can decode a constant on each
/// access, so one scan avoids the repeat decodes of separate graph,
/// grounding, and inductive-group scans. Outputs match those passes.
///
/// Fold directly into chunk-local maps instead of allocating and merging
/// graph fragments for every constant. Reverse edges to a common dependency
/// share one set within the chunk; only completed chunk maps are reduced.
/// Rayon chooses the chunks dynamically, retaining work-stealing balance
/// when some constants take much longer to decode and traverse than others.
pub fn setup_scan(env: &Env) -> SetupScan {
  #[derive(Default)]
  struct Acc {
    out_refs: RefMap,
    in_refs: RefMap,
    ungrounded: FxHashMap<Name, crate::ground::GroundError>,
    ind_groups: FxHashMap<Name, Vec<Name>>,
    source_contracts: Vec<Name>,
    semantic_sources: Vec<Name>,
    semantic_error: Option<ixon::CompileError>,
  }

  let names: Vec<&Name> = env.keys().collect();
  let acc = names
    .into_par_iter()
    .fold(Acc::default, |mut acc, name| {
      let Some(constant) = env.get(name) else {
        return acc;
      };
      match crate::semantic_contract::inspect_constant(&constant) {
        Ok(true) => acc.semantic_sources.push(name.clone()),
        Ok(false) => {},
        Err(error) => acc.semantic_error = Some(error),
      }
      let (deps, annotated) = inspect_constant_references(&constant);
      if annotated {
        acc.source_contracts.push(name.clone());
      }
      // Keep an empty reverse-edge entry even for an isolated constant.
      // Missing referenced names also retain their incoming edges, as in
      // the reference graph used by ungroundedness propagation.
      acc.in_refs.entry(name.clone()).or_default();
      for dep in &deps {
        acc.in_refs.entry(dep.clone()).or_default().insert(name.clone());
      }
      acc.out_refs.insert(name.clone(), deps);
      if let Err(err) = crate::ground::ground_const_check(&constant, env) {
        acc.ungrounded.insert(name.clone(), err);
      }
      // Members of one mutual family share the same `all`, so
      // first-wins insertion is value-identical regardless of which
      // member lands first.
      if let ConstantInfo::InductInfo(v) = &*constant
        && let Some(first) = v.all.first()
      {
        acc.ind_groups.entry(first.clone()).or_insert_with(|| v.all.clone());
      }
      acc
    })
    .reduce(Acc::default, |mut l, r| {
      l.out_refs = merge_ref_maps(l.out_refs, r.out_refs);
      l.in_refs = merge_ref_maps(l.in_refs, r.in_refs);
      l.ungrounded.extend(r.ungrounded);
      l.source_contracts.extend(r.source_contracts);
      l.semantic_sources.extend(r.semantic_sources);
      l.semantic_error = l.semantic_error.or(r.semantic_error);
      for (k, v) in r.ind_groups {
        l.ind_groups.entry(k).or_insert(v);
      }
      l
    });

  SetupScan {
    graph: RefGraph { out_refs: acc.out_refs, in_refs: acc.in_refs },
    immediate_ungrounded: acc.ungrounded,
    ind_groups: acc.ind_groups,
    source_contracts: acc.source_contracts,
    semantic_sources: match acc.semantic_error {
      Some(error) => Err(error),
      None => Ok(acc.semantic_sources),
    },
  }
}

/// What the setup scan records for one constant: the inputs of every
/// [`SetupScan`] field that constant contributes to.
pub struct ConstScan {
  /// Names the constant references (its `out_refs` entry).
  pub deps: NameSet,
  /// Whether some `Mdata` key lies in the reserved source-contract
  /// namespace (see [`is_source_contract_key`]).
  pub source_contract: bool,
  /// [`crate::semantic_contract::inspect_constant`]'s result.
  pub semantic: Result<bool, Box<ixon::CompileError>>,
  /// [`crate::ground::ground_const_check`]'s result.
  pub ground: Result<(), Box<crate::ground::GroundError>>,
  /// `(all[0], all)` for an inductive with a non-empty `all`.
  pub ind_group: Option<(Name, Vec<Name>)>,
}

/// The reference per-constant scan over a decoded constant: the same
/// three walks and the same inductive-group entry as [`setup_scan`].
pub fn scan_constant(constant: &ConstantInfo, env: &Env) -> ConstScan {
  let semantic =
    crate::semantic_contract::inspect_constant(constant).map_err(Box::new);
  let (deps, source_contract) = inspect_constant_references(constant);
  let ground =
    crate::ground::ground_const_check(constant, env).map_err(Box::new);
  let ind_group = match constant {
    ConstantInfo::InductInfo(v) => {
      v.all.first().map(|first| (first.clone(), v.all.clone()))
    },
    _ => None,
  };
  ConstScan { deps, source_contract, semantic, ground, ind_group }
}

/// Produces each constant's [`ConstScan`] for [`setup_scan_with`].
/// An implementation may read the constant from wherever it lives (the
/// ffi crate walks the Lean objects without decoding them), but its
/// results must equal [`scan_constant`] on the decoded constant.
pub trait ConstScanner: Sync {
  /// `None` exactly when `env.get(name)` is `None`.
  fn scan(&self, name: &Name, env: &Env) -> Option<ConstScan>;

  /// The setup scan is over: release what only the scan needed.
  fn release(&self) {}
}

/// [`ConstScanner`] over the decoded environment.
pub struct DecodedScanner;

impl ConstScanner for DecodedScanner {
  fn scan(&self, name: &Name, env: &Env) -> Option<ConstScan> {
    let constant = env.get(name)?;
    Some(scan_constant(&constant, env))
  }
}

/// [`setup_scan`] with a pluggable per-constant scan.
///
/// The outputs equal [`setup_scan`]'s whenever `scanner` agrees with
/// [`scan_constant`]: the reference graph, the immediately-ungrounded
/// set, `ind_groups` (first `all[0]` in key order wins), and
/// `source_contracts`/`semantic_sources` in `env.keys()` order, which is
/// the order rayon's order-preserving fold/reduce gives the old pass.
/// With several semantic errors the old pass reported the last error of
/// the leftmost fold chunk that had one, which depends on how rayon
/// split the work; this pass reports the first in key order, the result
/// the old pass gives when every chunk holds one constant.
///
/// The scans are collected per constant, then the maps are assembled:
/// `in_refs` by a parallel group-by on the dependency, with no serial
/// merge of per-thread maps.
pub fn setup_scan_with(env: &Env, scanner: &dyn ConstScanner) -> SetupScan {
  let start = std::time::Instant::now();
  let names: Vec<&Name> = env.keys().collect();
  let mut scans: Vec<Option<ConstScan>> =
    names.par_iter().map(|name| scanner.scan(name, env)).collect();
  let scanned = start.elapsed();

  let mut immediate_ungrounded = FxHashMap::default();
  let mut ind_groups: FxHashMap<Name, Vec<Name>> = FxHashMap::default();
  let mut source_contracts = Vec::new();
  let mut semantic_sources = Vec::new();
  let mut semantic_error = None;
  for (name, scan) in names.iter().zip(scans.iter_mut()) {
    let Some(scan) = scan else {
      continue;
    };
    match std::mem::replace(&mut scan.semantic, Ok(false)) {
      Ok(true) => semantic_sources.push((*name).clone()),
      Ok(false) => {},
      Err(error) => {
        semantic_error.get_or_insert(*error);
      },
    }
    if scan.source_contract {
      source_contracts.push((*name).clone());
    }
    if let Err(error) = std::mem::replace(&mut scan.ground, Ok(())) {
      immediate_ungrounded.insert((*name).clone(), *error);
    }
    if let Some((first, all)) = scan.ind_group.take() {
      ind_groups.entry(first).or_insert(all);
    }
  }

  let collected = start.elapsed();
  let in_refs = build_in_refs(&names, &scans);
  let grouped = start.elapsed();
  let mut out_refs = RefMap::with_capacity_and_hasher(
    scans.iter().filter(|scan| scan.is_some()).count(),
    Default::default(),
  );
  for (name, scan) in names.iter().zip(scans) {
    if let Some(scan) = scan {
      out_refs.insert((*name).clone(), scan.deps);
    }
  }
  if *crate::compile::IX_VERBOSE {
    eprintln!(
      "[compile_env] setup_scan phases: per-constant scans {:.2}s, \
       collect {:.2}s, in_refs {:.2}s, out_refs {:.2}s",
      scanned.as_secs_f32(),
      (collected - scanned).as_secs_f32(),
      (grouped - collected).as_secs_f32(),
      (start.elapsed() - grouped).as_secs_f32(),
    );
  }

  SetupScan {
    graph: RefGraph { out_refs, in_refs },
    immediate_ungrounded,
    ind_groups,
    source_contracts,
    semantic_sources: match semantic_error {
      Some(error) => Err(error),
      None => Ok(semantic_sources),
    },
  }
}

/// Reverse edges of the scanned constants, grouped in parallel.
///
/// Every scanned constant gets an entry (empty when nothing references
/// it), and so does every referenced name, present in the environment
/// or not. Edges are first bucketed by a shard of the dependency's
/// digest, chunk by chunk; then each shard builds its own map; the
/// shards hold disjoint keys, so the final union only moves entries.
fn build_in_refs(names: &[&Name], scans: &[Option<ConstScan>]) -> RefMap {
  const SHARDS: usize = 256;
  // The digest is uniform. The keys of one shard share this byte; each
  // shard's map hashes the whole digest.
  fn shard(name: &Name) -> usize {
    usize::from(name.get_hash().as_bytes()[31]) % SHARDS
  }
  // `u32::MAX` as the source marks the constant's own (possibly empty)
  // entry.
  const SELF: u32 = u32::MAX;
  assert!(names.len() < SELF as usize, "setup scan: too many constants");
  let chunk_len =
    names.len().div_ceil(rayon::current_num_threads() * 8).max(1024);
  let parts: Vec<Vec<Vec<(&Name, u32)>>> = scans
    .par_chunks(chunk_len)
    .enumerate()
    .map(|(chunk, scans)| {
      let mut out: Vec<Vec<(&Name, u32)>> = vec![Vec::new(); SHARDS];
      for (offset, scan) in scans.iter().enumerate() {
        let Some(scan) = scan else {
          continue;
        };
        let src = chunk * chunk_len + offset;
        let name = names[src];
        // `src < names.len() < u32::MAX`, checked above.
        #[allow(clippy::cast_possible_truncation)]
        let src = src as u32;
        out[shard(name)].push((name, SELF));
        for dep in &scan.deps {
          out[shard(dep)].push((dep, src));
        }
      }
      out
    })
    .collect();
  let t_parts = std::time::Instant::now();
  let shards: Vec<RefMap> = (0..SHARDS)
    .into_par_iter()
    .map(|shard| {
      let mut map = RefMap::default();
      // Start each shard at a different chunk, so that concurrent shards
      // do not clone the same source names at the same time.
      let start = shard * parts.len() / SHARDS;
      for part in parts[start..].iter().chain(&parts[..start]) {
        for &(dep, src) in &part[shard] {
          let src = (src != SELF).then(|| names[src as usize].clone());
          // Clone the key only when it is new.
          if let Some(set) = map.get_mut(dep) {
            set.extend(src);
          } else {
            map.insert(dep.clone(), src.into_iter().collect());
          }
        }
      }
      map
    })
    .collect();
  let t_shards = std::time::Instant::now();
  drop(parts);
  let t_drop = std::time::Instant::now();
  let mut in_refs = RefMap::with_capacity_and_hasher(
    shards.iter().map(RefMap::len).sum(),
    Default::default(),
  );
  for map in shards {
    in_refs.extend(map);
  }
  if *crate::compile::IX_VERBOSE {
    eprintln!(
      "[compile_env] in_refs: shards {:.3}s, drop {:.3}s, union {:.3}s",
      (t_shards - t_parts).as_secs_f32(),
      (t_drop - t_shards).as_secs_f32(),
      t_drop.elapsed().as_secs_f32()
    );
  }
  in_refs
}

/// Compare two setup scans field by field: the reference graph (both
/// directions), the immediately-ungrounded set with each error's
/// `Debug` rendering, `ind_groups`, `source_contracts` and
/// `semantic_sources` (in order; an error by its `Debug` rendering).
/// Returns a description of the first difference.
pub fn compare_setup_scans(
  actual: &SetupScan,
  expected: &SetupScan,
) -> Result<(), String> {
  fn compare_maps(
    what: &str,
    actual: &RefMap,
    expected: &RefMap,
  ) -> Result<(), String> {
    if actual.len() != expected.len() {
      return Err(format!(
        "{what}: {} entries, expected {}",
        actual.len(),
        expected.len()
      ));
    }
    for (name, set) in expected {
      match actual.get(name) {
        None => return Err(format!("{what}: no entry for {}", name.pretty())),
        Some(other) if other != set => {
          return Err(format!(
            "{what}: entry for {} has {} names, expected {}",
            name.pretty(),
            other.len(),
            set.len()
          ));
        },
        Some(_) => {},
      }
    }
    Ok(())
  }
  compare_maps("out_refs", &actual.graph.out_refs, &expected.graph.out_refs)?;
  compare_maps("in_refs", &actual.graph.in_refs, &expected.graph.in_refs)?;
  if actual.immediate_ungrounded.len() != expected.immediate_ungrounded.len() {
    return Err(format!(
      "immediate_ungrounded: {} entries, expected {}",
      actual.immediate_ungrounded.len(),
      expected.immediate_ungrounded.len()
    ));
  }
  for (name, error) in &expected.immediate_ungrounded {
    let expected = format!("{error:?}");
    match actual.immediate_ungrounded.get(name) {
      Some(other) if format!("{other:?}") == expected => {},
      other => {
        return Err(format!(
          "immediate_ungrounded: {} is {other:?}, expected {expected}",
          name.pretty()
        ));
      },
    }
  }
  if actual.ind_groups != expected.ind_groups {
    return Err(format!(
      "ind_groups differ ({} vs {} groups)",
      actual.ind_groups.len(),
      expected.ind_groups.len()
    ));
  }
  if actual.source_contracts != expected.source_contracts {
    return Err(format!(
      "source_contracts differ ({} vs {} names)",
      actual.source_contracts.len(),
      expected.source_contracts.len()
    ));
  }
  match (&actual.semantic_sources, &expected.semantic_sources) {
    (Ok(a), Ok(b)) if a == b => Ok(()),
    (Err(a), Err(b)) if format!("{a:?}") == format!("{b:?}") => Ok(()),
    (a, b) => Err(format!(
      "semantic_sources differ: {:?} vs {:?}",
      a.as_ref().map(Vec::len),
      b.as_ref().map(Vec::len)
    )),
  }
}

/// Compare two per-constant scans, as [`compare_setup_scans`] does.
pub fn compare_const_scans(
  actual: &ConstScan,
  expected: &ConstScan,
) -> Result<(), String> {
  if actual.deps != expected.deps {
    return Err(format!(
      "deps: {} names, expected {}",
      actual.deps.len(),
      expected.deps.len()
    ));
  }
  if actual.source_contract != expected.source_contract {
    return Err(format!(
      "source_contract: {}, expected {}",
      actual.source_contract, expected.source_contract
    ));
  }
  let semantic = |s: &Result<bool, Box<ixon::CompileError>>| format!("{s:?}");
  if semantic(&actual.semantic) != semantic(&expected.semantic) {
    return Err(format!(
      "semantic: {}, expected {}",
      semantic(&actual.semantic),
      semantic(&expected.semantic)
    ));
  }
  let ground =
    |g: &Result<(), Box<crate::ground::GroundError>>| format!("{g:?}");
  if ground(&actual.ground) != ground(&expected.ground) {
    return Err(format!(
      "ground: {}, expected {}",
      ground(&actual.ground),
      ground(&expected.ground)
    ));
  }
  if actual.ind_group != expected.ind_group {
    return Err("ind_group differs".into());
  }
  Ok(())
}

/// Size-aware map union (drain the smaller side into the bigger).
fn merge_ref_maps(l: RefMap, r: RefMap) -> RefMap {
  let (smaller, mut bigger) = if l.len() < r.len() { (l, r) } else { (r, l) };
  for (name, set) in smaller {
    match bigger.entry(name) {
      Entry::Vacant(entry) => {
        entry.insert(set);
      },
      Entry::Occupied(mut entry) => {
        entry.get_mut().extend(set);
      },
    }
  }
  bigger
}

pub fn build_ref_graph(env: &Env) -> RefGraph {
  let mk_in_refs = |name: &Name, deps: &NameSet| -> RefMap {
    let mut in_refs = RefMap::from_iter([(name.clone(), NameSet::default())]);
    for dep in deps {
      match in_refs.entry(dep.clone()) {
        Entry::Vacant(entry) => {
          entry.insert(NameSet::from_iter([name.clone()]));
        },
        Entry::Occupied(mut entry) => {
          entry.get_mut().insert(name.clone());
        },
      }
    }
    in_refs
  };

  let merge = |l: RefMap, r: RefMap| -> RefMap {
    let (smaller, mut bigger) = if l.len() < r.len() { (l, r) } else { (r, l) };
    for (name, set) in smaller {
      match bigger.entry(name) {
        Entry::Vacant(entry) => {
          entry.insert(set);
        },
        Entry::Occupied(mut entry) => {
          entry.get_mut().extend(set);
        },
      }
    }
    bigger
  };

  let names: Vec<&Name> = env.keys().collect();
  let (out_refs, in_refs) = names
    .into_par_iter()
    .filter_map(|name| {
      let constant = env.get(name)?;
      let deps = get_constant_info_references(&constant);
      let in_refs = mk_in_refs(name, &deps);
      let out_refs = RefMap::from_iter([(name.clone(), deps)]);
      Some((out_refs, in_refs))
    })
    .reduce(
      || (RefMap::default(), RefMap::default()),
      |(out_l, in_l), (out_r, in_r)| (merge(out_l, out_r), merge(in_l, in_r)),
    );

  //assert_eq!(env.len(), out_refs.len());
  //assert_eq!(out_refs.len(), in_refs.len());
  RefGraph { out_refs, in_refs }
}

pub fn get_constant_info_references(constant_info: &ConstantInfo) -> NameSet {
  inspect_constant_references(constant_info).0
}

fn inspect_constant_references(
  constant_info: &ConstantInfo,
) -> (NameSet, bool) {
  let mut acc = NameSet::default();
  let mut visited: FxHashSet<&Expr> = FxHashSet::default();
  let mut annotated = false;
  match constant_info {
    ConstantInfo::AxiomInfo(val) => {
      annotated |=
        collect_expr_references(&val.cnst.typ, &mut visited, &mut acc);
    },
    ConstantInfo::DefnInfo(val) => {
      annotated |=
        collect_expr_references(&val.cnst.typ, &mut visited, &mut acc);
      annotated |= collect_expr_references(&val.value, &mut visited, &mut acc);
    },
    ConstantInfo::ThmInfo(val) => {
      annotated |=
        collect_expr_references(&val.cnst.typ, &mut visited, &mut acc);
      annotated |= collect_expr_references(&val.value, &mut visited, &mut acc);
    },
    ConstantInfo::OpaqueInfo(val) => {
      annotated |=
        collect_expr_references(&val.cnst.typ, &mut visited, &mut acc);
      annotated |= collect_expr_references(&val.value, &mut visited, &mut acc);
    },
    ConstantInfo::QuotInfo(val) => {
      annotated |=
        collect_expr_references(&val.cnst.typ, &mut visited, &mut acc);
    },
    ConstantInfo::InductInfo(val) => {
      annotated |=
        collect_expr_references(&val.cnst.typ, &mut visited, &mut acc);
      acc.extend(val.ctors.iter().cloned());
    },
    ConstantInfo::CtorInfo(val) => {
      annotated |=
        collect_expr_references(&val.cnst.typ, &mut visited, &mut acc);
      acc.insert(val.induct.clone());
    },
    ConstantInfo::RecInfo(val) => {
      annotated |=
        collect_expr_references(&val.cnst.typ, &mut visited, &mut acc);
      for rule in &val.rules {
        acc.insert(rule.ctor.clone());
        annotated |= collect_expr_references(&rule.rhs, &mut visited, &mut acc);
      }
    },
  }
  (acc, annotated)
}

/// Match the reserved Lean metadata namespace by components, without allocating
/// strings or relying on a hash match. This also catches malformed markers.
pub fn is_source_contract_key(mut key: &Name) -> bool {
  loop {
    if let NameData::Str(source_parent, binder, _) = key.as_data()
      && binder == "binder"
      && let NameData::Str(ix_parent, source, _) = source_parent.as_data()
      && source == "source"
      && let NameData::Str(root, ix, _) = ix_parent.as_data()
      && ix == "ix"
      && matches!(root.as_data(), NameData::Anonymous(_))
    {
      return true;
    }
    match key.as_data() {
      NameData::Str(parent, ..) | NameData::Num(parent, ..) => key = parent,
      NameData::Anonymous(_) => return false,
    }
  }
}

/// Iterative DAG walk pushing every `Const`/`Proj` head into one shared
/// accumulator. `visited` keys on `Expr`'s digest-backed `Hash`/`Eq`
/// (Arc pointer fast path), so each distinct subterm — structurally
/// shared or not — is expanded once, exactly the dedup the old
/// per-constant memo provided. Θ(n + r) total: the old walk returned a
/// fresh `NameSet` per node and merged/cloned it into every parent
/// (Θ(n·r) allocations on ref-heavy constants). This feeds both
/// compile's `setup_scan` and decompile's Pass-2 ingress BFS. The
/// accumulated set is value-identical to the old result; no downstream
/// consumer reads set iteration order into output bytes (SCC members
/// and serialized sections are canonically re-sorted).
fn collect_expr_references<'a>(
  expr: &'a Expr,
  visited: &mut FxHashSet<&'a Expr>,
  acc: &mut NameSet,
) -> bool {
  let mut annotated = false;
  let mut stack: Vec<&'a Expr> = vec![expr];
  while let Some(e) = stack.pop() {
    if !visited.insert(e) {
      continue;
    }
    match e.as_data() {
      ExprData::Const(name, ..) => {
        acc.insert(name.clone());
      },
      ExprData::App(f, a, _) => {
        stack.push(f);
        stack.push(a);
      },
      ExprData::Lam(_, typ, body, ..) | ExprData::ForallE(_, typ, body, ..) => {
        stack.push(typ);
        stack.push(body);
      },
      ExprData::LetE(_, typ, value, body, ..) => {
        stack.push(typ);
        stack.push(value);
        stack.push(body);
      },
      ExprData::Mdata(data, inner, _) => {
        annotated |= data.iter().any(|(key, _)| is_source_contract_key(key));
        stack.push(inner);
      },
      ExprData::Proj(type_name, _, inner, _) => {
        acc.insert(type_name.clone());
        stack.push(inner);
      },
      _ => {},
    }
  }
  annotated
}

#[cfg(test)]
mod tests {
  use super::*;
  use bignat::Nat;
  use ix_common::env::*;

  fn n(s: &str) -> Name {
    Name::str(Name::anon(), s.to_string())
  }

  fn sort0() -> Expr {
    Expr::sort(Level::zero())
  }

  fn mk_cv(name: &str) -> ConstantVal {
    ConstantVal { name: n(name), level_params: vec![], typ: sort0() }
  }

  fn source_key() -> Name {
    ["ix", "source", "binder"]
      .into_iter()
      .fold(Name::anon(), |parent, part| Name::str(parent, part.to_owned()))
  }

  #[test]
  fn source_contract_namespace_is_structural() {
    let key = source_key();
    assert!(is_source_contract_key(&key));
    assert!(is_source_contract_key(&Name::str(key.clone(), "owned".into())));
    assert!(is_source_contract_key(&Name::num(key, Nat::from(1u64))));
    assert!(!is_source_contract_key(&n("ix.source.binder")));
    assert!(!is_source_contract_key(&n("borrowed")));
    assert!(!is_source_contract_key(&Name::str(
      Name::str(n("ix"), "source".into()),
      "binders".into()
    )));
  }

  #[test]
  fn source_contract_environment_rejects_before_emission() {
    use crate::compile::{CompileOptions, compile_env_with_options};
    use std::sync::Arc;

    let mut env = Env::default();
    for name in ["ZAnnotated", "AAnnotated"] {
      env.insert(
        n(name),
        ConstantInfo::AxiomInfo(AxiomVal {
          cnst: ConstantVal {
            name: n(name),
            level_params: vec![],
            // Even malformed markers must not be discarded as presentation data.
            typ: Expr::mdata(
              vec![(source_key(), DataValue::OfBool(true))],
              sort0(),
            ),
          },
          is_unsafe: false,
        }),
      );
    }
    let env = Arc::new(env);
    for workers in [1, 4] {
      let pool =
        rayon::ThreadPoolBuilder::new().num_threads(workers).build().unwrap();
      let result = pool
        .install(|| compile_env_with_options(&env, CompileOptions::default()));
      assert!(
        matches!(result, Err(ixon::CompileError::UnsupportedExpr { desc })
        if desc == "unresolved source binder contracts: AAnnotated")
      );
    }
  }

  #[test]
  fn source_contract_scan_covers_declaration_bodies() {
    let mut env = Env::default();
    let name = n("BodyMarker");
    env.insert(
      name.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::succ(Level::zero())),
        },
        value: Expr::mdata(
          vec![(source_key(), DataValue::OfBool(true))],
          sort0(),
        ),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name.clone()],
      }),
    );
    assert_eq!(setup_scan(&env).source_contracts, vec![name]);
  }

  #[test]
  fn setup_scan_preserves_semantic_validation() {
    use crate::semantic_contract::{Contract, Kind};
    use ixon::contract::{BinderContract, LetKind, ValueContract};
    let contract = Contract {
      kind: Kind::All,
      binder: BinderContract::default(),
      result: ValueContract::shared(),
      let_kind: LetKind::Value,
    };
    let name = n("Semantic");
    let mut env = Env::default();
    let axiom = |typ| {
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal { name: name.clone(), level_params: vec![], typ },
        is_unsafe: false,
      })
    };
    env.insert(
      name.clone(),
      axiom(contract.attach(Expr::all(
        n("x"),
        sort0(),
        sort0(),
        BinderInfo::Default,
      ))),
    );
    assert_eq!(setup_scan(&env).semantic_sources.unwrap(), vec![name.clone()]);
    // A well-formed frame attached to the wrong expression must still fail
    // before compilation, even though validation now shares the graph decode.
    env.insert(name.clone(), axiom(contract.attach(sort0())));
    assert!(setup_scan(&env).semantic_sources.is_err());
  }

  #[test]
  fn source_contract_guard_preserves_native_borrow_metadata() {
    use crate::compile::{CompileOptions, compile_env_with_options};
    use std::sync::Arc;

    let name = n("Ordinary");
    let compile = |borrowed: bool| {
      let mut env = Env::default();
      let domain = if borrowed {
        Expr::mdata(vec![(n("borrowed"), DataValue::OfBool(true))], sort0())
      } else {
        sort0()
      };
      env.insert(
        name.clone(),
        ConstantInfo::AxiomInfo(AxiomVal {
          cnst: ConstantVal {
            name: name.clone(),
            level_params: vec![],
            typ: Expr::all(n("x"), domain, sort0(), BinderInfo::Default),
          },
          is_unsafe: false,
        }),
      );
      assert!(setup_scan(&env).source_contracts.is_empty());
      let result =
        compile_env_with_options(&Arc::new(env), CompileOptions::default())
          .unwrap();
      result.name_to_addr.get(&name).unwrap().value().clone()
    };
    assert_eq!(compile(false), compile(true));
  }

  /// Frozen per-constant map/reduce implementation for differential tests
  /// and the opt-in performance comparison below.
  fn setup_scan_reference(env: &Env) -> SetupScan {
    let empty = || SetupScan {
      graph: RefGraph::default(),
      immediate_ungrounded: FxHashMap::default(),
      ind_groups: FxHashMap::default(),
      source_contracts: Vec::new(),
      semantic_sources: Ok(Vec::new()),
    };
    let names: Vec<_> = env.keys().collect();
    names
      .into_par_iter()
      .filter_map(|name| {
        let constant = env.get(name)?;
        let deps = get_constant_info_references(&constant);
        let mut scan = empty();
        scan.graph.in_refs =
          RefMap::from_iter([(name.clone(), NameSet::default())]);
        for dep in &deps {
          match scan.graph.in_refs.entry(dep.clone()) {
            Entry::Vacant(entry) => {
              entry.insert(NameSet::from_iter([name.clone()]));
            },
            Entry::Occupied(mut entry) => {
              entry.get_mut().insert(name.clone());
            },
          }
        }
        scan.graph.out_refs = RefMap::from_iter([(name.clone(), deps)]);
        if let Err(err) = crate::ground::ground_const_check(&constant, env) {
          scan.immediate_ungrounded.insert(name.clone(), err);
        }
        if let ConstantInfo::InductInfo(v) = &*constant
          && let Some(first) = v.all.first()
        {
          scan.ind_groups.insert(first.clone(), v.all.clone());
        }
        Some(scan)
      })
      .reduce(empty, |mut l, r| {
        l.graph.out_refs = merge_ref_maps(l.graph.out_refs, r.graph.out_refs);
        l.graph.in_refs = merge_ref_maps(l.graph.in_refs, r.graph.in_refs);
        l.immediate_ungrounded.extend(r.immediate_ungrounded);
        for (k, v) in r.ind_groups {
          l.ind_groups.entry(k).or_insert(v);
        }
        l
      })
  }

  fn assert_same_scan(actual: &SetupScan, expected: &SetupScan) {
    assert_eq!(actual.graph.out_refs, expected.graph.out_refs);
    assert_eq!(actual.graph.in_refs, expected.graph.in_refs);
    assert_eq!(actual.ind_groups, expected.ind_groups);
    assert_eq!(actual.source_contracts, expected.source_contracts);
    assert_eq!(
      actual.immediate_ungrounded.len(),
      expected.immediate_ungrounded.len()
    );
    for (name, expected) in &expected.immediate_ungrounded {
      assert_eq!(
        format!("{:?}", actual.immediate_ungrounded.get(name).unwrap()),
        format!("{expected:?}"),
        "grounding error for {name}",
      );
    }
  }

  /// Well-typed aliases with both shared and local dependencies. The input
  /// graph has no cycles, while many reverse edges meet at the same names.
  fn setup_fixture(count: usize) -> Env {
    let mut env = Env::default();
    let typ = Expr::sort(Level::succ(Level::zero()));
    for name in ["Base", "Isolated"] {
      env.insert(
        n(name),
        ConstantInfo::AxiomInfo(AxiomVal {
          cnst: ConstantVal {
            name: n(name),
            level_params: vec![],
            typ: typ.clone(),
          },
          is_unsafe: false,
        }),
      );
    }
    let names: Vec<_> = (0..count).map(|i| n(&format!("alias_{i}"))).collect();
    let base = Expr::cnst(n("Base"), vec![]);
    for (i, name) in names.iter().enumerate() {
      let mut value = base.clone();
      for offset in [1, 3, 17, 127] {
        let dep =
          i.checked_sub(offset).map_or_else(|| n("Base"), |j| names[j].clone());
        value = Expr::all(
          Name::anon(),
          Expr::cnst(dep, vec![]),
          value,
          BinderInfo::Default,
        );
      }
      env.insert(
        name.clone(),
        ConstantInfo::DefnInfo(DefinitionVal {
          cnst: ConstantVal {
            name: name.clone(),
            level_params: vec![],
            typ: typ.clone(),
          },
          value,
          hints: ReducibilityHints::Abbrev,
          safety: DefinitionSafety::Safe,
          all: vec![name.clone()],
        }),
      );
    }
    env
  }

  #[test]
  fn setup_scan_matches_reference_across_worker_counts() {
    let mut env = setup_fixture(1024);
    // Cover isolated nodes, self/cyclic edges, missing names, each family of
    // grounding error, and mutual-group deduplication across fold chunks.
    for (name, typ) in [
      ("Self", Expr::cnst(n("Self"), vec![])),
      ("CycleA", Expr::cnst(n("CycleB"), vec![])),
      ("CycleB", Expr::cnst(n("CycleA"), vec![])),
      ("Missing", Expr::cnst(n("Absent"), vec![])),
      ("Bvar", Expr::bvar(Nat::from(0u64))),
      ("Fvar", Expr::fvar(n("local"))),
      ("Mvar", Expr::mvar(n("hole"))),
      ("Universe", Expr::sort(Level::param(n("u")))),
    ] {
      env.insert(
        n(name),
        ConstantInfo::AxiomInfo(AxiomVal {
          cnst: ConstantVal { name: n(name), level_params: vec![], typ },
          is_unsafe: false,
        }),
      );
    }
    for (name, all, ctors) in [
      ("MutA", vec![n("MutA"), n("MutB")], vec![]),
      ("MutB", vec![n("MutA"), n("MutB")], vec![]),
      ("EmptyGroup", vec![], vec![]),
      ("BadCtor", vec![n("BadCtor")], vec![n("AbsentCtor")]),
    ] {
      env.insert(
        n(name),
        ConstantInfo::InductInfo(InductiveVal {
          cnst: mk_cv(name),
          num_params: Nat::from(0u64),
          num_indices: Nat::from(0u64),
          all,
          ctors,
          num_nested: Nat::from(0u64),
          is_rec: false,
          is_unsafe: false,
          is_reflexive: false,
        }),
      );
    }
    let expected = setup_scan_reference(&env);
    assert_eq!(expected.immediate_ungrounded.len(), 6);
    assert!(expected.graph.in_refs[&n("Isolated")].is_empty());
    assert_eq!(expected.ind_groups.len(), 2);
    let graph = build_ref_graph(&env);
    assert_eq!(expected.graph.out_refs, graph.out_refs);
    assert_eq!(expected.graph.in_refs, graph.in_refs);
    for workers in [1, 2, 4, 8] {
      let pool =
        rayon::ThreadPoolBuilder::new().num_threads(workers).build().unwrap();
      pool.install(|| {
        let scan = setup_scan(&env);
        assert_same_scan(&scan, &expected);
        let assembled = setup_scan_with(&env, &DecodedScanner);
        assert_same_scan(&assembled, &expected);
        compare_setup_scans(&assembled, &scan).unwrap();
        assert_same_scan(
          &setup_scan(&Env::default()),
          &setup_scan_reference(&Env::default()),
        );
        compare_setup_scans(
          &setup_scan_with(&Env::default(), &DecodedScanner),
          &setup_scan(&Env::default()),
        )
        .unwrap();
      });
    }
  }

  /// The assembled scan of a lazy environment whose name list repeats
  /// names (each fetch returns the same constant, as the ffi's handle map
  /// keeps one object per name) equals the fold's, including the order
  /// of `source_contracts` and `semantic_sources`.
  #[test]
  fn setup_scan_with_matches_fold_on_repeated_lazy_names() {
    use crate::semantic_contract::{Contract, Kind};
    use ixon::contract::{BinderContract, LetKind, ValueContract};
    use std::sync::Arc;
    let mut backing = setup_fixture(300);
    let contract = Contract {
      kind: Kind::All,
      binder: BinderContract::default(),
      result: ValueContract::shared(),
      let_kind: LetKind::Value,
    };
    for i in 0..40 {
      let name = n(&format!("semantic_{i}"));
      let typ = if i % 3 == 0 {
        Expr::mdata(vec![(source_key(), DataValue::OfBool(true))], sort0())
      } else {
        contract.attach(Expr::all(
          n("x"),
          sort0(),
          sort0(),
          BinderInfo::Default,
        ))
      };
      backing.insert(
        name.clone(),
        ConstantInfo::AxiomInfo(AxiomVal {
          cnst: ConstantVal { name, level_params: vec![], typ },
          is_unsafe: false,
        }),
      );
    }
    let mut names: Vec<_> = backing.keys().cloned().collect();
    names.sort();
    let repeated: Vec<_> = names.iter().step_by(7).cloned().collect();
    names.extend(repeated);
    names.push(n("Unavailable"));
    let backing = Arc::new(backing);
    let lazy = |names: Vec<Name>| {
      let backing = Arc::clone(&backing);
      Env::new_lazy(
        names,
        Box::new(move |name| backing.get(name).map(|entry| entry.cloned())),
        16,
      )
    };
    for workers in [1, 3, 8] {
      let pool =
        rayon::ThreadPoolBuilder::new().num_threads(workers).build().unwrap();
      pool.install(|| {
        let env = lazy(names.clone());
        let scan = setup_scan(&env);
        assert!(!scan.source_contracts.is_empty());
        assert!(scan.semantic_sources.as_ref().is_ok_and(|s| !s.is_empty()));
        compare_setup_scans(&setup_scan_with(&env, &DecodedScanner), &scan)
          .unwrap();
      });
    }
    // Exactly one semantic error: both report it.
    let mut broken = (*backing).clone();
    let name = n("semantic_1");
    broken.insert(
      name.clone(),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name,
          level_params: vec![],
          typ: contract.attach(sort0()),
        },
        is_unsafe: false,
      }),
    );
    let scan = setup_scan(&broken);
    assert!(scan.semantic_sources.is_err());
    compare_setup_scans(&setup_scan_with(&broken, &DecodedScanner), &scan)
      .unwrap();
  }

  /// `Env::key` returns the environment's own `Arc` for an equal name
  /// built separately, in both the eager and the lazy environment.
  #[test]
  fn env_key_returns_the_environments_own_name() {
    let backing = setup_fixture(4);
    let lazy =
      Env::new_lazy(backing.keys().cloned().collect(), Box::new(|_| None), 16);
    for env in [&backing, &lazy] {
      let fresh = n("alias_2");
      let key = env.key(&fresh).unwrap();
      assert_eq!(key, &fresh);
      assert!(!std::sync::Arc::ptr_eq(&key.0, &fresh.0));
      let own = env.keys().find(|k| *k == &fresh).unwrap();
      assert!(std::sync::Arc::ptr_eq(&key.0, &own.0));
      assert!(env.key(&n("absent")).is_none());
    }
  }

  #[test]
  fn setup_scan_fetches_each_lazy_entry_once_and_skips_unavailable_entries() {
    use std::sync::{
      Arc,
      atomic::{AtomicUsize, Ordering},
    };
    let backing = setup_fixture(256);
    let expected = setup_scan_reference(&backing);
    let mut names: Vec<_> = backing.keys().cloned().collect();
    names.push(n("Unavailable"));
    let calls = Arc::new(AtomicUsize::new(0));
    let counted = Arc::clone(&calls);
    let count = names.len();
    let env = Env::new_lazy(
      names,
      Box::new(move |name| {
        counted.fetch_add(1, Ordering::Relaxed);
        backing.get(name).map(|entry| entry.cloned())
      }),
      16,
    );
    assert_same_scan(&setup_scan(&env), &expected);
    assert_eq!(calls.load(Ordering::Relaxed), count);
  }

  #[test]
  fn setup_scan_preserves_compiled_fixture_bytes() {
    use crate::compile::{CompileOptions, compile_env_with_options};
    let source = std::sync::Arc::new(setup_fixture(32));
    for workers in [1, 4] {
      let compiled = compile_env_with_options(
        &source,
        CompileOptions { max_workers: Some(workers) },
      )
      .unwrap();
      assert!(compiled.ungrounded.is_empty());
      let mut bytes = Vec::new();
      compiled.env.put(&mut bytes).unwrap();
      // Ixon v4; both worker counts must preserve these bytes.
      assert_eq!(
        blake3::hash(&bytes).to_hex().as_str(),
        "ea6cf4ca0e86e8db054f872a11fc2115284a9638e7b67d697940e1d19555725e"
      );
    }
  }

  /// Run explicitly in release mode: cargo test -p ix-compile --release
  /// setup_scan_benchmark -- --ignored --nocapture --test-threads=1
  #[test]
  #[ignore = "synthetic setup-scan timing comparison; run in release mode"]
  fn setup_scan_benchmark() {
    use std::time::{Duration, Instant};
    for count in [50_000, 250_000] {
      let env = setup_fixture(count);
      for workers in [1, 8, 32] {
        let pool =
          rayon::ThreadPoolBuilder::new().num_threads(workers).build().unwrap();
        pool.install(|| {
          assert_same_scan(&setup_scan(&env), &setup_scan_reference(&env));
          let mut elapsed = [Duration::ZERO; 2];
          for trial in 0..6 {
            // Alternate order to reduce allocator/cache warmup bias. Exclude
            // destruction, which the compiler likewise performs after setup.
            for index in [trial % 2, 1 - trial % 2] {
              let start = Instant::now();
              let result = if index == 0 {
                setup_scan_reference(&env)
              } else {
                setup_scan(&env)
              };
              elapsed[index] += start.elapsed();
              std::hint::black_box(result);
            }
          }
          eprintln!(
            "setup_scan: {} constants, {workers} workers: per-constant {:.3}s, chunked {:.3}s ({:.2}x)",
            env.len(),
            elapsed[0].as_secs_f64() / 6.0,
            elapsed[1].as_secs_f64() / 6.0,
            elapsed[0].as_secs_f64() / elapsed[1].as_secs_f64()
          );
        });
      }
    }
  }

  #[test]
  fn empty_env() {
    let env = Env::default();
    let graph = build_ref_graph(&env);
    assert!(graph.out_refs.is_empty());
    assert!(graph.in_refs.is_empty());
  }

  #[test]
  fn axiom_no_deps() {
    // Axiom A : Sort 0 — references nothing
    let mut env = Env::default();
    env.insert(
      n("A"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("A"), is_unsafe: false }),
    );
    let graph = build_ref_graph(&env);
    assert!(graph.out_refs[&n("A")].is_empty());
    assert!(graph.in_refs[&n("A")].is_empty());
  }

  #[test]
  fn defn_with_const_refs() {
    // B : Sort 0, defn A : B := B
    // A's type refs B, A's value refs B
    let mut env = Env::default();
    env.insert(
      n("B"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("B"), is_unsafe: false }),
    );
    let b_ref = Expr::cnst(n("B"), vec![]);
    env.insert(
      n("A"),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: n("A"),
          level_params: vec![],
          typ: b_ref.clone(),
        },
        value: b_ref,
        hints: ReducibilityHints::Opaque,
        safety: DefinitionSafety::Safe,
        all: vec![n("A")],
      }),
    );
    let graph = build_ref_graph(&env);
    // A references B
    assert!(graph.out_refs[&n("A")].contains(&n("B")));
    // B is referenced by A
    assert!(graph.in_refs[&n("B")].contains(&n("A")));
    // B references nothing
    assert!(graph.out_refs[&n("B")].is_empty());
  }

  #[test]
  fn inductive_includes_ctors() {
    // Inductive T with constructors T.mk1, T.mk2
    let mut env = Env::default();
    env.insert(
      n("T"),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: mk_cv("T"),
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![n("T")],
        ctors: vec![n("T.mk1"), n("T.mk2")],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    // Add constructors to env so they can be referenced
    env.insert(
      n("T.mk1"),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: mk_cv("T.mk1"),
        induct: n("T"),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );
    env.insert(
      n("T.mk2"),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: mk_cv("T.mk2"),
        induct: n("T"),
        cidx: Nat::from(1u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );

    let graph = build_ref_graph(&env);
    // T references T.mk1 and T.mk2 (from ctors list)
    assert!(graph.out_refs[&n("T")].contains(&n("T.mk1")));
    assert!(graph.out_refs[&n("T")].contains(&n("T.mk2")));
  }

  #[test]
  fn inductive_all_members_are_not_graph_edges() {
    // `InductiveVal.all` is Lean source metadata. The canonical compiler
    // must still split inductive declarations into their minimal SCCs, so
    // members that do not structurally reference each other are not graph
    // dependencies merely because Lean recorded them in the same `all` list.
    let mut env = Env::default();
    for name in ["A", "B"] {
      env.insert(
        n(name),
        ConstantInfo::InductInfo(InductiveVal {
          cnst: mk_cv(name),
          num_params: Nat::from(0u64),
          num_indices: Nat::from(0u64),
          all: vec![n("A"), n("B")],
          ctors: vec![],
          num_nested: Nat::from(0u64),
          is_rec: false,
          is_unsafe: false,
          is_reflexive: false,
        }),
      );
    }

    let graph = build_ref_graph(&env);
    assert!(!graph.out_refs[&n("A")].contains(&n("B")));
    assert!(!graph.out_refs[&n("B")].contains(&n("A")));
  }

  #[test]
  fn ctor_includes_induct() {
    // Constructor T.mk references its parent T
    let mut env = Env::default();
    env.insert(
      n("T"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("T"), is_unsafe: false }),
    );
    env.insert(
      n("T.mk"),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: mk_cv("T.mk"),
        induct: n("T"),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );
    let graph = build_ref_graph(&env);
    assert!(graph.out_refs[&n("T.mk")].contains(&n("T")));
  }

  #[test]
  fn in_refs_bidirectional() {
    // A -> B, C -> B
    let mut env = Env::default();
    let b_ref = Expr::cnst(n("B"), vec![]);
    env.insert(
      n("B"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("B"), is_unsafe: false }),
    );
    env.insert(
      n("A"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: n("A"),
          level_params: vec![],
          typ: b_ref.clone(),
        },
        is_unsafe: false,
      }),
    );
    env.insert(
      n("C"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal { name: n("C"), level_params: vec![], typ: b_ref },
        is_unsafe: false,
      }),
    );
    let graph = build_ref_graph(&env);
    // B's in_refs should contain both A and C
    let b_in = &graph.in_refs[&n("B")];
    assert!(b_in.contains(&n("A")));
    assert!(b_in.contains(&n("C")));
  }

  #[test]
  fn recursor_refs_rules() {
    // Recursor T.rec with a rule for T.mk whose rhs references Q
    let mut env = Env::default();
    env.insert(
      n("T.mk"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: mk_cv("T.mk"),
        is_unsafe: false,
      }),
    );
    env.insert(
      n("Q"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("Q"), is_unsafe: false }),
    );
    env.insert(
      n("T.rec"),
      ConstantInfo::RecInfo(RecursorVal {
        cnst: mk_cv("T.rec"),
        all: vec![n("T")],
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        num_motives: Nat::from(1u64),
        num_minors: Nat::from(1u64),
        rules: vec![RecursorRule {
          ctor: n("T.mk"),
          n_fields: Nat::from(0u64),
          rhs: Expr::cnst(n("Q"), vec![]),
        }],
        k: false,
        is_unsafe: false,
      }),
    );
    let graph = build_ref_graph(&env);
    let rec_out = &graph.out_refs[&n("T.rec")];
    // References the ctor from the rule
    assert!(rec_out.contains(&n("T.mk")));
    // References Q from the rule's rhs
    assert!(rec_out.contains(&n("Q")));
    // `RecursorVal.all` is metadata; structural references come from the
    // recursor type and rules.
    assert!(!rec_out.contains(&n("T")));
  }

  #[test]
  fn expr_references_through_app_lam_let() {
    // Test that get_expr_references traverses App, Lam, LetE, Proj
    let mut env = Env::default();
    env.insert(
      n("X"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("X"), is_unsafe: false }),
    );
    env.insert(
      n("Y"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("Y"), is_unsafe: false }),
    );
    env.insert(
      n("Z"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("Z"), is_unsafe: false }),
    );
    // Build: fun (_ : X) => let _ : Y := #0 in Z
    let x_ref = Expr::cnst(n("X"), vec![]);
    let y_ref = Expr::cnst(n("Y"), vec![]);
    let z_ref = Expr::cnst(n("Z"), vec![]);
    let body = Expr::letE(
      Name::anon(),
      y_ref,
      Expr::bvar(Nat::from(0u64)),
      z_ref,
      false,
    );
    let lam = Expr::lam(Name::anon(), x_ref, body, BinderInfo::Default);
    env.insert(
      n("W"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal { name: n("W"), level_params: vec![], typ: lam },
        is_unsafe: false,
      }),
    );
    let graph = build_ref_graph(&env);
    let w_out = &graph.out_refs[&n("W")];
    assert!(w_out.contains(&n("X")));
    assert!(w_out.contains(&n("Y")));
    assert!(w_out.contains(&n("Z")));
  }

  #[test]
  fn proj_references_type_name() {
    // Proj references the type name it projects from
    let mut env = Env::default();
    env.insert(
      n("S"),
      ConstantInfo::AxiomInfo(AxiomVal { cnst: mk_cv("S"), is_unsafe: false }),
    );
    let proj_expr =
      Expr::proj(n("S"), Nat::from(0u64), Expr::bvar(Nat::from(0u64)));
    env.insert(
      n("P"),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: n("P"),
          level_params: vec![],
          typ: proj_expr,
        },
        is_unsafe: false,
      }),
    );
    let graph = build_ref_graph(&env);
    assert!(graph.out_refs[&n("P")].contains(&n("S")));
  }
}
