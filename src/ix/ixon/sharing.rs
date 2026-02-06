//! Sharing analysis for expression deduplication within mutual blocks.
//!
//! This module provides alpha-invariant sharing analysis using Merkle-tree hashing.
//! Expressions that are structurally identical get the same hash, and we decide
//! which subterms to share based on a profitability heuristic.

#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_precision_loss)]
#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::match_same_arms)]

use std::collections::HashMap;
use std::sync::Arc;

use indexmap::IndexSet;
use rustc_hash::FxHashMap;

use super::expr::Expr;
use super::tag::{Tag0, Tag4};

/// Information about a subterm for sharing analysis.
#[derive(Debug)]
pub struct SubtermInfo {
  /// Base size of this node alone (Tag4 header, not including children) for Ixon format
  pub base_size: usize,
  /// Size in a fully hash-consed store (32-byte key + value with hash references)
  pub hash_consed_size: usize,
  /// Number of occurrences within this block
  pub usage_count: usize,
  /// Canonical representative expression
  pub expr: Arc<Expr>,
  /// Hashes of child subterms (for topological ordering)
  pub children: Vec<blake3::Hash>,
}

/// Hash an expression node using Merkle-tree style hashing.
/// Returns (hash, child_hashes, value_size) where value_size is the size of the
/// serialized node value in a hash-consed store (not including the 32-byte key).
fn hash_node(
  expr: &Expr,
  child_hashes: &FxHashMap<*const Expr, blake3::Hash>,
  buf: &mut Vec<u8>,
) -> (blake3::Hash, Vec<blake3::Hash>, usize) {
  buf.clear();

  let children = match expr {
    Expr::Sort(univ_idx) => {
      buf.push(Expr::FLAG_SORT);
      buf.extend_from_slice(&univ_idx.to_le_bytes());
      vec![]
    },
    Expr::Var(idx) => {
      buf.push(Expr::FLAG_VAR);
      buf.extend_from_slice(&idx.to_le_bytes());
      vec![]
    },
    Expr::Ref(ref_idx, univ_indices) => {
      buf.push(Expr::FLAG_REF);
      buf.extend_from_slice(&ref_idx.to_le_bytes());
      buf.extend_from_slice(&(univ_indices.len() as u64).to_le_bytes());
      for idx in univ_indices {
        buf.extend_from_slice(&idx.to_le_bytes());
      }
      vec![]
    },
    Expr::Rec(rec_idx, univ_indices) => {
      buf.push(Expr::FLAG_REC);
      buf.extend_from_slice(&rec_idx.to_le_bytes());
      buf.extend_from_slice(&(univ_indices.len() as u64).to_le_bytes());
      for idx in univ_indices {
        buf.extend_from_slice(&idx.to_le_bytes());
      }
      vec![]
    },
    Expr::Prj(type_ref_idx, field_idx, val) => {
      buf.push(Expr::FLAG_PRJ);
      buf.extend_from_slice(&type_ref_idx.to_le_bytes());
      buf.extend_from_slice(&field_idx.to_le_bytes());
      let val_ptr = val.as_ref() as *const Expr;
      let val_hash = child_hashes.get(&val_ptr).unwrap();
      buf.extend_from_slice(val_hash.as_bytes());
      vec![*val_hash]
    },
    Expr::Str(ref_idx) => {
      buf.push(Expr::FLAG_STR);
      buf.extend_from_slice(&ref_idx.to_le_bytes());
      vec![]
    },
    Expr::Nat(ref_idx) => {
      buf.push(Expr::FLAG_NAT);
      buf.extend_from_slice(&ref_idx.to_le_bytes());
      vec![]
    },
    Expr::App(fun, arg) => {
      buf.push(Expr::FLAG_APP);
      let fun_ptr = fun.as_ref() as *const Expr;
      let arg_ptr = arg.as_ref() as *const Expr;
      let fun_hash = child_hashes.get(&fun_ptr).unwrap();
      let arg_hash = child_hashes.get(&arg_ptr).unwrap();
      buf.extend_from_slice(fun_hash.as_bytes());
      buf.extend_from_slice(arg_hash.as_bytes());
      vec![*fun_hash, *arg_hash]
    },
    Expr::Lam(ty, body) => {
      buf.push(Expr::FLAG_LAM);
      let ty_ptr = ty.as_ref() as *const Expr;
      let body_ptr = body.as_ref() as *const Expr;
      let ty_hash = child_hashes.get(&ty_ptr).unwrap();
      let body_hash = child_hashes.get(&body_ptr).unwrap();
      buf.extend_from_slice(ty_hash.as_bytes());
      buf.extend_from_slice(body_hash.as_bytes());
      vec![*ty_hash, *body_hash]
    },
    Expr::All(ty, body) => {
      buf.push(Expr::FLAG_ALL);
      let ty_ptr = ty.as_ref() as *const Expr;
      let body_ptr = body.as_ref() as *const Expr;
      let ty_hash = child_hashes.get(&ty_ptr).unwrap();
      let body_hash = child_hashes.get(&body_ptr).unwrap();
      buf.extend_from_slice(ty_hash.as_bytes());
      buf.extend_from_slice(body_hash.as_bytes());
      vec![*ty_hash, *body_hash]
    },
    Expr::Let(non_dep, ty, val, body) => {
      buf.push(Expr::FLAG_LET);
      buf.push(if *non_dep { 1 } else { 0 }); // size field encodes non_dep
      let ty_ptr = ty.as_ref() as *const Expr;
      let val_ptr = val.as_ref() as *const Expr;
      let body_ptr = body.as_ref() as *const Expr;
      let ty_hash = child_hashes.get(&ty_ptr).unwrap();
      let val_hash = child_hashes.get(&val_ptr).unwrap();
      let body_hash = child_hashes.get(&body_ptr).unwrap();
      buf.extend_from_slice(ty_hash.as_bytes());
      buf.extend_from_slice(val_hash.as_bytes());
      buf.extend_from_slice(body_hash.as_bytes());
      vec![*ty_hash, *val_hash, *body_hash]
    },
    Expr::Share(idx) => {
      buf.push(Expr::FLAG_SHARE);
      buf.extend_from_slice(&idx.to_le_bytes());
      vec![]
    },
  };

  let value_size = buf.len();
  (blake3::hash(buf), children, value_size)
}

/// Compute the base size of a node (Tag4 header size) for Ixon serialization.
fn compute_base_size(expr: &Expr) -> usize {
  match expr {
    Expr::Sort(univ_idx) => {
      Tag4::new(Expr::FLAG_SORT, *univ_idx).encoded_size()
    },
    Expr::Var(idx) => Tag4::new(Expr::FLAG_VAR, *idx).encoded_size(),
    Expr::Ref(ref_idx, univ_indices) => {
      // tag + ref_idx + N univ indices
      Tag4::new(Expr::FLAG_REF, univ_indices.len() as u64).encoded_size()
        + Tag0::new(*ref_idx).encoded_size()
        + univ_indices
          .iter()
          .map(|i| Tag0::new(*i).encoded_size())
          .sum::<usize>()
    },
    Expr::Rec(rec_idx, univ_indices) => {
      // tag + rec_idx + N univ indices
      Tag4::new(Expr::FLAG_REC, univ_indices.len() as u64).encoded_size()
        + Tag0::new(*rec_idx).encoded_size()
        + univ_indices
          .iter()
          .map(|i| Tag0::new(*i).encoded_size())
          .sum::<usize>()
    },
    Expr::Prj(type_ref_idx, field_idx, _) => {
      // Tag (field_idx in payload) + type_ref_idx (variable length, estimate 2 bytes)
      Tag4::new(Expr::FLAG_PRJ, *field_idx).encoded_size()
        + Tag0::new(*type_ref_idx).encoded_size()
    },
    Expr::Str(ref_idx) => Tag4::new(Expr::FLAG_STR, *ref_idx).encoded_size(),
    Expr::Nat(ref_idx) => Tag4::new(Expr::FLAG_NAT, *ref_idx).encoded_size(),
    Expr::App(..) => Tag4::new(Expr::FLAG_APP, 1).encoded_size(), // telescope count >= 1
    Expr::Lam(..) => Tag4::new(Expr::FLAG_LAM, 1).encoded_size(),
    Expr::All(..) => Tag4::new(Expr::FLAG_ALL, 1).encoded_size(),
    Expr::Let(non_dep, ..) => {
      // size=0 for dep, size=1 for non_dep
      Tag4::new(Expr::FLAG_LET, if *non_dep { 1 } else { 0 }).encoded_size()
    },
    Expr::Share(idx) => Tag4::new(Expr::FLAG_SHARE, *idx).encoded_size(),
  }
}

/// Get child expressions for traversal.
fn get_children(expr: &Expr) -> Vec<&Arc<Expr>> {
  match expr {
    Expr::Sort(_)
    | Expr::Var(_)
    | Expr::Ref(..)
    | Expr::Rec(..)
    | Expr::Str(_)
    | Expr::Nat(_)
    | Expr::Share(_) => {
      vec![]
    },
    Expr::Prj(_, _, val) => vec![val],
    Expr::App(fun, arg) => vec![fun, arg],
    Expr::Lam(ty, body) | Expr::All(ty, body) => vec![ty, body],
    Expr::Let(_, ty, val, body) => vec![ty, val, body],
  }
}

/// Analyze expressions for sharing opportunities within a block.
///
/// Returns a map from content hash to SubtermInfo, and a map from pointer to hash.
/// Uses a two-phase algorithm:
/// 1. Build DAG structure via post-order traversal with Merkle-tree hashing
/// 2. Propagate usage counts structurally from roots to leaves (O(n) total)
///
/// If `track_hash_consed_size` is true, computes the hash-consed size for each
/// subterm (32-byte key + value). This adds overhead and can be disabled when
/// only sharing analysis is needed.
pub fn analyze_block(
  exprs: &[Arc<Expr>],
  track_hash_consed_size: bool,
) -> (HashMap<blake3::Hash, SubtermInfo>, FxHashMap<*const Expr, blake3::Hash>)
{
  let mut info_map: HashMap<blake3::Hash, SubtermInfo> = HashMap::new();
  let mut ptr_to_hash: FxHashMap<*const Expr, blake3::Hash> =
    FxHashMap::default();
  let mut hash_buf: Vec<u8> = Vec::with_capacity(128);

  // Phase 1: Build DAG structure via post-order traversal
  // Don't compute usage counts here - just build the hash→children mapping
  enum Frame<'a> {
    Visit(&'a Arc<Expr>),
    Process(&'a Arc<Expr>),
  }

  for root in exprs {
    let mut stack: Vec<Frame<'_>> = vec![Frame::Visit(root)];

    while let Some(frame) = stack.pop() {
      match frame {
        Frame::Visit(arc_expr) => {
          let ptr = arc_expr.as_ref() as *const Expr;

          // Already processed this pointer - just skip
          // Usage counts will be computed in phase 2
          if ptr_to_hash.contains_key(&ptr) {
            continue;
          }

          // Push process frame, then children (in reverse for correct order)
          stack.push(Frame::Process(arc_expr));
          for child in get_children(arc_expr).into_iter().rev() {
            stack.push(Frame::Visit(child));
          }
        },
        Frame::Process(arc_expr) => {
          let ptr = arc_expr.as_ref() as *const Expr;
          if ptr_to_hash.contains_key(&ptr) {
            continue;
          }

          let (hash, children, value_size) =
            hash_node(arc_expr.as_ref(), &ptr_to_hash, &mut hash_buf);

          // Add to ptr_to_hash cache
          ptr_to_hash.insert(ptr, hash);

          // Add to info_map if not already present (same content hash from different pointer)
          info_map.entry(hash).or_insert_with(|| {
            let base_size = compute_base_size(arc_expr.as_ref());
            let hash_consed_size =
              if track_hash_consed_size { 32 + value_size } else { 0 };
            SubtermInfo {
              base_size,
              hash_consed_size,
              usage_count: 0, // Will be computed in phase 2
              expr: arc_expr.clone(),
              children,
            }
          });
        },
      }
    }
  }

  // Phase 2: Propagate usage counts structurally from roots to leaves
  // This is O(n) total - no subtree walks needed
  //
  // Algorithm:
  // 1. Each root expression contributes 1 to its hash's count
  // 2. Process in reverse topological order (roots first, leaves last)
  // 3. For each node, add its count to each child's count (with multiplicity)

  // Count root contributions
  for root in exprs {
    let ptr = root.as_ref() as *const Expr;
    if let Some(hash) = ptr_to_hash.get(&ptr)
      && let Some(info) = info_map.get_mut(hash)
    {
      info.usage_count += 1;
    }
  }

  // Get topological order (leaves first) and reverse it (roots first)
  let topo_order = topological_sort(&info_map);

  // Propagate counts from roots to leaves
  for hash in topo_order.iter().rev() {
    // Get this node's count and children
    let (count, children) = {
      let info = info_map.get(hash).unwrap();
      (info.usage_count, info.children.clone())
    };

    // Add this node's count to each child (with multiplicity from children array)
    for child_hash in children {
      if let Some(child_info) = info_map.get_mut(&child_hash) {
        child_info.usage_count += count;
      }
    }
  }

  (info_map, ptr_to_hash)
}

/// Compute the hash of a single expression.
/// This is useful for testing hash compatibility with Lean.
pub fn hash_expr(expr: &Arc<Expr>) -> blake3::Hash {
  let (_info_map, ptr_to_hash) =
    analyze_block(std::slice::from_ref(expr), false);
  let ptr = expr.as_ref() as *const Expr;
  *ptr_to_hash.get(&ptr).expect("Expression not found in ptr_to_hash")
}

/// Topological sort of subterms (leaves first, parents last).
/// CRITICAL: Keys are sorted by hash bytes for deterministic output.
/// This ensures Lean and Rust produce the same topological order.
pub fn topological_sort(
  info_map: &HashMap<blake3::Hash, SubtermInfo>,
) -> Vec<blake3::Hash> {
  #[derive(Clone, Copy, PartialEq, Eq)]
  enum VisitState {
    InProgress,
    Done,
  }

  let mut state: HashMap<blake3::Hash, VisitState> = HashMap::new();
  let mut result: Vec<blake3::Hash> = Vec::new();

  fn visit(
    hash: blake3::Hash,
    info_map: &HashMap<blake3::Hash, SubtermInfo>,
    state: &mut HashMap<blake3::Hash, VisitState>,
    result: &mut Vec<blake3::Hash>,
  ) {
    match state.get(&hash) {
      Some(VisitState::Done) => return,
      Some(VisitState::InProgress) => return, // Cycle (shouldn't happen)
      _ => {},
    }

    state.insert(hash, VisitState::InProgress);

    if let Some(info) = info_map.get(&hash) {
      for child in &info.children {
        visit(*child, info_map, state, result);
      }
    }

    state.insert(hash, VisitState::Done);
    result.push(hash);
  }

  // Sort keys deterministically by hash bytes (lexicographic comparison)
  let mut sorted_keys: Vec<blake3::Hash> = info_map.keys().cloned().collect();
  sorted_keys.sort_by_key(|h| *h.as_bytes());

  for hash in sorted_keys {
    visit(hash, info_map, &mut state, &mut result);
  }

  result
}

/// Compute effective sizes for all subterms in topological order.
/// Returns a map from hash to effective size (total serialized bytes).
pub fn compute_effective_sizes(
  info_map: &HashMap<blake3::Hash, SubtermInfo>,
  topo_order: &[blake3::Hash],
) -> HashMap<blake3::Hash, usize> {
  let mut sizes: HashMap<blake3::Hash, usize> = HashMap::new();

  for hash in topo_order {
    if let Some(info) = info_map.get(hash) {
      let mut size = info.base_size;
      for child_hash in &info.children {
        size += sizes.get(child_hash).copied().unwrap_or(0);
      }
      sizes.insert(*hash, size);
    }
  }

  sizes
}

/// Analyze sharing statistics for debugging pathological cases.
/// Returns a summary of why sharing may not be effective.
#[allow(dead_code)]
pub fn analyze_sharing_stats(
  info_map: &HashMap<blake3::Hash, SubtermInfo>,
) -> SharingStats {
  let topo_order = topological_sort(info_map);
  let effective_sizes = compute_effective_sizes(info_map, &topo_order);

  let total_subterms = info_map.len();
  let mut usage_distribution: HashMap<usize, usize> = HashMap::new();
  let mut size_distribution: HashMap<usize, usize> = HashMap::new();
  let mut total_usage: usize = 0;
  let mut unique_subterms = 0;
  let mut shared_subterms = 0;

  for (hash, info) in info_map.iter() {
    total_usage += info.usage_count;
    *usage_distribution.entry(info.usage_count).or_insert(0) += 1;

    let size = effective_sizes.get(hash).copied().unwrap_or(0);
    let size_bucket = match size {
      0..=1 => 1,
      2..=4 => 4,
      5..=10 => 10,
      11..=50 => 50,
      51..=100 => 100,
      _ => 1000,
    };
    *size_distribution.entry(size_bucket).or_insert(0) += 1;

    if info.usage_count == 1 {
      unique_subterms += 1;
    } else {
      shared_subterms += 1;
    }
  }

  // Count candidates at each filtering stage
  let candidates_usage_ge_2: usize =
    info_map.values().filter(|info| info.usage_count >= 2).count();

  let candidates_positive_potential: usize = info_map
    .iter()
    .filter(|(_, info)| info.usage_count >= 2)
    .filter(|(hash, info)| {
      let term_size = effective_sizes.get(hash).copied().unwrap_or(0);
      let n = info.usage_count;
      let potential = (n as isize - 1) * (term_size as isize) - (n as isize);
      potential > 0
    })
    .count();

  // Simulate actual sharing to count how many pass
  let mut simulated_shared = 0;
  let mut candidates: Vec<_> = info_map
    .iter()
    .filter(|(_, info)| info.usage_count >= 2)
    .filter_map(|(hash, info)| {
      let term_size = *effective_sizes.get(hash)?;
      let n = info.usage_count;
      let potential = (n as isize - 1) * (term_size as isize) - (n as isize);
      if potential > 0 { Some((term_size, n)) } else { None }
    })
    .collect();

  candidates.sort_unstable_by(|a, b| {
    let pot_a = (a.1 as isize - 1) * (a.0 as isize);
    let pot_b = (b.1 as isize - 1) * (b.0 as isize);
    pot_b.cmp(&pot_a)
  });

  for (term_size, usage_count) in candidates {
    let next_ref_size =
      Tag4::new(Expr::FLAG_SHARE, simulated_shared as u64).encoded_size();
    let n = usage_count as isize;
    let savings = (n - 1) * (term_size as isize) - n * (next_ref_size as isize);
    if savings > 0 {
      simulated_shared += 1;
    }
    // Don't break - process all candidates
  }

  SharingStats {
    total_subterms,
    unique_subterms,
    shared_subterms,
    total_usage,
    candidates_usage_ge_2,
    candidates_positive_potential,
    actually_shared: simulated_shared,
    usage_distribution,
    size_distribution,
  }
}

/// Statistics about sharing analysis.
#[derive(Debug)]
pub struct SharingStats {
  pub total_subterms: usize,
  pub unique_subterms: usize,
  pub shared_subterms: usize,
  pub total_usage: usize,
  pub candidates_usage_ge_2: usize,
  pub candidates_positive_potential: usize,
  pub actually_shared: usize,
  pub usage_distribution: HashMap<usize, usize>,
  pub size_distribution: HashMap<usize, usize>,
}

impl std::fmt::Display for SharingStats {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    writeln!(f, "=== Sharing Analysis ===")?;
    writeln!(f, "Total unique subterms: {}", self.total_subterms)?;
    writeln!(f, "  - Unique (usage=1): {}", self.unique_subterms)?;
    writeln!(f, "  - Shared (usage>=2): {}", self.shared_subterms)?;
    writeln!(f, "Total usage count: {}", self.total_usage)?;
    writeln!(
      f,
      "Average usage: {:.2}",
      if self.total_subterms > 0 {
        self.total_usage as f64 / self.total_subterms as f64
      } else {
        0.0
      }
    )?;
    writeln!(f)?;
    writeln!(f, "Filtering pipeline:")?;
    writeln!(
      f,
      "  1. Candidates with usage >= 2: {}",
      self.candidates_usage_ge_2
    )?;
    writeln!(
      f,
      "  2. With positive potential: {}",
      self.candidates_positive_potential
    )?;
    writeln!(f, "  3. Actually shared: {}", self.actually_shared)?;
    writeln!(f)?;
    writeln!(f, "Usage distribution:")?;
    let mut usage_counts: Vec<_> = self.usage_distribution.iter().collect();
    usage_counts.sort_by_key(|(k, _)| *k);
    for (usage, count) in usage_counts.iter().take(10) {
      writeln!(f, "  usage={}: {} subterms", usage, count)?;
    }
    if usage_counts.len() > 10 {
      writeln!(f, "  ... and {} more buckets", usage_counts.len() - 10)?;
    }
    writeln!(f)?;
    writeln!(f, "Size distribution (effective_size buckets):")?;
    let mut size_counts: Vec<_> = self.size_distribution.iter().collect();
    size_counts.sort_by_key(|(k, _)| *k);
    for (size_bucket, count) in size_counts {
      writeln!(f, "  size<={}: {} subterms", size_bucket, count)?;
    }
    Ok(())
  }
}

/// Decide which subterms to share based on profitability.
///
/// Sharing is profitable when: `(N - 1) * term_size > N * share_ref_size`
/// where N is usage count, term_size is effective size, and share_ref_size
/// is the size of a Share(idx) reference at the current index.
///
/// Optimized from O(k×n) to O(n log n) by pre-sorting candidates.
pub fn decide_sharing(
  info_map: &HashMap<blake3::Hash, SubtermInfo>,
) -> IndexSet<blake3::Hash> {
  let topo_order = topological_sort(info_map);
  let effective_sizes = compute_effective_sizes(info_map, &topo_order);

  // Pre-filter and sort candidates by potential savings (assuming minimal ref_size=1)
  // This gives us a stable ordering since relative savings don't change as ref_size grows
  let mut candidates: Vec<_> = info_map
    .iter()
    .filter(|(_, info)| info.usage_count >= 2)
    .filter_map(|(hash, info)| {
      let term_size = *effective_sizes.get(hash)?;
      let n = info.usage_count;
      // Potential savings assuming ref_size = 1 (minimum)
      let potential = (n as isize - 1) * (term_size as isize) - (n as isize);
      if potential > 0 { Some((*hash, term_size, n)) } else { None }
    })
    .collect();

  // Sort by decreasing gross benefit, with hash bytes as tie-breaker for determinism
  candidates.sort_unstable_by(|a, b| {
    let gross_a = (a.2 as isize - 1) * (a.1 as isize);
    let gross_b = (b.2 as isize - 1) * (b.1 as isize);
    match gross_b.cmp(&gross_a) {
      std::cmp::Ordering::Equal => a.0.as_bytes().cmp(b.0.as_bytes()),
      other => other,
    }
  });

  let mut shared: IndexSet<blake3::Hash> = IndexSet::new();

  // Process ALL candidates - don't break early!
  // The early-break was incorrect: ref_size growth affects candidates differently
  // based on their usage count. A high-usage small term may become unprofitable
  // while a low-usage large term remains profitable.
  for (hash, term_size, usage_count) in candidates {
    let next_idx = shared.len();
    let next_ref_size =
      Tag4::new(Expr::FLAG_SHARE, next_idx as u64).encoded_size();
    let n = usage_count as isize;
    let savings = (n - 1) * (term_size as isize) - n * (next_ref_size as isize);

    if savings > 0 {
      shared.insert(hash);
    }
  }

  shared
}

/// Rewrite expressions to use Share(idx) references for shared subterms.
///
/// Returns the rewritten expressions and the sharing vector.
pub fn build_sharing_vec(
  exprs: &[Arc<Expr>],
  shared_hashes: &IndexSet<blake3::Hash>,
  ptr_to_hash: &FxHashMap<*const Expr, blake3::Hash>,
  info_map: &HashMap<blake3::Hash, SubtermInfo>,
) -> (Vec<Arc<Expr>>, Vec<Arc<Expr>>) {
  // CRITICAL: Re-sort shared_hashes in topological order (leaves first).
  // decide_sharing returns hashes sorted by gross benefit (large terms first),
  // but we need leaves first so that when serializing sharing[i], all its
  // children are already available as Share(j) for j < i.
  let topo_order = topological_sort(info_map);
  let shared_in_topo_order: Vec<blake3::Hash> =
    topo_order.into_iter().filter(|h| shared_hashes.contains(h)).collect();

  // Build sharing vector incrementally to avoid forward references.
  // When building sharing[i], only Share(j) for j < i is allowed.
  let mut sharing_vec: Vec<Arc<Expr>> = Vec::with_capacity(shared_hashes.len());
  let mut hash_to_idx: HashMap<blake3::Hash, u64> = HashMap::new();
  let mut cache: FxHashMap<*const Expr, Arc<Expr>> = FxHashMap::default();

  for h in &shared_in_topo_order {
    let info = info_map.get(h).expect("shared hash must be in info_map");
    // Clear cache - hash_to_idx changed, so cached rewrites are invalid
    cache.clear();
    // Rewrite using only indices < current length (hash_to_idx doesn't include this entry yet)
    let rewritten =
      rewrite_expr(&info.expr, &hash_to_idx, ptr_to_hash, &mut cache);

    let idx = sharing_vec.len() as u64;
    sharing_vec.push(rewritten);
    // Now add this hash to the map for subsequent entries
    hash_to_idx.insert(*h, idx);
  }

  // Rewrite the root expressions (can use all Share indices)
  // Use a fresh cache since hash_to_idx is now complete
  cache.clear();
  let rewritten_exprs: Vec<Arc<Expr>> = exprs
    .iter()
    .map(|e| rewrite_expr(e, &hash_to_idx, ptr_to_hash, &mut cache))
    .collect();

  (rewritten_exprs, sharing_vec)
}

/// Frame for iterative rewrite traversal.
enum RewriteFrame<'a> {
  /// Visit an expression (check cache/share, then push children)
  Visit(&'a Arc<Expr>),
  /// Build a Prj node from rewritten children (type_ref_idx, field_idx)
  BuildPrj(&'a Arc<Expr>, u64, u64),
  /// Build an App node from rewritten children
  BuildApp(&'a Arc<Expr>),
  /// Build a Lam node from rewritten children
  BuildLam(&'a Arc<Expr>),
  /// Build an All node from rewritten children
  BuildAll(&'a Arc<Expr>),
  /// Build a Let node from rewritten children
  BuildLet(&'a Arc<Expr>, bool),
}

/// Rewrite an expression tree to use Share(idx) references.
/// Uses iterative traversal with caching to handle deep trees and Arc sharing.
fn rewrite_expr(
  expr: &Arc<Expr>,
  hash_to_idx: &HashMap<blake3::Hash, u64>,
  ptr_to_hash: &FxHashMap<*const Expr, blake3::Hash>,
  cache: &mut FxHashMap<*const Expr, Arc<Expr>>,
) -> Arc<Expr> {
  let mut stack: Vec<RewriteFrame<'_>> = vec![RewriteFrame::Visit(expr)];
  let mut results: Vec<Arc<Expr>> = Vec::new();

  while let Some(frame) = stack.pop() {
    match frame {
      RewriteFrame::Visit(e) => {
        let ptr = e.as_ref() as *const Expr;

        // Check cache first
        if let Some(cached) = cache.get(&ptr) {
          results.push(cached.clone());
          continue;
        }

        // Check if this expression should become a Share reference
        if let Some(hash) = ptr_to_hash.get(&ptr)
          && let Some(&idx) = hash_to_idx.get(hash)
        {
          let share = Expr::share(idx);
          cache.insert(ptr, share.clone());
          results.push(share);
          continue;
        }

        // Process based on node type
        match e.as_ref() {
          // Leaf nodes - return as-is
          Expr::Sort(_)
          | Expr::Var(_)
          | Expr::Ref(..)
          | Expr::Rec(..)
          | Expr::Str(_)
          | Expr::Nat(_)
          | Expr::Share(_) => {
            cache.insert(ptr, e.clone());
            results.push(e.clone());
          },

          // Nodes with children - push build frame, then visit children
          Expr::Prj(type_ref_idx, field_idx, val) => {
            stack.push(RewriteFrame::BuildPrj(e, *type_ref_idx, *field_idx));
            stack.push(RewriteFrame::Visit(val));
          },
          Expr::App(fun, arg) => {
            stack.push(RewriteFrame::BuildApp(e));
            stack.push(RewriteFrame::Visit(arg));
            stack.push(RewriteFrame::Visit(fun));
          },
          Expr::Lam(ty, body) => {
            stack.push(RewriteFrame::BuildLam(e));
            stack.push(RewriteFrame::Visit(body));
            stack.push(RewriteFrame::Visit(ty));
          },
          Expr::All(ty, body) => {
            stack.push(RewriteFrame::BuildAll(e));
            stack.push(RewriteFrame::Visit(body));
            stack.push(RewriteFrame::Visit(ty));
          },
          Expr::Let(non_dep, ty, val, body) => {
            stack.push(RewriteFrame::BuildLet(e, *non_dep));
            stack.push(RewriteFrame::Visit(body));
            stack.push(RewriteFrame::Visit(val));
            stack.push(RewriteFrame::Visit(ty));
          },
        }
      },

      RewriteFrame::BuildPrj(orig, type_ref_idx, field_idx) => {
        let new_val = results.pop().unwrap();
        let orig_val = match orig.as_ref() {
          Expr::Prj(_, _, v) => v,
          _ => unreachable!(),
        };
        let result = if Arc::ptr_eq(&new_val, orig_val) {
          orig.clone()
        } else {
          Expr::prj(type_ref_idx, field_idx, new_val)
        };
        let ptr = orig.as_ref() as *const Expr;
        cache.insert(ptr, result.clone());
        results.push(result);
      },

      RewriteFrame::BuildApp(orig) => {
        // Pop in reverse order of push: arg was pushed last, fun first
        let new_arg = results.pop().unwrap();
        let new_fun = results.pop().unwrap();
        let (orig_fun, orig_arg) = match orig.as_ref() {
          Expr::App(f, a) => (f, a),
          _ => unreachable!(),
        };
        let result = if Arc::ptr_eq(&new_fun, orig_fun)
          && Arc::ptr_eq(&new_arg, orig_arg)
        {
          orig.clone()
        } else {
          Expr::app(new_fun, new_arg)
        };
        let ptr = orig.as_ref() as *const Expr;
        cache.insert(ptr, result.clone());
        results.push(result);
      },

      RewriteFrame::BuildLam(orig) => {
        // Pop in reverse order of push: body was pushed last, ty first
        let new_body = results.pop().unwrap();
        let new_ty = results.pop().unwrap();
        let (orig_ty, orig_body) = match orig.as_ref() {
          Expr::Lam(t, b) => (t, b),
          _ => unreachable!(),
        };
        let result = if Arc::ptr_eq(&new_ty, orig_ty)
          && Arc::ptr_eq(&new_body, orig_body)
        {
          orig.clone()
        } else {
          Expr::lam(new_ty, new_body)
        };
        let ptr = orig.as_ref() as *const Expr;
        cache.insert(ptr, result.clone());
        results.push(result);
      },

      RewriteFrame::BuildAll(orig) => {
        // Pop in reverse order of push: body was pushed last, ty first
        let new_body = results.pop().unwrap();
        let new_ty = results.pop().unwrap();
        let (orig_ty, orig_body) = match orig.as_ref() {
          Expr::All(t, b) => (t, b),
          _ => unreachable!(),
        };
        let result = if Arc::ptr_eq(&new_ty, orig_ty)
          && Arc::ptr_eq(&new_body, orig_body)
        {
          orig.clone()
        } else {
          Expr::all(new_ty, new_body)
        };
        let ptr = orig.as_ref() as *const Expr;
        cache.insert(ptr, result.clone());
        results.push(result);
      },

      RewriteFrame::BuildLet(orig, non_dep) => {
        // Pop in reverse order of push: body, val, ty
        let new_body = results.pop().unwrap();
        let new_val = results.pop().unwrap();
        let new_ty = results.pop().unwrap();
        let (orig_ty, orig_val, orig_body) = match orig.as_ref() {
          Expr::Let(_, t, v, b) => (t, v, b),
          _ => unreachable!(),
        };
        let result = if Arc::ptr_eq(&new_ty, orig_ty)
          && Arc::ptr_eq(&new_val, orig_val)
          && Arc::ptr_eq(&new_body, orig_body)
        {
          orig.clone()
        } else {
          Expr::let_(non_dep, new_ty, new_val, new_body)
        };
        let ptr = orig.as_ref() as *const Expr;
        cache.insert(ptr, result.clone());
        results.push(result);
      },
    }
  }

  results.pop().unwrap()
}

#[cfg(test)]
mod tests {
  use super::*;

  /// Test that demonstrates the early-break bug in decide_sharing.
  ///
  /// The bug: decide_sharing sorts candidates by "gross benefit" (n-1)*size
  /// and breaks on the first unprofitable candidate. However, as ref_size
  /// grows (1 byte for idx<8, 2 bytes for idx>=8), a high-usage small-size
  /// term may become unprofitable while a low-usage large-size term remains
  /// profitable.
  ///
  /// At ref_size=2 (idx >= 8):
  /// - Term A: size=2, n=10, gross=18, savings = 18 - 20 = -2 < 0 (triggers break!)
  /// - Term B: size=5, n=2, gross=5, savings = 5 - 4 = 1 > 0 (profitable but skipped)
  ///
  /// We need 8 filler terms with gross > 18 to fill indices 0-7 first.
  #[test]
  fn test_early_break_bug() {
    // Filler: 8 unique terms with gross > 18
    // Var(256)..Var(263), each appearing 10 times
    // size=3 (256 fits in 2 bytes after Tag4 header), n=10, gross=9*3=27 > 18
    let mut all_exprs: Vec<Arc<Expr>> = Vec::new();

    for i in 0..8u64 {
      let var = Expr::var(256 + i); // size=3
      for _ in 0..10 {
        all_exprs.push(var.clone());
      }
    }

    // Term A: Var(10), appearing 10 times
    // size=2 (10 < 256, so fits in Tag4 with 2-byte encoding), n=10, gross=9*2=18
    // At ref_size=2 (idx >= 8): savings = 18 - 20 = -2 < 0 (triggers break!)
    let term_a = Expr::var(10);
    for _ in 0..10 {
      all_exprs.push(term_a.clone());
    }

    // Term B: All(Var(0), All(Var(1), Var(2))) appearing 2 times
    // This has effective_size = 1 + 1 + (1 + 1 + 1) = 5
    // gross = 1*5 = 5 < 18 ✓ (comes after A in sort order)
    // At ref_size=2: savings = 5 - 4 = 1 > 0 ✓ (profitable!)
    let term_b = Expr::all(Expr::var(0), Expr::all(Expr::var(1), Expr::var(2)));
    all_exprs.push(term_b.clone());
    all_exprs.push(term_b.clone());

    // Analyze all expressions together
    let (info_map, ptr_to_hash) = analyze_block(&all_exprs, false);
    let shared = decide_sharing(&info_map);

    // Verify term_a was found with usage_count=10
    let term_a_ptr = term_a.as_ref() as *const Expr;
    let term_a_hash = ptr_to_hash.get(&term_a_ptr);
    if let Some(hash) = term_a_hash {
      let info = info_map.get(hash).unwrap();
      assert_eq!(info.usage_count, 10, "term_a should have usage_count=10");
    }

    // Find term B's hash - it's the outer All(Var(0), ...)
    let term_b_ptr = term_b.as_ref() as *const Expr;
    let term_b_hash = ptr_to_hash.get(&term_b_ptr);

    if let Some(hash) = term_b_hash {
      let info = info_map.get(hash).unwrap();
      assert_eq!(info.usage_count, 2, "term_b should have usage_count=2");

      // Compute effective size
      let topo = topological_sort(&info_map);
      let sizes = compute_effective_sizes(&info_map, &topo);
      let term_b_size = sizes.get(hash).copied().unwrap_or(0);

      // This assertion will FAIL with buggy code (early break) and PASS with fix
      assert!(
        shared.contains(hash),
        "Term B (effective_size={}, n=2, gross={}) should be shared. \
         At ref_size=2, savings = {} - 4 = {} > 0. \
         But early-break bug skips it after term A fails. \
         shared.len()={}",
        term_b_size,
        term_b_size, // gross = (n-1)*size = 1*size
        term_b_size,
        term_b_size as isize - 4,
        shared.len()
      );
    }
  }

  #[test]
  fn test_analyze_simple() {
    // Create a simple expression: App(Var(0), Var(0))
    // Var(0) should have usage_count = 2
    let var0 = Expr::var(0);
    let app = Expr::app(var0.clone(), var0);

    let (info_map, ptr_to_hash) = analyze_block(&[app], false);

    // Should have 2 unique subterms: Var(0) and App(Var(0), Var(0))
    assert_eq!(info_map.len(), 2);

    // Find Var(0) info - it should have usage_count = 2
    let var_hash = ptr_to_hash.values().find(|h| {
      info_map
        .get(*h)
        .is_some_and(|info| matches!(info.expr.as_ref(), Expr::Var(0)))
    });
    assert!(var_hash.is_some());
    let var_info = info_map.get(var_hash.unwrap()).unwrap();
    assert_eq!(var_info.usage_count, 2);
  }

  #[test]
  fn test_decide_sharing_simple() {
    // Create expression with repeated subterm
    let ty = Expr::sort(0);
    let lam1 = Expr::lam(ty.clone(), Expr::var(0));
    let lam2 = Expr::lam(ty.clone(), Expr::var(1));
    let app = Expr::app(lam1, lam2);

    let (info_map, _) = analyze_block(&[app], false);
    let shared = decide_sharing(&info_map);

    // ty (Sort(0)) appears twice, might be shared depending on size
    // This is a basic smoke test
    assert!(shared.len() <= info_map.len());
  }

  #[test]
  fn test_topological_sort() {
    let var0 = Expr::var(0);
    let var1 = Expr::var(1);
    let app = Expr::app(var0, var1);

    let (info_map, _) = analyze_block(&[app], false);
    let topo = topological_sort(&info_map);

    // Should have all hashes
    assert_eq!(topo.len(), info_map.len());

    // Leaves (Var) should come before App
    let app_hash = info_map
      .iter()
      .find(|(_, info)| matches!(info.expr.as_ref(), Expr::App(..)))
      .map(|(h, _)| *h);

    if let Some(app_h) = app_hash {
      let app_pos = topo.iter().position(|h| *h == app_h).unwrap();
      // App should be last (after its children)
      for child_hash in &info_map.get(&app_h).unwrap().children {
        let child_pos = topo.iter().position(|h| h == child_hash).unwrap();
        assert!(
          child_pos < app_pos,
          "Child should come before parent in topo order"
        );
      }
    }
  }

  #[test]
  fn test_build_sharing_vec() {
    // Create expression with a shared subterm: App(App(var0, var0), var0)
    // var0 appears 3 times, should be shared
    let var0 = Expr::var(0);
    let app1 = Expr::app(var0.clone(), var0.clone());
    let app2 = Expr::app(app1, var0);

    let (info_map, ptr_to_hash) =
      analyze_block(std::slice::from_ref(&app2), false);
    let shared = decide_sharing(&info_map);

    // If var0 is shared, verify it
    if !shared.is_empty() {
      let (rewritten, sharing_vec) =
        build_sharing_vec(&[app2], &shared, &ptr_to_hash, &info_map);

      // Sharing vec should have the shared expressions
      assert_eq!(sharing_vec.len(), shared.len());

      // Rewritten should have at least one Share reference if sharing happened
      assert_eq!(rewritten.len(), 1);
    }
  }

  #[test]
  fn test_roundtrip_with_sharing() {
    use crate::ix::ixon::serialize::{get_expr, put_expr};

    // Create a simple expression with potential sharing
    let var0 = Expr::var(0);
    let var1 = Expr::var(1);
    let app = Expr::app(var0, var1);

    // Serialize and deserialize without sharing
    let mut buf = Vec::new();
    put_expr(&app, &mut buf);
    let recovered = get_expr(&mut buf.as_slice()).unwrap();

    assert_eq!(app.as_ref(), recovered.as_ref());
  }
}
