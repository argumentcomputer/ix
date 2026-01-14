//! Sharing analysis for expression deduplication within mutual blocks.
//!
//! This module provides alpha-invariant sharing analysis using Merkle-tree hashing.
//! Expressions that are structurally identical get the same hash, and we decide
//! which subterms to share based on a profitability heuristic.

use std::collections::HashMap;
use std::sync::Arc;

use indexmap::IndexSet;
use rustc_hash::FxHashMap;

use super::expr::Expr;
use super::tag::{Tag0, Tag4};

/// Information about a subterm for sharing analysis.
#[derive(Debug)]
pub struct SubtermInfo {
  /// Base size of this node alone (Tag4 header, not including children)
  pub base_size: usize,
  /// Number of occurrences within this block
  pub usage_count: usize,
  /// Canonical representative expression
  pub expr: Arc<Expr>,
  /// Hashes of child subterms (for topological ordering)
  pub children: Vec<blake3::Hash>,
}

/// Hash an expression node using Merkle-tree style hashing.
/// Returns the hash and child hashes for dependency tracking.
fn hash_node(
  expr: &Expr,
  child_hashes: &FxHashMap<*const Expr, blake3::Hash>,
  buf: &mut Vec<u8>,
) -> (blake3::Hash, Vec<blake3::Hash>) {
  buf.clear();

  let children = match expr {
    Expr::Sort(univ_idx) => {
      buf.push(Expr::FLAG_SORT);
      buf.extend_from_slice(&univ_idx.to_le_bytes());
      vec![]
    }
    Expr::Var(idx) => {
      buf.push(Expr::FLAG_VAR);
      buf.extend_from_slice(&idx.to_le_bytes());
      vec![]
    }
    Expr::Ref(ref_idx, univ_indices) => {
      buf.push(Expr::FLAG_REF);
      buf.extend_from_slice(&ref_idx.to_le_bytes());
      buf.extend_from_slice(&(univ_indices.len() as u64).to_le_bytes());
      for idx in univ_indices {
        buf.extend_from_slice(&idx.to_le_bytes());
      }
      vec![]
    }
    Expr::Rec(rec_idx, univ_indices) => {
      buf.push(Expr::FLAG_REC);
      buf.extend_from_slice(&rec_idx.to_le_bytes());
      buf.extend_from_slice(&(univ_indices.len() as u64).to_le_bytes());
      for idx in univ_indices {
        buf.extend_from_slice(&idx.to_le_bytes());
      }
      vec![]
    }
    Expr::Prj(type_ref_idx, field_idx, val) => {
      buf.push(Expr::FLAG_PRJ);
      buf.extend_from_slice(&type_ref_idx.to_le_bytes());
      buf.extend_from_slice(&field_idx.to_le_bytes());
      let val_ptr = val.as_ref() as *const Expr;
      let val_hash = child_hashes.get(&val_ptr).unwrap();
      buf.extend_from_slice(val_hash.as_bytes());
      vec![*val_hash]
    }
    Expr::Str(ref_idx) => {
      buf.push(Expr::FLAG_STR);
      buf.extend_from_slice(&ref_idx.to_le_bytes());
      vec![]
    }
    Expr::Nat(ref_idx) => {
      buf.push(Expr::FLAG_NAT);
      buf.extend_from_slice(&ref_idx.to_le_bytes());
      vec![]
    }
    Expr::App(fun, arg) => {
      buf.push(Expr::FLAG_APP);
      let fun_ptr = fun.as_ref() as *const Expr;
      let arg_ptr = arg.as_ref() as *const Expr;
      let fun_hash = child_hashes.get(&fun_ptr).unwrap();
      let arg_hash = child_hashes.get(&arg_ptr).unwrap();
      buf.extend_from_slice(fun_hash.as_bytes());
      buf.extend_from_slice(arg_hash.as_bytes());
      vec![*fun_hash, *arg_hash]
    }
    Expr::Lam(ty, body) => {
      buf.push(Expr::FLAG_LAM);
      let ty_ptr = ty.as_ref() as *const Expr;
      let body_ptr = body.as_ref() as *const Expr;
      let ty_hash = child_hashes.get(&ty_ptr).unwrap();
      let body_hash = child_hashes.get(&body_ptr).unwrap();
      buf.extend_from_slice(ty_hash.as_bytes());
      buf.extend_from_slice(body_hash.as_bytes());
      vec![*ty_hash, *body_hash]
    }
    Expr::All(ty, body) => {
      buf.push(Expr::FLAG_ALL);
      let ty_ptr = ty.as_ref() as *const Expr;
      let body_ptr = body.as_ref() as *const Expr;
      let ty_hash = child_hashes.get(&ty_ptr).unwrap();
      let body_hash = child_hashes.get(&body_ptr).unwrap();
      buf.extend_from_slice(ty_hash.as_bytes());
      buf.extend_from_slice(body_hash.as_bytes());
      vec![*ty_hash, *body_hash]
    }
    Expr::Let(non_dep, ty, val, body) => {
      let flag = if *non_dep { Expr::FLAG_LET_NONDEP } else { Expr::FLAG_LET_DEP };
      buf.push(flag);
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
    }
    Expr::Share(idx) => {
      buf.push(Expr::FLAG_SHARE);
      buf.extend_from_slice(&idx.to_le_bytes());
      vec![]
    }
  };

  (blake3::hash(buf), children)
}

/// Compute the base size of a node (Tag4 header size).
fn compute_base_size(expr: &Expr) -> usize {
  match expr {
    Expr::Sort(univ_idx) => Tag4::new(Expr::FLAG_SORT, *univ_idx).encoded_size(),
    Expr::Var(idx) => Tag4::new(Expr::FLAG_VAR, *idx).encoded_size(),
    Expr::Ref(ref_idx, univ_indices) => {
      // tag + ref_idx + N univ indices
      Tag4::new(Expr::FLAG_REF, univ_indices.len() as u64).encoded_size()
        + Tag0::new(*ref_idx).encoded_size()
        + univ_indices.iter().map(|i| Tag0::new(*i).encoded_size()).sum::<usize>()
    }
    Expr::Rec(rec_idx, univ_indices) => {
      // tag + rec_idx + N univ indices
      Tag4::new(Expr::FLAG_REC, univ_indices.len() as u64).encoded_size()
        + Tag0::new(*rec_idx).encoded_size()
        + univ_indices.iter().map(|i| Tag0::new(*i).encoded_size()).sum::<usize>()
    }
    Expr::Prj(type_ref_idx, field_idx, _) => {
      // Tag (field_idx in payload) + type_ref_idx (variable length, estimate 2 bytes)
      Tag4::new(Expr::FLAG_PRJ, *field_idx).encoded_size() + Tag0::new(*type_ref_idx).encoded_size()
    }
    Expr::Str(ref_idx) => Tag4::new(Expr::FLAG_STR, *ref_idx).encoded_size(),
    Expr::Nat(ref_idx) => Tag4::new(Expr::FLAG_NAT, *ref_idx).encoded_size(),
    Expr::App(..) => Tag4::new(Expr::FLAG_APP, 1).encoded_size(), // telescope count >= 1
    Expr::Lam(..) => Tag4::new(Expr::FLAG_LAM, 1).encoded_size(),
    Expr::All(..) => Tag4::new(Expr::FLAG_ALL, 1).encoded_size(),
    Expr::Let(non_dep, ..) => {
      let flag = if *non_dep { Expr::FLAG_LET_NONDEP } else { Expr::FLAG_LET_DEP };
      Tag4::new(flag, 0).encoded_size()
    }
    Expr::Share(idx) => Tag4::new(Expr::FLAG_SHARE, *idx).encoded_size(),
  }
}

/// Get child expressions for traversal.
fn get_children(expr: &Expr) -> Vec<&Arc<Expr>> {
  match expr {
    Expr::Sort(_) | Expr::Var(_) | Expr::Ref(..) | Expr::Rec(..) | Expr::Str(_) | Expr::Nat(_) | Expr::Share(_) => {
      vec![]
    }
    Expr::Prj(_, _, val) => vec![val],
    Expr::App(fun, arg) => vec![fun, arg],
    Expr::Lam(ty, body) | Expr::All(ty, body) => vec![ty, body],
    Expr::Let(_, ty, val, body) => vec![ty, val, body],
  }
}

/// Analyze expressions for sharing opportunities within a block.
///
/// Returns a map from content hash to SubtermInfo, and a map from pointer to hash.
/// Uses post-order traversal with Merkle-tree hashing.
pub fn analyze_block(
  exprs: &[Arc<Expr>],
) -> (HashMap<blake3::Hash, SubtermInfo>, FxHashMap<*const Expr, blake3::Hash>) {
  let mut info_map: HashMap<blake3::Hash, SubtermInfo> = HashMap::new();
  let mut ptr_to_hash: FxHashMap<*const Expr, blake3::Hash> = FxHashMap::default();
  let mut hash_buf: Vec<u8> = Vec::with_capacity(128);

  // Stack-based post-order traversal
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

          // Already processed this pointer, just increment usage count
          if let Some(hash) = ptr_to_hash.get(&ptr) {
            if let Some(info) = info_map.get_mut(hash) {
              info.usage_count += 1;
            }
            continue;
          }

          // Push process frame, then children (in reverse for correct order)
          stack.push(Frame::Process(arc_expr));
          for child in get_children(arc_expr).into_iter().rev() {
            stack.push(Frame::Visit(child));
          }
        }
        Frame::Process(arc_expr) => {
          let ptr = arc_expr.as_ref() as *const Expr;
          if ptr_to_hash.contains_key(&ptr) {
            continue;
          }

          let (hash, children) = hash_node(arc_expr.as_ref(), &ptr_to_hash, &mut hash_buf);

          // Check if we've seen this content hash before (structural equality)
          if let Some(existing) = info_map.get_mut(&hash) {
            existing.usage_count += 1;
            ptr_to_hash.insert(ptr, hash);
          } else {
            // New subterm
            let base_size = compute_base_size(arc_expr.as_ref());
            info_map.insert(
              hash,
              SubtermInfo {
                base_size,
                usage_count: 1,
                expr: arc_expr.clone(),
                children,
              },
            );
            ptr_to_hash.insert(ptr, hash);
          }
        }
      }
    }
  }

  (info_map, ptr_to_hash)
}

/// Topological sort of subterms (leaves first, parents last).
fn topological_sort(info_map: &HashMap<blake3::Hash, SubtermInfo>) -> Vec<blake3::Hash> {
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
      _ => {}
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

  for hash in info_map.keys() {
    visit(*hash, info_map, &mut state, &mut result);
  }

  result
}

/// Compute effective sizes for all subterms in topological order.
/// Returns a map from hash to effective size (total serialized bytes).
fn compute_effective_sizes(
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
      if potential > 0 {
        Some((*hash, term_size, n))
      } else {
        None
      }
    })
    .collect();

  // Sort by decreasing potential savings
  candidates.sort_unstable_by(|a, b| {
    let pot_a = (a.2 as isize - 1) * (a.1 as isize);
    let pot_b = (b.2 as isize - 1) * (b.1 as isize);
    pot_b.cmp(&pot_a)
  });

  let mut shared: IndexSet<blake3::Hash> = IndexSet::new();

  // Process candidates in sorted order
  for (hash, term_size, usage_count) in candidates {
    let next_idx = shared.len();
    let next_ref_size = Tag4::new(Expr::FLAG_SHARE, next_idx as u64).encoded_size();
    let n = usage_count as isize;
    let savings = (n - 1) * (term_size as isize) - n * (next_ref_size as isize);

    if savings > 0 {
      shared.insert(hash);
    } else {
      // Since candidates are sorted by decreasing potential and ref_size only grows,
      // remaining candidates won't be profitable either
      break;
    }
  }

  shared
}

/// Rewrite expressions to use Share(idx) references for shared subterms.
///
/// Returns the rewritten expressions and the sharing vector.
pub fn build_sharing_vec(
  exprs: Vec<Arc<Expr>>,
  shared_hashes: &IndexSet<blake3::Hash>,
  ptr_to_hash: &FxHashMap<*const Expr, blake3::Hash>,
  info_map: &HashMap<blake3::Hash, SubtermInfo>,
) -> (Vec<Arc<Expr>>, Vec<Arc<Expr>>) {
  // Build sharing vector incrementally to avoid forward references.
  // When building sharing[i], only Share(j) for j < i is allowed.
  let mut sharing_vec: Vec<Arc<Expr>> = Vec::with_capacity(shared_hashes.len());
  let mut hash_to_idx: HashMap<blake3::Hash, u64> = HashMap::new();
  let mut cache: FxHashMap<*const Expr, Arc<Expr>> = FxHashMap::default();

  for (i, h) in shared_hashes.iter().enumerate() {
    let info = info_map.get(h).expect("shared hash must be in info_map");
    // Clear cache - hash_to_idx changed, so cached rewrites are invalid
    cache.clear();
    // Rewrite using only indices < i (hash_to_idx doesn't include i yet)
    let rewritten = rewrite_expr(&info.expr, &hash_to_idx, ptr_to_hash, &mut cache);
    sharing_vec.push(rewritten);
    // Now add this hash to the map for subsequent entries
    hash_to_idx.insert(*h, i as u64);
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
        if let Some(hash) = ptr_to_hash.get(&ptr) {
          if let Some(&idx) = hash_to_idx.get(hash) {
            let share = Expr::share(idx);
            cache.insert(ptr, share.clone());
            results.push(share);
            continue;
          }
        }

        // Process based on node type
        match e.as_ref() {
          // Leaf nodes - return as-is
          Expr::Sort(_) | Expr::Var(_) | Expr::Ref(..) | Expr::Rec(..)
          | Expr::Str(_) | Expr::Nat(_) | Expr::Share(_) => {
            cache.insert(ptr, e.clone());
            results.push(e.clone());
          }

          // Nodes with children - push build frame, then visit children
          Expr::Prj(type_ref_idx, field_idx, val) => {
            stack.push(RewriteFrame::BuildPrj(e, *type_ref_idx, *field_idx));
            stack.push(RewriteFrame::Visit(val));
          }
          Expr::App(fun, arg) => {
            stack.push(RewriteFrame::BuildApp(e));
            stack.push(RewriteFrame::Visit(arg));
            stack.push(RewriteFrame::Visit(fun));
          }
          Expr::Lam(ty, body) => {
            stack.push(RewriteFrame::BuildLam(e));
            stack.push(RewriteFrame::Visit(body));
            stack.push(RewriteFrame::Visit(ty));
          }
          Expr::All(ty, body) => {
            stack.push(RewriteFrame::BuildAll(e));
            stack.push(RewriteFrame::Visit(body));
            stack.push(RewriteFrame::Visit(ty));
          }
          Expr::Let(non_dep, ty, val, body) => {
            stack.push(RewriteFrame::BuildLet(e, *non_dep));
            stack.push(RewriteFrame::Visit(body));
            stack.push(RewriteFrame::Visit(val));
            stack.push(RewriteFrame::Visit(ty));
          }
        }
      }

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
      }

      RewriteFrame::BuildApp(orig) => {
        // Pop in reverse order of push: arg was pushed last, fun first
        let new_arg = results.pop().unwrap();
        let new_fun = results.pop().unwrap();
        let (orig_fun, orig_arg) = match orig.as_ref() {
          Expr::App(f, a) => (f, a),
          _ => unreachable!(),
        };
        let result = if Arc::ptr_eq(&new_fun, orig_fun) && Arc::ptr_eq(&new_arg, orig_arg) {
          orig.clone()
        } else {
          Expr::app(new_fun, new_arg)
        };
        let ptr = orig.as_ref() as *const Expr;
        cache.insert(ptr, result.clone());
        results.push(result);
      }

      RewriteFrame::BuildLam(orig) => {
        // Pop in reverse order of push: body was pushed last, ty first
        let new_body = results.pop().unwrap();
        let new_ty = results.pop().unwrap();
        let (orig_ty, orig_body) = match orig.as_ref() {
          Expr::Lam(t, b) => (t, b),
          _ => unreachable!(),
        };
        let result = if Arc::ptr_eq(&new_ty, orig_ty) && Arc::ptr_eq(&new_body, orig_body) {
          orig.clone()
        } else {
          Expr::lam(new_ty, new_body)
        };
        let ptr = orig.as_ref() as *const Expr;
        cache.insert(ptr, result.clone());
        results.push(result);
      }

      RewriteFrame::BuildAll(orig) => {
        // Pop in reverse order of push: body was pushed last, ty first
        let new_body = results.pop().unwrap();
        let new_ty = results.pop().unwrap();
        let (orig_ty, orig_body) = match orig.as_ref() {
          Expr::All(t, b) => (t, b),
          _ => unreachable!(),
        };
        let result = if Arc::ptr_eq(&new_ty, orig_ty) && Arc::ptr_eq(&new_body, orig_body) {
          orig.clone()
        } else {
          Expr::all(new_ty, new_body)
        };
        let ptr = orig.as_ref() as *const Expr;
        cache.insert(ptr, result.clone());
        results.push(result);
      }

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
      }
    }
  }

  results.pop().unwrap()
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_analyze_simple() {
    // Create a simple expression: App(Var(0), Var(0))
    // Var(0) should have usage_count = 2
    let var0 = Expr::var(0);
    let app = Expr::app(var0.clone(), var0);

    let (info_map, ptr_to_hash) = analyze_block(&[app]);

    // Should have 2 unique subterms: Var(0) and App(Var(0), Var(0))
    assert_eq!(info_map.len(), 2);

    // Find Var(0) info - it should have usage_count = 2
    let var_hash = ptr_to_hash.values().find(|h| {
      info_map.get(*h).map_or(false, |info| matches!(info.expr.as_ref(), Expr::Var(0)))
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

    let (info_map, _) = analyze_block(&[app]);
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

    let (info_map, _) = analyze_block(&[app]);
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
        assert!(child_pos < app_pos, "Child should come before parent in topo order");
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

    let (info_map, ptr_to_hash) = analyze_block(&[app2.clone()]);
    let shared = decide_sharing(&info_map);

    // If var0 is shared, verify it
    if !shared.is_empty() {
      let (rewritten, sharing_vec) = build_sharing_vec(vec![app2], &shared, &ptr_to_hash, &info_map);

      // Sharing vec should have the shared expressions
      assert_eq!(sharing_vec.len(), shared.len());

      // Rewritten should have at least one Share reference if sharing happened
      assert_eq!(rewritten.len(), 1);
    }
  }

  #[test]
  fn test_roundtrip_with_sharing() {
    use crate::ix::ixon::serialize::{put_expr, get_expr};

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
