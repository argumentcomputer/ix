//! Computes strongly connected components (SCCs) using iterative Tarjan's algorithm.
//!
//! Produces a condensation of the reference graph: each SCC becomes a single block.
//! Used to identify mutual definition groups for the compilation pipeline.
//!
//! [`compute_sccs`] interns the names to dense `u32` ids, builds the
//! adjacency in compressed-sparse-row form and runs Tarjan over arrays.
//! [`compute_sccs_reference`] is the original name-keyed implementation; the
//! two agree in every observable respect (same components, same roots, and
//! the same iteration order of every map and set in the result), which the
//! tests here and `rs_compute_sccs_reference_diff` check.

use std::sync::Arc;

use rayon::prelude::*;
use rustc_hash::FxHashMap;

use ix_common::FxIndexSet;
use ix_common::env::{Name, NameData};

use crate::graph::{NameSet, RefMap};

/// The condensation of a reference graph into strongly connected components.
pub struct CondensedBlocks {
  /// Maps each name to the representative (low-link root) of its SCC.
  pub low_links: FxHashMap<Name, Name>,
  /// Maps each SCC representative to the set of names in that component.
  pub blocks: RefMap,
  /// Maps each SCC representative to the set of names referenced outside its component.
  pub block_refs: RefMap,
}

/// Sentinel for "not yet visited" (`index`) and "no component yet"
/// (`comp_of`).
const NONE: u32 = u32::MAX;

/// A node id or component id known to be below [`NONE`].
#[inline]
#[allow(clippy::cast_possible_truncation)]
fn dense(i: usize) -> u32 {
  debug_assert!(i < NONE as usize);
  i as u32
}

/// Compute strongly connected components using an iterative Tarjan's
/// algorithm over dense integer ids.
///
/// The result is identical to [`compute_sccs_reference`], including the
/// iteration order of `low_links`, `blocks` and `block_refs` and of every
/// set inside them:
///
/// * node ids follow `refs` iteration order and each adjacency list follows
///   its set's iteration order, so the depth-first search visits nodes, and
///   numbers them, exactly as the name-keyed search did; hence the same
///   roots and the same components, emitted in the same order;
/// * every set and map of the result is built from an empty one by the same
///   sequence of `insert`s as before (members in stack-pop order; low links
///   and external references in the member set's iteration order), so the
///   hash tables end up with the same layout.
///
/// Names are resolved to ids by their blake3 hash, which identifies a
/// `Name` (its `Ord` already compares by it) and, unlike `Name` equality,
/// never walks two separately allocated prefix chains.
///
/// Every name referenced in `refs` must be a key of `refs`; like the
/// reference implementation, this panics otherwise.
pub fn compute_sccs(refs: &RefMap) -> CondensedBlocks {
  // Dense ids, in the order the search takes its start nodes.
  let nodes: Vec<(&Name, &NameSet)> = refs.iter().collect();
  let n = nodes.len();
  assert!(n < NONE as usize, "compute_sccs: too many nodes ({n})");
  let mut ids: FxHashMap<&[u8; 32], u32> =
    FxHashMap::with_capacity_and_hasher(n, Default::default());
  for (i, (name, _)) in nodes.iter().enumerate() {
    ids.insert(name.get_hash().as_bytes(), dense(i));
  }

  // Compressed-sparse-row adjacency: the out-neighbours of node `v` are
  // `targets[offsets[v]..offsets[v + 1]]`, in its set's iteration order.
  let mut offsets: Vec<usize> = Vec::with_capacity(n + 1);
  offsets.push(0);
  let mut total = 0usize;
  for (_, set) in &nodes {
    total += set.len();
    offsets.push(total);
  }
  let mut targets: Vec<u32> = vec![0; total];
  {
    const CHUNK: usize = 4096;
    let mut parts: Vec<(usize, &mut [u32])> = Vec::new();
    let mut rest: &mut [u32] = &mut targets;
    let mut lo = 0;
    while lo < n {
      let hi = (lo + CHUNK).min(n);
      let (head, tail) = rest.split_at_mut(offsets[hi] - offsets[lo]);
      parts.push((lo, head));
      rest = tail;
      lo = hi;
    }
    parts.into_par_iter().for_each(|(lo, out)| {
      let hi = (lo + CHUNK).min(n);
      let mut k = 0;
      for (name, set) in &nodes[lo..hi] {
        for r in set.iter() {
          let Some(&id) = ids.get(r.get_hash().as_bytes()) else {
            panic!(
              "compute_sccs: {} references {}, which is not in the graph",
              name.pretty(),
              r.pretty()
            )
          };
          out[k] = id;
          k += 1;
        }
      }
    });
  }
  drop(ids);

  // Tarjan over the arrays. `comp_of[v] == NONE` for a visited node means
  // it is still on the Tarjan stack.
  let mut index = vec![NONE; n];
  let mut low = vec![0u32; n];
  let mut comp_of = vec![NONE; n];
  let mut stack: Vec<u32> = Vec::new();
  let mut work: Vec<(u32, usize)> = Vec::new();
  let mut next_index = 0u32;
  // Members of component `c` in stack-pop order (its root last):
  // `members[bounds[c]..bounds[c + 1]]`.
  let mut members: Vec<u32> = Vec::with_capacity(n);
  let mut bounds: Vec<usize> = vec![0];

  for start in 0..n {
    if index[start] != NONE {
      continue;
    }
    let start = dense(start);
    index[start as usize] = next_index;
    low[start as usize] = next_index;
    next_index += 1;
    stack.push(start);
    work.push((start, offsets[start as usize]));

    while let Some(top) = work.last_mut() {
      let (v, edge) = *top;
      let vu = v as usize;
      if edge < offsets[vu + 1] {
        top.1 += 1;
        let w = targets[edge];
        let wu = w as usize;
        if index[wu] == NONE {
          // Explore a new neighbour.
          index[wu] = next_index;
          low[wu] = next_index;
          next_index += 1;
          stack.push(w);
          work.push((w, offsets[wu]));
        } else if comp_of[wu] == NONE {
          // `w` is on the stack.
          low[vu] = low[vu].min(index[wu]);
        }
      } else {
        // All neighbours processed: pop, and update the parent.
        work.pop();
        if let Some(&(parent, _)) = work.last() {
          let pu = parent as usize;
          low[pu] = low[pu].min(low[vu]);
        }
        if low[vu] == index[vu] {
          // `v` is the root of a component: pop it off the stack.
          let c = dense(bounds.len() - 1);
          loop {
            let x = stack.pop().expect("compute_sccs: Tarjan stack underflow");
            comp_of[x as usize] = c;
            members.push(x);
            if x == v {
              break;
            }
          }
          bounds.push(members.len());
        }
      }
    }
  }
  drop(index);
  drop(low);

  // Per component, in parallel: the member set (inserted in pop order, as
  // before), the members in that set's iteration order when there are
  // several, and the set of external references (members in set order,
  // each member's references in its set's order).
  let n_comps = bounds.len() - 1;
  let per_comp: Vec<(NameSet, Option<Vec<u32>>, NameSet)> = (0..n_comps)
    .into_par_iter()
    .map(|c| {
      let cm = &members[bounds[c]..bounds[c + 1]];
      let mut component = NameSet::default();
      for &x in cm {
        component.insert(nodes[x as usize].0.clone());
      }
      let set_order: Option<Vec<u32>> = (cm.len() > 1).then(|| {
        // The set holds clones of the members' keys: map each back to its
        // id through the shared allocation.
        let by_ptr: FxHashMap<*const NameData, u32> = cm
          .iter()
          .map(|&x| (Arc::as_ptr(&nodes[x as usize].0.0), x))
          .collect();
        component.iter().map(|name| by_ptr[&Arc::as_ptr(&name.0)]).collect()
      });
      let c32 = dense(c);
      let mut all_refs = NameSet::default();
      let order: &[u32] = set_order.as_deref().unwrap_or(cm);
      for &x in order {
        let xu = x as usize;
        for &t in &targets[offsets[xu]..offsets[xu + 1]] {
          if comp_of[t as usize] != c32 {
            all_refs.insert(nodes[t as usize].0.clone());
          }
        }
      }
      (component, set_order, all_refs)
    })
    .collect();

  // The three result maps, each by the same insertion sequence as before
  // (no pre-sizing: the table layout, hence the iteration order, depends on
  // the growth history). They are independent, so build them concurrently.
  let mut comp_sets: Vec<NameSet> = Vec::with_capacity(n_comps);
  let mut set_orders: Vec<Option<Vec<u32>>> = Vec::with_capacity(n_comps);
  let mut ref_sets: Vec<NameSet> = Vec::with_capacity(n_comps);
  for (component, set_order, all_refs) in per_comp {
    comp_sets.push(component);
    set_orders.push(set_order);
    ref_sets.push(all_refs);
  }
  let root =
    |c: usize| -> &Name { nodes[members[bounds[c + 1] - 1] as usize].0 };
  let (blocks, (low_links, block_refs)) = rayon::join(
    || {
      let mut blocks = RefMap::default();
      for (c, component) in comp_sets.into_iter().enumerate() {
        blocks.insert(root(c).clone(), component);
      }
      blocks
    },
    || {
      rayon::join(
        || {
          let mut low_links: FxHashMap<Name, Name> = FxHashMap::default();
          for (c, set_order) in set_orders.iter().enumerate() {
            let v = root(c);
            let order: &[u32] = match set_order {
              Some(order) => order,
              None => &members[bounds[c]..bounds[c + 1]],
            };
            for &x in order {
              low_links.insert(nodes[x as usize].0.clone(), v.clone());
            }
          }
          low_links
        },
        || {
          let mut block_refs = RefMap::default();
          for (c, all_refs) in ref_sets.into_iter().enumerate() {
            block_refs.insert(root(c).clone(), all_refs);
          }
          block_refs
        },
      )
    },
  );
  CondensedBlocks { blocks, low_links, block_refs }
}

/// The original name-keyed iterative Tarjan, kept as the specification
/// that [`compute_sccs`] is tested against. Not used by the compiler.
#[doc(hidden)]
pub fn compute_sccs_reference(refs: &RefMap) -> CondensedBlocks {
  fn neighbors(refs: &RefMap, n: &Name) -> Vec<Name> {
    refs.get(n).unwrap().iter().cloned().collect()
  }

  struct Frame {
    node: Name,
    neighbors: Vec<Name>,
    /// Index of the next neighbor to visit.
    idx: usize,
  }

  let mut index = FxHashMap::default();
  let mut lowlink = FxHashMap::default();
  let mut stack = FxIndexSet::default();
  let mut next_index = 0usize;

  let mut blocks = RefMap::default();
  let mut block_low_links = FxHashMap::default();
  let mut block_refs = RefMap::default();

  let mut work = Vec::<Frame>::new();

  for start in refs.keys() {
    if index.contains_key(start) {
      continue;
    }

    work.push(Frame {
      node: start.clone(),
      neighbors: neighbors(refs, start),
      idx: 0,
    });

    while let Some(frame) = work.last_mut() {
      let v = &frame.node;

      if !index.contains_key(v) {
        index.insert(v.clone(), next_index);
        lowlink.insert(v.clone(), next_index);
        next_index += 1;
        stack.insert(v.clone());
      }

      if frame.idx < frame.neighbors.len() {
        let w = frame.neighbors[frame.idx].clone();
        frame.idx += 1;

        if !index.contains_key(&w) {
          // Explore new neighbor.
          work.push(Frame { neighbors: neighbors(refs, &w), node: w, idx: 0 });
        } else if stack.contains(&w) {
          // w is on stack.
          let low_v = *lowlink.get(v).unwrap();
          let idx_w = *index.get(&w).unwrap();
          lowlink.insert(v.clone(), low_v.min(idx_w));
        }
      } else {
        // All neighbors processed. Pop and process.
        let frame = work.pop().unwrap();
        let v = frame.node;

        // Update parent's lowlink.
        if let Some(parent) = work.last_mut() {
          let low_parent = *lowlink.get(&parent.node).unwrap();
          let low_v = *lowlink.get(&v).unwrap();
          lowlink.insert(parent.node.clone(), low_parent.min(low_v));
        }

        // Root of SCC?
        if lowlink[&v] == index[&v] {
          let mut component = NameSet::default();

          // Pop nodes from stack until we reach v.
          while let Some(node) = stack.pop() {
            component.insert(node.clone());
            if node == v {
              break;
            }
          }
          blocks.insert(v.clone(), component.clone());

          // Insert all nodes in the component directly into the result.
          let mut all_refs = NameSet::default();
          for node in &component {
            block_low_links.insert(node.clone(), v.clone());
            for r in refs.get(node).unwrap() {
              if !component.contains(r) && refs.contains_key(r) {
                all_refs.insert(r.clone());
              }
            }
          }
          block_refs.insert(v.clone(), all_refs);
        }
      }
    }
  }
  CondensedBlocks { blocks, low_links: block_low_links, block_refs }
}

/// Describe the first difference between two condensations, comparing
/// every map and set in iteration order; `None` when they are identical.
#[doc(hidden)]
pub fn condensed_difference(
  a: &CondensedBlocks,
  b: &CondensedBlocks,
) -> Option<String> {
  fn ref_map_diff(what: &str, a: &RefMap, b: &RefMap) -> Option<String> {
    if a.len() != b.len() {
      return Some(format!("{what}: {} vs {} entries", a.len(), b.len()));
    }
    for (i, ((ka, va), (kb, vb))) in a.iter().zip(b.iter()).enumerate() {
      if ka != kb {
        return Some(format!(
          "{what}: entry {i} has key {} vs {}",
          ka.pretty(),
          kb.pretty()
        ));
      }
      if !va.iter().eq(vb.iter()) {
        return Some(format!(
          "{what}: entry {i} ({}) differs in its members or their order",
          ka.pretty()
        ));
      }
    }
    None
  }
  if a.low_links.len() != b.low_links.len() {
    return Some(format!(
      "low_links: {} vs {} entries",
      a.low_links.len(),
      b.low_links.len()
    ));
  }
  for (i, (pa, pb)) in a.low_links.iter().zip(b.low_links.iter()).enumerate() {
    if pa != pb {
      return Some(format!(
        "low_links: entry {i} is ({}, {}) vs ({}, {})",
        pa.0.pretty(),
        pa.1.pretty(),
        pb.0.pretty(),
        pb.1.pretty()
      ));
    }
  }
  ref_map_diff("blocks", &a.blocks, &b.blocks)
    .or_else(|| ref_map_diff("block_refs", &a.block_refs, &b.block_refs))
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::slice;

  fn n(s: &str) -> Name {
    Name::str(Name::anon(), s.to_string())
  }

  fn map_of(pairs: &[(&Name, &[Name])]) -> RefMap {
    let mut map = RefMap::default();
    for (k, vs) in pairs {
      map.insert((*k).clone(), vs.iter().cloned().collect());
    }
    map
  }

  fn scc_to_vec(map: &CondensedBlocks) -> Vec<Vec<Name>> {
    let mut seen = FxIndexSet::default();
    let mut sccs = Vec::new();
    for (k, lo) in map.low_links.iter() {
      let set = map.blocks.get(lo).unwrap();
      if !seen.contains(k) {
        let mut names: Vec<_> = set.iter().cloned().collect();
        names.sort();
        sccs.push(names);
        seen.extend(set.iter().cloned());
      }
    }
    sccs.sort();
    sccs
  }

  /// Both implementations on `g`: identical results, orders included.
  fn sccs_agree(g: &RefMap) -> CondensedBlocks {
    let new = compute_sccs(g);
    let old = compute_sccs_reference(g);
    if let Some(diff) = condensed_difference(&old, &new) {
      panic!("compute_sccs differs from the reference: {diff}");
    }
    new
  }

  #[test]
  fn single_node() {
    let a = n("A");
    let g = map_of(&[(&a, &[])]);
    let sccs = sccs_agree(&g);
    assert_eq!(scc_to_vec(&sccs), vec![vec![n("A")]]);
  }

  #[test]
  fn simple_cycle() {
    let a = n("A");
    let b = n("B");
    let g = map_of(&[(&a, slice::from_ref(&b)), (&b, slice::from_ref(&a))]);
    let sccs = sccs_agree(&g);
    assert_eq!(scc_to_vec(&sccs), vec![vec![n("A"), n("B")]]);
  }

  #[test]
  fn chain_no_cycle() {
    let a = n("A");
    let b = n("B");
    let c = n("C");
    let g = map_of(&[
      (&a, slice::from_ref(&b)),
      (&b, slice::from_ref(&c)),
      (&c, &[]),
    ]);
    let sccs = sccs_agree(&g);
    let mut res = vec![vec![n("A")], vec![n("B")], vec![n("C")]];
    res.sort();
    assert_eq!(scc_to_vec(&sccs), res);
  }

  #[test]
  fn two_cycles_connected() {
    let a = n("A");
    let b = n("B");
    let c = n("C");
    let d = n("D");
    let g = map_of(&[
      (&a, slice::from_ref(&b)),
      (&b, &[a.clone(), c.clone()]),
      (&c, slice::from_ref(&d)),
      (&d, slice::from_ref(&c)),
    ]);
    let sccs = sccs_agree(&g);
    let mut res = vec![vec![n("A"), n("B")], vec![n("C"), n("D")]];
    for scc in &mut res {
      scc.sort();
    }
    res.sort();
    assert_eq!(scc_to_vec(&sccs), res);
  }

  #[test]
  fn complex_graph() {
    let a = n("A");
    let b = n("B");
    let c = n("C");
    let d = n("D");
    let e = n("E");
    let f = n("F");
    let g = n("G");
    let h = n("H");

    let graph = map_of(&[
      (&a, slice::from_ref(&b)),
      (&b, &[c.clone(), e.clone(), f.clone()]),
      (&c, &[d.clone(), g.clone()]),
      (&d, &[c.clone(), h.clone()]),
      (&e, &[a.clone(), f.clone()]),
      (&f, slice::from_ref(&g)),
      (&g, slice::from_ref(&f)),
      (&h, &[d.clone(), g.clone()]),
    ]);

    let sccs = sccs_agree(&graph);
    let mut res = vec![
      vec![n("A"), n("B"), n("E")],
      vec![n("C"), n("D"), n("H")],
      vec![n("F"), n("G")],
    ];
    for scc in &mut res {
      scc.sort();
    }
    res.sort();
    assert_eq!(scc_to_vec(&sccs), res,);
  }

  #[test]
  fn empty_graph() {
    let sccs = sccs_agree(&RefMap::default());
    assert!(sccs.blocks.is_empty());
    assert!(sccs.low_links.is_empty());
    assert!(sccs.block_refs.is_empty());
  }

  /// SplitMix64: a small deterministic generator for the random graphs.
  struct Rng(u64);
  impl Rng {
    fn next(&mut self) -> u64 {
      self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
      let mut z = self.0;
      z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
      z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
      z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
      usize::try_from(self.next() % (n as u64)).unwrap()
    }
  }

  /// A random graph on `nodes` names. Edges are drawn either uniformly or
  /// mostly "backwards" (towards smaller ids, so that most nodes are
  /// singletons, as in a real reference graph, with a few long cycles from
  /// the forward edges). Names are built as a hierarchy, sometimes with
  /// separately allocated but equal copies, and inserted in a random order.
  fn random_graph(rng: &mut Rng, nodes: usize, edges: usize) -> RefMap {
    let mut names: Vec<Name> = Vec::with_capacity(nodes);
    for i in 0..nodes {
      let name = if i > 0 && rng.below(3) == 0 {
        let parent = names[rng.below(i)].clone();
        Name::str(parent, format!("x{i}"))
      } else {
        n(&format!("N{i}"))
      };
      names.push(name);
    }
    let backwards = rng.below(2) == 0;
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); nodes];
    for _ in 0..edges {
      let from = rng.below(nodes);
      let to = if backwards && from > 0 && rng.below(10) != 0 {
        rng.below(from)
      } else {
        rng.below(nodes)
      };
      adj[from].push(to);
    }
    let mut order: Vec<usize> = (0..nodes).collect();
    for i in (1..nodes).rev() {
      order.swap(i, rng.below(i + 1));
    }
    let mut map = RefMap::default();
    for i in order {
      let set: NameSet = adj[i]
        .iter()
        .map(|&t| {
          // A structurally equal but separately allocated copy, half of
          // the time: lookups must go by value, not by pointer.
          if rng.below(2) == 0 {
            names[t].clone()
          } else {
            match names[t].as_data() {
              NameData::Str(pre, s, _) => Name::str(pre.clone(), s.clone()),
              _ => names[t].clone(),
            }
          }
        })
        .collect();
      map.insert(names[i].clone(), set);
    }
    map
  }

  #[test]
  fn random_graphs_match_reference() {
    let mut rng = Rng(0x1d_c0de);
    let mut multi = 0usize;
    for round in 0..400 {
      let nodes = 1 + rng.below(if round % 10 == 0 { 3000 } else { 120 });
      let edges = rng.below(4 * nodes + 1);
      let g = random_graph(&mut rng, nodes, edges);
      let sccs = sccs_agree(&g);
      multi += sccs.blocks.values().filter(|b| b.len() > 1).count();
      // Every name has exactly one root, and the blocks partition the keys.
      assert_eq!(sccs.low_links.len(), g.len());
      let members: usize = sccs.blocks.values().map(|b| b.len()).sum();
      assert_eq!(members, g.len());
    }
    // The generator must actually produce non-trivial components.
    assert!(multi > 100, "only {multi} multi-member components");
  }

  #[test]
  #[should_panic(expected = "not in the graph")]
  fn missing_reference_panics() {
    let a = n("A");
    let b = n("B");
    compute_sccs(&map_of(&[(&a, slice::from_ref(&b))]));
  }
}
