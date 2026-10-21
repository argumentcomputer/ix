//! Static producer planning; mirrors Opt.ProducerPlan.
use crate::condense::CondensedBlocks;
use ix_common::env::Name;
use rustc_hash::{FxHashMap, FxHashSet};

type Graph = FxHashMap<Name, Vec<Name>>;
pub type Refusals = FxHashMap<Name, FxHashMap<Name, String>>;

fn reach(graph: &Graph, start: &Name, bound: usize) -> FxHashSet<Name> {
  let mut seen = FxHashSet::from_iter([start.clone()]);
  let mut queue = vec![start.clone()];
  for i in 0..bound {
    let Some(n) = queue.get(i).cloned() else { break };
    for next in graph.get(&n).into_iter().flatten() {
      if seen.insert(next.clone()) {
        queue.push(next.clone());
      }
    }
  }
  seen
}

/// Propagate requirements through the existing graph after clique-owner union.
/// Project onto producers: Q->P iff Q reaches a caller C proposing C->P;
/// reachability includes Q=C. Remove all proposed edges whose Q and P lie
/// in one projected SCC simultaneously, including singleton self-loops.
/// Every new cycle alternates existing paths with proposed edges, so this
/// leaves the original DAG plus acyclic additions, independent of iteration.
/// Returned refusals apply to actual rewrites, never to unrelated recursor uses.
pub fn plan(
  blocks: &mut CondensedBlocks,
  seeds: Vec<(Name, Name)>,
) -> Refusals {
  if seeds.is_empty() {
    return Refusals::default();
  }
  let mut base = Graph::default();
  let mut reverse = Graph::default();
  for (lo, refs) in &blocks.block_refs {
    let deps: FxHashSet<Name> = refs
      .iter()
      .filter_map(|n| blocks.low_links.get(n))
      .filter(|p| *p != lo)
      .cloned()
      .collect();
    for p in &deps {
      reverse.entry(p.clone()).or_default().push(lo.clone());
    }
    base.insert(lo.clone(), deps.into_iter().collect());
  }
  let mut required = Vec::new();
  let mut seen = FxHashSet::default();
  let mut producers = FxHashSet::default();
  for pair in seeds {
    if seen.insert(pair.clone()) {
      producers.insert(pair.1.clone());
      required.push(pair);
    }
  }
  for i in 0..blocks.blocks.len() * producers.len() {
    let Some((caller, producer)) = required.get(i).cloned() else { break };
    for parent in reverse.get(&caller).into_iter().flatten() {
      let pair = (parent.clone(), producer.clone());
      if seen.insert(pair.clone()) {
        required.push(pair);
      }
    }
  }
  let old_reach: FxHashMap<Name, FxHashSet<Name>> = producers
    .iter()
    .filter_map(|p| {
      blocks
        .low_links
        .get(p)
        .map(|lo| (p.clone(), reach(&base, lo, blocks.blocks.len())))
    })
    .collect();
  let mut projected = Graph::default();
  for q in &producers {
    let next: FxHashSet<Name> = required
      .iter()
      .filter(|(caller, p)| {
        blocks.low_links.contains_key(p)
          && old_reach.get(q).is_some_and(|s| s.contains(caller))
      })
      .map(|(_, p)| p.clone())
      .collect();
    projected.insert(q.clone(), next.into_iter().collect());
  }
  let reachable: FxHashMap<Name, FxHashSet<Name>> = producers
    .iter()
    .map(|p| (p.clone(), reach(&projected, p, producers.len())))
    .collect();
  let mut refused_by_block = Refusals::default();
  for (caller, p) in required {
    let reason = if !blocks.low_links.contains_key(&p) {
      Some(format!("producer {} is outside the grounded input", p.pretty()))
    } else if producers.iter().any(|q| {
      old_reach.get(q).is_some_and(|s| s.contains(&caller))
        && reachable.get(&p).is_some_and(|s| s.contains(q))
    }) {
      let mut cycle: Vec<String> = producers
        .iter()
        .filter(|q| {
          reachable.get(&p).is_some_and(|s| s.contains(*q))
            && reachable.get(*q).is_some_and(|s| s.contains(&p))
        })
        .map(Name::pretty)
        .collect();
      cycle.sort();
      Some(format!(
        "producer {} would close a dependency cycle through [{}]",
        p.pretty(),
        cycle.join(", ")
      ))
    } else {
      None
    };
    if let Some(reason) = reason {
      refused_by_block.entry(caller).or_default().insert(p, reason);
    } else {
      blocks.block_refs.entry(caller).or_default().insert(p);
    }
  }
  let mut refused = Refusals::default();
  for (caller, reasons) in refused_by_block {
    for n in blocks.blocks.get(&caller).into_iter().flatten() {
      refused.insert(n.clone(), reasons.clone());
    }
  }
  refused
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::compile::pass3::expr::dotted;

  fn graph(names: &[Name], edges: &[(Name, Name)]) -> CondensedBlocks {
    let mut out = CondensedBlocks {
      low_links: names.iter().map(|n| (n.clone(), n.clone())).collect(),
      blocks: names
        .iter()
        .map(|n| (n.clone(), FxHashSet::from_iter([n.clone()])))
        .collect(),
      block_refs: names
        .iter()
        .map(|n| (n.clone(), FxHashSet::default()))
        .collect(),
    };
    for (a, b) in edges {
      out.block_refs.get_mut(a).unwrap().insert(b.clone());
    }
    out
  }

  #[test]
  fn cycles_are_removed_simultaneously_with_zero_length_paths() {
    let (p, q, a, b) = (dotted("P"), dotted("Q"), dotted("A"), dotted("B"));
    let mut single = graph(std::slice::from_ref(&p), &[]);
    let blocked = plan(&mut single, vec![(p.clone(), p.clone())]);
    assert!(blocked[&p].contains_key(&p));
    assert!(single.block_refs[&p].is_empty());
    let base = || {
      graph(
        &[p.clone(), q.clone(), a.clone(), b.clone()],
        &[(p.clone(), a.clone()), (q.clone(), b.clone())],
      )
    };
    let mut forward = base();
    let mut backward = base();
    let left =
      plan(&mut forward, vec![(a.clone(), q.clone()), (b.clone(), p.clone())]);
    let right =
      plan(&mut backward, vec![(b.clone(), p.clone()), (a.clone(), q.clone())]);
    assert_eq!(left, right);
    assert!(left[&a].contains_key(&q) && left[&b].contains_key(&p));
    assert!(!forward.block_refs[&a].contains(&q));
    assert!(!forward.block_refs[&b].contains(&p));
    assert_eq!(forward.block_refs, backward.block_refs);
  }

  #[test]
  fn requirements_reach_callers_and_missing_producers_never_make_edges() {
    let (p, a, b) = (dotted("P"), dotted("A"), dotted("B"));
    let mut base =
      graph(&[p.clone(), a.clone(), b.clone()], &[(b.clone(), a.clone())]);
    assert!(plan(&mut base, vec![(a.clone(), p.clone())]).is_empty());
    assert!(
      base.block_refs[&a].contains(&p) && base.block_refs[&b].contains(&p)
    );
    let mut missing = graph(std::slice::from_ref(&a), &[]);
    let blocked = plan(&mut missing, vec![(a.clone(), p.clone())]);
    assert!(blocked[&a][&p].contains("outside the grounded input"));
    assert!(missing.block_refs[&a].is_empty());
  }
}
