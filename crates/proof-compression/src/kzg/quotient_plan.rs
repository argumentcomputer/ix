//! Split quotient constraints by their fixed-column dependencies.
use std::collections::BTreeSet;

use super::Scalar;
use multi_stark::expr::Source;
use multi_stark::graph::ConstraintGraph;
use multi_stark::graph::Node;
use multi_stark::graph::NodeId;
use multi_stark::lookup::Lookup;

pub(super) struct Pass {
  pub fixed: Vec<usize>,
  pub graph: ConstraintGraph<Scalar>,
  pub weights: Vec<usize>,
  pub groups: Vec<(usize, Vec<Lookup<NodeId>>)>,
}

fn mark(graph: &ConstraintGraph<Scalar>, roots: &[NodeId]) -> Vec<bool> {
  let mut used = vec![false; graph.nodes.len()];
  for root in roots {
    used[root.index()] = true;
  }
  for i in (0..used.len()).rev() {
    if used[i] {
      match graph.nodes[i] {
        Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
          used[a.index()] = true;
          used[b.index()] = true;
        },
        Node::Neg(a) => used[a.index()] = true,
        _ => {},
      }
    }
  }
  used
}

pub(super) fn plan(
  graph: &ConstraintGraph<Scalar>,
  group_size: usize,
) -> Vec<Pass> {
  let groups = graph.lookups.len().div_ceil(group_size).max(1);
  let roots: Vec<Vec<NodeId>> = graph
    .zeros
    .iter()
    .map(|id| vec![*id])
    .chain((0..groups).map(|g| {
      graph
        .lookups
        .iter()
        .skip(g * group_size)
        .take(group_size)
        .flat_map(|l| {
          std::iter::once(l.multiplicity).chain(l.args.iter().copied())
        })
        .collect()
    }))
    .collect();
  let mut batches: Vec<(BTreeSet<usize>, Vec<usize>)> = Vec::new();
  for (index, root) in roots.iter().enumerate() {
    let used = mark(graph, root);
    let fixed: BTreeSet<_> = graph
      .nodes
      .iter()
      .zip(used)
      .filter_map(|(node, used)| match node {
        Node::Var(col) if used && col.source == Source::Preprocessed => {
          Some(col.index as usize)
        },
        _ => None,
      })
      .collect();
    // A single constraint may exceed the budget; it is never split or omitted.
    if let Some((columns, indices)) =
      batches.iter_mut().find(|(columns, _)| columns.union(&fixed).count() <= 8)
    {
      columns.extend(fixed);
      indices.push(index);
    } else {
      batches.push((fixed, vec![index]));
    }
  }
  batches
    .into_iter()
    .map(|(fixed, indices)| {
      let fixed: Vec<_> = fixed.into_iter().collect();
      let used = mark(
        graph,
        &indices
          .iter()
          .flat_map(|i| roots[*i].iter().copied())
          .collect::<Vec<_>>(),
      );
      let mut remap = vec![NodeId(u32::MAX); graph.nodes.len()];
      let mut nodes = Vec::new();
      let mut degrees = Vec::new();
      for (i, node) in graph.nodes.iter().copied().enumerate() {
        if !used[i] {
          continue;
        }
        let id = |id: NodeId| remap[id.index()];
        let node = match node {
          Node::Add(a, b) => Node::Add(id(a), id(b)),
          Node::Sub(a, b) => Node::Sub(id(a), id(b)),
          Node::Mul(a, b) => Node::Mul(id(a), id(b)),
          Node::Neg(a) => Node::Neg(id(a)),
          Node::Var(mut col) if col.source == Source::Preprocessed => {
            col.index = fixed
              .binary_search(&(col.index as usize))
              .unwrap()
              .try_into()
              .unwrap();
            Node::Var(col)
          },
          other => other,
        };
        remap[i] = NodeId(nodes.len().try_into().unwrap());
        nodes.push(node);
        degrees.push(graph.degrees[i]);
      }
      let mut zeros = Vec::new();
      let mut weights = Vec::new();
      let mut selected_groups = Vec::new();
      for index in indices {
        if index < graph.zeros.len() {
          zeros.push(remap[graph.zeros[index].index()]);
          weights.push(index);
        } else {
          let g = index - graph.zeros.len();
          selected_groups.push((
            g,
            graph
              .lookups
              .iter()
              .skip(g * group_size)
              .take(group_size)
              .map(|l| Lookup {
                multiplicity: remap[l.multiplicity.index()],
                args: l.args.iter().map(|id| remap[id.index()]).collect(),
              })
              .collect(),
          ));
        }
      }
      Pass {
        fixed,
        weights,
        groups: selected_groups,
        graph: ConstraintGraph {
          lookup_prefix_len: nodes.len(),
          nodes,
          degrees,
          zeros,
          lookups: vec![],
          max_constraint_degree: graph.max_constraint_degree,
        },
      }
    })
    .collect()
}

pub(super) fn lookup_graph(
  graph: &ConstraintGraph<Scalar>,
) -> (Vec<usize>, ConstraintGraph<Scalar>) {
  let mut graph = graph.clone();
  graph.nodes.truncate(graph.lookup_prefix_len);
  graph.degrees.truncate(graph.lookup_prefix_len);
  graph.zeros.clear();
  let fixed: Vec<_> = graph
    .nodes
    .iter()
    .filter_map(|node| match node {
      Node::Var(col) if col.source == Source::Preprocessed => {
        Some(col.index as usize)
      },
      _ => None,
    })
    .collect::<BTreeSet<_>>()
    .into_iter()
    .collect();
  for node in &mut graph.nodes {
    if let Node::Var(col) = node
      && col.source == Source::Preprocessed
    {
      col.index =
        fixed.binary_search(&(col.index as usize)).unwrap().try_into().unwrap();
    }
  }
  (fixed, graph)
}
