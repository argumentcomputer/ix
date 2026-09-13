// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use multi_stark::{
  expr::Source,
  graph::{Node, NodeId},
  lookup::Lookup,
};

use crate::G;

#[derive(Clone, Copy)]
pub(crate) struct GraphWidths {
  pub preprocessed: usize,
  pub main: usize,
  pub stage2: usize,
  pub publics: usize,
}

/// Check every read made by a full sweep and by the lookup-prefix sweep.
/// The latter has no stage-2 values. Check roots before deriving the prefix,
/// and children before degree recomputation or the native unchecked sweep.
pub(crate) fn checked_graph_prefix(
  nodes: &[Node<G>],
  zeros: &[NodeId],
  lookups: &[Lookup<NodeId>],
  widths: GraphWidths,
) -> Option<usize> {
  let in_bounds = |id: NodeId| id.index() < nodes.len();
  if !zeros.iter().copied().all(in_bounds)
    || !lookups.iter().all(|lookup| {
      in_bounds(lookup.multiplicity)
        && lookup.args.iter().copied().all(in_bounds)
    })
  {
    return None;
  }
  let prefix = lookups
    .iter()
    .flat_map(|lookup| {
      std::iter::once(lookup.multiplicity).chain(lookup.args.iter().copied())
    })
    .map(|id| id.index() + 1)
    .max()
    .unwrap_or(0);
  for (index, node) in nodes.iter().enumerate() {
    let valid = match *node {
      Node::Const(_)
      | Node::IsFirstRow
      | Node::IsLastRow
      | Node::IsTransition => true,
      Node::Var(col) => {
        let width = match col.source {
          Source::Preprocessed => widths.preprocessed,
          Source::Main => widths.main,
          Source::Stage2 => {
            if index < prefix {
              return None;
            }
            widths.stage2
          },
        };
        (col.index as usize) < width
      },
      Node::Public(public) => (public as usize) < widths.publics,
      Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
        a.index() < index && b.index() < index
      },
      Node::Neg(a) => a.index() < index,
    };
    if !valid {
      return None;
    }
  }
  Some(prefix)
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::{
    expr::{ColRef, RowOffset},
    p3_field::PrimeCharacteristicRing,
  };
  use std::{
    fs::File,
    io::{self, Write},
  };

  fn node_choices() -> Vec<Node<G>> {
    let indices = [0, 1, 3, 7, 8, u16::MAX.into(), u32::MAX];
    let mut choices = vec![
      Node::Const(G::ZERO),
      Node::Const(G::ONE),
      Node::Const(-G::ONE),
      Node::Const(G::from_u64(65536)),
      Node::IsFirstRow,
      Node::IsLastRow,
      Node::IsTransition,
    ];
    for source in [Source::Preprocessed, Source::Main, Source::Stage2] {
      for offset in [RowOffset::Current, RowOffset::Next] {
        for index in indices {
          choices.push(Node::Var(ColRef { source, offset, index }));
        }
      }
    }
    for index in indices {
      choices.push(Node::Public(index));
    }
    for left in indices {
      for right in indices {
        choices.extend([
          Node::Add(NodeId(left), NodeId(right)),
          Node::Sub(NodeId(left), NodeId(right)),
          Node::Mul(NodeId(left), NodeId(right)),
        ]);
      }
    }
    for index in indices {
      choices.push(Node::Neg(NodeId(index)));
    }
    assert_eq!(choices.len(), 210);
    choices
  }

  fn write_shapes(out: &mut Vec<u8>, nodes: &[Node<G>]) -> usize {
    let count = u32::try_from(nodes.len()).expect("small test graph");
    let last = count.saturating_sub(1);
    for width in [0, 1, 4, 8] {
      let widths = GraphWidths {
        preprocessed: width,
        main: width + 1,
        stage2: width + 2,
        publics: width,
      };
      for (zeros, lookups) in [
        (vec![], vec![]),
        (vec![NodeId(0)], vec![]),
        (vec![NodeId(last)], vec![]),
        (vec![NodeId(count)], vec![]),
        (vec![], vec![Lookup { multiplicity: NodeId(0), args: vec![] }]),
        (
          vec![],
          vec![Lookup { multiplicity: NodeId(last), args: vec![NodeId(0)] }],
        ),
        (
          vec![],
          vec![Lookup { multiplicity: NodeId(0), args: vec![NodeId(count)] }],
        ),
      ] {
        match checked_graph_prefix(nodes, &zeros, &lookups, widths) {
          None => out.push(0),
          Some(prefix) => {
            out.push(1);
            out.extend_from_slice(&(prefix as u64).to_le_bytes());
          },
        }
      }
    }
    28
  }

  #[test]
  fn graph_shape_snapshot() -> io::Result<()> {
    let mut out = b"Aiur graph shapes v1\n".to_vec();
    let mut checked = write_shapes(&mut out, &[]);
    for count in [1, 2, 4, 8] {
      for index in 0..count {
        for node in node_choices() {
          let mut nodes = vec![Node::Const(G::ZERO); count];
          nodes[index] = node;
          checked += write_shapes(&mut out, &nodes);
        }
      }
    }
    assert_eq!(checked, 88_228);
    if let Some(path) = std::env::var_os("IX_GRAPH_SHAPE_SNAPSHOT") {
      File::create(path)?.write_all(&out)?;
    }
    eprintln!("graph shapes: {checked} checked layouts");
    Ok(())
  }
}
