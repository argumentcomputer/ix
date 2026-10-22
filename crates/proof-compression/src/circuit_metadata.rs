//! Structural validation shared by the FRI and KZG verifier-key codecs.
use multi_stark::expr::Source;
use multi_stark::graph::Node;
use multi_stark::lookup::{
  MAX_LOOKUP_GROUP, logup_constraint_count, stage2_width,
};
use multi_stark::system::Circuit;
use multi_stark::traits::Field;

pub(crate) fn validate_circuit<F: Field>(
  c: &Circuit<F>,
  dimension: usize,
) -> Result<(), &'static str> {
  if !(1..=MAX_LOOKUP_GROUP).contains(&c.lookup_group_size) {
    return Err("lookup group size");
  }
  if c.num_lookups != c.graph.lookups.len()
    || c.stage_2_width
      != stage2_width(c.num_lookups, c.lookup_group_size, dimension)
    || c.num_publics != 4 * dimension
  {
    return Err("lookup/public widths");
  }
  let g = &c.graph;
  if g.nodes.len() != g.degrees.len() || g.lookup_prefix_len > g.nodes.len() {
    return Err("graph dimensions");
  }
  for (i, n) in g.nodes.iter().enumerate() {
    let degree = |id: multi_stark::graph::NodeId| {
      g.degrees
        .get(id.index())
        .filter(|_| id.index() < i)
        .copied()
        .ok_or("graph topology")
    };
    let d = match *n {
      Node::Const(_) | Node::IsTransition => 0,
      Node::Public(p) => {
        if p as usize >= c.num_publics {
          return Err("public index");
        }
        0
      },
      Node::IsFirstRow | Node::IsLastRow => 1,
      Node::Var(col) => {
        let width = match col.source {
          Source::Main => c.main_width,
          Source::Stage2 => c.stage_2_width,
          Source::Preprocessed => c.preprocessed_width,
        };
        if col.index as usize >= width {
          return Err("column index");
        }
        1
      },
      Node::Add(a, b) | Node::Sub(a, b) => degree(a)?.max(degree(b)?),
      Node::Mul(a, b) => {
        degree(a)?.checked_add(degree(b)?).ok_or("degree overflow")?
      },
      Node::Neg(a) => degree(a)?,
    };
    if g.degrees[i] != d {
      return Err("node degree");
    }
  }
  if g.zeros.iter().any(|n| n.index() >= g.nodes.len())
    || g.lookups.iter().any(|l| {
      l.args
        .iter()
        .chain(std::iter::once(&l.multiplicity))
        .any(|n| n.index() >= g.lookup_prefix_len)
    })
  {
    return Err("graph roots");
  }
  let mut lookup_degree = 1u64;
  for group in g.lookups.chunks(c.lookup_group_size) {
    let degrees: Vec<_> = group
      .iter()
      .map(|l| {
        l.args
          .iter()
          .map(|n| u64::from(g.degrees[n.index()]))
          .max()
          .unwrap_or(0)
      })
      .collect();
    let sum: u64 = degrees.iter().sum();
    lookup_degree = lookup_degree.max(sum + 1);
    for (l, &degree) in group.iter().zip(&degrees) {
      lookup_degree = lookup_degree
        .max(u64::from(g.degrees[l.multiplicity.index()]) + sum - degree);
    }
  }
  let lookup_degree = u32::try_from(lookup_degree)
    .map_err(|_overflow| "lookup degree overflow")?;
  let max = g.zeros.iter().map(|n| g.degrees[n.index()]).max().unwrap_or(0);
  if g.max_constraint_degree != max
    || c.max_constraint_degree != max.max(lookup_degree) as usize
    || c.constraint_count
      != g.zeros.len()
        + logup_constraint_count(c.num_lookups, c.lookup_group_size, dimension)
  {
    return Err("constraint metadata");
  }
  Ok(())
}
