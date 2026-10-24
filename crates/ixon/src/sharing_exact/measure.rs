//! Bounded graph/sequence measurements shared with the reference tests.

use super::SharingError;
use super::cost::{Len, tag0_len};
use super::dag::{Node, SharingDag, TermId, ix};
use super::dict::{DenseIndex, NoWidths, all_costs};

fn internal(msg: impl Into<String>) -> SharingError {
  SharingError::Internal(msg.into())
}
fn tid(i: usize) -> TermId {
  TermId::try_from(i).unwrap_or(TermId::MAX)
}

/// Expanded occurrence counts (saturating) of every term.
pub(crate) fn occurrences(dag: &SharingDag) -> Vec<u64> {
  let nodes = dag.nodes();
  let mut occ = vec![0u64; nodes.len()];
  for &r in dag.roots() {
    occ[ix(r)] = occ[ix(r)].saturating_add(1);
  }
  // Parents have larger IDs than children: a descending sweep sees each
  // node's final count before propagating it along every child edge.
  for t in (0..nodes.len()).rev() {
    let o = occ[t];
    if o == 0 {
      continue;
    }
    for &c in nodes[t].children().as_slice() {
      occ[ix(c)] = occ[ix(c)].saturating_add(o);
    }
  }
  occ
}

pub(super) fn candidates_of(occ: &[u64], base: &[Len]) -> Vec<TermId> {
  (0..occ.len())
    .filter(|&t| occ[t] >= 2 && base[t] > Len::new(1))
    .map(tid)
    .collect()
}

/// The terms some minimum may store after reductions R1 (at least two
/// expanded occurrences) and R2 (inline encoding longer than one byte), in
/// term-ID order. Its length is the search's candidate count.
pub fn candidate_terms(dag: &SharingDag) -> Vec<TermId> {
  let own: Vec<Len> = dag.nodes().iter().map(Node::own_len).collect();
  let base = all_costs(dag.nodes(), &own, &NoWidths, &mut 0);
  candidates_of(&occurrences(dag), &base)
}

/// Exact variable length of the table sequence `q` with every entry and
/// root at its minimum: `sum C_{q<i}(q_i) + tag0(|q|) + sum C_q(root)`.
pub fn sequence_len(
  dag: &SharingDag,
  q: &[TermId],
) -> Result<Len, SharingError> {
  let n = dag.len();
  let mut seen = vec![false; n];
  for &t in q {
    if ix(t) >= n || seen[ix(t)] {
      return Err(internal("sequence term out of range or repeated"));
    }
    seen[ix(t)] = true;
  }
  let own: Vec<Len> = dag.nodes().iter().map(Node::own_len).collect();
  let mut dict = DenseIndex::new(n);
  let mut work = 0u64;
  let k = u64::try_from(q.len()).map_err(|_e| internal("length"))?;
  let mut total = Len::new(tag0_len(k));
  for (i, &t) in q.iter().enumerate() {
    let costs = all_costs(dag.nodes(), &own, &dict, &mut work);
    total = total.plus(costs[ix(t)]);
    dict.set(t, u64::try_from(i).map_err(|_e| internal("index"))?);
  }
  let costs = all_costs(dag.nodes(), &own, &dict, &mut work);
  for &r in dag.roots() {
    total = total.plus(costs[ix(r)]);
  }
  Ok(total)
}
