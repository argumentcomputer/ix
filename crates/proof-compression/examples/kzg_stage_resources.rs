//! Inspect saved stage metadata without loading coefficient matrices or an SRS.

use ix_proof_compression::kzg::{KzgCommitment, Scalar, curve};
use multi_stark::{
  expr::Source,
  graph::{ConstraintGraph, Node, NodeId},
  system::Circuit,
};
use serde::de::DeserializeOwned;
use serde_json::json;
use std::{collections::BTreeSet, fs, path::Path};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

fn decode<T: DeserializeOwned>(path: &Path) -> Result<T> {
  let bytes = fs::read(path)?;
  let (value, used) = bincode::serde::decode_from_slice(
    &bytes,
    bincode::config::standard().with_limit::<16777216>(),
  )?;
  if used != bytes.len() {
    return Err("trailing metadata bytes".into());
  }
  Ok(value)
}

fn columns(
  graph: &ConstraintGraph<Scalar>,
  roots: impl IntoIterator<Item = NodeId>,
) -> BTreeSet<(u8, usize)> {
  let mut result = BTreeSet::new();
  let mut visited = BTreeSet::new();
  let mut pending: Vec<_> = roots.into_iter().collect();
  while let Some(id) = pending.pop() {
    if !visited.insert(id.index()) {
      continue;
    }
    match graph.nodes[id.index()] {
      Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
        pending.extend([a, b])
      },
      Node::Neg(a) => pending.push(a),
      Node::Var(column) => {
        let source = match column.source {
          Source::Preprocessed => 0,
          Source::Main => 1,
          Source::Stage2 => 2,
        };
        result.insert((source, column.index as usize));
      },
      _ => {},
    }
  }
  result
}

fn main() -> Result<()> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  let [stage] = args.as_slice() else {
    return Err("usage: kzg_stage_resources <saved-stage-dir>".into());
  };
  let stage = Path::new(stage);
  let (widths, heights, _claims): (Vec<usize>, Vec<usize>, Vec<Vec<Scalar>>) =
    decode(&stage.join("manifest.bin"))?;
  let mut circuits = Vec::new();
  let mut scalar_bytes = 0usize;
  for (i, (&width, &height)) in widths.iter().zip(&heights).enumerate() {
    let (circuit, _): (Circuit<Scalar>, KzgCommitment) =
      decode(&stage.join(format!("kzg/setup-{i}.bin")))?;
    if width != circuit.main_width || height != circuit.preprocessed_height {
      return Err("manifest/setup mismatch".into());
    }
    let group_size = circuit.lookup_group_size.max(1);
    let groups = circuit.stage_2_width;
    let ratio = circuit.quotient_degree();
    let graph = &circuit.graph;
    let mut lookup_columns = 0;
    let mut quotient_columns = graph
      .zeros
      .iter()
      .map(|&root| columns(graph, [root]).len())
      .max()
      .unwrap_or(0);
    for (group, lookups) in graph.lookups.chunks(group_size).enumerate() {
      let mut used = columns(
        graph,
        lookups.iter().flat_map(|lookup| {
          std::iter::once(lookup.multiplicity)
            .chain(lookup.args.iter().copied())
        }),
      );
      lookup_columns = lookup_columns.max(used.len());
      used.insert((2, group));
      used.insert((2, if group + 1 == groups { 0 } else { group + 1 }));
      quotient_columns = quotient_columns.max(used.len());
    }
    let all = circuit.preprocessed_width + circuit.main_width + groups;
    let bytes_per_column = height * size_of::<Scalar>();
    scalar_bytes += bytes_per_column * (all + ratio);
    // Treat every source column as varying and every graph node as a live
    // scratch slot. Runtime constant folding and liveness can reduce this bound.
    let overhead = (1usize << 30)
      + 256 * 128 * graph.nodes.len().max(1) * size_of::<Scalar>()
      + (graph.nodes.len()
        + graph.lookups.len()
        + all
        + circuit.num_publics
        + 32)
        * 1024;
    circuits.push(json!({
      "index": i, "rows": height, "main_columns": width,
      "fixed_columns": circuit.preprocessed_width, "lookup_columns": groups,
      "quotient_factor": ratio, "graph_nodes": graph.nodes.len(),
      "lookup_count": graph.lookups.len(), "lookup_group_size": group_size,
      "max_lookup_pass_columns": lookup_columns, "max_quotient_pass_columns": quotient_columns,
      "dense_lookup_bytes_upper": bytes_per_column * (all - groups + 4 * groups) + overhead,
      "pass_lookup_bytes_upper": bytes_per_column * (lookup_columns + groups + 3) + overhead,
      "dense_quotient_bytes_upper": bytes_per_column * (all + ratio + 1) + overhead,
      "pass_quotient_bytes_upper": bytes_per_column * (quotient_columns + ratio + 1) + overhead,
    }));
  }
  let max_height = heights.iter().copied().max().ok_or("empty stage")?;
  println!(
    "{}",
    serde_json::to_string_pretty(&json!({
      "curve": curve::NAME, "stage": stage, "circuits": circuits,
      "scalar_column_bytes": scalar_bytes,
      "srs_host_bytes": max_height * size_of::<curve::G1Affine>(),
      "scope": "Conservative column and GPU-pass accounting from metadata. Excludes frontend/witness memory, host transient copies, CUDA retained coefficients, SRS caches and MSM workspace. No proving arrays, SRS or CUDA context are allocated.",
    }))?
  );
  Ok(())
}
