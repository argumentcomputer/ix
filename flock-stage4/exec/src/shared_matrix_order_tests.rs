//! Setup-only order exploration for the original shared-weight matrices.
//! No candidate is adopted here, and node counts are not PLONK counts.

use super::{compile, expected, inputs, setup};
use flock_prover::field::F128;
use ix_stage4_trace::{
  F128FixedTableLimitsV0, F128FixedTableNodeV0 as Node, F128FixedTableV0,
  F128MatrixSideV1, F128StaticMatrixIdV1, F128StructuredMatricesV0,
  F128StructuredMatrixNodeV0 as Shared,
};
use std::{
  collections::{BTreeMap, HashMap},
  time::Instant,
};

struct HighSource {
  id: F128StaticMatrixIdV1,
  entries: Vec<(u64, [u8; 16])>,
}

struct Candidate {
  nodes: Vec<Shared>,
  outputs: Vec<(F128StaticMatrixIdV1, u32)>,
}

fn high_sources(
  setup: &ixby_flock::ixby::exec::CompiledExec,
  baseline: &F128StructuredMatricesV0,
) -> Vec<HighSource> {
  let block_ids = baseline
    .blocks()
    .iter()
    .enumerate()
    .map(|(id, pairs)| (pairs.clone(), id))
    .collect::<BTreeMap<_, _>>();
  baseline
    .outputs()
    .iter()
    .map(|&(id, _)| {
      let ty = &setup.verifier_shape().registry.boolean_types()
        [usize::try_from(id.table).unwrap()];
      let matrix = match id.side {
        F128MatrixSideV1::A => &ty.a_0,
        F128MatrixSideV1::B => &ty.b_0,
      };
      let high = id.variables - 6;
      let mut blocks = BTreeMap::<u64, Vec<u16>>::new();
      for (row, columns) in matrix.rows.iter().enumerate() {
        for &column in columns {
          let index = u64::try_from(row >> 6).unwrap()
            | (u64::try_from(column >> 6).unwrap() << high);
          let pair = u16::try_from((row & 63) | ((column & 63) << 6)).unwrap();
          blocks.entry(index).or_default().push(pair);
        }
      }
      let entries = blocks
        .into_iter()
        .filter_map(|(index, mut pairs)| {
          pairs.sort_unstable();
          let mut normalized = Vec::new();
          let mut first = 0;
          while first < pairs.len() {
            let mut end = first + 1;
            while end < pairs.len() && pairs[first] == pairs[end] {
              end += 1;
            }
            if (end - first) % 2 == 1 {
              normalized.push(pairs[first]);
            }
            first = end;
          }
          if normalized.is_empty() {
            return None;
          }
          let tag =
            u128::try_from(*block_ids.get(&normalized).unwrap()).unwrap() + 1;
          Some((index, tag.to_le_bytes()))
        })
        .collect();
      HighSource { id, entries }
    })
    .collect()
}

fn order(high: u32, variant: usize) -> Vec<u32> {
  match variant {
    0 => (0..high).rev().flat_map(|i| [i, high + i]).collect(),
    1 => (0..high).flat_map(|i| [i, high + i]).collect(),
    2 => (0..high).rev().flat_map(|i| [high + i, i]).collect(),
    3 => (0..high).flat_map(|i| [high + i, i]).collect(),
    4 => (0..high).rev().chain((high..2 * high).rev()).collect(),
    5 => (high..2 * high).rev().chain((0..high).rev()).collect(),
    6 => (0..2 * high).collect(),
    7 => (high..2 * high).chain(0..high).collect(),
    8..=15 => {
      let width = [2, 3, 4, 6][(variant - 8) / 2];
      let first = if variant.is_multiple_of(2) { 0 } else { high };
      let second = high - first;
      (0..high)
        .rev()
        .collect::<Vec<_>>()
        .chunks(width)
        .flat_map(|bits| {
          bits
            .iter()
            .map(move |i| first + i)
            .chain(bits.iter().map(move |i| second + i))
        })
        .collect()
    },
    _ => unreachable!(),
  }
}

fn candidate(
  sources: &[HighSource],
  orders: &[Vec<u32>],
) -> Result<Candidate, String> {
  assert_eq!(sources.len(), orders.len());
  let mut result = Candidate { nodes: Vec::new(), outputs: Vec::new() };
  let mut node_ids = HashMap::<Shared, u32>::new();
  for (source, order) in sources.iter().zip(orders) {
    let high_bits = source.id.variables - 6;
    let diagram = F128FixedTableV0::compile(
      order,
      source.entries.iter().copied(),
      F128FixedTableLimitsV0 { entries: 1_000_000, nodes: 200_000 },
    )
    .map_err(|error| error.to_string())?;
    let mut translated = Vec::with_capacity(diagram.nodes().len());
    for node in diagram.nodes() {
      let node = match *node {
        Node::Constant(tag) => {
          let tag = u128::from_le_bytes(tag);
          if tag == 0 {
            Shared::Zero
          } else {
            Shared::Block(u32::try_from(tag - 1).unwrap())
          }
        },
        Node::Branch { coordinate, low, high } => Shared::Branch {
          column: coordinate >= high_bits,
          bit: if coordinate >= high_bits {
            coordinate - high_bits
          } else {
            coordinate
          },
          low: translated[low as usize],
          high: translated[high as usize],
        },
        Node::Davio { .. } => unreachable!("Shannon-only compiler"),
      };
      let index = if let Some(&index) = node_ids.get(&node) {
        index
      } else {
        if result.nodes.len() >= 1_000_000 {
          return Err("shared node cap".into());
        }
        let index = u32::try_from(result.nodes.len()).unwrap();
        result.nodes.push(node);
        node_ids.insert(node, index);
        index
      };
      translated.push(index);
    }
    result.outputs.push((source.id, translated[diagram.root() as usize]));
  }
  Ok(result)
}

fn evaluate(
  program: &Candidate,
  blocks: &[F128],
  input: &[Vec<F128>; 4],
) -> Vec<F128> {
  let mut values = Vec::with_capacity(program.nodes.len());
  for node in &program.nodes {
    values.push(match *node {
      Shared::Zero => F128::ZERO,
      Shared::Block(id) => blocks[id as usize],
      Shared::Branch { column, bit, low, high } => {
        let x = input[if column { 3 } else { 2 }][bit as usize];
        values[low as usize]
          + x * (values[low as usize] + values[high as usize])
      },
    });
  }
  program.outputs.iter().map(|&(_, root)| values[root as usize]).collect()
}

#[test]
#[ignore = "bounded alternative high-coordinate orders with all 64 native matrix differentials; no R1CS census, topology adoption, key or proof"]
fn packed_small_shared_matrix_order_diagnostic() {
  let setup = setup();
  let replay = crate::compile_exec_replay(&setup).unwrap();
  let baseline = compile(&replay);
  let sources = high_sources(&setup, &baseline);
  let inputs = [0, 1, 0x91ad_8481_abe7_fa10_2758_019a_68a4_19fe].map(|seed| {
    let input = inputs(&baseline, seed);
    let expected = expected(&setup, &baseline, &input);
    let blocks = baseline
      .blocks()
      .iter()
      .map(|pairs| {
        pairs.iter().fold(F128::ZERO, |v, &pair| {
          v + input[0][usize::from(pair) & 63]
            * input[1][usize::from(pair) >> 6]
        })
      })
      .collect::<Vec<_>>();
    (input, expected, blocks)
  });
  for variant in 0..16 {
    let started = Instant::now();
    let orders = sources
      .iter()
      .map(|s| order(s.id.variables - 6, variant))
      .collect::<Vec<_>>();
    let result = match candidate(&sources, &orders) {
      Ok(program) => program,
      Err(error) => {
        eprintln!("shared matrix order {variant}: REFUSED {error}");
        continue;
      },
    };
    if variant == 0 {
      assert_eq!(result.nodes, baseline.nodes());
      assert_eq!(result.outputs, baseline.outputs());
    }
    for (input, expected, blocks) in &inputs {
      assert_eq!(
        &evaluate(&result, blocks, input),
        expected,
        "order {variant}"
      );
    }
    let branches = result
      .nodes
      .iter()
      .filter(|node| matches!(node, Shared::Branch { .. }))
      .count();
    eprintln!(
      "shared matrix order {variant}: nodes={}, branches={branches}, fixed_low_pairs={}, all 64 native differentials PASS; {:.3}s; COMPONENT NODE COUNT ONLY, no adoption",
      result.nodes.len(),
      baseline.pairs().len(),
      started.elapsed().as_secs_f64()
    );
  }
  let started = Instant::now();
  let mut selected = Vec::new();
  for source in &sources {
    let high = source.id.variables - 6;
    let count = |order: &[u32]| {
      F128FixedTableV0::compile(
        order,
        source.entries.iter().copied(),
        F128FixedTableLimitsV0 { entries: 1_000_000, nodes: 200_000 },
      )
      .map(|diagram| diagram.nodes().len())
    };
    let mut best_order = order(high, 0);
    let baseline_count = count(&best_order).unwrap();
    let mut best_count = baseline_count;
    for variant in 1..16 {
      let proposal = order(high, variant);
      if let Ok(nodes) = count(&proposal)
        && nodes < best_count
      {
        best_order = proposal;
        best_count = nodes;
      }
    }
    let predefined_count = best_count;
    // One bounded sifting pass: move each coordinate through every position.
    // Decisions use only exact setup diagrams, never point/witness values.
    for coordinate in 0..2 * high {
      let mut remaining = best_order.clone();
      remaining.retain(|&x| x != coordinate);
      for position in 0..=remaining.len() {
        let mut proposal = remaining.clone();
        proposal.insert(position, coordinate);
        if let Ok(nodes) = count(&proposal)
          && nodes < best_count
        {
          best_order = proposal;
          best_count = nodes;
        }
      }
    }
    eprintln!(
      "shared matrix sift table={} {:?} k={}: standalone nodes baseline={baseline_count}, predefined={predefined_count}, sifted={best_count}, order={best_order:?}",
      source.id.table, source.id.side, source.id.variables
    );
    selected.push(best_order);
  }
  let result = candidate(&sources, &selected).unwrap();
  for (input, expected, blocks) in &inputs {
    assert_eq!(&evaluate(&result, blocks, input), expected, "sifted orders");
  }
  let branches = result
    .nodes
    .iter()
    .filter(|node| matches!(node, Shared::Branch { .. }))
    .count();
  eprintln!(
    "shared matrix sifted: nodes={}, branches={branches}, fixed_low_pairs={}, all 64 native differentials PASS; {:.3}s; COMPONENT NODE COUNT ONLY, no adoption",
    result.nodes.len(),
    baseline.pairs().len(),
    started.elapsed().as_secs_f64()
  );
}
