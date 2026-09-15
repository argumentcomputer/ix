//! Exact module-valued cofactor span of all original matrix claims.
//! Component diagnostics only, not complete Exec closure or key adoption.

use super::{compile, expected, inputs, setup};
use flock_prover::field::F128;
use ix_stage4_trace::{
  F128FixedTableBasisLimitsV0, F128StructuredMatrixSpanV0,
};
use std::time::Instant;

const LIMITS: F128FixedTableBasisLimitsV0 = F128FixedTableBasisLimitsV0 {
  state_slots: 1_000_000,
  dense_words: 64_000_000,
  word_operations: 64_000_000_000,
  coefficient_terms: 5_000_000,
};

fn evaluate(
  program: &F128StructuredMatrixSpanV0,
  input: &[Vec<F128>; 4],
) -> Vec<F128> {
  let low = program.low_variables();
  let mask = (1usize << low) - 1;
  let mut values = program
    .leaf_generators()
    .iter()
    .map(|row| {
      row.iter().fold(F128::ZERO, |value, &pair| {
        let pair = usize::from(pair);
        value + input[0][pair & mask] * input[1][pair >> low]
      })
    })
    .collect::<Vec<_>>();
  let sum = |values: &[F128], terms: &[u32]| {
    terms
      .iter()
      .fold(F128::ZERO, |value, &index| value + values[index as usize])
  };
  for layer in program.layers().iter().rev() {
    assert_eq!(values.len(), layer.child_width() as usize);
    let coordinate = layer.coordinate();
    let high = program.high_variables();
    let point = if coordinate < high {
      input[2][coordinate as usize]
    } else {
      input[3][(coordinate - high) as usize]
    };
    values = layer
      .rows()
      .iter()
      .map(|row| sum(&values, row.low()) + point * sum(&values, row.slope()))
      .collect();
  }
  program.outputs().iter().map(|(_, output)| sum(&values, output)).collect()
}

#[test]
#[ignore = "bounded exact shared-matrix module cofactor span and all 64 native differentials; no circuit emission, adoption, key or proof"]
fn packed_small_shared_matrix_module_span_diagnostic() {
  let setup = setup();
  let replay = crate::compile_exec_replay(&setup).unwrap();
  let source = compile(&replay);
  let started = Instant::now();
  eprintln!(
    "shared matrix module span: starting complete setup-only forest compilation"
  );
  let program = match F128StructuredMatrixSpanV0::compile(&source, LIMITS) {
    Ok(program) => program,
    Err(error) => {
      eprintln!(
        "shared matrix module span REFUSED {error}; {:.3}s; no adoption",
        started.elapsed().as_secs_f64()
      );
      return;
    },
  };
  assert_eq!(program.source_digest(), source.digest());
  assert_eq!(
    program.outputs().iter().map(|(id, _)| id).collect::<Vec<_>>(),
    source.outputs().iter().map(|(id, _)| id).collect::<Vec<_>>()
  );
  for seed in [0, 1, 0x91ad_8481_abe7_fa10_2758_019a_68a4_19fe] {
    let input = inputs(&source, seed);
    assert_eq!(evaluate(&program, &input), expected(&setup, &source, &input));
  }
  let widths =
    program.layers().iter().map(|layer| layer.rows().len()).collect::<Vec<_>>();
  let slopes = program
    .layers()
    .iter()
    .flat_map(|layer| layer.rows())
    .filter(|row| !row.slope().is_empty())
    .count();
  let xor_sites = program
    .leaf_generators()
    .iter()
    .map(|row| row.len().saturating_sub(1))
    .sum::<usize>()
    + program
      .layers()
      .iter()
      .flat_map(|layer| layer.rows())
      .map(|row| {
        row.low().len().saturating_sub(1)
          + row.slope().len().saturating_sub(1)
          + usize::from(!row.low().is_empty() && !row.slope().is_empty())
      })
      .sum::<usize>()
    + program
      .outputs()
      .iter()
      .map(|(_, row)| row.len().saturating_sub(1))
      .sum::<usize>();
  eprintln!(
    "COMPLETE shared matrix module span: digest={}, source={}, pairs={}, leaf_width={}, widths={widths:?}, nonzero_slopes={slopes}, estimated_F128_XOR_sites={xor_sites}, {:?}; all 64 native differentials PASS; {:.3}s; COMPONENT SYMBOLIC COUNTS ONLY, no circuit/key/proof or adoption",
    blake3::Hash::from(program.digest()),
    blake3::Hash::from(program.source_digest()),
    program.pairs().len(),
    program.leaf_generators().len(),
    program.census(),
    started.elapsed().as_secs_f64()
  );
}
