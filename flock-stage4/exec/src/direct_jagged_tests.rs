//! Original jagged-claim native differentials and bounded component census.
//! No native sidecar callback discharges a circuit claim in this prototype.

use super::{capacity_tests::SMALL, closure_tests::decode, memory_summary};
use flock_prover::{
  field::F128,
  matrix_fold::{JaggedRowWeight, JaggedTable, jagged_bilinear},
  pcs::jagged::JaggedParams,
  union::UnionInstance,
};
use ix_stage4_trace::{F128JaggedDirectLimitsV0, F128JaggedDirectTableV0};
use ixby_flock::{
  blake3_backend::Blake3Backend,
  ixby::{
    decode::PrimitiveSet,
    exec::{SemanticProfile, compile_exec_profile_with_backend},
  },
};
use std::time::Instant;

fn bytes(v: F128) -> [u8; 16] {
  (u128::from(v.lo) | (u128::from(v.hi) << 64)).to_le_bytes()
}

fn point(n: usize, seed: u128) -> Vec<F128> {
  (0..n)
    .map(|i| {
      let v = seed
        .wrapping_mul(i as u128 + 3)
        .rotate_left(u32::try_from(i).unwrap() * 7);
      decode(&v.to_le_bytes())
    })
    .collect()
}

fn evaluate(
  table: &F128JaggedDirectTableV0,
  row: &JaggedRowWeight,
  col: &[F128],
) -> F128 {
  use ix_stage4_trace::{
    F128JaggedEqualityNodeV0 as E, F128JaggedRowNodeV0 as R,
  };
  let mut eq = Vec::new();
  for node in table.equality_nodes() {
    eq.push(match *node {
      E::Factor { coordinate, complement } => {
        col[coordinate as usize]
          + if complement { F128::ONE } else { F128::ZERO }
      },
      E::Multiply { left, right } => eq[left as usize] * eq[right as usize],
    });
  }
  let pairs =
    table.pair_outputs().iter().map(|&i| eq[i as usize]).collect::<Vec<_>>();
  match row {
    JaggedRowWeight::Eq(scale, point) => {
      let mut nodes = Vec::new();
      for node in table.row_nodes() {
        nodes.push(match *node {
          R::Pair(i) => pairs[i as usize],
          R::Branch { coordinate, low, high } => {
            nodes[low as usize]
              + point[coordinate as usize]
                * (nodes[low as usize] + nodes[high as usize])
          },
        });
      }
      *scale * nodes[table.row_root() as usize]
    },
    JaggedRowWeight::Combo(terms) => terms.iter().zip(table.combo()).fold(
      F128::ZERO,
      |sum, ((coefficient, address), (expected, pair))| {
        assert_eq!(address, expected);
        sum + *coefficient * pairs[*pair as usize]
      },
    ),
  }
}

#[test]
#[ignore = "bounded exact 3 original jagged claims with setup/assigned R1CS/PLONK component census; not the complete Exec relation, key or proof"]
fn packed_small_direct_jagged_original_claim_component_census() {
  use ix_fflonk::PlonkGateProjectionV1;
  use ix_terminal_circuit::{
    Constraint, ConstraintPhase, F128JaggedAssertionVariablesV1,
    F128JaggedClaimVariablesV1, F128JaggedComboTermVariablesV1,
    F128JaggedRowWeightVariablesV1, R1csBuilder, R1csError, alloc_f128_private,
    constrain_f128_jagged_direct,
  };
  let setup = compile_exec_profile_with_backend(
    SemanticProfile::scalar(SMALL).unwrap(),
    SMALL,
    PrimitiveSet::scalar(),
    Blake3Backend::PackedWordsV0,
  )
  .unwrap();
  let replay = crate::compile_exec_replay(&setup).unwrap();
  let shape = setup.verifier_shape();
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let params = JaggedParams::from_heights(
    &union.jagged_heights(),
    union.n_log(),
    setup.pcs_params().m - 7,
  );
  let native = JaggedTable::from_params(&params);
  let compile = || {
    F128JaggedDirectTableV0::compile(
      replay.pcs.multipoint.matrix,
      native.bounds.iter().copied(),
      replay.pcs.multipoint.group_column_addresses.iter().copied(),
      F128JaggedDirectLimitsV0 {
        runs: 100_000,
        combo_terms: 100_000,
        row_nodes: 1_000_000,
        equality_nodes: 1_000_000,
      },
    )
    .unwrap()
  };
  let table = compile();
  assert_eq!(table, compile());
  assert_eq!(table.matrix().row_variables as usize, native.k);
  assert_eq!(table.matrix().column_variables as usize, native.n_col_vars());
  let seed = 0x9b79_74a9_d199_7123_fa41_919d_7311_a638;
  let rows = [
    JaggedRowWeight::Eq(F128::new(17, 31), point(native.k, seed)),
    JaggedRowWeight::Eq(F128::new(19, 71), point(native.k, seed + 417)),
    JaggedRowWeight::Combo(
      point(table.combo().len(), seed + 985)
        .into_iter()
        .zip(table.combo().iter().map(|&(address, _)| address))
        .collect(),
    ),
  ];
  let column = point(native.n_col_vars(), seed + 7109);
  let expected = rows
    .iter()
    .map(|row| {
      let expected = jagged_bilinear(row, &column, &native);
      assert_eq!(evaluate(&table, row, &column), expected);
      expected
    })
    .collect::<Vec<_>>();
  eprintln!(
    "direct jagged original claims: digest={}, runs={}, pairs={}, equality_nodes={}, row_nodes={}, combo_terms={}, native differential PASS; {}",
    blake3::Hash::from(table.digest()),
    table.runs().len(),
    table.pairs().len(),
    table.equality_nodes().len(),
    table.row_nodes().len(),
    table.combo().len(),
    memory_summary(),
  );
  let phase = ConstraintPhase::MatrixFold;
  let mut first = None;
  for shape_only in [true, false] {
    let started = Instant::now();
    let plonk = PlonkGateProjectionV1::new();
    let observed = plonk.clone();
    let mut observe = observed.observer();
    let observer = move |c: &Constraint| {
      observe(c);
      let rows = observed
        .prefix()
        .map_err(|_| R1csError::InternalShape)?
        .constraint_rows;
      if rows > 100_000_000 {
        return Err(R1csError::ResourceLimit {
          resource: "direct jagged component PLONK rows",
          limit: 100_000_000,
          actual: rows,
        });
      }
      Ok(())
    };
    let mut builder = if shape_only {
      R1csBuilder::new_shape_projection_observed_fallible(observer)
    } else {
      R1csBuilder::new_projection_observed_fallible(observer)
    };
    let encode = |v| if shape_only { [0; 16] } else { bytes(v) };
    let column_point = column
      .iter()
      .map(|&v| alloc_f128_private(&mut builder, encode(v), phase).unwrap())
      .collect::<Vec<_>>();
    let claims = rows
      .iter()
      .zip(&expected)
      .map(|(row, &value)| {
        let row = match row {
          JaggedRowWeight::Eq(scale, point) => {
            F128JaggedRowWeightVariablesV1::Eq {
              scale: Box::new(
                alloc_f128_private(&mut builder, encode(*scale), phase)
                  .unwrap(),
              ),
              point: point
                .iter()
                .map(|&v| {
                  alloc_f128_private(&mut builder, encode(v), phase).unwrap()
                })
                .collect(),
            }
          },
          JaggedRowWeight::Combo(terms) => {
            F128JaggedRowWeightVariablesV1::Combo {
              terms: terms
                .iter()
                .map(|&(coefficient, address)| F128JaggedComboTermVariablesV1 {
                  coefficient: alloc_f128_private(
                    &mut builder,
                    encode(coefficient),
                    phase,
                  )
                  .unwrap(),
                  address,
                })
                .collect(),
            }
          },
        };
        F128JaggedClaimVariablesV1 {
          row,
          column_point: column_point.clone(),
          value: alloc_f128_private(&mut builder, encode(value), phase)
            .unwrap(),
        }
      })
      .collect();
    let assertion =
      F128JaggedAssertionVariablesV1 { matrix: table.matrix(), claims };
    let outputs =
      constrain_f128_jagged_direct(&mut builder, &table, &assertion, phase)
        .unwrap();
    if !shape_only {
      for (output, &expected) in outputs.iter().zip(&expected) {
        assert_eq!(*output.value(), bytes(expected));
      }
    }
    let r1cs = builder.finish_projection().unwrap();
    let plonk = plonk.finish_for_sizing(&r1cs).unwrap();
    eprintln!(
      "COMPLETE direct jagged original 3 claims shape_only={shape_only}: R1CS={}, PLONK={}, projection={}; {:.3}s; {}. COMPONENT ONLY, no complete Exec relation/key/proof.",
      r1cs.census().constraints,
      plonk.constraint_rows,
      blake3::Hash::from(r1cs.digest()),
      started.elapsed().as_secs_f64(),
      memory_summary(),
    );
    if let Some((shape, count)) = first.take() {
      assert_eq!(r1cs, shape);
      assert_eq!(plonk, count);
    } else {
      first = Some((r1cs, plonk));
    }
  }
}
