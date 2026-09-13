// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Combined opened-row arithmetic using the actual graph sweep, direct
//! logUp evaluator and domain selectors. The private verifier's wiring,
//! Horner fold, quotient recombination and claim loop are reproduced here;
//! these deliberately constructed openings are not authenticated proofs.

use super::*;
use multi_stark::{
  eval::VarValues,
  lookup::logup_constraint_values,
  p3_field::{
    BasedVectorSpace, Field, TwoAdicField, coset::TwoAdicMultiplicativeCoset,
  },
  system::Circuit,
  types::ExtVal,
};
use p3_commit::{LagrangeSelectors, PolynomialSpace};
use std::io;

#[derive(Clone, Copy)]
struct Challenges {
  beta: ExtVal,
  gamma: ExtVal,
  alpha: ExtVal,
  zeta: ExtVal,
}

struct Opening {
  index: usize,
  bits: usize,
  main: [Vec<ExtVal>; 2],
  stage2: [Vec<ExtVal>; 2],
  preprocessed: Option<[Vec<ExtVal>; 2]>,
  quotient: Vec<ExtVal>,
  accumulator: ExtVal,
}

struct Evaluation {
  selectors: LagrangeSelectors<ExtVal>,
  publics: Vec<ExtVal>,
  delta: Vec<ExtVal>,
  nodes: Vec<ExtVal>,
  user: Vec<ExtVal>,
  lookups: Vec<ExtVal>,
  composition: ExtVal,
  quotient: ExtVal,
}

impl Evaluation {
  fn accepts(&self) -> bool {
    self.composition * self.selectors.inv_vanishing == self.quotient
  }
}

fn nat(out: &mut Vec<u8>, value: usize) {
  out.extend(u64::try_from(value).unwrap().to_le_bytes());
}

fn field(out: &mut Vec<u8>, value: Val) {
  out.extend(value.as_canonical_u64().to_le_bytes());
}

fn extension(out: &mut Vec<u8>, value: ExtVal) {
  for &value in value.as_basis_coefficients_slice() {
    field(out, value);
  }
}

fn extensions(out: &mut Vec<u8>, values: &[ExtVal]) {
  nat(out, values.len());
  for &value in values {
    extension(out, value);
  }
}

fn scalar(seed: usize, slot: usize, index: usize) -> Val {
  let mut word = 0x79e3_4987_6a8b_051f_u64
    .wrapping_add(u64::try_from(seed).unwrap().wrapping_mul(0x74d8_b901))
    .wrapping_add(u64::try_from(slot).unwrap().wrapping_mul(0x5982_6407))
    .wrapping_add(u64::try_from(index).unwrap().wrapping_mul(0x8071_5823));
  for _ in 0..4 {
    word ^= word << 13;
    word ^= word >> 7;
    word ^= word << 17;
  }
  Val::from_u64(word)
}

fn value(seed: usize, slot: usize, index: usize) -> ExtVal {
  ExtVal::new([
    scalar(seed, slot * 2, index),
    scalar(seed, slot * 2 + 1, index),
  ])
}

fn challenges(seed: usize) -> Challenges {
  Challenges {
    beta: value(seed, 40, 0),
    gamma: value(seed, 41, 0),
    alpha: match seed % 6 {
      0 => ExtVal::ZERO,
      1 => ExtVal::ONE,
      2 => ExtVal::NEG_ONE,
      3 => ExtVal::new([Val::ZERO, Val::ONE]),
      _ => value(seed, 42, 0),
    },
    zeta: value(seed, 43, 0),
  }
}

fn opening(
  circuit: &Circuit<Val>,
  index: usize,
  bits: usize,
  seed: usize,
) -> Opening {
  let assignment =
    |width, slot| (0..width).map(|index| value(seed, slot, index)).collect();
  Opening {
    index,
    bits,
    main: [
      assignment(circuit.main_width, 0),
      assignment(circuit.main_width, 1),
    ],
    stage2: [
      assignment(circuit.stage_2_width, 2),
      assignment(circuit.stage_2_width, 3),
    ],
    preprocessed: (circuit.preprocessed_width != 0).then(|| {
      [
        assignment(circuit.preprocessed_width, 4),
        assignment(circuit.preprocessed_width, 5),
      ]
    }),
    quotient: assignment(circuit.quotient_degree() * 2, 6),
    accumulator: value(seed, 7, 0),
  }
}

fn evaluate(
  circuit: &Circuit<Val>,
  row: &Opening,
  challenges: Challenges,
  entering: ExtVal,
) -> Evaluation {
  let domain =
    TwoAdicMultiplicativeCoset::<Val>::new(Val::ONE, row.bits).unwrap();
  assert_ne!(domain.vanishing_poly_at_point(challenges.zeta), ExtVal::ZERO);
  let selectors = domain.selectors_at_point(challenges.zeta);
  let publics: Vec<_> =
    [challenges.beta, challenges.gamma, entering, row.accumulator]
      .iter()
      .flat_map(|value| {
        let coordinates: &[Val] = value.as_basis_coefficients_slice();
        coordinates.iter().copied().map(ExtVal::from)
      })
      .collect();
  let norm = ExtVal::from(
    (Val::from_usize(domain.size()) * Val::two_adic_generator(row.bits))
      .inverse(),
  );
  let delta: Vec<_> = (0..2)
    .map(|index| (publics[6 + index] - publics[4 + index]) * norm)
    .collect();
  let empty = Vec::new();
  let preprocessed = row
    .preprocessed
    .as_ref()
    .map_or([&empty, &empty], |rows| [&rows[0], &rows[1]]);
  let view = VarValues {
    preprocessed: [preprocessed[0], preprocessed[1]],
    main: [&row.main[0], &row.main[1]],
    stage2: [&row.stage2[0], &row.stage2[1]],
    publics: &publics,
    is_first_row: selectors.is_first_row,
    is_last_row: selectors.is_last_row,
    is_transition: selectors.is_transition,
  };
  let mut nodes = Vec::new();
  circuit.graph.sweep(&view, &mut nodes);
  let user = circuit.graph.constraint_values(&nodes);
  let mut lookups = Vec::new();
  logup_constraint_values(
    &circuit.graph.lookups,
    &nodes,
    view.stage2[0],
    view.stage2[1],
    &publics,
    &delta,
    selectors.is_last_row,
    Val::from_u64(7),
    2,
    circuit.lookup_group_size,
    &mut lookups,
  );
  assert_eq!(user.len() + lookups.len(), circuit.constraint_count());
  let composition = user
    .iter()
    .chain(&lookups)
    .fold(ExtVal::ZERO, |acc, &value| acc * challenges.alpha + value);
  let quotient = row
    .quotient
    .as_chunks::<2>()
    .0
    .iter()
    .zip(challenges.zeta.exp_power_of_2(row.bits).powers())
    .map(|(chunk, power)| {
      power
        * (chunk[0]
          + chunk[1]
            * <ExtVal as BasedVectorSpace<Val>>::ith_basis_element(1).unwrap())
    })
    .sum();
  Evaluation {
    selectors,
    publics,
    delta,
    nodes,
    user,
    lookups,
    composition,
    quotient,
  }
}

fn adjust(
  circuit: &Circuit<Val>,
  row: &mut Opening,
  challenges: Challenges,
  entering: ExtVal,
  accepted: bool,
) {
  let evaluated = evaluate(circuit, row, challenges, entering);
  row.quotient[0] += evaluated.composition * evaluated.selectors.inv_vanishing
    - evaluated.quotient;
  if !accepted {
    row.quotient[0] += ExtVal::ONE;
  }
  assert_eq!(evaluate(circuit, row, challenges, entering).accepts(), accepted);
}

fn write_challenges(out: &mut Vec<u8>, challenges: Challenges) {
  for value in
    [challenges.beta, challenges.gamma, challenges.alpha, challenges.zeta]
  {
    extension(out, value);
  }
}

fn write_opening(out: &mut Vec<u8>, row: &Opening) {
  nat(out, row.index);
  nat(out, row.bits);
  for pair in [&row.main, &row.stage2] {
    for values in pair {
      extensions(out, values);
    }
  }
  out.push(u8::from(row.preprocessed.is_some()));
  if let Some(rows) = &row.preprocessed {
    for values in rows {
      extensions(out, values);
    }
  }
  extensions(out, &row.quotient);
  extension(out, row.accumulator);
}

fn write_evaluation(out: &mut Vec<u8>, evaluated: &Evaluation) {
  for value in [
    evaluated.selectors.is_first_row,
    evaluated.selectors.is_last_row,
    evaluated.selectors.is_transition,
    evaluated.selectors.inv_vanishing,
  ] {
    extension(out, value);
  }
  for values in [
    &evaluated.publics,
    &evaluated.delta,
    &evaluated.nodes,
    &evaluated.user,
    &evaluated.lookups,
  ] {
    extensions(out, values);
  }
  extension(out, evaluated.composition);
  extension(out, evaluated.quotient);
  out.push(u8::from(evaluated.accepts()));
}

fn claim_message(challenges: Challenges, claim: &[Val]) -> ExtVal {
  challenges.beta
    + claim
      .iter()
      .rfold(ExtVal::ZERO, |acc, &value| acc * challenges.gamma + value)
}

fn initial(challenges: Challenges, claims: &[Vec<Val>]) -> Option<ExtVal> {
  claims.iter().try_fold(ExtVal::ZERO, |acc, claim| {
    Some(acc + claim_message(challenges, claim).try_inverse()?)
  })
}

fn claims(seed: usize, count: usize) -> Vec<Vec<Val>> {
  let lengths = [0, 1, 2, 3, 7, 16, 17];
  (0..count)
    .map(|index| {
      (0..lengths[(seed + index) % lengths.len()])
        .map(|arg| scalar(seed, 70 + index, arg))
        .collect()
    })
    .collect()
}

fn write_claims(out: &mut Vec<u8>, claims: &[Vec<Val>]) {
  nat(out, claims.len());
  for claim in claims {
    nat(out, claim.len());
    for &value in claim {
      field(out, value);
    }
  }
}

#[test]
fn verifier_arithmetic_snapshot() -> io::Result<()> {
  let system = graph_tests::graph_system();
  let mut out = b"Aiur verifier arithmetic v1\n".to_vec();
  nat(&mut out, system.circuits.len());
  for circuit in &system.circuits {
    let mut encoded = Vec::new();
    encode_circuit(&mut encoded, circuit);
    nat(&mut out, encoded.len());
    out.extend(encoded);
  }
  nat(&mut out, system.circuits.len() * 8 * 12);
  let mut nodes = 0;
  for (index, circuit) in system.circuits.iter().enumerate() {
    let largest =
      31 - usize::try_from(circuit.quotient_degree().trailing_zeros()).unwrap();
    for bits in [0, 1, 2, 4, 8, 16, 24, largest] {
      for seed in 0..12 {
        let challenges = challenges(seed);
        let entering = value(seed, 50, 0);
        let mut row = opening(circuit, index, bits, seed);
        adjust(circuit, &mut row, challenges, entering, seed % 2 == 0);
        let evaluated = evaluate(circuit, &row, challenges, entering);
        nat(&mut out, seed);
        write_challenges(&mut out, challenges);
        extension(&mut out, entering);
        write_opening(&mut out, &row);
        write_evaluation(&mut out, &evaluated);
        nodes += evaluated.nodes.len();
      }
    }
  }
  // Direct native inverse calls also cover poles; the total Lean model
  // rejects them before the private verifier's unguarded inverse call.
  nat(&mut out, 12 * 6);
  for seed in 0..12 {
    for count in [0, 1, 2, 3, 7, 16] {
      let mut challenges = challenges(seed);
      let claims = claims(seed, count);
      if seed % 3 == 0 && count != 0 {
        challenges.beta -= claim_message(challenges, &claims[0]);
      }
      let accumulator = initial(challenges, &claims);
      assert_eq!(accumulator.is_some(), seed % 3 != 0 || count == 0);
      write_challenges(&mut out, challenges);
      write_claims(&mut out, &claims);
      for claim in &claims {
        extension(&mut out, claim_message(challenges, claim));
      }
      out.push(u8::from(accumulator.is_some()));
      if let Some(accumulator) = accumulator {
        extension(&mut out, accumulator);
      }
    }
  }
  // Vary the active order, chain length, final boundary and an interior
  // quotient. Reusing the initial accumulator on every row changes these
  // native node/public/lookup values even when alpha is zero or one.
  nat(&mut out, 12 * 4);
  for seed in 0..12 {
    for count in [1, 2, 3, 10] {
      let challenges = challenges(seed + 20);
      let claims = claims(seed + 20, seed % 4);
      let mut entering = initial(challenges, &claims).unwrap();
      write_challenges(&mut out, challenges);
      write_claims(&mut out, &claims);
      nat(&mut out, count);
      let all_rows = seed % 3 != 1;
      for position in 0..count {
        let index = (position * 7 + seed) % system.circuits.len();
        let circuit = &system.circuits[index];
        let mut row =
          opening(circuit, index, 2 + position % 7, seed + 20 + position);
        if position + 1 == count && seed % 3 != 2 {
          row.accumulator = ExtVal::ZERO;
        }
        adjust(
          circuit,
          &mut row,
          challenges,
          entering,
          all_rows || position != count / 2,
        );
        write_opening(&mut out, &row);
        write_evaluation(
          &mut out,
          &evaluate(circuit, &row, challenges, entering),
        );
        entering = row.accumulator;
      }
      out.push(u8::from(all_rows));
      if all_rows {
        out.push(u8::from(entering == ExtVal::ZERO));
      }
    }
  }
  assert_eq!((system.circuits.len(), nodes), (10, 32064));
  if let Some(path) = std::env::var_os("IX_VERIFIER_ARITHMETIC_SNAPSHOT") {
    std::fs::write(path, &out)?;
  }
  eprintln!(
    "verifier arithmetic: 960 openings, {nodes} node values, 72 claim cases, 48 accumulator chains"
  );
  Ok(())
}
