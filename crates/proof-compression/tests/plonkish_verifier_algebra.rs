#[path = "support/parity_algebra.rs"]
mod adapter;
#[path = "support/parity.rs"]
mod parity;

use ix_proof_compression::fri::AlgebraicInputs;
use ix_proof_compression::fri::AlgebraicOutputs;
use ix_proof_compression::fri::QuadraticValue as Q;
use ix_proof_compression::fri::constrain_algebraic_checks;
use multi_stark::config::StarkGenericConfig;
use multi_stark::eval::VarValues;
use multi_stark::p3_field::BasedVectorSpace;
use multi_stark::p3_field::Field;
use multi_stark::p3_field::PrimeCharacteristicRing;
use multi_stark::p3_field::TwoAdicField;
use multi_stark::p3_field::extension::BinomiallyExtendable;
use multi_stark::plonkish::Assignment;
use multi_stark::plonkish::Circuit;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::plonkish::WitnessError;
use multi_stark::prover::Proof;
use multi_stark::system::System;
use multi_stark::system::SystemWitness;
use multi_stark::traits::Pcs;
use multi_stark::types::ExtVal;
use multi_stark::types::GoldilocksBlake3Config;
use multi_stark::types::Val;
use p3_commit::PolynomialSpace;

fn value(assignment: &Assignment<Val>, wire: Q) -> ExtVal {
  ExtVal::from_basis_coefficients_fn(|i| assignment.value(wire.0[i]).unwrap())
}

fn assignment(
  circuit: &Circuit<Val>,
  inputs: &AlgebraicInputs,
  proof: &Proof<GoldilocksBlake3Config>,
  claim: &[Val],
  challenges: [ExtVal; 4],
) -> Result<Assignment<Val>, WitnessError> {
  let mut witness = circuit.witness();
  adapter::assign(&mut witness, inputs, proof, &[claim], challenges)?;
  witness.generate()
}

/// Native oracle using the same primitives as System::verify, independent
/// of the gadget implementation. Compare every graph node and constraint.
fn check_intermediates(
  system: &System<GoldilocksBlake3Config>,
  proof: &Proof<GoldilocksBlake3Config>,
  claims: &[&[Val]],
  challenges: [ExtVal; 4],
  outputs: &AlgebraicOutputs,
  assignment: &Assignment<Val>,
) {
  let [beta, gamma, alpha, zeta] = challenges;
  let mut acc = claims
    .iter()
    .map(|claim| {
      let fingerprint =
        claim.iter().rev().fold(ExtVal::ZERO, |acc, &v| acc * gamma + v);
      (beta + fingerprint).inverse()
    })
    .sum();
  assert_eq!(value(assignment, outputs.claims_accumulator), acc);
  for (i, circuit) in system.circuits.iter().enumerate() {
    let output = &outputs.circuits[i];
    let domain = <_ as Pcs>::natural_domain_for_degree(
      system.config.pcs(),
      parity::HEIGHT,
    );
    let sels = domain.selectors_at_point(zeta);
    assert_eq!(
      value(assignment, output.selectors.is_first_row),
      sels.is_first_row
    );
    assert_eq!(
      value(assignment, output.selectors.is_last_row),
      sels.is_last_row
    );
    assert_eq!(
      value(assignment, output.selectors.is_transition),
      sels.is_transition
    );
    assert_eq!(
      value(assignment, output.selectors.inv_vanishing),
      sels.inv_vanishing
    );
    assert_eq!(
      value(assignment, output.zeta_next),
      domain.next_point(zeta).unwrap()
    );
    let next_acc = proof.intermediate_accumulators[i];
    let publics: Vec<ExtVal> = [beta, gamma, acc, next_acc]
      .iter()
      .flat_map(|v| v.as_basis_coefficients_slice())
      .map(|&v: &Val| ExtVal::from(v))
      .collect();
    let empty = [vec![], vec![]];
    let preprocessed = system.preprocessed_indices[i]
      .map_or(empty.as_slice(), |slot| {
        &proof.preprocessed_opened_values.as_ref().unwrap()[slot]
      });
    let view = VarValues {
      preprocessed: [&preprocessed[0], &preprocessed[1]],
      main: [
        &proof.stage_1_opened_values[i][0],
        &proof.stage_1_opened_values[i][1],
      ],
      stage2: [
        &proof.stage_2_opened_values[i][0],
        &proof.stage_2_opened_values[i][1],
      ],
      publics: &publics,
      is_first_row: sels.is_first_row,
      is_last_row: sels.is_last_row,
      is_transition: sels.is_transition,
    };
    let mut nodes = Vec::new();
    circuit.graph.sweep(&view, &mut nodes);
    assert_eq!(output.nodes.len(), nodes.len());
    for (&wire, &native) in output.nodes.iter().zip(&nodes) {
      assert_eq!(value(assignment, wire), native);
    }
    let g = Val::two_adic_generator(usize::from(parity::LOG_HEIGHT));
    let norm = (Val::from_usize(parity::HEIGHT) * g).inverse();
    let delta = std::array::from_fn::<_, 2, _>(|k| {
      (publics[6 + k] - publics[4 + k]) * norm
    });
    let mut constraints = circuit.graph.constraint_values(&nodes);
    multi_stark::lookup::logup_constraint_values(
      &circuit.graph.lookups,
      &nodes,
      view.stage2[0],
      view.stage2[1],
      &publics,
      &delta,
      sels.is_last_row,
      <Val as BinomiallyExtendable<2>>::W,
      2,
      circuit.lookup_group_size,
      &mut constraints,
    );
    assert_eq!(output.constraints.len(), constraints.len());
    for (&wire, &native) in output.constraints.iter().zip(&constraints) {
      assert_eq!(value(assignment, wire), native);
    }
    let composition =
      constraints.into_iter().fold(ExtVal::ZERO, |acc, c| acc * alpha + c);
    assert_eq!(value(assignment, output.composition), composition);
    let basis =
      <ExtVal as BasedVectorSpace<Val>>::ith_basis_element(1).unwrap();
    let power = zeta.exp_power_of_2(usize::from(parity::LOG_HEIGHT));
    let quotient: ExtVal = proof.quotient_opened_values[i][0]
      .as_chunks::<2>()
      .0
      .iter()
      .zip(power.powers())
      .map(|(chunk, power)| (chunk[0] + basis * chunk[1]) * power)
      .sum();
    assert_eq!(value(assignment, output.quotient), quotient);
    assert_eq!(composition * sels.inv_vanishing, quotient);
    acc = next_acc;
  }
}

#[test]
fn quadratic_gadgets_match_native_arithmetic_and_reject_zero_inverse() {
  let mut builder = CircuitBuilder::<Val>::new();
  let a = Q::input(&mut builder, "a");
  let b = Q::input(&mut builder, "b");
  let sum = a.add(&mut builder, b);
  let difference = a.sub(&mut builder, b);
  let product = a.mul(&mut builder, b);
  let inverse = a.inverse(&mut builder);
  let power = a.exp_power_of_2(&mut builder, 7);
  let circuit = builder.finish();
  for i in 0..32 {
    let a_value =
      ExtVal::from_basis_coefficients_slice(&[Val::from_u32(i), Val::ONE])
        .unwrap();
    let b_value =
      ExtVal::from_basis_coefficients_slice(&[Val::from_u32(2 * i), -Val::ONE])
        .unwrap();
    let mut witness = circuit.witness();
    adapter::set_extension(&mut witness, a, a_value).unwrap();
    adapter::set_extension(&mut witness, b, b_value).unwrap();
    let assignment = witness.generate().unwrap();
    assert_eq!(value(&assignment, sum), a_value + b_value);
    assert_eq!(value(&assignment, difference), a_value - b_value);
    assert_eq!(value(&assignment, product), a_value * b_value);
    assert_eq!(value(&assignment, inverse), a_value.inverse());
    assert_eq!(value(&assignment, power), a_value.exp_power_of_2(7));
  }
  let mut witness = circuit.witness();
  adapter::set_extension(&mut witness, a, ExtVal::ZERO).unwrap();
  adapter::set_extension(&mut witness, b, ExtVal::ONE).unwrap();
  assert!(matches!(witness.generate(), Err(WitnessError::HintFailed { .. })));
}

#[test]
fn parity_algebra_matches_native_for_multiple_proofs_with_one_circuit() {
  let (system, key) = System::new(parity::config(), parity::circuit_inputs());
  let mut builder = CircuitBuilder::new();
  let inputs = AlgebraicInputs::allocate(&mut builder, &system.circuits, &[3]);
  let outputs = constrain_algebraic_checks(
    &mut builder,
    &system.circuits,
    &[parity::LOG_HEIGHT; 2],
    &inputs,
  );
  let circuit = builder.finish();
  println!(
    "Parity algebra: {} values, {} gates",
    circuit.num_values(),
    circuit.gates().len()
  );
  for function in parity::Function::ALL {
    for n in [0, 1, 17, 100, 127] {
      let claim = parity::claim(function, n, function.result(n));
      let witness =
        SystemWitness::from_stage_1(parity::traces(function, n), &system);
      let proof = system.prove(&key, &claim, witness);
      system.verify(&claim, &proof).unwrap();
      let challenges = adapter::challenges(&system, &proof, &[&claim]);
      let assignment =
        assignment(&circuit, &inputs, &proof, &claim, challenges).unwrap();
      assert_eq!(assignment.public_values(), claim);
      check_intermediates(
        &system,
        &proof,
        &[&claim],
        challenges,
        &outputs,
        &assignment,
      );
    }
  }
}

#[test]
fn parity_algebra_rejects_tampered_claim_openings_accumulators_and_challenges()
{
  let (system, key) = System::new(parity::config(), parity::circuit_inputs());
  let claim = parity::claim(parity::Function::Even, 100, true);
  let proof = system.prove(
    &key,
    &claim,
    SystemWitness::from_stage_1(
      parity::traces(parity::Function::Even, 100),
      &system,
    ),
  );
  let challenges = adapter::challenges(&system, &proof, &[&claim]);
  let mut builder = CircuitBuilder::new();
  let inputs = AlgebraicInputs::allocate(&mut builder, &system.circuits, &[3]);
  constrain_algebraic_checks(
    &mut builder,
    &system.circuits,
    &[parity::LOG_HEIGHT; 2],
    &inputs,
  );
  let circuit = builder.finish();
  assert!(assignment(&circuit, &inputs, &proof, &claim, challenges).is_ok());
  for i in 0..claim.len() {
    let mut wrong = claim.clone();
    wrong[i] += Val::ONE;
    assert!(assignment(&circuit, &inputs, &proof, &wrong, challenges).is_err());
  }
  for i in 0..2 {
    let mut wrong = proof.clone();
    wrong.intermediate_accumulators[i] += ExtVal::ONE;
    assert!(assignment(&circuit, &inputs, &wrong, &claim, challenges).is_err());
    for kind in 0..4 {
      let mut wrong = proof.clone();
      let row = match kind {
        0 => &mut wrong.stage_1_opened_values[i][0],
        1 => &mut wrong.stage_2_opened_values[i][0],
        2 => &mut wrong.preprocessed_opened_values.as_mut().unwrap()[i][0],
        _ => &mut wrong.quotient_opened_values[i][0],
      };
      row[0] += ExtVal::ONE;
      assert!(
        assignment(&circuit, &inputs, &wrong, &claim, challenges).is_err(),
        "circuit {i}, kind {kind}"
      );
    }
  }
  for i in 0..4 {
    let mut wrong = challenges;
    wrong[i] += ExtVal::ONE;
    assert!(assignment(&circuit, &inputs, &proof, &claim, wrong).is_err());
  }
  // The vanishing denominator must be nonzero, not an unconstrained hint.
  let mut on_domain = challenges;
  on_domain[3] = ExtVal::ONE;
  assert!(assignment(&circuit, &inputs, &proof, &claim, on_domain).is_err());
  // Explicitly pin this milestone's security boundary: corrupted FRI
  // data is invisible to the algebraic gadget and needs the future PCS
  // constraints. Native verification does reject the same corruption.
  let mut bad_fri = proof.clone();
  bad_fri.opening_proof.final_poly[0] += ExtVal::ONE;
  assert!(system.verify(&claim, &bad_fri).is_err());
  assert!(assignment(&circuit, &inputs, &bad_fri, &claim, challenges).is_ok());
}

#[test]
fn parity_algebra_can_be_proved_but_is_not_yet_an_inner_proof_verifier() {
  let (system, key) = System::new(parity::config(), parity::circuit_inputs());
  let claim = parity::claim(parity::Function::Odd, 17, true);
  let proof = system.prove(
    &key,
    &claim,
    SystemWitness::from_stage_1(
      parity::traces(parity::Function::Odd, 17),
      &system,
    ),
  );
  let challenges = adapter::challenges(&system, &proof, &[&claim]);
  let mut builder = CircuitBuilder::new();
  let inputs = AlgebraicInputs::allocate(&mut builder, &system.circuits, &[3]);
  constrain_algebraic_checks(
    &mut builder,
    &system.circuits,
    &[parity::LOG_HEIGHT; 2],
    &inputs,
  );
  // Bind every supplied boundary value publicly for this algebra-only
  // proof. Otherwise private, unauthenticated openings are freely chosen.
  adapter::expose_boundary(&mut builder, &inputs);
  let compiled =
    builder.finish().lower_to_multi_stark(Val::from_u32(101)).unwrap();
  let assignment =
    assignment(compiled.circuit(), &inputs, &proof, &claim, challenges)
      .unwrap();
  // The outer statement is explicitly the complete algebraic instance,
  // not merely the parity result and not an authenticated inner proof.
  let expected = adapter::statement(&proof, &[&claim], challenges);
  assert_eq!(assignment.public_values(), expected);
  let outer_claims = compiled.claims(&expected).unwrap();
  let refs: Vec<_> = outer_claims.iter().map(Vec::as_slice).collect();
  let (outer, outer_key) =
    System::new(parity::config(), compiled.circuit_inputs());
  let outer_proof = outer.prove_multiple_claims(
    &outer_key,
    &refs,
    SystemWitness::from_stage_1(compiled.traces(&assignment).unwrap(), &outer),
  );
  outer.verify_multiple_claims(&refs, &outer_proof).unwrap();
  let mut wrong = outer_claims.clone();
  wrong[1][3] += Val::ONE;
  assert!(
    outer
      .verify_multiple_claims(
        &wrong.iter().map(Vec::as_slice).collect::<Vec<_>>(),
        &outer_proof
      )
      .is_err()
  );
}

#[test]
fn algebra_handles_selectors_next_rows_no_lookups_and_multiple_quotient_slices()
{
  use multi_stark::expr::Expr;
  use multi_stark::p3_matrix::dense::RowMajorMatrix;
  use multi_stark::system::CircuitInputs;

  let x = Expr::main(0);
  let square = Expr::main(1);
  let cube = Expr::main(2);
  let square_error = square.clone() + -(x.clone() * x.clone());
  let input = CircuitInputs {
    main_width: 3,
    constraints: vec![
      square_error.clone(),
      x.clone() * x.clone() * x.clone() - cube,
      Expr::IsFirstRow * x.clone(),
      Expr::IsLastRow
        * (x.clone() - Expr::constant(Val::from_usize(parity::HEIGHT - 1))),
      Expr::IsTransition * (Expr::main_next(0) - x - Expr::constant(Val::ONE)),
      Expr::public(0) * square_error,
    ],
    ..Default::default()
  };
  let (system, key) = System::new(parity::config(), [input]);
  assert_eq!(system.circuits[0].quotient_degree(), 2);
  let trace = RowMajorMatrix::new(
    (0..parity::HEIGHT)
      .flat_map(|n| {
        let x = Val::from_usize(n);
        [x, x * x, x * x * x]
      })
      .collect(),
    3,
  );
  let proof = system.prove_multiple_claims(
    &key,
    &[],
    SystemWitness::from_stage_1(vec![trace], &system),
  );
  system.verify_multiple_claims(&[], &proof).unwrap();
  let challenges = adapter::challenges(&system, &proof, &[]);
  let mut builder = CircuitBuilder::new();
  let inputs = AlgebraicInputs::allocate(&mut builder, &system.circuits, &[]);
  let outputs = constrain_algebraic_checks(
    &mut builder,
    &system.circuits,
    &[parity::LOG_HEIGHT],
    &inputs,
  );
  let circuit = builder.finish();
  let mut witness = circuit.witness();
  adapter::assign(&mut witness, &inputs, &proof, &[], challenges).unwrap();
  let assignment = witness.generate().unwrap();
  check_intermediates(&system, &proof, &[], challenges, &outputs, &assignment);
  // Exercise the non-leading quotient slice independently of the first.
  let mut wrong = proof.clone();
  wrong.quotient_opened_values[0][0][2] += ExtVal::ONE;
  let mut witness = circuit.witness();
  adapter::assign(&mut witness, &inputs, &wrong, &[], challenges).unwrap();
  assert!(witness.generate().is_err());
}

#[test]
fn grouped_logup_coordinates_match_native_for_full_and_partial_groups() {
  use multi_stark::expr::Expr;
  use multi_stark::lookup::Lookup;
  use multi_stark::system::CircuitInputs;
  use multi_stark::types::CommitmentParameters;
  use multi_stark::types::FriParameters;
  use p3_matrix::dense::RowMajorMatrix;
  let claim = vec![Val::from_u8(17)];
  for group in [1, 2, 3, 8] {
    let x = Expr::main(0);
    let pair = vec![x.clone(), x.clone() * x.clone()];
    let (system, key) = System::new(
      GoldilocksBlake3Config::new(
        CommitmentParameters { log_blowup: 4, cap_height: 0 },
        FriParameters {
          num_queries: 2,
          log_final_poly_len: 0,
          max_log_arity: 1,
          commit_proof_of_work_bits: 0,
          query_proof_of_work_bits: 0,
        },
      ),
      [CircuitInputs {
        main_width: 1,
        preprocessed: Some(RowMajorMatrix::new_col(
          (0..parity::HEIGHT).map(|i| Val::from_bool(i == 0)).collect(),
        )),
        lookups: vec![
          Lookup::pull(Expr::preprocessed(0), vec![x.clone()]),
          Lookup::push(x.clone(), vec![x.clone()]),
          Lookup::pull(x, vec![Expr::main(0)]),
          Lookup::push(Expr::constant(Val::ONE), pair.clone()),
          Lookup::pull(Expr::constant(Val::ONE), pair),
        ],
        lookup_group_size: group,
        ..Default::default()
      }],
    );
    let proof = system.prove(
      &key,
      &claim,
      SystemWitness::from_stage_1(
        vec![RowMajorMatrix::new_col(vec![claim[0]; parity::HEIGHT])],
        &system,
      ),
    );
    system.verify(&claim, &proof).unwrap();
    let challenges = adapter::challenges(&system, &proof, &[&claim]);
    let mut b = CircuitBuilder::new();
    let inputs = AlgebraicInputs::allocate(&mut b, &system.circuits, &[1]);
    let outputs = constrain_algebraic_checks(
      &mut b,
      &system.circuits,
      &[parity::LOG_HEIGHT],
      &inputs,
    );
    let circuit = b.finish();
    let a = assignment(&circuit, &inputs, &proof, &claim, challenges).unwrap();
    check_intermediates(&system, &proof, &[&claim], challenges, &outputs, &a);
    for point in 0..2 {
      for column in 0..system.circuits[0].stage_2_width {
        // Only the first accumulator carries across rows. Other
        // next-row columns are authenticated by PCS, not logUp.
        if point == 1 && column >= 2 {
          continue;
        }
        let mut forged = proof.clone();
        forged.stage_2_opened_values[0][point][column] += ExtVal::ONE;
        assert!(
          assignment(&circuit, &inputs, &forged, &claim, challenges).is_err(),
          "group {group}, point {point}, column {column}"
        );
      }
    }
  }
}
