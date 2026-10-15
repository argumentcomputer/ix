use super::*;
use crate::kzg::Srs;
use ark_bls12_381::Fq;
use multi_stark::{
  expr::Expr,
  lookup::Lookup,
  plonkish::Assignment,
  system::{CircuitInputs, ProverKey, SystemWitness},
};
use p3_matrix::dense::RowMajorMatrix;
use std::sync::Arc;

struct Fixture {
  system: System<KzgConfig>,
  key: ProverKey<KzgConfig>,
  srs: Arc<Srs>,
}

impl Fixture {
  fn new() -> Self {
    let srs = Arc::new(Srs::unsafe_dev_setup_prefix(
      4,
      6,
      b"recursive-reuse-development-only",
    ));
    let (system, key) = System::new(
      KzgConfig::new(srs.clone(), 2),
      [CircuitInputs {
        main_width: 1,
        preprocessed: Some(RowMajorMatrix::new_col(vec![
          Scalar::ONE,
          Scalar::ZERO,
          Scalar::ZERO,
          Scalar::ZERO,
        ])),
        constraints: vec![
          Expr::main_next(0) - Expr::main(0),
          Expr::preprocessed_next(0) * (Expr::main_next(0) - Expr::main(0)),
        ],
        lookups: vec![Lookup::pull(
          Expr::preprocessed(0),
          vec![
            Expr::constant(Scalar::from_u8(93)),
            Expr::constant(Scalar::ONE),
            Expr::constant(Scalar::ZERO),
            Expr::main(0),
          ],
        )],
        ..Default::default()
      }],
    );
    Self { system, key, srs }
  }

  fn proof(&self, word: u64) -> (Proof<KzgConfig>, Vec<Vec<Scalar>>) {
    let value = Scalar::from_u64(word);
    let claims =
      vec![vec![Scalar::from_u8(93), Scalar::ONE, Scalar::ZERO, value]];
    let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
    let proof = self.system.prove_multiple_claims(
      &self.key,
      &refs,
      SystemWitness::from_stage_1(
        vec![RowMajorMatrix::new_col(vec![value; 4])],
        &self.system,
      ),
    );
    self.system.verify_multiple_claims(&refs, &proof).unwrap();
    (proof, claims)
  }
}

fn layout() -> LayoutPolicy {
  LayoutPolicy {
    namespace: Scalar::from_u8(94),
    max_computation_height: 1 << 27,
    max_table_height: 1 << 27,
  }
}

fn schema(claims: &[Vec<Scalar>]) -> ClaimSchema {
  ClaimSchema::from_claims(claims, &[(0, 3)]).unwrap()
}

fn relation_digest(circuit: &Circuit<Scalar>) -> [u8; 32] {
  let mut hash = blake3::Hasher::new();
  hash.update(&(circuit.num_values() as u64).to_le_bytes());
  for gate in circuit.gates() {
    for value in gate.wires {
      hash.update(&(value.index() as u64).to_le_bytes());
    }
    for scalar in gate.coefficients {
      for limb in scalar.canonical_limbs_le() {
        hash.update(&limb.to_le_bytes());
      }
    }
  }
  for table in circuit.tables() {
    for row in table.rows() {
      hash.update(&(row.len() as u64).to_le_bytes());
      for value in row {
        for limb in value.canonical_limbs_le() {
          hash.update(&limb.to_le_bytes());
        }
      }
    }
  }
  for lookup in circuit.lookups() {
    hash.update(&(lookup.table.index() as u64).to_le_bytes());
    for value in &lookup.values {
      hash.update(&(value.index() as u64).to_le_bytes());
    }
  }
  for value in circuit.public_values() {
    hash.update(&(value.index() as u64).to_le_bytes());
  }
  *hash.finalize().as_bytes()
}

fn assignment_digest(
  circuit: &Circuit<Scalar>,
  assignment: &Assignment<Scalar>,
) -> [u8; 32] {
  let mut hash = blake3::Hasher::new();
  for value in circuit
    .gates()
    .iter()
    .flat_map(|gate| gate.wires)
    .chain(
      circuit.lookups().iter().flat_map(|lookup| lookup.values.iter().copied()),
    )
    .chain(circuit.public_values().iter().copied())
  {
    for limb in assignment.value(value).unwrap().canonical_limbs_le() {
      hash.update(&limb.to_le_bytes());
    }
  }
  *hash.finalize().as_bytes()
}

#[test]
fn recursive_frontend_reuses_two_statements_and_returns_first() {
  let fixture = Fixture::new();
  let (proof_a, claims_a) = fixture.proof(0x1234_5678_90ab_cdef);
  let (proof_b, claims_b) = fixture.proof(0x2345_6789_01ab_cdef);
  assert_ne!(
    proof_a.commitments.stage_1_trace,
    proof_b.commitments.stage_1_trace
  );
  let plan =
    Plan::new(&fixture.system, &[2], schema(&claims_a), layout()).unwrap();
  let id = plan.identity();
  let Compiled { circuit, bindings } = plan.compile().unwrap();
  let relation = relation_digest(&circuit);
  let compiled = circuit
    .lower_to_multi_stark_sharded(
      layout().namespace,
      layout().max_computation_height,
    )
    .unwrap()
    .merge_table_traces(layout().max_table_height)
    .unwrap();
  assert_eq!(compiled.main_heights().len(), 1);
  assert_eq!(compiled.num_circuits(), 2);
  let mut first_digest = None;
  for (index, (proof, claims)) in
    [(&proof_a, &claims_a), (&proof_b, &claims_b), (&proof_a, &claims_a)]
      .into_iter()
      .enumerate()
  {
    let candidate =
      Plan::new(&fixture.system, &[2], schema(claims), layout()).unwrap();
    assert_eq!(candidate.identity(), id);
    let assignment = bindings
      .check(candidate.identity(), proof, claims, compiled.witness())
      .unwrap();
    let digest = assignment_digest(compiled.circuit(), &assignment);
    if index == 0 {
      first_digest = Some(digest);
    }
    if index == 1 {
      assert_ne!(Some(digest), first_digest);
    }
    if index == 2 {
      assert_eq!(Some(digest), first_digest);
    }
    let fresh = candidate.build(proof, claims).unwrap();
    assert_eq!(relation_digest(&fresh.circuit), relation);
    let fresh_assignment = fresh.check().unwrap();
    assert_eq!(assignment.public_values(), fresh_assignment.public_values());
    assert_eq!(digest, assignment_digest(&fresh.circuit, &fresh_assignment));
  }
  assert!(bindings.check(id, &proof_a, &claims_b, compiled.witness()).is_err());
  let mut wrong = id;
  wrong[0] ^= 1;
  assert!(
    bindings.check(wrong, &proof_a, &claims_a, compiled.witness()).is_err()
  );
}

#[test]
fn recursive_schema_rejects_malformed_and_constant_claims() {
  let claims = vec![vec![Scalar::from_u8(9), Scalar::from_u8(17)]];
  assert!(ClaimSchema::from_claims(&claims, &[(0, 1), (0, 1)]).is_err());
  assert!(ClaimSchema::from_claims(&claims, &[(1, 0)]).is_err());
  assert!(ClaimSchema::from_claims(&claims, &[(0, 2)]).is_err());
  let schema = ClaimSchema::from_claims(&claims, &[(0, 1)]).unwrap();
  let mut changed = claims.clone();
  changed[0][0] += Scalar::ONE;
  assert!(schema.validate(&changed).is_err());
  changed = claims.clone();
  changed[0][1] = Scalar::from_limbs_le([0, 1, 0, 0]);
  assert!(schema.validate(&changed).is_err());
  assert!(ClaimSchema::from_claims(&changed, &[(0, 1)]).is_err());
  changed[0].pop();
  assert!(schema.validate(&changed).is_err());
  assert!(schema.validate(&[]).is_err());
}

#[test]
fn recursive_compact_preflight_rejects_malformed_resource_dimensions() {
  let mut fixture = Fixture::new();
  let (proof, claims) = fixture.proof(17);
  let encoded =
    crate::kzg::compact::FixedProofCodec::new(&fixture.system, &[2])
      .unwrap()
      .encode(&proof)
      .unwrap();
  let plan =
    Plan::new(&fixture.system, &[2], schema(&claims), layout()).unwrap();
  plan.validate_compact_len(encoded.len()).unwrap();
  assert!(plan.validate_compact_len(encoded.len() - 1).is_err());
  assert!(plan.validate_compact_len(encoded.len() + 1).is_err());
  let mut overflow = plan.shape.clone();
  overflow.rounds[Round::Main.index()].widths[0] = usize::MAX;
  assert!(overflow.checked_compact_len().is_err());
  drop(plan);
  fixture.system.circuits[0].main_width = 1 << 24;
  let huge =
    Plan::new(&fixture.system, &[2], schema(&claims), layout()).unwrap();
  assert!(huge.validate_compact_len(encoded.len()).is_err());
  drop(huge);
  fixture.system.circuits[0].main_width = usize::MAX;
  assert!(Plan::new(&fixture.system, &[2], schema(&claims), layout()).is_err());
}

#[test]
fn recursive_exact_shape_rejects_every_payload_dimension() {
  let fixture = Fixture::new();
  let (proof, claims) = fixture.proof(17);
  let plan =
    Plan::new(&fixture.system, &[2], schema(&claims), layout()).unwrap();
  let reject = |changed: Proof<KzgConfig>| {
    assert!(plan.validate_request(&changed, &claims).is_err())
  };
  let mutations: Vec<Box<dyn Fn(&mut Proof<KzgConfig>)>> = vec![
    Box::new(|p| {
      p.active.pop();
    }),
    Box::new(|p| p.active.push(true)),
    Box::new(|p| p.active[0] = false),
    Box::new(|p| {
      p.log_degrees.pop();
    }),
    Box::new(|p| p.log_degrees.push(2)),
    Box::new(|p| p.log_degrees[0] = 1),
    Box::new(|p| {
      p.intermediate_accumulators.pop();
    }),
    Box::new(|p| p.intermediate_accumulators.push(Scalar::ZERO)),
    Box::new(|p| p.intermediate_accumulators[0] = Scalar::ONE),
    Box::new(|p| {
      p.opening_proof.0.pop();
    }),
    Box::new(|p| p.opening_proof.0.push(G1Affine::identity())),
    Box::new(|p| p.preprocessed_opened_values = None),
  ];
  for mutate in mutations {
    let mut changed = proof.clone();
    mutate(&mut changed);
    reject(changed);
  }
  for round in [Round::Main, Round::Stage2, Round::Quotient] {
    for kind in 0..2 {
      let mut changed = proof.clone();
      let commitment = match round {
        Round::Main => &mut changed.commitments.stage_1_trace,
        Round::Stage2 => &mut changed.commitments.stage_2_trace,
        Round::Quotient => &mut changed.commitments.quotient_chunks,
        Round::Fixed => unreachable!(),
      };
      match kind {
        0 => {
          commitment.0.pop();
        },
        _ => commitment.0[0].push(G1Affine::identity()),
      }
      reject(changed);
    }
  }
  for round in Round::ALL {
    for kind in 0..4 {
      let mut changed = proof.clone();
      let openings = match round {
        Round::Fixed => changed.preprocessed_opened_values.as_mut().unwrap(),
        Round::Main => &mut changed.stage_1_opened_values,
        Round::Stage2 => &mut changed.stage_2_opened_values,
        Round::Quotient => &mut changed.quotient_opened_values,
      };
      match kind {
        0 => {
          openings.pop();
        },
        1 => openings[0].push(vec![]),
        2 => openings[0][0].push(Scalar::ZERO),
        _ => {
          openings[0][0].pop();
        },
      }
      reject(changed);
    }
  }
}

#[test]
fn recursive_profile_identity_binds_metadata_and_schema() {
  let mut fixture = Fixture::new();
  let (_, claims) = fixture.proof(17);
  let id = |system: &System<KzgConfig>, schema, layout| {
    Plan::new(system, &[2], schema, layout).unwrap().identity()
  };
  let baseline = id(&fixture.system, schema(&claims), layout());
  let mut other_claims = claims.clone();
  other_claims[0][3] += Scalar::ONE;
  assert_eq!(baseline, id(&fixture.system, schema(&other_claims), layout()));
  other_claims[0][0] += Scalar::ONE;
  assert_ne!(baseline, id(&fixture.system, schema(&other_claims), layout()));
  let schema_a = ClaimSchema::from_claims(&claims, &[(0, 0), (0, 3)]).unwrap();
  let schema_b = ClaimSchema::from_claims(&claims, &[(0, 3), (0, 0)]).unwrap();
  assert_ne!(
    id(&fixture.system, schema_a, layout()),
    id(&fixture.system, schema_b, layout())
  );
  for policy in [
    LayoutPolicy { namespace: Scalar::from_u8(95), ..layout() },
    LayoutPolicy { max_computation_height: 1 << 26, ..layout() },
    LayoutPolicy { max_table_height: 1 << 26, ..layout() },
  ] {
    assert_ne!(baseline, id(&fixture.system, schema(&claims), policy));
  }
  let point = fixture.system.preprocessed_commit.as_ref().unwrap().0[0][0];
  fixture.system.preprocessed_commit.as_mut().unwrap().0[0][0] =
    (point * ark_bls12_381::Fr::from(2u8)).into_affine();
  assert_ne!(baseline, id(&fixture.system, schema(&claims), layout()));
  fixture.system.preprocessed_commit.as_mut().unwrap().0[0][0] = point;
  fixture.system.circuits[0].graph.nodes.push(Node::Const(Scalar::from_u8(43)));
  fixture.system.circuits[0].graph.degrees.push(0);
  assert_ne!(baseline, id(&fixture.system, schema(&claims), layout()));
  fixture.system.circuits[0].graph.nodes.pop();
  fixture.system.circuits[0].graph.degrees.pop();
  let srs = fixture.srs.clone();
  let altered = Srs::from_public_powers(
    srs.g1.clone(),
    srs.g2,
    srs.tau_g2,
    crate::kzg::PublicSetup { max_degree: 6, id: [73; 32] },
  )
  .unwrap();
  fixture.system.config = KzgConfig::new(Arc::new(altered), 2);
  assert_ne!(baseline, id(&fixture.system, schema(&claims), layout()));
  fixture.system.preprocessed_indices.clear();
  assert!(Plan::new(&fixture.system, &[2], schema(&claims), layout()).is_err());
}

#[test]
fn recursive_profile_rejects_invalid_graph_and_fixed_points_before_construction()
 {
  let mut fixture = Fixture::new();
  let (_, claims) = fixture.proof(17);
  assert!(Plan::new(&fixture.system, &[1], schema(&claims), layout()).is_err());
  assert!(Plan::new(&fixture.system, &[], schema(&claims), layout()).is_err());
  fixture.system.circuits[0].graph.nodes.push(Node::Public(4));
  fixture.system.circuits[0].graph.degrees.push(0);
  assert!(Plan::new(&fixture.system, &[2], schema(&claims), layout()).is_err());
  fixture.system.circuits[0].graph.nodes.pop();
  fixture.system.circuits[0].graph.degrees.pop();
  fixture.system.preprocessed_commit.as_mut().unwrap().0[0][0] =
    G1Affine::new_unchecked(Fq::from(0u8), Fq::from(0u8));
  assert!(Plan::new(&fixture.system, &[2], schema(&claims), layout()).is_err());
}

#[test]
fn recursive_shape_deduplicates_log_zero_opening_points() {
  let mut fixture = Fixture::new();
  fixture.system.circuits[0].preprocessed_height = 1;
  let plan = Plan::new(
    &fixture.system,
    &[0],
    ClaimSchema::from_claims(&[], &[]).unwrap(),
    layout(),
  )
  .unwrap();
  assert_eq!(plan.shape.opening_generators, [Scalar::ONE]);
}

#[test]
fn recursive_profile_rejects_keccak_before_circuit_construction() {
  let mut fixture = Fixture::new();
  let (_, claims) = fixture.proof(7);
  let plan =
    Plan::new(&fixture.system, &[2], schema(&claims), layout()).unwrap();
  let mut profile = plan.profile;
  profile.transcript_kind = crate::kzg::TranscriptKind::Keccak256;
  assert!(matches!(
    Plan::from_profile(&profile, &[2], schema(&claims), layout()),
    Err(error) if error.contains("requires a BLAKE3 inner transcript")
  ));
  fixture.system.config = fixture
    .system
    .config
    .clone()
    .with_transcript(crate::kzg::TranscriptKind::Keccak256);
  assert!(matches!(
    Plan::new(&fixture.system, &[2], schema(&claims), layout()),
    Err(error) if error.contains("requires a BLAKE3 inner transcript")
  ));
}
