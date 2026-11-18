//! The narrow-stage terminal relation (`CompressFinalNarrow`) on an actual
//! Init narrow stage. Inputs are large and machine-local, so the test is
//! ignored by default:
//!
//! - `IX_AIUR_NARROW_TERMINAL_ARTIFACT`: `compress_final_narrow_export`
//!   output for the stage's configuration and key;
//! - `IX_AIUR_NARROW_STAGE`: the narrow stage's directory (`key.bin`,
//!   `claims.bin`, `proof.bin`, `narrow.json`, as `aiur_template_v2_init
//!   --save` writes them);
//! - `IX_AIUR_NARROW_POLICY`: the chain policy (`IXAUKG01`);
//! - the Ignition SRS through the release setup loader (`IX_PARAMS_DIR` or
//!   `IX_KZG_SRS`).

use aiur::{
  Execution, artifact::WidePackage, field::FieldBackend, hints::HintChannels,
  maps::MapOverrides, trace::TracePlan,
};
use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ix_proof_compression::{
  aiur_backend::{
    Bn254,
    compress_bn::{PackedCapacity, PackedPolicy},
    fq, g1,
    kzg::Compiler,
    kzg_advice as wire,
    pairing::{
      final_program::{
        Configuration, NARROW_ACCUMULATOR_ENTRY, statement_arguments,
      },
      verifier_anchors,
    },
    plonk::{TERMINAL_FORMAT, scs},
  },
  kzg::{Scalar, VerifierParams, curve::G1Affine},
  pipeline::SetupConfig,
};
use std::{path::PathBuf, sync::Arc};

fn variable(name: &str) -> PathBuf {
  std::env::var_os(name)
    .map_or_else(|| panic!("{name} is required"), PathBuf::from)
}

struct Fixture {
  plan: TracePlan<'static, Bn254>,
  key: Vec<u8>,
  claims: Vec<Vec<Scalar>>,
  proof: Vec<u8>,
  policy: Vec<u8>,
  statement: [u8; 32],
}

impl Fixture {
  fn execute(
    &self,
    claims: &[Vec<Scalar>],
    proof: &[u8],
    policy: &[u8],
    statement: &[u8; 32],
  ) -> Result<Execution<Bn254>, String> {
    let mut hints = HintChannels::new();
    aiur::library::u32::register(&mut hints, Bn254)?;
    aiur::library::u64::register(&mut hints, Bn254)?;
    fq::register(&mut hints)?;
    g1::register(&mut hints)?;
    wire::register(&mut hints)?;
    wire::Inputs::new(
      self.key.clone(),
      wire::claims_bytes(claims)?,
      proof.to_vec(),
      policy.to_vec(),
    )?
    .register(&mut hints)?;
    let mut maps = MapOverrides::new();
    aiur::library::u8::register_maps(self.plan.program(), &mut maps)?;
    self
      .plan
      .program()
      .prepare_hint_channels(&[], &hints)
      .map_err(|e| e.clone())?
      .with_map_overrides(&maps)
      .map_err(|e| e.clone())?
      .execute(
        NARROW_ACCUMULATOR_ENTRY,
        statement_arguments(statement).to_vec(),
      )
      .map_err(|e| e.to_string())
  }
}

/// Claims bytes as written by `kzg_advice::claims_bytes`: magic, count, then
/// each claim's length and canonical 32-byte little-endian scalars.
fn decode_claims(bytes: &[u8]) -> Vec<Vec<Scalar>> {
  let u32_at = |at: usize| {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap()) as usize
  };
  let mut at = 8;
  let count = u32_at(at);
  at += 4;
  let mut claims = vec![];
  for _ in 0..count {
    let len = u32_at(at);
    at += 4;
    let mut claim = vec![];
    for _ in 0..len {
      claim.push(Scalar(
        ark_bn254::Fr::deserialize_compressed(&bytes[at..at + 32]).unwrap(),
      ));
      at += 32;
    }
    claims.push(claim);
  }
  assert_eq!(at, bytes.len());
  assert_eq!(wire::claims_bytes(&claims).unwrap(), bytes);
  claims
}

fn pairing_holds(output: &[Scalar], parameters: &VerifierParams) -> bool {
  let pair =
    [g1::decode(&output[..9]).unwrap(), g1::decode(&output[9..]).unwrap()];
  let (_, anchors) = verifier_anchors(parameters);
  ark_bn254::Bn254::multi_pairing(pair, anchors).0
    == <ark_bn254::Bn254 as Pairing>::TargetField::from(1u8)
}

#[test]
#[ignore = "requires IX_AIUR_NARROW_TERMINAL_ARTIFACT (compress_final_narrow_export output), IX_AIUR_NARROW_STAGE (an Init narrow stage directory), IX_AIUR_NARROW_POLICY and the Ignition SRS (IX_PARAMS_DIR or IX_KZG_SRS)"]
fn narrow_terminal_binds_statement_policy_stage_claim_and_pairing() {
  let bytes =
    std::fs::read(variable("IX_AIUR_NARROW_TERMINAL_ARTIFACT")).unwrap();
  let stage_dir = variable("IX_AIUR_NARROW_STAGE");
  let package = WidePackage::decode(&bytes).unwrap();
  let trace = package.trace.unwrap();
  let mut program = package.program.check_with(Bn254).unwrap();
  program.track_depth(&trace).unwrap();
  let plan = TracePlan::new(Arc::new(program), trace).unwrap();
  let record: serde_json::Value = serde_json::from_slice(
    &std::fs::read(stage_dir.join("narrow.json")).unwrap(),
  )
  .unwrap();
  let hex = record["statement"].as_str().unwrap();
  let mut statement = [0u8; 32];
  for (i, byte) in statement.iter_mut().enumerate() {
    *byte = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap();
  }
  let fixture = Fixture {
    plan,
    key: std::fs::read(stage_dir.join("key.bin")).unwrap(),
    claims: decode_claims(
      &std::fs::read(stage_dir.join("claims.bin")).unwrap(),
    ),
    proof: std::fs::read(stage_dir.join("proof.bin")).unwrap(),
    policy: std::fs::read(variable("IX_AIUR_NARROW_POLICY")).unwrap(),
    statement,
  };
  let setup = SetupConfig::from_env(false).unwrap();
  let capacity = PackedCapacity {
    log_cap: 1,
    quotient_degree: 1,
    lookup_quotient_budget: None,
  };
  let config = capacity.config(&setup).unwrap();
  let parameters = multi_stark::config::ProofConfig::pcs(&config).parameters();
  let honest = |claims: &[Vec<Scalar>],
                proof: &[u8],
                policy: &[u8],
                statement: &[u8; 32]| {
    fixture.execute(claims, proof, policy, statement)
  };

  // Honest acceptance: the folded pair passes the Ignition pairing check.
  let record = honest(
    &fixture.claims,
    &fixture.proof,
    &fixture.policy,
    &fixture.statement,
  )
  .unwrap();
  assert_eq!(record.output.len(), 18);
  assert!(pairing_holds(&record.output, parameters));

  // Terminal contract: two public limbs, eighteen private affine outputs.
  let policy =
    PackedPolicy::from_chain_bytes(parameters, &fixture.policy).unwrap();
  let narrow_stage = record_stage(&stage_dir);
  let configuration =
    Configuration::narrow(&policy, parameters, narrow_stage + 1).unwrap();
  let compiler = Compiler::new(&fixture.plan).unwrap();
  let capacities: Vec<_> = compiler
    .row_counts(&record)
    .unwrap()
    .into_iter()
    .map(|n| n.max(1))
    .collect();
  let arguments = statement_arguments(&fixture.statement);
  let public = fixture
    .plan
    .public_args(&record, NARROW_ACCUMULATOR_ENTRY, &arguments)
    .unwrap();
  let terminal_stage = scs::stage(
    &fixture.plan,
    &compiler,
    &capacities,
    NARROW_ACCUMULATOR_ENTRY,
    &public,
    &record.output,
  )
  .unwrap();
  assert_eq!(terminal_stage["format"], TERMINAL_FORMAT);
  assert_eq!(
    (
      terminal_stage["public_inputs"].as_u64(),
      terminal_stage["private_outputs"].as_u64()
    ),
    (Some(2), Some(18))
  );
  scs::pairing(&fixture.plan, NARROW_ACCUMULATOR_ENTRY, &configuration)
    .unwrap();
  // A configuration for another terminal stage does not match the artifact.
  let other =
    Configuration::narrow(&policy, parameters, narrow_stage + 2).unwrap();
  assert!(
    scs::pairing(&fixture.plan, NARROW_ACCUMULATOR_ENTRY, &other).is_err()
  );

  // Statement, policy and every claim component are bound.
  let mut changed = fixture.statement;
  changed[5] ^= 1;
  assert!(
    honest(&fixture.claims, &fixture.proof, &fixture.policy, &changed).is_err()
  );
  let mut policy_bytes = fixture.policy.clone();
  let last = policy_bytes.len() - 1;
  policy_bytes[last] ^= 1;
  assert!(
    honest(&fixture.claims, &fixture.proof, &policy_bytes, &fixture.statement)
      .is_err()
  );
  let one = Bn254.one();
  // Chunk tag, instance key, policy word, stage, statement word and
  // accumulator word.
  for (chunk, index) in [(0, 0), (0, 1), (0, 2), (1, 4), (1, 6), (3, 2)] {
    let mut claims = fixture.claims.clone();
    claims[chunk][index] += one;
    assert!(
      honest(&claims, &fixture.proof, &fixture.policy, &fixture.statement)
        .is_err(),
      "claim {chunk}:{index}"
    );
  }
  let mut claims = fixture.claims.clone();
  claims.swap(1, 2);
  assert!(
    honest(&claims, &fixture.proof, &fixture.policy, &fixture.statement)
      .is_err()
  );
  let mut claims = fixture.claims.clone();
  claims.pop();
  assert!(
    honest(&claims, &fixture.proof, &fixture.policy, &fixture.statement)
      .is_err()
  );
  // Moving a value across a chunk boundary keeps the flattened call.
  let mut claims = fixture.claims.clone();
  let moved = claims[0].pop().unwrap();
  claims[1].insert(2, moved);
  assert!(
    honest(&claims, &fixture.proof, &fixture.policy, &fixture.statement)
      .is_err()
  );

  // A forged opening witness executes but fails the pairing check.
  let w2_at = fixture.proof.len() - 32;
  let w2 = G1Affine::deserialize_compressed(&fixture.proof[w2_at..]).unwrap();
  let shifted = (w2.into_group() + G1Affine::generator()).into_affine();
  let mut proof = fixture.proof.clone();
  let mut encoded = vec![];
  shifted.serialize_compressed(&mut encoded).unwrap();
  proof[w2_at..].copy_from_slice(&encoded);
  let record =
    honest(&fixture.claims, &proof, &fixture.policy, &fixture.statement)
      .unwrap();
  assert!(!pairing_holds(&record.output, parameters));
}

fn record_stage(dir: &std::path::Path) -> u32 {
  let record: serde_json::Value =
    serde_json::from_slice(&std::fs::read(dir.join("narrow.json")).unwrap())
      .unwrap();
  u32::try_from(record["stage"].as_u64().unwrap()).unwrap()
}
