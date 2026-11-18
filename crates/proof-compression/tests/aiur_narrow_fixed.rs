//! The fixed-key narrow stage (`CompressNarrowFixed::step_v1`) on an actual
//! Init CompressGL proof. Inputs are large and machine-local, so the test is
//! ignored by default:
//!
//! - `IX_AIUR_NARROW_FIXED_ARTIFACT`: `compress_narrow_fixed_export` output
//!   for the CompressGL key;
//! - `IX_AIUR_NARROW_FIXED_GL`: the CompressGL stage's directory
//!   (`gl-key.bin`, `gl/claims.bin`, `gl/proof.bin`, `policy.bin`, as
//!   `compress_gl_packed_chain` writes them);
//! - the Ignition SRS through the release setup loader (`IX_PARAMS_DIR` or
//!   `IX_KZG_SRS`).
//!
//! The program verifies the proof with the key in its own tables; the key
//! channel is left empty, so nothing read from it can matter.

use aiur::{
  Execution, artifact::WidePackage, hints::HintChannels, maps::MapOverrides,
  trace::TracePlan,
};
use ark_ec::{AffineRepr, CurveGroup};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ix_proof_compression::{
  aiur_backend::{
    Bn254,
    compress_bn::{
      Accumulator, PACKED_NARROW_FIXED_ENTRY, PackedCapacity, PackedPolicy,
      PolicyDigest, PublicInputs, Stage, StatementDigest,
    },
    fq, g1, kzg_advice as wire,
  },
  kzg::{Scalar, VerifierParams, curve::G1Affine},
  pipeline::SetupConfig,
};
use std::{path::PathBuf, sync::Arc};

fn variable(name: &str) -> PathBuf {
  std::env::var_os(name)
    .map_or_else(|| panic!("{name} is required"), PathBuf::from)
}

/// The failure, which must be an Aiur assertion containing `reason`.
fn refused(result: Result<Execution<Bn254>, String>, reason: &str) {
  match result {
    Ok(_) => panic!("accepted; expected {reason}"),
    Err(error) => assert!(error.contains(reason), "{error} is not {reason}"),
  }
}

struct Fixture {
  plan: TracePlan<'static, Bn254>,
}

impl Fixture {
  fn execute(
    &self,
    claims: &[u8],
    proof: &[u8],
    policy: &[u8],
    public: PublicInputs,
  ) -> Result<Execution<Bn254>, String> {
    let mut hints = HintChannels::new();
    aiur::library::u32::register(&mut hints, Bn254)?;
    aiur::library::u64::register(&mut hints, Bn254)?;
    fq::register(&mut hints)?;
    g1::register(&mut hints)?;
    wire::register(&mut hints)?;
    wire::Inputs::new(
      vec![],
      claims.to_vec(),
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
      .execute(PACKED_NARROW_FIXED_ENTRY, public.arguments().to_vec())
      .map_err(|e| e.to_string())
  }
}

/// The statement of a CompressGL claim `[tag, entry, reserved(8),
/// statement(8)]` in `kzg_advice::claims_bytes` form.
fn gl_statement(claims: &[u8]) -> [u8; 32] {
  let mut statement = [0u8; 32];
  for i in 0..8 {
    let at = 16 + 32 * (10 + i);
    statement[4 * i..4 * i + 4].copy_from_slice(&claims[at..at + 4]);
  }
  statement
}

fn pairing_holds(output: &[Scalar], parameters: &VerifierParams) -> bool {
  let accumulator = Accumulator::from_words(output).unwrap();
  accumulator.check_pairing(parameters).is_ok()
}

#[test]
#[ignore = "requires IX_AIUR_NARROW_FIXED_ARTIFACT (compress_narrow_fixed_export output), IX_AIUR_NARROW_FIXED_GL (an Init CompressGL stage directory) and the Ignition SRS (IX_PARAMS_DIR or IX_KZG_SRS)"]
fn narrow_fixed_binds_policy_key_stage_statement_and_pairing() {
  let bytes = std::fs::read(variable("IX_AIUR_NARROW_FIXED_ARTIFACT")).unwrap();
  let dir = variable("IX_AIUR_NARROW_FIXED_GL");
  let package = WidePackage::decode(&bytes).unwrap();
  let trace = package.trace.unwrap();
  let mut program = package.program.check_with(Bn254).unwrap();
  program.track_depth(&trace).unwrap();
  let fixture =
    Fixture { plan: TracePlan::new(Arc::new(program), trace).unwrap() };
  let claims = std::fs::read(dir.join("gl/claims.bin")).unwrap();
  let proof = std::fs::read(dir.join("gl/proof.bin")).unwrap();
  let policy = std::fs::read(dir.join("policy.bin")).unwrap();
  let gl_key = std::fs::read(dir.join("gl-key.bin")).unwrap();
  let setup = SetupConfig::from_env(false).unwrap();
  let capacity = PackedCapacity {
    log_cap: 1,
    quotient_degree: 1,
    lookup_quotient_budget: None,
  };
  let config = capacity.config(&setup).unwrap();
  let parameters = multi_stark::config::ProofConfig::pcs(&config).parameters();
  let public_of =
    |policy: &[u8], stage: u32, statement: [u8; 32]| PublicInputs {
      policy: PolicyDigest::from_trusted(*blake3::hash(policy).as_bytes()),
      stage: Stage::new(stage).unwrap(),
      statement: StatementDigest::new(statement),
    };
  let statement = gl_statement(&claims);
  let honest = public_of(&policy, 1, statement);

  // Honest acceptance: the deferred pair passes the Ignition pairing check.
  let record = fixture.execute(&claims, &proof, &policy, honest).unwrap();
  assert_eq!(record.output.len(), 4);
  assert!(pairing_holds(&record.output, parameters));

  // Statement and stage are bound.
  let mut changed = statement;
  changed[5] ^= 1;
  refused(
    fixture.execute(&claims, &proof, &policy, public_of(&policy, 1, changed)),
    "compression GL statement",
  );
  refused(
    fixture.execute(&claims, &proof, &policy, public_of(&policy, 2, statement)),
    "verifies the CompressGL proof",
  );

  // The policy bytes must hash to the public digest.
  let mut flipped = policy.clone();
  let last = flipped.len() - 1;
  flipped[last] ^= 1;
  refused(
    fixture.execute(&claims, &proof, &flipped, honest),
    "compression policy digest mismatch",
  );

  // A well-formed policy authorizing another CompressGL key digest is refused
  // under its own digest: the verified key is the embedded one.
  let parsed = PackedPolicy::from_chain_bytes(parameters, &policy).unwrap();
  let entry =
    u32::from_le_bytes(policy[8 + 128 + 32..8 + 128 + 36].try_into().unwrap());
  assert_eq!(&policy[8 + 128..8 + 128 + 32], blake3::hash(&gl_key).as_bytes());
  let mut other = *blake3::hash(&gl_key).as_bytes();
  other[0] ^= 1;
  let foreign = PackedPolicy::chain(parameters, (other, entry), parsed.bn())
    .unwrap()
    .to_bytes();
  refused(
    fixture.execute(
      &claims,
      &proof,
      &foreign,
      public_of(&foreign, 1, statement),
    ),
    "unauthorized compression predecessor key",
  );
  // So is a policy naming another CompressGL entry.
  let renamed = PackedPolicy::chain(
    parameters,
    (*blake3::hash(&gl_key).as_bytes(), entry + 1),
    parsed.bn(),
  )
  .unwrap()
  .to_bytes();
  refused(
    fixture.execute(
      &claims,
      &proof,
      &renamed,
      public_of(&renamed, 1, statement),
    ),
    "compression GL entry",
  );

  // A forged opening witness executes but fails the pairing check.
  let w2_at = proof.len() - 32;
  let w2 = G1Affine::deserialize_compressed(&proof[w2_at..]).unwrap();
  let shifted = (w2.into_group() + G1Affine::generator()).into_affine();
  let mut forged = proof.clone();
  let mut encoded = vec![];
  shifted.serialize_compressed(&mut encoded).unwrap();
  forged[w2_at..].copy_from_slice(&encoded);
  let record = fixture.execute(&claims, &forged, &policy, honest).unwrap();
  assert!(!pairing_holds(&record.output, parameters));
}
