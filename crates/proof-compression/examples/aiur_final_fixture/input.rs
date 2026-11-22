use std::sync::Arc;

use aiur::field::FieldBackend;
use ark_ec::{AffineRepr, CurveGroup};
use ix_proof_compression::{
  aiur_backend::{
    Bn254, kzg::VerifyingKey, kzg_advice as wire,
    pairing::final_program::Configuration,
  },
  kzg::{KzgConfig, Srs},
};
use multi_stark::{
  config::ProofConfig,
  expr::Expr,
  lookup::Lookup,
  system::{CircuitInputs, System, SystemWitness},
};
use p3_matrix::dense::RowMajorMatrix;

pub(crate) struct Fixture {
  pub configuration: Configuration,
  pub statement: [u8; 32],
  pub key: Vec<u8>,
  pub claims: Vec<u8>,
  pub proof: Vec<u8>,
  pub forged_opening: Vec<u8>,
  pub policy: Vec<u8>,
}

impl Fixture {
  pub(crate) fn new() -> Self {
    let statement = *blake3::hash(b"Aiur final verifier regression").as_bytes();
    let mut claim = vec![Bn254.one(), Bn254.from_u64(31)];
    claim.extend([Bn254.zero(); 8]);
    claim.extend(wire::digest_words(&statement));
    let input = CircuitInputs {
      main_width: 2,
      preprocessed: Some(RowMajorMatrix::new(
        vec![Bn254.one(), Bn254.one(), Bn254.from_u64(2), Bn254.zero()],
        2,
      )),
      constraints: vec![
        Expr::main(0) - Expr::preprocessed(0),
        Expr::main(1) - Expr::preprocessed(1),
      ],
      lookups: vec![Lookup::pull(
        Expr::main(1),
        claim.iter().copied().map(Expr::constant).collect(),
      )],
      ..Default::default()
    };
    let srs = Arc::new(Srs::unsafe_dev_setup_prefix(
      64,
      (1 << 24) - 1,
      b"aiur-final-test-only",
    ));
    let (system, proving_key) =
      System::new(KzgConfig::with_max_trace_len(srs, 1 << 24, 8), [input]);
    let witness = SystemWitness::from_stage_1(
      vec![RowMajorMatrix::new(
        vec![Bn254.one(), Bn254.one(), Bn254.from_u64(2), Bn254.zero()],
        2,
      )],
      &system,
    );
    let proof = system.prove(&proving_key, &claim, witness);
    system.verify(&claim, &proof).unwrap();
    let mut forged = proof.clone();
    forged.opening_proof.0[0] = (forged.opening_proof.0[0]
      + ark_bn254::G1Affine::generator())
    .into_affine();
    assert!(system.verify(&claim, &forged).is_err());
    let key = VerifyingKey::from_system(&system).unwrap();
    let key_bytes = wire::key_bytes(&key).unwrap();
    let parameters = system.config.pcs().verifier_params();
    let policy = wire::Policy::new(
      parameters,
      *blake3::hash(&key_bytes).as_bytes(),
      31,
      [0; 32],
      47,
    )
    .unwrap();
    Self {
      configuration: Configuration::new(&policy, parameters, 1, true).unwrap(),
      statement,
      key: key_bytes,
      claims: wire::claims_bytes(&[claim]).unwrap(),
      proof: wire::proof_bytes(&proof).unwrap(),
      forged_opening: wire::proof_bytes(&forged).unwrap(),
      policy: policy.to_bytes(),
    }
  }

  pub(crate) fn inputs(&self) -> wire::Inputs {
    wire::Inputs::new(
      self.key.clone(),
      self.claims.clone(),
      self.proof.clone(),
      self.policy.clone(),
    )
    .unwrap()
  }
}
