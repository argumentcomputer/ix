use ix_proof_compression::foreign::KzgCircuitExt;

use std::sync::Arc;

use ix_proof_compression::kzg::KzgConfig;
use ix_proof_compression::kzg::Scalar;
use ix_proof_compression::kzg::Srs;
use multi_stark::batch::Retention;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::plonkish::WitnessError;
use multi_stark::system::System;
use multi_stark::system::SystemWitness;
use multi_stark::traits::Algebra;
use multi_stark::traits::Field;

#[test]
fn regenerated_kzg_shards_preserve_global_copy_constraints() {
  let f = Scalar::from_u8;
  let mut b = CircuitBuilder::new();
  let x = b.input("x");
  let double = b.add(x, x);
  b.mul(x, x);
  b.expose_public(double);
  let compiled = b.finish().lower_to_multi_stark_sharded(f(81), 2).unwrap();
  assert_eq!(compiled.main_heights(), [2, 2, 2]);
  let mut witness = compiled.witness();
  witness.set(x, f(5)).unwrap();
  let assignment = witness.generate().unwrap();
  let shards = compiled.trace_shards(&assignment).unwrap();
  assert_eq!(shards.len(), 3);
  assert!(matches!(shards.traces(3), Err(WitnessError::ShardIndex { .. })));
  let claims = vec![compiled.claims(&[f(10)]).unwrap(), vec![], vec![]];
  let (system, key) = System::new(
    KzgConfig::new(Arc::new(Srs::unsafe_dev_setup(2, b"shards")), 8),
    compiled.kzg_circuit_inputs(2, 8).unwrap(),
  );
  let mut calls = [0; 3];
  let proof = system.prove_batch_with(
    &key,
    &claims,
    vec![],
    Retention::Regenerate,
    |shard| {
      calls[shard] += 1;
      SystemWitness::from_stage_1(shards.traces(shard).unwrap(), &system)
    },
  );
  assert_eq!(calls, [2; 3]);
  system.verify_batch(&proof).unwrap();
  assert!(
    proof
      .proofs
      .iter()
      .any(|p| p.intermediate_accumulators.last() != Some(&Scalar::ZERO))
  );
  let retained = system.prove_batch_with(
    &key,
    &claims,
    vec![],
    Retention::Retain,
    |shard| SystemWitness::from_stage_1(shards.traces(shard).unwrap(), &system),
  );
  assert_eq!(retained.to_bytes().unwrap(), proof.to_bytes().unwrap());

  let forged = system.prove_batch_with(
    &key,
    &claims,
    vec![],
    Retention::Regenerate,
    |shard| {
      let mut traces = shards.traces(shard).unwrap();
      if shard == 1 {
        // 7*7=49 satisfies this shard's arithmetic, but x=5 elsewhere.
        assert_eq!(&traces[1].values[..3], &[f(5), f(5), f(25)]);
        traces[1].values[..3].copy_from_slice(&[f(7), f(7), f(49)]);
      }
      SystemWitness::from_stage_1(traces, &system)
    },
  );
  assert!(system.verify_batch(&forged).is_err());

  // Reprove with a disconnected partition omitted, rather than merely
  // corrupting an existing proof. The required activation claim rejects it.
  let omitted = system.prove_batch_with(
    &key,
    &claims[..2],
    vec![],
    Retention::Regenerate,
    |shard| SystemWitness::from_stage_1(shards.traces(shard).unwrap(), &system),
  );
  assert!(system.verify_batch(&omitted).is_err());
  let mut wrong = proof.clone();
  wrong.preamble.headers[0].claims[1][3] += Scalar::ONE;
  assert!(system.verify_batch(&wrong).is_err());
}
