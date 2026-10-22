#[path = "support/verifier_audit.rs"]
mod fixture;

use ix_proof_compression::fri::*;
use multi_stark::batch::ShardInput;
use multi_stark::p3_field::BasedVectorSpace;
use multi_stark::p3_field::PrimeCharacteristicRing;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::types::ExtVal;
use multi_stark::types::Val;
use p3_symmetric::MerkleCap;

#[test]
fn every_verifier_boundary_rejects_tampering_without_native_prevalidation() {
  let (system, pk) = fixture::setup();
  let claims = fixture::claims();
  for envelope in [Envelope::Ordinary, Envelope::SingleBatch] {
    let ordinary = system.prove_multiple_claims(
      &pk,
      &[&claims[0]],
      fixture::witness(&system),
    );
    let batch = system.prove_batch(
      &pk,
      vec![ShardInput {
        claims: claims.clone(),
        witness: fixture::witness(&system),
      }],
      vec![],
    );
    system.verify_multiple_claims(&[&claims[0]], &ordinary).unwrap();
    system.verify_batch(&batch).unwrap();
    let shape =
      FixedPcsShape::from_profile(&system, &fixture::ACTIVE, &fixture::LOGS);
    let mut b = CircuitBuilder::new();
    b.enable_compact_blake3();
    let bytes = ByteGadgets::new(&mut b);
    let claim = vec![vec![b.public_input("tag"), b.public_input("value")]];
    let inputs = match envelope {
      Envelope::Ordinary => {
        constrain_fixed_verifier(&mut b, &bytes, &system, &shape, claim)
      },
      Envelope::SingleBatch => constrain_single_batch_verifier(
        &mut b,
        &bytes,
        &system,
        &shape,
        claim,
        &[],
      ),
    };
    let circuit = b.finish();
    let good = match envelope {
      Envelope::Ordinary => {
        expand_pcs_witness(&system, &shape, &ordinary, &[&claims[0]])
      },
      Envelope::SingleBatch => {
        expand_single_batch_witness(&system, &shape, &batch, &[])
      },
    }
    .unwrap();
    let mut w = circuit.witness();
    good.assign(&mut w, &inputs).unwrap();
    w.generate().unwrap();
    let mut count = 0;
    let mut reject =
      |name: &str, bad: ExpandedPcsWitness, native_changed: bool| {
        if native_changed {
          let rejected = match envelope {
            Envelope::Ordinary => system
              .verify_multiple_claims(&[&bad.claims[0]], &bad.proof)
              .is_err(),
            Envelope::SingleBatch => {
              let mut forged = batch.clone();
              forged.proofs[0] = bad.proof.clone();
              forged.preamble.headers[0].claims = bad.claims.clone();
              system.verify_batch(&forged).is_err()
            },
          };
          assert!(rejected, "native accepted {envelope:?} {name}");
        }
        // Mutate after normalization. Assignment only checks dimensions;
        // it never calls native cryptographic verification.
        let mut w = circuit.witness();
        bad.assign(&mut w, &inputs).unwrap();
        assert!(w.generate().is_err(), "circuit accepted {envelope:?} {name}");
        count += 1;
      };
    for column in 0..2 {
      let mut bad = good.clone();
      bad.claims[0][column] += Val::ONE;
      reject("public claim", bad, true);
    }
    for c in 0..4 {
      for coordinate in 0..2 {
        let unit = ExtVal::from_basis_coefficients_fn(|i| {
          if i == coordinate { Val::ONE } else { Val::ZERO }
        });
        let mut bad = good.clone();
        bad.challenges[c] += unit;
        reject("transcript challenge", bad, false);
      }
    }
    for matrix in 0..good.proof.intermediate_accumulators.len() {
      let mut bad = good.clone();
      bad.proof.intermediate_accumulators[matrix] += ExtVal::ONE;
      reject("accumulator chain and final balance", bad, true);
    }
    for batch_index in 0..4 {
      let openings = match batch_index {
        0 => &good.proof.stage_1_opened_values,
        1 => &good.proof.stage_2_opened_values,
        2 => &good.proof.quotient_opened_values,
        _ => good.proof.preprocessed_opened_values.as_ref().unwrap(),
      };
      for (matrix, rows) in openings.iter().enumerate() {
        for (point, row) in rows.iter().enumerate() {
          for column in 0..row.len() {
            for coordinate in 0..2 {
              let mut bad = good.clone();
              let openings = match batch_index {
                0 => &mut bad.proof.stage_1_opened_values,
                1 => &mut bad.proof.stage_2_opened_values,
                2 => &mut bad.proof.quotient_opened_values,
                _ => bad.proof.preprocessed_opened_values.as_mut().unwrap(),
              };
              openings[matrix][point][column] +=
                ExtVal::from_basis_coefficients_fn(|i| {
                  if i == coordinate { Val::ONE } else { Val::ZERO }
                });
              reject("OOD opening coordinate", bad, true);
            }
          }
        }
      }
    }
    for i in 0..3 {
      let mut bad = good.clone();
      let root = match i {
        0 => &mut bad.proof.commitments.stage_1_trace,
        1 => &mut bad.proof.commitments.stage_2_trace,
        _ => &mut bad.proof.commitments.quotient_chunks,
      };
      let mut bytes = root.roots()[0];
      bytes[0] ^= 1;
      *root = MerkleCap::new(vec![bytes]);
      reject("trace commitment", bad, true);
    }
    for query in 0..shape.queries {
      for batch_index in 0..4 {
        for matrix in 0..shape.widths[batch_index].len() {
          for column in 0..shape.widths[batch_index][matrix] {
            let mut bad = good.clone();
            bad.proof.opening_proof.input_openings[batch_index]
              .opened_values[query][matrix][column] += Val::ONE;
            reject("queried input column", bad, true);
          }
        }
        for depth in 0..good.input_paths[query][batch_index].len() {
          let mut bad = good.clone();
          bad.input_paths[query][batch_index][depth][0] ^= 1;
          reject("input Merkle path", bad, false);
        }
      }
      for round in 0..usize::from(shape.log_trace) {
        let mut bad = good.clone();
        bad.proof.opening_proof.commit_phase_openings[round].sibling_values
          [query][0] += ExtVal::ONE;
        reject("FRI sibling and fold", bad, true);
        for depth in 0..good.fri_paths[query][round].len() {
          let mut bad = good.clone();
          bad.fri_paths[query][round][depth][0] ^= 1;
          reject("FRI Merkle path", bad, false);
        }
      }
    }
    for round in 0..usize::from(shape.log_trace) {
      let mut bad = good.clone();
      let mut bytes =
        bad.proof.opening_proof.commit_phase_commits[round].roots()[0];
      bytes[0] ^= 1;
      bad.proof.opening_proof.commit_phase_commits[round] =
        MerkleCap::new(vec![bytes]);
      reject("FRI commitment", bad, true);
      let mut bad = good.clone();
      bad.proof.opening_proof.commit_pow_witnesses[round] += Val::ONE;
      reject("commit grinding", bad, true);
    }
    let mut bad = good.clone();
    bad.proof.opening_proof.query_pow_witness += Val::ONE;
    reject("query grinding", bad, true);
    let mut bad = good.clone();
    bad.proof.opening_proof.final_poly[0] += ExtVal::ONE;
    reject("final polynomial", bad, true);
    println!("{envelope:?}: {count} adversarial assignments rejected");
  }
}
