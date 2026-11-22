use aiur::{
  artifact::WidePackage, bytecode::Instruction, field::FieldBackend,
  hints::HintChannels, trace::TracePlan,
};
use ark_bn254::{Fq, Fr, G1Affine};
use ark_ec::AffineRepr;
use ark_ff::{BigInteger, PrimeField};
use ix_proof_compression::{
  aiur_backend::{Bn254, fq, g1, pairing},
  kzg::Scalar,
  recursive::native_field::integer,
};
use num_bigint::BigUint;
use std::{collections::HashSet, path::PathBuf, sync::Arc};

fn plan() -> TracePlan<'static, Bn254> {
  let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .join("../aiur/tests/fixtures/bn254-g1-encoding.ixa");
  let package = WidePackage::decode(&std::fs::read(path).unwrap()).unwrap();
  let trace = package.trace.unwrap();
  let mut program = package.program.check_with(Bn254).unwrap();
  program.track_depth(&trace).unwrap();
  TracePlan::new(Arc::new(program), trace).unwrap()
}
fn channels() -> HintChannels<Scalar> {
  let mut hints = HintChannels::new();
  fq::register(&mut hints).unwrap();
  g1::register(&mut hints).unwrap();
  hints
}
fn power(bit: usize) -> Scalar {
  Scalar(Fr::from_le_bytes_mod_order(
    &(BigUint::from(1u8) << bit).to_bytes_le(),
  ))
}
fn raw(points: [G1Affine; 2]) -> Vec<Scalar> {
  points.into_iter().flat_map(g1::encode).collect()
}

#[test]
fn canonical_four_chunk_encoding_matches_compressed_point_convention() {
  let plan = plan();
  let hints = channels();
  let executor = plan.program().prepare_hint_channels(&[], &hints).unwrap();
  let g = G1Affine::generator();
  assert_eq!(
    g1::encode_chunks([g, -g]).unwrap(),
    [Bn254.one(), Bn254.zero(), Bn254.one(), power(127)]
  );
  assert_eq!(
    g1::encode_chunks([G1Affine::identity(); 2]).unwrap(),
    [Bn254.zero(), power(126), Bn254.zero(), power(126)]
  );
  let parameters =
    ix_proof_compression::pipeline::ignition_parameters().unwrap();
  let (powers, _) = pairing::verifier_anchors(&parameters);
  for points in [
    [g, -g],
    [G1Affine::identity(); 2],
    [g, G1Affine::identity()],
    [powers[1], -powers[0]],
  ] {
    let chunks = g1::encode_chunks(points).unwrap();
    assert_eq!(g1::decode_chunks(&chunks).unwrap(), points);
    assert_eq!(
      executor.execute("G1EncodingTest::pack", raw(points)).unwrap().output,
      chunks
    );
    assert_eq!(
      executor
        .execute("G1EncodingTest::unpack", chunks.to_vec())
        .unwrap()
        .output,
      raw(points)
    );
  }
  let maximum = power(128) - Bn254.one();
  assert_eq!(
    executor.execute("G1EncodingTest::chunk", vec![maximum]).unwrap().output,
    vec![Bn254.from_u64(255); 16]
  );
  assert!(executor.execute("G1EncodingTest::chunk", vec![power(128)]).is_err());
  let mut chunks = g1::encode_chunks([g, -g]).unwrap();
  chunks[0] = power(128);
  assert!(g1::decode_chunks(&chunks).is_err());
}

fn poisoned(plan: &TracePlan<'_, Bn254>) -> HintChannels<Scalar> {
  let mut result = HintChannels::new();
  let mut seen = HashSet::new();
  for function in &plan.program().program().functions {
    for instruction in &function.code {
      let Instruction::Hint { channel, r#type, key_type, .. } = instruction
      else {
        continue;
      };
      if !seen.insert(channel.clone()) {
        continue;
      }
      let name = channel.clone();
      result
        .insert(
          channel,
          key_type.clone(),
          r#type.clone(),
          move |input, output| {
            let candidate = if name == "bn254.g1.decode" {
              g1::encode(G1Affine::generator()).to_vec()
            } else if name == "bn254.g1.u128_bytes"
              && integer(input[0]).bits() > 128
            {
              vec![Bn254.zero(); 16]
            } else {
              g1::advice(&name, input)?
            };
            output.copy_from_slice(&candidate);
            Ok(())
          },
        )
        .unwrap();
    }
  }
  result
}

#[test]
fn source_rejects_overwide_chunks_and_noncanonical_points_with_forged_advice() {
  let plan = plan();
  let hints = poisoned(&plan);
  let executor = plan.program().prepare_hint_channels(&[], &hints).unwrap();
  assert!(executor.execute("G1EncodingTest::chunk", vec![power(128)]).is_err());
  assert!(
    executor
      .execute("G1EncodingTest::chunk", vec![Bn254.neg(Bn254.one())])
      .is_err()
  );
  let g = G1Affine::generator();
  let mut alias = g1::encode_chunks([G1Affine::identity(), g]).unwrap();
  alias[0] = Bn254.one();
  assert!(g1::decode_chunks(&alias).is_err());
  assert!(executor.execute("G1EncodingTest::unpack", alias.to_vec()).is_err());
  let mut both_flags = alias;
  both_flags[1] = power(126) + power(127);
  assert!(
    executor.execute("G1EncodingTest::unpack", both_flags.to_vec()).is_err()
  );
  let encoded = Fq::MODULUS.to_bytes_le();
  let mut noncanonical = g1::encode_chunks([g, g]).unwrap();
  for (index, block) in encoded.as_chunks::<16>().0.iter().enumerate() {
    noncanonical[index] = Scalar(Fr::from(u128::from_le_bytes(*block)));
  }
  assert!(g1::decode_chunks(&noncanonical).is_err());
  assert!(
    executor.execute("G1EncodingTest::unpack", noncanonical.to_vec()).is_err()
  );
}
