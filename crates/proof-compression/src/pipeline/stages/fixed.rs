//! A fixed verifier for the normalizer's all-active, one-shard output.
//! Only the claim, proof and memory interval ends vary between invocations.
use super::{Prepared, Result};
use crate::fri::*;
use aiur::{synthesis::AiurProof, vk_codec::AiurVerifyingKey};
use multi_stark::{
  batch::{BatchMessage, BatchPreamble, ShardHeader},
  plonkish::{Circuit, CircuitBuilder, Value},
  types::Val,
};
use p3_field::{PrimeCharacteristicRing, PrimeField64};

#[derive(Clone)]
pub struct FixedRoot {
  log_height: u32,
  memory_widths: Vec<usize>,
  claim_len: usize,
}

struct Built {
  circuit: Circuit<Val>,
  public: Vec<Value>,
  ends: Vec<Value>,
  inputs: FixedVerifierInputs,
  shape: FixedPcsShape,
}

impl FixedRoot {
  /// Widths and claim length come from the locally compiled aggregate backend.
  pub fn new(
    log_height: u32,
    memory_widths: Vec<usize>,
    claim_len: usize,
  ) -> Result<Self> {
    if !(1..=26).contains(&log_height)
      || claim_len == 0
      || claim_len > 1024
      || memory_widths.len() > 4096
      || memory_widths.iter().any(|&w| w == 0 || w > u32::MAX as usize)
      || memory_widths.windows(2).any(|w| w[0] >= w[1])
    {
      return Err("invalid fixed root configuration".into());
    }
    Ok(Self { log_height, memory_widths, claim_len })
  }

  fn preamble(
    &self,
    key: &AiurVerifyingKey,
    expected: &[Val],
    ends: &[Val],
  ) -> Result<BatchPreamble<multi_stark::types::GoldilocksBlake3Config>> {
    let mut messages = vec![];
    for (&width, &end) in self.memory_widths.iter().zip(ends) {
      messages.push(BatchMessage::pull(
        aiur::memory::Memory::memseg_args(Val::from_usize(width), Val::ZERO)
          .to_vec(),
      ));
      messages.push(BatchMessage::push(
        aiur::memory::Memory::memseg_args(Val::from_usize(width), end).to_vec(),
      ));
    }
    Ok(BatchPreamble {
      headers: vec![ShardHeader {
        active: vec![true; key.num_circuits()],
        log_degrees: key
          .system()
          .circuits
          .iter()
          .map(|c| {
            if c.preprocessed_height == 0 {
              u8::try_from(self.log_height).expect("validated root height")
            } else {
              u8::try_from(c.preprocessed_height.ilog2())
                .expect("usize log fits u8")
            }
          })
          .collect(),
        // The policy check does not read commitments; use the trusted fixed
        // commitment as a placeholder, never any prover-supplied data.
        stage_1_trace: key
          .system()
          .preprocessed_commit
          .clone()
          .ok_or("missing Aiur fixed tables")?,
        claims: vec![expected.to_vec()],
      }],
      messages,
    })
  }

  fn build(
    &self,
    key: &AiurVerifyingKey,
    limits: VerifierLimits,
  ) -> Result<Built> {
    let preamble = self.preamble(
      key,
      &vec![Val::ZERO; self.claim_len],
      &vec![Val::ZERO; self.memory_widths.len()],
    )?;
    key
      .validate_preamble(&preamble.headers[0].claims[0], &preamble)
      .map_err(|e| format!("fixed root policy: {e:?}"))?;
    let verifier = VerifierKey::from_system(key.system());
    let header = &preamble.headers[0];
    let plan = VerifierPlan::validate(
      &verifier,
      ProofProfile {
        envelope: Envelope::SingleBatch,
        active: header.active.clone(),
        log_degrees: header.log_degrees.clone(),
        claim_lengths: vec![self.claim_len],
        message_lengths: vec![3; preamble.messages.len()],
        max_field_retries: DEFAULT_FIELD_RETRIES,
      },
      limits,
    )?;
    let shape = plan.shape().clone();
    let mut b = CircuitBuilder::new();
    b.enable_compact_blake3();
    let public: Vec<_> = (0..self.claim_len)
      .map(|i| b.public_input(format!("claim[{i}]")))
      .collect();
    let ends: Vec<_> = (0..self.memory_widths.len())
      .map(|i| b.input(format!("memory_end[{i}]")))
      .collect();
    let mut messages = vec![];
    for (&width, &end) in self.memory_widths.iter().zip(&ends) {
      // 0 <= end <= 2^log_height: low bits must vanish if the top bit is 1.
      // This also establishes canonical integer ordering for Aiur's policy.
      let mut low = b.constant(Val::ZERO);
      for bit in 0..self.log_height {
        let v = b.hint("memory end bit", &[end], move |v| {
          Ok(Val::from_u64((v[0].as_canonical_u64() >> bit) & 1))
        });
        b.assert_bool(v);
        low =
          b.affine([low, v], [Val::ONE, Val::from_u64(1u64 << bit)], Val::ZERO);
      }
      let log = self.log_height;
      let top = b.hint("memory end top", &[end], move |v| {
        Ok(Val::from_u64((v[0].as_canonical_u64() >> log) & 1))
      });
      b.assert_bool(top);
      let value =
        b.affine([low, top], [Val::ONE, Val::from_u64(1u64 << log)], Val::ZERO);
      b.assert_equal(value, end);
      let overflow = b.mul(low, top);
      b.assert_zero(overflow);
      let channel = b.constant(aiur::shard::memseg_channel_value());
      let width = b.constant(Val::from_usize(width));
      let zero = b.constant(Val::ZERO);
      let minus = b.constant(Val::NEG_ONE);
      let one = b.constant(Val::ONE);
      messages.push(Message {
        args: vec![channel, width, zero],
        multiplicity: minus,
      });
      messages
        .push(Message { args: vec![channel, width, end], multiplicity: one });
    }
    let bytes = ByteGadgets::new(&mut b);
    let mut inputs = constrain_batch_verifier(
      &mut b,
      &bytes,
      key.system(),
      std::slice::from_ref(&shape),
      vec![vec![public.clone()]],
      &messages,
    );
    Ok(Built {
      circuit: b.finish(),
      public,
      ends,
      inputs: inputs.remove(0),
      shape,
    })
  }

  /// Construct the verifier without any certificate or proof witness.
  pub fn circuit(
    &self,
    key: &AiurVerifyingKey,
    limits: VerifierLimits,
  ) -> Result<Circuit<Val>> {
    Ok(self.build(key, limits)?.circuit)
  }

  pub fn prepare(
    &self,
    key: &AiurVerifyingKey,
    proof: &AiurProof,
    expected: &[Val],
    limits: VerifierLimits,
  ) -> Result<Prepared<Val>> {
    key
      .verify(expected, proof)
      .map_err(|e| format!("normalized root: {e:?}"))?;
    if expected.len() != self.claim_len
      || proof.preamble.headers.len() != 1
      || proof.preamble.messages.len() != 2 * self.memory_widths.len()
    {
      return Err(
        "root does not match the fixed normalization configuration".into(),
      );
    }
    let ends: Vec<_> = proof
      .preamble
      .messages
      .iter()
      .skip(1)
      .step_by(2)
      .map(|m| m.args[2])
      .collect();
    if ends.iter().any(|e| e.as_canonical_u64() > 1u64 << self.log_height) {
      return Err("memory closure exceeds normalization bound".into());
    }
    let mut preamble = self.preamble(key, expected, &ends)?;
    preamble.headers[0].stage_1_trace =
      proof.preamble.headers[0].stage_1_trace.clone();
    if preamble.headers != proof.preamble.headers
      || preamble
        .messages
        .iter()
        .zip(&proof.preamble.messages)
        .any(|(a, b)| a.args != b.args || a.multiplicity != b.multiplicity)
    {
      return Err(
        "root does not match the fixed normalization configuration".into(),
      );
    }
    let built = self.build(key, limits)?;
    let expanded = expand_batch_witness(
      key.system(),
      std::slice::from_ref(&built.shape),
      proof,
    )?;
    let mut witness = built.circuit.witness();
    for (&wire, &value) in
      built.public.iter().zip(expected).chain(built.ends.iter().zip(&ends))
    {
      witness.set(wire, value)?;
    }
    expanded[0].assign_proof(&mut witness, &built.inputs)?;
    let assignment = witness.generate()?;
    Ok(Prepared { circuit: built.circuit, assignment })
  }
}

#[cfg(test)]
mod tests {
  use super::super::setup;
  use super::*;
  use multi_stark::{
    batch::ShardInput,
    expr::Expr,
    lookup::Lookup,
    system::{CircuitInputs, System, SystemWitness},
    types::{CommitmentParameters, FriParameters, GoldilocksBlake3Config},
  };
  use p3_matrix::dense::RowMajorMatrix;

  #[test]
  fn normalized_aiur_execution_matches_the_fixed_verifier() -> Result<()> {
    use aiur::{bytecode::*, execute::IOBuffer, synthesis::AiurSystem};
    let cp = CommitmentParameters { log_blowup: 2, cap_height: 0 };
    let fp = FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 2,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    };
    let layout = FunctionLayout {
      input_size: 2,
      selectors: 1,
      auxiliaries: 2,
      lookups: 1,
    };
    let top = Toplevel {
      functions: vec![Function {
        body: Block {
          ops: vec![Op::Mul(0, 1)],
          ctrl: Ctrl::Return(0, vec![2]),
        },
        layout,
        entry: true,
        constrained: true,
      }],
      memory_sizes: vec![1],
      circuits: vec![Circuit { members: vec![0], layout }],
    };
    let system = AiurSystem::build(top, cp, fp);
    let key = AiurVerifyingKey::from_bytes(
      &aiur::vk_codec::aiur_system_to_bytes(&system)?,
    )?;
    let fixed = FixedRoot::new(4, vec![1], 5)?;
    let config = || GoldilocksBlake3Config::new(cp, fp);
    let local =
      setup::fri(fixed.circuit(&key, Default::default())?, config(), 1 << 16)?;
    for value in [3, 7] {
      let input = vec![Val::from_u32(value), Val::TWO];
      let mut io =
        IOBuffer { data: Default::default(), map: Default::default() };
      let (record, output) =
        system.toplevel().execute(0, input.clone(), &mut io)?;
      let (claim, proof) = system
        .prove_from_execution_normalized(0, &input, &io, record, &output, 4)?;
      let prepared = fixed.prepare(&key, &proof, &claim, Default::default())?;
      let (verifier, proof) = prepared.prove_fri(config(), 1 << 16)?;
      assert_eq!(verifier.to_bytes()?, local.to_bytes()?);
      local.verify(&proof, &claim)?;
    }
    Ok(())
  }

  #[test]
  fn fixed_key_binds_claims_and_enforces_memory_bounds() -> Result<()> {
    let cp = CommitmentParameters { log_blowup: 1, cap_height: 0 };
    let fp = FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 2,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    };
    let channel = aiur::shard::memseg_channel_value();
    let (system, pk) = System::new(
      GoldilocksBlake3Config::new(cp, fp),
      [CircuitInputs {
        main_width: 3,
        preprocessed: Some(RowMajorMatrix::new_col(vec![Val::ZERO; 2])),
        lookups: vec![
          Lookup::pull(Expr::main(1), vec![Expr::main(0)]),
          Lookup::push(
            Expr::main(1),
            vec![channel.into(), Val::ONE.into(), Val::ZERO.into()],
          ),
          Lookup::pull(
            Expr::main(1),
            vec![channel.into(), Val::ONE.into(), Expr::main(2)],
          ),
        ],
        ..Default::default()
      }],
    );
    let key =
      AiurVerifyingKey::from_bytes(&aiur::vk_codec::to_bytes(&system, cp, fp))?;
    let fixed = FixedRoot::new(1, vec![1], 1)?;
    let config = || {
      GoldilocksBlake3Config::new(
        CommitmentParameters { log_blowup: 2, cap_height: 0 },
        fp,
      )
    };
    // Generated before, and independently of, every certificate and witness.
    let local =
      setup::fri(fixed.circuit(&key, Default::default())?, config(), 1 << 16)?;
    for end in 0..=3 {
      let expected = vec![Val::from_u32(17 + end)];
      let messages = vec![
        BatchMessage::pull(vec![channel, Val::ONE, Val::ZERO]),
        BatchMessage::push(vec![channel, Val::ONE, Val::from_u32(end)]),
      ];
      let proof = system.prove_batch(
        &pk,
        vec![ShardInput {
          claims: vec![expected.clone()],
          witness: SystemWitness::from_stage_1(
            vec![RowMajorMatrix::new(
              vec![
                expected[0],
                Val::ONE,
                Val::from_u32(end),
                Val::ZERO,
                Val::ZERO,
                Val::ZERO,
              ],
              3,
            )],
            &system,
          ),
        }],
        messages,
      );
      key.verify(&expected, &proof).unwrap();
      if end <= 2 {
        let stage =
          fixed.prepare(&key, &proof, &expected, Default::default())?;
        let (verifier, compressed) = stage.prove_fri(config(), 1 << 16)?;
        assert_eq!(verifier.to_bytes()?, local.to_bytes()?);
        local.verify(&compressed, &expected)?;
        assert!(local.verify(&compressed, &[expected[0] + Val::ONE]).is_err());
      } else {
        assert!(
          fixed.prepare(&key, &proof, &expected, Default::default()).is_err()
        );
        // Bypass the host bound check: the circuit must reject the witness too.
        let built = fixed.build(&key, Default::default())?;
        let expanded = expand_batch_witness(
          &system,
          std::slice::from_ref(&built.shape),
          &proof,
        )?;
        let mut witness = built.circuit.witness();
        witness.set(built.public[0], expected[0])?;
        witness.set(built.ends[0], Val::from_u32(end))?;
        expanded[0].assign_proof(&mut witness, &built.inputs)?;
        assert!(witness.generate().is_err());
      }
    }
    Ok(())
  }
}
