//! A fixed verifier for the normalizer's all-active, one-shard output.
//! Only the claim, proof and memory interval ends vary between invocations.
//!
//! A layout file (`.ixl`) is Ixon, written with the primitives of
//! [`aiur::ixon`] and as canonical as an Aiur artifact: decoding rejects
//! another magic or version, out-of-range values and trailing bytes, so an
//! accepted file re-encodes to its own bytes. Its identity is the BLAKE3
//! digest of those bytes ([`FixedRoot::digest`]).
//!
//! ```text
//! layout = "IXROOTL\0" nat(1) list(nat(log_height))
//!          list(nat(memory_width) nat(circuit)) nat(claim_len)
//! ```
use super::{Prepared, Result};
use crate::fri::*;
use aiur::{
  ixon::{Reader, Writer},
  trace::stark::{
    BatchProof as AiurProof, MEMSEG, VerifyingKey as AiurVerifyingKey,
    batch::memseg_args,
  },
};
use multi_stark::{
  batch::{BatchMessage, BatchPreamble, ShardHeader},
  plonkish::{Circuit, CircuitBuilder, Value},
  types::Val,
};
use p3_field::{PrimeCharacteristicRing, PrimeField64};

/// A fixed root layout file's magic number.
const LAYOUT_MAGIC: &[u8; 8] = b"IXROOTL\0";
/// The layout grammar's version.
const LAYOUT_VERSION: u64 = 1;

#[derive(Clone)]
pub struct FixedRoot {
  log_heights: Vec<u8>,
  // (memory width, circuit index), sorted by width.
  memory_traces: Vec<(usize, usize)>,
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
  /// Heights follow system circuit order, including fixed preprocessed tables.
  /// Memory (width, circuit index) pairs and claim length come from the trusted backend.
  pub fn new(
    log_heights: Vec<u8>,
    memory_traces: Vec<(usize, usize)>,
    claim_len: usize,
  ) -> Result<Self> {
    if log_heights.is_empty()
      || log_heights.iter().any(|log| !(1..=26).contains(log))
      || claim_len == 0
      || claim_len > 1024
      || memory_traces.len() > 4096
      || memory_traces.iter().any(|&(w, i)| {
        w == 0 || w > u32::MAX as usize || i >= log_heights.len()
      })
      || memory_traces.windows(2).any(|w| w[0].0 >= w[1].0)
      || memory_traces
        .iter()
        .map(|&(_, i)| i)
        .collect::<std::collections::BTreeSet<_>>()
        .len()
        != memory_traces.len()
    {
      return Err("invalid fixed root configuration".into());
    }
    Ok(Self { log_heights, memory_traces, claim_len })
  }

  /// Log-heights in system circuit order.
  pub fn log_heights(&self) -> &[u8] {
    &self.log_heights
  }

  /// `(memory width, circuit index)` pairs, ascending by width.
  pub fn memory_traces(&self) -> &[(usize, usize)] {
    &self.memory_traces
  }

  /// The layout file's bytes, readable by [`Self::from_bytes`].
  pub fn to_bytes(&self) -> Vec<u8> {
    let mut w = Writer::new();
    w.raw(LAYOUT_MAGIC);
    w.nat(LAYOUT_VERSION);
    w.list(&self.log_heights, |w, &log| w.nat(u64::from(log)));
    w.list(&self.memory_traces, |w, &(width, circuit)| {
      w.usize(width);
      w.usize(circuit);
    });
    w.usize(self.claim_len);
    w.into_bytes()
  }

  /// Decode a layout file, accepting only its canonical bytes.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    let mut r = Reader::new(bytes);
    if r.raw(LAYOUT_MAGIC.len()).ok() != Some(LAYOUT_MAGIC.as_slice()) {
      return Err("not a fixed root layout (.ixl)".into());
    }
    let version = r.nat()?;
    if version != LAYOUT_VERSION {
      return Err(
        format!("unsupported fixed root layout version {version}").into(),
      );
    }
    let log_heights = r.list(|r| {
      let log = r.nat()?;
      u8::try_from(log).map_err(|_e| r.error(format!("log height {log}")))
    })?;
    let memory_traces = r.list(|r| Ok((r.usize()?, r.usize()?)))?;
    let claim_len = r.usize()?;
    r.finish()?;
    Self::new(log_heights, memory_traces, claim_len)
  }

  /// The layout's content address: the BLAKE3 digest of its bytes.
  pub fn digest(&self) -> [u8; 32] {
    *blake3::hash(&self.to_bytes()).as_bytes()
  }

  /// Identity of the fixed verifier under `key`. It covers the backend and
  /// layout only: no claim, proof or memory end affects it.
  pub fn identity(&self, key: &AiurVerifyingKey) -> [u8; 32] {
    let mut hash = blake3::Hasher::new();
    hash.update(b"ix/fixed-root/v2");
    hash.update(blake3::hash(&key.to_bytes()).as_bytes());
    hash.update(&self.digest());
    *hash.finalize().as_bytes()
  }

  fn preamble(
    &self,
    key: &AiurVerifyingKey,
    expected: &[Val],
    ends: &[Val],
  ) -> Result<BatchPreamble<multi_stark::types::GoldilocksBlake3Config>> {
    if self.log_heights.len() != key.num_circuits()
      || key.system().circuits.iter().zip(&self.log_heights).any(|(c, &log)| {
        c.preprocessed_height != 0 && c.preprocessed_height != 1usize << log
      })
    {
      return Err(
        "fixed root heights do not match the aggregate backend".into(),
      );
    }
    let mut messages = vec![];
    for (&(width, _), &end) in self.memory_traces.iter().zip(ends) {
      messages.push(BatchMessage::pull(memseg_args(width, Val::ZERO).to_vec()));
      messages.push(BatchMessage::push(memseg_args(width, end).to_vec()));
    }
    Ok(BatchPreamble {
      headers: vec![ShardHeader {
        active: vec![true; key.num_circuits()],
        log_degrees: self.log_heights.clone(),
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
      &vec![Val::ZERO; self.memory_traces.len()],
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
    let ends: Vec<_> = (0..self.memory_traces.len())
      .map(|i| b.input(format!("memory_end[{i}]")))
      .collect();
    let mut messages = vec![];
    for (&(width, index), &end) in self.memory_traces.iter().zip(&ends) {
      let log = self.log_heights[index];
      // 0 <= end <= 2^log_height: low bits must vanish if the top bit is 1.
      // This also establishes canonical integer ordering for Aiur's policy.
      let mut low = b.constant(Val::ZERO);
      for bit in 0..log {
        let v = b.hint("memory end bit", &[end], move |v| {
          Ok(Val::from_u64((v[0].as_canonical_u64() >> bit) & 1))
        });
        b.assert_bool(v);
        low =
          b.affine([low, v], [Val::ONE, Val::from_u64(1u64 << bit)], Val::ZERO);
      }
      let top = b.hint("memory end top", &[end], move |v| {
        Ok(Val::from_u64((v[0].as_canonical_u64() >> log) & 1))
      });
      b.assert_bool(top);
      let value =
        b.affine([low, top], [Val::ONE, Val::from_u64(1u64 << log)], Val::ZERO);
      b.assert_equal(value, end);
      let overflow = b.mul(low, top);
      b.assert_zero(overflow);
      let channel = b.constant(Val::from_u64(MEMSEG));
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
      .verify(&[expected.to_vec()], proof)
      .map_err(|e| format!("normalized root: {e:?}"))?;
    if expected.len() != self.claim_len
      || proof.preamble.headers.len() != 1
      || proof.preamble.messages.len() != 2 * self.memory_traces.len()
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
    if ends
      .iter()
      .zip(&self.memory_traces)
      .any(|(e, &(_, i))| e.as_canonical_u64() > 1u64 << self.log_heights[i])
    {
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
  use super::*;
  use crate::pipeline::FriVerifier;
  use multi_stark::{
    batch::ShardInput,
    expr::Expr,
    lookup::Lookup,
    system::{CircuitInputs, System, SystemWitness},
    types::{CommitmentParameters, FriParameters, GoldilocksBlake3Config},
  };
  use p3_matrix::dense::RowMajorMatrix;

  /// A formal Aiur root proved in a fixed one-shard layout verifies, and
  /// compresses through FRI, under the fixed verifier of its artifact.
  #[test]
  fn normalized_formal_root_matches_the_fixed_verifier() -> Result<()> {
    use aiur::{
      Program,
      trace::{
        TraceArtifact, TracePlan,
        stark::{Backend, Parameters, planning},
      },
    };
    #[derive(serde::Deserialize)]
    struct Package {
      program: Program,
      trace: TraceArtifact,
    }
    // Calls, a fixed map table and memory, the shape of `crates/aiur`'s
    // `proves_calls_fixed_maps_and_rom_and_verifies_without_record`.
    let package: Package = serde_json::from_str(include_str!(
      "../../../tests/fixtures/formal-root.json"
    ))?;
    let program = package.program.check()?;
    let plan = TracePlan::new(&program, package.trace)?;
    let backend = Backend::for_batch(
      &plan,
      Parameters {
        log_blowup: 1,
        num_queries: 2,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
      },
    )?;
    let key = AiurVerifyingKey::from_bytes(&backend.verifying_key_bytes()?)?;
    let config = || {
      GoldilocksBlake3Config::new(
        CommitmentParameters { log_blowup: 2, cap_height: 0 },
        FriParameters {
          log_final_poly_len: 0,
          max_log_arity: 1,
          num_queries: 2,
          commit_proof_of_work_bits: 0,
          query_proof_of_work_bits: 0,
        },
      )
    };
    let entry = "root";
    let inputs = [3, 4];
    let records = inputs
      .iter()
      .map(|&input| program.execute(entry, vec![input]))
      .collect::<std::result::Result<Vec<_>, _>>()?;
    // One layout for every record: each circuit one doubling above the
    // largest record, fixed tables at their own heights.
    let mut logs = vec![0u8; key.num_circuits()];
    for record in &records {
      for (ci, &rows) in backend.record_rows(record)?.iter().enumerate() {
        logs[ci] = logs[ci].max(if backend.is_fixed_table(ci) {
          u8::try_from(rows.ilog2())?
        } else {
          u8::try_from(rows.max(1).next_power_of_two().ilog2())? + 1
        });
      }
    }
    let options = planning::Options {
      fixed_log_heights: Some(logs.clone()),
      max_ram_bytes: Some(1 << 30),
      ..Default::default()
    };
    let mut roots = vec![];
    let mut closed = std::collections::BTreeSet::new();
    for (record, input) in records.iter().zip(inputs) {
      let planned = backend.plan_record(record, &options, 0)?;
      let proof = backend.prove_incremental(
        record,
        entry,
        &[input],
        &record.output,
        planned.layout.as_ref().ok_or("no layout")?,
        planned.retention(),
      )?;
      let header = &proof.preamble.headers[0];
      assert!(header.active.iter().all(|&a| a));
      assert_eq!(header.log_degrees, logs);
      closed.extend(
        proof.preamble.messages.iter().map(|m| m.args[1].as_canonical_u64()),
      );
      roots.push((backend.claim(entry, &[input], &record.output)?, proof));
    }
    let memory: Vec<_> = backend
      .memory_circuits()
      .into_iter()
      .filter(|&(width, _)| closed.contains(&(width as u64)))
      .collect();
    let fixed = FixedRoot::new(logs.clone(), memory, roots[0].0.len())?;
    // Derived before, and independently of, every proof.
    let local = FriVerifier::derive(
      fixed.circuit(&key, Default::default())?,
      config(),
      1 << 16,
    )?;
    for (claim, proof) in &roots {
      let prepared = fixed.prepare(&key, proof, claim, Default::default())?;
      let (verifier, compressed) = prepared.prove_fri(config(), 1 << 16)?;
      assert_eq!(verifier.to_bytes()?, local.to_bytes()?);
      local.verify(&compressed, claim)?;
      let mut wrong = claim.clone();
      wrong[2] += Val::ONE;
      assert!(local.verify(&compressed, &wrong).is_err());
      assert!(fixed.prepare(&key, proof, &wrong, Default::default()).is_err());
    }
    Ok(())
  }

  #[test]
  fn normalized_aiur_execution_matches_the_fixed_verifier() -> Result<()> {
    use aiur::{
      artifact::Package,
      trace::{
        TracePlan,
        stark::{Backend, Parameters},
      },
    };
    let (mut program, trace) = Package::decode(include_bytes!(
      "../../../../aiur/tests/fixtures/grouping.ixa"
    ))
    .and_then(Package::traced)?;
    program.maps = serde_json::from_value(serde_json::json!([
      {"name":"id","params":[{"kind":"field"}],"result":{"kind":"tuple","items":[{"kind":"field"}]},"input":0,"output":0}
    ]))?;
    program.tables = serde_json::from_value(serde_json::json!([
      {"name":"xs","type":{"kind":"tuple","items":[{"kind":"field"}]},"rows":[[0],[1],[2],[3]]}
    ]))?;
    let program = program.check_field::<Val>()?;
    let plan = TracePlan::new(&program, trace)?;
    // Toy parameters keep the verifier circuit small; production keys must
    // meet the security floor.
    let params = Parameters {
      log_blowup: 2,
      num_queries: 2,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    };
    let backend = Backend::for_batch_below_floor(&plan, params)?;
    let (cp, fp) = (params.commitment(), params.fri());
    let bytes = backend.verifying_key_bytes()?;
    assert!(AiurVerifyingKey::from_bytes(&bytes).is_err());
    let key = AiurVerifyingKey::from_bytes_below_floor(&bytes)?;
    let fixed = FixedRoot::new(vec![4, 4, 2, 1], vec![(2, 3)], 4)?;
    for logs in [vec![4, 4, 2, 1, 1], vec![4, 4, 3, 1]] {
      let invalid = FixedRoot::new(logs, vec![(2, 3)], 4)?;
      assert!(invalid.circuit(&key, Default::default()).is_err());
    }
    for memories in [vec![(2, 4)], vec![(1, 3), (2, 3)], vec![(2, 3), (1, 0)]] {
      assert!(FixedRoot::new(vec![4, 4, 2, 1], memories, 4).is_err());
    }
    assert_eq!(backend.memory_circuits(), fixed.memory_traces());
    let bytes = fixed.to_bytes();
    assert_eq!(&bytes[..8], LAYOUT_MAGIC);
    assert_eq!(FixedRoot::from_bytes(&bytes)?.to_bytes(), bytes);
    assert_eq!(fixed.digest(), *blake3::hash(&bytes).as_bytes());
    // Another version, a trailing byte, any truncation and a count longer
    // than the input are rejected.
    let mut other_version = bytes.clone();
    other_version[8] = 2;
    assert!(FixedRoot::from_bytes(&other_version).is_err());
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(FixedRoot::from_bytes(&trailing).is_err());
    for len in 0..bytes.len() {
      assert!(FixedRoot::from_bytes(&bytes[..len]).is_err());
    }
    let mut long_count = bytes[..9].to_vec();
    long_count.extend([0x80, 0x00]);
    long_count.extend_from_slice(&bytes[10..]);
    assert!(FixedRoot::from_bytes(&long_count).is_err());
    let other = FixedRoot::new(vec![4, 4, 2, 2], vec![(2, 3)], 4)?;
    assert_ne!(fixed.identity(&key), other.identity(&key));
    let config = || GoldilocksBlake3Config::new(cp, fp);
    let local = FriVerifier::derive(
      fixed.circuit(&key, Default::default())?,
      config(),
      1 << 16,
    )?;
    for value in [3, 7] {
      let input = vec![Val::from_u32(value)];
      let record = program.execute("Grouped::run", input.clone())?;
      let logs =
        backend.normalized_log_heights(&backend.execution_rows(&record), 0)?;
      assert_eq!(logs[2], 2);
      assert!(logs.iter().zip(fixed.log_heights()).all(|(a, b)| a <= b));
      let output = record.output.clone();
      let (claim, proof) = backend.prove_normalized(
        "Grouped::run",
        &input,
        &output,
        record,
        &[4, 4, 2, 1],
      )?;
      assert!(other.prepare(&key, &proof, &claim, Default::default()).is_err());
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
    let channel = Val::from_u64(MEMSEG);
    let (system, pk) = System::new(
      GoldilocksBlake3Config::new(cp, fp),
      [(8, 8), (1, 2)].into_iter().map(|(width, height)| CircuitInputs {
        main_width: 4,
        preprocessed: Some(RowMajorMatrix::new_col(vec![Val::ZERO; height])),
        lookups: vec![
          Lookup::pull(
            if width == 8 { Expr::main(2) } else { Val::ZERO.into() },
            vec![Expr::main(0), Expr::main(1)],
          ),
          Lookup::push(
            Expr::main(2),
            vec![
              channel.into(),
              Val::from_usize(width).into(),
              Val::ZERO.into(),
            ],
          ),
          Lookup::pull(
            Expr::main(2),
            vec![channel.into(), Val::from_usize(width).into(), Expr::main(3)],
          ),
        ],
        ..Default::default()
      }),
    );
    let key = AiurVerifyingKey::from_bytes_below_floor(&stark_key::to_bytes(
      &system, cp, fp,
    ))?;
    let fixed = FixedRoot::new(vec![3, 1], vec![(1, 1), (8, 0)], 2)?;
    let config = || {
      GoldilocksBlake3Config::new(
        CommitmentParameters { log_blowup: 2, cap_height: 0 },
        fp,
      )
    };
    // Generated before, and independently of, every certificate and witness.
    let local = FriVerifier::derive(
      fixed.circuit(&key, Default::default())?,
      config(),
      1 << 16,
    )?;
    for (small_end, large_end) in [(0, 0), (2, 8), (3, 1), (1, 9)] {
      let expected =
        vec![Val::from_u32(17 + small_end), Val::from_u32(31 + large_end)];
      let ends = [small_end, large_end];
      let messages = [1, 8]
        .into_iter()
        .zip(ends)
        .flat_map(|(width, end)| {
          [
            BatchMessage::pull(vec![channel, Val::from_u32(width), Val::ZERO]),
            BatchMessage::push(vec![
              channel,
              Val::from_u32(width),
              Val::from_u32(end),
            ]),
          ]
        })
        .collect();
      let traces = [(large_end, 8), (small_end, 2)]
        .into_iter()
        .map(|(end, height)| {
          let mut values = vec![Val::ZERO; 4 * height];
          values[..4].copy_from_slice(&[
            expected[0],
            expected[1],
            Val::ONE,
            Val::from_u32(end),
          ]);
          RowMajorMatrix::new(values, 4)
        })
        .collect();
      let proof = system.prove_batch(
        &pk,
        vec![ShardInput {
          claims: vec![expected.clone()],
          witness: SystemWitness::from_stage_1(traces, &system),
        }],
        messages,
      );
      key.verify(std::slice::from_ref(&expected), &proof).unwrap();
      if small_end <= 2 && large_end <= 8 {
        let stage =
          fixed.prepare(&key, &proof, &expected, Default::default())?;
        let (verifier, compressed) = stage.prove_fri(config(), 1 << 16)?;
        assert_eq!(verifier.to_bytes()?, local.to_bytes()?);
        local.verify(&compressed, &expected)?;
        assert!(
          local
            .verify(&compressed, &[expected[0] + Val::ONE, expected[1]])
            .is_err()
        );
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
        for (&wire, &value) in built.public.iter().zip(&expected) {
          witness.set(wire, value)?;
        }
        for (&wire, end) in built.ends.iter().zip(ends) {
          witness.set(wire, Val::from_u32(end))?;
        }
        expanded[0].assign_proof(&mut witness, &built.inputs)?;
        assert!(witness.generate().is_err());
      }
    }
    Ok(())
  }
}
