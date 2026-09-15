use super::{CompiledExec, ExecStatementDigest, witness};
use anyhow::{Context, Result, ensure};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  field::F128,
  lincheck::LincheckCircuit,
  pcs::Commitment,
  proof::R1csProofCircuitMerged,
  prover::{self, UnionSlotProverInput},
  union::UnionInstance,
  verifier,
};
use serde::{Deserialize, Serialize};
use std::panic::{AssertUnwindSafe, catch_unwind};

const MAGIC: [u8; 8] = *b"IXBYEX00";
pub(super) const MAX_BYTES: u64 = 16 * 1024 * 1024;

/// Observational completion events for the ordinary prover path. These do
/// not establish verification or change the relation, setup or transcript.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecProvingPhaseV0 {
  InputAssignment,
  ExecutionWitness,
  RowDriverPreparation,
  /// Includes the native prover's deferred dense witness construction.
  NativeFlockProving,
  ProofEncoding,
}

#[derive(Serialize, Deserialize)]
struct Bundle {
  magic: [u8; 8],
  setup: [u8; 32],
  commitment: Commitment,
  proof: R1csProofCircuitMerged,
}

/// Read-only complete proof for replay/export, already checked by the native
/// verifier against this exact approved setup and externally expected S.
/// It is not a Stage 4 certificate: a replay circuit must constrain all phases
/// and discharge the terminal roots independently of this host check.
pub struct VerifiedExecProof<'a> {
  setup: &'a CompiledExec,
  expected: ExecStatementDigest,
  public: Vec<F128>,
  bundle: Bundle,
}

impl VerifiedExecProof<'_> {
  pub fn setup(&self) -> &CompiledExec {
    self.setup
  }
  pub fn expected(&self) -> ExecStatementDigest {
    self.expected
  }
  pub fn public_values(&self) -> &[F128] {
    &self.public
  }
  pub fn commitment(&self) -> &Commitment {
    &self.bundle.commitment
  }
  pub fn proof(&self) -> &R1csProofCircuitMerged {
    &self.bundle.proof
  }
}

fn codec() -> impl Options {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .with_little_endian()
    .with_limit(MAX_BYTES)
    .reject_trailing_bytes()
}

impl CompiledExec {
  /// Strict Exec-only entry for the terminal witness generator. This shares
  /// the complete native acceptance check; it cannot admit a deferred-root
  /// or legacy bundle merely because its message fields can be decoded.
  pub fn verify_for_replay(
    &self,
    expected: ExecStatementDigest,
    bytes: &[u8],
  ) -> Result<VerifiedExecProof<'_>> {
    self.verify(expected, bytes)?;
    Ok(VerifiedExecProof {
      setup: self,
      expected,
      public: self.public.instantiate(&expected.limbs())?,
      bundle: codec().deserialize(bytes)?,
    })
  }
  /// Generate a direct Flock execution proof from raw canonical code and input
  /// bytes. No output, trace, or resolved instruction is accepted as advice.
  /// The witness generator is untrusted; only `verify` establishes acceptance.
  pub fn prove(
    &self,
    expected: ExecStatementDigest,
    program: &[u8],
    input: &[u8],
  ) -> Result<Vec<u8>> {
    self.prove_observed(expected, program, input, |_| {})
  }

  /// The same prover as `prove`, with one event after each completed phase.
  /// Callbacks receive no witness data. A failed phase emits no completion
  /// event; only ordinary `verify` establishes acceptance. Native proving
  /// includes dense witness construction by its deferred row drivers.
  pub fn prove_observed(
    &self,
    expected: ExecStatementDigest,
    program: &[u8],
    input: &[u8],
    mut observe: impl FnMut(ExecProvingPhaseV0),
  ) -> Result<Vec<u8>> {
    let private = [
      buffer(self.capacity.program.bytes, program)?,
      buffer(self.capacity.input.bytes, input)?,
    ]
    .concat();
    let assigned = self.input.assign(&private)?;
    observe(ExecProvingPhaseV0::InputAssignment);
    let witness =
      catch_unwind(AssertUnwindSafe(|| self.shape.run(&assigned, &[])))
        .map_err(|_| {
          anyhow::anyhow!("Exec witness generation rejected input")
        })?;
    let public = self.public.instantiate(&expected.limbs())?;
    ensure!(
      witness.public == public,
      "execution output does not match expected statement"
    );
    observe(ExecProvingPhaseV0::ExecutionWitness);
    let drivers = witness::drivers(self, &witness);
    observe(ExecProvingPhaseV0::RowDriverPreparation);
    self.prove_rows_observed(&public, drivers, &mut observe)
  }

  #[cfg(test)]
  pub(super) fn prove_rows(
    &self,
    public: &[F128],
    drivers: Vec<UnionSlotProverInput<'_>>,
  ) -> Result<Vec<u8>> {
    self.prove_rows_observed(public, drivers, &mut |_| {})
  }

  fn prove_rows_observed(
    &self,
    public: &[F128],
    drivers: Vec<UnionSlotProverInput<'_>>,
    observe: &mut impl FnMut(ExecProvingPhaseV0),
  ) -> Result<Vec<u8>> {
    let union =
      UnionInstance::new(&self.shape.registry, self.shape.counts.clone());
    let mut challenger = self.challenger();
    let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
      &union,
      &self.shape.circuit,
      public,
      &self.params,
      drivers,
      Vec::new(),
      &mut challenger,
    );
    observe(ExecProvingPhaseV0::NativeFlockProving);
    let bytes = codec()
      .serialize(&Bundle {
        magic: MAGIC,
        setup: self.identities.digest(),
        commitment,
        proof,
      })
      .context("encode Exec proof")?;
    observe(ExecProvingPhaseV0::ProofEncoding);
    Ok(bytes)
  }

  /// Only approved setup, externally expected S, and strict Exec proof bytes
  /// are consumed. No program/input, host interpreter, or public-vector dump.
  pub fn verify(
    &self,
    expected: ExecStatementDigest,
    bytes: &[u8],
  ) -> Result<()> {
    ensure!(
      (40..=MAX_BYTES as usize).contains(&bytes.len()),
      "Exec proof byte admission"
    );
    // Fail before decoding large proof fields, with no legacy fallback.
    ensure!(bytes[..8] == MAGIC, "Exec proof domain/revision");
    ensure!(
      bytes[8..40] == self.identities.digest(),
      "Exec proof setup identity"
    );
    let bundle: Bundle =
      codec().deserialize(bytes).context("decode Exec proof")?;
    ensure!(
      codec().serialize(&bundle)? == bytes,
      "noncanonical Exec proof encoding"
    );
    let public = self.public.instantiate(&expected.limbs())?;
    let linchecks: Vec<&dyn LincheckCircuit> = self
      .tables
      .iter()
      .map(|table| table.csc_lincheck_circuit() as &dyn LincheckCircuit)
      .collect();
    let union =
      UnionInstance::new(&self.shape.registry, self.shape.counts.clone());
    let mut challenger = self.challenger();
    catch_unwind(AssertUnwindSafe(|| {
      verifier::verify_ligerito_union_circuit(
        &union,
        &self.shape.circuit,
        &public,
        &linchecks,
        &bundle.commitment,
        &bundle.proof,
        &self.params,
        &mut challenger,
      )
    }))
    .map_err(|_| anyhow::anyhow!("malformed Exec proof"))?
    .map_err(|error| anyhow::anyhow!("Exec proof rejected: {error:?}"))?;
    Ok(())
  }

  fn challenger(&self) -> FsChallenger {
    // Setup identity is fixed verifier policy, not a proof-supplied challenge
    // prefix. The native verifier also binds registry/circuit/public words.
    FsChallenger::with_chained_blake3(&self.transcript_domain())
  }
}

pub(super) fn buffer(capacity: usize, data: &[u8]) -> Result<Vec<F128>> {
  ensure!(data.len() <= capacity, "Exec private byte capacity");
  let mut padded = vec![0; capacity.div_ceil(16) * 16];
  padded[..data.len()].copy_from_slice(data);
  let mut words = vec![F128::new(data.len() as u64, 0)];
  words.extend(
    padded.as_chunks::<16>().0.iter().map(|word| crate::hash::pack_bytes(word)),
  );
  Ok(words)
}
