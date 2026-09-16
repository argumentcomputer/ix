use super::layout::Layout;
use anyhow::Result;
use flock_prover::{
  circuit::builder::CircuitShape, field::F128, pcs::PcsParams,
};
use ixby_flock::ixby::{
  io::PublicLayout,
  ixbf_decode::paged::{
    code_capture::batch::{CodeCaptureStatement, CompiledCodeCapture},
    commitment_bridge::{
      ArtifactDomain, CommitmentBridgeStatement, CompiledCommitmentBridge,
    },
    constructor_ids::{CompiledConstructorIds, ConstructorIdsStatement},
    endpoints::{
      CompiledEndpoints, Component, EndpointStatement, FunctionalProfile,
    },
    input_capture::batch::{CompiledInputCapture, InputCaptureStatement},
    output_bytes::{CompiledOutputBytes, OutputBytesStatement},
    references::{CompiledReferences, ReferenceStatement},
    source_bytes::{CompiledSourceBytes, SourceBank, SourceBytesStatement},
  },
  paged_exec::{BatchClass, CompiledPagedExecution, ExecutionStatement},
};
use ixby_stage4_exec::{
  CompiledFlockReplay, FlockVerifierSetup, GrammarBatchReplayWitness,
};

const _: fn() = || {
  fn shareable<T: Send + Sync>() {}
  shareable::<CompiledSourceBytes>();
  shareable::<CompiledCodeCapture>();
  shareable::<CompiledReferences>();
  shareable::<CompiledConstructorIds>();
  shareable::<CompiledInputCapture>();
  shareable::<CompiledPagedExecution>();
  shareable::<CompiledOutputBytes>();
  shareable::<CompiledCommitmentBridge>();
  shareable::<CompiledEndpoints>();
};

pub(super) enum Leaf {
  Source(CompiledSourceBytes),
  Code(CompiledCodeCapture),
  References(CompiledReferences),
  ConstructorIds(CompiledConstructorIds),
  Input(CompiledInputCapture),
  Execution(CompiledPagedExecution),
  Output(CompiledOutputBytes),
  Bridge(CompiledCommitmentBridge),
  Endpoints(CompiledEndpoints),
}
macro_rules! call {
  ($leaf:expr, $method:ident) => {
    match $leaf {
      Leaf::Source(s) => s.$method(),
      Leaf::Code(s) => s.$method(),
      Leaf::References(s) => s.$method(),
      Leaf::ConstructorIds(s) => s.$method(),
      Leaf::Input(s) => s.$method(),
      Leaf::Execution(s) => s.$method(),
      Leaf::Output(s) => s.$method(),
      Leaf::Bridge(s) => s.$method(),
      Leaf::Endpoints(s) => s.$method(),
    }
  };
}
impl Leaf {
  pub(super) fn component(kind: Component, class: BatchClass) -> Result<Self> {
    use Component::*;
    Ok(match kind {
      ProgramBytes => {
        Self::Source(CompiledSourceBytes::compile(SourceBank::Program)?)
      },
      CodeCapture => Self::Code(CompiledCodeCapture::compile()?),
      References => Self::References(CompiledReferences::compile()?),
      ConstructorIds => {
        Self::ConstructorIds(CompiledConstructorIds::compile()?)
      },
      InputBytes => {
        Self::Source(CompiledSourceBytes::compile(SourceBank::Input)?)
      },
      InputCapture => Self::Input(CompiledInputCapture::compile()?),
      Execution => Self::Execution(CompiledPagedExecution::compile(class)?),
      OutputBytes => Self::Output(CompiledOutputBytes::compile()?),
      ProgramCommitment => Self::Bridge(CompiledCommitmentBridge::compile(
        ArtifactDomain::Program,
      )?),
      InputCommitment => {
        Self::Bridge(CompiledCommitmentBridge::compile(ArtifactDomain::Input)?)
      },
      OutputCommitment => {
        Self::Bridge(CompiledCommitmentBridge::compile(ArtifactDomain::Output)?)
      },
    })
  }
  pub(super) fn endpoints(profile: FunctionalProfile) -> Result<Self> {
    Ok(Self::Endpoints(CompiledEndpoints::compile(profile)?))
  }
  pub(super) fn layout(&self) -> Layout {
    use Component::*;
    Layout::Component(match self {
      Self::Source(s) => match s.bank() {
        SourceBank::Program => ProgramBytes,
        SourceBank::Input => InputBytes,
      },
      Self::Code(_) => CodeCapture,
      Self::References(_) => References,
      Self::ConstructorIds(_) => ConstructorIds,
      Self::Input(_) => InputCapture,
      Self::Execution(_) => Execution,
      Self::Output(_) => OutputBytes,
      Self::Bridge(s) => match s.bank() {
        ArtifactDomain::Program => ProgramCommitment,
        ArtifactDomain::Input => InputCommitment,
        ArtifactDomain::Output => OutputCommitment,
      },
      Self::Endpoints(_) => return Layout::Endpoints,
    })
  }
  pub(super) fn replay<S: FlockVerifierSetup>(
    &self,
    replay: &CompiledFlockReplay<S>,
    expected: &[F128],
    bytes: &[u8],
  ) -> Result<GrammarBatchReplayWitness> {
    macro_rules! verify {
      ($setup:expr, $statement:ty) => {{
        let expected = <$statement>::from_words(expected)?;
        let v = $setup.verify_for_replay(&expected, bytes)?;
        replay.replay_proof(v.public_values(), v.commitment(), v.proof())
      }};
    }
    match self {
      Self::Source(s) => verify!(s, SourceBytesStatement),
      Self::Code(s) => verify!(s, CodeCaptureStatement),
      Self::References(s) => verify!(s, ReferenceStatement),
      Self::ConstructorIds(s) => verify!(s, ConstructorIdsStatement),
      Self::Input(s) => verify!(s, InputCaptureStatement),
      Self::Execution(s) => verify!(s, ExecutionStatement),
      Self::Output(s) => verify!(s, OutputBytesStatement),
      Self::Bridge(s) => verify!(s, CommitmentBridgeStatement),
      Self::Endpoints(s) => verify!(s, EndpointStatement),
    }
  }
}
impl FlockVerifierSetup for Leaf {
  fn verifier_shape(&self) -> &CircuitShape {
    call!(self, verifier_shape)
  }
  fn public_template(&self) -> &PublicLayout {
    call!(self, public_template)
  }
  fn pcs_params(&self) -> &PcsParams {
    call!(self, pcs_params)
  }
  fn transcript_domain(&self) -> Vec<u8> {
    call!(self, transcript_domain).to_vec()
  }
  fn registry_digest(&self) -> [u8; 32] {
    self.verifier_shape().registry.digest()
  }
  fn circuit_digest(&self) -> [u8; 32] {
    self.verifier_shape().circuit.digest()
  }
}
