//! Sequential, bounded-memory leaf generation. Native state is advice; every
//! saved statement is checked by its production Flock verifier before reuse.
use super::{Artifacts, Store};
use crate::store::{join, leaf_name};
use anyhow::{Result, ensure};
use flock_prover::field::F128;
use ix_flock_recursion::MAX_PAGED_CHAIN_LEAVES;
use ixby_flock::ixby::{
  auth_memory::{MemoryDepth, SparseMemory},
  ixbf::DecodeLimits,
  ixbf_decode::{
    dispatch::DISPATCH_CONTEXT_INDICES,
    paged::{
      code_capture::batch::{CodeCaptureWitness, CompiledCodeCapture},
      commitment_bridge::{
        ArtifactDomain, CommitmentBridgeWitness, CompiledCommitmentBridge,
      },
      constructor_ids::{CompiledConstructorIds, ConstructorIdsAdvice},
      endpoints::{
        CompiledEndpoints, Component, EndpointAdvice, EndpointFacts,
        FunctionalProfile,
      },
      input_capture::batch::{CompiledInputCapture, InputCaptureWitness},
      output_bytes::{CompiledOutputBytes, OutputBytesWitness},
      references::{CompiledReferences, ReferenceWitness},
      source_bytes::{CompiledSourceBytes, SourceBank, SourceBytesWitness},
    },
  },
  paged_exec::{
    BatchClass, CompiledPagedExecution, ExecutionStatement, NativeImage,
  },
};

struct Summary {
  count: usize,
  statement: Option<Vec<F128>>,
}
impl Summary {
  fn new() -> Self {
    Self { count: 0, statement: None }
  }
  fn record(
    &mut self,
    store: &Store,
    component: Component,
    statement: &[F128],
    prove: impl FnOnce() -> Result<Vec<u8>>,
    verify: impl Fn(&[u8]) -> Result<()>,
  ) -> Result<()> {
    ensure!(
      self.count < MAX_PAGED_CHAIN_LEAVES,
      "component batch count exceeds policy"
    );
    ensure!(
      statement.len() == component.range().len(),
      "component statement width"
    );
    let whole = if let Some(previous) = &self.statement {
      join(component, previous, statement)?
    } else {
      statement.to_vec()
    };
    store.prove(&leaf_name(component, self.count), statement, prove, verify)?;
    self.count += 1;
    self.statement = Some(whole);
    Ok(())
  }
}
pub(super) fn generate(
  artifacts: &Artifacts,
  profile: &FunctionalProfile,
  class: BatchClass,
  store: &Store,
) -> Result<[usize; 11]> {
  let Artifacts { program, input, output } = artifacts;
  let mut memory = SparseMemory::new(MemoryDepth::new(40)?);
  let mut summaries: [Summary; 11] = std::array::from_fn(|_| Summary::new());
  macro_rules! record {
    ($component:ident, $setup:expr, $a:expr) => {{
      let c = Component::$component;
      summaries[c as usize].record(
        store,
        c,
        $a.statement.words(),
        || $setup.prove(&$a),
        |p| $setup.verify(&$a.statement, p),
      )?;
    }};
  }
  let setup = CompiledSourceBytes::compile(SourceBank::Program)?;
  let mut walk = SourceBytesWitness::new(SourceBank::Program, program)?;
  while let Some(a) = walk.next_batch(&mut memory)? {
    record!(ProgramBytes, setup, a);
  }
  drop(setup);
  let setup = CompiledCodeCapture::compile()?;
  let mut walk = CodeCaptureWitness::new(program)?;
  while let Some(a) = walk.next_batch(&mut memory)? {
    record!(CodeCapture, setup, a);
  }
  let context = DISPATCH_CONTEXT_INDICES.map(|i| walk.parser()[i]);
  drop(setup);
  let setup = CompiledReferences::compile()?;
  let mut walk = ReferenceWitness::new([context[1], context[0], context[12]])?;
  while let Some(a) = walk.next_batch(&mut memory)? {
    record!(References, setup, a);
  }
  drop(setup);
  let setup = CompiledConstructorIds::compile()?;
  let a =
    ConstructorIdsAdvice::new(&mut memory, usize::try_from(context[0].lo)?)?;
  record!(ConstructorIds, setup, a);
  drop(setup);
  let setup = CompiledSourceBytes::compile(SourceBank::Input)?;
  let mut walk = SourceBytesWitness::new(SourceBank::Input, input)?;
  while let Some(a) = walk.next_batch(&mut memory)? {
    record!(InputBytes, setup, a);
  }
  drop(setup);
  let setup = CompiledInputCapture::compile()?;
  let mut walk = InputCaptureWitness::new(input, context)?;
  while let Some(a) = walk.next_batch(&mut memory)? {
    record!(InputCapture, setup, a);
  }
  drop(setup);
  let image = NativeImage::load(program, input, DecodeLimits::default())?;
  ensure!(
    image.memory.root() == memory.root(),
    "captured/native initial memory differs"
  );
  let mut machine = image.machine()?;
  drop(image);
  let setup = CompiledPagedExecution::compile(class)?;
  while let Some(a) = machine.batch(class, &mut memory)? {
    let c = Component::Execution;
    let statement = ExecutionStatement::from_words(&a.expected)?;
    summaries[c as usize].record(
      store,
      c,
      statement.words(),
      || setup.prove(&a),
      |p| setup.verify(&statement, p),
    )?;
  }
  drop(setup);
  let setup = CompiledOutputBytes::compile()?;
  let mut walk =
    OutputBytesWitness::new(output, [machine.state[2], machine.state[3]])?;
  while let Some(a) = walk.next_batch(&mut memory)? {
    record!(OutputBytes, setup, a);
  }
  drop(setup);
  let mut parent = profile.digest();
  for (component, domain, raw) in [
    (Component::ProgramCommitment, ArtifactDomain::Program, program),
    (Component::InputCommitment, ArtifactDomain::Input, input),
    (Component::OutputCommitment, ArtifactDomain::Output, output),
  ] {
    let setup = CompiledCommitmentBridge::compile(domain)?;
    let mut walk = CommitmentBridgeWitness::new(domain, raw, parent)?;
    while let Some(a) = walk.next_batch()? {
      summaries[component as usize].record(
        store,
        component,
        a.statement.words(),
        || setup.prove(&a),
        |p| setup.verify(&a.statement, p),
      )?;
    }
    if domain == ArtifactDomain::Program {
      parent = walk.digest();
    }
  }
  ensure!(summaries.iter().all(|s| s.count > 0), "empty execution component");
  let facts = EndpointFacts::assemble(
    summaries.each_ref().map(|s| s.statement.as_ref().unwrap().as_slice()),
  )?;
  let endpoints = EndpointAdvice::new(profile, facts)?;
  ensure!(
    endpoints.statement.digest() == artifacts.statement(profile),
    "independent original-artifact commitment differs"
  );
  let setup = CompiledEndpoints::compile(profile.clone())?;
  store.prove(
    "endpoints",
    endpoints.statement.words(),
    || setup.prove(&endpoints),
    |p| setup.verify(&endpoints.statement, p),
  )?;
  Ok(summaries.map(|s| s.count))
}
