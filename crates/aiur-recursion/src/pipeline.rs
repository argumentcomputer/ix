//! The recursion tail over an Aiur Hypercube proof: `normalize` every shard
//! (see [`crate::normalize`]), fold the results with SP1's compose program,
//! then SP1's shrink and BN254 wrap programs — the last of which is what the
//! gnark PLONK circuit verifies (see [`crate::plonk`]).
//!
//! Everything after the leaf is SP1's own recursion machinery, instantiated
//! from `sp1_prover` with vk verification off (the recursion vk allowlist is
//! SP1's dummy tree, whose root every stage still threads through the public
//! values). The programs are built from the actual inputs rather than SP1's
//! fixed shapes, so the wrap verifying key — and with it the PLONK circuit —
//! is stable only while the shard shapes are; pinning it to SP1's reduce
//! shape is the remaining step towards a fixed on-chain verifier.

use std::sync::Arc;

use anyhow::{Result, anyhow};
use slop_algebra::{AbstractField, PrimeField32};
use sp1_hypercube::{
  HashableKey, InnerSC, MachineVerifier, MachineVerifyingKey, SP1PcsProofInner,
  SP1PcsProofOuter, SP1RecursionProof, SP1WrapProof, ShardProof, ShardVerifier,
  inner_perm, prover::SimpleProver,
};
use sp1_primitives::{
  SP1ExtensionField, SP1Field, SP1GlobalContext, SP1OuterGlobalContext,
};
use sp1_prover::{
  CompressAir, CpuSP1ProverComponents, RecursionSC, SP1ProverComponents,
  ShrinkSC, WrapSC,
  recursion::{
    RecursionVks, compose_program_from_input, recursive_verifier,
    shrink_program_from_input,
  },
};
use sp1_recursion_circuit::{
  WrapConfig,
  machine::{
    PublicValuesOutputDigest, SP1CompressRootVerifierWithVKey,
    SP1CompressWithVKeyWitnessValues, SP1MerkleProofWitnessValues,
    SP1ShapedWitnessValues,
  },
  shard::RecursiveShardVerifier,
  witness::{WitnessBlock, Witnessable},
};
use sp1_recursion_compiler::{
  circuit::AsmCompiler,
  config::InnerConfig,
  ir::{Builder, Config, DslIrProgram},
};
use sp1_recursion_executor::{DIGEST_SIZE, Executor, RecursionProgram};

use aiur_hypercube::{
  AiurAir, AiurMachine, AiurProof, AiurVerifyingKey, ProverParams,
  prover::shard_verifier,
};

use crate::normalize::{AiurNormalizeWitnessValues, AiurRecursiveVerifier};

/// A proof of SP1's recursion machine (normalize, compose or shrink level).
pub type RecursionProof = SP1RecursionProof<SP1GlobalContext, SP1PcsProofInner>;
/// A proof of SP1's BN254 wrap machine: the input of the gnark circuit.
pub type WrapProof = SP1WrapProof<SP1OuterGlobalContext, SP1PcsProofOuter>;

type AiurShardProof = ShardProof<SP1GlobalContext, SP1PcsProofInner>;

/// Prover for the recursion tail over one Aiur machine.
pub struct AiurRecursionProver {
  aiur_verifier: RecursiveShardVerifier<SP1GlobalContext, AiurAir, InnerConfig>,
  compress_verifier: MachineVerifier<SP1GlobalContext, RecursionSC>,
  shrink_verifier: MachineVerifier<SP1GlobalContext, ShrinkSC>,
  wrap_verifier: MachineVerifier<SP1OuterGlobalContext, WrapSC>,
  vks: RecursionVks,
  arity: usize,
  runtime: tokio::runtime::Runtime,
}

impl AiurRecursionProver {
  /// `arity` is the compose fan-in (SP1's default is 2).
  pub fn new(
    machine: &AiurMachine,
    params: ProverParams,
    arity: usize,
  ) -> Result<Self> {
    assert!(arity >= 1, "compose arity must be positive");
    let aiur_verifier = recursive_verifier::<SP1GlobalContext, _, InnerConfig>(
      &shard_verifier(machine, params),
    );
    Ok(Self {
      aiur_verifier,
      compress_verifier: CpuSP1ProverComponents::compress_verifier(),
      shrink_verifier: CpuSP1ProverComponents::shrink_verifier(),
      wrap_verifier: CpuSP1ProverComponents::wrap_verifier(),
      vks: RecursionVks::new(None, arity, false),
      arity,
      runtime: tokio::runtime::Runtime::new()?,
    })
  }

  /// The recursion vk allowlist root every stage commits to.
  pub fn vk_root(&self) -> [SP1Field; DIGEST_SIZE] {
    self.vks.root()
  }

  /// The compress-level verifier (for checking normalize/compose proofs).
  pub fn compress_verifier(
    &self,
  ) -> &MachineVerifier<SP1GlobalContext, RecursionSC> {
    &self.compress_verifier
  }

  /// The BN254 wrap verifier (for checking wrap proofs).
  pub fn wrap_verifier(
    &self,
  ) -> &MachineVerifier<SP1OuterGlobalContext, WrapSC> {
    &self.wrap_verifier
  }

  /// Verify one Aiur shard proof in the recursion circuit. `shard_index` is
  /// the shard's ordinal in compose order; `is_complete` only when the shard
  /// is the whole Aiur proof.
  pub fn normalize(
    &self,
    vk: &AiurVerifyingKey,
    shard: &AiurShardProof,
    shard_index: usize,
    is_complete: bool,
  ) -> Result<RecursionProof> {
    let witness = AiurNormalizeWitnessValues::new(
      vk.clone(),
      shard.clone(),
      shard_index,
      is_complete,
      self.vks.root(),
    );
    let program = {
      let mut builder = Builder::<InnerConfig>::default();
      let input = witness.read(&mut builder);
      AiurRecursiveVerifier::verify(&mut builder, &self.aiur_verifier, input);
      compile(builder)
    };
    let mut blocks: Vec<WitnessBlock> = Vec::new();
    Witnessable::<InnerConfig>::write(&witness, &mut blocks);
    let (vk, proof) = self.prove_inner(
      self.compress_verifier.shard_verifier(),
      Arc::new(program),
      blocks,
    )?;
    self.finish_recursion_proof(vk, proof)
  }

  /// Fold recursion proofs (normalize or compose level) with SP1's compose
  /// program. The children must be in shard order.
  pub fn compose(
    &self,
    children: Vec<RecursionProof>,
    is_complete: bool,
  ) -> Result<RecursionProof> {
    let input = self.compress_input(children, is_complete)?;
    let program = compose_program_from_input(
      &recursive_verifier(self.compress_verifier.shard_verifier()),
      false,
      &input,
    );
    let mut blocks: Vec<WitnessBlock> = Vec::new();
    Witnessable::<InnerConfig>::write(&input, &mut blocks);
    let (vk, proof) = self.prove_inner(
      self.compress_verifier.shard_verifier(),
      Arc::new(program),
      blocks,
    )?;
    self.finish_recursion_proof(vk, proof)
  }

  /// The whole compress stage: normalize every shard of `proof`, then fold
  /// the leaves `arity` at a time into one complete compress-level proof.
  pub fn compress(
    &self,
    vk: &AiurVerifyingKey,
    proof: &AiurProof,
  ) -> Result<RecursionProof> {
    let n = proof.shard_proofs.len();
    if n == 0 {
      return Err(anyhow!("the Aiur proof has no shards"));
    }
    let mut level: Vec<RecursionProof> = Vec::with_capacity(n);
    for (k, shard) in proof.shard_proofs.iter().enumerate() {
      tracing::info!("normalize shard {k}/{n}");
      level.push(self.normalize(vk, shard, k, n == 1)?);
    }
    while level.len() > 1 {
      let last_level = level.len() <= self.arity;
      let mut next = Vec::with_capacity(level.len().div_ceil(self.arity));
      for chunk in level.chunks(self.arity) {
        tracing::info!("compose {} proofs", chunk.len());
        next.push(self.compose(chunk.to_vec(), last_level)?);
      }
      level = next;
    }
    Ok(level.pop().expect("one proof"))
  }

  /// SP1's shrink program over a complete compress-level proof.
  pub fn shrink(&self, proof: RecursionProof) -> Result<RecursionProof> {
    let input = self.compress_input(vec![proof], true)?;
    let program = shrink_program_from_input(
      &recursive_verifier(self.compress_verifier.shard_verifier()),
      false,
      &input,
    );
    let mut blocks: Vec<WitnessBlock> = Vec::new();
    Witnessable::<InnerConfig>::write(&input, &mut blocks);
    let (vk, proof) = self.prove_inner(
      self.shrink_verifier.shard_verifier(),
      Arc::new(program),
      blocks,
    )?;
    self.finish_recursion_proof(vk, proof)
  }

  /// SP1's BN254 wrap program over a shrink proof.
  pub fn wrap(&self, proof: RecursionProof) -> Result<WrapProof> {
    let input = self.compress_input(vec![proof], true)?;
    let program = {
      let verifier = recursive_verifier::<SP1GlobalContext, _, WrapConfig>(
        self.shrink_verifier.shard_verifier(),
      );
      let mut builder = Builder::<WrapConfig>::default();
      let input = input.read(&mut builder);
      SP1CompressRootVerifierWithVKey::<WrapConfig, _>::verify(
        &mut builder,
        &verifier,
        input,
        false,
        PublicValuesOutputDigest::Root,
      );
      compile(builder)
    };
    let mut blocks: Vec<WitnessBlock> = Vec::new();
    Witnessable::<WrapConfig>::write(&input, &mut blocks);
    let shard_verifier = self.wrap_verifier.shard_verifier();
    let program = Arc::new(program);
    let mut runtime = Executor::<SP1Field, SP1ExtensionField, _>::new(
      program.clone(),
      inner_perm(),
    );
    runtime.witness_stream = blocks.into();
    runtime
      .run()
      .map_err(|e| anyhow!("wrap program execution failed: {e:?}"))?;
    let record = runtime.record;
    let prover = SimpleProver::new(
      shard_verifier.clone(),
      <CpuSP1ProverComponents as SP1ProverComponents>::WrapProver::new(
        shard_verifier.clone(),
      ),
    );
    let (vk, proof) = self
      .runtime
      .block_on(prover.setup_and_prove_shard(program, None, record));
    Ok(SP1WrapProof { vk, proof })
  }

  /// Compress, shrink and wrap: the full tail from an Aiur proof to the
  /// gnark circuit's input.
  pub fn prove_wrap(
    &self,
    vk: &AiurVerifyingKey,
    proof: &AiurProof,
  ) -> Result<WrapProof> {
    let compressed = self.compress(vk, proof)?;
    tracing::info!("shrink");
    let shrunk = self.shrink(compressed)?;
    tracing::info!("wrap");
    self.wrap(shrunk)
  }

  /// Execute `program` on the recursion executor with `witness`, then prove
  /// the record on one of the KoalaBear recursion machines.
  fn prove_inner(
    &self,
    shard_verifier: &ShardVerifier<
      SP1GlobalContext,
      InnerSC<CompressAir<SP1Field>>,
    >,
    program: Arc<RecursionProgram<SP1Field>>,
    witness: Vec<WitnessBlock>,
  ) -> Result<(
    MachineVerifyingKey<SP1GlobalContext>,
    ShardProof<SP1GlobalContext, SP1PcsProofInner>,
  )> {
    let mut runtime = Executor::<SP1Field, SP1ExtensionField, _>::new(
      program.clone(),
      inner_perm(),
    );
    runtime.witness_stream = witness.into();
    runtime
      .run()
      .map_err(|e| anyhow!("recursion program execution failed: {e:?}"))?;
    let record = runtime.record;
    let prover = SimpleProver::new(
      shard_verifier.clone(),
      <CpuSP1ProverComponents as SP1ProverComponents>::RecursionProver::new(
        shard_verifier.clone(),
      ),
    );
    Ok(
      self
        .runtime
        .block_on(prover.setup_and_prove_shard(program, None, record)),
    )
  }

  /// Attach the (dummy) allowlist opening of `vk`.
  fn finish_recursion_proof(
    &self,
    vk: MachineVerifyingKey<SP1GlobalContext>,
    proof: ShardProof<SP1GlobalContext, SP1PcsProofInner>,
  ) -> Result<RecursionProof> {
    let (_, vk_merkle_proof) =
      self.vks.open(&vk).map_err(|e| anyhow!("vk allowlist opening: {e:?}"))?;
    Ok(SP1RecursionProof { vk, proof, vk_merkle_proof })
  }

  /// The compose/shrink/wrap witness over `children`, with the allowlist
  /// values SP1 derives when vk verification is off (see
  /// `RecursionProverData::append_merkle_proofs_to_witness`).
  fn compress_input(
    &self,
    children: Vec<RecursionProof>,
    is_complete: bool,
  ) -> Result<SP1CompressWithVKeyWitnessValues<SP1PcsProofInner>> {
    let num_vks = self.vks.num_keys();
    let mut vks_and_proofs = Vec::with_capacity(children.len());
    let mut values = Vec::with_capacity(children.len());
    let mut vk_merkle_proofs = Vec::with_capacity(children.len());
    for SP1RecursionProof { vk, proof, vk_merkle_proof } in children {
      let digest = vk.hash_koalabear();
      let index = (digest[0].as_canonical_u32() as usize) % num_vks;
      values.push([SP1Field::from_canonical_usize(index); DIGEST_SIZE]);
      vk_merkle_proofs.push(vk_merkle_proof);
      vks_and_proofs.push((vk, proof));
    }
    Ok(SP1CompressWithVKeyWitnessValues {
      compress_val: SP1ShapedWitnessValues { vks_and_proofs, is_complete },
      merkle_val: SP1MerkleProofWitnessValues {
        root: self.vks.root(),
        values,
        vk_merkle_proofs,
      },
    })
  }
}

/// Compile a DSL program into a recursion machine program.
fn compile<C: Config<N = SP1Field>>(
  builder: Builder<C>,
) -> RecursionProgram<SP1Field> {
  let block = builder.into_root_block();
  // SAFETY: the circuit is well-formed; it uses no synchronization
  // primitives (the same invariant `sp1_prover` relies on).
  let program = unsafe { DslIrProgram::new_unchecked(block) };
  AsmCompiler::default().compile(program)
}
