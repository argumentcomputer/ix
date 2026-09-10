//! The recursion tail over an Aiur Hypercube proof: `normalize` every shard
//! (see [`crate::normalize`]), fold the results with SP1's compose program,
//! then SP1's shrink and BN254 wrap programs — the last of which is what the
//! gnark PLONK circuit verifies (see [`crate::plonk`]).
//!
//! The pipeline is *fixed* the way SP1's is. Every program is compiled from
//! a dummy input of a known shape, never from the proof at hand, and the
//! set of programs is finite:
//!
//! - one leaf program per shard shape in the machine's catalogue
//!   (`aiur_hypercube::shape`), each pinned to the leaf shape;
//! - one compose program per fan-in `1..=arity` over leaf proofs and one
//!   per fan-in over compress proofs, pinned to the compress shape;
//! - SP1's shrink program over one compress proof, and its wrap program.
//!
//! The verifying keys of all of them form the allowlist ([`crate::vks`]):
//! every compose step checks its children's keys against it, its root
//! rides in the public values to the PLONK proof, and a prover cannot
//! substitute a program of its own. The leaf programs and their keys depend
//! on the Aiur machine (the toplevel), so their setup is per machine and
//! cached on disk (see [`cache_dir`]); everything above is common to every
//! machine that fits the pinned shapes, so the wrap verifying key — and the
//! PLONK circuit — are the same for every Aiur toplevel.
//!
//! A machine's leaf programs fit the built-in shapes or the machine is
//! rejected at setup; see [`crate::shapes`] for recomputing them.

use std::{
  collections::{BTreeMap, BTreeSet},
  path::PathBuf,
  sync::{Arc, Mutex},
};

use anyhow::{Context as _, Result, anyhow};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
use sp1_hypercube::{
  HashableKey, InnerSC, MachineVerifier, MachineVerifyingKey, SP1PcsProofInner,
  SP1PcsProofOuter, SP1RecursionProof, SP1WrapProof, ShardProof, ShardVerifier,
  inner_perm, prover::SimpleProver,
};
use sp1_primitives::{
  SP1ExtensionField, SP1Field, SP1GlobalContext, SP1OuterGlobalContext,
  fri_params::recursion_fri_config,
};
use sp1_prover::{
  CompressAir, CpuSP1ProverComponents, RecursionSC, SP1ProverComponents,
  ShrinkSC, WrapSC,
  recursion::{
    compose_program_from_input, recursive_verifier, shrink_program_from_input,
  },
  shapes::SP1RecursionProofShape,
};
use sp1_recursion_circuit::{
  WrapConfig,
  dummy::{dummy_shard_proof, dummy_vk},
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
use sp1_recursion_executor::{
  Executor, RecursionProgram, shape::RecursionShape,
};

use aiur_hypercube::{
  AiurAir, AiurMachine, AiurProof, AiurVerifyingKey, F, ProverParams,
  ShardShape,
  prover::{fri_config, shard_verifier},
  shape::{catalogue, core_shape, shape_of_proof},
};

use crate::{
  normalize::{AiurNormalizeWitnessValues, AiurRecursiveVerifier},
  shapes::{
    PinnedShapes, fits, max_shape, program_heights, shape_from_heights,
    under_cap,
  },
  vks::{AiurVks, Digest, VK_TREE_HEIGHT},
};

/// A proof of SP1's recursion machine (normalize, compose or shrink level).
pub type RecursionProof = SP1RecursionProof<SP1GlobalContext, SP1PcsProofInner>;
/// A proof of SP1's BN254 wrap machine: the input of the gnark circuit.
pub type WrapProof = SP1WrapProof<SP1OuterGlobalContext, SP1PcsProofOuter>;

type AiurShardProof = ShardProof<SP1GlobalContext, SP1PcsProofInner>;
type InnerShardVerifier =
  ShardVerifier<SP1GlobalContext, InnerSC<CompressAir<SP1Field>>>;

/// The programs of the pipeline.
#[derive(
  Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub enum ProgramKind {
  /// The leaf over a shard of this shape.
  Leaf(ShardShape),
  /// Compose over `n` leaf proofs.
  ComposeLeaf(usize),
  /// Compose over `n` compress proofs.
  Compose(usize),
  /// Shrink over one compress proof.
  Shrink,
}

impl ProgramKind {
  fn is_leaf(self) -> bool {
    matches!(self, Self::Leaf(_))
  }
}

/// The verifiers and parameters the programs are built from: everything
/// about the pipeline that is not a shape or a key.
struct Context {
  machine: sp1_hypercube::Machine<F, AiurAir>,
  fingerprint: [u8; 32],
  aiur_params: ProverParams,
  aiur_verifier: RecursiveShardVerifier<SP1GlobalContext, AiurAir, InnerConfig>,
  /// The recursion machine the leaf proofs are proven on. An Aiur machine
  /// has far more chips and columns than SP1's RISC-V core, so its leaf
  /// program does not fit SP1's compress limits (2^21 rows per chip); the
  /// leaf level gets its own, larger caps (see [`leaf_params`]).
  leaf_verifier: MachineVerifier<SP1GlobalContext, RecursionSC>,
  compress_verifier: MachineVerifier<SP1GlobalContext, RecursionSC>,
  shrink_verifier: MachineVerifier<SP1GlobalContext, ShrinkSC>,
  wrap_verifier: MachineVerifier<SP1OuterGlobalContext, WrapSC>,
  catalogue: Vec<ShardShape>,
  arity: usize,
  runtime: tokio::runtime::Runtime,
}

impl Context {
  fn new(
    machine: &AiurMachine,
    aiur_params: ProverParams,
    arity: usize,
  ) -> Result<Self> {
    if arity == 0 {
      return Err(anyhow!("compose arity must be positive"));
    }
    let aiur_verifier = recursive_verifier::<SP1GlobalContext, _, InnerConfig>(
      &shard_verifier(machine, aiur_params),
    );
    let (leaf_log_stacking_height, leaf_max_log_row_count) = leaf_params();
    let leaf_verifier =
      MachineVerifier::new(ShardVerifier::from_basefold_parameters(
        recursion_fri_config(),
        leaf_log_stacking_height,
        leaf_max_log_row_count,
        CompressAir::<SP1Field>::compress_machine(),
      ));
    Ok(Self {
      machine: machine.machine().clone(),
      fingerprint: machine.fingerprint(),
      aiur_params,
      aiur_verifier,
      leaf_verifier,
      compress_verifier: CpuSP1ProverComponents::compress_verifier(),
      shrink_verifier: CpuSP1ProverComponents::shrink_verifier(),
      wrap_verifier: CpuSP1ProverComponents::wrap_verifier(),
      catalogue: catalogue(machine.machine(), aiur_params),
      arity,
      runtime: tokio::runtime::Runtime::new()?,
    })
  }

  /// Every program of the pipeline, leaves first.
  fn kinds(&self) -> Vec<ProgramKind> {
    let mut kinds: Vec<ProgramKind> =
      self.catalogue.iter().map(|s| ProgramKind::Leaf(*s)).collect();
    kinds.extend((1..=self.arity).map(ProgramKind::ComposeLeaf));
    kinds.extend((1..=self.arity).map(ProgramKind::Compose));
    kinds.push(ProgramKind::Shrink);
    kinds
  }

  /// The machine configuration a program of this kind is proven on.
  fn verifier_of(&self, kind: ProgramKind) -> &InnerShardVerifier {
    match kind {
      ProgramKind::Leaf(_) => self.leaf_verifier.shard_verifier(),
      ProgramKind::ComposeLeaf(_) | ProgramKind::Compose(_) => {
        self.compress_verifier.shard_verifier()
      },
      ProgramKind::Shrink => self.shrink_verifier.shard_verifier(),
    }
  }

  /// The leaf program over a shard of shape `shape`, from a dummy proof of
  /// that shape.
  fn leaf_program(&self, shape: ShardShape) -> RecursionProgram<SP1Field> {
    let core = core_shape(&self.machine, self.aiur_params, shape);
    let s = self.aiur_params.log_stacking_height as usize;
    let proof = dummy_shard_proof(
      core.shard_chips,
      self.aiur_params.max_log_row_count,
      fri_config(self.aiur_params),
      s,
      &[core.preprocessed_area >> s, core.main_area >> s],
      &[core.preprocessed_padding_cols, core.main_padding_cols],
    );
    let witness = AiurNormalizeWitnessValues::new(
      dummy_vk(),
      proof,
      1,
      false,
      Default::default(),
    );
    let mut builder = Builder::<InnerConfig>::default();
    let input = witness.read(&mut builder);
    AiurRecursiveVerifier::verify(&mut builder, &self.aiur_verifier, input);
    compile(builder)
  }

  /// A dummy compose/shrink input: `arity` proofs of `child_shape` on the
  /// child level's machine configuration.
  fn dummy_compress_input(
    &self,
    child: &MachineVerifier<SP1GlobalContext, RecursionSC>,
    child_shape: &SP1RecursionProofShape,
    arity: usize,
  ) -> SP1CompressWithVKeyWitnessValues<SP1PcsProofInner> {
    let chips: BTreeSet<_> =
      child.shard_verifier().machine().chips().iter().cloned().collect();
    child_shape.dummy_input(
      arity,
      VK_TREE_HEIGHT,
      chips,
      child.max_log_row_count(),
      *child.fri_config(),
      child.log_stacking_height() as usize,
    )
  }

  /// The program of `kind`, its dummy input shaped by `shapes` (leaf
  /// proofs have the leaf shape, compress proofs the compress shape). With
  /// `pin`, the program's traces are padded to the shape of its level —
  /// the leaf shape for leaves, the compress shape for compose programs;
  /// shrink is never pinned — as every program of the pipeline is; without,
  /// they have their natural heights, which is how the shapes are measured.
  fn program(
    &self,
    kind: ProgramKind,
    shapes: &PinnedShapes,
    pin: bool,
  ) -> RecursionProgram<SP1Field> {
    let mut program = match kind {
      ProgramKind::Leaf(shape) => self.leaf_program(shape),
      ProgramKind::ComposeLeaf(n) => {
        let input =
          self.dummy_compress_input(&self.leaf_verifier, &shapes.leaf, n);
        compose_program_from_input(
          &recursive_verifier(self.leaf_verifier.shard_verifier()),
          true,
          &input,
        )
      },
      ProgramKind::Compose(n) => {
        let input = self.dummy_compress_input(
          &self.compress_verifier,
          &shapes.compress,
          n,
        );
        compose_program_from_input(
          &recursive_verifier(self.compress_verifier.shard_verifier()),
          true,
          &input,
        )
      },
      ProgramKind::Shrink => {
        let input = self.dummy_compress_input(
          &self.compress_verifier,
          &shapes.compress,
          1,
        );
        shrink_program_from_input(
          &recursive_verifier(self.compress_verifier.shard_verifier()),
          true,
          &input,
        )
      },
    };
    if pin {
      program.shape = match kind {
        ProgramKind::Leaf(_) => Some(shapes.leaf.shape.clone()),
        ProgramKind::ComposeLeaf(_) | ProgramKind::Compose(_) => {
          Some(shapes.compress.shape.clone())
        },
        ProgramKind::Shrink => None,
      };
    }
    program
  }

  /// The proving-key setup of `program` on its machine: its verifying key.
  fn setup(
    &self,
    kind: ProgramKind,
    program: Arc<RecursionProgram<SP1Field>>,
  ) -> MachineVerifyingKey<SP1GlobalContext> {
    let sv = self.verifier_of(kind);
    let prover = SimpleProver::new(
      sv.clone(),
      <CpuSP1ProverComponents as SP1ProverComponents>::RecursionProver::new(
        sv.clone(),
      ),
    );
    self.runtime.block_on(async { prover.setup(program).await.1 })
  }

  /// The per-chip heights of `program` on the machine of `kind`.
  fn heights(
    &self,
    kind: ProgramKind,
    program: Arc<RecursionProgram<SP1Field>>,
  ) -> BTreeMap<String, usize> {
    let sv = self.verifier_of(kind);
    program_heights(
      &self.runtime,
      sv.machine(),
      sv.max_log_row_count(),
      program,
    )
  }

  /// Compute the pinned shapes for this machine: the leaf shape as the
  /// per-chip maximum over the catalogue's leaf programs, the compress
  /// shape as the fixed point over the compose programs (SP1's
  /// `compute_compress_shape`).
  fn compute_shapes(&self) -> Result<PinnedShapes> {
    let leaf_cap = self.leaf_verifier.max_log_row_count();
    let (leaf_log_stacking_height, leaf_max_log_row_count) = leaf_params();
    let mut shapes = PinnedShapes {
      leaf: SP1RecursionProofShape { shape: RecursionShape::empty() },
      compress: SP1RecursionProofShape { shape: RecursionShape::empty() },
      leaf_params: (leaf_log_stacking_height, leaf_max_log_row_count),
      arity: self.arity,
      vk_tree_height: VK_TREE_HEIGHT,
    };
    for shape in &self.catalogue {
      let kind = ProgramKind::Leaf(*shape);
      let program = Arc::new(self.program(kind, &shapes, false));
      report_program(&format!("{kind:?}"), &program);
      let heights = self.heights(kind, program);
      under_cap(&heights, leaf_cap).map_err(|e| {
        anyhow!("leaf program for {shape:?} exceeds the leaf row cap: {e}")
      })?;
      shapes.leaf = max_shape(&shapes.leaf, &shape_from_heights(&heights));
    }
    tracing::info!("leaf shape: {:?}", shapes.leaf.shape);

    let compress_cap = self.compress_verifier.max_log_row_count();
    // Seed: the compose programs over leaf proofs (independent of the
    // compress shape).
    for n in 1..=self.arity {
      let kind = ProgramKind::ComposeLeaf(n);
      let program = Arc::new(self.program(kind, &shapes, false));
      report_program(&format!("{kind:?}"), &program);
      let heights = self.heights(kind, program);
      under_cap(&heights, compress_cap).map_err(|e| {
        anyhow!(
          "compose program over {n} leaf proofs exceeds the compress row \
           cap ({e}); lower the arity"
        )
      })?;
      shapes.compress =
        max_shape(&shapes.compress, &shape_from_heights(&heights));
    }
    // Close under the compose programs over compress proofs.
    for round in 0..8 {
      let mut grown = false;
      for n in 1..=self.arity {
        let kind = ProgramKind::Compose(n);
        let program = Arc::new(self.program(kind, &shapes, false));
        report_program(&format!("{kind:?} (round {round})"), &program);
        let heights = self.heights(kind, program);
        under_cap(&heights, compress_cap).map_err(|e| {
          anyhow!(
            "compose program over {n} compress proofs exceeds the compress \
             row cap ({e}); lower the arity"
          )
        })?;
        if fits(&shapes.compress, &heights).is_err() {
          grown = true;
          shapes.compress =
            max_shape(&shapes.compress, &shape_from_heights(&heights));
        }
      }
      if !grown {
        tracing::info!("compress shape: {:?}", shapes.compress.shape);
        return Ok(shapes);
      }
    }
    Err(anyhow!("the compress shape did not converge"))
  }

  /// A digest of the parameters the universal programs depend on.
  fn universal_key(&self, shapes: &PinnedShapes) -> String {
    let mut h = Sha256::new();
    h.update(b"aiur-recursion universal v1\n");
    h.update(shapes.to_json().as_bytes());
    h.update(self.arity.to_le_bytes());
    hex::encode(h.finalize())
  }

  /// A digest of the parameters the leaf programs depend on.
  fn machine_key(&self, shapes: &PinnedShapes) -> String {
    let mut h = Sha256::new();
    h.update(b"aiur-recursion machine v1\n");
    h.update(self.fingerprint);
    h.update(self.aiur_params.log_blowup.to_le_bytes());
    h.update(self.aiur_params.log_stacking_height.to_le_bytes());
    h.update(self.aiur_params.max_log_row_count.to_le_bytes());
    h.update(shapes.to_json().as_bytes());
    hex::encode(h.finalize())
  }
}

/// Where the verifying-key maps are cached: `~/.ix/cache/recursion/`.
pub fn cache_dir() -> Result<PathBuf> {
  let home = std::env::var_os("HOME")
    .map(PathBuf::from)
    .ok_or_else(|| anyhow!("HOME is not set"))?;
  Ok(home.join(".ix").join("cache").join("recursion"))
}

type VkMap = BTreeMap<ProgramKind, Digest>;

fn read_vk_map(path: &PathBuf) -> Option<VkMap> {
  let bytes = std::fs::read(path).ok()?;
  bincode::deserialize(&bytes).ok()
}

fn write_vk_map(path: &PathBuf, map: &VkMap) -> Result<()> {
  if let Some(dir) = path.parent() {
    std::fs::create_dir_all(dir)?;
  }
  let bytes = bincode::serialize(map)?;
  std::fs::write(path, bytes)
    .with_context(|| format!("writing {}", path.display()))
}

/// Prover for the recursion tail over one Aiur machine.
pub struct AiurRecursionProver {
  ctx: Context,
  shapes: PinnedShapes,
  vks: AiurVks,
  /// The verifying key each program of the pipeline must have.
  expected: VkMap,
  programs: Mutex<BTreeMap<ProgramKind, Arc<RecursionProgram<SP1Field>>>>,
}

impl AiurRecursionProver {
  /// The pipeline over `machine` with the built-in shapes (or the ones
  /// `IX_REC_SHAPES` selects; see [`crate::shapes`]). `arity` is the
  /// compose fan-in (SP1's default is 4). The first construction for a
  /// machine sets up its leaf programs and caches their keys.
  pub fn new(
    machine: &AiurMachine,
    params: ProverParams,
    arity: usize,
  ) -> Result<Self> {
    let ctx = Context::new(machine, params, arity)?;
    let shapes = match std::env::var("IX_REC_SHAPES").ok().as_deref() {
      None | Some("") => PinnedShapes::builtin()?,
      Some("compute") => {
        let shapes = ctx.compute_shapes()?;
        if let Some(out) = std::env::var_os("IX_REC_SHAPES_OUT") {
          std::fs::write(&out, shapes.to_json())
            .with_context(|| format!("writing {}", out.to_string_lossy()))?;
          tracing::info!(
            "recursion shapes written to {}",
            out.to_string_lossy()
          );
        }
        shapes
      },
      Some(path) => PinnedShapes::from_file(std::path::Path::new(path))?,
    };
    Self::with_shapes_ctx(ctx, shapes)
  }

  /// The pipeline pinned to `shapes` (see [`Self::compute_shapes`]).
  pub fn with_shapes(
    machine: &AiurMachine,
    params: ProverParams,
    arity: usize,
    shapes: PinnedShapes,
  ) -> Result<Self> {
    Self::with_shapes_ctx(Context::new(machine, params, arity)?, shapes)
  }

  /// The shapes this machine's pipeline needs (see [`crate::shapes`]).
  pub fn compute_shapes(
    machine: &AiurMachine,
    params: ProverParams,
    arity: usize,
  ) -> Result<PinnedShapes> {
    Context::new(machine, params, arity)?.compute_shapes()
  }

  fn with_shapes_ctx(ctx: Context, shapes: PinnedShapes) -> Result<Self> {
    if shapes.leaf_params != leaf_params() {
      return Err(anyhow!(
        "the pinned shapes were computed for leaf parameters {:?}, the \
         pipeline runs with {:?}",
        shapes.leaf_params,
        leaf_params()
      ));
    }
    if shapes.vk_tree_height != VK_TREE_HEIGHT {
      return Err(anyhow!(
        "the pinned shapes were computed for another allowlist height"
      ));
    }
    if ctx.arity > shapes.arity {
      return Err(anyhow!(
        "arity {} exceeds the {} the pinned shapes were closed under",
        ctx.arity,
        shapes.arity
      ));
    }

    // The verifying keys: from the caches, or set up now.
    let dir = cache_dir()?;
    let machine_path = dir.join(format!("{}.vks", ctx.machine_key(&shapes)));
    let universal_path =
      dir.join(format!("{}.vks", ctx.universal_key(&shapes)));
    let mut machine_map = read_vk_map(&machine_path).unwrap_or_default();
    let mut universal_map = read_vk_map(&universal_path).unwrap_or_default();
    let mut programs = BTreeMap::new();
    let mut machine_dirty = false;
    let mut universal_dirty = false;
    for kind in ctx.kinds() {
      let map =
        if kind.is_leaf() { &mut machine_map } else { &mut universal_map };
      if map.contains_key(&kind) {
        continue;
      }
      tracing::info!("recursion setup: {kind:?}");
      let program = Arc::new(ctx.program(kind, &shapes, true));
      report_program(&format!("{kind:?}"), &program);
      Self::check_fits(&ctx, &shapes, kind, &program)?;
      let vk = ctx.setup(kind, program.clone());
      map.insert(kind, vk.hash_koalabear());
      if kind.is_leaf() {
        machine_dirty = true;
      } else {
        universal_dirty = true;
        // The universal programs are small; keep them.
        programs.insert(kind, program);
      }
    }
    if machine_dirty {
      write_vk_map(&machine_path, &machine_map)?;
    }
    if universal_dirty {
      write_vk_map(&universal_path, &universal_map)?;
    }
    let mut expected = machine_map;
    expected.extend(universal_map);
    let vks = AiurVks::new(expected.values().copied())?;
    Ok(Self { ctx, shapes, vks, expected, programs: Mutex::new(programs) })
  }

  /// Reject a program that does not fit the shape it is pinned to, before
  /// the prover panics on it. The event counts give a cheap upper bound on
  /// the heights; only when that fails are the real heights generated.
  fn check_fits(
    ctx: &Context,
    shapes: &PinnedShapes,
    kind: ProgramKind,
    program: &Arc<RecursionProgram<SP1Field>>,
  ) -> Result<()> {
    let shape = match kind {
      ProgramKind::Leaf(_) => &shapes.leaf,
      ProgramKind::ComposeLeaf(_) | ProgramKind::Compose(_) => &shapes.compress,
      ProgramKind::Shrink => return Ok(()),
    };
    let bound = sp1_prover::shapes::build_shape_from_recursion_air_event_count(
      &program.event_counts,
    );
    let bound: BTreeMap<String, usize> = bound.shape.into_iter().collect();
    if fits(shape, &bound).is_ok() {
      return Ok(());
    }
    let heights = ctx.heights(kind, program.clone());
    fits(shape, &heights).map_err(|e| {
      anyhow!(
        "the {kind:?} program does not fit the pinned shape ({e}); this \
         machine is larger than the shapes were computed for — recompute \
         them (IX_REC_SHAPES=compute)"
      )
    })
  }

  /// The pinned shapes in use.
  pub fn shapes(&self) -> &PinnedShapes {
    &self.shapes
  }

  /// The recursion vk allowlist root every stage commits to.
  pub fn vk_root(&self) -> Digest {
    self.vks.root()
  }

  /// The allowlist.
  pub fn vks(&self) -> &AiurVks {
    &self.vks
  }

  /// The leaf-level verifier (for checking normalize proofs).
  pub fn leaf_verifier(
    &self,
  ) -> &MachineVerifier<SP1GlobalContext, RecursionSC> {
    &self.ctx.leaf_verifier
  }

  /// The compress-level verifier (for checking compose proofs).
  pub fn compress_verifier(
    &self,
  ) -> &MachineVerifier<SP1GlobalContext, RecursionSC> {
    &self.ctx.compress_verifier
  }

  /// The BN254 wrap verifier (for checking wrap proofs).
  pub fn wrap_verifier(
    &self,
  ) -> &MachineVerifier<SP1OuterGlobalContext, WrapSC> {
    &self.ctx.wrap_verifier
  }

  /// The program of `kind`, compiled on first use.
  fn program(&self, kind: ProgramKind) -> Arc<RecursionProgram<SP1Field>> {
    if let Some(p) = self.programs.lock().unwrap().get(&kind) {
      return p.clone();
    }
    tracing::info!("compiling the {kind:?} program");
    let program = Arc::new(self.ctx.program(kind, &self.shapes, true));
    report_program(&format!("{kind:?}"), &program);
    self.programs.lock().unwrap().insert(kind, program.clone());
    program
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
    let shape = shape_of_proof(&self.ctx.machine, self.ctx.aiur_params, shard)
      .map_err(|e| anyhow!("shard {shard_index}: {e}"))?;
    let kind = ProgramKind::Leaf(shape);
    let witness = AiurNormalizeWitnessValues::new(
      vk.clone(),
      shard.clone(),
      shard_index,
      is_complete,
      self.vks.root(),
    );
    let mut blocks: Vec<WitnessBlock> = Vec::new();
    Witnessable::<InnerConfig>::write(&witness, &mut blocks);
    let (vk, proof) = self.prove(kind, blocks)?;
    self.finish_recursion_proof(vk, proof)
  }

  /// Fold recursion proofs with SP1's compose program. The children must be
  /// in shard order and all from the same level: `leaves` says whether they
  /// are normalize proofs (proven on the leaf machine configuration) or
  /// compose proofs.
  pub fn compose(
    &self,
    children: Vec<RecursionProof>,
    leaves: bool,
    is_complete: bool,
  ) -> Result<RecursionProof> {
    let n = children.len();
    if n == 0 || n > self.ctx.arity {
      return Err(anyhow!(
        "compose over {n} proofs (arity {})",
        self.ctx.arity
      ));
    }
    let kind = if leaves {
      ProgramKind::ComposeLeaf(n)
    } else {
      ProgramKind::Compose(n)
    };
    let input = self.compress_input(children, is_complete);
    let mut blocks: Vec<WitnessBlock> = Vec::new();
    Witnessable::<InnerConfig>::write(&input, &mut blocks);
    let (vk, proof) = self.prove(kind, blocks)?;
    self.finish_recursion_proof(vk, proof)
  }

  /// The whole compress stage: normalize every shard of `proof`, then fold
  /// the leaves `arity` at a time into one complete compress-level proof
  /// (a single shard is folded by the arity-1 compose program).
  pub fn compress(
    &self,
    vk: &AiurVerifyingKey,
    proof: &AiurProof,
  ) -> Result<RecursionProof> {
    let n = proof.shard_proofs.len();
    if n == 0 {
      return Err(anyhow!("the Aiur proof has no shards"));
    }
    let arity = self.ctx.arity;
    let mut level: Vec<RecursionProof> = Vec::with_capacity(n);
    for (k, shard) in proof.shard_proofs.iter().enumerate() {
      tracing::info!("normalize shard {k}/{n}");
      level.push(self.normalize(vk, shard, k, n == 1)?);
    }
    let mut leaves = true;
    loop {
      let last_level = level.len() <= arity;
      let mut next = Vec::with_capacity(level.len().div_ceil(arity));
      for chunk in level.chunks(arity) {
        tracing::info!("compose {} proofs", chunk.len());
        next.push(self.compose(chunk.to_vec(), leaves, last_level)?);
      }
      level = next;
      leaves = false;
      if level.len() == 1 {
        return Ok(level.pop().expect("one proof"));
      }
    }
  }

  /// SP1's shrink program over a complete compress-level proof.
  pub fn shrink(&self, proof: RecursionProof) -> Result<RecursionProof> {
    let input = self.compress_input(vec![proof], true);
    let mut blocks: Vec<WitnessBlock> = Vec::new();
    Witnessable::<InnerConfig>::write(&input, &mut blocks);
    let (vk, proof) = self.prove(ProgramKind::Shrink, blocks)?;
    self.finish_recursion_proof(vk, proof)
  }

  /// SP1's BN254 wrap program over a shrink proof. The shrink program is
  /// fixed, so its proofs have one shape and the wrap program built from
  /// them is one program.
  pub fn wrap(&self, proof: RecursionProof) -> Result<WrapProof> {
    let input = self.compress_input(vec![proof], true);
    let program = {
      let verifier = recursive_verifier::<SP1GlobalContext, _, WrapConfig>(
        self.ctx.shrink_verifier.shard_verifier(),
      );
      let mut builder = Builder::<WrapConfig>::default();
      let input = input.read(&mut builder);
      SP1CompressRootVerifierWithVKey::<WrapConfig, _>::verify(
        &mut builder,
        &verifier,
        input,
        true,
        PublicValuesOutputDigest::Root,
      );
      compile(builder)
    };
    let mut blocks: Vec<WitnessBlock> = Vec::new();
    Witnessable::<WrapConfig>::write(&input, &mut blocks);
    let shard_verifier = self.ctx.wrap_verifier.shard_verifier();
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
      .ctx
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

  /// Execute the program of `kind` with `witness`, prove the record on the
  /// kind's machine, and check the key is the one the allowlist expects.
  fn prove(
    &self,
    kind: ProgramKind,
    witness: Vec<WitnessBlock>,
  ) -> Result<(
    MachineVerifyingKey<SP1GlobalContext>,
    ShardProof<SP1GlobalContext, SP1PcsProofInner>,
  )> {
    let program = self.program(kind);
    let mut runtime = Executor::<SP1Field, SP1ExtensionField, _>::new(
      program.clone(),
      inner_perm(),
    );
    runtime.witness_stream = witness.into();
    runtime
      .run()
      .map_err(|e| anyhow!("{kind:?} program execution failed: {e:?}"))?;
    let record = runtime.record;
    let sv = self.ctx.verifier_of(kind);
    let prover = SimpleProver::new(
      sv.clone(),
      <CpuSP1ProverComponents as SP1ProverComponents>::RecursionProver::new(
        sv.clone(),
      ),
    );
    let (vk, proof) = self
      .ctx
      .runtime
      .block_on(prover.setup_and_prove_shard(program, None, record));
    let expected = self.expected.get(&kind).expect("every kind has a key");
    if vk.hash_koalabear() != *expected {
      return Err(anyhow!(
        "the {kind:?} program's verifying key is not the allowlisted one: \
         the program compiled from the dummy input differs from this one"
      ));
    }
    Ok((vk, proof))
  }

  /// Attach the allowlist opening of `vk`.
  fn finish_recursion_proof(
    &self,
    vk: MachineVerifyingKey<SP1GlobalContext>,
    proof: ShardProof<SP1GlobalContext, SP1PcsProofInner>,
  ) -> Result<RecursionProof> {
    let (_, vk_merkle_proof) = self.vks.open(&vk)?;
    Ok(SP1RecursionProof { vk, proof, vk_merkle_proof })
  }

  /// The compose/shrink/wrap witness over `children`, with each child's
  /// allowlist opening.
  fn compress_input(
    &self,
    children: Vec<RecursionProof>,
    is_complete: bool,
  ) -> SP1CompressWithVKeyWitnessValues<SP1PcsProofInner> {
    let mut vks_and_proofs = Vec::with_capacity(children.len());
    let mut values = Vec::with_capacity(children.len());
    let mut vk_merkle_proofs = Vec::with_capacity(children.len());
    for SP1RecursionProof { vk, proof, vk_merkle_proof } in children {
      values.push(vk.hash_koalabear());
      vk_merkle_proofs.push(vk_merkle_proof);
      vks_and_proofs.push((vk, proof));
    }
    SP1CompressWithVKeyWitnessValues {
      compress_val: SP1ShapedWitnessValues { vks_and_proofs, is_complete },
      merkle_val: SP1MerkleProofWitnessValues {
        root: self.vks.root(),
        values,
        vk_merkle_proofs,
      },
    }
  }
}

/// The leaf machine's `(log_stacking_height, max_log_row_count)`: defaults
/// `(21, 23)` — four times SP1's compress row cap, sized for the 181-chip
/// stage-2 verifier — overridable through `IX_REC_LEAF_LOG_STACKING` and
/// `IX_REC_LEAF_MAX_LOG_ROWS` (the pinned shapes must match).
pub fn leaf_params() -> (u32, usize) {
  let env = |k: &str, d: usize| {
    std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d)
  };
  let stacking = env("IX_REC_LEAF_LOG_STACKING", 21);
  let rows = env("IX_REC_LEAF_MAX_LOG_ROWS", 23);
  (u32::try_from(stacking).expect("log stacking height"), rows)
}

/// With `IX_HC_DEBUG` set, print a program's recursion-chip event counts —
/// the row counts the recursion machine must fit.
fn report_program(stage: &str, program: &RecursionProgram<SP1Field>) {
  if std::env::var_os("IX_HC_DEBUG").is_some() {
    eprintln!("recursion {stage} program: {:?}", program.event_counts);
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
