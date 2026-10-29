//! Aggregation rebase: restate an extension's root onto a base library.
//!
//! An extension environment holds its own constants plus the base constants
//! they reference. Its manifest partitions only its own constants; prepared
//! against the base's constant set, every shard keeps its edges to base
//! constants as assumptions, and the aggregate root claims
//! `CheckEnv(R_d, some A_d)` with `A_d` the base constants it references. The
//! rebase shape (13) discharges every leaf of `A_d` by a membership path into
//! the base's subjects root `R_base` and proves `CheckEnv(R_d, some R_base)`,
//! which a merge with the base's closed certificate then closes.

use super::{
  RunConfig,
  plan::build_statement_specs,
  prepare::{
    PreparedRun, RootAssumptions, prepare_run, prepare_run_with_base,
    validate_root_statement,
  },
  protocol::{
    REBASE_SHAPE, aggregate_outer_claim, allowed_blob, packed_digest,
    serialize_claims,
  },
  prove::{push_canonical_tree, rebase_path_advice},
  run,
  statement::Statement,
  store::{decode_wrapper, persist_wrapper, read_store},
};
use aiur::synthesis::{AiurProof, AiurSystem, GatedProve};
use ix_common::address::Address;
use ix_kernel::shard::ShardManifest;
use ixvm_codegen::{
  aiur_ix_aggr_runner::{
    AggrAdvice, AggrPath, AggrPreimage, AggrTree, aggr_io_buffer,
    execute_ix_aggr,
  },
  env_handle::EnvHandle,
};
use rustc_hash::FxHashSet;
use std::{fs, path::Path, sync::Arc};

#[derive(Clone, Copy)]
pub(super) struct RebaseConfig<'a> {
  /// The extension's Stage 2 run. Its environment holds the extension's
  /// constants and the base constants they reference; its manifest
  /// partitions only the former. The rebase sets its base constants and
  /// reads its root back from the store, so it must write its outputs.
  pub(super) extension: RunConfig<'a>,
  pub(super) base: BaseSource<'a>,
}

/// Where a base library comes from: its environment, its manifest, and the
/// structural threshold that fixes its subject-tree shape and so its root.
#[derive(Clone, Copy)]
pub(super) struct BaseSource<'a> {
  pub(super) ixe_path: &'a Path,
  pub(super) manifest_path: &'a Path,
  pub(super) structural_above: usize,
}

pub(super) fn read_manifest(path: &Path) -> Result<ShardManifest, String> {
  let bytes = fs::read(path)
    .map_err(|error| format!("read manifest {}: {error}", path.display()))?;
  ShardManifest::from_bytes(&bytes)
    .map_err(|error| format!("manifest parse failed: {error}"))
}

fn root_statement(
  prepared: &PreparedRun,
  structural_above: usize,
) -> Result<Arc<Statement>, String> {
  Ok(
    build_statement_specs(prepared, structural_above)?
      .last()
      .ok_or("manifest produced no root statement")?
      .statement
      .clone(),
  )
}

/// A base library's closed root and its constant set, rebuilt from its
/// environment and manifest.
pub(super) struct Base {
  pub(super) prepared: PreparedRun,
  pub(super) root: Arc<Statement>,
  pub(super) constants: FxHashSet<Address>,
}

impl Base {
  pub(super) fn prepare(
    env: &ixon::Env,
    manifest: &ShardManifest,
    structural_above: usize,
  ) -> Result<Self, String> {
    let prepared = prepare_run(env, manifest)?;
    let root = root_statement(&prepared, structural_above)?;
    validate_root_statement(&prepared, &root, RootAssumptions::Closed)
      .map_err(|error| format!("base root: {error}"))?;
    let constants = prepared.owner_by_address.keys().cloned().collect();
    Ok(Self { prepared, root, constants })
  }

  pub(super) fn load(source: BaseSource<'_>) -> Result<Self, String> {
    let env = EnvHandle::from_ixe_path(source.ixe_path).map_err(|error| {
      format!("base environment {}: {error}", source.ixe_path.display())
    })?;
    Self::prepare(
      &env.env,
      &read_manifest(source.manifest_path)?,
      source.structural_above,
    )
  }

  pub(super) fn subjects_root(&self) -> &Address {
    &self.root.subjects.root
  }
}

/// An extension root and its rebase onto a base, checked before proving.
pub(super) struct RebasePlan {
  child: Arc<Statement>,
  output: Arc<Statement>,
  paths: Vec<(Address, Vec<u8>)>,
}

/// Rebuild an extension partition's root against `base` and plan its rebase:
/// the root must assume only base constants, at least one, and every one must
/// have a membership path into the base subjects root.
pub(super) fn plan_rebase(
  env: &ixon::Env,
  manifest: &ShardManifest,
  structural_above: usize,
  base: &Base,
) -> Result<RebasePlan, String> {
  let prepared = prepare_run_with_base(env, manifest, Some(&base.constants))?;
  let child = root_statement(&prepared, structural_above)?;
  validate_root_statement(&prepared, &child, RootAssumptions::External)?;
  if child.assumptions.is_none() {
    return Err(
      "the extension references no base constant; it needs no rebase".into(),
    );
  }
  let base_root = base.subjects_root();
  let output = Statement::rebased(child.subjects.clone(), base_root);
  validate_root_statement(
    &prepared,
    &output,
    RootAssumptions::Base(base_root),
  )?;
  let paths = rebase_path_advice(
    &child,
    &base.root.subjects,
    &base.prepared.owner_by_address,
  )?;
  Ok(RebasePlan { child, output, paths })
}

impl RebasePlan {
  /// The rebased root statement, `CheckEnv(R_d, some R_base)`.
  pub(super) fn output(&self) -> &Arc<Statement> {
    &self.output
  }

  /// The extension constants the rebased root certifies, each exactly once.
  pub(super) fn subject_count(&self) -> usize {
    self.output.subjects.count
  }
}

fn load_child_proof(
  store_dir: &Path,
  hex: &str,
  expected: &Statement,
) -> Result<AiurProof, String> {
  let address = Address::from_hex(hex.trim()).ok_or_else(|| {
    format!("rebase child proof is not a 64-character address: {hex}")
  })?;
  let bytes = read_store(store_dir, &address)?;
  if Address::hash(&bytes) != address {
    return Err(format!(
      "rebase child store object {} has the wrong digest",
      address.hex()
    ));
  }
  let wrapper = decode_wrapper(&bytes).map_err(|error| {
    format!("decode rebase child proof {}: {error}", address.hex())
  })?;
  if wrapper.claim != expected.claim {
    return Err(format!(
      "rebase child proof {} does not prove the extension's statement",
      address.hex()
    ));
  }
  AiurProof::from_bytes(&wrapper.proof).map_err(|error| {
    format!("rebase child proof {} does not decode: {error}", address.hex())
  })
}

/// Aggregate the extension against the base with Stage 2, prove the rebase of
/// its root onto the base, and return the rebased proof's store address. The
/// base must be a closed root of its manifest; the result is conditional on
/// exactly the base's subjects root.
pub(super) fn run_rebase(config: RebaseConfig<'_>) -> Result<String, String> {
  let extension = config.extension;
  if extension.plan_only
    || extension.verify_only
    || extension.subtree.is_some()
    || extension.reprove_slot.is_some()
  {
    return Err("a rebase proves the whole extension root".into());
  }
  if !extension.write_outputs {
    return Err("a rebase reads the extension root from the store".into());
  }
  let base = Base::load(config.base)?;
  let plan = plan_rebase(
    &extension.env_handle.env,
    &read_manifest(extension.manifest_path)?,
    extension.structural_above,
    &base,
  )?;
  let child_hex =
    run(RunConfig { base_constants: Some(&base.constants), ..extension })?;
  let home = std::env::var_os("HOME").ok_or("no HOME environment variable")?;
  prove_rebase(
    RebaseSystems {
      ixvm_system: extension.ixvm_system,
      aggr_system: extension.aggr_system,
      verify_idx: extension.verify_idx,
      aggr_idx: extension.aggr_idx,
    },
    &plan,
    &child_hex,
    &Path::new(&home).join(".ix").join("store"),
  )
}

#[derive(Clone, Copy)]
pub(super) struct RebaseSystems<'a> {
  pub(super) ixvm_system: &'a AiurSystem,
  pub(super) aggr_system: &'a AiurSystem,
  pub(super) verify_idx: usize,
  pub(super) aggr_idx: usize,
}

/// Prove the planned rebase of the extension root proof at `child_hex` in the
/// store, persist it, and return its address.
pub(super) fn prove_rebase(
  systems: RebaseSystems<'_>,
  plan: &RebasePlan,
  child_hex: &str,
  store_dir: &Path,
) -> Result<String, String> {
  let RebasePlan { child, output, paths } = plan;
  let base_root =
    output.assumptions_root().ok_or("a rebased statement names its base")?;
  let child_proof = load_child_proof(store_dir, child_hex, child)?;
  let ixvm_vk = aiur::vk_codec::aiur_system_to_bytes(systems.ixvm_system)
    .map_err(|error| format!("IxVM VK serialization failed: {error}"))?;
  let aggr_vk = aiur::vk_codec::aiur_system_to_bytes(systems.aggr_system)
    .map_err(|error| format!("ixAggr VK serialization failed: {error}"))?;
  let allowed =
    allowed_blob(&ixvm_vk, systems.verify_idx, &aggr_vk, systems.aggr_idx);
  let child_outer =
    aggregate_outer_claim(systems.aggr_idx, &allowed, &child.claim_bytes);
  // Verifies the child under this aggregation identity before expanding it.
  let child_advice = systems
    .aggr_system
    .proof_to_advice_bytes(&child_outer, &child_proof)
    .map_err(|error| format!("rebase child proof advice failed: {error}"))?;
  let child_claims = serialize_claims(&[&child_outer]);

  let preimages = [AggrPreimage {
    digest: *blake3::hash(&child.claim_bytes).as_bytes(),
    bytes: &child.claim_bytes,
  }];
  let mut tree_storage = Vec::new();
  if let Some(tree) = &child.assumptions {
    push_canonical_tree(&mut tree_storage, tree);
  }
  let trees: Vec<AggrTree<'_>> = tree_storage
    .iter()
    .map(|tree| AggrTree { root: tree.root, bytes: &tree.bytes })
    .collect();
  let paths: Vec<AggrPath<'_>> = paths
    .iter()
    .map(|(candidate, bytes)| AggrPath {
      candidate: *candidate.as_bytes(),
      bytes,
    })
    .collect();
  let mut io = aggr_io_buffer(&AggrAdvice {
    shape: REBASE_SHAPE,
    proof_advice: [&child_advice, &[]],
    ixvm_vk: &ixvm_vk,
    self_vk: &aggr_vk,
    child_claims: [&child_claims, &[]],
    output_claim: &output.claim_bytes,
    allowed: &allowed,
    preimages: &preimages,
    trees: &trees,
    paths: &paths,
  });
  let mut public_input = packed_digest(&allowed);
  public_input.extend(packed_digest(&output.claim_bytes));
  let (outer_claim, proof) = match systems.aggr_system.prove_ixvm_within_budget(
    systems.aggr_idx,
    &public_input,
    &mut io,
    execute_ix_aggr,
    None,
    false,
    false,
    None,
  ) {
    GatedProve::Proved { claim, proof, .. } => (claim, proof),
    GatedProve::Failed(error) => {
      return Err(format!("rebase execution failed: {error}"));
    },
    _ => return Err("rebase prove did not produce a proof".into()),
  };
  let expected_outer =
    aggregate_outer_claim(systems.aggr_idx, &allowed, &output.claim_bytes);
  if outer_claim != expected_outer {
    return Err("rebase prover returned an unexpected outer claim".into());
  }
  systems.aggr_system.verify(&expected_outer, &proof).map_err(|error| {
    format!("rebased root proof failed verification: {error:?}")
  })?;
  let address = persist_wrapper(store_dir, output, &proof)?;
  eprintln!(
    "[aggregate] rebased {} assumption(s) onto base {}: {}",
    paths.len(),
    base_root.hex(),
    address.hex()
  );
  Ok(address.hex())
}
