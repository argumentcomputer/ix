//! The proving controller: from an environment and its shard manifest to a
//! verified aggregate root, for any proof system behind [`Backend`].
//!
//! Everything data-dependent after the proof systems are built is kept
//! here: manifest/environment binding, shard-claim reconstruction,
//! statement folding, cache validation, dependency scheduling, admission
//! under a shared record budget, bisection of oversized claims, resumption
//! and persistence. A backend executes, proves, verifies and encodes one
//! unit of work.
//!
//! The host statements deliberately cache roots and sorted leaves. Structural
//! subject trees carry only their two children and a small shard-membership
//! bitset, so deciding whether an assumption is discharged is O(1), and a
//! Merkle path is O(log n). This avoids the eager recursive `root`/`leaves`/
//! `contains` traversals that made the former Lean startup super-linear.

use std::sync::Arc;

use ixon::shard::ShardManifest;

pub mod advice;
pub mod aggregate;
pub mod backend;
pub mod catalog;
pub mod discharge;
pub mod lanes;
pub mod plan;
pub mod prepare;
pub mod protocol;
pub mod scheduler;
pub mod statement;
pub mod store;
pub mod streams;

pub use backend::{
  Backend, BackendSlot, ChildProof, ExtraNode, Identity, PrepareFailure,
  ProvenClaim, Run, Slot,
};

pub const MIB: usize = 1024 * 1024;
pub const GIB: usize = 1024 * 1024 * 1024;

pub fn format_gib(bytes: usize) -> String {
  let tenths = bytes.saturating_mul(10) / GIB;
  format!("{}.{:01}", tenths / 10, tenths % 10)
}

pub fn format_mib(bytes: usize) -> String {
  let tenths = bytes.saturating_mul(10) / MIB;
  format!("{}.{:01}", tenths / 10, tenths % 10)
}

pub fn panic_text(payload: &Box<dyn std::any::Any + Send>) -> &str {
  payload
    .downcast_ref::<&str>()
    .copied()
    .or_else(|| payload.downcast_ref::<String>().map(String::as_str))
    .unwrap_or("unknown Rust panic")
}

/// The root statement a manifest folds to, after a full constant, shard and
/// assumption audit, and the number of constants it covers.
pub fn expected_from_manifest(
  ctx: &ixon::ClaimContext,
  env: &ixon::Env,
  manifest: &ShardManifest,
  structural_above: usize,
) -> Result<(Arc<statement::Statement>, usize), String> {
  let prepared = prepare::prepare_run(ctx, env, manifest)?;
  let specs = plan::build_statement_specs(&prepared, structural_above)?;
  let root = specs
    .last()
    .ok_or("aggregate manifest produced no root statement")?
    .statement
    .clone();
  prepare::validate_root_statement(&prepared, &root)?;
  Ok((root, prepared.env_count))
}

/// The context of the claims proven over `env`: its own role binding under
/// this specification set, assumed rather than validated with
/// `assume_binding`.
pub fn claim_context(
  env: &ixon::Env,
  assume_binding: bool,
) -> Result<ixon::ClaimContext, String> {
  let ctx = ixon::ClaimContext::for_env(env)?;
  Ok(if assume_binding { ctx.assuming_binding() } else { ctx })
}

#[cfg(test)]
mod tests;
