//! Nested-inductive detection and flat block construction.
//!
//! Detects nested occurrences in constructor field types (e.g., `List (Option A)`)
//! and builds auxiliary entries for the flat block. Currently stubbed to return
//! no nested occurrences — will be ported from ix_old when needed.

use crate::ix::env::{Env as LeanEnv, Expr as LeanExpr, Level, Name};

/// A member of the flat block (original inductive or nested auxiliary).
#[derive(Clone)]
pub(crate) struct CompileFlatMember {
  pub name: Name,
  pub spec_params: Vec<LeanExpr>,
  pub occurrence_level_args: Vec<Level>,
  pub own_params: usize,
  pub n_indices: usize,
}

/// Build a flat block from an ordered list of original inductives.
///
/// Detects nested inductive occurrences in constructor fields and
/// creates auxiliary entries. Currently returns only the originals
/// (no nested detection yet).
pub(crate) fn build_compile_flat_block(
  ordered_originals: &[Name],
  lean_env: &LeanEnv,
) -> Vec<CompileFlatMember> {
  use crate::ix::env::ConstantInfo;

  ordered_originals
    .iter()
    .filter_map(|name| {
      let ind = match lean_env.get(name) {
        Some(ConstantInfo::InductInfo(v)) => v,
        _ => return None,
      };
      Some(CompileFlatMember {
        name: name.clone(),
        spec_params: vec![],
        occurrence_level_args: vec![],
        own_params: ind.num_params.to_u64().unwrap_or(0) as usize,
        n_indices: ind.num_indices.to_u64().unwrap_or(0) as usize,
      })
    })
    .collect()
}
