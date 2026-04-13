//! `.noConfusionType` and `.noConfusion` generation.
//!
//! `.noConfusionType` builds a type family for constructor discrimination.
//! `.noConfusion` uses `.casesOn` to prove distinct constructors differ.
//!
//! NOTE: noConfusion's value calls casesOn, so it needs regeneration when
//! casesOn changes arity due to alpha-collapse. This is complex (requires
//! MetaM-like operations) and is deferred. Currently returns None, which
//! means the original Lean noConfusion will be compiled as-is. This will
//! produce structurally incorrect Ixon for collapsed blocks — the noConfusion
//! value will have too many arguments to casesOn. This will be caught by
//! the kernel type checker when roundtrip testing is enabled.

use crate::ix::compile::aux_gen::AuxDef;
use crate::ix::env::{Env as LeanEnv, Name};
use crate::ix::ixon::CompileError;

/// Generate `.noConfusionType` and `.noConfusion` for an inductive.
///
/// Returns `(noConfusionType, Option<noConfusion>)`.
/// Returns `None` if the inductive structure cannot be processed.
pub(crate) fn _generate_no_confusion(
  _ind_name: &Name,
  _sorted_classes: &[Vec<Name>],
  _lean_env: &LeanEnv,
) -> Result<Option<(AuxDef, Option<AuxDef>)>, CompileError> {
  // TODO: Implement from Lean 4 reference
  Ok(None)
}
