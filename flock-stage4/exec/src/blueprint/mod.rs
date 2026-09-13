//! Proof-free verifier topology compilation. Each phase is reconstructed from
//! approved interpreter/protocol geometry, then compared with native replay.
//! These blueprints fix the complete root-conditional replay. Key generation
//! and terminal root closure are separate obligations, not implied by them.

mod algebra;
mod boolean;
mod folds;
mod hash;
mod inner;
mod pcs;
mod tape;
mod transcript;
mod wiring;

pub(crate) use boolean::{BooleanBlueprint, compile_boolean};
pub(crate) use folds::{FoldBlueprint, compile_folds};
pub(crate) use pcs::{PcsBlueprint, compile_pcs};
pub(crate) use transcript::{MainBlueprint, compile_transcript};
pub(crate) use wiring::compile_wiring;
