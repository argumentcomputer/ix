//! Proof-free verifier topology compilation. Each phase is reconstructed from
//! approved interpreter/protocol geometry, then compared with native replay.
//! Until every phase is covered this is not a complete Stage 4 setup compiler.

mod algebra;
mod boolean;
mod inner;
mod pcs;
mod tape;
mod transcript;
mod wiring;

pub(crate) use boolean::compile_boolean;
pub(crate) use pcs::compile_pcs;
pub(crate) use transcript::compile_transcript;
pub(crate) use wiring::compile_wiring;
