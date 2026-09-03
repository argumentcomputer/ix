//! SP1 Hypercube proving backend for Aiur.
//!
//! Aiur circuits are symbolic: base-field constraint expressions plus
//! lookups (a signed multiplicity and a message). This crate interprets that
//! IR inside SP1 Hypercube's `AirBuilder`, so every Aiur circuit becomes a
//! Hypercube chip without hand-written constraint code, and the lookups
//! become LogUp-GKR interactions.
//!
//! Hypercube differences the backend absorbs:
//! - interaction messages and multiplicities must be affine in the trace
//!   columns, so non-affine lookup arguments are materialized into extra
//!   columns ([`expr::Lowered`]);
//! - constraints are row-local (no next-row references or row selectors);
//! - the top-level claim enters through the public values via a dedicated
//!   claim chip.

pub mod air;
pub mod expr;
pub mod frontend;
pub mod global;
pub mod machine;
pub mod prover;
pub mod record;
pub mod shard;

/// The Hypercube base field (KoalaBear).
pub type F = sp1_primitives::SP1Field;

/// The frontend field Aiur circuits are expressed in for this backend:
/// Plonky3's KoalaBear (same modulus as [`F`], checked at the boundary).
pub type FrontendField = p3_koala_bear::KoalaBear;

pub use air::AiurAir;
pub use frontend::ToplevelMachine;
pub use machine::{AiurMachine, BuildError, CircuitSpec};
pub use prover::{AiurProof, AiurVerifyingKey, ProverParams, prove, verify};
pub use record::{AiurProgram, AiurRecord};
pub use shard::ShardingParams;
