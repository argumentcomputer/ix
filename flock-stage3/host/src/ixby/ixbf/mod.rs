//! Strict host-side intake for the complete functional `IXBF` format.
//!
//! This is NOT the constrained `IXBY` decoder and does not admit a Flock
//! execution proof. It preserves the original bytes and arbitrary-precision
//! naturals for witness generation, differential tests, and capacity planning.
//! No acceptance bit or decoded table from this module is trusted by `exec`.
//! Format/semantic revisions and primitive tags remain separate from the
//! existing proving-profile wire. A native constraint/codec correspondence
//! proof is still required before connecting this intake to a proving path.

mod decode;
mod encode;
#[cfg(test)]
mod external_tests;
mod inventory;
mod model;
mod primitive;
#[cfg(test)]
mod tests;
mod validate;

pub use decode::DecodeLimits;
pub use inventory::{Inventory, PrimitiveInventory, ScalarInventory};
pub use model::{
  Alternative, Artifact, Block, ConstructorDeclaration, ConstructorId,
  Function, Input, Instruction, Limits, Operand, Operation, Output, Scalar,
  ValueForest, ValueKind, ValueNode,
};
pub use primitive::Primitive;

pub const FORMAT_VERSION: u32 = 1;
pub const SEMANTICS_VERSION: u32 = 0;

/// Parse and validate every declaration, including unreachable instructions.
/// Host loader limits are independent of the semantic limits inside the file.
pub fn decode_program(
  bytes: &[u8],
  loader: DecodeLimits,
) -> anyhow::Result<Artifact<'_>> {
  decode::program(bytes, loader)
}

pub fn decode_input<'a>(
  artifact: &Artifact<'_>,
  bytes: &'a [u8],
  loader: DecodeLimits,
) -> anyhow::Result<Input<'a>> {
  decode::input(artifact, bytes, loader)
}

pub fn decode_output<'a>(
  artifact: &Artifact<'_>,
  bytes: &'a [u8],
  loader: DecodeLimits,
) -> anyhow::Result<Output<'a>> {
  decode::output(artifact, bytes, loader)
}
