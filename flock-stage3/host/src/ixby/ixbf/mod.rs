//! Strict host-side intake for the complete functional `IXBF` format.
//!
//! It preserves original bytes and arbitrary-precision naturals for witness
//! generation, differential tests, and capacity planning. Its acceptance bit
//! and decoded tables are untrusted advice. The paged constrained admission
//! path independently checks the original bytes and execution memory.

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
pub const SEMANTICS_VERSION: u32 = 2;
/// Programs and typed IO share one current semantic revision.
pub const PROGRAM_SEMANTICS_VERSION: u32 = SEMANTICS_VERSION;

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
