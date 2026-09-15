//! Commit actual completed transport arenas and read individual authenticated
//! records. Child/root locators are untrusted hints, checked against the tree
//! metadata derived by the source-bound loader. This is not mutable VM memory.
#[cfg(test)]
mod fixtures;
mod gate;
mod layout;
#[cfg(test)]
mod proof_tests;
mod relation;
mod slots;
#[cfg(test)]
mod tests;

pub use gate::{ValueAccessGate, ValueAccessOp, ValueAccessRow};
pub use layout::{ValueKind, ValueLayout};
pub use slots::{
  AuthenticatedValueChunk, SealedValues, ValueAccessReadWires,
  ValueAccessSlots, ValueCommitSlots, ValueRequestWires,
};
