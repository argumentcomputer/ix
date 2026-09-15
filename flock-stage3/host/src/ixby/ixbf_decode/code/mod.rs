//! BLAKE3 commitments to actual completed typed code, with reusable
//! authenticated chunk handles and record-sized consumers. Sealing is still
//! bounded by the existing body loader; access never carries its full bank.
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

pub use gate::{CodeGate, CodeOp, CodeRow};
pub use layout::{CodeKind, CodeLayout};
pub use slots::{
  AuthenticatedCodeChunk, CodeAccessSlots, CodeCommitSlots, CodeReadWires,
  CodeRequestWires, SealedCode,
};
