//! Packed functional code and authenticated fetch consumers for paged frames.
//! Host packing is only witness advice. Admission must independently connect
//! every stored header/operand to the original IXBF grammar events and check
//! whole-program references; the host packer does not establish that bridge.
mod gate;
mod model;
mod slots;
mod synthesis;
#[cfg(test)]
mod tests;
pub use gate::{CodeGate, CodeGateKind, CodeRow};
pub use model::{
  BLOCKS, CONSTRUCTORS, FUNCTIONS, Header, PackedProgram, block_address,
};
pub use slots::{CodeReadWires, CodeSlots, OperandReadWires};
