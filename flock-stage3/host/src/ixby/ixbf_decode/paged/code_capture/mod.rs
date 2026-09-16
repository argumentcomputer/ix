//! Consume the actual Program dispatcher events and materialize the paged
//! code format. All carried parser/capture state and emitted memory accesses
//! must be chained. This is physical code capture, not whole-program semantic
//! reference validation or execution admission.
pub mod batch;
mod gate;
mod relation;
mod slots;
#[cfg(test)]
mod tests;
use super::synthesis::*;
pub use gate::{CodeCaptureGate, CodeCaptureRow};
pub use slots::{CodeCaptureSlots, CodeCaptureWires};

pub const STATE_WORDS: usize = 7;
pub const INPUTS: usize = 36;
pub const OUTPUTS: usize = 23;
/// Original cursor/control/count words consumed by the capture relation.
pub const GRAMMAR_INDICES: [usize; 10] = [0, 1, 2, 3, 7, 8, 5, 6, 10, 11];
const NEXT: usize = 10;
const NEXT_CONTROL: usize = 11;
const TAG: usize = 12;
const COMMITTED: usize = 13;
const FIELDS: usize = 14;
const NATURAL: usize = 27;
const RANGE: usize = 28;
const STATE: usize = 29;
const CURRENT: usize = STATE;
const OPEN: usize = STATE + 1;
const HEADER: usize = STATE + 2;
const OPERANDS: usize = STATE + 3;
const SCALAR: usize = STATE + 4;
const SEEN: usize = STATE + 5;
