//! Materialize the actual Input grammar events into entry locals and immutable
//! heap vectors. A stack holds only nonempty remaining sibling spans, so one
//! completed value needs at most one pop. Every popped stack cell is cleared.
pub mod batch;
mod gate;
mod relation;
mod slots;
use super::synthesis::*;
pub use gate::{InputCaptureGate, InputCaptureRow};
pub use slots::{InputCaptureSlots, InputCaptureWires};
pub const STATE_WORDS: usize = 5;
pub const INPUTS: usize = 40;
pub const OUTPUTS: usize = 30;
pub const GRAMMAR_INDICES: [usize; 8] = [0, 1, 2, 3, 11, 13, 24, 25];
pub const STACK: u64 = 11 << 36;
const NEXT: usize = 8;
const TAG: usize = 9;
const COMMITTED: usize = 10;
const FIELDS: usize = 11;
const NATURAL: usize = 24;
const RANGE: usize = 25;
const STATE: usize = 26;
const SPAN: usize = STATE;
const HEAP: usize = STATE + 1;
const DEPTH: usize = STATE + 2;
const SCALAR: usize = STATE + 3;
const ENTRY: usize = STATE + 4;
const RESOLVED: usize = 31;
const REPLIES: usize = 32;
