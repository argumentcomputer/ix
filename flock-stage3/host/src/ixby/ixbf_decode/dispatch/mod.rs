//! Fixed-topology, state-selected decoding of the original wire grammar.
//!
//! Every step emits every decoder. Selection, bounds, byte requests, payload
//! lengths and progress are constrained from the carried state, not chosen by
//! a host AST. UTF-8 may take several steps before a grammar event commits.
//! A caller must authenticate the requested bytes to ONE expected artifact,
//! pin genuine initialization and final completion, and consume committed
//! typed events. This is not registry admission or an Exec proving profile.

mod control;
#[cfg(test)]
mod external_tests;
mod gate;
#[cfg(test)]
mod model_tests;
#[cfg(test)]
mod proof_tests;
mod routing;
mod slots;
#[cfg(test)]
mod tests;

pub use gate::{DispatchConfig, DispatchGate, DispatchOp, DispatchRow};
pub use slots::{DispatchSlots, DispatchState, DispatchStepWires};

use super::synthesis::{Bits, Builder};

pub const DISPATCH_STATE_WORDS: usize = 30;
/// Constructors, functions, ten limits, entry, entry arity, and fuel.
/// Transport callers must bind these to the admitted program, not free advice.
pub const DISPATCH_CONTEXT_WORDS: usize = 15;
pub const DISPATCH_CONTEXT_INDICES: [usize; DISPATCH_CONTEXT_WORDS] =
  [2, 3, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27];

pub(super) const REQUEST_WORDS: usize = 9;
pub(super) const ENABLES: usize = 18;
pub(super) const RECORD_PORTS: usize = ENABLES;
pub(super) const HEADER_PORT: usize = RECORD_PORTS + 13 * 9;
pub(super) const NATURAL_PORT: usize = HEADER_PORT + 18;

fn word(index: usize) -> Bits {
  (index * 128..(index + 1) * 128).collect()
}
fn masked(b: &mut Builder, flag: usize, input: &[usize]) -> Bits {
  input.iter().map(|&bit| b.b.and(flag, bit)).collect()
}
/// Inputs to this selector are pairwise exclusive derived Boolean flags.
fn select(b: &mut Builder, choices: &[(usize, Bits)], width: usize) -> Bits {
  (0..width)
    .map(|bit| {
      let terms: Vec<_> =
        choices.iter().map(|(flag, bits)| b.b.and(*flag, bits[bit])).collect();
      b.sum(&terms)
    })
    .collect()
}
fn tags(b: &mut Builder, index: usize) -> Bits {
  b.require_zero(b.one, &word(index)[8..]);
  let flags: Bits =
    (0..18).map(|tag| b.eq_const(&word(index)[..8], tag)).collect();
  let valid = b.any(&flags);
  b.require(b.one, valid);
  flags
}
