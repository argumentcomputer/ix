//! Exact batched memory access constraints. The fixed switching network moves
//! complete records, using constrained Boolean selectors and native F128
//! arithmetic. No witness-selected topology or probabilistic multiset equality
//! is used. Memory authentication and execution are separate callers.

mod audit;
mod boolean_switch;
mod packing;
mod permutation;
#[cfg(test)]
mod proof_tests;
mod slots;
mod switch;
#[cfg(test)]
mod tests;
mod timed;
mod witness;

pub use audit::{
  AuditGate, AuditRow, PAD, READ, RECORD_WORDS, SEAL, SEED, WRITE,
};
pub use boolean_switch::{BooleanSwitchGate, BooleanSwitchRow};
pub use packing::{RecordLayout, RecordPackingGate, RecordPackingRow};
pub use permutation::{PermutationPlan, PermutationSlots, RoutingKind};
pub use slots::{AccessWires, BoundaryWires, MemoryLogSlots};
pub use switch::{SwitchGate, SwitchRow};
pub use timed::{TimedAccessWires, TimedMemoryLogSlots};
#[cfg(test)]
pub(crate) use witness::shared_parent_count;
pub use witness::{
  AccessAdvice, BoundaryAdvice, MemoryBatch, MemoryBatchAdvice,
};
