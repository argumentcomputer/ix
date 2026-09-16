//! Exact batched memory access constraints. The fixed switching network moves
//! complete records, using constrained Boolean selectors and native F128
//! arithmetic. No witness-selected topology or probabilistic multiset equality
//! is used. Memory authentication and execution are separate callers.

mod audit;
mod permutation;
#[cfg(test)]
mod proof_tests;
mod slots;
mod switch;
#[cfg(test)]
mod tests;
mod witness;

pub use audit::{
  AuditGate, AuditRow, PAD, READ, RECORD_WORDS, SEAL, SEED, WRITE,
};
pub use permutation::{PermutationPlan, PermutationSlots};
pub use slots::{AccessWires, BoundaryWires, MemoryLogSlots};
pub use switch::{SwitchGate, SwitchRow};
pub use witness::{
  AccessAdvice, BoundaryAdvice, MemoryBatch, MemoryBatchAdvice,
};
