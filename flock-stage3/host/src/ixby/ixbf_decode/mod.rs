//! Constrained codecs for the original functional wire, separate from IXBY.
//!
//! These component relations are not a whole-image admission or an Exec
//! proving profile. Their raw-byte wires must be shared with the authenticated
//! original artifact, and their outputs with the actual parser/interpreter.
//! A host-selected byte window or acceptance bit cannot establish that link.
//! Existing native codecs, factories, profile encodings and keys are unchanged.

pub mod bodies;
mod byte_span;
#[cfg(test)]
mod byte_span_tests;
pub mod dispatch;
#[cfg(test)]
mod external_tests;
mod grammar;
#[cfg(test)]
mod grammar_reference_tests;
#[cfg(test)]
mod grammar_tests;
mod header;
#[cfg(test)]
mod header_tests;
mod link;
#[cfg(test)]
mod link_tests;
mod natural;
mod natural_limit;
mod payload;
#[cfg(test)]
mod proof_tests;
mod record;
#[cfg(test)]
mod record_external_tests;
#[cfg(test)]
mod record_tests;
pub mod references;
pub mod registry;
#[cfg(test)]
mod scalar_payload_tests;
pub mod source;
mod synthesis;
#[cfg(test)]
mod tests;
mod utf8;
pub mod values;

pub use byte_span::{
  ByteArraySpanGate, ByteArraySpanRow, ByteArraySpanSlot, ByteArraySpanWires,
};
pub use grammar::{
  GRAMMAR_EVENT_FIELDS, GRAMMAR_INPUTS, GRAMMAR_STATE_WORDS, GrammarEvent,
  GrammarKind, GrammarState, GrammarStepGate, GrammarStepRow, GrammarStepSlot,
};
pub use header::{
  HEADER_FIELDS, HEADER_METADATA_BITS, HEADER_PREFIX_BYTES,
  HEADER_PREFIX_WORDS, HeaderDecodeGate, HeaderDecodeRow, HeaderDecodeSlot,
  HeaderWires, MAX_HEADER_BYTES,
};
pub use link::{RecordLinkGate, RecordLinkKind, RecordLinkRow, RecordLinkSlot};
pub use natural::{
  NaturalCapacity, NaturalDecodeGate, NaturalDecodeRow, NaturalDecodeSlot,
};
pub use natural_limit::{NaturalLimitGate, NaturalLimitRow, NaturalLimitSlot};
pub use payload::{
  PayloadCursorGate, PayloadCursorRow, PayloadCursorSlot, PayloadCursorWires,
};
pub use record::{
  RECORD_FIELDS, RECORD_INPUTS, RECORD_LOOKAHEAD_BYTES, RECORD_LOOKAHEAD_WORDS,
  RecordDecodeGate, RecordDecodeRow, RecordDecodeSlot, RecordKind, RecordWires,
};
pub use utf8::{Utf8ChunkGate, Utf8ChunkRow, Utf8ChunkSlot, Utf8ChunkWires};

/// Component semantics revision; this is not the IXBF format version, an
/// IXBP profile revision, or authorization to use these codecs in Exec.
pub const CODEC_REVISION: u32 = 0;

/// Explicit local codec capacity, not an implicit change to a guest's limits.
pub const MAX_NAT_BITS: usize = 4096;
