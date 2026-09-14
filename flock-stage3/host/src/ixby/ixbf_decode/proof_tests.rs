//! Component proofs only. Public prefix/payload words are externally expected
//! inputs. HeaderFuel binds the decoded budget to the ledger, but its public
//! control kinds are not authenticated VM states and do not prove execution.

use super::*;
use crate::ixby::wide_fuel::{Fuel64StepGate, Fuel64StepSlot};
use anyhow::{Result, ensure};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{
    CircuitShape, CircuitWitness, GateType, ShapeBuilder, SlotId,
  },
  field::F128,
  hash::HashKind,
  lincheck::LincheckCircuit,
  pcs::{
    Commitment, PcsParams,
    ligerito::{LigeritoProfile, embedded_initial_k_or_default},
  },
  proof::R1csProofCircuitMerged,
  prover::{self, UnionSlotProverInput},
  r1cs::BlockR1cs,
  union::UnionInstance,
  verifier,
};
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
use std::{
  io::{Read, Write},
  process::{Command, Stdio},
};

const MAGIC: [u8; 8] = *b"IXFCOD00";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
const CHILD: &str = "IXBY_FUNCTIONAL_CODEC_VERIFY_CHILD";
const TEST: &str = "ixby::ixbf_decode::proof_tests::functional_codec_proofs_verify_in_fresh_process_and_reject_recomputed_substitutions";
const STEPS: usize = 6;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Component {
  Natural,
  Header,
  HeaderFuel,
  ByteSpan,
  HeaderSpan,
  Record(RecordKind),
  Link(RecordLinkKind),
  CallRecords,
  ConstructorRecords,
  Grammar(GrammarKind),
  GrammarProgram,
  GrammarForest,
  Payload,
  NaturalLimit,
  Utf8,
  GrammarNatural,
  GrammarString,
}

impl Component {
  fn tag(self) -> u8 {
    match self {
      Self::Natural => 0,
      Self::Header => 1,
      Self::HeaderFuel => 2,
      Self::ByteSpan => 3,
      Self::HeaderSpan => 4,
      Self::Record(kind) => 16 + kind as u8,
      Self::Link(kind) => 32 + kind as u8,
      Self::CallRecords => 64,
      Self::ConstructorRecords => 65,
      Self::Grammar(kind) => 48 + kind as u8,
      Self::GrammarProgram => 66,
      Self::GrammarForest => 67,
      Self::Payload => 51,
      Self::NaturalLimit => 52,
      Self::Utf8 => 53,
      Self::GrammarNatural => 68,
      Self::GrammarString => 69,
    }
  }
  fn from_tag(tag: u8) -> Result<Self> {
    Ok(match tag {
      0 => Self::Natural,
      1 => Self::Header,
      2 => Self::HeaderFuel,
      3 => Self::ByteSpan,
      4 => Self::HeaderSpan,
      16..=28 => Self::Record(RecordKind::ALL[usize::from(tag - 16)]),
      32..=36 => Self::Link(RecordLinkKind::ALL[usize::from(tag - 32)]),
      64 => Self::CallRecords,
      65 => Self::ConstructorRecords,
      48 => Self::Grammar(GrammarKind::Program),
      49 => Self::Grammar(GrammarKind::Input),
      50 => Self::Grammar(GrammarKind::Output),
      66 => Self::GrammarProgram,
      67 => Self::GrammarForest,
      51 => Self::Payload,
      52 => Self::NaturalLimit,
      53 => Self::Utf8,
      68 => Self::GrammarNatural,
      69 => Self::GrammarString,
      _ => anyhow::bail!("unknown codec component"),
    })
  }
  fn nu(self) -> usize {
    match self {
      Self::Natural => 7,
      Self::ByteSpan => 9,
      Self::Record(kind) => {
        22 - RecordDecodeGate::new(3, kind).unwrap().plan().k_log()
      },
      Self::Link(kind) => {
        22 - RecordLinkGate::new(3, kind).unwrap().plan().k_log()
      },
      Self::CallRecords => 7,
      Self::ConstructorRecords => 6,
      Self::Payload => 10,
      Self::NaturalLimit => 7,
      Self::Utf8 => 8,
      _ => 5,
    }
  }
  fn pins(self) -> usize {
    if self == Self::GrammarNatural {
      return 15;
    }
    if self == Self::GrammarString {
      return 17;
    }
    if self == Self::GrammarProgram {
      return 14;
    }
    if self == Self::GrammarForest {
      return 8;
    }
    if matches!(self, Self::CallRecords | Self::ConstructorRecords) {
      return 5;
    }
    if matches!(self, Self::HeaderFuel | Self::HeaderSpan) { 2 } else { 1 }
  }
  fn fixed_public(self) -> Vec<F128> {
    if self == Self::GrammarNatural {
      return [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 8, 9, 11, 14, 17]
        .map(|v| F128::new(v, 0))
        .to_vec();
    }
    if self == Self::GrammarString {
      return [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 8, 9, 11, 1, 15, 17]
        .map(|v| F128::new(v, 0))
        .to_vec();
    }
    if self == Self::GrammarProgram {
      return [0, 0, 0, 0, 0, 0, 0, 1, 13, 1, 4, 5, 10, 17]
        .map(|v| F128::new(v, 0))
        .to_vec();
    }
    if self == Self::GrammarForest {
      return [0, 0, 0, 0, 1, 7, 9, 17].map(|v| F128::new(v, 0)).to_vec();
    }
    if self == Self::CallRecords {
      return vec![
        F128::ZERO,
        F128::ZERO,
        F128::ZERO,
        F128::new(1, 0),
        F128::new(5, 0),
      ];
    }
    if self == Self::ConstructorRecords {
      return vec![
        F128::ZERO,
        F128::ZERO,
        F128::ZERO,
        F128::new(1, 0),
        F128::new(1, 0),
      ];
    }
    vec![F128::ZERO; self.pins()]
  }
  fn public_words(self) -> usize {
    match self {
      Self::Natural => 71,
      Self::Header => 33,
      Self::HeaderFuel => 41,
      Self::ByteSpan => 7,
      Self::HeaderSpan => 39,
      Self::Record(_) => 19,
      Self::Link(_) => 12,
      Self::CallRecords => 42,
      Self::ConstructorRecords => 41,
      Self::Grammar(_) => 1 + GRAMMAR_INPUTS + GRAMMAR_STATE_WORDS,
      Self::GrammarProgram => 85,
      Self::GrammarForest => 79,
      Self::Payload => 7,
      Self::NaturalLimit => 36,
      Self::Utf8 => 8,
      Self::GrammarNatural => 123,
      Self::GrammarString => 96,
    }
  }
  fn domain(self) -> &'static [u8] {
    match self {
      Self::Natural => b"ix:ixby:ixbf-nat4096-codec-conformance:v0",
      Self::Header => b"ix:ixby:ixbf-header128-codec-conformance:v0",
      Self::HeaderFuel => b"ix:ixby:ixbf-header-fuel64-conformance:v0",
      Self::ByteSpan => b"ix:ixby:ixbf-byte-span-conformance:v0",
      Self::HeaderSpan => b"ix:ixby:ixbf-header-byte-span-conformance:v0",
      Self::Record(kind) => match kind {
        RecordKind::Metadata => b"ix:ixby:ixbf-record-metadata:v0",
        RecordKind::Count => b"ix:ixby:ixbf-record-count:v0",
        RecordKind::Index => b"ix:ixby:ixbf-record-index:v0",
        RecordKind::Constructor => b"ix:ixby:ixbf-record-constructor:v0",
        RecordKind::Function => b"ix:ixby:ixbf-record-function:v0",
        RecordKind::Block => b"ix:ixby:ixbf-record-block:v0",
        RecordKind::Alternative => b"ix:ixby:ixbf-record-alternative:v0",
        RecordKind::Input => b"ix:ixby:ixbf-record-input:v0",
        RecordKind::Output => b"ix:ixby:ixbf-record-output:v0",
        RecordKind::Value => b"ix:ixby:ixbf-record-value:v0",
        RecordKind::Operand => b"ix:ixby:ixbf-record-operand:v0",
        RecordKind::Scalar => b"ix:ixby:ixbf-record-scalar:v0",
        RecordKind::Operation => b"ix:ixby:ixbf-record-operation:v0",
      },
      Self::Link(kind) => match kind {
        RecordLinkKind::ExactArity => b"ix:ixby:ixbf-record-exact-arity:v0",
        RecordLinkKind::PartialArity => b"ix:ixby:ixbf-record-partial-arity:v0",
        RecordLinkKind::SuccessorFrame => b"ix:ixby:ixbf-record-frame-link:v0",
        RecordLinkKind::ConstructorValue => {
          b"ix:ixby:ixbf-record-constructor-link:v0"
        },
        RecordLinkKind::DistinctConstructors => {
          b"ix:ixby:ixbf-record-distinct-constructors:v0"
        },
      },
      Self::CallRecords => b"ix:ixby:ixbf-decoded-call-link:v0",
      Self::ConstructorRecords => b"ix:ixby:ixbf-decoded-constructor-link:v0",
      Self::Grammar(GrammarKind::Program) => {
        b"ix:ixby:ixbf-program-grammar-step:v0"
      },
      Self::Grammar(GrammarKind::Input) => {
        b"ix:ixby:ixbf-input-grammar-step:v0"
      },
      Self::Grammar(GrammarKind::Output) => {
        b"ix:ixby:ixbf-output-grammar-step:v0"
      },
      Self::GrammarProgram => b"ix:ixby:ixbf-decoded-return-grammar-chain:v0",
      Self::GrammarForest => b"ix:ixby:ixbf-decoded-pap-forest-chain:v0",
      Self::Payload => b"ix:ixby:ixbf-payload-cursor:v0",
      Self::NaturalLimit => b"ix:ixby:ixbf-declared-nat-limit:v0",
      Self::Utf8 => b"ix:ixby:ixbf-utf8-chunk:v0",
      Self::GrammarNatural => b"ix:ixby:ixbf-decoded-natural-grammar-chain:v0",
      Self::GrammarString => b"ix:ixby:ixbf-decoded-string-grammar-chain:v0",
    }
  }
}

enum Driver {
  Natural(NaturalDecodeGate, SlotId),
  Header(HeaderDecodeGate, SlotId),
  Fuel(Fuel64StepGate, SlotId),
  ByteSpan(ByteArraySpanGate, SlotId),
  Record(RecordDecodeGate, SlotId),
  Link(RecordLinkGate, SlotId),
  Grammar(GrammarStepGate, SlotId),
  Payload(PayloadCursorGate, SlotId),
  NaturalLimit(NaturalLimitGate, SlotId),
  Utf8(Utf8ChunkGate, SlotId),
}

impl Driver {
  fn r1cs(&self) -> BlockR1cs {
    match self {
      Self::Natural(gate, _) => gate.r1cs(),
      Self::Header(gate, _) => gate.r1cs(),
      Self::Fuel(gate, _) => gate.r1cs(),
      Self::ByteSpan(gate, _) => gate.r1cs(),
      Self::Record(gate, _) => gate.r1cs(),
      Self::Link(gate, _) => gate.r1cs(),
      Self::Grammar(gate, _) => gate.r1cs(),
      Self::Payload(gate, _) => gate.r1cs(),
      Self::NaturalLimit(gate, _) => gate.r1cs(),
      Self::Utf8(gate, _) => gate.r1cs(),
    }
  }
  fn slot(&self) -> SlotId {
    match self {
      Self::Natural(_, slot)
      | Self::Header(_, slot)
      | Self::Fuel(_, slot)
      | Self::ByteSpan(_, slot)
      | Self::Record(_, slot)
      | Self::Link(_, slot)
      | Self::Grammar(_, slot)
      | Self::Payload(_, slot)
      | Self::NaturalLimit(_, slot)
      | Self::Utf8(_, slot) => *slot,
    }
  }
  fn prover<'a>(
    &'a self,
    witness: &'a CircuitWitness,
    circuit: &'a dyn LincheckCircuit,
    substitute: bool,
  ) -> UnionSlotProverInput<'a> {
    match self {
      Self::Payload(gate, slot) => {
        let mut rows = witness.rows::<PayloadCursorGate>(*slot).to_vec();
        if substitute {
          rows[0].0[0].hi += 1;
          assert_eq!(payload::evaluate(&rows[0].0).last(), Some(&F128::ZERO));
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          circuit,
        )
      },
      Self::NaturalLimit(gate, slot) => {
        let mut rows = witness.rows::<NaturalLimitGate>(*slot).to_vec();
        if substitute {
          let original = natural_limit::evaluate(gate.capacity(), &rows[0].0);
          // Same magnitude, bit length and every grammar endpoint. Only the
          // link to the actual decoded program limit is substituted.
          rows[0].0[0].lo += 1;
          assert_eq!(
            natural_limit::evaluate(gate.capacity(), &rows[0].0),
            original
          );
          assert_eq!(original.last(), Some(&F128::ZERO));
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          circuit,
        )
      },
      Self::Utf8(gate, slot) => {
        let mut rows = witness.rows::<Utf8ChunkGate>(*slot).to_vec();
        if substitute {
          let index = rows.len() - 1;
          let original = utf8::evaluate(&rows[index].0);
          if rows.len() == 2 {
            let first = rows[0].0;
            assert_eq!(rows[1].0[1].hi, 6); // First chunk ends in F0.
            rows[1].0[1].hi = 3; // Locally valid, but not the carried DFA wire.
            assert_eq!(rows[0].0, first);
          } else {
            rows[0].0[3].lo ^= 1; // Different ASCII; same local endpoints.
          }
          assert_eq!(utf8::evaluate(&rows[index].0), original);
          assert_eq!(original.last(), Some(&F128::ZERO));
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          circuit,
        )
      },
      Self::Grammar(gate, slot) => {
        let mut rows = witness.rows::<GrammarStepGate>(*slot).to_vec();
        if substitute {
          let endpoints = (rows.first().unwrap().0, rows.last().unwrap().0);
          // In a chain, alter an interior row only. Both endpoint rows and
          // every external/public source word stay unchanged: rejection must
          // involve the internal decoder/state wiring, not just a new final
          // public endpoint. A standalone component has only one row.
          let selected = usize::from(rows.len() > 2);
          let row = &mut rows[selected].0;
          if gate.kind() == GrammarKind::Program && row[1].lo & 255 == 0 {
            // A different decoded header fuel is locally legal but cannot
            // replace the externally expected input or the real decoder wire.
            row[GRAMMAR_STATE_WORDS + 4 + 10].lo ^= 1;
          } else {
            // Recompute a transition using a different carried context word.
            // Local validity survives; complete state continuity does not.
            row[grammar::FUEL].lo ^= 1;
          }
          assert!(grammar_reference_tests::step(gate.kind(), row).is_ok());
          assert_eq!(
            crate::ixby::bits::evaluate_words(
              gate.plan(),
              row,
              GRAMMAR_STATE_WORDS + 1
            )
            .last(),
            Some(&F128::ZERO)
          );
          if rows.len() > 2 {
            assert_eq!(rows.first().unwrap().0, endpoints.0);
            assert_eq!(rows.last().unwrap().0, endpoints.1);
          }
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          circuit,
        )
      },
      Self::Natural(gate, slot) => {
        let mut rows = witness.rows::<NaturalDecodeGate>(*slot).to_vec();
        if substitute {
          rows[0].0[1].lo ^= 1;
          assert_eq!(
            natural::evaluate(gate.capacity(), &rows[0].0).last(),
            Some(&F128::ZERO)
          );
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          circuit,
        )
      },
      Self::Header(gate, slot) => {
        let mut rows = witness.rows::<HeaderDecodeGate>(*slot).to_vec();
        if substitute {
          rows[0].0[0].lo += 1;
          assert_eq!(header::evaluate(&rows[0].0).last(), Some(&F128::ZERO));
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          circuit,
        )
      },
      Self::Fuel(gate, slot) => {
        let mut rows = witness.rows::<Fuel64StepGate>(*slot).to_vec();
        if substitute {
          // Locally valid fuel with a different budget must not replace the
          // header-derived budget, even with all row advice recomputed.
          let budget = F128::new(17_000_000_000, 0);
          let mut output = Vec::new();
          rows[0] = gate.eval(&[budget, F128::ZERO, budget], &(), &mut output);
          assert_eq!(output.last(), Some(&F128::ZERO));
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          circuit,
        )
      },
      Self::ByteSpan(gate, slot) => {
        let mut rows = witness.rows::<ByteArraySpanGate>(*slot).to_vec();
        if substitute {
          // Keep the scalar and its endpoints locally valid, but substitute
          // a more permissive limit in place of the header/public limit wire.
          rows[0].0[1].lo |= 1 << 32;
          assert_eq!(byte_span::evaluate(&rows[0].0).last(), Some(&F128::ZERO));
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          circuit,
        )
      },
      Self::Record(gate, slot) => {
        let mut rows = witness.rows::<RecordDecodeGate>(*slot).to_vec();
        if substitute {
          rows[0].0[0].hi += 1;
          assert_eq!(
            record::evaluate(gate.kind(), &rows[0].0).last(),
            Some(&F128::ZERO)
          );
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          circuit,
        )
      },
      Self::Link(gate, slot) => {
        let mut rows = witness.rows::<RecordLinkGate>(*slot).to_vec();
        if substitute {
          // Change both sides consistently: the local metadata relation
          // remains valid, but the rows no longer use the decoded records.
          let pair = if gate.kind() == RecordLinkKind::ExactArity {
            (2, 7)
          } else {
            (1, 6)
          };
          rows[0].0[pair.0].lo ^= 1;
          rows[0].0[pair.1].lo ^= 1;
          assert_eq!(link::evaluate(gate.kind(), &rows[0].0), F128::ZERO);
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          circuit,
        )
      },
    }
  }
}

struct Setup {
  shape: CircuitShape,
  drivers: Vec<Driver>,
  tables: Vec<BlockR1cs>,
}

// These two fixed conformance shapes are image-independent within their
// particular small grammar schedules. They are not a generic full-image
// admission factory and do not authenticate arbitrary source windows.
fn grammar_program_setup(b: &mut ShapeBuilder, nu: usize) -> Vec<Driver> {
  let grammar_gate = GrammarStepGate::new(nu, GrammarKind::Program).unwrap();
  let grammar = GrammarStepSlot::declare(b, grammar_gate.clone());
  let header_gate = HeaderDecodeGate::new(nu).unwrap();
  let header_slot = HeaderDecodeSlot::declare(b, header_gate.clone());
  let records = [
    RecordKind::Count,
    RecordKind::Function,
    RecordKind::Block,
    RecordKind::Operand,
  ]
  .map(|kind| {
    let gate = RecordDecodeGate::new(nu, kind).unwrap();
    let slot = RecordDecodeSlot::declare(b, gate.clone());
    (gate, slot)
  });
  // Data constants must not alias residual pins: otherwise a gate's zero
  // output would also become its own input in the circuit DAG.
  let zero = b.fixed_public_input(F128::ZERO);
  let one = b.fixed_public_input(F128::new(1, 0));
  let tags = [
    GrammarEvent::Header,
    GrammarEvent::Record(RecordKind::Count),
    GrammarEvent::Record(RecordKind::Function),
    GrammarEvent::Record(RecordKind::Block),
    GrammarEvent::Record(RecordKind::Operand),
    GrammarEvent::Done,
  ]
  .map(|event| b.fixed_public_input(F128::new(event.tag().into(), 0)));
  let length = b.public_input();
  let mut initial = [zero; GRAMMAR_STATE_WORDS];
  initial[0] = b.public_input();
  let prefix =
    (0..HEADER_PREFIX_WORDS).map(|_| b.public_input()).collect::<Vec<_>>();
  let header = header_slot.decode(b, length, &prefix);
  let fields = header
    .limits
    .into_iter()
    .chain([header.max_steps, header.entry, header.constructor_count])
    .collect::<Vec<_>>()
    .try_into()
    .unwrap();
  let mut state = grammar.step(
    b,
    GrammarState(initial),
    tags[0],
    [length, zero, zero],
    fields,
    header.constructors_offset,
  );
  for (index, (_, slot)) in records.iter().enumerate() {
    let bounds = match index {
      0 => [state.0[grammar::LIMITS], zero, zero],
      1 => [
        state.0[grammar::LIMITS + 4],
        state.0[grammar::LIMITS + 3],
        state.0[grammar::LIMITS + 2],
      ],
      2 => [state.0[grammar::LIMITS + 3], zero, zero],
      3 => [state.0[grammar::LOCALS], zero, zero],
      _ => unreachable!(),
    };
    let bytes = std::array::from_fn(|_| b.public_input());
    let record = slot.decode(b, state.0[0], one, bounds, bytes);
    let mut fields = [zero; GRAMMAR_EVENT_FIELDS];
    fields[..RECORD_FIELDS].copy_from_slice(&record.fields);
    state =
      grammar.step(b, state, tags[index + 1], bounds, fields, record.next);
  }
  state = grammar.step(
    b,
    state,
    tags[5],
    [zero; 3],
    [zero; GRAMMAR_EVENT_FIELDS],
    state.0[0],
  );
  for value in state.0 {
    b.publish(value);
  }
  let mut drivers = vec![
    Driver::Grammar(grammar_gate, grammar.slot()),
    Driver::Header(header_gate, header_slot.slot()),
  ];
  drivers.extend(
    records.into_iter().map(|(gate, slot)| Driver::Record(gate, slot.slot())),
  );
  drivers
}

fn forest_context_word(index: usize) -> bool {
  index == 0
    || index == grammar::CTORS
    || index == grammar::FUNCTIONS
    || (grammar::LIMITS..=grammar::ENTRY_ARITY).contains(&index)
    || index == grammar::FUEL
}

fn grammar_forest_setup(b: &mut ShapeBuilder, nu: usize) -> Vec<Driver> {
  let grammar_gate = GrammarStepGate::new(nu, GrammarKind::Input).unwrap();
  let grammar = GrammarStepSlot::declare(b, grammar_gate.clone());
  let input_gate = RecordDecodeGate::new(nu, RecordKind::Input).unwrap();
  let input_slot = RecordDecodeSlot::declare(b, input_gate.clone());
  let value_gate = RecordDecodeGate::new(nu, RecordKind::Value).unwrap();
  let value_slot = RecordDecodeSlot::declare(b, value_gate.clone());
  let zero = b.fixed_public_input(F128::ZERO);
  let one = b.fixed_public_input(F128::new(1, 0));
  let tags = [
    GrammarEvent::Record(RecordKind::Input),
    GrammarEvent::Record(RecordKind::Value),
    GrammarEvent::Done,
  ]
  .map(|event| b.fixed_public_input(F128::new(event.tag().into(), 0)));
  let mut state = GrammarState(std::array::from_fn(|index| {
    if forest_context_word(index) { b.public_input() } else { zero }
  }));
  for index in 0..4 {
    let (slot, tag, bounds) = if index == 0 {
      (
        &input_slot,
        tags[0],
        [
          state.0[grammar::LIMITS + 4],
          state.0[grammar::ENTRY_ARITY],
          state.0[grammar::LIMITS + 6],
        ],
      )
    } else {
      // A supplied word is constrained to nodes_limit - seen - 1 by the
      // grammar relation. It is not a host-approved budget or selector.
      let remaining = b.public_input();
      (
        &value_slot,
        tags[1],
        [state.0[grammar::LIMITS + 4], state.0[grammar::FUNCTIONS], remaining],
      )
    };
    let bytes = std::array::from_fn(|_| b.public_input());
    let record = slot.decode(b, state.0[0], one, bounds, bytes);
    let mut fields = [zero; GRAMMAR_EVENT_FIELDS];
    fields[..RECORD_FIELDS].copy_from_slice(&record.fields);
    state = grammar.step(b, state, tag, bounds, fields, record.next);
  }
  state = grammar.step(
    b,
    state,
    tags[2],
    [zero; 3],
    [zero; GRAMMAR_EVENT_FIELDS],
    state.0[0],
  );
  for value in state.0 {
    b.publish(value);
  }
  vec![
    Driver::Grammar(grammar_gate, grammar.slot()),
    Driver::Record(input_gate, input_slot.slot()),
    Driver::Record(value_gate, value_slot.slot()),
  ]
}

// Two more setup-owned schedules: one output scalar Nat, or one nonempty
// output String of at most 64 bytes. The program header is decoded, not the
// whole program. Source authentication and registry ownership remain separate.
fn grammar_scalar_setup(
  b: &mut ShapeBuilder,
  nu: usize,
  string: bool,
) -> Vec<Driver> {
  let grammar_gate = GrammarStepGate::new(nu, GrammarKind::Output).unwrap();
  let grammar = GrammarStepSlot::declare(b, grammar_gate.clone());
  let header_gate = HeaderDecodeGate::new(nu).unwrap();
  let header_slot = HeaderDecodeSlot::declare(b, header_gate.clone());
  let records = [RecordKind::Output, RecordKind::Value, RecordKind::Scalar]
    .map(|kind| {
      let gate = RecordDecodeGate::new(nu, kind).unwrap();
      let slot = RecordDecodeSlot::declare(b, gate.clone());
      (gate, slot)
    });
  let payload_gate = PayloadCursorGate::new(nu).unwrap();
  let payload_slot = PayloadCursorSlot::declare(b, payload_gate.clone());
  let cap = NaturalCapacity::new(4096).unwrap();
  let natural = (!string).then(|| {
    let gate = NaturalDecodeGate::new(nu, cap).unwrap();
    let slot = NaturalDecodeSlot::declare(b, gate.clone());
    let limit_gate = NaturalLimitGate::new(nu, cap).unwrap();
    let limit_slot = NaturalLimitSlot::declare(b, limit_gate.clone());
    (gate, slot, limit_gate, limit_slot)
  });
  let text = string.then(|| {
    let count_gate = RecordDecodeGate::new(nu, RecordKind::Count).unwrap();
    let count = RecordDecodeSlot::declare(b, count_gate.clone());
    let utf8_gate = Utf8ChunkGate::new(nu).unwrap();
    let utf8 = Utf8ChunkSlot::declare(b, utf8_gate.clone());
    (count_gate, count, utf8_gate, utf8)
  });
  let zero = b.fixed_public_input(F128::ZERO);
  let one = b.fixed_public_input(F128::ONE);
  // Distinct from data zero and every residual pin: no output-input alias.
  let final_utf8 = string.then(|| b.fixed_public_input(F128::ZERO));
  let mut events = vec![
    GrammarEvent::Record(RecordKind::Output),
    GrammarEvent::Record(RecordKind::Value),
    GrammarEvent::Record(RecordKind::Scalar),
  ];
  if string {
    events.extend([
      GrammarEvent::Record(RecordKind::Count),
      GrammarEvent::StringPayload,
    ]);
  } else {
    events.push(GrammarEvent::Natural);
  }
  events.push(GrammarEvent::Done);
  let tags: Vec<_> = events
    .iter()
    .map(|event| b.fixed_public_input(F128::new(event.tag().into(), 0)))
    .collect();
  let program_length = b.public_input();
  let prefix: Vec<_> =
    (0..HEADER_PREFIX_WORDS).map(|_| b.public_input()).collect();
  let header = header_slot.decode(b, program_length, &prefix);
  let mut state = GrammarState([zero; GRAMMAR_STATE_WORDS]);
  state.0[0] = b.public_input();
  state.0[grammar::CTORS] = header.constructor_count;
  state.0[grammar::FUNCTIONS] = b.public_input();
  state.0[grammar::LIMITS..grammar::LIMITS + 10]
    .copy_from_slice(&header.limits);
  state.0[grammar::ENTRY] = header.entry;
  state.0[grammar::ENTRY_ARITY] = b.public_input();
  state.0[grammar::FUEL] = header.max_steps;
  for (index, (_, slot)) in records.iter().enumerate() {
    let bounds = match index {
      0 => [state.0[grammar::LIMITS + 6], zero, zero],
      1 => [
        state.0[grammar::LIMITS + 4],
        state.0[grammar::FUNCTIONS],
        b.public_input(),
      ],
      2 => [zero; 3],
      _ => unreachable!(),
    };
    let bytes = std::array::from_fn(|_| b.public_input());
    let record = slot.decode(b, state.0[0], one, bounds, bytes);
    let mut fields = [zero; GRAMMAR_EVENT_FIELDS];
    fields[..RECORD_FIELDS].copy_from_slice(&record.fields);
    state = grammar.step(b, state, tags[index], bounds, fields, record.next);
  }
  let mut drivers = vec![
    Driver::Grammar(grammar_gate, grammar.slot()),
    Driver::Header(header_gate, header_slot.slot()),
    Driver::Payload(payload_gate, payload_slot.slot()),
  ];
  drivers.extend(
    records.into_iter().map(|(gate, slot)| Driver::Record(gate, slot.slot())),
  );
  let range;
  let mut bits = None;
  if let Some((gate, slot, limit_gate, limit_slot)) = natural {
    let length = b.public_input();
    let payload = payload_slot.advance(b, state.0[0], length, one);
    range = payload.range;
    let encoded: Vec<_> =
      (0..cap.encoded_words()).map(|_| b.public_input()).collect();
    let magnitude = slot.decode(b, payload.natural_control, &encoded);
    bits =
      Some(limit_slot.check(b, state.0[grammar::LIMITS + 7], one, &magnitude));
    let mut fields = [zero; GRAMMAR_EVENT_FIELDS];
    fields[0] = length;
    state = grammar.step(b, state, tags[3], [zero; 3], fields, payload.next);
    drivers.extend([
      Driver::Natural(gate, slot.slot()),
      Driver::NaturalLimit(limit_gate, limit_slot.slot()),
    ]);
  } else {
    let (count_gate, count, utf8_gate, utf8) = text.unwrap();
    let bounds = [state.0[grammar::LIMITS + 8], zero, zero];
    let bytes = std::array::from_fn(|_| b.public_input());
    let record = count.decode(b, state.0[0], one, bounds, bytes);
    let mut fields = [zero; GRAMMAR_EVENT_FIELDS];
    fields[..RECORD_FIELDS].copy_from_slice(&record.fields);
    state = grammar.step(b, state, tags[3], bounds, fields, record.next);
    let payload = payload_slot.advance(b, state.0[0], record.fields[0], one);
    range = payload.range;
    let mut cursor = state.0[0];
    // Count field is already narrow-checked by the cursor packer: its high
    // zero lane also establishes the actual initial ground DFA, with no hint.
    let mut utf8_state = record.fields[0];
    for _ in 0..2 {
      let bytes = [b.public_input(), b.public_input()];
      let chunk = utf8.check(b, cursor, utf8_state, one, bytes);
      cursor = chunk.next;
      utf8_state = chunk.state;
    }
    b.connect(utf8_state, final_utf8.unwrap());
    b.connect(cursor, payload.next);
    state = grammar.step(
      b,
      state,
      tags[4],
      [zero; 3],
      [zero; GRAMMAR_EVENT_FIELDS],
      cursor,
    );
    drivers.extend([
      Driver::Record(count_gate, count.slot()),
      Driver::Utf8(utf8_gate, utf8.slot()),
    ]);
  }
  state = grammar.step(
    b,
    state,
    *tags.last().unwrap(),
    [zero; 3],
    [zero; GRAMMAR_EVENT_FIELDS],
    state.0[0],
  );
  for word in state.0 {
    b.publish(word);
  }
  b.publish(range);
  if let Some(bits) = bits {
    b.publish(bits);
  }
  drivers
}

fn setup(component: Component) -> Setup {
  let nu = component.nu();
  let mut b = ShapeBuilder::new(nu);
  let drivers = match component {
    Component::Payload => {
      let gate = PayloadCursorGate::new(nu).unwrap();
      let slot = PayloadCursorSlot::declare(&mut b, gate.clone());
      let cursor = b.public_input();
      let length = b.public_input();
      let enabled = b.public_input();
      let payload = slot.advance(&mut b, cursor, length, enabled);
      b.publish(payload.natural_control);
      b.publish(payload.range);
      b.publish(payload.next);
      vec![Driver::Payload(gate, slot.slot())]
    },
    Component::NaturalLimit => {
      let cap = NaturalCapacity::new(4096).unwrap();
      let gate = NaturalLimitGate::new(nu, cap).unwrap();
      let slot = NaturalLimitSlot::declare(&mut b, gate.clone());
      let limit = b.public_input();
      let enabled = b.public_input();
      let magnitude: Vec<_> =
        (0..cap.magnitude_words()).map(|_| b.public_input()).collect();
      let length = slot.check(&mut b, limit, enabled, &magnitude);
      b.publish(length);
      vec![Driver::NaturalLimit(gate, slot.slot())]
    },
    Component::Utf8 => {
      let gate = Utf8ChunkGate::new(nu).unwrap();
      let slot = Utf8ChunkSlot::declare(&mut b, gate.clone());
      let cursor = b.public_input();
      let state = b.public_input();
      let enabled = b.public_input();
      let bytes = [b.public_input(), b.public_input()];
      let chunk = slot.check(&mut b, cursor, state, enabled, bytes);
      b.publish(chunk.next);
      b.publish(chunk.state);
      vec![Driver::Utf8(gate, slot.slot())]
    },
    Component::GrammarNatural | Component::GrammarString => {
      grammar_scalar_setup(&mut b, nu, component == Component::GrammarString)
    },
    Component::Grammar(kind) => {
      let gate = GrammarStepGate::new(nu, kind).unwrap();
      let slot = GrammarStepSlot::declare(&mut b, gate.clone());
      let state = GrammarState(std::array::from_fn(|_| b.public_input()));
      let tag = b.public_input();
      let bounds = std::array::from_fn(|_| b.public_input());
      let fields = std::array::from_fn(|_| b.public_input());
      let next = b.public_input();
      let state = slot.step(&mut b, state, tag, bounds, fields, next);
      for value in state.0 {
        b.publish(value);
      }
      vec![Driver::Grammar(gate, slot.slot())]
    },
    Component::GrammarProgram => grammar_program_setup(&mut b, nu),
    Component::GrammarForest => grammar_forest_setup(&mut b, nu),
    Component::Record(kind) => {
      let gate = RecordDecodeGate::new(nu, kind).unwrap();
      let slot = RecordDecodeSlot::declare(&mut b, gate.clone());
      let cursor = b.public_input();
      let enabled = b.public_input();
      let bounds = std::array::from_fn(|_| b.public_input());
      let bytes = std::array::from_fn(|_| b.public_input());
      let record = slot.decode(&mut b, cursor, enabled, bounds, bytes);
      for field in record.fields {
        b.publish(field);
      }
      b.publish(record.next);
      vec![Driver::Record(gate, slot.slot())]
    },
    Component::Link(kind) => {
      let gate = RecordLinkGate::new(nu, kind).unwrap();
      let slot = RecordLinkSlot::declare(&mut b, gate.clone());
      let enabled = b.public_input();
      let left = std::array::from_fn(|_| b.public_input());
      let right = std::array::from_fn(|_| b.public_input());
      slot.check(&mut b, enabled, left, right);
      vec![Driver::Link(gate, slot.slot())]
    },
    Component::CallRecords | Component::ConstructorRecords => {
      let call = component == Component::CallRecords;
      let first_gate = RecordDecodeGate::new(
        nu,
        if call { RecordKind::Function } else { RecordKind::Constructor },
      )
      .unwrap();
      let second_gate = RecordDecodeGate::new(
        nu,
        if call { RecordKind::Operation } else { RecordKind::Value },
      )
      .unwrap();
      let link_gate = RecordLinkGate::new(
        nu,
        if call {
          RecordLinkKind::ExactArity
        } else {
          RecordLinkKind::ConstructorValue
        },
      )
      .unwrap();
      let first = RecordDecodeSlot::declare(&mut b, first_gate.clone());
      let second = RecordDecodeSlot::declare(&mut b, second_gate.clone());
      let link = RecordLinkSlot::declare(&mut b, link_gate.clone());
      let one = b.fixed_public_input(F128::new(1, 0));
      // A distinct fixed wire avoids making a record output its own enable
      // input when the constructor-value tag also equals one.
      let kind = b.fixed_public_input(F128::new(if call { 5 } else { 1 }, 0));
      let mut decode = |slot: &RecordDecodeSlot| {
        let cursor = b.public_input();
        let enabled = b.public_input();
        b.connect(enabled, one);
        let bounds = std::array::from_fn(|_| b.public_input());
        let bytes = std::array::from_fn(|_| b.public_input());
        slot.decode(&mut b, cursor, enabled, bounds, bytes)
      };
      let a = decode(&first);
      let z = decode(&second);
      b.connect(z.fields[0], kind);
      if call {
        let index = b.public_input();
        // These zero fields come from the constrained unused output fields.
        link.check(
          &mut b,
          one,
          [z.fields[2], z.fields[3], a.fields[3], a.fields[4], a.fields[5]],
          [index, a.fields[0], a.fields[3], a.fields[4], a.fields[5]],
        );
      } else {
        link.check(
          &mut b,
          one,
          z.fields[1..6].try_into().unwrap(),
          a.fields[..5].try_into().unwrap(),
        );
      }
      for record in [a, z] {
        for field in record.fields {
          b.publish(field);
        }
        b.publish(record.next);
      }
      vec![
        Driver::Record(first_gate, first.slot()),
        Driver::Record(second_gate, second.slot()),
        Driver::Link(link_gate, link.slot()),
      ]
    },
    Component::Natural => {
      let gate =
        NaturalDecodeGate::new(nu, NaturalCapacity::new(4096).unwrap())
          .unwrap();
      let slot = NaturalDecodeSlot::declare(&mut b, gate.clone());
      let control = b.public_input();
      let bytes: Vec<_> = (0..gate.capacity().encoded_words())
        .map(|_| b.public_input())
        .collect();
      for magnitude in slot.decode(&mut b, control, &bytes) {
        b.publish(magnitude);
      }
      vec![Driver::Natural(gate, slot.slot())]
    },
    Component::ByteSpan => {
      let gate = ByteArraySpanGate::new(nu).unwrap();
      let slot = ByteArraySpanSlot::declare(&mut b, gate.clone());
      let cursor = b.public_input();
      let limit = b.public_input();
      let lookahead = [b.public_input(), b.public_input()];
      let span = slot.decode(&mut b, cursor, limit, lookahead);
      b.publish(span.range);
      b.publish(span.next);
      vec![Driver::ByteSpan(gate, slot.slot())]
    },
    Component::Header | Component::HeaderFuel | Component::HeaderSpan => {
      let gate = HeaderDecodeGate::new(nu).unwrap();
      let slot = HeaderDecodeSlot::declare(&mut b, gate.clone());
      let fuel = (component == Component::HeaderFuel).then(|| {
        let gate = Fuel64StepGate::new(nu).unwrap();
        let slot = Fuel64StepSlot::declare(&mut b, gate.clone());
        (gate, slot)
      });
      let span = (component == Component::HeaderSpan).then(|| {
        let gate = ByteArraySpanGate::new(nu).unwrap();
        let slot = ByteArraySpanSlot::declare(&mut b, gate.clone());
        (gate, slot)
      });
      let length = b.public_input();
      let prefix: Vec<_> =
        (0..HEADER_PREFIX_WORDS).map(|_| b.public_input()).collect();
      let controls: Vec<_> = (0..if fuel.is_some() { STEPS } else { 0 })
        .map(|_| b.public_input())
        .collect();
      let span_input = span
        .as_ref()
        .map(|_| (b.public_input(), [b.public_input(), b.public_input()]));
      let header = slot.decode(&mut b, length, &prefix);
      for word in header.limits.into_iter().chain([
        header.max_steps,
        header.entry,
        header.constructor_count,
        header.constructors_offset,
      ]) {
        b.publish(word);
      }
      let mut drivers = vec![Driver::Header(gate, slot.slot())];
      if let Some((gate, slot)) = fuel {
        // The same exact wire initializes (remaining, consumed) and supplies
        // the original budget. The fuel constraints enforce its high lane 0.
        let mut state = header.max_steps;
        for control in controls {
          state = slot.step(&mut b, state, control, header.max_steps);
        }
        b.publish(state);
        drivers.push(Driver::Fuel(gate, slot.slot()));
      }
      if let Some((gate, slot)) = span {
        let (cursor, lookahead) = span_input.unwrap();
        let range = slot.decode(&mut b, cursor, header.limits[9], lookahead);
        b.publish(range.range);
        b.publish(range.next);
        drivers.push(Driver::ByteSpan(gate, slot.slot()));
      }
      drivers
    },
  };
  let shape = b.finish().unwrap();
  let mut drivers = drivers;
  drivers.sort_by_key(|driver| shape.registry_slot(driver.slot()));
  for (index, driver) in drivers.iter().enumerate() {
    assert_eq!(shape.registry_slot(driver.slot()), index);
  }
  let tables = drivers.iter().map(Driver::r1cs).collect();
  Setup { shape, drivers, tables }
}

#[derive(Serialize, Deserialize)]
struct Bundle {
  magic: [u8; 8],
  component: u8,
  commitment: Commitment,
  proof: R1csProofCircuitMerged,
}

fn codec() -> impl Options {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .with_little_endian()
    .with_limit(MAX_BYTES)
    .reject_trailing_bytes()
}

fn params(union: &UnionInstance<'_>) -> PcsParams {
  let m = union.dense_m();
  assert!((22..=35).contains(&m), "unchanged pinned PCS geometry");
  let profile = LigeritoProfile::Fast128;
  let log_batch_size = embedded_initial_k_or_default(m, profile);
  PcsParams {
    m,
    profile,
    log_batch_size,
    log_inv_rate: profile.log_inv_rate(),
    num_lanes: union.commit_lanes(log_batch_size),
    merkle_hash: HashKind::Blake3,
  }
}

fn prove(
  component: Component,
  setup: &Setup,
  witness: &CircuitWitness,
  expected: &[F128],
  substitute: bool,
) -> Vec<u8> {
  let inputs = setup
    .drivers
    .iter()
    .enumerate()
    .map(|(index, driver)| {
      let selected = match component {
        Component::HeaderFuel => matches!(driver, Driver::Fuel(_, _)),
        Component::HeaderSpan => matches!(driver, Driver::ByteSpan(_, _)),
        Component::CallRecords | Component::ConstructorRecords => {
          matches!(driver, Driver::Link(_, _))
        },
        Component::GrammarProgram | Component::GrammarForest => {
          matches!(driver, Driver::Grammar(_, _))
        },
        Component::GrammarNatural => {
          matches!(driver, Driver::NaturalLimit(_, _))
        },
        Component::GrammarString => matches!(driver, Driver::Utf8(_, _)),
        _ => index == 0,
      };
      driver.prover(
        witness,
        setup.tables[index].csc_lincheck_circuit(),
        substitute && selected,
      )
    })
    .collect();
  prove_rows(component, setup, expected, inputs)
}

fn prove_rows(
  component: Component,
  setup: &Setup,
  expected: &[F128],
  inputs: Vec<UnionSlotProverInput<'_>>,
) -> Vec<u8> {
  let union =
    UnionInstance::new(&setup.shape.registry, setup.shape.counts.clone());
  let mut challenger = FsChallenger::with_chained_blake3(component.domain());
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &setup.shape.circuit,
    expected,
    &params(&union),
    inputs,
    Vec::new(),
    &mut challenger,
  );
  codec()
    .serialize(&Bundle {
      magic: MAGIC,
      component: component.tag(),
      commitment,
      proof,
    })
    .unwrap()
}

fn verify(
  component: Component,
  expected: &[F128],
  bytes: &[u8],
  domain: &[u8],
) -> Result<()> {
  ensure!(
    expected.len() == component.public_words(),
    "codec public ABI length"
  );
  ensure!(
    expected[..component.pins()] == component.fixed_public(),
    "fixed codec public template"
  );
  ensure!(bytes.len() as u64 <= MAX_BYTES, "codec proof byte limit");
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(
    bundle.magic == MAGIC && bundle.component == component.tag(),
    "codec proof kind or revision"
  );
  ensure!(codec().serialize(&bundle)? == bytes, "noncanonical codec proof");
  let setup = setup(component);
  let union =
    UnionInstance::new(&setup.shape.registry, setup.shape.counts.clone());
  let circuits: Vec<&dyn LincheckCircuit> = setup
    .tables
    .iter()
    .map(|table| table.csc_lincheck_circuit() as &dyn LincheckCircuit)
    .collect();
  let mut challenger = FsChallenger::with_chained_blake3(domain);
  verifier::verify_ligerito_union_circuit(
    &union,
    &setup.shape.circuit,
    expected,
    &circuits,
    &bundle.commitment,
    &bundle.proof,
    &params(&union),
    &mut challenger,
  )
  .map_err(|error| {
    anyhow::anyhow!("functional codec proof rejected: {error:?}")
  })?;
  Ok(())
}

fn isolated(component: Component, expected: &[F128], proof: &[u8]) -> bool {
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args(["--ignored", "--exact", TEST, "--test-threads=1", "--nocapture"])
    .current_dir(std::env::temp_dir())
    .env_clear()
    .env(CHILD, "1")
    .env("RAYON_NUM_THREADS", "4")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();
  let mut input = child.stdin.take().unwrap();
  input.write_all(&[component.tag()]).unwrap();
  for word in expected {
    input.write_all(&word.lo.to_le_bytes()).unwrap();
    input.write_all(&word.hi.to_le_bytes()).unwrap();
  }
  input.write_all(proof).unwrap();
  drop(input);
  let output = child.wait_with_output().unwrap();
  if !output.status.success() {
    eprintln!(
      "fresh functional codec verifier rejected: {}",
      String::from_utf8_lossy(&output.stderr)
    );
  }
  output.status.success()
}

fn child() -> Result<()> {
  let mut input = Vec::new();
  std::io::stdin().take(MAX_BYTES + 4097).read_to_end(&mut input)?;
  let component = Component::from_tag(
    *input.first().ok_or_else(|| anyhow::anyhow!("missing codec component"))?,
  )?;
  let prefix = 1 + 16 * component.public_words();
  ensure!(
    (prefix..=prefix + MAX_BYTES as usize).contains(&input.len()),
    "codec verifier input length"
  );
  let expected: Vec<_> = input[1..prefix]
    .as_chunks::<16>()
    .0
    .iter()
    .map(|word| crate::hash::pack_bytes(word))
    .collect();
  verify(component, &expected, &input[prefix..], component.domain())
}

fn check_fixture(
  component: Component,
  data: &[F128],
  output: &[F128],
  substitute: bool,
) {
  let setup = setup(component);
  let mut input = component.fixed_public();
  input.extend_from_slice(data);
  let mut expected = input.clone();
  expected.extend_from_slice(output);
  assert_eq!(expected.len(), component.public_words());
  let witness = setup.shape.run(&input, &[]);
  assert_eq!(witness.public, expected, "independent public codec endpoints");
  let proof = prove(component, &setup, &witness, &expected, false);
  assert!(isolated(component, &expected, &proof));
  eprintln!(
    "functional codec component {component:?}: {} bytes; public_words={}",
    proof.len(),
    expected.len()
  );
  if substitute {
    // Supply locally valid replacement advice and recompute every derived
    // value; only the original statement and cross-component wiring reject.
    let forged = prove(component, &setup, &witness, &expected, true);
    assert!(!isolated(component, &expected, &forged));
  }
  for index in 0..component.pins() {
    let mut changed = expected.clone();
    changed[index].lo ^= 1;
    assert!(verify(component, &changed, &proof, component.domain()).is_err());
  }
  for word in [component.pins(), expected.len() / 2, expected.len() - 1] {
    for high in [false, true] {
      let mut changed = expected.clone();
      if high {
        changed[word].hi ^= 1 << 32;
      } else {
        changed[word].lo ^= 1 << 32;
      }
      assert!(verify(component, &changed, &proof, component.domain()).is_err());
    }
  }
  let mut trailing = proof.clone();
  trailing.push(0);
  assert!(verify(component, &expected, &trailing, component.domain()).is_err());
  assert!(
    verify(component, &expected, &proof[..proof.len() - 1], component.domain())
      .is_err()
  );
  let mut changed = proof.clone();
  changed[0] ^= 1;
  assert!(verify(component, &expected, &changed, component.domain()).is_err());
  changed = proof.clone();
  changed[8] ^= 1;
  assert!(verify(component, &expected, &changed, component.domain()).is_err());
  assert!(
    verify(component, &expected, &proof, b"ix:ixby:wide-fuel-conformance:v0")
      .is_err()
  );
}

#[test]
fn codec_record_domains_tags_and_fixed_public_templates_are_distinct() {
  let components: Vec<_> = [
    Component::Natural,
    Component::Header,
    Component::HeaderFuel,
    Component::ByteSpan,
    Component::HeaderSpan,
    Component::CallRecords,
    Component::ConstructorRecords,
    Component::GrammarProgram,
    Component::GrammarForest,
    Component::Payload,
    Component::NaturalLimit,
    Component::Utf8,
    Component::GrammarNatural,
    Component::GrammarString,
  ]
  .into_iter()
  .chain(RecordKind::ALL.map(Component::Record))
  .chain(RecordLinkKind::ALL.map(Component::Link))
  .chain(
    [GrammarKind::Program, GrammarKind::Input, GrammarKind::Output]
      .map(Component::Grammar),
  )
  .collect();
  let mut tags = std::collections::BTreeSet::new();
  let mut domains = std::collections::BTreeSet::new();
  for component in &components {
    assert!(tags.insert(component.tag()));
    assert!(domains.insert(component.domain()));
    assert_eq!(Component::from_tag(component.tag()).unwrap(), *component);
    assert_eq!(component.fixed_public().len(), component.pins());
  }
  for tag in 0..=255 {
    assert_eq!(Component::from_tag(tag).is_ok(), tags.contains(&tag));
  }
  // Keep the multi-record DAG construction in the ordinary regression too.
  for component in [
    Component::CallRecords,
    Component::ConstructorRecords,
    Component::GrammarProgram,
    Component::GrammarForest,
    Component::GrammarNatural,
    Component::GrammarString,
  ] {
    let _ = setup(component);
  }
}

const GRAMMAR_IDENTITY: &[u8] = &[
  b'I', b'X', b'B', b'F', 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 8, 0x80,
  0x20, 64, 64, 24, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0,
];

fn grammar_program_fixture() -> (Vec<F128>, Vec<F128>) {
  let source = GRAMMAR_IDENTITY;
  let artifact = crate::ixby::ixbf::decode_program(
    source,
    crate::ixby::ixbf::DecodeLimits::default(),
  )
  .unwrap();
  let prefix = header_tests::input(source, source.len() as u64);
  let decoded = header::evaluate(&prefix);
  assert_eq!(decoded[..14], external_tests::expected_header(&artifact));
  let mut state = [F128::ZERO; GRAMMAR_STATE_WORDS];
  state[0] = F128::new(0, source.len() as u64);
  let mut data = vec![prefix[0], state[0]];
  data.extend_from_slice(&prefix[1..]);
  let mut trace = grammar_tests::Trace::new(GrammarKind::Program, state);
  trace.step(
    GrammarEvent::Header,
    [prefix[0], F128::ZERO, F128::ZERO],
    &decoded[..13],
    decoded[13],
  );
  for (kind, bounds) in [
    (RecordKind::Count, [1, 0, 0]),
    (RecordKind::Function, [1, 1, 1]),
    (RecordKind::Block, [1, 0, 0]),
    (RecordKind::Operand, [1, 0, 0]),
  ] {
    let bounds = bounds.map(|v| F128::new(v, 0));
    let input = record_tests::input(source, trace.state[0].lo as usize, bounds);
    data.extend_from_slice(&input[5..]);
    let decoded = record::evaluate(kind, &input);
    assert_eq!(decoded[RECORD_FIELDS + 1], F128::ZERO);
    trace.step(
      GrammarEvent::Record(kind),
      bounds,
      &decoded[..RECORD_FIELDS],
      decoded[RECORD_FIELDS],
    );
  }
  trace.finish();
  assert_eq!(trace.state[grammar::ENTRY_ARITY], F128::new(1, 0));
  (data, trace.state.to_vec())
}

fn grammar_forest_fixture() -> (Vec<F128>, Vec<F128>) {
  use crate::ixby::ixbf;
  let mut program = GRAMMAR_IDENTITY.to_vec();
  for offset in [15, 16, 27, 30] {
    program[offset] = 2;
  }
  program[18] = 3;
  let artifact =
    ixbf::decode_program(&program, ixbf::DecodeLimits::default()).unwrap();
  let source = b"IXFI\x01\0\0\0\0\0\0\0\x02\x02\0\x01\x03\x03";
  let input_model =
    ixbf::decode_input(&artifact, source, ixbf::DecodeLimits::default())
      .unwrap();
  assert_eq!(input_model.values().roots(), &[0, 2]);
  assert_eq!(input_model.values().nodes()[0].children, vec![1]);
  let mut state = [F128::ZERO; GRAMMAR_STATE_WORDS];
  state[0] = F128::new(0, source.len() as u64);
  state[grammar::FUNCTIONS] = F128::new(1, 0);
  state[grammar::LIMITS..grammar::LIMITS + 10]
    .copy_from_slice(&external_tests::expected_header(&artifact)[..10]);
  state[grammar::ENTRY_ARITY] = F128::new(2, 0);
  state[grammar::FUEL] = F128::new(24, 0);
  let mut data = state
    .iter()
    .enumerate()
    .filter_map(|(index, value)| forest_context_word(index).then_some(*value))
    .collect::<Vec<_>>();
  let mut trace = grammar_tests::Trace::new(GrammarKind::Input, state);
  for index in 0..4 {
    let (kind, bounds) = if index == 0 {
      (RecordKind::Input, [2, 2, 3])
    } else {
      let remaining = 3 - index;
      data.push(F128::new(remaining, 0));
      (RecordKind::Value, [2, 1, remaining])
    };
    let bounds = bounds.map(|v| F128::new(v, 0));
    let input = record_tests::input(source, trace.state[0].lo as usize, bounds);
    data.extend_from_slice(&input[5..]);
    let decoded = record::evaluate(kind, &input);
    assert_eq!(decoded[RECORD_FIELDS + 1], F128::ZERO);
    trace.step(
      GrammarEvent::Record(kind),
      bounds,
      &decoded[..RECORD_FIELDS],
      decoded[RECORD_FIELDS],
    );
  }
  trace.finish();
  assert_eq!(trace.state[grammar::SEEN], F128::new(3, 0));
  (data, trace.state.to_vec())
}

#[test]
fn grammar_decoder_chains_have_independent_endpoints_and_fixed_setup_templates()
{
  for (component, (data, output)) in [
    (Component::GrammarProgram, grammar_program_fixture()),
    (Component::GrammarForest, grammar_forest_fixture()),
  ] {
    let setup = setup(component);
    let mut inputs = component.fixed_public();
    inputs.extend(data);
    let mut expected = inputs.clone();
    expected.extend(output);
    assert_eq!(expected.len(), component.public_words());
    let witness = setup.shape.run(&inputs, &[]);
    assert_eq!(witness.public, expected);
  }
}

fn grammar_scalar_fixture(string: bool) -> (Vec<F128>, Vec<F128>) {
  use crate::ixby::ixbf;
  let old_header = header::evaluate(&header_tests::input(
    GRAMMAR_IDENTITY,
    GRAMMAR_IDENTITY.len() as u64,
  ));
  let mut fields: [u128; HEADER_FIELDS] = old_header[..HEADER_FIELDS]
    .iter()
    .map(|w| u128::from(w.lo) | (u128::from(w.hi) << 64))
    .collect::<Vec<_>>()
    .try_into()
    .unwrap();
  fields[7] = 65;
  fields[8] = 36;
  let program = header_tests::bytes(
    &fields,
    &GRAMMAR_IDENTITY[old_header[13].lo as usize..],
  );
  let artifact =
    ixbf::decode_program(&program, ixbf::DecodeLimits::default()).unwrap();
  let prefix = header_tests::input(&program, program.len() as u64);
  let header = external_tests::expected_header(&artifact);
  let mut source = b"IXFO\x01\0\0\0\0\0\0\0\0".to_vec();
  source.push(u8::from(string));
  let natural = (BigUint::from(1u8) << 64usize) + 17u8;
  let mut text = vec![b'a'; 31];
  text.extend([0xf0, 0x90, 0x80, 0x80, b'z']);
  if string {
    source.push(text.len() as u8);
    source.extend(&text);
  } else {
    source.extend(tests::natural_bytes(&natural));
  }
  let model =
    ixbf::decode_output(&artifact, &source, ixbf::DecodeLimits::default())
      .unwrap();
  assert_eq!(model.values().roots(), &[0]);
  match &model.values().nodes()[0].kind {
    ixbf::ValueKind::Scalar(ixbf::Scalar::Nat(value)) if !string => {
      assert_eq!(value, &natural)
    },
    ixbf::ValueKind::Scalar(ixbf::Scalar::String(value)) if string => {
      assert_eq!(value.as_bytes(), text)
    },
    _ => panic!("independent scalar output fixture"),
  }
  let mut state = [F128::ZERO; GRAMMAR_STATE_WORDS];
  state[0] = F128::new(0, source.len() as u64);
  state[grammar::CTORS] = header[12];
  state[grammar::FUNCTIONS] = F128::ONE;
  state[grammar::LIMITS..grammar::LIMITS + 10].copy_from_slice(&header[..10]);
  state[grammar::ENTRY] = header[11];
  state[grammar::ENTRY_ARITY] = F128::ONE;
  state[grammar::FUEL] = header[10];
  let mut data = prefix;
  data.extend([
    state[0],
    state[grammar::FUNCTIONS],
    state[grammar::ENTRY_ARITY],
  ]);
  let mut trace = grammar_tests::Trace::new(GrammarKind::Output, state);
  for (index, kind) in
    [RecordKind::Output, RecordKind::Value, RecordKind::Scalar]
      .into_iter()
      .enumerate()
  {
    let bounds = match index {
      0 => [header[6], F128::ZERO, F128::ZERO],
      1 => {
        let remaining = F128::new(header[6].lo - 1, 0);
        data.push(remaining);
        [header[4], F128::ONE, remaining]
      },
      2 => [F128::ZERO; 3],
      _ => unreachable!(),
    };
    let input =
      record_tests::input(&source, trace.state[0].lo as usize, bounds);
    data.extend_from_slice(&input[5..]);
    let decoded = record::evaluate(kind, &input);
    assert_eq!(decoded[RECORD_FIELDS + 1], F128::ZERO);
    trace.step(
      GrammarEvent::Record(kind),
      bounds,
      &decoded[..RECORD_FIELDS],
      decoded[RECORD_FIELDS],
    );
  }
  let range;
  if string {
    let bounds = [header[8], F128::ZERO, F128::ZERO];
    let input =
      record_tests::input(&source, trace.state[0].lo as usize, bounds);
    data.extend_from_slice(&input[5..]);
    let decoded = record::evaluate(RecordKind::Count, &input);
    assert_eq!(decoded[0], F128::new(text.len() as u64, 0));
    trace.step(
      GrammarEvent::Record(RecordKind::Count),
      bounds,
      &decoded[..RECORD_FIELDS],
      decoded[RECORD_FIELDS],
    );
    range = F128::new(trace.state[0].lo, text.len() as u64);
    let mut cursor = trace.state[0];
    let mut state = decoded[0];
    for index in 0..2 {
      let input =
        scalar_payload_tests::utf8_input(&source, cursor, state, true);
      data.extend_from_slice(&input[3..]);
      let output = utf8::evaluate(&input);
      assert_eq!(output[2], F128::ZERO);
      cursor = output[0];
      state = output[1];
      if index == 0 {
        assert_eq!(state, F128::new(4, 6));
      }
    }
    assert_eq!(state, F128::ZERO);
    trace.step(GrammarEvent::StringPayload, [F128::ZERO; 3], &[], cursor);
  } else {
    let bytes = tests::natural_bytes(&natural);
    let length = F128::new(bytes.len() as u64, 0);
    range = F128::new(trace.state[0].lo, length.lo);
    data.push(length);
    let gate =
      NaturalDecodeGate::new(3, NaturalCapacity::new(4096).unwrap()).unwrap();
    let input = tests::input(&gate, &bytes, true);
    data.extend_from_slice(&input[1..]);
    trace.step(
      GrammarEvent::Natural,
      [F128::ZERO; 3],
      &[length],
      F128::new(source.len() as u64, source.len() as u64),
    );
  }
  trace.finish();
  let mut output = trace.state.to_vec();
  output.push(range);
  if !string {
    output.push(F128::new(natural.bits(), 0));
  }
  (data, output)
}

#[test]
fn scalar_payload_decoder_chains_have_independent_endpoints_and_fixed_templates()
 {
  for component in [Component::GrammarNatural, Component::GrammarString] {
    let (data, output) =
      grammar_scalar_fixture(component == Component::GrammarString);
    let setup = setup(component);
    let mut input = component.fixed_public();
    input.extend(data);
    let mut expected = input.clone();
    expected.extend(output);
    assert_eq!(expected.len(), component.public_words());
    assert_eq!(setup.shape.run(&input, &[]).public, expected);
  }
}

#[test]
#[ignore = "scalar payload checks and actual decoder/grammar/UTF-8 chains with fresh verifiers and same-endpoint internal substitutions"]
fn scalar_payload_components_and_decoder_chains_verify_in_isolation() {
  let payload = [F128::new(7, 10), F128::new(3, 0), F128::ONE];
  check_fixture(
    Component::Payload,
    &payload,
    &payload::evaluate(&payload)[..3],
    true,
  );
  let cap = NaturalCapacity::new(4096).unwrap();
  let value = (BigUint::from(1u8) << 64usize) + 17u8;
  let mut input = vec![F128::new(65, 0), F128::ONE];
  input.extend(scalar_payload_tests::magnitude(&value, cap));
  check_fixture(
    Component::NaturalLimit,
    &input,
    &[F128::new(value.bits(), 0)],
    true,
  );
  let input = scalar_payload_tests::utf8_input(
    b"good",
    F128::new(0, 4),
    F128::new(4, 0),
    true,
  );
  check_fixture(Component::Utf8, &input, &[F128::new(4, 4), F128::ZERO], true);
  for component in [Component::GrammarNatural, Component::GrammarString] {
    let (data, output) =
      grammar_scalar_fixture(component == Component::GrammarString);
    check_fixture(component, &data, &output, true);
  }
}

#[test]
#[ignore = "Flock grammar-control components and complete small decoder/state chains with fresh verifiers and recomputed state substitutions"]
fn grammar_control_and_decoder_chains_verify_in_isolation() {
  for kind in [GrammarKind::Program, GrammarKind::Input, GrammarKind::Output] {
    let input = grammar_tests::fixture(kind);
    let output = grammar_reference_tests::step(kind, &input).unwrap();
    check_fixture(Component::Grammar(kind), &input, &output, true);
  }
  let (data, output) = grammar_program_fixture();
  check_fixture(Component::GrammarProgram, &data, &output, true);
  let (data, output) = grammar_forest_fixture();
  check_fixture(Component::GrammarForest, &data, &output, true);
}

#[test]
#[ignore = "real body-record and semantic-link Flock component proofs with isolated verifiers and recomputed substitutions"]
fn record_component_proofs_verify_in_isolation_and_reject_recomputed_advice() {
  for kind in RecordKind::ALL {
    let fixture = record_tests::fixture(kind);
    let input = record_tests::input(&fixture.bytes, 0, fixture.bounds);
    let mut output = fixture.fields.to_vec();
    output.push(F128::new(fixture.consumed as u64, fixture.bytes.len() as u64));
    check_fixture(Component::Record(kind), &input, &output, true);
  }
  for kind in RecordLinkKind::ALL {
    check_fixture(Component::Link(kind), &link_tests::fixture(kind), &[], true);
  }
  let mut input = [F128::ZERO; RECORD_INPUTS];
  input[0] = F128::new(17, 23);
  input[2..5].copy_from_slice(&[
    F128::new(8, 0),
    F128::new(10, 0),
    F128::new(7, 0),
  ]);
  let mut output = vec![F128::ZERO; RECORD_FIELDS];
  output.push(input[0]);
  check_fixture(Component::Record(RecordKind::Value), &input, &output, false);
}

#[test]
#[ignore = "cross-record Flock proofs binding decoded call/constructor fields directly to semantic consumers"]
fn decoded_records_feed_call_and_constructor_checks_without_host_replacement() {
  let function = record_tests::fixture(RecordKind::Function);
  let function_input = record_tests::input(&function.bytes, 0, function.bounds);
  let call = [5, 7, 3, 2, 2, 2];
  let call_input = record_tests::input(
    &call,
    0,
    [F128::new(8, 0), F128::new(4, 0), F128::new(10, 0)],
  );
  let mut input = function_input.to_vec();
  input.extend(call_input);
  input.push(F128::new(7, 0));
  let mut output = function.fields.to_vec();
  output.push(F128::new(function.consumed as u64, function.bytes.len() as u64));
  output.extend([5, 0, 7, 3, 0, 0].map(|value| F128::new(value, 0)));
  output.push(F128::new(3, call.len() as u64));
  check_fixture(Component::CallRecords, &input, &output, true);
  let constructor = record_tests::fixture(RecordKind::Constructor);
  let constructor_input =
    record_tests::input(&constructor.bytes, 0, constructor.bounds);
  let mut value = vec![1];
  value.extend(&constructor.bytes[..constructor.consumed]);
  value.extend([3, 3, 3]);
  let value_input = record_tests::input(
    &value,
    0,
    [F128::new(8, 0), F128::new(10, 0), F128::new(7, 0)],
  );
  let mut input = constructor_input.to_vec();
  input.extend(value_input);
  let mut output = constructor.fields.to_vec();
  output.push(F128::new(
    constructor.consumed as u64,
    constructor.bytes.len() as u64,
  ));
  output.push(F128::new(1, 0));
  output.extend(&constructor.fields[..5]);
  output.push(F128::new((constructor.consumed + 1) as u64, value.len() as u64));
  check_fixture(Component::ConstructorRecords, &input, &output, true);
}

#[test]
#[ignore = "requires the exact retained Init image for an original decoded call/callee arity-link proof"]
fn retained_init_call_and_callee_records_verify_in_isolation() {
  use crate::ixby::ixbf::{self, Instruction, Operation};
  let bytes =
    external_tests::read(&external_tests::path("IXBY_IXBF_STAGE2_IMAGE"));
  assert_eq!(
    blake3::hash(&bytes).to_hex().as_str(),
    "a661dfede7c18bfb915d031393ffb258e65c21940d48039cdf44ab16428fe301"
  );
  let artifact =
    ixbf::decode_program(&bytes, ixbf::DecodeLimits::default()).unwrap();
  let (block, target, args) = artifact
    .functions()
    .iter()
    .flat_map(|function| &function.blocks)
    .find_map(|block| match &block.instruction {
      Instruction::Let(Operation::Call(target, args), _) => {
        Some((block, *target, args))
      },
      _ => None,
    })
    .unwrap();
  let callee = &artifact.functions()[target];
  let header_values = [
    &callee.arity,
    &BigUint::from(callee.entry),
    &BigUint::from(callee.blocks.len()),
  ];
  let function_start = callee.blocks[0].encoded.start
    - header_values
      .iter()
      .map(|value| tests::natural_bytes(value).len())
      .sum::<usize>();
  let call_start =
    block.encoded.start + tests::natural_bytes(&block.locals).len() + 1;
  let call_end = call_start
    + 1
    + tests::natural_bytes(&BigUint::from(target)).len()
    + tests::natural_bytes(&BigUint::from(args.len())).len();
  let limits = artifact.limits();
  let first = record_tests::input(
    &bytes,
    function_start,
    [&limits.operands, &limits.locals, &limits.blocks]
      .map(external_tests::word),
  );
  let second = record_tests::input(
    &bytes,
    call_start,
    [
      external_tests::word(&limits.operands),
      F128::new(artifact.constructors().len() as u64, 0),
      F128::new(artifact.functions().len() as u64, 0),
    ],
  );
  let mut input = first.to_vec();
  input.extend(second);
  input.push(F128::new(target as u64, 0));
  let mut output = header_values.map(external_tests::word).to_vec();
  output.extend([F128::ZERO; 3]);
  output
    .push(F128::new(callee.blocks[0].encoded.start as u64, bytes.len() as u64));
  output.extend(
    [5, 0, target as u64, args.len() as u64, 0, 0]
      .map(|value| F128::new(value, 0)),
  );
  output.push(F128::new(call_end as u64, bytes.len() as u64));
  check_fixture(Component::CallRecords, &input, &output, true);
  eprintln!(
    "exact Init call at {call_start}, callee {target} at {function_start}, {} arguments: decoded-record wiring proof passed; source membership, registry ownership and full execution remain unproved",
    args.len()
  );
}

#[test]
#[ignore = "real functional codec and header-derived fuel proofs, fresh verifier and recomputed row substitutions"]
fn functional_codec_proofs_verify_in_fresh_process_and_reject_recomputed_substitutions()
 {
  if std::env::var_os(CHILD).is_some() {
    child().unwrap();
    return;
  }
  let gate =
    NaturalDecodeGate::new(7, NaturalCapacity::new(4096).unwrap()).unwrap();
  for (index, value) in [
    BigUint::from(0u8),
    (BigUint::from(1u8) << 64usize) + 17u8,
    (BigUint::from(1u8) << 4096usize) - 1u8,
  ]
  .iter()
  .enumerate()
  {
    let input = tests::input(&gate, &tests::natural_bytes(value), true);
    let mut magnitude = value.to_bytes_le();
    magnitude.resize(512, 0);
    let output: Vec<_> = magnitude
      .as_chunks::<16>()
      .0
      .iter()
      .map(|word| crate::hash::pack_bytes(word))
      .collect();
    check_fixture(Component::Natural, &input, &output, index == 0);
  }
  let (fields, data) = header_tests::fixture();
  let input = header_tests::input(&data, data.len() as u64);
  let mut output: Vec<_> = fields
    .iter()
    .map(|value| F128::new(*value as u64, (value >> 64) as u64))
    .collect();
  output.push(F128::new((data.len() - 5) as u64, 0));
  check_fixture(Component::Header, &input, &output, true);
  for budget in [16_000_000_000, u64::MAX] {
    let mut fields = fields;
    fields[10] = u128::from(budget);
    fields[11] = 680;
    let data = header_tests::bytes(&fields, &[3; 5]);
    let mut input = header_tests::input(&data, data.len() as u64);
    input.extend([0, 1, 3, 0, 1, 2].map(|kind| F128::new(kind, 0)));
    let mut output: Vec<_> = fields
      .iter()
      .map(|value| F128::new(*value as u64, (value >> 64) as u64))
      .collect();
    output.push(F128::new((data.len() - 5) as u64, 0));
    output.push(F128::new(budget - 5, 5));
    check_fixture(
      Component::HeaderFuel,
      &input,
      &output,
      budget == 16_000_000_000,
    );
  }
  let small = byte_span_tests::input(&[6, 3, 7, 8, 9], 0, F128::new(3, 0));
  check_fixture(
    Component::ByteSpan,
    &small,
    &[F128::new(2, 3), F128::new(5, 5)],
    true,
  );
  // This wide-range fixture is not an authenticated copy of the real Init
  // proof. Only a fixed, synthetic lookahead is supplied here.
  let mut scalar = vec![6];
  scalar.extend(tests::natural_bytes(&BigUint::from(9_611_064u64)));
  scalar.resize(32, 0);
  let mut span = byte_span_tests::input(&scalar, 0, F128::new(16_777_216, 0));
  span[0] = F128::new(51, 9_611_120);
  let span_output = [F128::new(56, 9_611_064), F128::new(9_611_120, 9_611_120)];
  check_fixture(Component::ByteSpan, &span, &span_output, false);
  let mut input = header_tests::input(&data, data.len() as u64);
  input.extend([span[0], span[2], span[3]]);
  let mut output: Vec<_> = fields
    .iter()
    .map(|value| F128::new(*value as u64, (value >> 64) as u64))
    .collect();
  output.push(F128::new((data.len() - 5) as u64, 0));
  output.extend(span_output);
  check_fixture(Component::HeaderSpan, &input, &output, true);
}

#[test]
#[ignore = "real negative Flock proof for a header budget exceeding the u64 ledger class"]
fn header_derived_fuel_rejects_budgets_wider_than_u64() {
  let setup = setup(Component::HeaderFuel);
  let (fields, data) = header_tests::fixture();
  let header_input = header_tests::input(&data, data.len() as u64);
  let Driver::Header(header_gate, _) = &setup.drivers[0] else {
    unreachable!()
  };
  let Driver::Fuel(fuel_gate, _) = &setup.drivers[1] else { unreachable!() };
  let header_rows = [HeaderDecodeRow(header_input.clone())];
  let mut header_output = header::evaluate(&header_input);
  assert_eq!(header_output.pop(), Some(F128::ZERO));
  // Header decoding itself accepts the exact 71-bit maxSteps; the u64 ledger
  // does not silently reinterpret its upper lane as pre-consumed steps.
  let budget = F128::new(fields[10] as u64, (fields[10] >> 64) as u64);
  assert_eq!(header_output[10], budget);
  let mut state = budget;
  let mut fuel_rows = Vec::new();
  for _ in 0..STEPS {
    let mut output = Vec::new();
    fuel_rows.push(fuel_gate.eval(
      &[state, F128::ZERO, budget],
      &(),
      &mut output,
    ));
    state = output[0];
    assert_eq!(output[1], F128::new(1, 0));
  }
  // Bypass the honest builder's early copy-constraint assertion. A malicious
  // prover may supply any advice, so rejection must also hold in verification.
  let mut expected = vec![F128::ZERO; 2];
  expected.extend(header_input);
  expected.extend([F128::ZERO; STEPS]);
  expected.extend(header_output);
  expected.push(state);
  let inputs = vec![
    UnionSlotProverInput::in_place(
      |dst| header_gate.generate_witness_into(&header_rows, dst),
      setup.tables[0].csc_lincheck_circuit(),
    ),
    UnionSlotProverInput::in_place(
      |dst| fuel_gate.generate_witness_into(&fuel_rows, dst),
      setup.tables[1].csc_lincheck_circuit(),
    ),
  ];
  let proof = prove_rows(Component::HeaderFuel, &setup, &expected, inputs);
  assert!(!isolated(Component::HeaderFuel, &expected, &proof));
}

#[test]
#[ignore = "requires the exact retained Init image for real prefix and header-derived budget proofs"]
fn retained_init_prefix_and_decoded_budget_verify_in_isolation() {
  let bytes =
    external_tests::read(&external_tests::path("IXBY_IXBF_STAGE2_IMAGE"));
  assert_eq!(
    blake3::hash(&bytes).to_hex().as_str(),
    "a661dfede7c18bfb915d031393ffb258e65c21940d48039cdf44ab16428fe301"
  );
  let artifact = crate::ixby::ixbf::decode_program(
    &bytes,
    crate::ixby::ixbf::DecodeLimits::default(),
  )
  .unwrap();
  let mut input = header_tests::input(&bytes, bytes.len() as u64);
  let mut output = external_tests::expected_header(&artifact);
  assert_eq!(output[10], F128::new(16_000_000_000, 0));
  check_fixture(Component::Header, &input, &output, false);
  input.extend([0, 1, 3, 0, 1, 2].map(|kind| F128::new(kind, 0)));
  output.push(F128::new(16_000_000_000 - 5, 5));
  check_fixture(Component::HeaderFuel, &input, &output, false);
  eprintln!(
    "real Init prefix and decoded budget component proofs passed; the rest of the program and execution are not proved"
  );
}

#[test]
#[ignore = "requires exact Init program and transports for program-limit-bound ByteArray range proofs"]
fn retained_init_byte_spans_and_program_limit_verify_in_isolation() {
  use crate::ixby::ixbf;
  let program =
    external_tests::read(&external_tests::path("IXBY_IXBF_STAGE2_IMAGE"));
  assert_eq!(
    blake3::hash(&program).to_hex().as_str(),
    "a661dfede7c18bfb915d031393ffb258e65c21940d48039cdf44ab16428fe301"
  );
  let artifact =
    ixbf::decode_program(&program, ixbf::DecodeLimits::default()).unwrap();
  let input =
    external_tests::read(&external_tests::path("IXBY_IXBF_INIT_INPUT"));
  let output =
    external_tests::read(&external_tests::path("IXBY_IXBF_INIT_OUTPUT"));
  assert_eq!(
    blake3::hash(&input).to_hex().as_str(),
    "713a6a0b72dbaad673192c38c6e10115b1386482394cc22a945837c1a03f11c8"
  );
  assert_eq!(
    blake3::hash(&output).to_hex().as_str(),
    "3e6cb8264cfb6d253c41f22aa05221805a58f857d73877305adfed0781115a28"
  );
  let input_values =
    ixbf::decode_input(&artifact, &input, ixbf::DecodeLimits::default())
      .unwrap();
  let output_values =
    ixbf::decode_output(&artifact, &output, ixbf::DecodeLimits::default())
      .unwrap();
  let gate = ByteArraySpanGate::new(3).unwrap();
  let r1cs = gate.r1cs();
  for (source, forest) in
    [(&input, input_values.values()), (&output, output_values.values())]
  {
    for node in forest.nodes() {
      let ixbf::ValueKind::Scalar(ixbf::Scalar::Bytes(payload)) = node.kind
      else {
        panic!("exact Init ByteArray value")
      };
      let (span, endpoints) = external_tests::check_span(
        &gate,
        &r1cs,
        source,
        payload,
        &artifact.limits().byte_array_bytes,
      );
      let mut input = header_tests::input(&program, program.len() as u64);
      input.extend([span[0], span[2], span[3]]);
      let mut output = external_tests::expected_header(&artifact);
      output.extend(endpoints);
      check_fixture(Component::HeaderSpan, &input, &output, false);
    }
  }
  eprintln!(
    "real Init range/declared-limit component proofs passed; full payload authentication and execution are not proved"
  );
}
