use super::*;
use crate::{
  hash::pack_bytes,
  ixby::{
    auth_memory::{MemoryDepth, SparseMemory},
    bounded_hash::BoundedBlake3,
    io::{InputLayout, LayoutEmitter, PublicLayout},
    ixbf_decode::{
      dispatch::DISPATCH_CONTEXT_INDICES,
      grammar,
      paged::{finalize::FinalizeSlots, initialize::InitializeSlots},
    },
    select::{SelectWordsGate, SelectWordsSlot},
  },
  sizing::CircuitEmitter,
};
use flock_prover::circuit::builder::{SlotId, Wire};

pub(super) struct Emission {
  pub gates: Vec<(SlotId, EndpointGate)>,
  pub initialize: InitializeSlots,
  pub finalize: FinalizeSlots,
  pub hashes: [BoundedBlake3; 2],
  pub publish_gate: (SlotId, SelectWordsGate),
  pub inputs: InputLayout,
  pub public: PublicLayout,
}
fn join(b: &mut impl CircuitEmitter, a: &[Wire], c: &[Wire]) {
  assert_eq!(a.len(), c.len());
  for (&a, &c) in a.iter().zip(c) {
    b.connect(a, c);
  }
}
fn zeroes(b: &mut impl CircuitEmitter, values: &[Wire], zero: Wire) {
  for &w in values {
    b.connect(w, zero);
  }
}
fn check(
  b: &mut impl CircuitEmitter,
  gate: SlotId,
  input: [Wire; 4],
  zero: Wire,
) {
  let residual = b.gate(gate, &input)[0];
  b.connect(residual, zero);
}
pub(super) fn emit(
  b: &mut impl CircuitEmitter,
  profile: &FunctionalProfile,
) -> Result<Emission> {
  use Component::*;
  let mut b = LayoutEmitter::new(b);
  let zero = b.fixed_public_input(F128::ZERO);
  let gates: Vec<_> = [
    EndpointOp::Parser,
    EndpointOp::Source,
    EndpointOp::Bridge,
    EndpointOp::Bytes,
    EndpointOp::References,
    EndpointOp::Clock,
  ]
  .into_iter()
  .map(|op| {
    let gate = EndpointGate::new(NU, op).unwrap();
    (b.slot(gate.clone()), gate)
  })
  .collect();
  let initialize = InitializeSlots::declare(&mut b, NU)?;
  let finalize = FinalizeSlots::declare(&mut b, NU)?;
  let profile_hash = BoundedBlake3::declare(&mut b, NU, 200)?;
  let statement_hash = profile_hash.sharing_primitives(&mut b, 144)?;
  let publish_gate = SelectWordsGate::new(NU, 32)?;
  let publish_slot = SelectWordsSlot::declare(&mut b, publish_gate.clone());
  let one = b.fixed_public_input(F128::ONE);
  let mut message = b"IxBy/commit/v0\0\0".to_vec();
  message.extend(profile.encode());
  message.resize(profile_hash.padded_words() * 16, 0);
  let message: Vec<_> = message
    .as_chunks::<16>()
    .0
    .iter()
    .map(|w| b.fixed_public_input(pack_bytes(w)))
    .collect();
  let length = b.fixed_public_input(F128::new(200, 0));
  let p = profile_hash.hash(&mut b, length, &message);
  let facts: Vec<_> = (0..FACT_WORDS).map(|_| b.input()).collect();
  let get = |c: Component| &facts[c.range()];
  let raw_p = get(ProgramBytes);
  let code = get(CodeCapture);
  let references = get(References);
  let ids = get(ConstructorIds);
  let raw_i = get(InputBytes);
  let input = get(InputCapture);
  let exec = get(Execution);
  let output = get(OutputBytes);
  let context = DISPATCH_CONTEXT_INDICES.map(|i| code[42 + i]);
  // Full byte-bank admission begins at chunk zero, includes exact EOF, and
  // carries both actual root words into the next memory stage.
  let empty = SparseMemory::new(MemoryDepth::new(40)?)
    .root()
    .map(|v| b.fixed_public_input(v));
  join(&mut b, &raw_p[4..6], &empty);
  join(&mut b, &raw_p[7..9], &code[40..42]);
  join(&mut b, &code[79..81], &raw_i[4..6]);
  join(&mut b, &raw_i[7..9], &input[38..40]);
  for raw in [raw_p, raw_i] {
    b.connect(raw[3], zero);
    check(&mut b, gates[1].0, [raw[0], raw[6], zero, zero], zero);
  }
  join(&mut b, &raw_p[..3], &code[..3]);
  join(&mut b, &raw_i[..3], &input[..3]);
  // Exact parser initialization, Done at EOF, and no unfinished obligation.
  for (capture, final_at, is_input) in [(code, 42, false), (input, 40, true)] {
    check(
      &mut b,
      gates[0].0,
      [capture[0], capture[3], capture[final_at], capture[final_at + 1]],
      zero,
    );
    for i in 1..30 {
      let expected = if is_input {
        DISPATCH_CONTEXT_INDICES
          .iter()
          .position(|&c| c == i)
          .map_or(zero, |at| context[at])
      } else {
        zero
      };
      b.connect(capture[3 + i], expected);
    }
    for i in [
      grammar::FUNCTIONS_LEFT,
      grammar::BLOCKS_LEFT,
      grammar::CTORS_LEFT,
      grammar::ITEMS,
      grammar::PAYLOAD,
      grammar::PENDING,
      28,
      29,
    ] {
      b.connect(capture[final_at + i], zero);
    }
  }
  zeroes(&mut b, &code[33..40], zero);
  zeroes(&mut b, &code[72..79], zero);
  zeroes(&mut b, &input[33..38], zero);
  for i in [70, 72, 73] {
    b.connect(input[i], zero);
  }
  for (i, &wire) in DISPATCH_CONTEXT_INDICES.iter().zip(&context) {
    b.connect(input[40 + i], wire);
  }
  // The setup owns semantic limits and the complete fuel budget. Program
  // counts, entry and arity remain variables bound to the captured program.
  for (&wire, value) in
    context[2..12].iter().chain([&context[14]]).zip(profile.words())
  {
    let expected = b.fixed_public_input(value);
    b.connect(wire, expected);
  }
  join(&mut b, &references[..3], &[context[1], context[0], context[12]]);
  join(&mut b, &references[3..5], &code[79..81]);
  zeroes(&mut b, &references[5..8], zero);
  zeroes(&mut b, &references[9..11], zero);
  check(&mut b, gates[4].0, [context[1], references[8], zero, zero], zero);
  b.connect(ids[0], context[0]);
  join(&mut b, &ids[1..3], &code[79..81]);
  let initialized =
    initialize.derive(&mut b, context, input[70..75].try_into().unwrap());
  join(&mut b, &exec[..3], &initialized.parameters);
  b.connect(exec[3], initialized.clock);
  join(&mut b, &exec[4..28], &initialized.state);
  join(&mut b, &exec[28..30], &input[75..77]);
  check(&mut b, gates[5].0, [exec[3], exec[30], zero, zero], zero);
  let halted = finalize.derive(
    &mut b,
    exec[..3].try_into().unwrap(),
    exec[31..55].try_into().unwrap(),
    [raw_p[0], raw_i[0]],
  );
  join(&mut b, &output[3..5], &exec[55..57]);
  join(&mut b, &output[5..7], &halted.result);
  b.connect(output[7], zero);
  check(&mut b, gates[3].0, [output[6], output[8], zero, zero], zero);
  // Each bridge already constrains the domain and every transformed source
  // chunk. Here all three complete chains use the same actual B digest.
  let bridge_p = get(ProgramCommitment);
  let bridge_i = get(InputCommitment);
  let bridge_o = get(OutputCommitment);
  for (bridge, raw, parent) in [
    (bridge_p, raw_p, &p[..]),
    (bridge_i, raw_i, &bridge_p[5..7]),
    (bridge_o, output, &bridge_p[5..7]),
  ] {
    join(&mut b, &bridge[..3], &raw[..3]);
    join(&mut b, &bridge[3..5], parent);
    b.connect(bridge[7], zero);
    check(&mut b, gates[2].0, [bridge[0], bridge[8], zero, zero], zero);
  }
  let mut message =
    vec![b.fixed_public_input(pack_bytes(b"IxBy/commit/v0\0\x04"))];
  message.extend(p);
  message.extend(&bridge_p[5..7]);
  message.extend(&bridge_i[5..7]);
  message.extend(&bridge_o[5..7]);
  message.resize(statement_hash.padded_words(), zero);
  let length = b.fixed_public_input(F128::new(144, 0));
  let digest = statement_hash.hash(&mut b, length, &message);
  // Commit every fact through a real table, including parser metadata whose
  // meaning is checked only in its component proof. No dangling public input
  // can be changed while reusing this proof in a closing recursive relation.
  for chunk in facts.chunks(32) {
    let mut block = [zero; 32];
    block[..chunk.len()].copy_from_slice(chunk);
    let copied = publish_slot.select(&mut b, one, &block, &[zero; 32]);
    for &word in &copied[..chunk.len()] {
      b.publish(word);
    }
  }
  for word in digest {
    b.publish(word);
  }
  let (inputs, public) = b.finish();
  Ok(Emission {
    gates,
    initialize,
    finalize,
    hashes: [profile_hash, statement_hash],
    publish_gate: (publish_slot.slot(), publish_gate),
    inputs,
    public,
  })
}
