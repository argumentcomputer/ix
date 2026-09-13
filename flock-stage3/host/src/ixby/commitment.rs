//! The exact byte binding of `Ix.Ixby.Commitment.Internal.bind`, followed by
//! `Statement.digest`, inside the fixed-capacity Flock circuit:
//! P = H(0, profile), B = H(1, P || program), I = H(2, B || input),
//! O = H(3, B || output), S = H(4, P || B || I || O).
//!
//! Each H includes the fixed 16-byte ASCII/NUL/domain prefix. Profile bytes
//! are setup-owned; program/input/output buffers and their lengths are wires.
//! Hashing is NOT codec admission or execution: the interpreter must constrain
//! their canonical encodings, full program admission, and output semantics.

use super::{
  bounded_hash::BoundedBlake3,
  hash_control::MAX_HASH_CAPACITY,
  length::{CheckedLengthAddGate, CheckedLengthAddSlot},
};
use crate::{hash::pack_bytes, sizing::CircuitEmitter};
use anyhow::{Result, ensure};
use flock_prover::{circuit::builder::Wire, field::F128};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CommitmentCapacities {
  pub program: usize,
  pub input: usize,
  pub output: usize,
}

#[derive(Clone, Copy)]
pub struct ByteBuffer<'a> {
  pub length: Wire,
  /// Exactly ceil(capacity / 16) little-endian words, including zero padding.
  pub words: &'a [Wire],
}

#[derive(Clone, Copy, Debug)]
pub struct StatementWires {
  pub profile: [Wire; 2],
  pub program: [Wire; 2],
  pub input: [Wire; 2],
  pub output: [Wire; 2],
  pub digest: [Wire; 2],
}

pub struct ByteCommitmentSlots {
  capacities: CommitmentCapacities,
  hashes: [BoundedBlake3; 5],
  length_gate: CheckedLengthAddGate,
  length_slot: CheckedLengthAddSlot,
  prefixes: [Wire; 4],
  profile_length: Wire,
  profile_message: Vec<Wire>,
  statement_length: Wire,
  zero: Wire,
}

fn prefix(tag: u8) -> F128 {
  let mut bytes = *b"IxBy/commit/v0\0\0";
  bytes[15] = tag;
  pack_bytes(&bytes)
}

impl ByteCommitmentSlots {
  /// Only capacities and the caller-owned profile image are accepted at setup.
  /// No program, input, output, execution trace or derived digest is accepted.
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    fixed_profile: &[u8],
    capacities: CommitmentCapacities,
  ) -> Result<Self> {
    ensure!(
      fixed_profile.len() <= MAX_HASH_CAPACITY - 16,
      "profile hash capacity"
    );
    for capacity in [capacities.program, capacities.input, capacities.output] {
      ensure!(capacity <= MAX_HASH_CAPACITY - 48, "artifact hash capacity");
    }
    let profile = BoundedBlake3::declare(b, nu, fixed_profile.len() + 16)?;
    let program = profile.sharing_primitives(b, capacities.program + 48)?;
    let input = profile.sharing_primitives(b, capacities.input + 48)?;
    let output = profile.sharing_primitives(b, capacities.output + 48)?;
    let statement = profile.sharing_primitives(b, 144)?;
    let length_gate = CheckedLengthAddGate::new(nu, 48)?;
    let length_slot = CheckedLengthAddSlot::declare(b, length_gate.clone());
    let prefixes = [1, 2, 3, 4].map(|tag| b.fixed_public_input(prefix(tag)));
    let zero = b.fixed_public_input(F128::ZERO);
    let profile_length =
      b.fixed_public_input(F128::new((fixed_profile.len() + 16) as u64, 0));
    let mut padded_profile = vec![0; profile.padded_words() * 16];
    padded_profile[..16].copy_from_slice(b"IxBy/commit/v0\0\0");
    padded_profile[16..16 + fixed_profile.len()].copy_from_slice(fixed_profile);
    let profile_message = padded_profile
      .as_chunks::<16>()
      .0
      .iter()
      .map(|word| b.fixed_public_input(pack_bytes(word)))
      .collect();
    let statement_length = b.fixed_public_input(F128::new(144, 0));
    Ok(Self {
      capacities,
      hashes: [profile, program, input, output, statement],
      length_gate,
      length_slot,
      prefixes,
      profile_length,
      profile_message,
      statement_length,
      zero,
    })
  }

  /// Hash capacity-specific tables are distinct; compression, selectors and
  /// ROOT slots are shared. Prover drivers must include each unique slot once.
  pub fn hashes(&self) -> &[BoundedBlake3; 5] {
    &self.hashes
  }
  pub fn length_gate(&self) -> &CheckedLengthAddGate {
    &self.length_gate
  }
  pub fn length_slot(&self) -> CheckedLengthAddSlot {
    self.length_slot
  }

  pub fn bind(
    &self,
    b: &mut impl CircuitEmitter,
    program: ByteBuffer<'_>,
    input: ByteBuffer<'_>,
    output: ByteBuffer<'_>,
  ) -> StatementWires {
    let profile =
      self.hashes[0].hash(b, self.profile_length, &self.profile_message);
    let program =
      self.artifact(b, 1, self.capacities.program, profile, program);
    let input = self.artifact(b, 2, self.capacities.input, program, input);
    let output = self.artifact(b, 3, self.capacities.output, program, output);
    let mut statement = vec![self.prefixes[3]];
    for digest in [profile, program, input, output] {
      statement.extend(digest);
    }
    statement.resize(self.hashes[4].padded_words(), self.zero);
    let digest = self.hashes[4].hash(b, self.statement_length, &statement);
    StatementWires { profile, program, input, output, digest }
  }

  fn artifact(
    &self,
    b: &mut impl CircuitEmitter,
    domain: usize,
    capacity: usize,
    parent: [Wire; 2],
    data: ByteBuffer<'_>,
  ) -> [Wire; 2] {
    assert_eq!(
      data.words.len(),
      capacity.div_ceil(16),
      "fixed artifact buffer width"
    );
    let length = self.length_slot.add(b, data.length);
    let mut words = vec![self.prefixes[domain - 1], parent[0], parent[1]];
    words.extend_from_slice(data.words);
    words.resize(self.hashes[domain].padded_words(), self.zero);
    self.hashes[domain].hash(b, length, &words)
  }
}

#[cfg(test)]
pub(super) mod tests {
  use super::*;
  use crate::ixby::io::LayoutEmitter;
  use crate::sizing::CountingEmitter;
  use flock_prover::circuit::builder::ShapeBuilder;

  pub(crate) fn native(
    profile: &[u8],
    program: &[u8],
    input: &[u8],
    output: &[u8],
  ) -> [[F128; 2]; 5] {
    fn hash(tag: u8, prefix: &[u8], data: &[u8]) -> [u8; 32] {
      let mut bytes = b"IxBy/commit/v0".to_vec();
      bytes.extend([0, tag]);
      bytes.extend_from_slice(prefix);
      bytes.extend_from_slice(data);
      *::blake3::hash(&bytes).as_bytes()
    }
    let p = hash(0, &[], profile);
    let b = hash(1, &p, program);
    let i = hash(2, &b, input);
    let o = hash(3, &b, output);
    let s = hash(4, &[], &[p, b, i, o].concat());
    [p, b, i, o, s]
      .map(|digest| [pack_bytes(&digest[..16]), pack_bytes(&digest[16..])])
  }

  fn data_wires(
    b: &mut impl CircuitEmitter,
    capacity: usize,
  ) -> (Wire, Vec<Wire>) {
    let length = b.input();
    (length, (0..capacity.div_ceil(16)).map(|_| b.input()).collect())
  }

  pub(crate) fn advice(capacity: usize, data: &[u8]) -> Vec<F128> {
    assert!(data.len() <= capacity);
    let mut bytes = vec![0; capacity.div_ceil(16) * 16];
    bytes[..data.len()].copy_from_slice(data);
    let mut words = vec![F128::new(data.len() as u64, 0)];
    words.extend(bytes.as_chunks::<16>().0.iter().map(|word| pack_bytes(word)));
    words
  }

  pub(crate) fn emit(
    b: &mut impl CircuitEmitter,
    profile: &[u8],
    capacities: CommitmentCapacities,
    expose_components: bool,
  ) -> (
    ByteCommitmentSlots,
    super::super::io::InputLayout,
    super::super::io::PublicLayout,
  ) {
    let mut b = LayoutEmitter::new(b);
    let slots =
      ByteCommitmentSlots::declare(&mut b, 8, profile, capacities).unwrap();
    let (program_length, program) = data_wires(&mut b, capacities.program);
    let (input_length, input) = data_wires(&mut b, capacities.input);
    let (output_length, output) = data_wires(&mut b, capacities.output);
    let statement = slots.bind(
      &mut b,
      ByteBuffer { length: program_length, words: &program },
      ByteBuffer { length: input_length, words: &input },
      ByteBuffer { length: output_length, words: &output },
    );
    // Expose intermediate outputs only in this component differential. The
    // eventual Exec public ABI publishes only the final two digest limbs.
    let digests = if expose_components {
      vec![
        statement.profile,
        statement.program,
        statement.input,
        statement.output,
        statement.digest,
      ]
    } else {
      vec![statement.digest]
    };
    for digest in digests {
      for word in digest {
        b.publish(word);
      }
    }
    let (inputs, public) = b.finish();
    (slots, inputs, public)
  }

  #[test]
  fn complete_domain_chain_matches_native_for_changed_private_artifacts() {
    let profile: Vec<_> = (0..68).map(|i| (i * 31) as u8).collect();
    let capacities =
      CommitmentCapacities { program: 130, input: 1100, output: 67 };
    let mut builder = ShapeBuilder::new(8);
    let (slots, layout, public) =
      emit(&mut builder, &profile, capacities, true);
    let shape = builder.finish().unwrap();
    let identity = shape.circuit.digest();
    for (program_length, input_length, output_length) in
      [(0, 0, 0), (1, 1, 1), (16, 976, 16), (17, 977, 17), (130, 1100, 67)]
    {
      let program: Vec<_> =
        (0..program_length).map(|i| (i * 17 + 1) as u8).collect();
      let input: Vec<_> =
        (0..input_length).map(|i| (i * 29 + 3) as u8).collect();
      let output: Vec<_> =
        (0..output_length).map(|i| (i * 41 + 7) as u8).collect();
      let private = [
        advice(capacities.program, &program),
        advice(capacities.input, &input),
        advice(capacities.output, &output),
      ]
      .concat();
      let witness = shape.run(&layout.assign(&private).unwrap(), &[]);
      let expected: Vec<_> = native(&profile, &program, &input, &output)
        .into_iter()
        .flatten()
        .collect();
      assert_eq!(witness.public, public.instantiate(&expected).unwrap());
      assert_eq!(shape.circuit.digest(), identity);
    }
    let mut count = CountingEmitter::new();
    let (_, counted_input, counted_public) =
      emit(&mut count, &profile, capacities, true);
    count.ensure_matches(&shape).unwrap();
    assert_eq!(counted_input, layout);
    assert_eq!(counted_public, public);
    assert_eq!(
      shape.counts.len(),
      9,
      "shared primitives plus five capacity tables and checked length"
    );
    for hash in slots.hashes().iter().skip(1) {
      assert_eq!(
        shape.registry_slot(hash.compression_slot()),
        shape.registry_slot(slots.hashes()[0].compression_slot())
      );
      assert_eq!(
        shape.registry_slot(hash.select_slot()),
        shape.registry_slot(slots.hashes()[0].select_slot())
      );
      assert_eq!(
        shape.registry_slot(hash.root_slot()),
        shape.registry_slot(slots.hashes()[0].root_slot())
      );
    }
    assert_eq!(
      shape.counts[shape.registry_slot(slots.length_slot().slot())],
      3
    );
  }

  #[test]
  fn admission_happens_before_allocating_or_emitting_any_hash_tables() {
    let mut count = CountingEmitter::new();
    for capacities in [
      CommitmentCapacities { program: usize::MAX, input: 0, output: 0 },
      CommitmentCapacities { program: 0, input: MAX_HASH_CAPACITY, output: 0 },
      CommitmentCapacities {
        program: 0,
        input: 0,
        output: MAX_HASH_CAPACITY - 47,
      },
    ] {
      assert!(
        ByteCommitmentSlots::declare(&mut count, 3, &[], capacities).is_err()
      );
      assert_eq!(count.table_rows().count(), 0);
    }
  }

  // These exact canonical identity artifacts and all five digest vectors are
  // also checked by Tests/Ixby/Codec.lean against the pure Lean implementation.
  // The profile has its ordinary logical limits; this is a byte-binding vector,
  // not a claim that the small physical hash buffer admits that Exec profile.
  pub(crate) const GOLDEN_PROFILE: &[u8] = &[
    73, 88, 66, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 16, 0, 0, 0, 0, 1,
    0, 0, 16, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 64, 66, 15, 0,
  ];
  pub(crate) const GOLDEN_PROGRAM: &[u8] = &[
    73, 88, 66, 89, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0,
  ];
  pub(crate) const GOLDEN_INPUT: &[u8] =
    &[73, 88, 66, 73, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 120, 86, 52, 18];
  pub(crate) const GOLDEN_OUTPUT: &[u8] =
    &[73, 88, 66, 79, 0, 0, 0, 0, 0, 1, 120, 86, 52, 18];

  #[test]
  fn pure_lean_golden_identity_commitments_match_every_circuit_component() {
    let golden = [
      [
        6966460787449768616,
        2128275386604001288,
        2459209300616560705,
        13389247344911543908,
      ],
      [
        14569967937961839496,
        13001501475163155991,
        8455333540139103506,
        16233222503319093095,
      ],
      [
        5547401797206108288,
        10199118524644542921,
        17387493906737207323,
        17266618757657491293,
      ],
      [
        5580381423085667084,
        3527724868188812160,
        3817058062606425944,
        8195236551432502967,
      ],
      [
        6407977636521055359,
        3463446082552244464,
        6667175477628965062,
        16312016406872336668,
      ],
    ]
    .map(|words| {
      [F128::new(words[0], words[1]), F128::new(words[2], words[3])]
    });
    assert_eq!(
      native(GOLDEN_PROFILE, GOLDEN_PROGRAM, GOLDEN_INPUT, GOLDEN_OUTPUT),
      golden
    );
    let capacities =
      CommitmentCapacities { program: 64, input: 32, output: 32 };
    let mut builder = ShapeBuilder::new(8);
    let (_, layout, public) =
      emit(&mut builder, GOLDEN_PROFILE, capacities, true);
    let shape = builder.finish().unwrap();
    let private = [
      advice(capacities.program, GOLDEN_PROGRAM),
      advice(capacities.input, GOLDEN_INPUT),
      advice(capacities.output, GOLDEN_OUTPUT),
    ]
    .concat();
    let witness = shape.run(&layout.assign(&private).unwrap(), &[]);
    assert_eq!(
      witness.public,
      public
        .instantiate(&golden.into_iter().flatten().collect::<Vec<_>>())
        .unwrap()
    );
  }
}
