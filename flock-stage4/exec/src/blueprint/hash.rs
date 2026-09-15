//! Pure operation-tree -> chained-BLAKE3 topology lowering. No compression is
//! evaluated and no dummy proof/nonce/message is generated. The two witness
//! columns of each row are deliberately zero placeholders. They are ignored
//! by structural comparison and setup-only emission, never used as a witness.

use super::algebra::Addresses;
use crate::replay::Stage4TranscriptOpV1 as Op;
use anyhow::{Result, ensure};
use flock_prover::{
  challenger::{
    KIND_NONE, KIND_SCALAR, KIND_SLICE, OP_BYTES, OP_DOMAIN, OP_LABEL,
    OP_OBSERVE, pow_squeeze_counter,
  },
  r1cs_hashes::fs_chain::{CHAIN_ABSORB, CHAIN_SQUEEZE},
};
use ix_stage4_trace::{
  ChainedBlake3ChainV1 as Chain, ChainedBlake3ChallengeSourceV1,
  ChainedBlake3ChildV1, ChainedBlake3PowConstraintV1,
  ChainedBlake3TranscriptV1 as Transcript, ChainingValueSourceV1 as Cv,
  CompressionLinkV1, CompressionOutputWordV1, CompressionRowV1,
  StreamWordSourceV1 as Word,
};

pub(crate) struct HashBlueprint {
  topology: Transcript,
}

impl HashBlueprint {
  /// Only the shape-only builder may consume this value-free trace directly.
  pub(crate) fn setup_topology(&self) -> &Transcript {
    &self.topology
  }

  pub(crate) fn topology_digest(&self) -> [u8; 32] {
    self.topology.topology_digest()
  }
  /// Compare every structural field directly. The only excluded fields are
  /// the compression's concrete CV and message (both witness columns).
  pub(crate) fn matches(&self, actual: &Transcript) -> bool {
    let expected = &self.topology;
    expected.domain == actual.domain
      && expected.challenge_sources == actual.challenge_sources
      && expected.pow_constraints == actual.pow_constraints
      && same_chain(&expected.parent, &actual.parent)
      && expected.children.len() == actual.children.len()
      && expected.children.iter().zip(&actual.children).all(|(e, a)| {
        e.label == a.label
          && e.parent_seed_squeeze == a.parent_seed_squeeze
          && e.child_seed_word == a.child_seed_word
          && e.child_digest_squeeze == a.child_digest_squeeze
          && e.parent_digest_word == a.parent_digest_word
          && same_chain(&e.chain, &a.chain)
      })
  }
}

fn same_chain(expected: &Chain, actual: &Chain) -> bool {
  expected.stream_words == actual.stream_words
    && expected.finalize_after == actual.finalize_after
    && expected.squeeze_words == actual.squeeze_words
    && expected.compression_rows.len() == actual.compression_rows.len()
    && expected.compression_rows.iter().zip(&actual.compression_rows).all(
      |(e, a)| {
        e.counter == a.counter
          && e.block_length == a.block_length
          && e.flags == a.flags
          && e.link == a.link
          && e.stream_offset == a.stream_offset
          && e.stream_word_count == a.stream_word_count
      },
    )
}

pub(super) fn compile_hash(
  operations: &[Op],
  domain: &[u8],
  expected_observed: u64,
  expected_challenges: u64,
  expected_payloads: &[usize],
) -> Result<HashBlueprint> {
  let mut address = Addresses { observed: 0, challenges: 0 };
  let mut payloads = Vec::new();
  let mut children = Vec::new();
  let parent = stream(
    operations,
    domain,
    &mut address,
    &mut payloads,
    &mut children,
    false,
  )?;
  ensure!(
    address.observed == expected_observed && payloads == expected_payloads,
    "hash stream address/payload agreement"
  );
  let mut topology = Transcript {
    domain: domain.to_vec(),
    parent,
    children,
    challenge_sources: Vec::new(),
    pow_constraints: Vec::new(),
  };
  map_squeezes(
    operations,
    0,
    &topology.parent,
    &topology.children,
    &mut topology.challenge_sources,
    &mut topology.pow_constraints,
  )?;
  ensure!(
    topology.challenge_sources.len() as u64 == expected_challenges,
    "hash challenge address agreement"
  );
  topology.validate(usize::try_from(expected_observed)?, expected_payloads)?;
  Ok(HashBlueprint { topology })
}

fn stream(
  operations: &[Op],
  domain: &[u8],
  address: &mut Addresses,
  payloads: &mut Vec<usize>,
  children: &mut Vec<ChainedBlake3ChildV1>,
  is_child: bool,
) -> Result<Chain> {
  let mut chain = Chain {
    stream_words: Vec::new(),
    finalize_after: Vec::new(),
    compression_rows: Vec::new(),
    squeeze_words: Vec::new(),
  };
  let mut squeezes = Vec::new();
  let mut pending_pow = None;
  append_label(&mut chain.stream_words, OP_DOMAIN, domain);
  for (index, op) in operations.iter().enumerate() {
    ensure!(
      pending_pow.is_none()
        || matches!(op, Op::SqueezeScalar | Op::SqueezeSlice(_)),
      "PoW must immediately precede a squeeze"
    );
    match op {
      Op::Label(label) => {
        append_label(&mut chain.stream_words, OP_LABEL, label)
      },
      Op::ObserveScalar => {
        chain.stream_words.push(header(OP_OBSERVE, KIND_SCALAR, 1));
        chain.stream_words.push(Word::ObservedValue(address.observe_index()));
      },
      Op::ObserveSlice(count) => {
        chain.stream_words.push(header(OP_OBSERVE, KIND_SLICE, *count));
        for _ in 0..*count {
          chain.stream_words.push(Word::ObservedValue(address.observe_index()));
        }
      },
      Op::ObserveBytes(length) => {
        chain.stream_words.push(header(OP_BYTES, KIND_NONE, *length));
        for word in 0..length.div_ceil(16) {
          chain
            .stream_words
            .push(Word::BytePayload { payload: payloads.len() as u64, word });
        }
        payloads.push(usize::try_from(*length)?);
      },
      Op::Pow { bits } => {
        ensure!(*bits <= 128, "PoW difficulty exceeds one field word");
        chain
          .stream_words
          .push(Word::BytePayload { payload: payloads.len() as u64, word: 0 });
        payloads.push(8);
        pending_pow = Some(*bits);
      },
      Op::SqueezeScalar | Op::SqueezeSlice(_) => {
        let count = match op {
          Op::SqueezeSlice(n) => *n,
          _ => 1,
        };
        ensure!(
          count != 0,
          "empty squeezed vectors are not admitted by the terminal trace"
        );
        chain.finalize_after.push(chain.stream_words.len() as u64);
        squeezes.push((count, pending_pow.take()));
      },
      Op::Forked { label, ops } => {
        ensure!(
          !is_child,
          "nested forks are outside the pinned Exec transcript"
        );
        ensure!(
          index >= 2
            && operations[index - 2..index]
              == [Op::SqueezeScalar, Op::SqueezeScalar],
          "fork seed schedule"
        );
        ensure!(
          ops.starts_with(&[Op::ObserveScalar, Op::ObserveScalar])
            && ops.ends_with(&[Op::SqueezeScalar, Op::SqueezeScalar]),
          "child seed/closure schedule"
        );
        let child =
          stream(ops, label, address, payloads, &mut Vec::new(), true)?;
        let child_digest_squeeze = u64::try_from(child.finalize_after.len())?
          .checked_sub(2)
          .ok_or_else(|| anyhow::anyhow!("missing child closure"))?;
        children.push(ChainedBlake3ChildV1 {
          label: label.clone(),
          chain: child,
          parent_seed_squeeze: chain.finalize_after.len() as u64 - 2,
          child_seed_word: 2 + label.len().div_ceil(16) as u64,
          child_digest_squeeze,
          parent_digest_word: u64::MAX,
        });
      },
      Op::Merge { fork } => {
        ensure!(
          operations.get(index + 1..index + 3)
            == Some(&[Op::ObserveScalar, Op::ObserveScalar]),
          "parent merge observation schedule"
        );
        let child = children
          .get_mut(usize::try_from(*fork)?)
          .ok_or_else(|| anyhow::anyhow!("merge names absent child"))?;
        ensure!(child.parent_digest_word == u64::MAX, "child merged twice");
        child.parent_digest_word = chain.stream_words.len() as u64 + 1;
      },
      Op::LegacyPow { .. } => {
        anyhow::bail!("legacy PoW is not an Exec transcript")
      },
    }
  }
  ensure!(pending_pow.is_none(), "unfinished PoW");
  ensure!(
    children.iter().all(|child| child.parent_digest_word != u64::MAX),
    "unmerged child"
  );
  lower_rows(&mut chain, &squeezes)?;
  Ok(chain)
}

fn header(op: u8, kind: u8, length: u64) -> Word {
  let mut word = [0; 16];
  word[0] = op;
  word[1] = kind;
  word[8..].copy_from_slice(&length.to_le_bytes());
  Word::Constant(word)
}

fn append_label(words: &mut Vec<Word>, op: u8, label: &[u8]) {
  words.push(header(op, KIND_NONE, label.len() as u64));
  for chunk in label.chunks(16) {
    let mut word = [0; 16];
    word[..chunk.len()].copy_from_slice(chunk);
    words.push(Word::Constant(word));
  }
}

struct Rows {
  rows: Vec<CompressionRowV1>,
  cv: Cv,
}

impl Rows {
  fn emit(
    &mut self,
    offset: Option<u64>,
    words: u8,
    counter: u64,
    block_length: u32,
    flags: u32,
    high: bool,
  ) -> u64 {
    let row = self.rows.len() as u64;
    self.rows.push(CompressionRowV1 {
      chaining_value: [0; 8],
      message: [0; 16],
      counter,
      block_length,
      flags,
      link: CompressionLinkV1 {
        chaining_value: self.cv,
        right: None,
        repeats: None,
      },
      stream_offset: offset,
      stream_word_count: words,
    });
    self.cv = if high { Cv::RowHigh(row) } else { Cv::Row(row) };
    row
  }
}

fn lower_rows(
  chain: &mut Chain,
  squeezes: &[(u64, Option<u32>)],
) -> Result<()> {
  let mut rows = Rows { rows: Vec::new(), cv: Cv::Iv };
  let mut offset = 0u64;
  for (&upto, &(wanted, pow)) in chain.finalize_after.iter().zip(squeezes) {
    let mut pending = upto
      .checked_sub(offset)
      .ok_or_else(|| anyhow::anyhow!("nonmonotone stream"))?;
    // Fused grinding retains the last full block, ensuring that its nonce
    // remains in the same compression as the protected challenge.
    while pending > 4 || (pending == 4 && pow.is_none()) {
      rows.emit(Some(offset * 16), 4, 0, 64, CHAIN_ABSORB, false);
      pending -= 4;
      offset += 4;
    }
    let mut sources = Vec::new();
    if let Some(bits) = pow {
      ensure!(pending != 0, "PoW needs its pending nonce word");
      let row = rows.emit(
        Some(offset * 16),
        u8::try_from(pending)?,
        pow_squeeze_counter(bits, usize::try_from(pending * 16)?),
        64,
        CHAIN_SQUEEZE,
        true,
      );
      for word in [0, 2, 3].into_iter().take(usize::try_from(wanted)?) {
        sources.push(CompressionOutputWordV1 { row, word });
      }
      pending = 0;
    }
    while (sources.len() as u64) < wanted {
      let row = rows.emit(
        (pending != 0).then_some(offset * 16),
        u8::try_from(pending)?,
        0,
        u32::try_from(pending * 16)?,
        CHAIN_SQUEEZE,
        false,
      );
      pending = 0;
      for word in 0..4 {
        if sources.len() as u64 == wanted {
          break;
        }
        sources.push(CompressionOutputWordV1 { row, word });
      }
    }
    offset = upto;
    chain.squeeze_words.push(sources);
  }
  while chain.stream_words.len() as u64 - offset >= 4 {
    rows.emit(Some(offset * 16), 4, 0, 64, CHAIN_ABSORB, false);
    offset += 4;
  }
  chain.compression_rows = rows.rows;
  Ok(())
}

fn map_squeezes(
  ops: &[Op],
  chain_id: u64,
  chain: &Chain,
  children: &[ChainedBlake3ChildV1],
  challenges: &mut Vec<ChainedBlake3ChallengeSourceV1>,
  pow: &mut Vec<ChainedBlake3PowConstraintV1>,
) -> Result<()> {
  let mut index = 0;
  let mut child = 0;
  let mut pending = None;
  for op in ops {
    match op {
      Op::Pow { bits } => pending = Some(*bits),
      Op::SqueezeScalar | Op::SqueezeSlice(_) => {
        let count = match op {
          Op::SqueezeSlice(count) => *count,
          _ => 1,
        };
        if let Some(bits) = pending.take() {
          pow.push(ChainedBlake3PowConstraintV1 {
            chain: chain_id,
            row: chain.squeeze_words[index][0].row,
            bits,
          });
        }
        for squeeze_word in 0..count {
          challenges.push(ChainedBlake3ChallengeSourceV1 {
            chain: chain_id,
            squeeze: index as u64,
            squeeze_word,
          });
        }
        index += 1;
      },
      Op::Forked { ops, .. } => {
        let next = children
          .get(child)
          .ok_or_else(|| anyhow::anyhow!("missing hash child"))?;
        map_squeezes(ops, child as u64 + 1, &next.chain, &[], challenges, pow)?;
        child += 1;
      },
      _ => {},
    }
  }
  ensure!(
    index == chain.squeeze_words.len() && child == children.len(),
    "hash squeeze/child coverage"
  );
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{blueprint::tape::Tape, replay::Stage4FlockTranscriptWitnessV1};
  use flock_prover::{
    challenger::{Challenger, FsChallenger},
    field::F128,
    transcript_record::RecordingChallenger,
  };

  fn compile(tape: &Tape, domain: &[u8]) -> HashBlueprint {
    compile_hash(
      &tape.ops,
      domain,
      tape.address.observed,
      tape.address.challenges,
      &tape.payload_lengths,
    )
    .unwrap()
  }

  #[test]
  fn symbolic_layout_matches_native_absorb_pow_and_xof_boundaries() {
    let domain = b"IxBy/hash-layout-differential/v0";
    for length in [0, 1, 15, 16, 31, 32, 47, 48, 63, 64, 65, 129] {
      for width in [1, 3, 4, 5, 7, 8, 13] {
        for bits in [0, 3] {
          let mut tape = Tape::new();
          tape.label(b"prefix");
          tape.bytes(length);
          tape.squeeze_slice(width, None);
          tape.observe_slice(length % 9);
          tape.squeeze_slice(width, Some(bits));
          tape.observe();
          tape.squeeze(None);
          tape.bytes(length);
          // The expected layout exists before any native values or hashes.
          let expected = compile(&tape, domain);
          for seed in [7u64, 93] {
            let mut native = RecordingChallenger::new(
              FsChallenger::with_chained_blake3(domain),
            );
            native.observe_label(b"prefix");
            native.observe_bytes(&vec![u8::try_from(seed).unwrap(); length]);
            native.sample_f128_vec(width);
            native
              .observe_f128_slice(&vec![F128::new(seed, seed + 1); length % 9]);
            native.grind_pow_and_sample_f128_vec(bits, width);
            native.observe_f128(F128::new(seed + 2, seed + 3));
            native.sample_f128();
            native.observe_bytes(&vec![0x71; length]);
            let actual =
              Stage4FlockTranscriptWitnessV1::from_recording(&native, domain)
                .unwrap();
            assert_eq!(tape.ops, actual.operations());
            assert!(
              expected.matches(actual.chained_blake3()),
              "length={length}, width={width}, bits={bits}, seed={seed}"
            );
            assert_eq!(
              expected.topology_digest(),
              actual.chained_blake3().topology_digest()
            );
          }
        }
      }
    }
  }

  fn fork_fixture() -> (HashBlueprint, Transcript) {
    let domain = b"IxBy/hash-fork-differential/v0";
    let mut tape = Tape::new();
    tape.observe();
    let child = tape
      .fork(b"child", |child| {
        child.observe_slice(4);
        child.squeeze_slice(8, Some(0));
        Ok(())
      })
      .unwrap();
    tape.observe();
    tape.squeeze_slice(5, Some(3));
    tape.merge(child);
    tape.squeeze(None);
    let expected = compile(&tape, domain);
    let mut native =
      RecordingChallenger::new(FsChallenger::with_chained_blake3(domain));
    native.observe_f128(F128::new(2, 7));
    let mut child = native.fork(b"child");
    child.observe_f128_slice(&[F128::ONE; 4]);
    child.grind_pow_and_sample_f128_vec(0, 8);
    native.observe_f128(F128::new(13, 19));
    native.grind_pow_and_sample_f128_vec(3, 5);
    native.merge_child(child);
    native.sample_f128();
    let actual =
      Stage4FlockTranscriptWitnessV1::from_recording(&native, domain).unwrap();
    assert_eq!(tape.ops, actual.operations());
    assert!(expected.matches(actual.chained_blake3()));
    (expected, actual.chained_blake3().clone())
  }

  #[test]
  fn exact_layout_check_rejects_changes_to_every_kind_of_structural_field() {
    let (expected, actual) = fork_fixture();
    let changes: &[fn(&mut Transcript)] = &[
      |x| x.domain[0] ^= 1,
      |x| x.challenge_sources[0].chain += 1,
      |x| x.challenge_sources[0].squeeze += 1,
      |x| x.challenge_sources[0].squeeze_word += 1,
      |x| x.pow_constraints[0].bits += 1,
      |x| x.pow_constraints[0].row += 1,
      |x| x.pow_constraints[0].chain += 1,
      |x| x.parent.stream_words[0] = Word::ObservedValue(0),
      |x| x.parent.finalize_after[0] += 1,
      |x| x.parent.squeeze_words[0][0].word += 1,
      |x| x.parent.squeeze_words[0][0].row += 1,
      |x| x.parent.compression_rows[0].counter += 1,
      |x| x.parent.compression_rows[0].block_length += 1,
      |x| x.parent.compression_rows[0].flags ^= 1,
      |x| x.parent.compression_rows[0].stream_offset = None,
      |x| x.parent.compression_rows[0].stream_word_count += 1,
      |x| x.parent.compression_rows[0].link.chaining_value = Cv::Row(0),
      |x| x.parent.compression_rows[0].link.right = Some(0),
      |x| x.parent.compression_rows[0].link.repeats = Some(0),
      |x| {
        x.parent.compression_rows.pop();
      },
      |x| x.children[0].label[0] ^= 1,
      |x| x.children[0].parent_seed_squeeze += 1,
      |x| x.children[0].child_seed_word += 1,
      |x| x.children[0].child_digest_squeeze += 1,
      |x| x.children[0].parent_digest_word += 1,
      |x| x.children[0].chain.compression_rows[0].counter += 1,
      |x| {
        x.children.pop();
      },
    ];
    for (index, change) in changes.iter().enumerate() {
      let mut bad = actual.clone();
      change(&mut bad);
      assert!(!expected.matches(&bad), "structural mutation {index}");
    }
    let mut witness_only = actual;
    witness_only.parent.compression_rows[0].chaining_value[0] ^= 1;
    witness_only.parent.compression_rows[0].message[0] ^= 1;
    // This is topology equivalence, not transcript acceptance. The separate
    // compression constraints must reject these forged witness columns.
    assert!(expected.matches(&witness_only));
  }

  #[test]
  fn malformed_operation_trees_cannot_become_approved_hash_shapes() {
    let mut tape = Tape::new();
    let fork = tape.fork(b"child", |_| Ok(())).unwrap();
    tape.merge(fork);
    compile(&tape, b"domain");
    let mut mutations = Vec::new();
    let mut bad = tape.ops.clone();
    bad.push(Op::Pow { bits: 2 });
    mutations.push(bad);
    let mut bad = tape.ops.clone();
    bad.remove(0);
    mutations.push(bad);
    let mut bad = tape.ops.clone();
    bad.retain(|op| !matches!(op, Op::Merge { .. }));
    mutations.push(bad);
    let mut bad = tape.ops.clone();
    bad.push(Op::LegacyPow { bits: 0 });
    mutations.push(bad);
    let mut bad = tape.ops.clone();
    bad.push(Op::SqueezeSlice(0));
    mutations.push(bad);
    let mut bad = tape.ops.clone();
    bad.push(Op::Merge { fork: 1 });
    bad.extend([Op::ObserveScalar, Op::ObserveScalar]);
    mutations.push(bad);
    let mut bad = tape.ops.clone();
    let child_ops = tape.ops.clone();
    let Op::Forked { ops, .. } = &mut bad[2] else { unreachable!() };
    ops.splice(2..2, child_ops);
    mutations.push(bad);
    for bad in mutations {
      assert!(
        compile_hash(
          &bad,
          b"domain",
          tape.address.observed,
          tape.address.challenges,
          &tape.payload_lengths
        )
        .is_err()
      );
    }
  }
}
