use super::*;
use crate::{
  hash::pack_bytes,
  ixby::{
    auth_memory::{MemoryDepth, SparseMemory},
    bits::{fill_words, read_words},
  },
  sizing::CountedGate,
};
use flock_prover::{circuit::builder::GateType, union::UnionInstance};

fn evaluate(g: &SourceBytesGate, input: &[F128]) -> Vec<F128> {
  let mut output = Vec::new();
  g.eval(input, &(), &mut output);
  let mut row = vec![false; g.r1cs().n()];
  g.plan().fill_row(&mut row[..g.plan().k()], |bits| fill_words(input, bits));
  assert_eq!(read_words(&row, input.len(), output.len()), output);
  assert!(g.r1cs().satisfies(&row));
  output
}
fn data(len: usize) -> Vec<u8> {
  (0..len).map(|i| (i.wrapping_mul(197) ^ (i >> 9)) as u8).collect()
}
fn memory() -> SparseMemory {
  SparseMemory::new(MemoryDepth::new(MEMORY_DEPTH).unwrap())
}

#[test]
fn source_control_covers_exact_length_and_all_high_bits() {
  let g = SourceBytesGate::new(SourceBank::Program, 3, SourceBytesOp::Control)
    .unwrap();
  for len in
    [0u64, 1, 1023, 1024, 1025, 2048, 2049, 4096, (1 << 24) - 1, 1 << 24]
  {
    let last = len.saturating_sub(1) >> 10;
    for first in [0, last.saturating_sub(1), last] {
      let input = [F128::new(len, 0), F128::new(first, 0)];
      assert_eq!(
        evaluate(&g, &input),
        [
          (first + 1).min(last),
          last,
          u64::from(first < last),
          (first + 2).min(last + 1),
          0
        ]
        .map(|v| F128::new(v, 0))
      );
      for at in 0..2 {
        let mut bad = input;
        bad[at].hi = 1 << 63;
        assert_eq!(evaluate(&g, &bad).last(), Some(&F128::ONE));
      }
    }
    assert_eq!(
      evaluate(&g, &[F128::new(len, 0), F128::new(last + 1, 0)]).last(),
      Some(&F128::ONE)
    );
  }
  assert_eq!(
    evaluate(&g, &[F128::new((1 << 24) + 1, 0), F128::ZERO]).last(),
    Some(&F128::ONE)
  );
}
#[test]
fn copy_outputs_addresses_padding_and_recycled_rows_are_constrained() {
  for bank in [SourceBank::Program, SourceBank::Input] {
    let g = SourceBytesGate::new(bank, 3, SourceBytesOp::Copy).unwrap();
    for live in [0, 1] {
      let mut input = (0..130).map(|i| F128::new(i, !i)).collect::<Vec<_>>();
      input[0] = F128::new(16383, 0);
      input[1] = F128::new(live, 0);
      let out = evaluate(&g, &input);
      assert_eq!(out.last(), Some(&F128::ZERO));
      for cell in 0..64 {
        assert_eq!(
          out[3 * cell],
          F128::new(bank.address() + 16383 * 32 + cell as u64, 0)
        );
        assert_eq!(
          out[3 * cell + 1..3 * cell + 3],
          if cell < 32 || live == 1 {
            input[2 + 2 * cell..4 + 2 * cell].to_vec()
          } else {
            vec![F128::ZERO; 2]
          }
        );
      }
      let r1cs = g.r1cs();
      let mut row = vec![false; r1cs.n()];
      g.plan()
        .fill_row(&mut row[..g.plan().k()], |bits| fill_words(&input, bits));
      // Each address/value/residual word, including both highest bits.
      for at in g.input_count()..g.input_count() + g.output_count() {
        for bit in [0, 63, 64, 127] {
          row[at * 128 + bit] ^= true;
          assert!(!r1cs.satisfies(&row));
          row[at * 128 + bit] ^= true;
        }
      }
      crate::ixby::test_support::padding(
        g.plan(),
        &[SourceBytesRow(input.clone())],
        |r, bits| fill_words(&r.0, bits),
        |dst| g.generate_witness_into(&[SourceBytesRow(input.clone())], dst),
      );
      for at in [0, 1] {
        let mut bad = input.clone();
        bad[at].hi = 1;
        assert_eq!(evaluate(&g, &bad).last(), Some(&F128::ONE));
      }
      input[1] = F128::new(2, 0);
      assert_eq!(evaluate(&g, &input).last(), Some(&F128::ONE));
    }
  }
}
#[test]
fn authenticated_source_chains_match_native_memory_and_reject_private_changes()
{
  for bank in [SourceBank::Program, SourceBank::Input] {
    let setup = CompiledSourceBytes::compile(bank).unwrap();
    for length in [0, 1, 1024, 1025, 2048, 2049, 4097] {
      let bytes = data(length);
      let mut mem = memory();
      let empty = mem.root();
      let mut source = SourceBytesWitness::new(bank, &bytes).unwrap();
      let mut previous = None;
      let mut first_statement = None;
      let mut last_statement = None;
      while let Some(advice) = source.next_batch(&mut mem).unwrap() {
        setup.check_advice(&advice).unwrap();
        if let Some(previous) = previous {
          assert_eq!(advice.statement.initial(), &previous);
        }
        previous = Some(*advice.statement.final_state());
        first_statement.get_or_insert(advice.statement.clone());
        last_statement = Some(advice.statement.clone());
        if length == 2049 && advice.statement.initial()[0] == F128::ZERO {
          let tree = 8 + 3 * (64 + 2 * SOURCE_DEPTH);
          for at in [
            0,
            1,
            3,
            4,
            6,
            8,
            8 + 64,
            tree + 2,
            tree + 4 * capacity().frontier() + 2,
          ] {
            let mut bad = advice.clone();
            bad.private[at] += F128::ONE;
            assert!(
              setup.check_advice(&bad).is_err(),
              "accepted private word {at}"
            );
          }
        }
      }
      let mut whole = *first_statement.unwrap().words();
      whole[6..].copy_from_slice(last_statement.unwrap().final_state());
      SourceBytesStatement::from_words(&whole)
        .unwrap()
        .check_complete(empty)
        .unwrap();
      let cells = bytes.chunks(32).enumerate().map(|(i, bytes)| {
        let mut cell = [0; 32];
        cell[..bytes.len()].copy_from_slice(bytes);
        (
          bank.address() + i as u64,
          [pack_bytes(&cell[..16]), pack_bytes(&cell[16..])],
        )
      });
      assert_eq!(
        mem.root(),
        SparseMemory::from_cells(
          MemoryDepth::new(MEMORY_DEPTH).unwrap(),
          cells
        )
        .unwrap()
        .root()
      );
      let mut replay = SourceBytesWitness::new(bank, &bytes).unwrap();
      if bytes.iter().take(2048).any(|&byte| byte != 0) {
        assert!(replay.next_batch(&mut mem).is_err());
      }
    }
  }
}

#[test]
#[ignore = "real source-to-memory proofs, isolated verification and recomputed local-row attacks"]
fn source_bytes_prove_fresh_and_reject_recomputed_copies() {
  use flock_prover::prover::UnionSlotProverInput;
  use std::{
    io::{Read, Write},
    process::{Command, Stdio},
    time::Instant,
  };
  const CHILD: &str = "IXBY_SOURCE_BYTES_VERIFY_CHILD";
  let bank =
    if std::env::var_os(CHILD).as_deref() == Some(std::ffi::OsStr::new("1")) {
      SourceBank::Input
    } else {
      SourceBank::Program
    };
  // Receiver kind is carried in an explicit test harness byte, never trusted
  // by production verification to select a relation from proof bytes.
  let started = Instant::now();
  let setup = CompiledSourceBytes::compile(bank).unwrap();
  let setup_time = started.elapsed();
  if std::env::var_os(CHILD).is_some() {
    let mut bytes = Vec::new();
    std::io::stdin()
      .take(8 * 1024 * 1024 + 145)
      .read_to_end(&mut bytes)
      .unwrap();
    assert!(bytes.len() >= 144);
    let words = bytes[..144]
      .as_chunks::<16>()
      .0
      .iter()
      .map(|b| pack_bytes(b))
      .collect::<Vec<_>>();
    setup
      .verify(&SourceBytesStatement::from_words(&words).unwrap(), &bytes[144..])
      .unwrap();
    return;
  }
  for (bank, setup) in [
    (SourceBank::Program, setup),
    (
      SourceBank::Input,
      CompiledSourceBytes::compile(SourceBank::Input).unwrap(),
    ),
  ] {
    let bytes = data(2049);
    let mut mem = memory();
    let mut source = SourceBytesWitness::new(bank, &bytes).unwrap();
    let first = source.next_batch(&mut mem).unwrap().unwrap();
    let tail = source.next_batch(&mut mem).unwrap().unwrap();
    for advice in [&first, &tail] {
      let started = Instant::now();
      let proof = setup.prove(advice).unwrap();
      let prove_time = started.elapsed();
      setup.verify(&advice.statement, &proof).unwrap();
      let mut child=Command::new(std::env::current_exe().unwrap()).args(["--ignored","--exact","ixby::ixbf_decode::paged::source_bytes::tests::source_bytes_prove_fresh_and_reject_recomputed_copies","--test-threads=1","--nocapture"]).current_dir(std::env::temp_dir()).env_clear().env(CHILD,if bank==SourceBank::Input {"1"}else{"0"}).env("RAYON_NUM_THREADS","4").stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
      let mut stdin = child.stdin.take().unwrap();
      for word in advice.statement.words() {
        stdin.write_all(&word.lo.to_le_bytes()).unwrap();
        stdin.write_all(&word.hi.to_le_bytes()).unwrap();
      }
      stdin.write_all(&proof).unwrap();
      drop(stdin);
      let result = child.wait_with_output().unwrap();
      assert!(
        result.status.success(),
        "{} {}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
      );
      let union =
        UnionInstance::new(&setup.shape.registry, setup.shape.counts.clone());
      eprintln!(
        "source bank={bank:?} cursor={}..{} proof={} setup={setup_time:?} prove={prove_time:?} M={} dense={} words",
        advice.statement.initial()[0].lo,
        advice.statement.final_state()[0].lo,
        proof.len(),
        union.dense_m(),
        union.dense_words()
      );
      for at in 0..PUBLIC_WORDS {
        let mut words = *advice.statement.words();
        words[at] += F128::ONE;
        if let Ok(bad) = SourceBytesStatement::from_words(&words) {
          assert!(setup.verify(&bad, &proof).is_err());
        }
      }
      assert!(
        setup.verify(&advice.statement, &proof[..proof.len() - 1]).is_err()
      );
      let mut extended = proof.clone();
      extended.push(0);
      assert!(setup.verify(&advice.statement, &extended).is_err());
    }
    let witness = setup.witness(&first).unwrap();
    for attack in 0..4 {
      let (slot, g) = &setup.emission.gates[usize::from(attack != 0)];
      let mut rows = witness.rows::<SourceBytesGate>(*slot).to_vec();
      match attack {
        0 => rows[0].0[1] = F128::ONE,
        1 => rows[0].0[0] = F128::ONE,
        2 => rows[0].0[1] = F128::ZERO,
        _ => rows[0].0[2] += F128::ONE,
      };
      assert_eq!(evaluate(g, &rows[0].0).last(), Some(&F128::ZERO));
      let table = g.r1cs();
      let boolean = setup
        .drivers
        .iter()
        .map(|d| {
          if d.slot() == *slot {
            let rows = rows.clone();
            UnionSlotProverInput::in_place(
              move |dst| g.generate_witness_into(&rows, dst),
              table.csc_lincheck_circuit(),
            )
          } else {
            d.prover(&witness)
          }
        })
        .collect();
      let bad = setup.prove_rows(&witness, boolean).unwrap();
      let error = setup.verify(&first.statement, &bad).unwrap_err();
      eprintln!("recomputed source attack {attack} rejected: {error}");
      assert!(format!("{error}").contains("Wiring"));
    }
  }
}
