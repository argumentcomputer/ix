use super::*;
use crate::{
  hash::pack_bytes,
  ixby::{
    auth_memory::{MemoryDepth, SparseMemory},
    bits::{fill_words, read_words},
    ixbf::{self, DecodeLimits},
    paged_code::{self, PackedProgram},
  },
};
use flock_prover::{circuit::builder::GateType, union::UnionInstance};
fn ids(count: usize) -> SparseMemory {
  let mut cells = Vec::new();
  for i in 0..count {
    let mut id = [F128::ZERO; 4];
    if i != 0 {
      let bit = 2 * i - 1;
      let w = &mut id[bit / 128];
      if bit % 128 < 64 {
        w.lo = 1 << (bit % 64);
      } else {
        w.hi = 1 << (bit % 64);
      }
    }
    let a = paged_code::CONSTRUCTORS + 3 * i as u64;
    cells.extend([(a, [id[0], id[1]]), (a + 1, [id[2], id[3]])]);
  }
  SparseMemory::from_cells(MemoryDepth::new(40).unwrap(), cells).unwrap()
}
fn eval(g: &ConstructorIdGate, r: &[F128]) -> Vec<F128> {
  let mut out = Vec::new();
  g.eval(r, &(), &mut out);
  out
}
#[test]
fn fixed_readonly_tree_and_exact_sort_admit_all_counts_and_reject_duplicates() {
  let setup = CompiledConstructorIds::compile().unwrap();
  for count in [0, 1, 2, 255, 256] {
    let mut memory = ids(count);
    let root = memory.root();
    let advice = ConstructorIdsAdvice::new(&mut memory, count).unwrap();
    setup.check_advice(&advice).unwrap();
    assert_eq!(memory.root(), root);
  }
  let mut memory = ids(256);
  memory.replace(paged_code::CONSTRUCTORS + 3 * 255, [F128::ZERO; 2]).unwrap();
  memory
    .replace(paged_code::CONSTRUCTORS + 3 * 255 + 1, [F128::ZERO; 2])
    .unwrap();
  let advice = ConstructorIdsAdvice::new(&mut memory, 256).unwrap();
  assert!(setup.check_advice(&advice).is_err());
  let mut memory = ids(256);
  let undeclared = ConstructorIdsAdvice::new(&mut memory, 255).unwrap();
  assert!(setup.check_advice(&undeclared).is_err());
  let advice = ConstructorIdsAdvice::new(&mut memory, 256).unwrap();
  for at in [0, 1, 2, 3, 6, 3 + 4 * 256, 3 + 4 * 256 + plan().switches() + 1] {
    let mut bad = advice.clone();
    bad.private[at] += F128::ONE;
    assert!(setup.check_advice(&bad).is_err(), "private word {at}");
  }
  let union =
    UnionInstance::new(&setup.shape.registry, setup.shape.counts.clone());
  eprintln!(
    "constructor IDs M={} dense={} leaves={} parents={}",
    union.dense_m(),
    union.dense_words(),
    CELLS,
    PARENTS
  );
}
#[test]
fn identifier_comparison_uses_every_bit_and_source_padding_is_canonical() {
  let audit = ConstructorIdGate::new(3, ConstructorIdKind::Audit).unwrap();
  for bit in 0..512 {
    let mut input = vec![F128::ZERO; 11];
    input[0] = F128::ONE;
    input[5] = F128::ONE;
    let w = &mut input[6 + bit / 128];
    if bit % 128 < 64 {
      w.lo = 1 << (bit % 64);
    } else {
      w.hi = 1 << (bit % 64);
    }
    assert_eq!(eval(&audit, &input), [F128::ZERO]);
    for i in 1..5 {
      input.swap(i, 5 + i);
    }
    assert_eq!(eval(&audit, &input), [F128::ONE]);
  }
  let mut equal = vec![F128::ZERO; 11];
  equal[0] = F128::ONE;
  equal[5] = F128::ONE;
  assert_eq!(eval(&audit, &equal), [F128::ONE]);
  equal[10] = F128::ONE;
  assert_eq!(eval(&audit, &equal), [F128::ONE]);
  let source = ConstructorIdGate::new(3, ConstructorIdKind::Source).unwrap();
  let mut rows = Vec::new();
  for count in [0, 1, 2, 255, 256] {
    for index in [0, 1, 254, 255] {
      let live = index < count;
      let mut r = vec![F128::new(count, 0), F128::new(index, 0)];
      r.extend(
        [if live { F128::new(u64::MAX, u64::MAX) } else { F128::ZERO }; 4],
      );
      let out = eval(&source, &r);
      assert_eq!(out[0], F128::new(u64::from(live), 0));
      assert_eq!(&out[1..5], &r[2..]);
      assert_eq!(out[5], F128::ZERO);
      for at in 0..2 {
        let mut bad = r.clone();
        bad[at].hi = 1;
        assert_eq!(eval(&source, &bad).last(), Some(&F128::ONE));
      }
      if !live {
        let mut bad = r.clone();
        bad[5] = F128::new(0, 1 << 63);
        assert_eq!(eval(&source, &bad).last(), Some(&F128::ONE));
      }
      rows.push(ConstructorIdRow(r));
    }
  }
  for (g, r) in
    [(&source, rows.last().unwrap().0.clone()), (&audit, vec![F128::ZERO; 11])]
  {
    let table = g.r1cs();
    let mut bits = vec![false; table.n()];
    g.plan().fill_row(&mut bits[..g.plan().k()], |b| fill_words(&r, b));
    assert!(table.satisfies(&bits));
    assert_eq!(
      read_words(&bits, g.kind.inputs(), g.kind.outputs()),
      eval(g, &r)
    );
    for at in g.kind.inputs()..g.kind.inputs() + g.kind.outputs() {
      for bit in [0, 63, 64, 127] {
        bits[at * 128 + bit] ^= true;
        assert!(!table.satisfies(&bits));
        bits[at * 128 + bit] ^= true;
      }
    }
  }
  rows.truncate(7);
  crate::ixby::test_support::padding(
    source.plan(),
    &rows,
    |r, b| fill_words(&r.0, b),
    |dst| source.generate_witness_into(&rows, dst),
  );
}
#[test]
#[ignore = "complete original full-ID uniqueness circuit; set IXBY_PAGED_PROGRAM"]
fn original_program_all_constructor_ids() {
  let bytes = std::fs::read(
    std::env::var_os("IXBY_PAGED_PROGRAM").expect("IXBY_PAGED_PROGRAM"),
  )
  .unwrap();
  let a = ixbf::decode_program(&bytes, DecodeLimits::default()).unwrap();
  let mut memory = SparseMemory::from_cells(
    MemoryDepth::new(40).unwrap(),
    PackedProgram::from_artifact(&a).unwrap().cells,
  )
  .unwrap();
  let advice =
    ConstructorIdsAdvice::new(&mut memory, a.constructors().len()).unwrap();
  let setup = CompiledConstructorIds::compile().unwrap();
  setup.check_advice(&advice).unwrap();
  eprintln!("original constructor IDs count={}", a.constructors().len());
}

#[test]
#[ignore = "full 256-constructor proofs with fresh receivers and valid recomputed ID substitutions"]
fn constructor_ids_prove_fresh_and_reject_recomputed_ids() {
  use flock_prover::prover::UnionSlotProverInput;
  use std::{
    io::{Read, Write},
    process::{Command, Stdio},
    time::Instant,
  };
  const CHILD: &str = "IXBY_CONSTRUCTOR_IDS_VERIFY_CHILD";
  const TEST: &str = "ixby::ixbf_decode::paged::constructor_ids::tests::constructor_ids_prove_fresh_and_reject_recomputed_ids";
  let start = Instant::now();
  let setup = CompiledConstructorIds::compile().unwrap();
  let setup_time = start.elapsed();
  if std::env::var_os(CHILD).is_some() {
    let mut bytes = Vec::new();
    std::io::stdin()
      .take(8 * 1024 * 1024 + 16 * PUBLIC_WORDS as u64 + 1)
      .read_to_end(&mut bytes)
      .unwrap();
    assert!(bytes.len() >= 16 * PUBLIC_WORDS);
    let expected = bytes[..16 * PUBLIC_WORDS]
      .as_chunks::<16>()
      .0
      .iter()
      .map(|v| pack_bytes(v))
      .collect::<Vec<_>>();
    setup
      .verify(
        &ConstructorIdsStatement::from_words(&expected).unwrap(),
        &bytes[16 * PUBLIC_WORDS..],
      )
      .unwrap();
    return;
  }
  for count in [256, 0] {
    let mut memory = ids(count);
    let advice = ConstructorIdsAdvice::new(&mut memory, count).unwrap();
    let witness = setup.witness(&advice).unwrap();
    let start = Instant::now();
    let proof = setup.prove(&advice).unwrap();
    let elapsed = start.elapsed();
    setup.verify(&advice.statement, &proof).unwrap();
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
    let mut stdin = child.stdin.take().unwrap();
    for word in advice.statement.words() {
      stdin.write_all(&word.lo.to_le_bytes()).unwrap();
      stdin.write_all(&word.hi.to_le_bytes()).unwrap();
    }
    stdin.write_all(&proof).unwrap();
    drop(stdin);
    let output = child.wait_with_output().unwrap();
    assert!(
      output.status.success(),
      "{} {}",
      String::from_utf8_lossy(&output.stdout),
      String::from_utf8_lossy(&output.stderr)
    );
    eprintln!(
      "constructor IDs count={count}: proof={} setup={setup_time:?} witness+prove={elapsed:?}",
      proof.len()
    );
    for at in 0..PUBLIC_WORDS {
      let mut words = *advice.statement.words();
      words[at] += F128::ONE;
      if let Ok(bad) = ConstructorIdsStatement::from_words(&words) {
        assert!(
          setup.verify(&bad, &proof).is_err(),
          "accepted expected word {at}"
        );
      }
    }
    assert!(
      setup.verify(&advice.statement, &proof[..proof.len() - 1]).is_err()
    );
    let mut extra = proof.clone();
    extra.push(0);
    assert!(setup.verify(&advice.statement, &extra).is_err());
    if count == 0 {
      continue;
    }
    for attack in 0..4 {
      let (slot, g) = &setup.emission.gates[usize::from(attack == 3)];
      let slot = *slot;
      let mut rows = witness.rows::<ConstructorIdGate>(slot).to_vec();
      let row = &mut rows[0];
      match attack {
        0 => row.0[0].lo -= 1,
        1 => row.0[1] += F128::ONE,
        2 => row.0[5] = F128::new(0, 1 << 63),
        _ => row.0[9] = F128::new(0, 1 << 63),
      }
      let mut output = Vec::new();
      g.eval(&row.0, &(), &mut output);
      assert_eq!(output.last(), Some(&F128::ZERO));
      let table = g.r1cs();
      let boolean = setup
        .drivers
        .iter()
        .map(|d| {
          if d.slot() == slot {
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
      let error = setup.verify(&advice.statement, &bad).unwrap_err();
      eprintln!("recomputed constructor ID attack {attack} rejected: {error}");
      assert!(format!("{error}").contains("Wiring"));
    }
  }
}
