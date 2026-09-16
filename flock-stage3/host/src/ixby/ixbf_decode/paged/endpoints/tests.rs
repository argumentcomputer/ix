use super::*;
use crate::ixby::{
  auth_memory::{MemoryDepth, SparseMemory},
  ixbf::DecodeLimits,
  ixbf_decode::{
    dispatch::DISPATCH_CONTEXT_INDICES,
    paged::{
      code_capture::batch::{CodeCaptureWitness, CompiledCodeCapture},
      commitment_bridge::{
        ArtifactDomain, CommitmentBridgeWitness, CompiledCommitmentBridge,
      },
      constructor_ids::{CompiledConstructorIds, ConstructorIdsAdvice},
      input_capture::batch::{CompiledInputCapture, InputCaptureWitness},
      output_bytes::{CompiledOutputBytes, OutputBytesWitness},
      references::{CompiledReferences, ReferenceWitness},
      source_bytes::{CompiledSourceBytes, SourceBank, SourceBytesWitness},
    },
  },
  paged_exec::{BatchClass, CompiledPagedExecution, NativeImage},
};
use flock_prover::circuit::builder::GateType;

const IDENTITY: &[u8] = &[
  b'I', b'X', b'B', b'F', 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 8, 0x80,
  0x20, 64, 64, 24, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0,
];
fn profile() -> FunctionalProfile {
  FunctionalProfile::new([1, 0, 1, 1, 1, 0, 8, 4096, 64, 64], 24).unwrap()
}
// Join independently emitted actual statements. This helper checks every
// component circuit; it is never part of the endpoint or recursive verifier.
fn fixture(payload: &[u8]) -> EndpointAdvice {
  let mut input = b"IXFI\x01\0\0\0\0\0\0\0\x01\0\x06".to_vec();
  input.push(payload.len() as u8);
  input.extend(payload);
  let mut output = b"IXFO\x01\0\0\0\0\0\0\0\0\x06".to_vec();
  output.push(payload.len() as u8);
  output.extend(payload);
  let mut memory = SparseMemory::new(MemoryDepth::new(40).unwrap());
  let mut components: Vec<Vec<F128>> = Vec::new();
  fn joined(
    acc: &mut Option<Vec<F128>>,
    next: &[F128],
    shared: usize,
    boundary: usize,
  ) {
    if let Some(prev) = acc {
      assert_eq!(&prev[..shared], &next[..shared]);
      assert_eq!(&prev[shared + boundary..], &next[shared..shared + boundary]);
      prev[shared + boundary..].copy_from_slice(&next[shared + boundary..]);
    } else {
      *acc = Some(next.to_vec());
    }
  }
  let setup = CompiledSourceBytes::compile(SourceBank::Program).unwrap();
  let mut walk =
    SourceBytesWitness::new(SourceBank::Program, IDENTITY).unwrap();
  let mut whole = None;
  while let Some(a) = walk.next_batch(&mut memory).unwrap() {
    setup.check_advice(&a).unwrap();
    joined(&mut whole, a.statement.words(), 3, 3);
  }
  components.push(whole.unwrap());
  drop(setup);
  let setup = CompiledCodeCapture::compile().unwrap();
  let mut walk = CodeCaptureWitness::new(IDENTITY).unwrap();
  let mut whole = None;
  while let Some(a) = walk.next_batch(&mut memory).unwrap() {
    setup.check_advice(&a).unwrap();
    joined(&mut whole, a.statement.words(), 3, 39);
  }
  let context = DISPATCH_CONTEXT_INDICES.map(|i| walk.parser()[i]);
  components.push(whole.unwrap());
  drop(setup);
  let setup = CompiledReferences::compile().unwrap();
  let mut walk =
    ReferenceWitness::new([context[1], context[0], context[12]]).unwrap();
  let mut whole = None;
  while let Some(a) = walk.next_batch(&mut memory).unwrap() {
    setup.check_advice(&a).unwrap();
    joined(&mut whole, a.statement.words(), 5, 3);
  }
  components.push(whole.unwrap());
  drop(setup);
  let setup = CompiledConstructorIds::compile().unwrap();
  let a = ConstructorIdsAdvice::new(&mut memory, 0).unwrap();
  setup.check_advice(&a).unwrap();
  components.push(a.statement.words().to_vec());
  drop(setup);
  let setup = CompiledSourceBytes::compile(SourceBank::Input).unwrap();
  let mut walk = SourceBytesWitness::new(SourceBank::Input, &input).unwrap();
  let mut whole = None;
  while let Some(a) = walk.next_batch(&mut memory).unwrap() {
    setup.check_advice(&a).unwrap();
    joined(&mut whole, a.statement.words(), 3, 3);
  }
  components.push(whole.unwrap());
  drop(setup);
  let setup = CompiledInputCapture::compile().unwrap();
  let mut walk = InputCaptureWitness::new(&input, context).unwrap();
  let mut whole = None;
  while let Some(a) = walk.next_batch(&mut memory).unwrap() {
    setup.check_advice(&a).unwrap();
    joined(&mut whole, a.statement.words(), 3, 37);
  }
  components.push(whole.unwrap());
  drop(setup);
  let image =
    NativeImage::load(IDENTITY, &input, DecodeLimits::default()).unwrap();
  assert_eq!(memory.root(), image.memory.root());
  let setup = CompiledPagedExecution::compile(BatchClass::Small).unwrap();
  let mut machine = image.machine().unwrap();
  let mut whole = None;
  while let Some(a) = machine.batch(BatchClass::Small, &mut memory).unwrap() {
    setup.check_advice(&a).unwrap();
    joined(&mut whole, &a.expected, 3, 27);
  }
  components.push(whole.unwrap());
  drop(setup);
  assert_eq!(machine.state[0], F128::new(2, 0));
  let setup = CompiledOutputBytes::compile().unwrap();
  let mut walk =
    OutputBytesWitness::new(&output, [machine.state[2], machine.state[3]])
      .unwrap();
  let mut whole = None;
  while let Some(a) = walk.next_batch(&mut memory).unwrap() {
    setup.check_advice(&a).unwrap();
    joined(&mut whole, a.statement.words(), 7, 1);
  }
  components.push(whole.unwrap());
  drop(setup);
  let p = profile();
  let mut parent = p.digest();
  for (domain, raw) in [
    (ArtifactDomain::Program, IDENTITY),
    (ArtifactDomain::Input, input.as_slice()),
    (ArtifactDomain::Output, output.as_slice()),
  ] {
    let setup = CompiledCommitmentBridge::compile(domain).unwrap();
    let mut walk = CommitmentBridgeWitness::new(domain, raw, parent).unwrap();
    let mut whole = None;
    while let Some(a) = walk.next_batch().unwrap() {
      setup.check_advice(&a).unwrap();
      joined(&mut whole, a.statement.words(), 7, 1);
    }
    if domain == ArtifactDomain::Program {
      parent = walk.digest();
    }
    components.push(whole.unwrap());
  }
  let facts = EndpointFacts::assemble(
    components
      .iter()
      .map(Vec::as_slice)
      .collect::<Vec<_>>()
      .try_into()
      .unwrap(),
  )
  .unwrap();
  let a = EndpointAdvice::new(&p, facts).unwrap();
  assert_eq!(
    a.statement.digest(),
    crate::ixby::commitment::tests::native(
      &p.encode(),
      IDENTITY,
      &input,
      &output
    )[4]
  );
  a
}

#[test]
fn functional_profile_encoding_is_explicit_canonical_and_full_width() {
  let p = profile();
  assert_eq!(FunctionalProfile::decode(&p.encode()).unwrap(), p);
  for at in 0..16 {
    let mut bad = p.encode();
    bad[at] ^= 1;
    assert!(FunctionalProfile::decode(&bad).is_err());
  }
  assert!(FunctionalProfile::decode(&p.encode()[..183]).is_err());
  let mut limits = *p.limits();
  limits[0] = u128::MAX;
  let wide = FunctionalProfile::new(limits, u64::MAX).unwrap();
  assert_eq!(FunctionalProfile::decode(&wide.encode()).unwrap(), wide);
  assert_ne!(wide.digest(), p.digest());
  limits[3] = 1 << 64;
  assert!(FunctionalProfile::new(limits, 0).is_err());
}

#[test]
fn endpoint_integer_gates_constrain_exact_eof_and_nonwrapping_progress() {
  let mut cases = Vec::new();
  for length in [0, 1, 31, 32, 33, 976, 977, 1023, 1024, 1025, 1 << 24] {
    for op in [EndpointOp::Source, EndpointOp::Bridge, EndpointOp::Bytes] {
      let (first, count) = match op {
        EndpointOp::Source => {
          (F128::new(length, 0), length.div_ceil(1024).max(1))
        },
        EndpointOp::Bridge => {
          (F128::new(length, 0), (length + 48).div_ceil(1024))
        },
        _ => (F128::new(0x1234, length), length.div_ceil(32).max(1)),
      };
      cases.push((op, [first, F128::new(count, 0), F128::ZERO, F128::ZERO]));
    }
    cases.push((
      EndpointOp::Parser,
      [
        F128::new(length, 0),
        F128::new(0, length),
        F128::new(length, length),
        F128::new(20, 0),
      ],
    ));
  }
  for count in [0, 1, 681, 1024] {
    cases.push((
      EndpointOp::References,
      [
        F128::new(count, 0),
        F128::new(3 | count << 8, 0),
        F128::ZERO,
        F128::ZERO,
      ],
    ));
  }
  cases.push((
    EndpointOp::Clock,
    [F128::ZERO, F128::new((1 << 59) - 1, 0), F128::ZERO, F128::ZERO],
  ));
  for (op, input) in cases {
    let gate = EndpointGate::new(3, op).unwrap();
    let mut out = Vec::new();
    let row = gate.eval(&input, &(), &mut out);
    assert_eq!(out, [F128::ZERO], "{op:?} {input:?}");
    let table = gate.r1cs();
    let mut bits = vec![false; table.n()];
    gate.plan().fill_row(&mut bits[..gate.plan().k()], |b| {
      crate::ixby::bits::fill_words(&input, b)
    });
    assert!(table.satisfies(&bits));
    bits[4 * 128] ^= true;
    assert!(!table.satisfies(&bits));
    for bit in [0, 63, 64, 127] {
      let mut bad = input;
      if bit < 64 {
        bad[1].lo ^= 1 << bit;
      } else {
        bad[1].hi ^= 1 << (bit - 64);
      }
      if op == EndpointOp::Clock && bit == 0 {
        bad[1] = bad[0];
      }
      let mut out = Vec::new();
      gate.eval(&bad, &(), &mut out);
      assert_eq!(out, [F128::ONE], "{op:?} changed boundary {bit}");
    }
    let rows = [row];
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |r, b| crate::ixby::bits::fill_words(&r.0, b),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
}

#[test]
fn actual_components_bind_complete_initialization_halt_and_commitments() {
  let a = fixture(b"complete original-format execution");
  let setup = CompiledEndpoints::compile(profile()).unwrap();
  setup.check_advice(&a).unwrap();
  for (component, indices) in [
    (Component::ProgramBytes, vec![0, 1, 3, 4, 6, 7]),
    (
      Component::CodeCapture,
      vec![1, 3, 4, 33, 40, 42, 44, 45, 46, 56, 69, 70, 71, 72, 79],
    ),
    (Component::References, (0..11).collect()),
    (Component::ConstructorIds, (0..3).collect()),
    (Component::InputBytes, vec![0, 1, 3, 4, 6, 7]),
    (
      Component::InputCapture,
      vec![
        1, 3, 4, 5, 17, 30, 31, 32, 33, 38, 40, 42, 54, 67, 68, 69, 70, 71, 72,
        73, 74, 75,
      ],
    ),
    (
      Component::Execution,
      (0..30).chain([30, 31, 32, 35, 36, 55, 56]).collect(),
    ),
    (Component::OutputBytes, (0..9).collect()),
    (Component::ProgramCommitment, vec![0, 1, 2, 3, 4, 5, 6, 7, 8]),
    (Component::InputCommitment, vec![0, 1, 2, 3, 4, 7, 8]),
    (Component::OutputCommitment, vec![0, 1, 2, 3, 4, 7, 8]),
  ] {
    for i in indices {
      let mut facts = *a.facts.words();
      facts[component.range().start + i].hi ^= 1 << 63;
      let bad = EndpointAdvice::new(
        &profile(),
        EndpointFacts::from_words(&facts).unwrap(),
      )
      .unwrap();
      assert!(setup.check_advice(&bad).is_err(), "unbound {component:?}[{i}]");
    }
  }
  let mut wrong = profile().encode();
  wrong[176] += 1;
  let wrong = FunctionalProfile::decode(&wrong).unwrap();
  let other = CompiledEndpoints::compile(wrong).unwrap();
  assert_ne!(
    setup.public_template().digest(),
    other.public_template().digest()
  );
  assert!(other.check_advice(&a).is_err());
}

#[test]
fn empty_bytes_preserve_the_virtual_output_window_in_the_complete_chain() {
  let advice = fixture(&[]);
  let output = advice.facts.component(Component::OutputBytes);
  assert_eq!(output[6], F128::ZERO);
  assert_eq!(&output[7..], &[F128::ZERO, F128::ONE]);
  CompiledEndpoints::compile(profile()).unwrap().check_advice(&advice).unwrap();
}

const CHILD: &str = "IXBY_ENDPOINT_VERIFY_CHILD";
const TEST: &str = "ixby::ixbf_decode::paged::endpoints::tests::endpoint_proof_binds_every_fact_and_rejects_recomputed_valid_rows";
fn fresh_verify(statement: &EndpointStatement, proof: &[u8]) {
  use std::{
    io::Write,
    process::{Command, Stdio},
  };
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
  for v in statement.words() {
    stdin.write_all(&v.lo.to_le_bytes()).unwrap();
    stdin.write_all(&v.hi.to_le_bytes()).unwrap();
  }
  stdin.write_all(proof).unwrap();
  drop(stdin);
  let output = child.wait_with_output().unwrap();
  assert!(
    output.status.success(),
    "{}{}",
    String::from_utf8_lossy(&output.stdout),
    String::from_utf8_lossy(&output.stderr)
  );
}

#[test]
#[ignore = "real endpoint proof, fresh statement-only receiver, every public fact and recomputed witness attacks"]
fn endpoint_proof_binds_every_fact_and_rejects_recomputed_valid_rows() {
  use crate::hash::{Blake3Gate, pack_bytes};
  use flock_prover::{
    prover::UnionSlotProverInput, r1cs_hashes::blake3 as flock_blake3,
  };
  use std::{io::Read, time::Instant};
  if std::env::var_os(CHILD).is_some() {
    let setup = CompiledEndpoints::compile(profile()).unwrap();
    let mut bytes = Vec::new();
    std::io::stdin()
      .take(8 * 1024 * 1024 + 16 * PUBLIC_WORDS as u64 + 1)
      .read_to_end(&mut bytes)
      .unwrap();
    assert!(bytes.len() > 16 * PUBLIC_WORDS);
    let expected = bytes[..16 * PUBLIC_WORDS]
      .as_chunks::<16>()
      .0
      .iter()
      .map(|v| pack_bytes(v))
      .collect::<Vec<_>>();
    setup
      .verify(
        &EndpointStatement::from_words(&expected).unwrap(),
        &bytes[16 * PUBLIC_WORDS..],
      )
      .unwrap();
    return;
  }
  let advice = fixture(b"complete original-format execution");
  let started = Instant::now();
  let setup = CompiledEndpoints::compile(profile()).unwrap();
  let setup_time = started.elapsed();
  let started = Instant::now();
  let proof = setup.prove(&advice).unwrap();
  eprintln!(
    "endpoint proof: {} bytes, setup {:?}, witness+prove {:?}, M={}",
    proof.len(),
    setup_time,
    started.elapsed(),
    setup.pcs_params().m
  );
  setup.verify(&advice.statement, &proof).unwrap();
  fresh_verify(&advice.statement, &proof);
  for at in 0..PUBLIC_WORDS {
    for high in [false, true] {
      let mut expected = *advice.statement.words();
      if high {
        expected[at].hi ^= 1 << 63;
      } else {
        expected[at].lo ^= 1;
      }
      assert!(
        setup
          .verify(&EndpointStatement::from_words(&expected).unwrap(), &proof)
          .is_err(),
        "unbound public {at}, high={high}"
      );
    }
  }
  let mut bad = proof.clone();
  bad.pop();
  assert!(setup.verify(&advice.statement, &bad).is_err());
  let mut bad = proof.clone();
  bad.push(0);
  assert!(setup.verify(&advice.statement, &bad).is_err());
  let mut changed = profile().encode();
  changed[176] += 1;
  let other =
    CompiledEndpoints::compile(FunctionalProfile::decode(&changed).unwrap())
      .unwrap();
  assert!(other.verify(&advice.statement, &proof).is_err());
  drop(other);
  let witness = setup.witness(&advice).unwrap();
  for (index, at, name) in
    [(0, 3, "ParserDoneMetadata"), (1, 0, "SourceLength"), (5, 1, "FinalClock")]
  {
    let (slot, gate) = &setup.emission.gates[index];
    let mut rows = witness.rows::<EndpointGate>(*slot).to_vec();
    let mut changed = rows[0].0.clone();
    if index == 0 {
      changed[at].hi ^= 1;
    } else {
      changed[at].lo += 1;
    }
    let mut out = Vec::new();
    rows[0] = gate.eval(&changed, &(), &mut out);
    assert_eq!(out, [F128::ZERO], "locally valid {name}");
    let table = gate.r1cs();
    let mut drivers =
      setup.drivers.iter().map(|d| d.prover(&witness)).collect::<Vec<_>>();
    drivers[setup.shape.registry_slot(*slot)] = UnionSlotProverInput::in_place(
      |dst| gate.generate_witness_into(&rows, dst),
      table.csc_lincheck_circuit(),
    );
    let bad = setup.prove_rows(&witness, drivers).unwrap();
    let error = setup.verify(&advice.statement, &bad).unwrap_err();
    assert!(format!("{error:?}").contains("Wiring"));
    eprintln!("recomputed {name} rejected: {error}");
  }
  let code = advice.facts.component(Component::CodeCapture);
  let input = advice.facts.component(Component::InputCapture);
  let (slot, gate) = setup.emission.initialize.gate();
  let mut changed = DISPATCH_CONTEXT_INDICES.map(|i| code[42 + i]).to_vec();
  changed.extend(&input[70..75]);
  changed[14].lo += 1;
  let mut out = Vec::new();
  let row = gate.eval(&changed, &(), &mut out);
  assert_eq!(out[27], F128::ZERO);
  let rows = [row];
  let table = gate.r1cs();
  let mut drivers =
    setup.drivers.iter().map(|d| d.prover(&witness)).collect::<Vec<_>>();
  drivers[setup.shape.registry_slot(slot)] = UnionSlotProverInput::in_place(
    |dst| gate.generate_witness_into(&rows, dst),
    table.csc_lincheck_circuit(),
  );
  let bad = setup.prove_rows(&witness, drivers).unwrap();
  let error = setup.verify(&advice.statement, &bad).unwrap_err();
  assert!(format!("{error:?}").contains("Wiring"));
  eprintln!("recomputed InitialBudget rejected: {error}");
  let exec = advice.facts.component(Component::Execution);
  let (slot, gate) = setup.emission.finalize.gate();
  let mut changed = exec[..3].to_vec();
  changed.extend(&exec[31..55]);
  changed
    .extend([advice.facts.component(Component::ProgramBytes)[0], input[0]]);
  changed[6].hi -= 1;
  let mut out = Vec::new();
  let row = gate.eval(&changed, &(), &mut out);
  assert_eq!(out[3], F128::ZERO);
  let rows = [row];
  let table = gate.r1cs();
  let mut drivers =
    setup.drivers.iter().map(|d| d.prover(&witness)).collect::<Vec<_>>();
  drivers[setup.shape.registry_slot(slot)] = UnionSlotProverInput::in_place(
    |dst| gate.generate_witness_into(&rows, dst),
    table.csc_lincheck_circuit(),
  );
  let bad = setup.prove_rows(&witness, drivers).unwrap();
  let error = setup.verify(&advice.statement, &bad).unwrap_err();
  assert!(format!("{error:?}").contains("Wiring"));
  eprintln!("recomputed FinalResult rejected: {error}");
  let slot = setup.emission.hashes[0].compression_slot();
  let mut rows = witness.rows::<Blake3Gate>(slot).to_vec();
  rows[0].1[4] ^= 1;
  let table = flock_blake3::build_block_r1cs(NU);
  let mut drivers =
    setup.drivers.iter().map(|d| d.prover(&witness)).collect::<Vec<_>>();
  drivers[setup.shape.registry_slot(slot)] = UnionSlotProverInput::in_place(
    |mut dst| {
      dst.elide_padding_writes = false;
      flock_blake3::generate_witness_batch_major_partial_into(&rows, NU, dst)
    },
    table.csc_lincheck_circuit(),
  );
  let bad = setup.prove_rows(&witness, drivers).unwrap();
  let error = setup.verify(&advice.statement, &bad).unwrap_err();
  assert!(format!("{error:?}").contains("Wiring"));
  eprintln!("recomputed ProfileHash rejected: {error}");
}
