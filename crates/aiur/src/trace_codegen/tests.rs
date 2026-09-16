use super::*;
use crate::execute::IOKeyInfo;

#[allow(unreachable_pub)]
#[rustfmt::skip]
mod generated;

#[cfg(feature = "cuda-trace-codegen")]
#[allow(unreachable_pub)]
#[rustfmt::skip]
mod generated_cuda;

#[cfg(feature = "cuda-trace-codegen")]
mod cuda;
#[cfg(feature = "cuda-trace-codegen")]
#[allow(unreachable_pub)]
#[rustfmt::skip]
pub(crate) mod blake3;
#[cfg(feature = "cuda-trace-codegen")]
#[allow(unreachable_pub)]
#[rustfmt::skip]
pub(crate) mod blake3_cuda;

fn io() -> IOBuffer {
  IOBuffer { data: Default::default(), map: Default::default() }
}

fn circuit_of(program: &Toplevel, function: usize) -> usize {
  program.circuits.iter().position(|c| c.members.contains(&function)).unwrap()
}

fn snapshot(record: &QueryRecord) -> Vec<u64> {
  let mut words = vec![];
  for table in
    record.function_queries.iter().chain(record.memory_queries.values())
  {
    words.push(u64::try_from(table.len()).unwrap());
    for (key, result) in table.iter() {
      words
        .extend(key.iter().chain(result.output).map(|x| x.as_canonical_u64()));
      words.push(result.multiplicity.as_canonical_u64());
    }
  }
  words
}

fn parity(program: &Toplevel, record: &QueryRecord, io: &IOBuffer) -> usize {
  let bound = generated::PROGRAM.bind(program).unwrap();
  let before = snapshot(record);
  let mut checked = 0;
  for (index, queries) in record.function_queries.iter().enumerate() {
    let Some(writer) = bound.function(index) else {
      continue;
    };
    let circuit = circuit_of(program, index);
    for query in 0..queries.len() {
      if queries.get_index(query).unwrap().1.multiplicity == G::ZERO {
        continue;
      }
      let mut seed = vec![u64::MAX; writer.seed_words()];
      writer.pack_row(record, io, query, false, &mut seed).unwrap();
      let mut strict = vec![u64::MAX; writer.seed_words()];
      writer.pack_row(record, io, query, true, &mut strict).unwrap();
      assert_eq!(
        seed, strict,
        "function {index}, query {query}: strict seed differs"
      );
      let encoding = SeedEncoding::for_words(&seed).unwrap();
      let mut packed = vec![0xff; encoding.stride(seed.len()).unwrap()];
      encoding.encode(&seed, &mut packed).unwrap();
      let mut direct =
        vec![0xff; SeedEncoding::U8Payload.stride(seed.len()).unwrap()];
      let fits = writer.pack_u8_row(record, io, query, &mut direct).unwrap();
      assert_eq!(fits, encoding == SeedEncoding::U8Payload);
      if fits {
        assert_eq!(direct, packed, "direct packed seed differs");
      }
      let mut decoded = vec![0; seed.len()];
      encoding.decode(&packed, &mut decoded).unwrap();
      assert_eq!(seed, decoded);
      let expected =
        program.main_row_for_test(circuit, index, query, record, io);
      let mut actual = vec![u64::MAX; expected.len()];
      writer.write_row(&decoded, circuit, &mut actual).unwrap();
      for (column, (actual, expected)) in
        actual.iter().zip(&expected).enumerate()
      {
        assert_eq!(
          *actual,
          expected.as_canonical_u64(),
          "function {index}, query {query}, column {column}"
        );
        assert!(*actual < G::ORDER_U64);
      }
      checked += 1;
    }
  }
  #[cfg(feature = "cuda-trace-codegen")]
  cuda::parity(program, record, io);
  assert_eq!(before, snapshot(record), "packing changed the finalized record");
  checked
}

fn run(function: usize, args: &[u64]) -> usize {
  let program = (generated::PROGRAM.expected)();
  let mut io = io();
  let (record, _) = program
    .execute(function, args.iter().copied().map(G::from_u64).collect(), &mut io)
    .unwrap();
  parity(&program, &record, &io)
}

#[test]
fn canonical_fields_zero_inverses_and_constant_degree() {
  let boundary = [0, 1, 2, 255, 256, (1 << 32) - 1, 1 << 32, G::ORDER_U64 - 1];
  for a in boundary {
    for b in boundary {
      assert_eq!(run(0, &[a, b]), 1);
    }
  }
  assert_eq!(run(12, &[]), 1);
}

#[test]
fn byte_operations_and_virtual_carries() {
  let boundary = [0, 1, 15, 16, 127, 128, 254, 255];
  for a in boundary {
    for b in boundary {
      assert_eq!(run(1, &[a, b]), 1);
    }
  }
}

#[test]
fn u32_boundaries_and_virtual_values() {
  let boundary = [0_u32, 1, 255, 256, 1 << 31, u32::MAX];
  for a in boundary {
    for b in boundary {
      let args: Vec<_> = [a, b, u32::MAX]
        .iter()
        .flat_map(|word| word.to_le_bytes().map(u64::from))
        .collect();
      assert_eq!(run(2, &args), 1);
    }
  }
}

#[test]
fn branch_columns_and_grouped_member_offsets() {
  for tag in [0, 1, 2, G::ORDER_U64 - 1] {
    for value in [0, 1, 127, 255] {
      assert_eq!(run(3, &[tag, value]), 1);
    }
  }
  let program = (generated::PROGRAM.expected)();
  let mut record = QueryRecord::new(&program);
  let mut io = io();
  for (function, args) in [
    (0, vec![G::ZERO, -G::ONE]),
    (3, vec![G::ONE, G::from_u8(255)]),
    (12, vec![]),
  ] {
    program.execute_in(function, args, &mut io, &mut record).unwrap();
  }
  assert_eq!(parity(&program, &record, &io), 3);
}

#[test]
fn call_load_dependencies_and_nonzero_pointer_namespace() {
  let program = (generated::PROGRAM.expected)();
  for base in [0, 1024, 1 << 30] {
    let mut io = io();
    let (record, _) = program
      .execute_with_pointer_base(4, vec![G::from_u8(7)], &mut io, base)
      .unwrap();
    assert_eq!(parity(&program, &record, &io), 2);
  }
}

#[test]
fn strict_alias_verification_and_unconstrained_calls() {
  for value in [0, 7, G::ORDER_U64 - 1] {
    assert_eq!(run(6, &[value]), 2);
    assert!(run(14, &[value]) >= 1);
  }
  let program = (generated::PROGRAM.expected)();
  let mut record = QueryRecord::new(&program);
  record.function_queries[6].insert(&[G::ZERO], &[G::ONE], G::ONE).unwrap();
  record.function_queries[5].insert(&[G::ZERO], &[G::ZERO], G::ONE).unwrap();
  let bound = generated::PROGRAM.bind(&program).unwrap();
  let writer = bound.function(6).unwrap();
  let mut seed = vec![0; writer.seed_words()];
  writer.pack_row(&record, &io(), 0, false, &mut seed).unwrap();
  let error = writer.pack_row(&record, &io(), 0, true, &mut seed).unwrap_err();
  assert_eq!(error.function, 6);
  assert_eq!(error.operation, Some(1));
  assert_eq!(error.query, Some(0));
  assert!(error.detail.contains("alias disagrees"));
}

#[test]
fn early_returns_do_not_resolve_unexecuted_reads() {
  for function in [8, 9] {
    assert_eq!(run(function, &[0]), 1);
    let program = (generated::PROGRAM.expected)();
    let mut record = QueryRecord::with_pointer_base(&program, 7);
    record
      .memory_queries
      .get_mut(&1)
      .unwrap()
      .insert(&[G::from_u8(42)], &[G::from_u8(7)], G::ZERO)
      .unwrap();
    let mut io = io();
    program
      .execute_in(function, vec![G::from_u8(7)], &mut io, &mut record)
      .unwrap();
    assert_eq!(parity(&program, &record, &io), 1);
    record.memory_queries.clear();
    let bound = generated::PROGRAM.bind(&program).unwrap();
    let writer = bound.function(function).unwrap();
    let mut seed = vec![0; writer.seed_words()];
    let error = writer.pack_row(&record, &io, 0, false, &mut seed).unwrap_err();
    assert!(error.detail.contains("missing loaded values"));
  }
}

#[test]
fn io_reads_and_shared_branch_seed_slots() {
  let program = (generated::PROGRAM.expected)();
  let channel = G::from_u8(3);
  let mut io = io();
  io.data.insert(channel, vec![G::ONE, G::TWO, G::from_u8(77)]);
  io.map.insert((channel, vec![G::from_u8(12)]), IOKeyInfo { idx: 0, len: 2 });
  let (record, _) =
    program.execute(7, vec![channel, G::from_u8(12)], &mut io).unwrap();
  assert_eq!(parity(&program, &record, &io), 1);
  for tag in [0, 1] {
    let (record, _) =
      program.execute(10, vec![G::from_u64(tag), channel], &mut io).unwrap();
    assert_eq!(parity(&program, &record, &io), 1);
  }
}

fn store_list(record: &mut QueryRecord, limbs: &[u64]) -> G {
  let table = record.memory_queries.get_mut(&10).unwrap();
  let mut nil = [G::ZERO; 10];
  nil[0] = G::ONE;
  if table.is_empty() {
    table.insert(&nil, &[G::from_usize(record.pointer_base)], G::ZERO).unwrap();
  }
  let mut pointer = G::from_usize(record.pointer_base);
  for limb in limbs.iter().rev() {
    let mut node = [G::ZERO; 10];
    node[1..9].copy_from_slice(&limb.to_le_bytes().map(G::from_u8));
    node[9] = pointer;
    pointer = if let Some(query) = table.get(&node) {
      query.output[0]
    } else {
      let pointer = G::from_usize(record.pointer_base + table.len());
      table.insert(&node, &[pointer], G::ZERO).unwrap();
      pointer
    };
  }
  pointer
}

#[test]
fn big_uint_results_resolve_existing_list_nodes() {
  let program = (generated::PROGRAM.expected)();
  for base in [0, 4096] {
    for divisor in [vec![], vec![7], vec![3, 2]] {
      let mut record = QueryRecord::with_pointer_base(&program, base);
      let a = store_list(&mut record, &[u64::MAX, 9]);
      let b = store_list(&mut record, &divisor);
      let mut io = io();
      program.execute_in(11, vec![a, b], &mut io, &mut record).unwrap();
      assert_eq!(parity(&program, &record, &io), 1);
    }
  }
}

#[test]
fn zero_output_reads_do_not_need_seeds() {
  let program = (generated::PROGRAM.expected)();
  let mut record = QueryRecord::new(&program);
  record
    .memory_queries
    .get_mut(&0)
    .unwrap()
    .insert(&[], &[G::ZERO], G::ZERO)
    .unwrap();
  let mut io = io();
  program.execute_in(15, vec![G::ZERO], &mut io, &mut record).unwrap();
  assert_eq!(parity(&program, &record, &io), 2);
}

#[test]
fn current_blake3_bytecode_all_stages_and_negative_multiplicities() {
  let program = (generated::PROGRAM.expected)();
  assert_eq!(program.functions[17].layout.width(), 533);
  let bound = generated::PROGRAM.bind(&program).unwrap();
  let writer = bound.function(17).unwrap();
  assert_eq!(writer.seed_words(), 162);
  assert_eq!(SeedEncoding::U8Payload.stride(writer.seed_words()), Some(176));
  for sample in 0..4 {
    let mut state = 0x12345678_u64 + sample;
    let mut args = vec![G::ZERO];
    for _ in 0..128 {
      state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
      args.push(G::from_u8((state >> 56) as u8));
    }
    let mut io = io();
    let (mut record, _) = program.execute(17, args, &mut io).unwrap();
    assert_eq!(record.function_queries[17].len(), 8);
    for i in 0..8 {
      *record.function_queries[17].get_index_mut(i).unwrap().1 =
        if i % 2 == 0 { -G::ONE } else { G::from_u64(1 << 40) };
    }
    assert_eq!(parity(&program, &record, &io), 8);
    let mut seed = vec![0; writer.seed_words()];
    writer.pack_row(&record, &io, 7, true, &mut seed).unwrap();
    drop(record);
    let mut row = vec![0; 533];
    writer.write_row(&seed, circuit_of(&program, 17), &mut row).unwrap();
  }
}

#[test]
fn partial_coverage_keeps_library_and_descriptor_checks() {
  let program = (generated::PROGRAM.expected)();
  let mut functions = generated::PROGRAM.functions.to_vec();
  functions[0] = None;
  let mut partial = GeneratedProgram {
    fingerprint: generated::PROGRAM.fingerprint,
    complete: true,
    expected: generated::PROGRAM.expected,
    functions: Box::leak(functions.into_boxed_slice()),
  };
  assert!(partial.bind(&program).is_err());
  partial.complete = false;
  let bound = partial.bind(&program).unwrap();
  assert!(bound.function(0).is_none());
  assert!(bound.function(1).is_some());
  let mut changed = (generated::PROGRAM.expected)();
  changed.functions[0].body.ops.push(crate::bytecode::Op::Const(G::ONE));
  assert!(partial.bind(&changed).is_err());
  let mut functions = partial.functions.to_vec();
  functions[13] = functions[1];
  partial.functions = Box::leak(functions.into_boxed_slice());
  assert!(partial.bind(&program).is_err());
}

#[test]
fn library_binding_rejects_changed_callees_and_grouping() {
  let mut program = (generated::PROGRAM.expected)();
  program.functions[13].body.ops.push(crate::bytecode::Op::Const(G::ONE));
  assert!(generated::PROGRAM.bind(&program).is_err());
  let mut program = (generated::PROGRAM.expected)();
  program.circuits[0].members.swap(0, 1);
  assert!(generated::PROGRAM.bind(&program).is_ok());
  program.circuits[0].members.push(0);
  assert!(generated::PROGRAM.bind(&program).is_err());
  let mut program = (generated::PROGRAM.expected)();
  let Ctrl::MatchContinue(_, arms, ..) = &mut program.functions[3].body.ctrl
  else {
    unreachable!()
  };
  arms.swap_indices(0, 1);
  assert!(generated::PROGRAM.bind(&program).is_err());
}

#[test]
fn seed_codec_guards_and_wide_fallback() {
  for words in [
    vec![G::ORDER_U64 - 1, 0, 255],
    vec![1 << 40, 256, 1 << 32],
    vec![1, G::ORDER_U64 - 1],
  ] {
    let encoding = SeedEncoding::for_words(&words).unwrap();
    assert_eq!(
      encoding,
      if words[1..].iter().all(|&w| w < 256) {
        SeedEncoding::U8Payload
      } else {
        SeedEncoding::Canonical
      }
    );
    let mut bytes = vec![0; encoding.stride(words.len()).unwrap()];
    encoding.encode(&words, &mut bytes).unwrap();
    let mut decoded = vec![0; words.len()];
    encoding.decode(&bytes, &mut decoded).unwrap();
    assert_eq!(words, decoded);
  }
  assert!(SeedEncoding::U8Payload.encode(&[1, 256], &mut [0; 16]).is_err());
  assert!(SeedEncoding::for_words(&[G::ORDER_U64]).is_err());
  assert!(SeedEncoding::for_words(&[]).is_err());
  assert!(
    SeedEncoding::Canonical
      .decode(&G::ORDER_U64.to_le_bytes(), &mut [0])
      .is_err()
  );
  let mut padded = [0; 16];
  padded[15] = 1;
  assert!(SeedEncoding::U8Payload.decode(&padded, &mut [0; 2]).is_err());
}

#[test]
fn scalar_rejects_noncanonical_seed_words() {
  let program = (generated::PROGRAM.expected)();
  let bound = generated::PROGRAM.bind(&program).unwrap();
  let writer = bound.function(0).unwrap();
  let mut seed = vec![0; writer.seed_words()];
  seed[0] = G::ORDER_U64;
  let mut row = vec![0; program.circuits[0].layout.width()];
  assert!(writer.write_row(&seed, 0, &mut row).is_err());
}

#[test]
fn nested_yields_compute_host_read_keys() {
  let program = (generated::PROGRAM.expected)();
  let mut io = io();
  let channel = G::from_u8(3);
  io.data.insert(channel, vec![G::ZERO, G::ONE, G::TWO, G::from_u8(3)]);
  for outer in [0, 1] {
    for inner in [0, 1, 2] {
      let (record, _) = program
        .execute(
          18,
          vec![G::from_u8(outer), channel, G::from_u8(inner)],
          &mut io,
        )
        .unwrap();
      assert_eq!(parity(&program, &record, &io), 1);
    }
  }
}

#[test]
fn missing_match_and_inactive_queries_are_rejected() {
  let program = (generated::PROGRAM.expected)();
  let mut io = io();
  let (mut record, _) = program.execute(19, vec![G::ZERO], &mut io).unwrap();
  assert_eq!(parity(&program, &record, &io), 1);
  let bound = generated::PROGRAM.bind(&program).unwrap();
  let writer = bound.function(19).unwrap();
  let mut seed = vec![0; writer.seed_words()];
  writer.pack_row(&record, &io, 0, false, &mut seed).unwrap();
  seed[1] = 7;
  let circuit = circuit_of(&program, 19);
  let mut row = vec![0; program.circuits[circuit].layout.width()];
  let error = writer.write_row(&seed, circuit, &mut row).unwrap_err();
  assert!(error.detail.contains("no match"));
  *record.function_queries[19].get_index_mut(0).unwrap().1 = G::ZERO;
  assert!(writer.pack_row(&record, &io, 0, false, &mut seed).is_err());
  seed[0] = 0;
  assert!(writer.write_row(&seed, circuit, &mut row).is_err());
}

#[test]
fn canonical_wide_words_preserve_u128_carries() {
  for value in [0, 255, 256, 1 << 32, G::ORDER_U64 - 1] {
    assert_eq!(run(20, &[value; 12]), 1);
  }
}

#[test]
fn current_u64_multiply_bytecode_boundaries() {
  for a in [0_u64, 1, 255, 65535, 1 << 32, u64::MAX] {
    for b in [0_u64, 1, 65536, u64::MAX] {
      let args: Vec<_> = a
        .to_le_bytes()
        .into_iter()
        .chain(b.to_le_bytes())
        .map(u64::from)
        .collect();
      assert_eq!(run(21, &args), 1);
    }
  }
}
