use super::*;
use crate::{
  boolean::generate_boolean_witness,
  hash::{
    Blake3Gate, CHUNK_END, CHUNK_START, ROOT, pack_bytes, pack_params, pack8,
  },
  ixby::io::{InputLayout, LayoutEmitter, PublicLayout},
  sizing::CountingEmitter,
};
use flock_prover::{
  circuit::builder::{CircuitShape, ShapeBuilder},
  union::UnionInstance,
};

pub(super) fn emit(
  b: &mut impl CircuitEmitter,
  nu: usize,
  compressions: usize,
) -> (PackedBlake3, InputLayout, PublicLayout) {
  let mut b = LayoutEmitter::new(b);
  let slots = PackedBlake3::declare(&mut b, nu).unwrap();
  for _ in 0..compressions {
    let input: [Wire; 7] = std::array::from_fn(|_| b.input());
    for output in slots.compress(
      &mut b,
      input[..2].try_into().unwrap(),
      input[2..6].try_into().unwrap(),
      input[6],
    ) {
      b.publish(output);
    }
  }
  let (inputs, public) = b.finish();
  (slots, inputs, public)
}

pub(super) fn setup(
  nu: usize,
) -> (PackedBlake3, InputLayout, PublicLayout, CircuitShape) {
  let mut b = ShapeBuilder::new(nu);
  let (slots, inputs, public) = emit(&mut b, nu, 1);
  (slots, inputs, public, b.finish().unwrap())
}

pub(super) fn expected(input: &[F128; 7]) -> [F128; 4] {
  let mut output = Vec::new();
  Blake3Gate { nu: 3 }.eval(input, &(), &mut output);
  output.try_into().unwrap()
}

fn row_bits(gate: &PackedWordGate, row: &PackedWordRow) -> Vec<bool> {
  let mut bits = vec![false; gate.plan().k()];
  gate.plan().fill_row(&mut bits, |bits| {
    for (i, input) in row.0.iter().enumerate() {
      write_f128(bits, 128 * i, *input);
    }
  });
  bits
}

fn satisfies_row(r1cs: &BlockR1cs, bits: &[bool]) -> bool {
  r1cs.a_0.rows.iter().zip(&r1cs.b_0.rows).zip(bits).all(|((a, b), z)| {
    let parity = |row: &[usize]| row.iter().fold(false, |p, i| p ^ bits[*i]);
    (parity(a) & parity(b)) == *z
  })
}

fn check_row(gate: &PackedWordGate, input: &[F128]) -> Vec<bool> {
  let mut output = Vec::new();
  let row = gate.eval(input, &(), &mut output);
  let bits = row_bits(gate, &row);
  let mut expected = vec![false; output.len() * 128];
  for (i, value) in output.iter().enumerate() {
    write_f128(&mut expected, 128 * i, *value);
  }
  let start = gate.input_count() * 128;
  assert_eq!(&bits[start..start + expected.len()], expected, "{:?}", gate.kind);
  assert!(satisfies_row(&gate.r1cs(), &bits));
  bits
}

fn sample(seed: u64, index: usize) -> F128 {
  // Deterministic conformance data, not proof randomness or a PRNG claim.
  let mix = |x: u64| {
    let x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    let x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
  };
  let x = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(index as u64);
  F128::new(mix(x), mix(x.wrapping_add(0xd134_2543_de82_ef95)))
}

#[test]
fn packed_tables_match_native_words_and_reject_every_single_bit_change() {
  for kind in PackedGateKind::ALL {
    let gate = PackedWordGate::new(3, kind).unwrap();
    for seed in 0..32 {
      let input: Vec<_> =
        (0..gate.input_count()).map(|i| sample(seed, i)).collect();
      check_row(&gate, &input);
    }
    for value in [F128::ZERO, F128::new(u64::MAX, u64::MAX)] {
      check_row(&gate, &vec![value; gate.input_count()]);
    }
    let input: Vec<_> =
      (0..gate.input_count()).map(|i| sample(59, i)).collect();
    let mut bits = check_row(&gate, &input);
    let r1cs = gate.r1cs();
    let mut full = vec![false; r1cs.n()];
    full[..bits.len()].copy_from_slice(&bits);
    assert!(r1cs.satisfies(&full), "including all seven inactive rows");
    assert_eq!(r1cs.const_pin, None);
    for bit in 0..bits.len() {
      bits[bit] ^= true;
      assert!(!satisfies_row(&r1cs, &bits), "{kind:?} unconstrained bit {bit}");
      bits[bit] ^= true;
    }
    let useful = gate.plan().useful_bits();
    assert!(bits[useful..].iter().all(|bit| !*bit));
  }
  assert!(PackedWordGate::new(2, PackedGateKind::Add).is_err());
  assert!(PackedWordGate::new(21, PackedGateKind::Add).is_err());
}

#[test]
fn addition_carries_wrap_without_crossing_packed_lanes() {
  let gate = PackedWordGate::new(3, PackedGateKind::Add).unwrap();
  for bit in 0..32 {
    let low = (1u64 << bit) - 1;
    let input = [
      pack4([low as u32, u32::MAX, 0xaaaa_aaaa, 1 << bit]),
      pack4([1, 1, 0x5555_5555, 1 << bit]),
    ];
    check_row(&gate, &input);
  }
  let input = [pack4([u32::MAX, 0, u32::MAX, 0]), pack4([1, 0, 1, 0])];
  let mut output = Vec::new();
  gate.eval(&input, &(), &mut output);
  assert_eq!(output, [F128::ZERO]);
}

#[test]
fn schedule_routes_every_message_bit_in_every_round() {
  let gate = PackedWordGate::new(3, PackedGateKind::MessageSchedule).unwrap();
  // Independent literal round map, checked against every input basis bit.
  let mut indices: [usize; 16] = std::array::from_fn(|i| i);
  let permutation = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];
  let mut routes = Vec::new();
  for _ in 0..7 {
    for order in [[0, 2, 4, 6], [1, 3, 5, 7], [8, 10, 12, 14], [9, 11, 13, 15]]
    {
      routes.push(order.map(|i| indices[i]));
    }
    indices = permutation.map(|i| indices[i]);
  }
  for bit in 0..512 {
    let mut input = [F128::ZERO; 4];
    let word_bit = bit % 128;
    if word_bit < 64 {
      input[bit / 128].lo = 1 << word_bit;
    } else {
      input[bit / 128].hi = 1 << (word_bit - 64);
    }
    let bits = check_row(&gate, &input);
    for (word, lanes) in routes.iter().enumerate() {
      for (lane, index) in lanes.iter().enumerate() {
        for local_bit in 0..32 {
          assert_eq!(
            bits[512 + word * 128 + lane * 32 + local_bit],
            index * 32 + local_bit == bit,
          );
        }
      }
    }
  }
}

#[test]
fn pooled_witness_matches_full_matrices_and_clears_reused_padding() {
  for kind in PackedGateKind::ALL {
    let gate = PackedWordGate::new(4, kind).unwrap();
    for count in [0, 1, 7, 8, 9, 16] {
      let rows: Vec<_> = (0..count)
        .map(|row| {
          PackedWordRow(
            (0..gate.input_count()).map(|i| sample(row as u64, i)).collect(),
          )
        })
        .collect();
      let expected =
        generate_boolean_witness(gate.plan(), &rows, 4, |row, bits| {
          for (i, input) in row.0.iter().enumerate() {
            write_f128(bits, i * 128, *input);
          }
        });
      let len = gate.plan().k() / 128 * 16;
      let stale = F128::new(u64::MAX, u64::MAX);
      let mut z = vec![stale; len];
      let mut a = vec![stale; len];
      let mut b = vec![stale; len];
      let stripe = gate.generate_witness_into(
        &rows,
        SlotWitnessDest {
          z: &mut z,
          a: &mut a,
          b: &mut b,
          elide_padding_writes: true,
        },
      );
      assert_eq!((z, a, b, stripe), expected, "{kind:?}, count {count}");
    }
  }
}

#[test]
fn complete_compression_matches_upstream_for_arbitrary_private_parameters() {
  let (slots, input_layout, public_layout, shape) = setup(7);
  let identity = shape.circuit.digest();
  for seed in 0..64 {
    let inputs = std::array::from_fn(|i| sample(seed, i));
    let witness = shape.run(&input_layout.assign(&inputs).unwrap(), &[]);
    assert_eq!(
      witness.public,
      public_layout.instantiate(&expected(&inputs)).unwrap()
    );
    for (gate, slot) in slots.gates() {
      for row in witness.rows::<PackedWordGate>(*slot) {
        check_row(gate, &row.0);
      }
    }
    assert_eq!(shape.circuit.digest(), identity);
  }
}

#[test]
fn single_block_hash_matches_independent_blake3_at_every_length() {
  let (_, inputs, public, shape) = setup(7);
  for length in 0..=64 {
    let message: Vec<_> = (0..length).map(|i| (i * 17 + 3) as u8).collect();
    let mut padded = [0u8; 64];
    padded[..length].copy_from_slice(&message);
    let cv = pack8(&IV);
    let mut private = [F128::ZERO; 7];
    private[..2].copy_from_slice(&cv);
    for (i, bytes) in padded.as_chunks::<16>().0.iter().enumerate() {
      private[2 + i] = pack_bytes(bytes);
    }
    private[6] = pack_params(0, length as u32, CHUNK_START | CHUNK_END | ROOT);
    let witness = shape.run(&inputs.assign(&private).unwrap(), &[]);
    let output = expected(&private);
    let digest = ::blake3::hash(&message);
    assert_eq!(
      output[..2],
      [
        pack_bytes(&digest.as_bytes()[..16]),
        pack_bytes(&digest.as_bytes()[16..]),
      ]
    );
    assert_eq!(witness.public, public.instantiate(&output).unwrap());
  }
}

#[test]
fn exact_count_and_shape_agree_for_shared_tables_without_private_data() {
  for compressions in [1, 2, 19] {
    let mut count = CountingEmitter::new();
    let (_, counted_inputs, counted_public) = emit(&mut count, 3, compressions);
    let nu = count.required_nu(9).unwrap();
    let mut builder = ShapeBuilder::new(nu);
    let (slots, inputs, public) = emit(&mut builder, nu, compressions);
    let shape = builder.finish().unwrap();
    count.ensure_matches(&shape).unwrap();
    let (counted_registry, counted_rows) = count.registry(nu);
    assert_eq!(counted_rows, shape.counts);
    assert_eq!(counted_registry.digest(), shape.registry.digest());
    for (counted, compiled) in
      counted_registry.types().iter().zip(shape.registry.types())
    {
      assert_eq!(counted.a_0.rows, compiled.a_0.rows);
      assert_eq!(counted.b_0.rows, compiled.b_0.rows);
      assert_eq!(counted.c_0.rows, compiled.c_0.rows);
    }
    assert_eq!(inputs, counted_inputs);
    assert_eq!(public, counted_public);
    let union = UnionInstance::new(&shape.registry, shape.counts.clone());
    assert_eq!(union.dense_words(), compressions * 632);
    assert!(union.m_total() >= 22);
    assert_eq!(union.dense_m(), 22);
    for (gate, slot) in slots.gates() {
      let per = match gate.kind {
        PackedGateKind::Add => 84,
        PackedGateKind::Xor => 4,
        PackedGateKind::MessageSchedule => 1,
        _ => 14,
      };
      assert_eq!(shape.counts[shape.registry_slot(*slot)], per * compressions);
    }
    let nnz: usize = shape
      .registry
      .types()
      .iter()
      .map(|table| {
        table
          .a_0
          .rows
          .iter()
          .chain(&table.b_0.rows)
          .map(Vec::len)
          .sum::<usize>()
      })
      .sum();
    assert_eq!(nnz, 23_808);
    eprintln!(
      "packed BLAKE3 component: compressions={compressions}, tables={}, nu={nu}, virtual_m={}, dense_m={}, dense_words={}, A+B_nnz={nnz}",
      shape.counts.len(),
      union.m_total(),
      union.dense_m(),
      union.dense_words()
    );
  }
}
