use super::*;
use crate::{
  boolean::generate_boolean_witness,
  ixby::bits::{fill_words, read_words},
};

fn layouts() -> Vec<RecordLayout> {
  vec![
    RecordLayout::new(
      [40, 64, 3, 128, 128].map(RecordLayout::low_bits).to_vec(),
    )
    .unwrap(),
    RecordLayout::new(vec![
      1,
      127 | (RecordLayout::low_bits(40) << 64),
      u128::MAX,
      u128::MAX,
      u128::MAX,
      u128::MAX,
    ])
    .unwrap(),
    // Exercise holes and both endpoints of the bit range in a full-width record.
    RecordLayout::new(
      (0..26)
        .map(|word| {
          if word % 3 == 0 {
            1 | (1 << 127)
          } else if word % 3 == 1 {
            u128::MAX
          } else {
            0
          }
        })
        .collect(),
    )
    .unwrap(),
  ]
}
fn values(masks: &[u128], seed: u128) -> Vec<F128> {
  masks
    .iter()
    .enumerate()
    .map(|(i, mask)| {
      let v = seed.rotate_left((i * 7 % 128) as u32) & mask;
      F128::new(v as u64, (v >> 64) as u64)
    })
    .collect()
}
fn satisfies_at(table: &BlockR1cs, bits: &[bool], row: usize) -> bool {
  let parity =
    |columns: &[usize]| columns.iter().fold(false, |p, &i| p ^ bits[i]);
  (parity(&table.a_0.rows[row]) & parity(&table.b_0.rows[row])) == bits[row]
}

#[test]
fn packing_is_exact_and_removed_bits_cannot_hide_data() {
  for layout in layouts() {
    let pack = RecordPackingGate::new(3, layout.clone(), false).unwrap();
    let unpack = RecordPackingGate::new(3, layout.clone(), true).unwrap();
    for input in [
      values(&layout.masks, u128::MAX),
      values(&layout.masks, 0xabcdef0123456789_fedcba9876543210),
    ] {
      let encoded = pack.output(&input);
      assert_eq!(unpack.output(&encoded), input);
      for (gate, input) in [(&pack, &input), (&unpack, &encoded)] {
        let table = gate.r1cs();
        let mut bits = vec![false; table.n()];
        gate
          .plan()
          .fill_row(&mut bits[..gate.plan().k()], |b| fill_words(input, b));
        assert!(table.satisfies(&bits));
        assert_eq!(
          read_words(&bits, gate.input_count(), gate.output_count()),
          gate.output(input)
        );
        for bit in 0..gate.output_count() * 128 {
          let at = gate.input_count() * 128 + bit;
          bits[at] ^= true;
          assert!(
            !satisfies_at(&table, &bits, at),
            "unpack={} output bit={bit}",
            gate.unpack
          );
          bits[at] ^= true;
        }
        for (word, mask) in gate.input_masks().into_iter().enumerate() {
          for bit in 0..128 {
            if mask >> bit & 1 != 0 {
              continue;
            }
            let at = word * 128 + bit;
            // Recompute all derived columns after inserting the hidden bit.
            // The constraint on that supplied bit must still reject it.
            gate.plan().fill_row(&mut bits[..gate.plan().k()], |b| {
              fill_words(input, b);
              b[at] = true;
            });
            assert!(
              !satisfies_at(&table, &bits, at),
              "unpack={} hidden bit={at}",
              gate.unpack
            );
          }
        }
      }
    }
  }
}

#[test]
fn packed_record_writer_matches_matrices_and_recycled_buffers() {
  for layout in layouts() {
    for unpack in [false, true] {
      let mut gate = RecordPackingGate::new(6, layout.clone(), unpack).unwrap();
      let rows = (0..9)
        .map(|i| {
          RecordPackingRow(values(
            &gate.input_masks(),
            (0xfeedface_cafebeef0123456789_u128).rotate_left(i * 3),
          ))
        })
        .collect::<Vec<_>>();
      for count in [0, 1, 7, 8, 9] {
        let expected =
          generate_boolean_witness(gate.plan(), &rows[..count], 6, |r, b| {
            fill_words(&r.0, b)
          });
        let poison = F128::new(u64::MAX, u64::MAX);
        for elide_padding_writes in [false, true] {
          let mut z = vec![poison; expected.0.len()];
          let mut a = z.clone();
          let mut b = z.clone();
          let stripe = gate.generate_witness_into(
            &rows[..count],
            SlotWitnessDest {
              z: &mut z,
              a: &mut a,
              b: &mut b,
              elide_padding_writes,
            },
          );
          if elide_padding_writes {
            let columns = gate.plan().useful_bits().div_ceil(128);
            for (got, want) in
              [(&z, &expected.0), (&a, &expected.1), (&b, &expected.2)]
            {
              for (at, &value) in got.iter().enumerate() {
                assert_eq!(
                  value,
                  if at / 64 < columns && at % 64 < count.div_ceil(8) * 8 {
                    want[at]
                  } else {
                    poison
                  }
                );
              }
            }
            let live = count.div_ceil(8) * gate.plan().k();
            assert_eq!(stripe[..live], expected.3[..live]);
          } else {
            assert_eq!((z, a, b, stripe), expected);
          }
        }
      }
      gate.nu = 3;
      crate::ixby::test_support::padding(
        gate.plan(),
        &rows[..7],
        |r, b| fill_words(&r.0, b),
        |dst| gate.generate_witness_into(&rows[..7], dst),
      );
    }
  }
}

#[test]
fn untimed_kind_selection_packs_and_restores_complete_records() {
  use crate::{ixby::io::LayoutEmitter, sizing::CircuitEmitter};
  use flock_prover::circuit::builder::ShapeBuilder;
  let mut builder = ShapeBuilder::new(6);
  let mut b = LayoutEmitter::new(&mut builder);
  let slots = super::super::PermutationSlots::declare_packed(
    &mut b,
    6,
    layouts().remove(0),
  )
  .unwrap();
  let mut private = Vec::new();
  let mut expected = Vec::new();
  for lane in 0..super::super::switch::SWITCHES_PER_ROW {
    let selector = lane % 2;
    let records = [0, 1].map(|side| {
      let index = (lane * 2 + side) as u64;
      vec![
        F128::new(index, 0),
        F128::new(u64::MAX - index, 0),
        F128::new(index % 5, 0),
        F128::new(index, !index),
        F128::new(!index, index),
      ]
    });
    private.push(F128::new(selector as u64, 0));
    private.extend(records.iter().flatten().copied());
    expected.extend(&records[selector]);
    expected.extend(&records[1 - selector]);
  }
  let inputs = private.iter().map(|_| b.input()).collect::<Vec<_>>();
  for word in slots.switch_full_records(&mut b, &inputs) {
    b.publish(word);
  }
  let (inputs, public) = b.finish();
  let shape = builder.finish().unwrap();
  let witness = shape.run(&inputs.assign(&private).unwrap(), &[]);
  assert_eq!(witness.public, public.instantiate(&expected).unwrap());
  for (slot, gate) in slots.packing_gates() {
    let table = gate.r1cs();
    let mut bits = vec![false; table.n()];
    for row in witness.rows::<RecordPackingGate>(slot) {
      gate
        .plan()
        .fill_row(&mut bits[..gate.plan().k()], |b| fill_words(&row.0, b));
      assert!(table.satisfies(&bits));
    }
  }
}
