//! Generic Flock BLAKE3 compression gate and canonical little-endian packing.
//! Extracted without the historical Stage 2 statement-binding relation.

use flock_prover::{
  circuit::builder::{GateType, SlotWitness},
  field::F128,
  r1cs_hashes::blake3,
  schedule::TableType,
};

const WORD_BYTES: usize = 16;

pub const CHUNK_START: u32 = 1 << 0;
pub const CHUNK_END: u32 = 1 << 1;
pub const PARENT: u32 = 1 << 2;
pub const ROOT: u32 = 1 << 3;
pub const IV: [u32; 8] = [
  0x6A09_E667,
  0xBB67_AE85,
  0x3C6E_F372,
  0xA54F_F53A,
  0x510E_527F,
  0x9B05_688C,
  0x1F83_D9AB,
  0x5BE0_CD19,
];

pub struct Blake3Gate {
  pub nu: usize,
}

impl GateType for Blake3Gate {
  type Row = blake3::Compression;
  type Hint = ();

  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(blake3::build_block_r1cs(self.nu))
      .with_io_schema(blake3::io_schema())
  }

  fn eval(
    &self,
    inputs: &[F128],
    _hint: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let cv = unpack8(inputs[0], inputs[1]);
    let mut message = [0u32; 16];
    for index in 0..4 {
      message[4 * index..4 * index + 4]
        .copy_from_slice(&unpack4(inputs[2 + index]));
    }
    let (counter, block_len, flags) = unpack_params(inputs[6]);
    let output =
      blake3::blake3_compress(&cv, &message, counter, block_len, flags);
    let output_lo: [u32; 8] = output[..8].try_into().unwrap();
    let output_hi: [u32; 8] = output[8..].try_into().unwrap();
    outputs.extend_from_slice(&[
      pack8(&output_lo)[0],
      pack8(&output_lo)[1],
      pack8(&output_hi)[0],
      pack8(&output_hi)[1],
    ]);
    (cv, message, counter, block_len, flags)
  }

  fn witness(&self, _rows: &[Self::Row], _nu: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

pub fn pack_bytes(bytes: &[u8]) -> F128 {
  assert_eq!(bytes.len(), WORD_BYTES);
  F128::new(
    u64::from_le_bytes(bytes[..8].try_into().unwrap()),
    u64::from_le_bytes(bytes[8..].try_into().unwrap()),
  )
}

pub fn pack4(words: [u32; 4]) -> F128 {
  F128::new(
    words[0] as u64 | ((words[1] as u64) << 32),
    words[2] as u64 | ((words[3] as u64) << 32),
  )
}

pub fn unpack4(value: F128) -> [u32; 4] {
  [
    value.lo as u32,
    (value.lo >> 32) as u32,
    value.hi as u32,
    (value.hi >> 32) as u32,
  ]
}

pub fn pack8(words: &[u32; 8]) -> [F128; 2] {
  [
    pack4([words[0], words[1], words[2], words[3]]),
    pack4([words[4], words[5], words[6], words[7]]),
  ]
}

pub fn unpack8(first: F128, second: F128) -> [u32; 8] {
  let first = unpack4(first);
  let second = unpack4(second);
  [
    first[0], first[1], first[2], first[3], second[0], second[1], second[2],
    second[3],
  ]
}

pub fn pack_params(counter: u64, block_len: u32, flags: u32) -> F128 {
  F128::new(counter, block_len as u64 | ((flags as u64) << 32))
}

fn unpack_params(value: F128) -> (u64, u32, u32) {
  (value.lo, value.hi as u32, (value.hi >> 32) as u32)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn packing_preserves_every_word_and_parameter_bit() {
    let words = [0, 1, u32::MAX, 1 << 31, 7, 0x1234_5678, 9, 0xabcd_ef01];
    let packed = pack8(&words);
    assert_eq!(unpack8(packed[0], packed[1]), words);
    let bytes: Vec<u8> =
      words.iter().flat_map(|word| word.to_le_bytes()).collect();
    assert_eq!(pack_bytes(&bytes[..16]), packed[0]);
    assert_eq!(pack_bytes(&bytes[16..]), packed[1]);
    assert_eq!(
      unpack_params(pack_params(u64::MAX, 64, u32::MAX)),
      (u64::MAX, 64, u32::MAX)
    );
  }

  #[test]
  fn compression_gate_matches_native_hash_at_block_boundaries() {
    let gate = Blake3Gate { nu: 3 };
    for length in [0usize, 1, 3, 31, 32, 63, 64] {
      let bytes: Vec<u8> =
        (0..length).map(|index| (index * 17 + 3) as u8).collect();
      let mut padded = [0u8; 64];
      padded[..length].copy_from_slice(&bytes);
      let mut inputs = Vec::from(pack8(&IV));
      inputs.extend(
        padded.as_chunks::<16>().0.iter().map(|bytes| pack_bytes(bytes)),
      );
      inputs.push(pack_params(
        0,
        length as u32,
        CHUNK_START | CHUNK_END | ROOT,
      ));
      let mut output = Vec::new();
      let row = gate.eval(&inputs, &(), &mut output);
      let expected = ::blake3::hash(&bytes);
      assert_eq!(
        output[..2],
        [
          pack_bytes(&expected.as_bytes()[..16]),
          pack_bytes(&expected.as_bytes()[16..])
        ]
      );
      let r1cs = blake3::build_block_r1cs(3);
      let mut witness = blake3::generate_witness(&[row], 3);
      assert!(r1cs.satisfies(&witness));
      witness[blake3::OUT_LO_BASE + 17] ^= true;
      assert!(!r1cs.satisfies(&witness));
    }
  }

  #[test]
  fn partial_witness_zeros_unused_rows_including_constant_pins() {
    let row = (IV, [7u32; 16], 0, 64, CHUNK_START | CHUNK_END | ROOT);
    let (z, a, b, stripe) =
      blake3::generate_witness_batch_major_partial(&[row; 2], 3);
    for chunk in 0..(1usize << blake3::K_LOG) / 128 {
      for outer in 2..8 {
        let index = (chunk << 3) + outer;
        assert_eq!(z[index], F128::ZERO);
        assert_eq!(a[index], F128::ZERO);
        assert_eq!(b[index], F128::ZERO);
      }
    }
    assert!(stripe.iter().all(|byte| byte & !0b11 == 0));
    assert_eq!(stripe[blake3::Z_CONST_POS], 0b11);
  }
}
