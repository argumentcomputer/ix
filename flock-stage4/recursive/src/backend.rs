//! A value-independent native constraint graph. Values are separate advice.
//! Arithmetic equations are packed into fixed 64-operation element rows;
//! canonical bit decompositions use one fixed 128-bit packing table.
use crate::{ConstraintPhase, R1csError};
use flock_prover::field::F128;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum BitRef {
  Constant(bool),
  Word { word: usize, bit: u8 },
}
impl BitRef {
  pub(crate) fn minus(self, other: &Self) -> (Self, Self) {
    (self, *other)
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NativeGraph {
  pub(crate) constants: Vec<(usize, F128)>,
  pub(crate) variables: usize,
  /// x*y + addend = output. Every referenced value is a circuit wire.
  pub(crate) macs: Vec<[usize; 4]>,
  /// 128 Boolean scalar wires followed by their packed polynomial-basis word.
  pub(crate) packs: Vec<Vec<usize>>,
  pub(crate) compressions: Vec<([usize; 7], [usize; 4])>,
  pub(crate) equalities: Vec<(usize, usize)>,
  pub(crate) published: Vec<usize>,
}

pub(crate) struct NativeBuilder {
  pub(crate) graph: NativeGraph,
  pub(crate) values: Vec<F128>,
  shape_only: bool,
  constants: HashMap<F128, usize>,
  splits: HashMap<usize, [usize; 128]>,
  packed: HashMap<[BitRef; 128], usize>,
}
impl NativeBuilder {
  pub(crate) fn new(shape_only: bool) -> Self {
    Self {
      graph: NativeGraph {
        constants: vec![],
        variables: 0,
        macs: vec![],
        packs: vec![],
        compressions: vec![],
        equalities: vec![],
        published: vec![],
      },
      values: vec![],
      shape_only,
      constants: HashMap::new(),
      splits: HashMap::new(),
      packed: HashMap::new(),
    }
  }
  pub(crate) fn is_shape_only(&self) -> bool {
    self.shape_only
  }
  pub(crate) fn alloc(&mut self, value: F128) -> usize {
    let index = self.values.len();
    self.values.push(value);
    self.graph.variables += 1;
    index
  }
  pub(crate) fn constant(&mut self, value: F128) -> usize {
    if let Some(&index) = self.constants.get(&value) {
      return index;
    }
    let index = self.alloc(value);
    self.constants.insert(value, index);
    self.graph.constants.push((index, value));
    index
  }
  pub(crate) fn bits(word: usize) -> [BitRef; 128] {
    std::array::from_fn(|bit| BitRef::Word {
      word,
      bit: u8::try_from(bit).expect("bit below 128"),
    })
  }
  pub(crate) fn bit_value(&self, bit: BitRef) -> bool {
    match bit {
      BitRef::Constant(value) => value,
      BitRef::Word { word, bit } => {
        let value = self.values[word];
        if bit < 64 {
          (value.lo >> bit) & 1 != 0
        } else {
          (value.hi >> (bit - 64)) & 1 != 0
        }
      },
    }
  }
  pub(crate) fn bit(&mut self, bit: BitRef) -> usize {
    match bit {
      BitRef::Constant(value) => {
        self.constant(if value { F128::ONE } else { F128::ZERO })
      },
      BitRef::Word { word, bit } => {
        if !self.splits.contains_key(&word) {
          let source = self.values[word];
          let bits = std::array::from_fn(|i| {
            let value = if i < 64 {
              (source.lo >> i) & 1
            } else {
              (source.hi >> (i - 64)) & 1
            };
            self.alloc(F128::new(value, 0))
          });
          let mut row = bits.to_vec();
          row.push(word);
          self.graph.packs.push(row);
          self.splits.insert(word, bits);
        }
        self.splits[&word][usize::from(bit)]
      },
    }
  }
  pub(crate) fn pack(&mut self, bits: &[BitRef; 128]) -> usize {
    if let BitRef::Word { word, bit: 0 } = bits[0]
      && bits.iter().enumerate().all(|(i, &b)| {
        b == (BitRef::Word {
          word,
          bit: u8::try_from(i).expect("bit below 128"),
        })
      })
    {
      return word;
    }
    if bits.iter().all(|b| matches!(b, BitRef::Constant(_))) {
      let value = bits
        .iter()
        .enumerate()
        .fold(0u128, |v, (i, &b)| v | ((u128::from(self.bit_value(b))) << i));
      return self.constant(ixby_flock::hash::pack_bytes(&value.to_le_bytes()));
    }
    if let Some(&word) = self.packed.get(bits) {
      return word;
    }
    let value = bits
      .iter()
      .enumerate()
      .fold(0u128, |v, (i, &b)| v | ((u128::from(self.bit_value(b))) << i));
    let word = self.alloc(ixby_flock::hash::pack_bytes(&value.to_le_bytes()));
    let mut row = bits.iter().map(|&bit| self.bit(bit)).collect::<Vec<_>>();
    row.push(word);
    self.graph.packs.push(row);
    self.packed.insert(*bits, word);
    word
  }
  pub(crate) fn add(&mut self, a: usize, b: usize) -> usize {
    let output = self.alloc(self.values[a] + self.values[b]);
    let one = self.constant(F128::ONE);
    self.graph.macs.push([a, one, b, output]);
    output
  }
  pub(crate) fn multiply(&mut self, a: usize, b: usize) -> usize {
    let output = self.alloc(self.values[a] * self.values[b]);
    let zero = self.constant(F128::ZERO);
    self.graph.macs.push([a, b, zero, output]);
    output
  }
  pub(crate) fn inverse(&mut self, a: usize) -> usize {
    let value = self.values[a];
    let inverse = if value == F128::ZERO { F128::ZERO } else { value.inv() };
    let output = self.alloc(inverse);
    let zero = self.constant(F128::ZERO);
    let one = self.constant(F128::ONE);
    self.graph.macs.push([a, output, zero, one]);
    output
  }
  pub(crate) fn equal(&mut self, a: usize, b: usize) {
    self.graph.equalities.push((a, b));
  }
  pub(crate) fn enforce_zero(
    &mut self,
    _phase: ConstraintPhase,
    pair: (BitRef, BitRef),
  ) {
    let a = self.bit(pair.0);
    let b = self.bit(pair.1);
    self.equal(a, b);
  }
  pub(crate) fn compress(&mut self, input: [usize; 7]) -> [usize; 4] {
    let v = input.map(|i| self.values[i]);
    let cv = ixby_flock::hash::unpack8(v[0], v[1]);
    let message: [u32; 16] = v[2..6]
      .iter()
      .flat_map(|&v| ixby_flock::hash::unpack4(v))
      .collect::<Vec<_>>()
      .try_into()
      .unwrap();
    let output = flock_prover::r1cs_hashes::blake3::blake3_compress(
      &cv,
      &message,
      v[6].lo,
      ixby_flock::hash::unpack4(v[6])[2],
      ixby_flock::hash::unpack4(v[6])[3],
    );
    let output = std::array::from_fn(|i| {
      self.alloc(ixby_flock::hash::pack4(
        output[4 * i..4 * i + 4].try_into().unwrap(),
      ))
    });
    self.graph.compressions.push((input, output));
    output
  }
  pub(crate) fn check(&self) -> Result<(), R1csError> {
    let valid = self.graph.macs.iter().all(|&[a, b, c, d]| {
      self.values[a] * self.values[b] + self.values[c] == self.values[d]
    }) && self
      .graph
      .equalities
      .iter()
      .all(|&(a, b)| self.values[a] == self.values[b])
      && self.graph.constants.iter().all(|&(i, value)| self.values[i] == value)
      && self.graph.packs.iter().all(|row| {
        let mut value = F128::ZERO;
        for (i, &bit) in row[..128].iter().enumerate() {
          if self.values[bit] != F128::ZERO && self.values[bit] != F128::ONE {
            return false;
          }
          let basis = if i < 64 {
            F128::new(1 << i, 0)
          } else {
            F128::new(0, 1 << (i - 64))
          };
          value += self.values[bit] * basis;
        }
        value == self.values[row[128]]
      });
    if valid { Ok(()) } else { Err(R1csError::InternalShape) }
  }
}
