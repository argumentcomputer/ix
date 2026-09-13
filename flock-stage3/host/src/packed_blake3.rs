//! Experimental BLAKE3 compression from ten reusable packed-word tables.
//!
//! A word packs four independent little-endian u32 lanes. The same tables
//! implement all seven rounds; neither messages nor parameters select wiring.
//! This component does NOT replace the approved Exec compression backend.
//! Adoption requires new implementation/key identities and whole-relation
//! cost admission: smaller inner matrices need more outer rows and I/O words.

use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
    table_from_block_r1cs, write_f128,
  },
  hash::{IV, pack4, unpack4},
  sizing::{CircuitEmitter, CountedGate},
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{GateType, SlotId, SlotWitness, Wire},
  field::F128,
  r1cs::BlockR1cs,
  r1cs_hashes::blake3::MSG_PERMUTATION,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};
use std::sync::{Arc, OnceLock};

/// Finite, setup-owned variants; arbitrary rotations cannot introduce extra
/// tables or change a declared slot after setup.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackedGateKind {
  Add,
  Xor,
  XorRotate7,
  XorRotate8,
  XorRotate12,
  XorRotate16,
  LanesLeft1,
  LanesLeft2,
  LanesLeft3,
  MessageSchedule,
}

impl PackedGateKind {
  pub const ALL: [Self; 10] = [
    Self::Add,
    Self::Xor,
    Self::XorRotate7,
    Self::XorRotate8,
    Self::XorRotate12,
    Self::XorRotate16,
    Self::LanesLeft1,
    Self::LanesLeft2,
    Self::LanesLeft3,
    Self::MessageSchedule,
  ];

  fn rotation(self) -> Option<usize> {
    match self {
      Self::Xor => Some(0),
      Self::XorRotate7 => Some(7),
      Self::XorRotate8 => Some(8),
      Self::XorRotate12 => Some(12),
      Self::XorRotate16 => Some(16),
      _ => None,
    }
  }

  fn lane_shift(self) -> Option<usize> {
    match self {
      Self::LanesLeft1 => Some(1),
      Self::LanesLeft2 => Some(2),
      Self::LanesLeft3 => Some(3),
      _ => None,
    }
  }
}

#[derive(Clone, Debug)]
pub struct PackedWordGate {
  kind: PackedGateKind,
  nu: usize,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}

/// Only the input words are advice. Output and carry bits are constrained by
/// the table; native gate evaluation is not trusted by the verifier.
#[derive(Clone, Debug)]
pub struct PackedWordRow(Vec<F128>);

impl PackedWordGate {
  pub fn new(nu: usize, kind: PackedGateKind) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "packed BLAKE3 row-domain admission");
    Ok(Self { kind, nu, plan: Arc::new(OnceLock::new()) })
  }

  pub fn kind(&self) -> PackedGateKind {
    self.kind
  }

  fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| {
      let inputs = self.input_count();
      let k_log = if self.kind == PackedGateKind::MessageSchedule {
        12
      } else if self.kind.lane_shift().is_some() {
        8
      } else {
        9
      };
      let mut b =
        BooleanR1csBuilder::new(k_log, (inputs + self.output_count()) * 128);
      for bit in 0..inputs * 128 {
        b.free_boolean_at(bit);
      }
      if self.kind == PackedGateKind::Add {
        for lane in 0..4 {
          // If c_i = XOR(p_0,...,p_{i-1}), then
          // p_i = (x_i + c_i)(y_i + c_i) and
          // c_{i+1} = c_i + p_i = x_i*y_i + c_i*(x_i+y_i).
          // Dropping c_32 implements wrapping u32 addition, independently
          // in each lane. No constant-one pin is needed.
          let mut carry = Vec::new();
          for bit in 0..32 {
            let x = lane * 32 + bit;
            let y = 128 + x;
            let mut sum = vec![x, y];
            sum.extend_from_slice(&carry);
            linear_output(&mut b, 256 + x, &sum);
            if bit < 31 {
              let mut a = vec![x];
              a.extend_from_slice(&carry);
              let mut rhs = vec![y];
              rhs.extend_from_slice(&carry);
              carry.push(b.product_of_parities(&a, &rhs));
            }
          }
        }
      } else if let Some(rotation) = self.kind.rotation() {
        for lane in 0..4 {
          for bit in 0..32 {
            let source = lane * 32 + (bit + rotation) % 32;
            linear_output(
              &mut b,
              256 + lane * 32 + bit,
              &[source, 128 + source],
            );
          }
        }
      } else if let Some(shift) = self.kind.lane_shift() {
        for lane in 0..4 {
          for bit in 0..32 {
            linear_output(
              &mut b,
              128 + lane * 32 + bit,
              &[((lane + shift) % 4) * 32 + bit],
            );
          }
        }
      } else {
        assert_eq!(self.kind, PackedGateKind::MessageSchedule);
        for (word, lanes) in message_schedule().iter().enumerate() {
          for (lane, source) in lanes.iter().enumerate() {
            for bit in 0..32 {
              linear_output(
                &mut b,
                512 + word * 128 + lane * 32 + bit,
                &[source * 32 + bit],
              );
            }
          }
        }
      }
      b.finish()
    })
  }

  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }

  pub fn generate_witness_into(
    &self,
    rows: &[PackedWordRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(
      self.plan(),
      rows,
      self.nu,
      dst,
      |row, bits| {
        assert_eq!(row.0.len(), self.input_count());
        for (word, value) in row.0.iter().enumerate() {
          write_f128(bits, word * 128, *value);
        }
      },
    )
  }
}

// In a Boolean table, every linear form is a bit: f*f=f over GF(2).
// C=I therefore binds this pre-reserved output to the XOR of its inputs.
fn linear_output(b: &mut BooleanR1csBuilder, output: usize, form: &[usize]) {
  b.write_product_of_parities(output, form, form);
}

/// For each round: column x, column y, diagonal x, diagonal y. Each u32
/// source index names the ORIGINAL message, not a witness-selected shuffle.
fn message_schedule() -> [[usize; 4]; 28] {
  let mut permutation: [usize; 16] = std::array::from_fn(|i| i);
  let mut schedule = [[0; 4]; 28];
  for round in 0..7 {
    for half in 0..2 {
      for xy in 0..2 {
        schedule[4 * round + 2 * half + xy] =
          std::array::from_fn(|lane| permutation[8 * half + 2 * lane + xy]);
      }
    }
    permutation = std::array::from_fn(|i| permutation[MSG_PERMUTATION[i]]);
  }
  schedule
}

impl CountedGate for PackedWordGate {
  fn input_count(&self) -> usize {
    if self.kind == PackedGateKind::MessageSchedule {
      4
    } else if self.kind.lane_shift().is_some() {
      1
    } else {
      2
    }
  }
  fn output_count(&self) -> usize {
    if self.kind == PackedGateKind::MessageSchedule { 28 } else { 1 }
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for PackedWordGate {
  type Row = PackedWordRow;
  type Hint = ();

  fn table(&self) -> TableType {
    let inputs = self.input_count();
    let mut schema: Vec<_> = (0..inputs).map(IoWord::input).collect();
    schema.extend((inputs..inputs + self.output_count()).map(IoWord::output));
    table_from_block_r1cs(self.r1cs()).with_io_schema(schema)
  }

  fn eval(
    &self,
    inputs: &[F128],
    _: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    assert_eq!(inputs.len(), self.input_count());
    // Independent native word arithmetic; does not execute the Boolean plan.
    let first = unpack4(inputs[0]);
    if self.kind == PackedGateKind::Add {
      let second = unpack4(inputs[1]);
      outputs
        .push(pack4(std::array::from_fn(|i| first[i].wrapping_add(second[i]))));
    } else if let Some(rotation) = self.kind.rotation() {
      let second = unpack4(inputs[1]);
      outputs.push(pack4(std::array::from_fn(|i| {
        (first[i] ^ second[i]).rotate_right(rotation as u32)
      })));
    } else if let Some(shift) = self.kind.lane_shift() {
      outputs.push(pack4(std::array::from_fn(|i| first[(i + shift) % 4])));
    } else {
      let message: Vec<_> =
        inputs.iter().flat_map(|word| unpack4(*word)).collect();
      outputs.extend(
        message_schedule().map(|lanes| pack4(lanes.map(|i| message[i]))),
      );
    }
    PackedWordRow(inputs.to_vec())
  }

  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

/// Reusable compression slots within one emitter. The IV is a fixed public
/// word; the two CV words, four message words, and parameter word may all be
/// private. This is raw compression: hash-mode length/flag constraints belong
/// to the caller, just as for the original seven-input BLAKE3 gate.
pub struct PackedBlake3 {
  gates: Vec<(PackedWordGate, SlotId)>,
  iv: Wire,
}

impl PackedBlake3 {
  pub fn declare(b: &mut impl CircuitEmitter, nu: usize) -> Result<Self> {
    let mut gates = Vec::new();
    for kind in PackedGateKind::ALL {
      let gate = PackedWordGate::new(nu, kind)?;
      let slot = b.slot(gate.clone());
      gates.push((gate, slot));
    }
    let iv = b.fixed_public_input(pack4(IV[..4].try_into().unwrap()));
    Ok(Self { gates, iv })
  }

  pub fn gates(&self) -> &[(PackedWordGate, SlotId)] {
    &self.gates
  }

  fn slot(&self, kind: PackedGateKind) -> SlotId {
    self.gates.iter().find(|(gate, _)| gate.kind == kind).unwrap().1
  }

  fn word(
    &self,
    b: &mut impl CircuitEmitter,
    kind: PackedGateKind,
    inputs: &[Wire],
  ) -> Wire {
    b.gate(self.slot(kind), inputs)[0]
  }

  fn mix(
    &self,
    b: &mut impl CircuitEmitter,
    [mut a, mut v_b, mut c, mut d]: [Wire; 4],
    mx: Wire,
    my: Wire,
  ) -> [Wire; 4] {
    use PackedGateKind::*;
    a = self.word(b, Add, &[a, v_b]);
    a = self.word(b, Add, &[a, mx]);
    d = self.word(b, XorRotate16, &[d, a]);
    c = self.word(b, Add, &[c, d]);
    v_b = self.word(b, XorRotate12, &[v_b, c]);
    a = self.word(b, Add, &[a, v_b]);
    a = self.word(b, Add, &[a, my]);
    d = self.word(b, XorRotate8, &[d, a]);
    c = self.word(b, Add, &[c, d]);
    v_b = self.word(b, XorRotate7, &[v_b, c]);
    [a, v_b, c, d]
  }

  /// All sixteen compression output u32s, in the upstream gate's order.
  pub fn compress(
    &self,
    b: &mut impl CircuitEmitter,
    cv: [Wire; 2],
    message: [Wire; 4],
    params: Wire,
  ) -> [Wire; 4] {
    use PackedGateKind::*;
    let schedule = b.gate(self.slot(MessageSchedule), &message);
    let mut state = [cv[0], cv[1], self.iv, params];
    for round in 0..7 {
      state = self.mix(b, state, schedule[4 * round], schedule[4 * round + 1]);
      state[1] = self.word(b, LanesLeft1, &[state[1]]);
      state[2] = self.word(b, LanesLeft2, &[state[2]]);
      state[3] = self.word(b, LanesLeft3, &[state[3]]);
      state =
        self.mix(b, state, schedule[4 * round + 2], schedule[4 * round + 3]);
      state[1] = self.word(b, LanesLeft3, &[state[1]]);
      state[2] = self.word(b, LanesLeft2, &[state[2]]);
      state[3] = self.word(b, LanesLeft1, &[state[3]]);
    }
    [
      self.word(b, Xor, &[state[0], state[2]]),
      self.word(b, Xor, &[state[1], state[3]]),
      self.word(b, Xor, &[state[2], cv[0]]),
      self.word(b, Xor, &[state[3], cv[1]]),
    ]
  }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod proof_tests;
