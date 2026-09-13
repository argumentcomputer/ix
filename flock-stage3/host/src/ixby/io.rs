//! Setup-owned input/public layouts for generic circuit components. Recording
//! the layout never evaluates private inputs. This is not an artifact decoder
//! or by itself the Exec ABI: the `exec` adapter additionally requires exactly
//! two statement digest limbs and an approved setup/configuration.
//!
//! The shape builder consumes fixed public constants as input values as well.
//! Keep those positions explicit so a verifier never needs a prover-generated
//! public vector, a witness run, or private advice to reconstruct its inputs.

use crate::sizing::{CircuitEmitter, CountedGate};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum InputWord {
  Fixed(F128),
  Private(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PublicWord {
  Fixed(F128),
  Output(usize),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct InputLayout {
  words: Vec<InputWord>,
  private_words: usize,
}

impl InputLayout {
  /// Bind positions as well as values; a zero fixed word is not private advice.
  pub fn digest(&self) -> [u8; 32] {
    let mut bytes = b"IxBy/Flock/input-layout/v0\0".to_vec();
    bytes.extend_from_slice(&(self.words.len() as u64).to_le_bytes());
    bytes.extend_from_slice(&(self.private_words as u64).to_le_bytes());
    for word in &self.words {
      match word {
        InputWord::Fixed(value) => fixed(&mut bytes, *value),
        InputWord::Private(index) => indexed(&mut bytes, *index),
      }
    }
    *blake3::hash(&bytes).as_bytes()
  }
  pub fn private_words(&self) -> usize {
    self.private_words
  }
  pub fn assign(&self, private: &[F128]) -> Result<Vec<F128>> {
    ensure!(private.len() == self.private_words, "private input layout width");
    Ok(
      self
        .words
        .iter()
        .map(|word| match *word {
          InputWord::Fixed(value) => value,
          InputWord::Private(index) => private[index],
        })
        .collect(),
    )
  }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PublicLayout {
  words: Vec<PublicWord>,
  outputs: usize,
}

impl PublicLayout {
  /// Verifier-owned positions, including fixed zero words. A replay adapter
  /// must use this template rather than infer fixed positions from values.
  pub fn words(&self) -> &[PublicWord] {
    &self.words
  }
  /// The template identity includes each fixed word and each output index.
  pub fn digest(&self) -> [u8; 32] {
    let mut bytes = b"IxBy/Flock/public-layout/v0\0".to_vec();
    bytes.extend_from_slice(&(self.words.len() as u64).to_le_bytes());
    bytes.extend_from_slice(&(self.outputs as u64).to_le_bytes());
    for word in &self.words {
      match word {
        PublicWord::Fixed(value) => fixed(&mut bytes, *value),
        PublicWord::Output(index) => indexed(&mut bytes, *index),
      }
    }
    *blake3::hash(&bytes).as_bytes()
  }
  pub fn outputs(&self) -> usize {
    self.outputs
  }
  pub fn instantiate(&self, expected: &[F128]) -> Result<Vec<F128>> {
    ensure!(expected.len() == self.outputs, "expected public output width");
    Ok(
      self
        .words
        .iter()
        .map(|word| match *word {
          PublicWord::Fixed(value) => value,
          PublicWord::Output(index) => expected[index],
        })
        .collect(),
    )
  }
}

fn fixed(bytes: &mut Vec<u8>, value: F128) {
  bytes.push(0);
  bytes.extend_from_slice(&value.lo.to_le_bytes());
  bytes.extend_from_slice(&value.hi.to_le_bytes());
}
fn indexed(bytes: &mut Vec<u8>, index: usize) {
  bytes.push(1);
  bytes.extend_from_slice(&(index as u64).to_le_bytes());
}

pub struct LayoutEmitter<'a, B> {
  builder: &'a mut B,
  inputs: InputLayout,
  public: PublicLayout,
}

impl<'a, B: CircuitEmitter> LayoutEmitter<'a, B> {
  pub fn new(builder: &'a mut B) -> Self {
    Self {
      builder,
      inputs: InputLayout::default(),
      public: PublicLayout::default(),
    }
  }
  pub fn finish(self) -> (InputLayout, PublicLayout) {
    (self.inputs, self.public)
  }
}

impl<B: CircuitEmitter> CircuitEmitter for LayoutEmitter<'_, B> {
  fn slot<G>(&mut self, gate: G) -> SlotId
  where
    G: CountedGate + Send + Sync + 'static,
    G::Row: Send + 'static,
    G::Hint: 'static,
  {
    self.builder.slot(gate)
  }
  fn input(&mut self) -> Wire {
    self.inputs.words.push(InputWord::Private(self.inputs.private_words));
    self.inputs.private_words += 1;
    self.builder.input()
  }
  fn public_input(&mut self) -> Wire {
    // Each variable public word must be a constrained output with an explicit
    // externally expected value; do not introduce unnamed public advice.
    panic!("generic layout requires publishing constrained outputs")
  }
  fn fixed_public_input(&mut self, value: F128) -> Wire {
    self.inputs.words.push(InputWord::Fixed(value));
    self.public.words.push(PublicWord::Fixed(value));
    self.builder.fixed_public_input(value)
  }
  fn gate(&mut self, slot: SlotId, inputs: &[Wire]) -> Vec<Wire> {
    self.builder.gate(slot, inputs)
  }
  fn publish(&mut self, wire: Wire) {
    self.public.words.push(PublicWord::Output(self.public.outputs));
    self.public.outputs += 1;
    self.builder.publish(wire);
  }
  fn connect(&mut self, first: Wire, second: Wire) {
    self.builder.connect(first, second);
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ixby::select::{SelectWordsGate, SelectWordsSlot};
  use flock_prover::circuit::builder::ShapeBuilder;

  #[test]
  fn interleaved_fixed_inputs_and_outputs_have_exact_separate_layouts() {
    let mut builder = ShapeBuilder::new(3);
    let mut emitter = LayoutEmitter::new(&mut builder);
    let selector = SelectWordsSlot::declare(
      &mut emitter,
      SelectWordsGate::new(3, 1).unwrap(),
    );
    let choice = emitter.fixed_public_input(F128::new(1, 0));
    let private = emitter.input();
    let zero = emitter.fixed_public_input(F128::ZERO);
    let output = selector.select(&mut emitter, choice, &[private], &[zero])[0];
    emitter.publish(output);
    let constant = emitter.fixed_public_input(F128::new(31, 41));
    emitter.publish(constant);
    let (inputs, public) = emitter.finish();
    let shape = builder.finish().unwrap();
    let value = F128::new(17, 29);
    assert_eq!(inputs.private_words(), 1);
    assert_eq!(public.outputs(), 2);
    assert_eq!(
      shape.run(&inputs.assign(&[value]).unwrap(), &[]).public,
      public.instantiate(&[value, F128::new(31, 41)]).unwrap()
    );
    assert!(inputs.assign(&[]).is_err());
    assert!(inputs.assign(&[value; 2]).is_err());
    assert!(public.instantiate(&[value]).is_err());
    assert!(public.instantiate(&[value; 3]).is_err());
  }

  #[test]
  fn identities_bind_fixed_zero_positions_output_order_and_private_layout() {
    let template = PublicLayout {
      words: vec![
        PublicWord::Fixed(F128::ZERO),
        PublicWord::Output(0),
        PublicWord::Output(1),
      ],
      outputs: 2,
    };
    for words in [
      vec![
        PublicWord::Output(0),
        PublicWord::Fixed(F128::ZERO),
        PublicWord::Output(1),
      ],
      vec![
        PublicWord::Fixed(F128::ZERO),
        PublicWord::Output(1),
        PublicWord::Output(0),
      ],
      vec![
        PublicWord::Fixed(F128::new(1, 0)),
        PublicWord::Output(0),
        PublicWord::Output(1),
      ],
    ] {
      assert_ne!(
        template.digest(),
        PublicLayout { words, outputs: 2 }.digest()
      );
    }
    let first = InputLayout {
      words: vec![InputWord::Fixed(F128::ZERO), InputWord::Private(0)],
      private_words: 1,
    };
    let second = InputLayout {
      words: vec![InputWord::Private(0), InputWord::Fixed(F128::ZERO)],
      private_words: 1,
    };
    assert_eq!(
      first.assign(&[F128::ZERO]).unwrap(),
      second.assign(&[F128::ZERO]).unwrap()
    );
    assert_ne!(first.digest(), second.digest());
    assert_ne!(
      PublicLayout::default().digest(),
      InputLayout::default().digest()
    );
  }
}
