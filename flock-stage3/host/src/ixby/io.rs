//! Setup-owned input/public layouts for generic circuit components. Recording
//! the layout never evaluates private inputs. This is not an artifact decoder
//! or the final Exec ABI: that adapter must additionally require exactly the
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
enum PublicWord {
  Fixed(F128),
  Output(usize),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct InputLayout {
  words: Vec<InputWord>,
  private_words: usize,
}

impl InputLayout {
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
}
