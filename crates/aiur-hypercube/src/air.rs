//! The generic Hypercube chip interpreting a lowered Aiur circuit.

use std::mem::MaybeUninit;

use slop_air::{Air, BaseAir, PairBuilder};
use slop_matrix::{Matrix, dense::RowMajorMatrix};
use sp1_hypercube::{
  InteractionKind,
  air::{AirInteraction, InteractionScope, MachineAir, SP1AirBuilder},
};

use crate::{
  F,
  expr::Lowered,
  global::GlobalSpec,
  record::{AiurProgram, AiurRecord},
};

/// The interaction kind every Aiur lookup is tagged with. Aiur multiplexes
/// its tables through the first message element (the channel), so a single
/// Hypercube kind suffices. The LogUp-GKR verifier sizes its fingerprint
/// randomness from `max(chip arities, kind.num_values() + 1)` for the kinds in
/// the public-value interactions while the prover uses the chip arities
/// alone, so the kind's table arity must not exceed what the chips already
/// guarantee (see [`crate::record::CLAIM_WIDTH`]).
pub const AIUR_INTERACTION_KIND: InteractionKind = InteractionKind::Memory;

/// What a chip evaluates: most chips interpret a [`Lowered`] circuit, the
/// cross-shard adapter chips run the hand-written [`GlobalSpec`] AIR.
#[derive(Debug)]
pub enum AirKind {
  Interpreted(Lowered),
  Global(GlobalSpec),
}

/// A chip of the Aiur machine, dispatching on [`AirKind`].
#[derive(Debug)]
pub struct AiurAir {
  name: &'static str,
  /// Position of this chip's trace in [`AiurRecord::traces`].
  index: usize,
  kind: AirKind,
  preprocessed: Option<RowMajorMatrix<F>>,
}

impl AiurAir {
  pub fn new(
    name: String,
    index: usize,
    kind: AirKind,
    preprocessed: Option<RowMajorMatrix<F>>,
  ) -> Self {
    // `MachineAir::name` wants a `&'static str`; chips are created once per
    // machine, so leaking the handful of names is fine.
    let name: &'static str = Box::leak(name.into_boxed_str());
    Self { name, index, kind, preprocessed }
  }

  pub fn index(&self) -> usize {
    self.index
  }

  pub fn kind(&self) -> &AirKind {
    &self.kind
  }

  pub fn preprocessed(&self) -> Option<&RowMajorMatrix<F>> {
    self.preprocessed.as_ref()
  }

  fn trace<'a>(&self, record: &'a AiurRecord) -> Option<&'a RowMajorMatrix<F>> {
    record.traces.get(self.index).and_then(Option::as_ref)
  }
}

impl BaseAir<F> for AiurAir {
  fn width(&self) -> usize {
    match &self.kind {
      AirKind::Interpreted(lowered) => lowered.main_width,
      AirKind::Global(spec) => spec.width(),
    }
  }
}

impl MachineAir<F> for AiurAir {
  type Record = AiurRecord;
  type Program = AiurProgram;

  fn name(&self) -> &'static str {
    self.name
  }

  fn num_rows(&self, input: &Self::Record) -> Option<usize> {
    Some(self.trace(input).map_or(0, Matrix::height))
  }

  fn generate_trace_into(
    &self,
    input: &Self::Record,
    _output: &mut Self::Record,
    buffer: &mut [MaybeUninit<F>],
  ) {
    let trace = self.trace(input).expect("chip included without a trace");
    assert_eq!(
      trace.width(),
      BaseAir::<F>::width(self),
      "trace width mismatch"
    );
    assert_eq!(buffer.len(), trace.values.len(), "trace buffer size mismatch");
    for (dst, src) in buffer.iter_mut().zip(&trace.values) {
      dst.write(*src);
    }
  }

  fn included(&self, shard: &Self::Record) -> bool {
    self.trace(shard).is_some_and(|t| t.height() > 0)
  }

  fn preprocessed_width(&self) -> usize {
    self.preprocessed.as_ref().map_or(0, Matrix::width)
  }

  fn preprocessed_num_rows(&self, _program: &Self::Program) -> Option<usize> {
    self.preprocessed.as_ref().map(Matrix::height)
  }

  fn generate_preprocessed_trace_into(
    &self,
    _program: &Self::Program,
    buffer: &mut [MaybeUninit<F>],
  ) {
    let prep = self.preprocessed.as_ref().expect("no preprocessed trace");
    assert_eq!(buffer.len(), prep.values.len(), "preprocessed buffer mismatch");
    for (dst, src) in buffer.iter_mut().zip(&prep.values) {
      dst.write(*src);
    }
  }
}

impl<AB> Air<AB> for AiurAir
where
  AB: SP1AirBuilder<F = F> + PairBuilder,
{
  fn eval(&self, builder: &mut AB) {
    let lowered = match &self.kind {
      AirKind::Interpreted(lowered) => lowered,
      AirKind::Global(spec) => return spec.eval(builder),
    };
    let main = builder.main();
    let main_row = main.row_slice(0);
    let main_row: &[AB::Var] = &main_row;

    // Only touch the preprocessed matrix when the chip has one; some
    // builders have nothing sensible to hand out otherwise.
    let prep = self.preprocessed.is_some().then(|| builder.preprocessed());
    let prep_row = prep.as_ref().map(|p| p.row_slice(0));
    let prep_row: &[AB::Var] = prep_row.as_deref().unwrap_or(&[]);

    for constraint in &lowered.constraints {
      let expr = constraint.eval_air::<AB>(prep_row, main_row, builder);
      builder.assert_zero(expr);
    }

    for interaction in &lowered.interactions {
      let multiplicity =
        interaction.multiplicity.eval_air::<AB>(prep_row, main_row);
      let values = interaction
        .values
        .iter()
        .map(|v| v.eval_air::<AB>(prep_row, main_row))
        .collect();
      builder.send(
        AirInteraction::new(values, multiplicity, AIUR_INTERACTION_KIND),
        InteractionScope::Local,
      );
    }
  }
}
