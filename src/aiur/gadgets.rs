pub(crate) mod bytes1;
pub(crate) mod bytes2;

use multi_stark::{
  builder::symbolic::SymbolicExpression, lookup::Lookup,
  p3_matrix::dense::RowMajorMatrix,
};

use crate::aiur::{G, execute::QueryRecord};

/// A trait representing a generic Aiur gadget.
///
/// Gadgets define small, reusable components for Aiur. Implementing this trait
/// requires a gadget to define:
///
/// - How many outputs it produces for a given operation.
/// - How to execute its computation on concrete inputs.
/// - Which symbolic lookups it requires during circuit synthesis.
/// - How to provide witness data for the prover.
pub(crate) trait AiurGadget {
  /// The type representing the gadget's operation.
  type Op;

  /// Returns the number of output values this gadget produces for the given operation.
  fn output_size(&self, op: &Self::Op) -> usize;

  /// Executes the gadget on concrete inputs, returning the resulting output values.
  fn execute(
    &self,
    op: &Self::Op,
    input: &[G],
    record: &mut QueryRecord,
  ) -> Vec<G>;

  /// Returns the symbolic lookups associated with this gadget.
  fn lookups(&self) -> Vec<Lookup<SymbolicExpression<G>>>;

  /// Returns the witness data (stage 1 main trace) for the prover. Concrete
  /// per-row lookup values are derived in `multi_stark::Lookup::stage_2_traces`
  /// from this trace plus the symbolic lookups returned by `lookups`.
  fn witness_data(&self, record: &QueryRecord) -> RowMajorMatrix<G>;
}
