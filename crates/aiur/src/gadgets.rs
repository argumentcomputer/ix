pub(crate) mod bytes1;
pub(crate) mod bytes2;

use multi_stark::{
  builder::symbolic::SymbolicExpression,
  lookup::{Lookup, LookupValues},
  p3_matrix::dense::RowMajorMatrix,
};

use crate::{G, execute::QueryRecord};

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

  /// Returns the witness data for the prover, including a row-major trace matrix and
  /// the flat lookup values.
  ///
  /// `slot_arg_widths[j]` must be the maximum number of arguments of lookup slot `j`,
  /// derived from the symbolic lookups returned by the `lookups` method so the witness
  /// layout always matches the AIR.
  fn witness_data(
    &self,
    record: &QueryRecord,
    slot_arg_widths: &[usize],
  ) -> (RowMajorMatrix<G>, LookupValues<G>);
}
