use binius_circuits::builder::witness::Builder;
use binius_core::constraint_system::ConstraintSystem;
use binius_field::BinaryField128b;
use bumpalo::Bump;
use std::{cell::RefCell, rc::Rc};

#[inline]
pub fn witness_builder<'a>(
    allocator: &'a Bump,
    cs: &ConstraintSystem<BinaryField128b>,
) -> Builder<'a> {
    // The following clone is cheap because `MultilinearOracleSet` is a wrapper
    // around a `Vec<Arc<_>>`.
    Builder::new(allocator, Rc::new(RefCell::new(cs.oracles.clone())))
}
