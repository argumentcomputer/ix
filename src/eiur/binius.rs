use binius_circuits::builder::witness::Builder;
use binius_core::constraint_system::ConstraintSystem;
use binius_field::{as_packed_field::PackScalar, TowerField};
use bumpalo::Bump;
use std::{cell::RefCell, rc::Rc};

#[inline]
pub fn witness_builder<'a, F: TowerField, U: PackScalar<F>>(
    allocator: &'a Bump,
    cs: &ConstraintSystem<F>,
) -> Builder<'a, U, F> {
    Builder::new(allocator, Rc::new(RefCell::new(cs.oracles.clone())))
}
