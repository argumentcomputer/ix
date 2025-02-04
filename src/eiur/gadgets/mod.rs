pub mod uint_add;
pub mod uint_sub;

use anyhow::Result;
use binius_circuits::builder::{witness::Builder, ConstraintSystemBuilder};
use binius_core::oracle::OracleId;
use binius_field::{
    as_packed_field::PackScalar, underlier::UnderlierType, BinaryField1b as B1, TowerField,
};
use bytemuck::Pod;

/// Trait for Eiur-compatible gadgets
pub trait Gadget {
    /// Type for the set of input oracles, usually associated with committed columns
    type InputOracles;
    /// Type for the set of virtual columns, returned by the constraining algorithm
    type VirtualOracles;
    /// Type for arbitrary configurations that a gadget may receive
    type Config;
    /// Creates the constraints for the gadget. New columns, if needed, should be
    /// transparent and returned. The constraints should be relaxed where `enabled`
    /// is zero.
    fn constrain<F: TowerField, U: UnderlierType + PackScalar<F>>(
        builder: &mut ConstraintSystemBuilder<U, F>,
        name: impl ToString,
        input: Self::InputOracles,
        enabled: OracleId,
        config: Self::Config,
    ) -> Result<Self::VirtualOracles>;
    /// Populates the columns with witness data that satisfy the constraints.
    fn generate_witness<F: TowerField, U: PackScalar<F> + PackScalar<B1> + Pod>(
        builder: &mut Builder<U, F>,
        input: Self::InputOracles,
        vrtual: Self::VirtualOracles,
        config: Self::Config,
    ) -> Result<()>;
}

pub enum UIntType {
    U8,
    U16,
    U32,
    U64,
}

impl UIntType {
    const fn n_vars(&self) -> usize {
        match self {
            Self::U8 => 3,
            Self::U16 => 4,
            Self::U32 => 5,
            Self::U64 => 6,
        }
    }
}
