pub mod uint_add;
pub mod uint_sub;

use anyhow::Result;
use binius_circuits::builder::{ConstraintSystemBuilder, witness::Builder};
use binius_core::oracle::OracleId;

/// Trait for Aiur-compatible gadgets
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
    fn constrain(
        builder: &mut ConstraintSystemBuilder<'_>,
        name: impl ToString,
        input: Self::InputOracles,
        enabled: OracleId,
        config: Self::Config,
    ) -> Result<Self::VirtualOracles>;
    /// Populates the columns with witness data that satisfy the constraints.
    fn generate_witness(
        builder: &mut Builder<'_>,
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
