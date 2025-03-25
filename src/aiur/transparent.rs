use binius_circuits::builder::witness;
use binius_core::{
    oracle::OracleId,
    polynomial::{Error, MultivariatePoly},
};
use binius_field::{Field, TowerField, underlier::WithUnderlier};
use binius_utils::bail;

use super::layout::{AiurByteField, AiurField, FunctionIndexField, MultiplicityField};

#[derive(PartialEq, Eq, Hash)]
pub enum Virtual {
    Constant {
        constant: Fields,
        log_n: usize,
    },
    Address {
        log_n: usize,
    },
    StepDown {
        index: usize,
        log_n: usize,
    },
    Sum {
        oracles: Vec<OracleId>,
        offset: AiurByteField,
        log_n: usize,
    },
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub enum Fields {
    FunctionIndex(FunctionIndexField),
    Multiplicity(MultiplicityField),
}

#[derive(Debug, Clone)]
pub struct Address {
    n_vars: usize,
}

impl Address {
    pub fn new(n_vars: usize) -> Self {
        assert!(n_vars <= 64);
        Address { n_vars }
    }

    pub fn populate(address: OracleId, witness: &mut witness::Builder<'_>) {
        let mut slice = witness.new_column::<AiurField>(address);
        for (i, val) in slice.as_mut_slice::<AiurField>().iter_mut().enumerate() {
            *val = AiurField::from_underlier(i as u128);
        }
    }
}

impl MultivariatePoly<AiurField> for Address {
    fn degree(&self) -> usize {
        1
    }

    fn n_vars(&self) -> usize {
        self.n_vars
    }

    fn evaluate(&self, query: &[AiurField]) -> Result<AiurField, Error> {
        let n_vars = MultivariatePoly::n_vars(self);
        if query.len() != n_vars {
            bail!(Error::IncorrectQuerySize { expected: n_vars });
        }
        let mut result = AiurField::ZERO;
        let mut coeff = 1;
        for arg in query.iter() {
            result += *arg * AiurField::from_underlier(coeff);
            coeff <<= 1;
        }

        Ok(result)
    }

    fn binary_tower_level(&self) -> usize {
        AiurField::TOWER_LEVEL
    }
}
