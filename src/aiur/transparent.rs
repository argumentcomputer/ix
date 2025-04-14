use binius_circuits::builder::witness;
use binius_core::{
    oracle::OracleId,
    polynomial::{Error, MultivariatePoly},
};
use binius_field::{Field, TowerField, underlier::WithUnderlier};
use binius_utils::bail;

use super::layout::{B1, B8, B32, B64, B128};

#[derive(PartialEq, Debug, Eq, Hash)]
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
        offset: B64,
        log_n: usize,
    },
}

#[derive(PartialEq, Debug, Eq, Hash, Clone, Copy)]
pub enum Fields {
    B1(B1),
    B8(B8),
    B32(B32),
    B64(B64),
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
        let mut slice = witness.new_column::<B128>(address);
        for (i, val) in slice.as_mut_slice::<B128>().iter_mut().enumerate() {
            *val = B128::from_underlier(i as u128);
        }
    }
}

impl MultivariatePoly<B128> for Address {
    fn degree(&self) -> usize {
        1
    }

    fn n_vars(&self) -> usize {
        self.n_vars
    }

    fn evaluate(&self, query: &[B128]) -> Result<B128, Error> {
        let n_vars = MultivariatePoly::n_vars(self);
        if query.len() != n_vars {
            bail!(Error::IncorrectQuerySize { expected: n_vars });
        }
        let mut result = B128::ZERO;
        let mut coeff = 1;
        for arg in query.iter() {
            result += *arg * B128::from_underlier(coeff);
            coeff <<= 1;
        }

        Ok(result)
    }

    fn binary_tower_level(&self) -> usize {
        B64::TOWER_LEVEL
    }
}
