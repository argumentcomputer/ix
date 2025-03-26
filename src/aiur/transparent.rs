use std::marker::PhantomData;

use binius_core::{
    oracle::OracleId,
    polynomial::{Error, MultivariatePoly},
};
use binius_field::{TowerField, underlier::WithUnderlier};
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
pub struct Address<F> {
    n_vars: usize,
    phantom: PhantomData<F>,
}

impl<F> Address<F> {
    pub fn new(n_vars: usize) -> Self {
        assert!(n_vars <= 64);
        let phantom = PhantomData;
        Address { n_vars, phantom }
    }
}

impl<F: TowerField + WithUnderlier<Underlier = u128>> MultivariatePoly<F> for Address<F> {
    fn degree(&self) -> usize {
        1
    }

    fn n_vars(&self) -> usize {
        self.n_vars
    }

    fn evaluate(&self, query: &[F]) -> Result<F, Error> {
        let n_vars = MultivariatePoly::<F>::n_vars(self);
        if query.len() != n_vars {
            bail!(Error::IncorrectQuerySize { expected: n_vars });
        }
        let mut result = F::ZERO;
        let mut coeff = 1;
        for arg in query.iter() {
            result += *arg * F::from_underlier(coeff);
            coeff <<= 1;
        }

        Ok(result)
    }

    fn binary_tower_level(&self) -> usize {
        F::TOWER_LEVEL
    }
}
