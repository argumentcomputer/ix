use std::marker::PhantomData;

use binius_core::polynomial::{Error, MultivariatePoly};
use binius_field::{TowerField, underlier::WithUnderlier};
use binius_utils::bail;

#[derive(Debug, Clone)]
pub struct Index<F> {
    n_vars: usize,
    phantom: PhantomData<F>,
}

impl<F> Index<F> {
    pub fn new(n_vars: usize) -> Self {
        assert!(n_vars <= 64);
        let phantom = PhantomData;
        Index { n_vars, phantom }
    }
}

impl<F: TowerField + WithUnderlier<Underlier = u128>> MultivariatePoly<F> for Index<F> {
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
