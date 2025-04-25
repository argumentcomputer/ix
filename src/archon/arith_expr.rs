use binius_core::oracle::OracleId;
use binius_math::ArithExpr as ArithExprCore;

use super::F;

#[derive(Clone, PartialEq)]
pub enum ArithExpr {
    Const(F),
    Var(usize),
    Oracle(OracleId),
    Add(Box<ArithExpr>, Box<ArithExpr>),
    Mul(Box<ArithExpr>, Box<ArithExpr>),
    Pow(Box<ArithExpr>, u64),
}

impl std::ops::Add for ArithExpr {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self::Add(Box::new(self), Box::new(rhs))
    }
}

impl std::ops::Mul for ArithExpr {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self::Mul(Box::new(self), Box::new(rhs))
    }
}

impl ArithExpr {
    #[inline]
    pub fn pow(self, e: u64) -> Self {
        Self::Pow(Box::new(self), e)
    }

    pub(crate) fn offset_oracles(&mut self, by: usize) {
        match self {
            Self::Oracle(o) => *o += by,
            Self::Add(a, b) | Self::Mul(a, b) => {
                a.offset_oracles(by);
                b.offset_oracles(by);
            }
            Self::Pow(a, _) => a.offset_oracles(by),
            _ => (),
        }
    }

    pub(crate) fn into_arith_expr_core(self, binds: &mut Vec<OracleId>) -> ArithExprCore<F> {
        match self {
            Self::Const(c) => ArithExprCore::Const(c),
            Self::Var(i) => ArithExprCore::Var(i),
            Self::Oracle(o) => {
                let i = binds.iter().position(|&id| o == id).unwrap_or_else(|| {
                    binds.push(o);
                    binds.len() - 1
                });
                ArithExprCore::Var(i)
            }
            Self::Add(a, b) => {
                let a = a.into_arith_expr_core(binds);
                let b = b.into_arith_expr_core(binds);
                a + b
            }
            Self::Mul(a, b) => {
                let a = a.into_arith_expr_core(binds);
                let b = b.into_arith_expr_core(binds);
                a * b
            }
            Self::Pow(a, e) => a.into_arith_expr_core(binds).pow(e),
        }
    }
}
