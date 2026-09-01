//! The backend's constraint IR.
//!
//! Aiur circuits arrive as [`multi_stark::expr::Expr`] trees over the
//! frontend field. This module converts them into a small internal AST over
//! the Hypercube base field ([`F`]), computes degrees, extracts the affine
//! forms Hypercube's lookup argument needs for interaction messages, and
//! lowers whatever is not affine into materialized columns.

use multi_stark::{
  expr::{Expr, RowOffset, Source},
  lookup::Lookup,
  p3_field::PrimeField64,
};
use slop_air::AirBuilderWithPublicValues;
use slop_algebra::{AbstractField, PrimeField32};

use crate::F;

/// A column of a committed trace, at the current row.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Col {
  Main(usize),
  Preprocessed(usize),
}

/// A base-field expression over trace columns, public values and constants.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ast {
  Const(F),
  Col(Col),
  Public(usize),
  Add(Box<Ast>, Box<Ast>),
  Sub(Box<Ast>, Box<Ast>),
  Mul(Box<Ast>, Box<Ast>),
  Neg(Box<Ast>),
}

/// An affine combination of columns: `constant + Σ coeff · col`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Affine {
  pub constant: F,
  pub terms: Vec<(Col, F)>,
}

/// Why a frontend circuit cannot be expressed in the Hypercube backend.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConvertError {
  /// The frontend field is not the backend field. Field elements are
  /// converted by canonical value, which is only meaningful when the
  /// moduli agree.
  FieldMismatch { frontend: u64, backend: u64 },
  /// Hypercube constraints are row-local: there is no "next row".
  NextRowUnsupported,
  /// Hypercube has no row-position selectors.
  RowSelectorUnsupported(&'static str),
  /// The frontend's public inputs are protocol-owned (logUp challenges) and
  /// have no backend counterpart.
  PublicUnsupported,
  /// The frontend's stage-2 (lookup accumulator) columns are protocol-owned.
  Stage2Unsupported,
  /// A constraint exceeds Hypercube's maximum constraint degree.
  DegreeTooHigh { degree: usize, max: usize },
}

impl std::fmt::Display for ConvertError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::FieldMismatch { frontend, backend } => write!(
        f,
        "frontend field modulus {frontend} differs from backend field modulus {backend}"
      ),
      Self::NextRowUnsupported => {
        write!(f, "next-row column references are not supported by Hypercube")
      },
      Self::RowSelectorUnsupported(sel) => {
        write!(f, "row selector `{sel}` is not supported by Hypercube")
      },
      Self::PublicUnsupported => {
        write!(f, "frontend public inputs have no Hypercube counterpart")
      },
      Self::Stage2Unsupported => {
        write!(f, "frontend stage-2 columns have no Hypercube counterpart")
      },
      Self::DegreeTooHigh { degree, max } => {
        write!(f, "constraint degree {degree} exceeds the maximum {max}")
      },
    }
  }
}

impl std::error::Error for ConvertError {}

/// Checks that the frontend field `FF` is the backend field, so that
/// converting elements by canonical value preserves arithmetic.
pub fn check_field<FF: PrimeField64>() -> Result<(), ConvertError> {
  let frontend = FF::ORDER_U64;
  let backend = u64::from(F::ORDER_U32);
  if frontend == backend {
    Ok(())
  } else {
    Err(ConvertError::FieldMismatch { frontend, backend })
  }
}

/// Converts a frontend field element by canonical value. Only sound after
/// [`check_field`] succeeded.
#[inline]
pub fn convert_element<FF: PrimeField64>(x: FF) -> F {
  let canonical = x.as_canonical_u64();
  let canonical = u32::try_from(canonical)
    .expect("frontend element does not fit the backend field");
  F::from_canonical_u32(canonical)
}

impl Ast {
  pub fn constant(x: F) -> Self {
    Self::Const(x)
  }

  pub fn main(i: usize) -> Self {
    Self::Col(Col::Main(i))
  }

  pub fn preprocessed(i: usize) -> Self {
    Self::Col(Col::Preprocessed(i))
  }

  /// Converts a frontend expression into the backend AST.
  pub fn from_expr<FF: PrimeField64>(
    expr: &Expr<FF>,
  ) -> Result<Self, ConvertError> {
    let bin = |x: &Expr<FF>, y: &Expr<FF>| -> Result<(Box<Ast>, Box<Ast>), _> {
      Ok((Box::new(Self::from_expr(x)?), Box::new(Self::from_expr(y)?)))
    };
    let ast = match expr {
      Expr::Const(c) => Self::Const(convert_element(*c)),
      Expr::Var(col) => {
        if col.offset != RowOffset::Current {
          return Err(ConvertError::NextRowUnsupported);
        }
        let index = col.index as usize;
        match col.source {
          Source::Main => Self::Col(Col::Main(index)),
          Source::Preprocessed => Self::Col(Col::Preprocessed(index)),
          Source::Stage2 => return Err(ConvertError::Stage2Unsupported),
        }
      },
      Expr::Public(_) => return Err(ConvertError::PublicUnsupported),
      Expr::IsFirstRow => {
        return Err(ConvertError::RowSelectorUnsupported("is_first_row"));
      },
      Expr::IsLastRow => {
        return Err(ConvertError::RowSelectorUnsupported("is_last_row"));
      },
      Expr::IsTransition => {
        return Err(ConvertError::RowSelectorUnsupported("is_transition"));
      },
      Expr::Add(x, y) => {
        let (x, y) = bin(x, y)?;
        Self::Add(x, y)
      },
      Expr::Sub(x, y) => {
        let (x, y) = bin(x, y)?;
        Self::Sub(x, y)
      },
      Expr::Mul(x, y) => {
        let (x, y) = bin(x, y)?;
        Self::Mul(x, y)
      },
      Expr::Neg(x) => Self::Neg(Box::new(Self::from_expr(x)?)),
    };
    Ok(ast)
  }

  /// The polynomial degree of the expression in the trace columns. Public
  /// values are verifier-known and count as constants.
  pub fn degree(&self) -> usize {
    match self {
      Self::Const(_) | Self::Public(_) => 0,
      Self::Col(_) => 1,
      Self::Add(x, y) | Self::Sub(x, y) => x.degree().max(y.degree()),
      Self::Mul(x, y) => x.degree() + y.degree(),
      Self::Neg(x) => x.degree(),
    }
  }

  /// The affine form of the expression, if it has degree at most one and
  /// does not reference public values (interaction messages can only read
  /// trace columns).
  pub fn to_affine(&self) -> Option<Affine> {
    match self {
      Self::Const(c) => Some(Affine { constant: *c, terms: vec![] }),
      Self::Col(col) => {
        Some(Affine { constant: F::zero(), terms: vec![(*col, F::one())] })
      },
      Self::Public(_) => None,
      Self::Add(x, y) => {
        let mut x = x.to_affine()?;
        let y = y.to_affine()?;
        x.constant += y.constant;
        x.terms.extend(y.terms);
        Some(x.normalized())
      },
      Self::Sub(x, y) => {
        let mut x = x.to_affine()?;
        let y = y.to_affine()?;
        x.constant -= y.constant;
        x.terms.extend(y.terms.into_iter().map(|(c, w)| (c, -w)));
        Some(x.normalized())
      },
      Self::Mul(x, y) => {
        let x = x.to_affine()?;
        let y = y.to_affine()?;
        // Exactly one side may carry columns.
        if x.terms.is_empty() {
          Some(y.scaled(x.constant))
        } else if y.terms.is_empty() {
          Some(x.scaled(y.constant))
        } else {
          None
        }
      },
      Self::Neg(x) => Some(x.to_affine()?.scaled(-F::one())),
    }
  }

  /// Evaluates the expression on concrete row values.
  pub fn eval_row(&self, preprocessed: &[F], main: &[F], publics: &[F]) -> F {
    match self {
      Self::Const(c) => *c,
      Self::Col(Col::Main(i)) => main[*i],
      Self::Col(Col::Preprocessed(i)) => preprocessed[*i],
      Self::Public(i) => publics[*i],
      Self::Add(x, y) => {
        x.eval_row(preprocessed, main, publics)
          + y.eval_row(preprocessed, main, publics)
      },
      Self::Sub(x, y) => {
        x.eval_row(preprocessed, main, publics)
          - y.eval_row(preprocessed, main, publics)
      },
      Self::Mul(x, y) => {
        x.eval_row(preprocessed, main, publics)
          * y.eval_row(preprocessed, main, publics)
      },
      Self::Neg(x) => -x.eval_row(preprocessed, main, publics),
    }
  }

  /// Evaluates the expression symbolically inside an AIR builder.
  pub fn eval_air<AB>(
    &self,
    preprocessed: &[AB::Var],
    main: &[AB::Var],
    builder: &AB,
  ) -> AB::Expr
  where
    AB: AirBuilderWithPublicValues<F = F>,
  {
    match self {
      Self::Const(c) => AB::Expr::from(*c),
      Self::Col(Col::Main(i)) => main[*i].into(),
      Self::Col(Col::Preprocessed(i)) => preprocessed[*i].into(),
      Self::Public(i) => builder.public_values()[*i].into(),
      Self::Add(x, y) => {
        x.eval_air(preprocessed, main, builder)
          + y.eval_air(preprocessed, main, builder)
      },
      Self::Sub(x, y) => {
        x.eval_air(preprocessed, main, builder)
          - y.eval_air(preprocessed, main, builder)
      },
      Self::Mul(x, y) => {
        x.eval_air(preprocessed, main, builder)
          * y.eval_air(preprocessed, main, builder)
      },
      Self::Neg(x) => -x.eval_air(preprocessed, main, builder),
    }
  }
}

impl std::ops::Add for Ast {
  type Output = Ast;
  fn add(self, rhs: Ast) -> Ast {
    Ast::Add(Box::new(self), Box::new(rhs))
  }
}

impl std::ops::Sub for Ast {
  type Output = Ast;
  fn sub(self, rhs: Ast) -> Ast {
    Ast::Sub(Box::new(self), Box::new(rhs))
  }
}

impl std::ops::Mul for Ast {
  type Output = Ast;
  fn mul(self, rhs: Ast) -> Ast {
    Ast::Mul(Box::new(self), Box::new(rhs))
  }
}

impl std::ops::Neg for Ast {
  type Output = Ast;
  fn neg(self) -> Ast {
    Ast::Neg(Box::new(self))
  }
}

impl Affine {
  fn scaled(mut self, k: F) -> Self {
    self.constant *= k;
    for (_, w) in &mut self.terms {
      *w *= k;
    }
    self.normalized()
  }

  /// Merges duplicate columns and drops zero coefficients, so the form is
  /// canonical and cheap to evaluate.
  fn normalized(mut self) -> Self {
    self.terms.sort_by_key(|(col, _)| *col);
    let mut merged: Vec<(Col, F)> = Vec::with_capacity(self.terms.len());
    for (col, w) in self.terms.drain(..) {
      match merged.last_mut() {
        Some((last, acc)) if *last == col => *acc += w,
        _ => merged.push((col, w)),
      }
    }
    merged.retain(|(_, w)| *w != F::zero());
    self.terms = merged;
    self
  }

  /// Evaluates the affine form on concrete row values.
  pub fn eval_row(&self, preprocessed: &[F], main: &[F]) -> F {
    self.terms.iter().fold(self.constant, |acc, (col, w)| {
      let v = match col {
        Col::Main(i) => main[*i],
        Col::Preprocessed(i) => preprocessed[*i],
      };
      acc + *w * v
    })
  }

  /// Evaluates the affine form symbolically inside an AIR builder.
  pub fn eval_air<AB>(
    &self,
    preprocessed: &[AB::Var],
    main: &[AB::Var],
  ) -> AB::Expr
  where
    AB: AirBuilderWithPublicValues<F = F>,
  {
    self.terms.iter().fold(AB::Expr::from(self.constant), |acc, (col, w)| {
      let v: AB::Expr = match col {
        Col::Main(i) => main[*i].into(),
        Col::Preprocessed(i) => preprocessed[*i].into(),
      };
      acc + v * AB::Expr::from(*w)
    })
  }
}

/// One Hypercube interaction: a signed multiplicity and a message, both
/// affine in the trace columns. Aiur's push/pull convention is carried by
/// the sign of the multiplicity, so every lookup is emitted as a `send`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interaction {
  pub multiplicity: Affine,
  pub values: Vec<Affine>,
}

/// A circuit lowered to what the Hypercube chip evaluates directly.
#[derive(Clone, Debug)]
pub struct Lowered {
  /// Main width including the materialized columns.
  pub main_width: usize,
  /// The frontend main width (the prefix of the trace the frontend fills).
  pub frontend_width: usize,
  /// Zero constraints, including one `col − expr` per materialized column.
  pub constraints: Vec<Ast>,
  pub interactions: Vec<Interaction>,
  /// Extra columns appended to the frontend trace: `(column, expression)`,
  /// filled by evaluating the expression on each row.
  pub materialized: Vec<(usize, Ast)>,
}

impl Lowered {
  /// Lowers frontend constraints and lookups. Non-affine lookup arguments
  /// and multiplicities are materialized into fresh columns.
  pub fn from_frontend<FF: PrimeField64>(
    main_width: usize,
    constraints: &[Expr<FF>],
    lookups: &[Lookup<Expr<FF>>],
  ) -> Result<Self, ConvertError> {
    let constraints =
      constraints.iter().map(Ast::from_expr).collect::<Result<Vec<_>, _>>()?;
    let lookups = lookups
      .iter()
      .map(|l| {
        let multiplicity = Ast::from_expr(&l.multiplicity)?;
        let args =
          l.args.iter().map(Ast::from_expr).collect::<Result<Vec<_>, _>>()?;
        Ok((multiplicity, args))
      })
      .collect::<Result<Vec<_>, ConvertError>>()?;
    Self::new(main_width, constraints, lookups)
  }

  /// Lowers backend-AST constraints and lookups (`(multiplicity, args)`).
  pub fn new(
    main_width: usize,
    mut constraints: Vec<Ast>,
    lookups: Vec<(Ast, Vec<Ast>)>,
  ) -> Result<Self, ConvertError> {
    let mut materialized: Vec<(usize, Ast)> = Vec::new();
    let mut next_col = main_width;
    let mut affine = |expr: Ast| -> Affine {
      if let Some(a) = expr.to_affine() {
        return a;
      }
      // Reuse a column already materializing an identical expression.
      let col = match materialized.iter().find(|(_, e)| *e == expr) {
        Some((col, _)) => *col,
        None => {
          let col = next_col;
          next_col += 1;
          materialized.push((col, expr));
          col
        },
      };
      Affine { constant: F::zero(), terms: vec![(Col::Main(col), F::one())] }
    };
    let interactions = lookups
      .into_iter()
      .map(|(multiplicity, args)| Interaction {
        multiplicity: affine(multiplicity),
        values: args.into_iter().map(&mut affine).collect(),
      })
      .collect::<Vec<_>>();
    constraints.extend(
      materialized.iter().map(|(col, expr)| Ast::main(*col) - expr.clone()),
    );
    let max = sp1_hypercube::MAX_CONSTRAINT_DEGREE;
    for c in &constraints {
      let degree = c.degree();
      if degree > max {
        return Err(ConvertError::DegreeTooHigh { degree, max });
      }
    }
    Ok(Self {
      main_width: next_col,
      frontend_width: main_width,
      constraints,
      interactions,
      materialized,
    })
  }
}
