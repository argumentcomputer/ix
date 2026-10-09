//! Fixed-shape inner proof fixture for the Plonkish verifier experiment.
//!
//! Each function has 128 slots, with argument `n` fixed in slot `n` by
//! preprocessing. A live row consumes its call and (unless `n == 0`) emits
//! a call to the other function at `n - 1`, with the same return value.
//! Unused slots contain `[live = 0, result = 0]` and emit no messages.
//! This deliberately supports one public root call, not arbitrary batches.

use multi_stark::expr::Expr;
use multi_stark::lookup::Lookup;
use multi_stark::p3_field::PrimeCharacteristicRing;
use multi_stark::p3_matrix::dense::RowMajorMatrix;
use multi_stark::system::CircuitInputs;
use multi_stark::types::CommitmentParameters;
use multi_stark::types::FriParameters;
use multi_stark::types::GoldilocksBlake3Config;
use multi_stark::types::Val;

pub(crate) const HEIGHT: usize = 128;
pub(crate) const LOG_HEIGHT: u8 = 7;
pub(crate) const NUM_QUERIES: usize = 4;

#[derive(Clone, Copy, Debug)]
pub(crate) enum Function {
  Even,
  Odd,
}

impl Function {
  pub(crate) const ALL: [Self; 2] = [Self::Even, Self::Odd];

  pub(crate) fn index(self) -> usize {
    match self {
      Self::Even => 0,
      Self::Odd => 1,
    }
  }

  fn other(self) -> Self {
    match self {
      Self::Even => Self::Odd,
      Self::Odd => Self::Even,
    }
  }

  pub(crate) fn result(self, n: usize) -> bool {
    n % 2 == self.index()
  }
}

/// Tiny test parameters, NOT a production security configuration.
pub(crate) fn config() -> GoldilocksBlake3Config {
  GoldilocksBlake3Config::new(
    CommitmentParameters { log_blowup: 1, cap_height: 0 },
    FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: NUM_QUERIES,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    },
  )
}

pub(crate) fn circuit_inputs() -> Vec<CircuitInputs<Val>> {
  Function::ALL
    .into_iter()
    .map(|function| {
      let one = Expr::constant(Val::ONE);
      let live = Expr::main(0);
      let result = Expr::main(1);
      let n = Expr::preprocessed(0);
      let base = Expr::preprocessed(1);
      let tag = Expr::constant(Val::from_usize(function.index()));
      let other_tag = Expr::constant(Val::from_usize(function.other().index()));
      let base_result = Expr::constant(Val::from_bool(function.result(0)));
      CircuitInputs {
        main_width: 2,
        preprocessed: Some(RowMajorMatrix::new(
          (0..HEIGHT)
            .flat_map(|n| [Val::from_usize(n), Val::from_bool(n == 0)])
            .collect(),
          2,
        )),
        constraints: vec![
          live.clone() * (live.clone() - one.clone()),
          result.clone() * (result.clone() - one.clone()),
          (one.clone() - live.clone()) * result.clone(),
          base.clone() * (result.clone() - base_result * live.clone()),
        ],
        lookups: vec![
          Lookup::pull(live.clone(), vec![tag, n.clone(), result.clone()]),
          Lookup::push(
            live * (one.clone() - base),
            vec![other_tag, n - one, result],
          ),
        ],
        ..Default::default()
      }
    })
    .collect()
}

/// The verifier supplies the expected result independently of the witness.
pub(crate) fn claim(function: Function, n: usize, expected: bool) -> Vec<Val> {
  assert!(n < HEIGHT, "parity fixture supports arguments 0..128");
  vec![
    Val::from_usize(function.index()),
    Val::from_usize(n),
    Val::from_bool(expected),
  ]
}

pub(crate) fn traces(function: Function, n: usize) -> Vec<RowMajorMatrix<Val>> {
  assert!(n < HEIGHT, "parity fixture supports arguments 0..128");
  let mut traces: Vec<_> = Function::ALL
    .iter()
    .map(|_| RowMajorMatrix::new(vec![Val::ZERO; HEIGHT * 2], 2))
    .collect();
  let mut callee = function;
  for argument in (0..=n).rev() {
    let row = &mut traces[callee.index()].values[argument * 2..][..2];
    row.copy_from_slice(&[Val::ONE, Val::from_bool(callee.result(argument))]);
    callee = callee.other();
  }
  traces
}
