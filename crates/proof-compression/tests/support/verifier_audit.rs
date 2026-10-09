use multi_stark::expr::Expr;
use multi_stark::lookup::Lookup;
use multi_stark::p3_field::PrimeCharacteristicRing;
use multi_stark::system::CircuitInputs;
use multi_stark::system::ProverKey;
use multi_stark::system::System;
use multi_stark::system::SystemWitness;
use multi_stark::types::CommitmentParameters;
use multi_stark::types::FriParameters;
use multi_stark::types::GoldilocksBlake3Config as Config;
use multi_stark::types::Val;
use p3_matrix::dense::RowMajorMatrix;

pub(crate) const ACTIVE: [bool; 4] = [false, true, true, true];
pub(crate) const LOGS: [u8; 3] = [2, 3, 0];

pub(crate) fn setup() -> (System<Config>, ProverKey<Config>) {
  let x = Expr::main(0);
  System::new(
    Config::new(
      CommitmentParameters { log_blowup: 2, cap_height: 0 },
      FriParameters {
        num_queries: 2,
        log_final_poly_len: 0,
        max_log_arity: 1,
        commit_proof_of_work_bits: 3,
        query_proof_of_work_bits: 4,
      },
    ),
    [
      CircuitInputs { main_width: 1, ..Default::default() },
      CircuitInputs {
        main_width: 1,
        preprocessed: Some(RowMajorMatrix::new_col(vec![
          Val::ONE,
          Val::ZERO,
          Val::ZERO,
          Val::ZERO,
        ])),
        // Three lookups exercise a full group and a partial group.
        lookups: vec![
          Lookup::pull(
            Expr::preprocessed(0),
            vec![Expr::constant(Val::from_u8(13)), x.clone()],
          ),
          Lookup::push(x.clone(), vec![x.clone()]),
          Lookup::pull(x.clone(), vec![x.clone()]),
        ],
        lookup_group_size: 2,
        ..Default::default()
      },
      CircuitInputs {
        main_width: 2,
        constraints: vec![
          Expr::IsFirstRow * x.clone(),
          Expr::IsLastRow * (x.clone() - Expr::constant(Val::from_u8(7))),
          Expr::IsTransition
            * (Expr::main_next(0) - x.clone() - Expr::constant(Val::ONE)),
          x.clone() * x.clone() * x - Expr::main(1),
        ],
        ..Default::default()
      },
      CircuitInputs {
        main_width: 1,
        preprocessed: Some(RowMajorMatrix::new_col(vec![Val::from_u8(9)])),
        constraints: vec![Expr::main(0) - Expr::preprocessed(0)],
        ..Default::default()
      },
    ],
  )
}
pub(crate) fn claims() -> Vec<Vec<Val>> {
  vec![vec![Val::from_u8(13), Val::from_u8(42)]]
}
pub(crate) fn witness(system: &System<Config>) -> SystemWitness<Val> {
  SystemWitness::from_stage_1(
    vec![
      RowMajorMatrix::new_col(vec![]),
      RowMajorMatrix::new_col(vec![Val::from_u8(42); 4]),
      RowMajorMatrix::new(
        (0..8)
          .flat_map(|i| {
            let x = Val::from_u8(i);
            [x, x * x * x]
          })
          .collect(),
        2,
      ),
      RowMajorMatrix::new_col(vec![Val::from_u8(9)]),
    ],
    system,
  )
}
