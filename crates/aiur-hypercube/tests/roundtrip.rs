//! End-to-end: Aiur-style circuits (frontend `Expr`/`Lookup` IR over
//! KoalaBear) proved and verified with the Hypercube backend.

use aiur_hypercube::{
  AiurMachine, CircuitSpec, ProverParams,
  expr::{Ast, ConvertError, Lowered},
  prove, verify,
};
use multi_stark::{
  expr::Expr, lookup::Lookup, p3_field::PrimeCharacteristicRing,
  p3_matrix::dense::RowMajorMatrix,
};
use p3_koala_bear::KoalaBear as FF;

const FN_CHANNEL: u32 = 0;
const SQUARE_CHANNEL: u32 = 7;

fn k(x: u32) -> Expr<FF> {
  Expr::constant(FF::from_u32(x))
}

fn m(i: u32) -> Expr<FF> {
  Expr::main(i)
}

/// A memoized "squares" table: columns `[mult, x, x²]`. Provides
/// `(SQUARE_CHANNEL, x, x²)` with multiplicity `mult` (a pull, i.e. negated).
fn squares_spec() -> CircuitSpec<FF> {
  CircuitSpec {
    name: "Squares".into(),
    main_width: 3,
    preprocessed: None,
    constraints: vec![m(2) - m(1) * m(1)],
    lookups: vec![Lookup {
      multiplicity: -m(0),
      args: vec![k(SQUARE_CHANNEL), m(1), m(2)],
    }],
  }
}

/// An Aiur-style function `f(x) = x² + 1`: columns `[x, sel, mult, sq, out]`.
/// Written "branching-style": lookup arguments are selector-gated, so they
/// are degree 2 and the backend must materialize them.
fn function_spec() -> CircuitSpec<FF> {
  let (x, sel, mult, sq, out) = (m(0), m(1), m(2), m(3), m(4));
  let gate = |e: Expr<FF>| sel.clone() * e;
  CircuitSpec {
    name: "F".into(),
    main_width: 5,
    preprocessed: None,
    constraints: vec![
      sel.clone() * (sel.clone() - k(1)),
      gate(out.clone() - sq.clone() - k(1)),
    ],
    lookups: vec![
      // Return provide: pulls (FN_CHANNEL, fn_idx = 0, x, out) `mult` times.
      Lookup {
        multiplicity: -mult,
        args: vec![gate(k(FN_CHANNEL)), gate(k(0)), gate(x.clone()), gate(out)],
      },
      // Requires x² from the squares table.
      Lookup {
        multiplicity: sel.clone(),
        args: vec![gate(k(SQUARE_CHANNEL)), gate(x), gate(sq)],
      },
    ],
  }
}

fn machine() -> AiurMachine {
  AiurMachine::build(vec![squares_spec(), function_spec()], &[], 4).unwrap()
}

fn params() -> ProverParams {
  ProverParams { log_blowup: 1, log_stacking_height: 14, max_log_row_count: 12 }
}

fn f(x: u32) -> FF {
  FF::from_u32(x)
}

struct Witness {
  squares: Vec<[u32; 3]>,
  function: Vec<[u32; 5]>,
  claim: [u32; 4],
}

fn honest_witness() -> Witness {
  Witness {
    // (mult, x, x²): x = 3 is required once by the function row.
    squares: vec![[1, 3, 9], [1, 5, 25]],
    // (x, sel, mult, sq, out): the claimed entry f(3) = 10, plus a row
    // f(5) = 26 that nobody asked for (mult 0) but that still requires 25.
    function: vec![[3, 1, 1, 9, 10], [5, 1, 0, 25, 26]],
    claim: [FN_CHANNEL, 0, 3, 10],
  }
}

fn run(w: &Witness) -> Result<(), String> {
  let machine = machine();
  let squares =
    RowMajorMatrix::new(w.squares.iter().flatten().map(|&x| f(x)).collect(), 3);
  let function = RowMajorMatrix::new(
    w.function.iter().flatten().map(|&x| f(x)).collect(),
    5,
  );
  let claim: Vec<FF> = w.claim.iter().map(|&x| f(x)).collect();
  // The trailing `None` is the (empty) memory-boundary main trace.
  let record = machine
    .record(vec![Some(squares), Some(function), None], &claim)
    .map_err(|e| e.to_string())?;
  let (vk, proof) = prove(&machine, vec![record], params());
  verify(&machine, params(), &vk, &proof)
    .map(|_| ())
    .map_err(|e| format!("{e:?}"))
}

#[test]
fn honest_proof_verifies() {
  run(&honest_witness()).unwrap();
}

#[test]
fn wrong_multiplicity_fails() {
  let mut w = honest_witness();
  // Claim x = 3 was never required: the lookup argument must not balance.
  w.squares[0][0] = 0;
  assert!(run(&w).is_err());
}

#[test]
fn wrong_claim_fails() {
  let mut w = honest_witness();
  // The public claim says f(3) = 11 while the function row computes 10.
  w.claim[3] = 11;
  assert!(run(&w).is_err());
}

#[test]
fn materializes_gated_lookup_arguments() {
  let spec = function_spec();
  let lowered =
    Lowered::from_frontend(spec.main_width, &spec.constraints, &spec.lookups)
      .unwrap();
  // Gated constants (`sel * c`) are still affine. The gated columns are
  // `sel * x` (shared by both lookups), `sel * out` and `sel * sq`, so 3
  // columns are materialized. The multiplicities `-mult` and `sel` stay
  // affine too.
  assert_eq!(lowered.materialized.len(), 3);
  assert_eq!(lowered.main_width, 5 + 3);
  assert_eq!(lowered.constraints.len(), 2 + 3);
  // Every interaction message is now at most a single column (gated
  // constants reduce to constants).
  for interaction in &lowered.interactions {
    for value in &interaction.values {
      assert!(value.terms.len() <= 1);
    }
  }
}

#[test]
fn rejects_unsupported_frontend_features() {
  let next: Expr<FF> = Expr::main_next(0) - m(0);
  assert_eq!(
    Lowered::from_frontend(1, &[next], &[]).unwrap_err(),
    ConvertError::NextRowUnsupported
  );
  let transition: Expr<FF> = Expr::IsTransition * m(0);
  assert_eq!(
    Lowered::from_frontend(1, &[transition], &[]).unwrap_err(),
    ConvertError::RowSelectorUnsupported("is_transition")
  );
  let quartic: Expr<FF> = m(0) * m(0) * m(0) * m(0);
  assert_eq!(
    Lowered::from_frontend(1, &[quartic], &[]).unwrap_err(),
    ConvertError::DegreeTooHigh { degree: 4, max: 3 }
  );
}

#[test]
fn affine_extraction_is_canonical() {
  use aiur_hypercube::F;
  use slop_algebra::AbstractField;
  // 2·c0 + c1 − c0 + 5 → c0 + c1 + 5
  let two = Ast::constant(F::from_canonical_u32(2));
  let five = Ast::constant(F::from_canonical_u32(5));
  let e = two * Ast::main(0) + Ast::main(1) - Ast::main(0) + five;
  let a = e.to_affine().unwrap();
  assert_eq!(a.constant, F::from_canonical_u32(5));
  assert_eq!(a.terms.len(), 2);
  assert!(a.terms.iter().all(|(_, w)| *w == F::one()));
  // Products of two columns are not affine.
  assert!((Ast::main(0) * Ast::main(1)).to_affine().is_none());
}
