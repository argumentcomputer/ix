use super::*;
use crate::kzg::{KzgConfig, Scalar, domain::Radix2Coset, pcs::KzgProverData};
use multi_stark::{
  config::{LookupCommitInput, QuotientCommitInput},
  expr::Expr,
  lookup::{Lookup, LookupValues},
  system::{
    Circuit, CircuitInputs, compute_lookup_values_range, extension_params,
  },
  traits::{Algebra, EvaluationDomain as _},
};
use p3_matrix::dense::RowMajorMatrix;

fn evaluations(
  columns: &[Vec<Fr>],
  domain: Radix2EvaluationDomain<Fr>,
) -> RowMajorMatrix<Scalar> {
  let columns: Vec<_> = columns.iter().map(|c| domain.fft(c)).collect();
  RowMajorMatrix::new(
    (0..domain.size())
      .flat_map(|row| columns.iter().map(move |c| Scalar(c[row])))
      .collect(),
    columns.len(),
  )
}

fn coefficients(
  matrix: &RowMajorMatrix<Scalar>,
  domain: Radix2EvaluationDomain<Fr>,
) -> Vec<Vec<Fr>> {
  (0..matrix.width)
    .map(|column| {
      let values: Vec<_> = matrix
        .values
        .iter()
        .skip(column)
        .step_by(matrix.width)
        .map(|v| v.0)
        .collect();
      domain.ifft(&values)
    })
    .collect()
}

fn fixture(fixed: RowMajorMatrix<Scalar>) -> Circuit<Scalar> {
  let x = Expr::main(0);
  let message = vec![x.clone(), Expr::main_next(0), Expr::preprocessed_next(1)];
  let spec = CircuitInputs {
    main_width: 2,
    preprocessed: Some(fixed.clone()),
    constraints: vec![
      x.clone() * Expr::main_next(0) - Expr::preprocessed(0),
      Expr::preprocessed_next(1) - Expr::main(1),
      Expr::IsFirstRow * x.clone() + Expr::IsLastRow * Expr::main_next(0),
      Expr::IsTransition * (x - Expr::preprocessed(1)),
    ],
    lookups: vec![
      Lookup::push(
        Expr::constant(Scalar::ONE),
        vec![Expr::constant(Scalar::ZERO)],
      ),
      Lookup::push(Expr::IsFirstRow + Expr::IsLastRow, message.clone()),
      Lookup::pull(Expr::IsTransition, message.clone()),
      Lookup::push(Expr::main(1), message.clone()),
      Lookup::pull(Expr::preprocessed(0), message),
    ],
    lookup_group_size: 2,
    ..Default::default()
  };
  let graph = spec.compile_graph(&extension_params::<KzgConfig>()).unwrap();
  let groups = multi_stark::lookup::stage2_width(spec.lookups.len(), 2, 1);
  let constraint_count = graph.zeros.len() + groups;
  let max_constraint_degree = graph
    .max_constraint_degree
    .max(multi_stark::lookup::logup_max_degree(&graph, 2))
    as usize;
  Circuit {
    graph,
    main_width: 2,
    preprocessed_height: fixed.values.len() / fixed.width,
    preprocessed_width: fixed.width,
    preprocessed: Some(fixed),
    num_lookups: spec.lookups.len(),
    stage_2_width: groups,
    num_publics: 4,
    lookup_group_size: 2,
    constraint_count,
    max_constraint_degree,
  }
}

fn quotient_reference(
  input: &QuotientCommitInput<'_, KzgConfig>,
  fixed: &[Vec<Fr>],
  main: &[Vec<Fr>],
  stage2: &[Vec<Fr>],
  alpha: Scalar,
) -> Vec<Vec<Fr>> {
  let rows = input.trace_domain.size();
  let ratio = input.quotient_domain.size() / rows;
  let mut values = vec![Scalar::ZERO; rows * ratio];
  let passes = crate::kzg::quotient_plan::plan(
    &input.circuit.graph,
    input.circuit.lookup_group_size,
  );
  let mut shift = input.quotient_domain.shift;
  for coset in 0..ratio {
    let domain = Radix2Coset { log_size: input.trace_domain.log_size, shift };
    let ark_domain = Radix2EvaluationDomain::<Fr>::new(rows)
      .unwrap()
      .get_coset(shift.0)
      .unwrap();
    let main = evaluations(main, ark_domain);
    let stage2 = evaluations(stage2, ark_domain);
    for pass in &passes {
      let selected: Vec<_> =
        pass.fixed.iter().map(|&i| fixed[i].clone()).collect();
      let fixed =
        (!selected.is_empty()).then(|| evaluations(&selected, ark_domain));
      crate::kzg::quotient::evaluate_coset(
        input,
        pass,
        domain,
        fixed.as_ref(),
        &main,
        &stage2,
        alpha,
        coset,
        ratio,
        &mut values,
      );
    }
    shift *= input.quotient_domain.generator();
  }
  let domain = Radix2EvaluationDomain::<Fr>::new(rows * ratio)
    .unwrap()
    .get_coset(input.quotient_domain.shift.0)
    .unwrap();
  let values: Vec<_> = values.into_iter().map(|v| v.0).collect();
  domain.ifft(&values).chunks(rows).map(<[Fr]>::to_vec).collect()
}

fn compare_paths(log_size: usize) {
  let rows = 1 << log_size;
  let domain = Radix2Coset { log_size, shift: Scalar::ONE };
  let ark_domain = Radix2EvaluationDomain::<Fr>::new(rows).unwrap();
  let fixed = vec![vec![Fr::from(3), Fr::ONE], scalars(rows)];
  let main = vec![scalars(rows), vec![Fr::from(7)]];
  let fixed_data = KzgProverData::coefficient_fixture(domain, fixed.clone());
  let main_data = KzgProverData::coefficient_fixture(domain, main.clone());
  if log_size >= 16 {
    assert!(
      fixed_data.matrices[0].resident_columns()[1].is_some(),
      "fixture must retain fixed GPU input"
    );
    assert!(
      main_data.matrices[0].resident_columns()[0].is_some(),
      "fixture must retain main GPU input"
    );
  }
  let fixed_values = evaluations(&fixed, ark_domain);
  let main_values = evaluations(&main, ark_domain);
  let circuit = fixture(fixed_values.clone());
  for beta in [Scalar::ZERO, Scalar(Fr::from(17))] {
    let gamma = Scalar(Fr::from(23));
    let lookup_values = compute_lookup_values_range(
      &circuit.graph,
      &main_values,
      Some(&fixed_values),
      0..rows,
    );
    let (traces, totals) = LookupValues::stage_2_traces(
      &[lookup_values.clone()],
      &[circuit.lookup_group_size],
      beta,
      &gamma,
      Scalar::ZERO,
    );
    let expected = coefficients(&traces[0], ark_domain);
    let input = LookupCommitInput {
      circuit: &circuit,
      lookup_values: &lookup_values,
      preprocessed: Some((&fixed_data, 0)),
      stage_1: (&main_data, 0),
    };
    for mode in [PassMode::Off, PassMode::Force] {
      let actual = lookup::coefficients_with_mode(&input, beta, gamma, mode)
        .expect("fixture must execute CUDA lookup construction");
      assert_eq!(
        actual,
        (expected.clone(), totals[0]),
        "lookup mode={mode:?}, beta={beta:?}"
      );
    }
    let stage2 = KzgProverData::coefficient_fixture(domain, expected.clone());
    if log_size >= 16 {
      assert!(
        stage2.matrices[0].resident_columns().iter().any(Option::is_some),
        "fixture must retain lookup GPU input"
      );
    }
    let quotient_input = QuotientCommitInput {
      circuit: &circuit,
      lookup_publics: vec![beta, gamma, Scalar::ZERO, totals[0]],
      trace_domain: domain,
      quotient_domain: Radix2Coset {
        log_size: log_size + 2,
        shift: Scalar(Fr::from(7)),
      },
      preprocessed: Some((&fixed_data, 0)),
      stage_1: (&main_data, 0),
      stage_2: (&stage2, 0),
      constraint_count: circuit.constraint_count,
    };
    let alpha = Scalar(Fr::from(29));
    let reference =
      quotient_reference(&quotient_input, &fixed, &main, &expected, alpha);
    for mode in [PassMode::Off, PassMode::Force] {
      let actual =
        quotient::coefficients_with_mode(&quotient_input, alpha, mode)
          .expect("fixture must execute CUDA quotient construction");
      assert_eq!(actual, reference, "quotient mode={mode:?}, beta={beta:?}");
    }
  }
}

#[test]
#[ignore = "requires a CUDA GPU; 1024-row host inputs"]
fn dense_and_pass_constraints_match_cpu_with_zero_denominators() {
  compare_paths(10);
}

#[test]
#[ignore = "requires a CUDA GPU; 65536-row resident inputs"]
fn resident_dense_and_pass_constraints_match_cpu() {
  compare_paths(16);
}
