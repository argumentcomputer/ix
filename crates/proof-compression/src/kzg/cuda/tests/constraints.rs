use super::*;
use crate::kzg::{
  CurveScalar, KzgConfig,
  curve::{Bls12381, Bn254},
  domain::Radix2Coset,
  pcs::KzgProverData,
};
use multi_stark::{
  config::{LookupCommitInput, QuotientCommitInput},
  expr::Expr,
  lookup::{Lookup, LookupValues},
  system::{
    Circuit, CircuitInputs, compute_lookup_values_range, extension_params,
  },
  traits::{Algebra, EvaluationDomain as _, Field as _},
};
use p3_matrix::dense::RowMajorMatrix;

fn evaluations<C: KzgCurve>(
  columns: &[Vec<C::Fr>],
  domain: Radix2EvaluationDomain<C::Fr>,
) -> RowMajorMatrix<CurveScalar<C>> {
  let columns: Vec<_> = columns.iter().map(|c| domain.fft(c)).collect();
  RowMajorMatrix::new(
    (0..domain.size())
      .flat_map(|row| columns.iter().map(move |c| CurveScalar(c[row])))
      .collect(),
    columns.len(),
  )
}

fn coefficients<C: KzgCurve>(
  matrix: &RowMajorMatrix<CurveScalar<C>>,
  domain: Radix2EvaluationDomain<C::Fr>,
) -> Vec<Vec<C::Fr>> {
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

fn fixture<C: KzgCurve>(
  fixed: RowMajorMatrix<CurveScalar<C>>,
) -> Circuit<CurveScalar<C>> {
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
        Expr::constant(CurveScalar::<C>::ONE),
        vec![Expr::constant(CurveScalar::<C>::ZERO)],
      ),
      Lookup::push(Expr::IsFirstRow + Expr::IsLastRow, message.clone()),
      Lookup::pull(Expr::IsTransition, message.clone()),
      Lookup::push(Expr::main(1), message.clone()),
      Lookup::pull(Expr::preprocessed(0), message),
    ],
    lookup_group_size: 2,
    ..Default::default()
  };
  let graph = spec.compile_graph(&extension_params::<KzgConfig<C>>()).unwrap();
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

fn quotient_reference<C: KzgCurve>(
  input: &QuotientCommitInput<'_, KzgConfig<C>>,
  fixed: &[Vec<C::Fr>],
  main: &[Vec<C::Fr>],
  stage2: &[Vec<C::Fr>],
  alpha: CurveScalar<C>,
) -> Vec<Vec<C::Fr>> {
  let rows = input.trace_domain.size();
  let ratio = input.quotient_domain.size() / rows;
  let mut values = vec![CurveScalar::<C>::ZERO; rows * ratio];
  let passes = crate::kzg::quotient_plan::plan::<C>(
    &input.circuit.graph,
    input.circuit.lookup_group_size,
  );
  let mut powers: Vec<_> =
    alpha.powers().take(input.constraint_count).collect();
  powers.reverse();
  let mut shift = input.quotient_domain.shift;
  for coset in 0..ratio {
    let domain = Radix2Coset { log_size: input.trace_domain.log_size, shift };
    let ark_domain = Radix2EvaluationDomain::<C::Fr>::new(rows)
      .unwrap()
      .get_coset(shift.0)
      .unwrap();
    let main = evaluations::<C>(main, ark_domain);
    let stage2 = evaluations::<C>(stage2, ark_domain);
    let selectors =
      crate::kzg::quotient::CosetSelectors::new(input.trace_domain, domain);
    for pass in &passes {
      let selected: Vec<_> =
        pass.fixed.iter().map(|&i| fixed[i].clone()).collect();
      let fixed =
        (!selected.is_empty()).then(|| evaluations::<C>(&selected, ark_domain));
      crate::kzg::quotient::evaluate_coset::<C>(
        input,
        pass,
        domain,
        &selectors,
        &powers,
        fixed.as_ref(),
        &main,
        &stage2,
        coset,
        ratio,
        None,
        &mut values,
      );
    }
    shift *= input.quotient_domain.generator();
  }
  let domain = Radix2EvaluationDomain::<C::Fr>::new(rows * ratio)
    .unwrap()
    .get_coset(input.quotient_domain.shift.0)
    .unwrap();
  let values: Vec<_> = values.into_iter().map(|v| v.0).collect();
  domain.ifft(&values).chunks(rows).map(<[C::Fr]>::to_vec).collect()
}

/// Independent CPU reference for LogUp stage-2 traces following the
/// `inverse(0) = 0` convention implemented by `cuda/kzg_lookup.cuh`.
/// `LookupValues::stage_2_traces` now rejects zero lookup denominators via
/// `batch_inverse_masked`, so `beta = 0` exercises zero-denominator masking
/// against this reference while nonzero `beta` cross-checks both.
fn stage_2_reference<C: KzgCurve>(
  circuit: &Circuit<CurveScalar<C>>,
  main: &RowMajorMatrix<CurveScalar<C>>,
  fixed: &RowMajorMatrix<CurveScalar<C>>,
  beta: CurveScalar<C>,
  gamma: CurveScalar<C>,
) -> (RowMajorMatrix<CurveScalar<C>>, CurveScalar<C>) {
  use multi_stark::eval::VarValues;
  let height = main.values.len() / main.width;
  let width = circuit.stage_2_width;
  let group_size = circuit.lookup_group_size.max(1);
  let empty: [CurveScalar<C>; 0] = [];
  let mut sweep_buf = Vec::with_capacity(circuit.graph.nodes.len());
  let mut values = vec![CurveScalar::<C>::ZERO; height * width];
  let mut local = CurveScalar::<C>::ZERO;
  for r in 0..height {
    let r_next = if r + 1 == height { 0 } else { r + 1 };
    let view = VarValues {
      preprocessed: [
        &fixed.values[r * fixed.width..(r + 1) * fixed.width],
        &fixed.values[r_next * fixed.width..(r_next + 1) * fixed.width],
      ],
      main: [
        &main.values[r * main.width..(r + 1) * main.width],
        &main.values[r_next * main.width..(r_next + 1) * main.width],
      ],
      stage2: [&empty[..], &empty[..]],
      publics: &empty[..],
      is_first_row: if r == 0 {
        CurveScalar::<C>::ONE
      } else {
        CurveScalar::<C>::ZERO
      },
      is_last_row: if r + 1 == height {
        CurveScalar::<C>::ONE
      } else {
        CurveScalar::<C>::ZERO
      },
      is_transition: if r + 1 == height {
        CurveScalar::<C>::ZERO
      } else {
        CurveScalar::<C>::ONE
      },
    };
    circuit.graph.sweep_lookup_prefix(&view, &mut sweep_buf);
    let out_row = &mut values[r * width..(r + 1) * width];
    for (slot, group) in
      out_row.iter_mut().zip(circuit.graph.lookups.chunks(group_size))
    {
      *slot = local;
      for lookup in group {
        let mult = sweep_buf[lookup.multiplicity.index()];
        let fp =
          lookup.args.iter().rev().fold(CurveScalar::<C>::ZERO, |acc, a| {
            acc * gamma + sweep_buf[a.index()]
          });
        let msg = beta + fp;
        let inv = CurveScalar(msg.0.inverse().unwrap_or(C::FR_ZERO));
        local += mult * inv;
      }
    }
  }
  (RowMajorMatrix::new(values, width), local)
}

fn compare_paths<C: KzgCurve>(log_size: usize) {
  let rows = 1 << log_size;
  let domain = Radix2Coset::<C> { log_size, shift: CurveScalar::<C>::ONE };
  let ark_domain = Radix2EvaluationDomain::<C::Fr>::new(rows).unwrap();
  let fixed = vec![vec![C::Fr::from(3u64), C::FR_ONE], scalars::<C>(rows)];
  let main = vec![scalars::<C>(rows), vec![C::Fr::from(7u64)]];
  let fixed_data =
    KzgProverData::<C>::coefficient_fixture(domain, fixed.clone());
  let main_data = KzgProverData::<C>::coefficient_fixture(domain, main.clone());
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
  let fixed_values = evaluations::<C>(&fixed, ark_domain);
  let main_values = evaluations::<C>(&main, ark_domain);
  let circuit = fixture::<C>(fixed_values.clone());
  for beta in [CurveScalar::<C>::ZERO, CurveScalar(C::Fr::from(17u64))] {
    let gamma = CurveScalar(C::Fr::from(23u64));
    let lookup_values = compute_lookup_values_range(
      &circuit.graph,
      &main_values,
      Some(&fixed_values),
      0..rows,
    );
    let (expected_trace, expected_total) = stage_2_reference::<C>(
      &circuit,
      &main_values,
      &fixed_values,
      beta,
      gamma,
    );
    if beta != CurveScalar::<C>::ZERO {
      let (traces, totals) = LookupValues::stage_2_traces(
        std::slice::from_ref(&lookup_values),
        &[circuit.lookup_group_size],
        beta,
        &gamma,
        CurveScalar::<C>::ZERO,
      );
      assert_eq!(expected_trace, traces[0]);
      assert_eq!(expected_total, totals[0]);
    }
    let expected = coefficients::<C>(&expected_trace, ark_domain);
    let input = LookupCommitInput::<KzgConfig<C>> {
      circuit: &circuit,
      lookup_values: &lookup_values,
      preprocessed: Some((&fixed_data, 0)),
      stage_1: (&main_data, 0),
    };
    for mode in [PassMode::Off, PassMode::Force] {
      let actual = lookup::coefficients_with_mode::<C, KzgConfig<C>>(
        &input, beta, gamma, mode,
      )
      .expect("fixture must execute CUDA lookup construction");
      assert_eq!(
        actual,
        (expected.clone(), expected_total),
        "lookup mode={mode:?}, beta={beta:?}"
      );
    }
    let stage2 =
      KzgProverData::<C>::coefficient_fixture(domain, expected.clone());
    if log_size >= 16 {
      assert!(
        stage2.matrices[0].resident_columns().iter().any(Option::is_some),
        "fixture must retain lookup GPU input"
      );
    }
    let quotient_input = QuotientCommitInput::<KzgConfig<C>> {
      circuit: &circuit,
      lookup_publics: vec![beta, gamma, CurveScalar::<C>::ZERO, expected_total],
      trace_domain: domain,
      quotient_domain: Radix2Coset {
        log_size: log_size + 2,
        shift: CurveScalar(C::Fr::from(7u64)),
      },
      preprocessed: Some((&fixed_data, 0)),
      stage_1: (&main_data, 0),
      stage_2: (&stage2, 0),
      constraint_count: circuit.constraint_count,
      zk_boundary_mask: None,
    };
    let alpha = CurveScalar(C::Fr::from(29u64));
    let reference =
      quotient_reference::<C>(&quotient_input, &fixed, &main, &expected, alpha);
    for mode in [PassMode::Off, PassMode::Force] {
      let actual = quotient::coefficients_with_mode::<C, KzgConfig<C>>(
        &quotient_input,
        alpha,
        mode,
      )
      .expect("fixture must execute CUDA quotient construction");
      assert_eq!(actual, reference, "quotient mode={mode:?}, beta={beta:?}");
    }
  }
}

#[test]
#[ignore = "requires a CUDA GPU; 1024-row host inputs"]
fn dense_and_pass_constraints_match_cpu_with_zero_denominators() {
  compare_paths::<Bn254>(10);
}

#[test]
#[ignore = "requires a CUDA GPU; 65536-row resident inputs"]
fn resident_dense_and_pass_constraints_match_cpu() {
  compare_paths::<Bn254>(16);
}

#[test]
#[ignore = "requires a CUDA GPU; BLS12-381 1024-row host inputs"]
fn bls12_381_dense_and_pass_constraints_match_cpu_with_zero_denominators() {
  compare_paths::<Bls12381>(10);
}

#[test]
#[ignore = "requires a CUDA GPU; BLS12-381 65536-row resident inputs"]
fn bls12_381_resident_dense_and_pass_constraints_match_cpu() {
  compare_paths::<Bls12381>(16);
}
