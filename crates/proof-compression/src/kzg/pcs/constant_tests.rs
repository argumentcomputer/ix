use super::*;
use multi_stark::traits::{Algebra, Field};

fn compare_representations(height: usize) {
  let pcs =
    KzgPcs::new(Arc::new(Srs::unsafe_dev_setup(height, b"compact-columns")), 2);
  let domain = pcs.natural_domain_for_degree(height);
  let (commitment, compact) = pcs.commit(vec![(
    domain,
    RowMajorMatrix::new(
      (0..height)
        .flat_map(|row| {
          [Scalar::ZERO, Scalar::from_u8(7), Scalar::from_usize(row)]
        })
        .collect(),
      3,
    ),
  )]);
  assert!(matches!(compact.matrices[0].columns[0], Column::Constant { .. }));
  assert!(matches!(compact.matrices[0].columns[1], Column::Constant { .. }));
  assert!(matches!(compact.matrices[0].columns[2], Column::Resident { .. }));
  let columns: Vec<_> = compact.matrices[0]
    .columns
    .iter()
    .map(|column| Column::Resident {
      values: Arc::new(column.load().unwrap().into_owned()),
      range: 0..column.len(),
    })
    .collect();
  let matrix = CommittedMatrix {
    domain,
    columns,
    constants: vec![false; 3],
    #[cfg(feature = "cuda")]
    resident: Default::default(),
  };
  assert_eq!(pcs.commit_matrix_columns(&matrix), commitment.0[0]);
  let dense = KzgProverData { commitment, matrices: vec![matrix] };
  for evaluation_domain in [domain, domain.create_disjoint_domain(height * 2)] {
    assert_eq!(
      pcs.get_evaluations_on_domain(&compact, 0, evaluation_domain),
      pcs.get_evaluations_on_domain(&dense, 0, evaluation_domain),
    );
  }
  let points = vec![vec![Scalar::from_u8(13), Scalar::from_u8(19)]];
  let open = |data: &KzgProverData| {
    pcs.open(vec![(data, points.clone())], &mut KzgTranscript::default())
  };
  assert_eq!(open(&compact), open(&dense));
  let mut bytes = vec![];
  compact.write_checkpoint(&mut bytes).unwrap();
  let mut reference = vec![];
  dense.write_checkpoint(&mut reference).unwrap();
  assert_eq!(bytes, reference);
  let restored = KzgProverData::read_checkpoint(bytes.as_slice()).unwrap();
  assert_eq!(open(&compact), open(&restored));
  let path = std::env::temp_dir()
    .join(format!("compact-columns-{}-{height}.bin", std::process::id(),));
  std::fs::write(&path, bytes).unwrap();
  let disk = KzgProverData::read_checkpoint_file(&path).unwrap();
  assert_eq!(open(&compact), open(&disk));
  drop(disk);
  std::fs::remove_file(path).unwrap();
  #[cfg(feature = "cuda")]
  {
    let views = compact.matrices[0].cuda_columns().unwrap();
    assert_eq!(
      views.iter().map(|(c, _, _)| c.len()).collect::<Vec<_>>(),
      [1, 1, height]
    );
    assert_eq!(
      views.iter().map(|(_, _, c)| *c).collect::<Vec<_>>(),
      [true, true, false]
    );
  }
}

#[test]
fn compact_constants_match_dense_and_checkpoint_openings() {
  compare_representations(16);
}

#[cfg(feature = "cuda")]
#[test]
#[ignore = "requires a CUDA GPU"]
fn compact_constants_match_dense_device_operations() {
  compare_representations(1 << 12);
}
