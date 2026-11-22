use aiur::{artifact::WidePackage, field::FieldBackend, trace::TracePlan};
use ix_proof_compression::aiur_backend::{Bn254, kzg::Compiler};
use p3_matrix::Matrix;
use std::sync::Arc;

#[test]
fn counted_rows_match_packed_groups_fixed_tables_and_rom() {
  for (bytes, entry, args) in [
    (
      include_bytes!("../../aiur/tests/fixtures/bn254-trace.ixa").as_slice(),
      "BN254Trace::run",
      vec![Bn254.from_u64(5), Bn254.zero()],
    ),
    (
      include_bytes!("../../aiur/tests/fixtures/bn254-grouped.ixa").as_slice(),
      "BN254Grouped::run",
      vec![Bn254.from_u64(2)],
    ),
    (
      include_bytes!("../../aiur/tests/fixtures/bn254-gap.ixa").as_slice(),
      "BN254Gap::run",
      vec![Bn254.from_u64(6), Bn254.neg(Bn254.one())],
    ),
  ] {
    let package = WidePackage::decode(bytes).unwrap();
    let trace = package.trace.unwrap();
    let mut program = package.program.check_with(Bn254).unwrap();
    program.track_depth(&trace).unwrap();
    let plan = TracePlan::new(Arc::new(program), trace).unwrap();
    let record = plan.program().execute(entry, args.clone()).unwrap();
    let compiler = Compiler::new(&plan).unwrap();
    let heights = compiler.row_counts(&record).unwrap();
    assert_eq!(heights.len(), compiler.inputs().len());
    assert_eq!(heights.len(), compiler.names().len());
    let matrices = compiler.generate(&record, entry, &args).unwrap();
    assert_eq!(
      heights,
      matrices.iter().map(Matrix::height).collect::<Vec<_>>()
    );
  }
}
