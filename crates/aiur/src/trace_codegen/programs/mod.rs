//! Production kernels selected at code generation time.

use std::sync::Arc;

use super::{
  GeneratedProgram, contract,
  cuda::{CudaLibrary, RegisteredCudaProgram},
};
use crate::bytecode::Toplevel;

#[allow(unreachable_pub)]
#[rustfmt::skip]
mod ixvm;
#[allow(unreachable_pub)]
#[rustfmt::skip]
mod ixvm_cuda;
#[allow(unreachable_pub)]
#[rustfmt::skip]
mod multi_stark;
#[allow(unreachable_pub)]
#[rustfmt::skip]
mod multi_stark_cuda;
#[allow(unreachable_pub)]
#[rustfmt::skip]
mod ix_aggr;
#[allow(unreachable_pub)]
#[rustfmt::skip]
mod ix_aggr_cuda;

const PROGRAMS: &[(&str, &GeneratedProgram, &CudaLibrary)] = &[
  ("ixvm", &ixvm::PROGRAM, &ixvm_cuda::CUDA),
  ("multi-stark", &multi_stark::PROGRAM, &multi_stark_cuda::CUDA),
  ("ix-aggr", &ix_aggr::PROGRAM, &ix_aggr_cuda::CUDA),
];

pub(crate) fn register(
  bytecode: Arc<Toplevel>,
) -> Result<RegisteredCudaProgram, String> {
  let fingerprint = contract::fingerprint(&bytecode);
  let Some(&(name, generated, cuda)) = PROGRAMS
    .iter()
    .find(|(_, generated, _)| generated.fingerprint == fingerprint)
  else {
    return Err("no generated CUDA library matches this bytecode; regenerate with ix codegen --trace-bundle and rebuild".into());
  };
  let registered = cuda
    .register(generated, bytecode.clone())
    .map_err(|error| format!("{name}: {error}"))?;
  let covered = (0..bytecode.circuits.len())
    .filter(|&c| registered.bound().supports(c))
    .count();
  tracing::info!(
    program = name,
    generated_functions =
      generated.functions.iter().filter(|f| f.is_some()).count(),
    constrained_functions =
      bytecode.functions.iter().filter(|f| f.constrained).count(),
    generated_circuits = covered,
    function_circuits = bytecode.circuits.len(),
    "registered generated CUDA traces; uncovered circuits use CPU traces"
  );
  Ok(registered)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    G,
    execute::{IOBuffer, QueryRecord},
    gpu_trace::TraceProvider,
  };
  use ::multi_stark::{
    cuda::CudaDft,
    p3_field::{PrimeCharacteristicRing, PrimeField64},
    witness::TraceSource,
  };

  #[test]
  fn production_registration_and_dispatch_match_oracle() {
    let fixture = (crate::trace_codegen::tests::blake3::PROGRAM.expected)();
    let mut io = IOBuffer { data: Default::default(), map: Default::default() };
    let mut input = vec![G::ZERO];
    input.extend((0..128).map(|i| G::from_usize((i * 37 + 19) % 256)));
    let (fixture_record, _) = fixture.execute(0, input, &mut io).unwrap();
    for &(name, generated, _) in PROGRAMS {
      assert!(!generated.complete);
      let top = Arc::new((generated.expected)());
      let selected: Vec<_> = generated
        .functions
        .iter()
        .enumerate()
        .filter_map(|(i, f)| f.as_ref().map(|_| i))
        .collect();
      // The selection is whole circuits, so every member of a covered
      // circuit is generated and no generated function is left uncovered.
      let registered = register(top.clone()).unwrap();
      let covered: Vec<_> = (0..top.circuits.len())
        .filter(|&c| registered.bound().supports(c))
        .collect();
      let mut covered_functions: Vec<_> =
        covered.iter().flat_map(|&c| top.circuits[c].members.clone()).collect();
      covered_functions.sort_unstable();
      assert_eq!(covered_functions, selected, "{name}: partial circuit");
      // BLAKE3 is the member whose rows the fixture record supplies.
      let function = selected
        .iter()
        .copied()
        .find(|&f| top.functions[f].layout == fixture.functions[0].layout)
        .expect("blake3_compress is selected");
      let circuit = top
        .circuits
        .iter()
        .position(|c| c.members.contains(&function))
        .unwrap();
      assert_eq!(top.circuits[circuit].members, [function]);
      let provider = TraceProvider::Generated(registered);
      let mut record = QueryRecord::new(&top);
      for (input, result) in fixture_record.function_queries[0].iter() {
        record.function_queries[function]
          .insert(input, result.output, result.multiplicity)
          .unwrap();
      }
      let count = record.function_queries[function].len();
      let (source, _) = provider
        .prepare(&top, circuit, &record, &io, &[], (0, 0), (0, count), count)
        .unwrap();
      let mut expected: Vec<_> = (0..count)
        .flat_map(|row| {
          top.main_row_for_test(circuit, function, row, &record, &io)
        })
        .map(|cell| cell.as_canonical_u64())
        .collect();
      let width = top.circuits[circuit].layout.width();
      let height = count.next_power_of_two();
      expected.resize(height * width, 0);
      let TraceSource::Generated(source) = source else {
        panic!("{name}: missing generated source")
      };
      let rows =
        CudaDft::new(0).generated_trace_rows(source, height - 1, height + 1);
      let raw = unsafe {
        std::slice::from_raw_parts(
          rows.values.as_ptr().cast::<u64>(),
          rows.values.len(),
        )
      };
      for (i, &word) in raw.iter().enumerate() {
        assert_eq!(
          word,
          expected[(((height - 1) + i / width) % height) * width + i % width],
          "{name}: cell {i}"
        );
      }
      let uncovered =
        (0..top.circuits.len()).find(|&c| !covered.contains(&c)).unwrap();
      assert!(
        provider
          .prepare(&top, uncovered, &record, &io, &[], (0, 0), (0, 1), 1)
          .is_none()
      );
      assert!(
        provider
          .prepare(&top, circuit, &record, &io, &[], (0, 0), (0, 0), 0)
          .is_none()
      );
      let mut stale = (generated.expected)();
      stale.functions[0].entry = !stale.functions[0].entry;
      assert!(register(Arc::new(stale)).is_err());
    }
    assert!(register(Arc::new(fixture)).is_err());
  }
}
