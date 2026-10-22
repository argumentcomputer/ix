//! Legacy ixvm runner and host advice.
//! Bytecode execution is the default. The `native` feature selects the generated
//! kernels from `ixvm-legacy-native`, preserving the same query and IO records.

use aiur::G;
use aiur::bytecode::{FunIdx, Toplevel};
use aiur::execute::{ExecError, IOBuffer, QueryRecord};

#[cfg(feature = "native")]
use ixvm_legacy_native::execute_ixvm as execute_generated;

/// Execute using bytecode, or the generated kernel with the `native` feature.
/// Both preserve `Toplevel::execute`'s return shape and entry flag check.
/// The native kernel handles recursion with `stacker::maybe_grow`.
// `args: Vec<G>` mirrors `Toplevel::execute`'s signature so this function
// satisfies `AiurSystem::prove_ixvm`'s executor bound; a `&[G]` here would
// break it.
#[allow(clippy::needless_pass_by_value)]
pub fn execute_ixvm(
  toplevel: &Toplevel,
  fun_idx: FunIdx,
  args: Vec<G>,
  io_buffer: &mut IOBuffer,
) -> Result<(QueryRecord, Vec<G>), ExecError> {
  #[cfg(not(feature = "native"))]
  {
    toplevel.execute(fun_idx, args, io_buffer)
  }
  #[cfg(feature = "native")]
  {
    if !toplevel.functions[fun_idx].entry {
      return Err(ExecError::NotEntryFunction(fun_idx));
    }
    let mut record = QueryRecord::new(toplevel);
    let output = execute_generated(fun_idx, &args, &mut record, io_buffer)?;
    Ok((record, output))
  }
}

/// [`execute_ixvm`] into an existing record, memoizing against what it
/// already holds (see `Toplevel::execute_in`).
pub fn execute_ixvm_in(
  toplevel: &Toplevel,
  fun_idx: FunIdx,
  args: &[G],
  io_buffer: &mut IOBuffer,
  record: &mut QueryRecord,
) -> Result<Vec<G>, ExecError> {
  #[cfg(not(feature = "native"))]
  {
    toplevel.execute_in(fun_idx, args.to_vec(), io_buffer, record)
  }
  #[cfg(feature = "native")]
  {
    if !toplevel.functions[fun_idx].entry {
      return Err(ExecError::NotEntryFunction(fun_idx));
    }
    execute_generated(fun_idx, args, record, io_buffer)
  }
}

#[cfg(all(test, not(feature = "native")))]
mod tests {
  use super::*;
  use aiur::bytecode::{Block, Ctrl, Function, FunctionLayout, Op};
  use multi_stark::p3_field::PrimeCharacteristicRing;

  #[test]
  fn bytecode_fallback_checks_entries_and_reuses_the_record() {
    let mut top = Toplevel {
      functions: vec![Function {
        body: Block {
          ops: vec![Op::Add(0, 1)],
          ctrl: Ctrl::Return(0, vec![2]),
        },
        layout: FunctionLayout {
          input_size: 2,
          selectors: 1,
          auxiliaries: 1,
          lookups: 1,
        },
        entry: true,
        constrained: true,
      }],
      circuits: vec![],
      memory_sizes: vec![],
    };
    let args = vec![G::from_u8(20), G::from_u8(22)];
    let mut io = IOBuffer { data: Default::default(), map: Default::default() };
    let (mut record, output) =
      execute_ixvm(&top, 0, args.clone(), &mut io).unwrap();
    assert_eq!(output, vec![G::from_u8(42)]);
    assert_eq!(
      execute_ixvm_in(&top, 0, &args, &mut io, &mut record).unwrap(),
      output
    );
    assert_eq!(record.function_queries[0].len(), 1);
    assert_eq!(
      record.function_queries[0].get(&args).unwrap().multiplicity,
      G::from_u8(2)
    );
    top.functions[0].entry = false;
    assert!(matches!(
      execute_ixvm(&top, 0, args, &mut io),
      Err(ExecError::NotEntryFunction(0))
    ));
  }
}
