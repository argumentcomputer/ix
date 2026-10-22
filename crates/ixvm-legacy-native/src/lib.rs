//! Optional generated legacy kernels. Kept outside the ordinary host build.

use aiur::G;
use aiur::execute::{ExecError, IOBuffer, QueryRecord};

mod aiur_ixvm;

pub fn execute_ixvm(
  fun_idx: usize,
  args: &[G],
  record: &mut QueryRecord,
  io: &mut IOBuffer,
) -> Result<Vec<G>, ExecError> {
  aiur_ixvm::execute_generated(fun_idx, args, record, io)
}

mod aiur_multi_stark;

pub fn execute_multi_stark(
  fun_idx: usize,
  args: &[G],
  record: &mut QueryRecord,
  io: &mut IOBuffer,
) -> Result<Vec<G>, ExecError> {
  aiur_multi_stark::execute_generated(fun_idx, args, record, io)
}

mod aiur_ix_aggr;

pub fn execute_ix_aggr(
  fun_idx: usize,
  args: &[G],
  record: &mut QueryRecord,
  io: &mut IOBuffer,
) -> Result<Vec<G>, ExecError> {
  aiur_ix_aggr::execute_generated(fun_idx, args, record, io)
}
