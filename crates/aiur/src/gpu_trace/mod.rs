//! Selection of the main-trace provider for GPU proving.
//!
//! The CPU builder is always available. The generated provider is compiled
//! from bytecode by `ix codegen --trace-bundle` and covers the circuits its
//! registry lists; every other circuit falls back to CPU rows.

use std::sync::Arc;

use multi_stark::{lookup::LookupValues, witness::TraceSource};

use crate::{
  G,
  bytecode::Toplevel,
  execute::{IOBuffer, QueryRecord},
  trace::QueryPosition,
};

pub(crate) enum TraceProvider {
  Cpu,
  #[cfg(feature = "cuda-trace-codegen")]
  Generated(crate::trace_codegen::cuda::RegisteredCudaProgram),
}

impl TraceProvider {
  pub(crate) fn from_env(_top: Arc<Toplevel>) -> Self {
    let mode = std::env::var("AIUR_GPU_TRACE").unwrap_or_else(|_| "cpu".into());
    if mode != "cpu" {
      assert!(
        crate::trace::trace_only_lookups(),
        "AIUR_GPU_TRACE={mode} requires AIUR_TRACE_ONLY_LOOKUPS=1"
      );
    }
    match mode.as_str() {
      "cpu" => Self::Cpu,
      #[cfg(feature = "cuda-trace-codegen")]
      "generated" => Self::Generated(
        crate::trace_codegen::programs::register(_top)
          .unwrap_or_else(|error| panic!("AIUR_GPU_TRACE=generated: {error}")),
      ),
      #[cfg(not(feature = "cuda-trace-codegen"))]
      "generated" => panic!(
        "AIUR_GPU_TRACE=generated requires the cuda-trace-codegen feature (IX_CUDA_TRACE_CODEGEN=1)"
      ),
      _ => panic!("unsupported AIUR_GPU_TRACE={mode}; use cpu or generated"),
    }
  }

  /// A memory table range on the device; `None` leaves it to the CPU builder.
  ///
  /// Opt-in through `AIUR_GPU_TRACE_MEMORY=1`: a memory seed is the row minus
  /// one column, so generation moves as many bytes as the CPU trace and adds
  /// a launch per span. On the Init proof it cost 5 s of wall time
  /// (`bench/aiur-trace-init-2026-09-16`). It stays available for workloads
  /// where the host builder, not transport, is the limit.
  pub(crate) fn prepare_memory(
    &self,
    _record: &QueryRecord,
    _size: usize,
    _slots: &[usize],
    _range: std::ops::Range<usize>,
  ) -> Option<(TraceSource<G>, LookupValues<G>)> {
    match self {
      Self::Cpu => None,
      #[cfg(feature = "cuda-trace-codegen")]
      Self::Generated(_) => {
        if std::env::var("AIUR_GPU_TRACE_MEMORY").as_deref() != Ok("1") {
          return None;
        }
        match crate::trace_codegen::cuda::prepare_memory(
          _record,
          _size,
          _slots,
          _range.clone(),
        ) {
          Ok(prepared) => Some(prepared),
          Err(error) => {
            tracing::warn!(
              size = _size,
              rows = _range.len(),
              %error,
              "CPU trace: generated memory seed preparation failed"
            );
            None
          },
        }
      },
    }
  }

  /// `None` leaves the circuit to the CPU trace builder.
  pub(crate) fn prepare(
    &self,
    _top: &Toplevel,
    _circuit: usize,
    _record: &QueryRecord,
    _io: &IOBuffer,
    _slots: &[usize],
    _start: QueryPosition,
    _end: QueryPosition,
    _row_count: usize,
  ) -> Option<(TraceSource<G>, LookupValues<G>)> {
    match self {
      Self::Cpu => None,
      #[cfg(feature = "cuda-trace-codegen")]
      Self::Generated(program) => {
        if _row_count == 0 {
          return None;
        }
        let bound = program.bound();
        if !bound.supports(_circuit) {
          tracing::debug!(
            circuit = _circuit,
            rows = _row_count,
            "CPU trace: circuit lacks generated CUDA coverage"
          );
          return None;
        }
        // A preparation error means the record disagrees with the generated
        // packer or a resource ran out; the CPU builder is the reference, so
        // fall back to it and say so rather than abort the proof.
        match bound.prepare(
          _circuit, _record, _io, _slots, _start, _end, _row_count, false,
        ) {
          Ok(prepared) => Some(prepared),
          Err(error) => {
            tracing::warn!(
              circuit = _circuit,
              rows = _row_count,
              %error,
              "CPU trace: generated seed preparation failed"
            );
            None
          },
        }
      },
    }
  }
}
