//! The formal IxVM and recursive verifier prover as a library. [`aggregate`]
//! is the formal backend of the aggregate controller, which proves
//! manifests, their joins and `ix aggregate`; [`tools`] holds the stateless
//! operations: single-claim proving, verification, key identity, execution
//! checks and proof inspection. The `ix` CLI links it through FFI.
pub mod aggregate;
mod executor;
mod output;
pub mod protocol;
pub mod request;
pub mod tools;

use aiur::{
  bytecode::CheckedProgram, field::NativeField, trace::TraceArtifact,
};
use multi_stark::types::Val;
use record_pool::BudgetError;

type Field = NativeField<Val>;
type Program = CheckedProgram<Field>;

#[derive(serde::Deserialize)]
struct Package {
  program: aiur::Program,
  trace: TraceArtifact,
}

fn load_package(path: &std::path::Path) -> Result<Package, String> {
  aiur::decode_artifact::<Package>(
    &std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?,
  )
  .map_err(|e| e.to_string())
}

/// Names the executors this build links: `interpreter`, plus the generated
/// native kernels with feature `native`.
pub fn executors() -> &'static [&'static str] {
  executor::Executor::available()
}

/// Install the texray subscriber. A process has one global subscriber; if
/// another is already installed (in `ix`, by `--texray` elsewhere), spans go
/// to that one instead.
pub fn init_tracing(enabled: bool) {
  use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};
  if enabled {
    let _ = tracing_subscriber::Registry::default()
      .with(tracing_texray::TeXRayLayer::new().track_ram().streaming())
      .try_init();
  }
}

enum PrepFailure {
  Resource(BudgetError),
  Other(String),
}
impl From<BudgetError> for PrepFailure {
  fn from(e: BudgetError) -> Self {
    Self::Resource(e)
  }
}
