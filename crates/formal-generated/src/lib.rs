//! The generated code of the formal Aiur programs: IxVM's claim verifier,
//! the recursive verifier and aggregation. `lake build ix` generates it
//! from the certified programs into `.lake/build/formal-generated` before
//! Cargo runs (see `ix_prover::codegen`); with feature `executors` this
//! crate compiles the native executors, and with `cuda` also the trace
//! writers.
//!
//! Each native executor implements [`aiur::native::Kernel`] and binds only
//! to a program with exactly its fingerprint; each trace bundle is
//! registered by fingerprint as well. A program that changed since its code
//! was generated therefore runs on the interpreter and the host population
//! until `ix` is rebuilt.

#[cfg(feature = "executors")]
macro_rules! generated {
  ($module:ident, $file:literal) => {
    #[allow(warnings, clippy::all, clippy::pedantic)]
    mod $module {
      include!(concat!("../../../.lake/build/formal-generated", $file));
    }
  };
}

#[cfg(feature = "executors")]
generated!(ixvm, "/native/ixvm.rs");
#[cfg(feature = "executors")]
generated!(verifier, "/native/verifier.rs");
#[cfg(feature = "executors")]
generated!(aggregation, "/native/aggregation.rs");

#[cfg(feature = "executors")]
pub use aggregation::Aggregation;
#[cfg(feature = "executors")]
pub use ixvm::Ixvm;
#[cfg(feature = "executors")]
pub use verifier::Verifier;

/// The compiled trace writers, registered with
/// `aiur::trace::stark::compiled::register`.
#[cfg(feature = "cuda")]
pub mod cuda {
  macro_rules! bundle {
    ($module:ident, $file:literal) => {
      #[allow(warnings, clippy::all, clippy::pedantic)]
      pub mod $module {
        include!(concat!("../../../.lake/build/formal-generated", $file));
      }
    };
  }

  bundle!(ixvm, "/cuda/ixvm/bundle.rs");
  bundle!(verifier, "/cuda/verifier/bundle.rs");
  bundle!(aggregation, "/cuda/aggregation/bundle.rs");
}
