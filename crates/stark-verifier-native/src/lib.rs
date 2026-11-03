//! Generated native executors for the recursive verifier programs. Each is
//! built at compile time from the exported package named by its environment
//! variable (`stark-export export`, with `--aggregate` for aggregation).

#[cfg(feature = "kernel")]
aiur_macros::kernel!(pub Verifier, env = "AIUR_VERIFIER_ARTIFACT");
#[cfg(feature = "kernel")]
aiur_macros::kernel!(pub Aggregation, env = "AIUR_AGGREGATION_ARTIFACT");
