use zisk_sdk::{load_program, GuestProgram};

/// Leaf guest: typechecks Anon work items in `[start, end)` and
/// commits `env_hash[32] || start[4] || end[4] || failures[4]` (44 B).
pub static SHARD_PROGRAM: GuestProgram = load_program!("zisk-guest");

/// Aggregation guest: reads `num_proofs: u32` + N proof blobs, verifies
/// each via `ziskos::io::verify_zisk_proof`, and emits a recursive proof
/// committing `num_proofs`. Matches the shape of the upstream Zisk
/// aggregation example.
pub static AGG_PROGRAM: GuestProgram = load_program!("zisk-agg-guest");
