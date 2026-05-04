/-
  tracing-texray Lean API.

  The Rust prover (multi-stark + ix_rs) emits `tracing` spans for each major
  proving stage. After `init` installs the texray subscriber, every span tree
  rooted at an `examine`'d span (e.g. `aiur/prove`) is dumped to stderr when
  the root span exits.
-/

module

public section

namespace TracingTexray

/-- Install the global `tracing-texray` subscriber. Idempotent: subsequent
    calls are no-ops once the subscriber has been set. RAM tracking is
    enabled (Linux-only; zeros elsewhere). -/
@[extern "rs_texray_init"]
opaque init : IO Unit

end TracingTexray

end
