module

public section

namespace Cronos

/-- Dump the global timeline collected by `cronos::clock(...)` calls inside
    `multi-stark` and the `ix_rs` Aiur prover. Backed by `rs_cronos_print`. -/
@[extern "rs_cronos_print"]
opaque rsPrint : IO Unit

/-- Enable streaming mode: every completed `cronos::clock(tag)` call on the
    Rust side prints a one-line `[cronos] <tag>: <duration>` immediately,
    in addition to the buffered timeline `rsPrint` dumps at the end. -/
@[extern "rs_cronos_streaming_enable"]
opaque rsStreamingEnable : IO Unit

/-- Disable streaming mode. -/
@[extern "rs_cronos_streaming_disable"]
opaque rsStreamingDisable : IO Unit

end Cronos

end