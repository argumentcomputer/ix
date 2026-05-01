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

/-- Enable RAM tracking: every completed `cronos::clock(tag)` records process
    RSS (Linux) so streaming output and the final timeline report net deltas
    plus the running peak per stage. Off by default. -/
@[extern "rs_cronos_ram_enable"]
opaque rsRamEnable : IO Unit

/-- Disable RAM tracking. -/
@[extern "rs_cronos_ram_disable"]
opaque rsRamDisable : IO Unit

end Cronos

end