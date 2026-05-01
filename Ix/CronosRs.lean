module

public section

namespace Cronos

/-- Dump the global timeline collected by `cronos::clock(...)` calls inside
    `multi-stark` and the `ix_rs` Aiur prover. Backed by `rs_cronos_print`. -/
@[extern "rs_cronos_print"]
opaque rsPrint : IO Unit

end Cronos

end