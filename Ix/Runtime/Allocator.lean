module

public import Init

public section

namespace Ix.Runtime

/-- Configure the process's mimalloc allocator for proving: freed memory goes
    back to the OS immediately, so RSS tracks the record pool's budget. The
    Rust side (`crates/ffi/src/lib.rs`) leaves an explicit
    `MIMALLOC_PURGE_DELAY` in the environment in force. -/
@[extern "rs_configure_allocator"]
opaque configureAllocator : Unit → BaseIO Unit

end Ix.Runtime
