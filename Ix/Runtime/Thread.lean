module

public import Init

public section

namespace Ix.Tc

/-- Set the stack size, in bytes, for subsequently spawned Lean runtime
    threads (`.dedicated` task threads and not-yet-spawned pool workers) —
    the knob behind `lean --tstack`. Already-running threads keep their
    stacks. The Rust shim (`crates/ffi/src/kernel.rs`) adapts the bare
    `void(size_t)` runtime call to the IO ABI. -/
@[extern "rs_lean_set_thread_stack_size"]
opaque setLeanThreadStackSize : USize → BaseIO Unit

end Ix.Tc
