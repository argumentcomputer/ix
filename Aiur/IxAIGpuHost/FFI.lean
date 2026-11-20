/-!
# The CUDA step behind its C shim

`cuda/step.cu` holds the kernels and their C entry points; `cuda/ixai_gpu.c` adapts those to
Lean's object ABI. A `Context` owns the device buffers of one model shape, and the model stays on
the device between steps. Every buffer is a `ByteArray` of little-endian int64 words in the
row-major order of `step.cu`; `IxAIGpuHost.Host` packs and unpacks them.
-/

namespace IxAIGpuHost

opaque ContextPointed : NonemptyType

/-- Device buffers of one shape: `nIn` inputs, `nHidden` hidden units, `nOut` outputs, and
batches of at most `maxBatch` examples. Released when the last reference is dropped. -/
def Context : Type := ContextPointed.type

instance : Nonempty Context := ContextPointed.property

@[extern "ixai_lean_gpu_create"]
opaque Context.create (nIn nHidden nOut maxBatch : UInt32) : IO Context

/-- Upload `w1 ++ b1 ++ w2 ++ b2` (`w1` is `nHidden × nIn`, `w2` is `nOut × nHidden`). -/
@[extern "ixai_lean_gpu_set_model"]
opaque Context.setModel (ctx : @& Context) (model : @& ByteArray) : IO Unit

/-- Download the model, as `setModel` takes it. -/
@[extern "ixai_lean_gpu_model"]
opaque Context.model (ctx : @& Context) : IO ByteArray

/-- `IxAIGpu.gpuStep` on the device's model, with inputs `x` (`batch × nIn`), targets `t`
(`batch × nOut`) and the raw learning rate `lr` as int64 bits. `false` when an intermediate value
left its fixed width (`IxAIGpu.StepGuard` fails); the device's model is then invalid. -/
@[extern "ixai_lean_gpu_step"]
opaque Context.step (ctx : @& Context) (x t : @& ByteArray) (batch : UInt32) (lr : UInt64) : IO Bool

/-- The last step's key buffers, concatenated: per example `h`, `o`, `dz` and `z` sums
(`batch × nHidden`, `batch × nOut`, `batch × nHidden`, `batch × nHidden`), then the gradient
sums of `w1` and `w2`, then the products `lr · g` of `w1`, `b1`, `w2`, `b2`. -/
@[extern "ixai_lean_gpu_keys"]
opaque Context.keys (ctx : @& Context) : IO ByteArray

/-- How the step's GEMMs run: `0` tensor cores for the large ones and CUDA cores for the rest,
`1` CUDA cores only, `2` tensor cores whenever the operands fit four int8 limbs. Every path gives
the same result. -/
@[extern "ixai_lean_gpu_set_path"]
opaque Context.setPath (ctx : @& Context) (path : UInt32) : IO Unit

/-- How many of the last step's GEMMs ran on tensor cores. -/
@[extern "ixai_lean_gpu_tensor_gemms"]
opaque Context.tensorGemms (ctx : @& Context) : IO UInt32

/-- The last step's device time in milliseconds, from its first kernel to its last. -/
@[extern "ixai_lean_gpu_kernel_ms"]
opaque Context.kernelMs (ctx : @& Context) : IO Float

end IxAIGpuHost
