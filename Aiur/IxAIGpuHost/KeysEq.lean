import IxAIStep
import IxAIGpu.Keys

/-!
# The GPU's hint keys are the host's hint table's keys

`IxAIGpu.gpuStepHintKeys` lists the values the kernels write to their key buffers in the order
`Gpu.hintKeys` assembles them. On a triage-shaped model and batch they are
`IxAIAiur.stepHintKeys`, the keys of the hint table `IxAIAiur.hintTable` builds for the host's own
`Fixed::step` packages (`IxAIGpu.hostStepHintKeys` is its restatement over `IxAICore` alone).
-/

namespace IxAIGpuHost
open IxAICore

theorem gpuStepHintKeys_eq_stepHintKeys (g : IxAIGpu.Geometry) (lr : Fx) (m : Model)
    (batch : List (List Fx × List Fx)) (hm : IxAIGpu.Shaped m 8) (hb : IxAIGpu.BatchShaped m 8 batch) :
    IxAIGpu.gpuStepHintKeys g m batch lr = IxAIAiur.stepHintKeys m batch lr :=
  IxAIGpu.gpuStepHintKeys_eq g lr m batch hm hb

end IxAIGpuHost
