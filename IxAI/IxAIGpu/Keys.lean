import IxAIGpu.Step
import IxAIGpu.HostKeys

/-!
# The GPU's hint keys are the host's

`gpuStepHintKeys` lists the values the kernels write to their key buffers (`hidden_kernel`,
`output_kernel`, `dz_kernel`, `update_w_kernel`, `update_b_kernel`, and `z` from
`hidden_kernel`) in the order `IxAIGpuHost.Gpu.hintKeys` (the trainer's Lean host) assembles them.
`gpuStepHintKeys_eq`: for every launch geometry, on a triage-shaped model (8 inputs) and batch,
they are `hostStepHintKeys`, the keys of the host's `Fixed::step` hint table. The hint answers are
functions of the keys alone (`shr8Words`, `signWords`), so the GPU's hint table is the host's.
-/

namespace IxAIGpu
open IxAICore Finset

def gpuStepHintKeys (g : Geometry) (m : Model) (batch : List (List Fx × List Fx)) (lr : Fx) :
    List Int × List Int :=
  let nB := batch.length
  let nH := m.b1.length
  let nI := (getD m.w1 0 []).length
  let nO := m.b2.length
  let W1 := Mat.ofRows m.w1
  let B1 := Vec.ofList m.b1
  let W2 := Mat.ofRows m.w2
  let B2 := Vec.ofList m.b2
  let X := Mat.ofRows (batch.map (·.1))
  let T := Mat.ofRows (batch.map (·.2))
  let Z := hiddenZ g nI W1 B1 X
  let Hm : Mat := fun b j => relu (Z b j)
  let Dout := outputDelta g nH W2 B2 Hm T
  let Dz := dzK g nO (transposeK W2) Z Dout
  let perExample := (List.range nB).flatMap fun b =>
    (List.range nH).map (hiddenKey g nI W1 X b) ++ (List.range nO).map (outputKey g nH W2 Hm b) ++
      (List.range nH).map (dzKey g nO (transposeK W2) Dout b)
  let gw1 := (List.range nH).flatMap fun r =>
    (List.range nI).map (gradKey g nB (transposeK Dz) (transposeK X) r)
  let gw2 := (List.range nO).flatMap fun r =>
    (List.range nH).map (gradKey g nB (transposeK Dout) (transposeK Hm) r)
  let products := gw1.map (fun (s : Int) => lr.raw * (s >>> (8 : Nat))) ++
    (List.range nH).map (fun r => lr.raw * blockReduce g (transposeK Dz r) nB) ++
    gw2.map (fun (s : Int) => lr.raw * (s >>> (8 : Nat))) ++
    (List.range nO).map (fun r => lr.raw * blockReduce g (transposeK Dout r) nB)
  ((perExample ++ gw1 ++ gw2 ++ products).eraseDups,
   ((List.range nB).flatMap fun b => (List.range nH).map (Z b)).eraseDups)

theorem gpuStepHintKeys_eq (g : Geometry) (lr : Fx) (m : Model) (batch : List (List Fx × List Fx))
    (hm : Shaped m 8) (hb : BatchShaped m 8 batch) :
    gpuStepHintKeys g m batch lr = hostStepHintKeys m batch lr := by
  have hw1 := w1_eq m 8 hm
  have hw2 := w2_eq m 8 hm
  have hb1 := list_eq_toList m.b1
  have hb2 := list_eq_toList m.b2
  have hwidth := hm.width
  have hbatch := batch_eq m 8 batch hb
  unfold gpuStepHintKeys hostStepHintKeys
  unfold hiddenZ hiddenKey outputDelta outputKey dzK dzKey gradKey transposeK
  simp only [blockReduce_eq, hwidth]
  generalize Mat.ofRows (batch.map (·.1)) = X at hbatch ⊢
  generalize Mat.ofRows (batch.map (·.2)) = T at hbatch ⊢
  generalize batch.length = nB at hbatch ⊢
  subst hbatch
  obtain ⟨w1, b1, w2, b2⟩ := m
  simp only at hw1 hw2 hb1 hb2 ⊢
  generalize Mat.ofRows w1 = W1 at hw1 ⊢
  generalize Vec.ofList b1 = B1 at hb1 ⊢
  generalize Mat.ofRows w2 = W2 at hw2 ⊢
  generalize Vec.ofList b2 = B2 at hb2 ⊢
  generalize b1.length = nH at hb1 hw1 hw2 ⊢
  generalize b2.length = nO at hb2 hw2 ⊢
  subst hw1 hw2 hb1 hb2
  simp only [Model.delta, Model.hidden, Mat.toRows, Vec.toList, List.map_map, Function.comp_def,
    List.flatMap_map, List.map_flatMap, List.map_append, zipWith_range, dot_range, dotRaw_range,
    sumRaw_range, transposeN_range, Fx.add, Fx.sub, relu_mk, Fx.pos,
    decide_eq_true_eq, ite_raw, Fx.zero]

end IxAIGpu
