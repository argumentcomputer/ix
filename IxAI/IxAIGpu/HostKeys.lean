import IxAICore

/-!
# The hint keys of one `Fixed::step`, as the host computes them

`hostStepHintKeys` is `IxAIAiur.stepHintKeys` from `ix.ixai-aiur/Aiur/IxAIStep.lean`, restated over
`IxAICore` alone so that this project can evaluate it without the Aiur library. It lists every key
the `Fixed` circuit asks its hint provider about, in the order the host's hint table lists them:

* `fx.shr8` keys: the exact sums that get rounded. Per example, the hidden pre-activations' dot
  products, the outputs' dot products and the back-propagated dot products (for every hidden unit,
  because `back_unit` rounds before it multiplies by `pos z`); then the weight-gradient sums of
  `w1` and `w2`; then every product `lr · g` of the update.
* `fx.sign` keys: the hidden pre-activations `z`, per example.

Duplicates are erased, keeping first occurrences. The values are the same whichever party computes
them; the GPU trainer emits them from its kernels, and `GpuExport` prints these for comparison.
-/

namespace IxAIGpu
open IxAICore

def hostStepHintKeys (m : Model) (batch : List (List Fx × List Fx)) (lr : Fx) : List Int × List Int :=
  let hidden := m.b1.length
  let w2T := transposeN hidden m.w2
  let perExample : List (List Int × List Int) := batch.map fun (x, t) =>
    let (z, h) := m.hidden x
    let o := List.zipWith (fun row b => Fx.add (Fx.dot row h) b) m.w2 m.b2
    let dout := List.zipWith Fx.sub o t
    (m.w1.map (Fx.dotRaw · x) ++ m.w2.map (Fx.dotRaw · h) ++ w2T.map (Fx.dotRaw · dout),
     z.map (·.raw))
  let ds : List Delta := batch.map fun (x, t) => m.delta w2T x t
  let dzT := transposeN hidden (ds.map (·.dz))
  let xT := transposeN 8 (ds.map (·.x))
  let hT := transposeN hidden (ds.map (·.h))
  let doutT := transposeN m.b2.length (ds.map (·.dout))
  let gw1 : List Int := dzT.flatMap fun dz => xT.map fun x => Fx.dotRaw dz x
  let gw2 : List Int := doutT.flatMap fun d => hT.map fun h => Fx.dotRaw d h
  let shift : Int → Int := fun v => v >>> (8 : Nat)
  let grads : List Int := gw1.map shift ++ dzT.map Fx.sumRaw ++ gw2.map shift ++ doutT.map Fx.sumRaw
  let shr : List Int := perExample.flatMap (·.1) ++ gw1 ++ gw2 ++ grads.map fun g => lr.raw * g
  (shr.eraseDups, (perExample.flatMap (·.2)).eraseDups)

end IxAIGpu
