import IxCC.Recheck.Rc.Replay
import IxCC.Recheck.Produce

set_option autoImplicit false
namespace IxCC.Recheck.RcReplay


def produce (cfg : Config) (input : Recheck.Input) : Except Err (Cert × Artifact) := do
  let cfg := cfg.forInput input
  let base ← Recheck.produce cfg input
  let oldFront ← Recheck.runLir cfg input.program base
  let proposal : Cert := {
    base
    own := Own.Plain.Certificate.encode (Own.Plain.Program.canonical oldFront.fir).bodies }
  let f ← runFront cfg input.program proposal
  let (xv, _) ← (Xv.Select.run f.lowered.program).mapError Err.ofSelect
  let allocated ← (Xv.Alloc.run cfg.env xv).mapError fun message =>
    { stage := .alloc, code := "alloc.fallback", message }
  let frames := Xv.Stacking.produce allocated.program
  let stacked ← (Xv.Stacking.run allocated.program frames f.reps cfg.env).mapError
    (Err.ofBackend ∘ .stacking)
  let order := X86.Layout.Order.produce (X86.Layout.tunnel stacked.program) stacked.shape
  let cert : Cert := { proposal with base := { base with alloc := allocated.outs, frames, order } }
  let artifact ← run cfg input.program cert
  return (cert, artifact)

end IxCC.Recheck.RcReplay
