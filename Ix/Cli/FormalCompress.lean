module
public import Ix.Cli.FormalAggregate

/-! Compression inputs for formal aggregate roots. The compression pipeline
verifies a multi-stark batch under a trusted backend key: the formal
aggregation artifact's, checked under formal Aiur's batch policy. A root is
first wrapped once more by the artifact's `ix_aggr` program and proved as one
all-active trace shard in a fixed layout, so the compression verifier
depends on the artifact and the layout only. -/
public section
namespace Ix.Cli.FormalCompress
open Lean FormalAiur FormalAggregate

private def magic : ByteArray := "IXAGGR2\x00".toUTF8

/-- Whether `proof` (an `Ixon.Proof` payload) is a formal aggregate root. -/
def isFormalRoot (proof : ByteArray) : Bool :=
  proof.extract 0 magic.size == magic

/-- Wrap the root `wrapper` once more and prove the wrap as one trace shard
with the heights of `layout` (`.ixl` bytes), on the device and within the RAM budget `p`
selects. The prover verifies the root first and the normalized proof after;
returns the raw normalized proof. -/
def normalize (p : Cli.Parsed) (ctx : Context) (wrapper : Ixon.Proof) (layout : ByteArray) :
    IO ByteArray := do
  let options ← hostOptions p
  FormalProver.normalizeRoot ctx.ixvmSystem ctx.aggrSystem
    { device := options.device, options := options.job } layout
    (Ix.Claim.ser wrapper.claim) wrapper.proof

end Ix.Cli.FormalCompress
end
