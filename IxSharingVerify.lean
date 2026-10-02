import IxSharingVerify.SharingExact
import IxSharingVerify.SharingExactPasses
import IxSharingVerify.SharingExactCanon
import IxSharingVerify.UniformModel
import IxSharingVerify.UniformOptimizer
import IxSharingVerify.UniformLength
import IxSharingVerify.UniformWritings
import IxSharingVerify.UniformExchange
import IxSharingVerify.UniformGain
import IxSharingVerify.UniformClasses
import IxSharingVerify.UniformDecomp
import IxSharingVerify.UniformChecks
import IxSharingVerify.UniformFinal
import IxSharingVerify.UniformSearch
import IxSharingVerify.UniformOptimal
import IxSharingVerify.UniformRevisible
import IxSharingVerify.UniformTies
import IxSharingVerify.UniformTables
import IxSharingVerify.UniformSearchSpec
import IxSharingVerify.UniformKnapsack
import IxSharingVerify.UniformOptimality
import IxSharingVerify.TieredSelect
import IxSharingVerify.TieredTier
import IxSharingVerify.TieredModel
import IxSharingVerify.TieredPhase3
import IxSharingVerify.TieredIdem
import IxSharingVerify.TieredWire
import IxSharingVerify.TieredGuard

/-!
# Proofs of the canonical sharing construction

Theorems about the executable sharing core `Ix.Sharing.Exact`, over the Ixon
v4 codec laws of `Ixon.Verify.Codec` and the TagN bijection of
`Ixon.Verify.TagN`, and the structural wire domain of `Ix.Ixon.Wire`:

* `SharingExact*`: the TagN widths and expression lengths the construction
  counts are the production encodings' lengths, and the exact core's passes
  (materialization, canonicalization) meet their specifications;
* `Uniform*` (namespace `UniformModel`): the uniform-width optimizer of
  phase 1 returns a minimum of its cost model, with the component search,
  knapsack and tie-breaking proved against their specifications;
* `Tiered*` (namespace `Tiered`): the tiered phases 2 and 3, phase 3 never
  worse than phase 1, idempotence, and the output format: every table entry
  and root of `canonicalSharingTiered` is wire-safe and the reported length
  is the serialized length.

`Ix.Sharing.Verify.Builder` (not imported here, since it imports the compiler
`Ix.CompileM`) applies the format theorem to the compiler's sharing builder
`Ix.CompileM.buildConstantWithSharing`: every block it builds is in the
constant codec's wire domain.

The `@[csimp]` theorems in `Ix.Sharing.Exact` make compiled code run fast
bodies in place of these specifications. The audits under
`Ix.Sharing.Verify.Audit` fix every root's axioms, require each such csimp
theorem on the compiler's import path to be a root, and keep `Ix.Sharing`
free of `sorryAx`. Built by the `IxSharingVerify` library (`lake lint`).
-/
