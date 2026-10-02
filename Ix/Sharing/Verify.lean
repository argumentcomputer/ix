import Ix.Sharing.Verify.SharingExact
import Ix.Sharing.Verify.SharingExactPasses
import Ix.Sharing.Verify.SharingExactCanon
import Ix.Sharing.Verify.UniformModel
import Ix.Sharing.Verify.UniformOptimizer
import Ix.Sharing.Verify.UniformLength
import Ix.Sharing.Verify.UniformWritings
import Ix.Sharing.Verify.UniformExchange
import Ix.Sharing.Verify.UniformGain
import Ix.Sharing.Verify.UniformClasses
import Ix.Sharing.Verify.UniformDecomp
import Ix.Sharing.Verify.UniformChecks
import Ix.Sharing.Verify.UniformFinal
import Ix.Sharing.Verify.UniformSearch
import Ix.Sharing.Verify.UniformOptimal
import Ix.Sharing.Verify.UniformRevisible
import Ix.Sharing.Verify.UniformTies
import Ix.Sharing.Verify.UniformTables
import Ix.Sharing.Verify.UniformSearchSpec
import Ix.Sharing.Verify.UniformKnapsack
import Ix.Sharing.Verify.UniformOptimality
import Ix.Sharing.Verify.TieredSelect
import Ix.Sharing.Verify.TieredTier
import Ix.Sharing.Verify.TieredModel
import Ix.Sharing.Verify.TieredPhase3
import Ix.Sharing.Verify.TieredIdem
import Ix.Sharing.Verify.TieredWire
import Ix.Sharing.Verify.TieredGuard

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

The `@[csimp]` theorems in `Ix.Sharing.Exact` make compiled code run fast
bodies in place of these specifications. The audits under
`Ix.Sharing.Verify.Audit` fix every root's axioms, require each such csimp
theorem on the compiler's import path to be a root, and keep `Ix.Sharing`
free of `sorryAx`. Built by the `IxSharingVerify` library (`lake lint`).
-/
