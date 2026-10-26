import IxSharingVerify.SharingExact
import IxSharingVerify.SharingExactPasses
import IxSharingVerify.SharingExactCanon
import IxSharingVerify.ExprCache
import IxSharingVerify.Ingestion
import IxSharingVerify.IngestionTable
import IxSharingVerify.IngestionUnique
import IxSharingVerify.CanonicalMeaning
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
import IxSharingVerify.CanonicalProduction
import IxSharingVerify.FamilyExactConstant

/-!
# Proofs of the canonical sharing construction

Theorems about the executable sharing core `Ix.Sharing`, over the Ixon
v4 codec laws of `Ixon.Verify.Codec` and the TagN bijection of
`Ixon.Verify.TagN`, and the structural wire domain of `Ix.Ixon.Wire`.

The production entry `Ix.Sharing.Exact.canonicalSharingTiered` runs the
frozen rule `sharing-k16-greedy-v1` (`Ix.Sharing.Family`, with the fixed
parameter `canonicalFamilyConfig`). In phase 1, each initial uncertain
component takes its stored set from a fixed family: every subset when the
component has at most 16 members, otherwise the prefixes of one greedy
chain. The tiered phases 2 and 3 follow. The previous exact component search
remains as `Ix.Sharing.Exact.Reference`, which only tests run, with its
stronger optimality results.

* `SharingExact*`: the TagN widths and expression lengths the construction
  counts are the production encodings' lengths, and the exact core's passes
  (materialization, canonicalization) meet their specifications;
* `ExprCache`, `Ingestion*`, `CanonicalMeaning`: the interner's pointer cache
  reuses an ID only for an equal expression, ingestion of the table and the
  roots preserves each expression's meaning, and canonical numbering
  preserves the interpreted roots;
* `Family*` (namespace `Ix.Sharing.Family`): the production phase-1 rule.
  These modules prove its families and per-count tables, slack trimming and
  knapsack origins, and selection of the least model within the family
  product, the meaning and wire format of every successful output, and
  conditional idempotence. The closure-local, cached and area-local
  evaluator twins that compiled code runs are proved equal to the
  specification beside their definitions in `Ix.Sharing`; their axioms are
  fixed here. `FamilyExact*` proves byte equality with the reference route's
  default search when both succeed at the same limits and every initial
  component has at most 16 members.
  `FamilyCost*`, `FamilyFullWitness`, `FamilyResidual`, `FamilyLocalWriting`
  and `FamilyWritingBound` are groundwork for an output-size bound. None of
  these modules proves that the rule never fails;
* `CanonicalProduction`: the compiler-facing theorems of the production
  entry (`canonicalSharingTiered_meaning`, `_format`, `_serialized` and their
  table variants), derived from the `Family*` results with no further
  premise;
* `Uniform*` (namespace `UniformModel`): the reference route's uniform-width
  optimizer of phase 1 returns a minimum of its cost model, with the component
  search, knapsack and tie-breaking proved against their specifications;
* `Tiered*` (namespace `Tiered`): the tiered phases 2 and 3, phase 3 never
  worse than phase 1, idempotence of the reference route, and the output
  format: every table entry and root is wire-safe and the reported length is
  the serialized length.

`IxSharingVerify.Builder` applies the format theorem to the compiler's
sharing builder `Ix.CompileM.buildConstantWithSharing`: every block it builds
is in the constant codec's wire domain. It imports the compiler
`Ix.CompileM`, so this root does not import it; `Ix.CompileCert.SharingRoots`
does.

The `@[csimp]` theorems in `Ix.Sharing` make compiled code run fast
bodies in place of these specifications. The audits
`IxSharingVerify.Audit.*` fix every root's axioms, require each such csimp
theorem on the compiler's import path to be a root, and keep `Ix.Sharing`
free of `sorryAx`. Built by the `IxSharingVerify` library
(`lake build IxSharingVerify`, and `lake lint`).
-/
