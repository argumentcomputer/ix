import Ix.CompileCert.EmissionBlocks
import Ix.CompileCert.ProjectionLayout

/-! # Inductives through the driver's mutual path (N-READS, N5 b)

The driver (`Ix.CompileM.compileBlockWithAux`) compiles every inductive block,
singletons included, through `compileMutualBlock` over `MutConst.mkIndc`
members, not through `compileConstantInfo (.inductInfo …)` (the
`compileInductiveFamilyBlock` emitter, which `InductiveReading.inductive_reads`
covers; only `compileConstNoAuxPure` takes it). This module carries the family
reading over to the mutual path.

**A one-member inductive class** (`singletonBlock_correct`): `compileMutualBlock
[[.indc d]]` runs the same member emitter as the family path
(`compileMutConstMember (.indc d)` is `compileInductiveData d` under
`withCurrent`, and `compileInductive` is `compileInductiveData` of the
family's `sourceData`, `Emission.compileInductive_eq`), the same sharing
builder over `.muts #[.indc ind]` (`ProjectionLayout.finish_mutual_ok`), and
only the projections differ (`buildMutualProjections`). So the emitted record
keeps the payload's skeleton and reads its roots as terms related to the
source's, as `EmissionBlocks.familyBlock_correct` states for the family path. -/

namespace Ix.CompileCert.MutualInductiveReading

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.CompileCert.UniversePipeline
open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader (Ctx CName CExpr ReadM MemberReader)

/-- The context `compileMutualBlock classes` runs its members in. -/
def mutContext (classes : List (List MutConst)) (context : CompileEnv × BlockEnv) : CompileEnv × BlockEnv :=
  (context.1, { context.2 with mutCtx := MutConst.ctx classes })

/-- **A one-member inductive class compiles as its member emitter**:
`compileMutConsts [[.indc d]]` is `compileInductiveData d` under `withCurrent`,
with the payload as its one member and its metadata after the member's name. -/
theorem mutConsts_indc (d : Ix.Ind) {context : CompileEnv × BlockEnv} {before after : BlockState}
    {payload : Array Ixon.MutConst × Array Ixon.Expr × Array (Ix.Name × Ixon.ConstantMeta)}
    (ran : rawRun (compileMutConsts [[.indc d]]) context before = (.ok payload, after)) :
    ∃ out, rawRun (compileInductiveData d) (Emission.current d.name context) before = (.ok out, after) ∧
      payload.1 = #[.indc out.1] ∧ payload.2.2 = #[] ++ (#[(d.name, out.2.1)] ++ out.2.2.1) := by
  unfold compileMutConsts at ran
  obtain ⟨state, middle, classesRan, finish⟩ := bind_ok ran
  rw [rawRun_pure] at finish
  cases finish
  rw [compileMutConstClasses] at classesRan
  obtain ⟨classState, classMiddle, classRan, restRan⟩ := bind_ok classesRan
  rw [compileMutConstClasses, rawRun_pure] at restRan
  cases restRan
  rw [compileMutConstClass] at classRan
  obtain ⟨member, memberMiddle, memberRan, equivRan⟩ := bind_ok classRan
  rw [compileEquivalentMutConsts, rawRun_pure] at equivRan
  cases equivRan
  unfold compileMutConstMember at memberRan
  obtain ⟨out, outMiddle, outRan, wrapRan⟩ := bind_ok memberRan
  unfold withCurrent at outRan
  rw [rawRun_withBlockEnv] at outRan
  obtain ⟨ind, constMeta, ctorMetaPairs, exprs⟩ := out
  dsimp only at wrapRan
  rw [rawRun_pure] at wrapRan
  cases wrapRan
  exact ⟨_, outRan, rfl, rfl⟩

end Ix.CompileCert.MutualInductiveReading
