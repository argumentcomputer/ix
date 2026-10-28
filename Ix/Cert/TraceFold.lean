import Ix.Cert.GroupRuns
import Ix.Cert.BindingsResolve

/-! # The fold's facts in the trace's forms

`TraceSegments.TraceNeeds` asks, of the block the fold compiled for each of quotient Source's
groups, for the block's run, its claim, and facts about the fold's state the block was compiled
at. `GroupRuns` gives the run and the claim at the block's `FoldBlock`; this module gives the
rest, in the forms the segment theorems take:

* `FoldBlock.bound`: the snapshot's bindings resolve in the artifact (`BindingsResolve`);
* `FoldBlock.fresh_of`: the block's members are unbound at the snapshot;
* `GroupRuns.FoldBlock.blobsKept` (in `GroupRuns`): the blobs the run reads are the artifact's,
  since the block compile's tail after the members' compile only adds names (`GroupRuns.Grows`);
* `cacheRefs`: every entry of a compiled block's reference table is a mentioned name's binding
  or a blob of `runBlock`'s final state (`CompiledRefs.CacheRefs`). -/

namespace Ix.Cert.TraceFold

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.Cert.Resolution Ix.Cert.Schedule
open Ix.Cert.GroupRuns (FoldBlock)
open Ix.Cert.BlockContext (BoundResolve)

variable {env sub : Ix.Environment} {ixe : Ixon.Env} {failures : Failures} {snap : DriverAcc}
  {rep : Ix.Name} {all : Ix.Set Ix.Name} {r : BlockResult} {c : BlockState}

/-! ## The snapshot's bindings and the block's members -/

/-- **The snapshot's bindings resolve in the artifact** (`bound`, `bound₁`, `bound₂`), when the
input's inductives list their constructors at their positions. -/
theorem FoldBlock.bound (fb : FoldBlock env sub ixe failures snap rep all r c)
    (idx : BindingsResolve.ConstructorIndices env) : BoundResolve ixe snap.cenv := by
  obtain ⟨_, _, _, hu, hrun, hsnap, -⟩ := fb.fold
  exact BindingsResolve.boundResolve_onRun hu idx hrun hsnap

/-- **The members of the block are unbound at the snapshot** (`BlockCompiled.fresh`). -/
theorem FoldBlock.fresh_of {α : Type} (fb : FoldBlock env sub ixe failures snap rep all r c) {xs : List α}
    {name : α → Ix.Name} (mem : ∀ x ∈ xs, all.contains (name x) = true) :
    ∀ x ∈ xs, snap.cenv.nameToAddr.get? (name x) = none :=
  fun x hx => fb.fresh (name x) (mem x hx)

/-! ## The reference table at the merged cache -/

/-- **`RefTables.runBlock_refs` at `runBlock`'s final state** (`CompiledRefs.CacheRefs`): a lone
constant's compile ends there, and the block compile's tail after a mutual compile keeps every
blob it read (`GroupRuns.runBlock_paths`). -/
theorem cacheRefs : CompiledRefs.CacheRefs := by
  intro cenv all lo r c hr a ha
  obtain ⟨const, hconst, paths⟩ := GroupRuns.runBlock_paths hr
  rcases paths with ⟨hcond, hs⟩ | ⟨-, cs, out, s₄, hloop, hout, hext, hrec⟩
  · have hi : ∀ v, const = .inductInfo v → False := by
      rintro v rfl
      simp [GroupRuns.isIndConst] at hcond
    have hc : ∀ v, const = .ctorInfo v → False := by
      rintro v rfl
      simp [GroupRuns.isIndConst] at hcond
    obtain ⟨hI, same⟩ := RefTables.Holds.constantInfo (B := bindingView {})
      (N := fun x => all.contains x = true ∨ x = lo) hconst (Or.inr rfl) hi hc _ {} r c RefTables.refsOK_empty
      trivial hs
    exact hI.2 a (by rw [← same]; exact ha)
  · have members := RefTables.members_covers (cenv, { all, current := lo, mutCtx := default, univCtx := [] }) all
      (N := fun x => all.contains x = true ∨ x = lo) (fun x hx => .inl hx)
    rw [Std.HashSet.forIn_eq_forIn_toList] at members
    have cov := members {} cs {} hloop
    obtain ⟨hI, refs⟩ := RefTables.Holds.mutualBlock (B := bindingView {}) (sourceClasses cs)
      (fun cls hcls m hm => cov m (Claims.mem_sourceClasses hcls hm)) _ {} out s₄ RefTables.refsOK_empty trivial hout
    have block : r.block = out.block := (Prod.mk.inj hrec).1
    exact RefTables.Allowed.mono (hI.2 a (by rw [← refs, ← block]; exact ha)) hext

end Ix.Cert.TraceFold

/-- info: 'Ix.Cert.TraceFold.cacheRefs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.TraceFold.cacheRefs
