import IxVMRefinement.Guard.UseStore
import IxVMRefinement.Assembly.NativeBlockGuardUse

/-! # A use's observation over the run's store, from the traced walk

`Core.GuardWalk.proj_guard_traced` gives, for a `KernelInfer::proj_guard` run that took the
checked walk: the guard level as the fold of the field levels under the flags, the flags against
the stored constructor type, the run's constructor load, the raw telescope behind its type
pointer, and the classifier's field traces of that telescope with the zero-set agreement.

* `projGuardUse_runStore`: over a run store that holds the run's hashed records, those data are
  the use-site observation `Ix.Kernel.ProjGuardUse` over the store's raw dictionary, at the
  constructor's raw telescope read from the store. The trace answers are read in the store as
  for the install (`typeAnswer_runStore`, `valueAnswer_runStore`), and the telescope by
  `ctorRaw_runStore`.

The statement takes the traced data as hypotheses, so it does not depend on which facts of the
context the walk was read from.
-/

namespace IxVM.Refinement.Guard

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open IxVM.Refinement.Core
open IxVM.Refinement.Decl (RawExprRep RawTypeAt RawDeltaAt RawFieldTraces)

/-- **The use-site observation over the run's store** (module docstring). -/
theorem projGuardUse_runStore {c : ScopedCtx} {calls : List (Call F)} {E' : Ixon.Env}
    (hS : LoadedReads.RunStore calls E') (hcov : LoadedReads.HashedRecordsStored calls E')
    (hbound : IxVM.Consistency.Bounded calls)
    {b : Bytes.Address} {bp : SourceValue F} {i : F} {h : Heap F}
    (hb : Bytes.RepAddressRef addrTy h b bp)
    {T : KExpr} {nP f : Nat} {g : KLevel}
    {lus : List KLevel} {flags : List Bool} {sigs : List KLevel} {S : KExpr}
    {ptr x_cty w₁ w₃ w₄ w₅ w₆ w₇ w₈ : SourceValue F} {m : Heap F} {cs₀ : List (Call F)}
    (hfold : g = (List.range f).foldl
      (fun acc j => if flags.getD j false then Ix.Kernel.Level.max acc (lus.getD j .zero)
        else acc) (lus.getD f .zero))
    (hflags : ∀ j, j < f → Ix.Kernel.structUsedLater T nP j = true →
      flags.getD j false = true)
    (load : ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field 0] h ptr m cs₀)
    (inside : ∀ cl ∈ cs₀, cl ∈ calls)
    (ld : loadValue m ptr = .ok (.construct kciEnum "Ctor" [w₁, x_cty, w₃, w₄, w₅, w₆, w₇, w₈]))
    (physical : RawExprRep (Core.keyOf GuardRaw.addressTable) m 0 S x_cty)
    (traces : RawFieldTraces (RawTypeAt c (Core.keyOf GuardRaw.addressTable) calls)
      (RawDeltaAt c (Core.keyOf GuardRaw.addressTable) calls) nP (f + 1) [] S sigs)
    (zeros : ∀ j, j ≤ f → ∀ φ : Ix.Kernel.LevelParam → Nat,
      Ix.Kernel.Level.eval φ (lus.getD j .zero) = 0 ↔
        Ix.Kernel.Level.eval φ (sigs.getD j .zero) = 0) :
    ∃ raw, Guard.ctorRaw E' (ixAddr b) (ZMod.val i) 0 = some raw ∧
      Ix.Kernel.ProjGuardUse (GuardRaw.ofStore E') raw T nP f g := by
  have hpar := loadParentsHeld_of_runStore hS hcov
  obtain ⟨fuel, walked⟩ := traces.fieldSignatures_erased (look := GuardRaw.ofStore E')
    (fun _ _ _ answer =>
      typeAnswer_runStore hS hcov hpar hbound (fun _ member => member) answer)
    (fun _ _ _ answer =>
      valueAnswer_runStore hS hcov hpar hbound (fun _ member => member) answer)
  exact ⟨S.eraseMeta,
    ctorRaw_runStore hS hcov (bounded_sub inside hbound) inside load hb ld
      (Heap.Extends.refl m) physical,
    ⟨lus, sigs, fuel, fun j => flags.getD j false, walked, zeros, hflags, hfold⟩⟩

end IxVM.Refinement.Guard
