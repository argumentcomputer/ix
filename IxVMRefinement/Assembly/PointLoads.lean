import IxVMRefinement.Assembly.PointUnitStep
import IxVMRefinement.Assembly.PointNewLoads

/-! # The load facts at the new constants of a constructors-only install

`pointLoadsFrom`: the step's load interface `PointLoadsFrom` holds outright. At an install as the
store reads it (`PointInstall`) over a prefix whose invariant holds, the load contract's fields
that reach a new constant are the reload fields (`PointNewLoads.lean`: a load at a new former's
or constructor's address represents the stored constant; no projection table is stored) and the
fields a constructors-only family is never asked (`PointGateLoads.lean`), the latter from the
block's shape (`PointShape`) and the install's family fact (`PointInstall.famNew`).

`unitStep_pointBlock'` is `unitStep_pointBlock` with that interface discharged.
-/

namespace IxVM.Refinement.Typing

open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo)

universe u

/-- **The load facts at the new constants, discharged.** -/
theorem pointLoadsFrom (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (B : _root_.Address)
    (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (n : Nat) :
    PointLoadsFrom.{u} t E B cb ms n := by
  intro env new hI hinv haux hfresh hgate
  have hmod : ModeledAt E B := PointShape.modeledAt hinv hI.recordAt hI.muts hgate
  have hfam : PointFamNew ⟨E, env, t, some n⟩ new B ms :=
    fun b i hbh hi hf => hI.famNew hbh hi hf
  have hE := hI.blockEta hinv hgate hmod hfam
  exact
    { getCI := hI.newGetCI
      getCprj := hI.newGetCprj
      getIprj := hI.newGetIprj
      inductRecord := hI.newInductRecord
      projTables := hI.newProjTables hmod hfam
      projTablesAt := hI.newProjTablesAt hmod hfam
      unitLike := hI.newUnitLike hgate hfam
      unitLikeRaw := hI.newUnitLikeRaw hgate hfam
      eta := hE.eta
      etaIota := hE.etaIota
      inductBlock := hI.newInductBlock
      projCtorTele := hI.newProjCtorTele haux hfresh
      projFire := fun _ tbl hm _ _ => (hI.noTable tbl hm).elim
      ctorIndRes := hI.newCtorIndRes }

/-- **`UnitStep` for a block on the constructors-only route, the load interface discharged.** The
named hypotheses left are the block's shape (`hgate`), the unstored roles (`hunb`) and the
refinement of the block's arm (`hev`). -/
theorem unitStep_pointBlock' {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {R E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {B : _root_.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hshape : TableShape.{u} t (fun _ => True) R envT)
    (hrec : ModeledBlockRecord E₀ B cb ms) (hlim : lim = some n)
    (hgate : PointShape E B ms)
    (hunb : ∀ x, ConstAddrOf B cb x → ∀ r, ¬ StoredRole r → t.addressOf? r ≠ some x)
    (hP : HashedBlockProjectionsHeld E)
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hev : PointEvidence.{u} t E₀ E B cb ms n) :
    UnitStep.{u} (PointX.{u} t E) t envT E₀ E lim B cb :=
  unitStep_pointBlock ht hS hst hshape hrec hlim hgate hunb hP hinert hcover hev
    (pointLoadsFrom.{u} t E B cb ms n)

end IxVM.Refinement.Typing
