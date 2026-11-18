import IxVMRefinement.Assembly.TypingRecLateFinal
import IxVMRefinement.Assembly.NativeBlockFinalRetHead

/-! # A native late recursor step using the registered family facts

The return-head and no-projection facts are supplied by the registry at the actual
step environment. They are not required at arbitrary environments independently
of that registry. The basis-major exclusion and the comparison's numeric bounds
remain explicit inputs until their producers are supplied.
-/

universe u

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency

/-- A checked native recursor preserves the stronger registered-family clause. -/
theorem unitStep_recLate_registered
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) (hlogic : InLogic c)
    (hnat : RecArmRun calls t A lim)
    (hkey : Decl.KeyFree (keyOf t A)) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    (hres : RecMajorNotBasis t E₀ A c rc)
    (hbounds : ∀ env P ip fam, StepAt.{u} t envT E₀ E lim A c env →
      MatchedAt t E env P ip fam →
      ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
        Ix.Cert.recordAt E ip.block = some cb → cb.info = .muts ms →
        ms[ip.idx.toNat]? = some (.indc ind) → RecArmBounds ip ind fam) :
    UnitStep.{u} (NativeBlockXR.{u} t E) t envT E₀ E lim A c :=
  unitStep_recLate_xr (RecMajorTie t E₀ A c rc) ht hinfo (address_size_of_record hS hc)
    (fun env hstep => recParent_of_arm_tied ht hS hst hc hinfo hnat hinert hcover hres env
      hstep)
    (fun env P ip fam hstep hlv hpar htie hm hhead hnoProj =>
      recLateOut_of_arm ht hS hcov hst hc hinfo hlogic hnat hkey hinert hcover hstep hlv
        hpar htie hm (famCtorRetHead_of_ixon hhead) hnoProj (hbounds env P ip fam hstep hm))

end IxVM.Refinement.Typing
