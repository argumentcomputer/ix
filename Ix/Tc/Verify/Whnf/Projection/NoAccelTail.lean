import Ix.Tc.Verify.Whnf.Structural.VerifiedStep

/-!
# Concrete no-acceleration projection tail

`VerifiedStep` still exposes the whole production projection helper as one boundary.
This slice removes its non-String core: after preprocessing, `.noAccel`
forces the `Fin.val`/`Decidable.rec` acceleration probe to miss, lazy lookup
is handled by the actual `tryGetConst` state theorem, and a selected field is
proved supported from the finite spine-input closure.

Only String-literal construction/normalization and the installed lazy-ingress
hook remain as explicit premises when the tail is composed below.
-/

namespace Ix.Tc
namespace RecM

namespace WhnfCoreInputSupport

/-- Every element returned by `collectSpine` is covered by the finite input
support.  Non-applications have an empty spine; the application case is
exactly the `WhnfCoreInputSupport.app` field. -/
theorem spineArg {support : RunSupport}
    (hinputs : WhnfCoreInputSupport support)
    {value head arg : KExpr .anon} {args : Array (KExpr .anon)}
    (hvalue : support value)
    (hspine : value.collectSpine = (head, args))
    (harg : arg ∈ args.toList) :
    support arg := by
  cases value with
  | app f a info =>
      exact (hinputs.app hvalue hspine).2 arg harg
  | var idx name info => simp [KExpr.collectSpine, KExpr.collectSpine.go] at hspine; rw [hspine.2] at harg; simp at harg
  | fvar id name info => simp [KExpr.collectSpine, KExpr.collectSpine.go] at hspine; rw [hspine.2] at harg; simp at harg
  | sort u info => simp [KExpr.collectSpine, KExpr.collectSpine.go] at hspine; rw [hspine.2] at harg; simp at harg
  | const id us info => simp [KExpr.collectSpine, KExpr.collectSpine.go] at hspine; rw [hspine.2] at harg; simp at harg
  | lam name bi ty body info => simp [KExpr.collectSpine, KExpr.collectSpine.go] at hspine; rw [hspine.2] at harg; simp at harg
  | all name bi ty body info => simp [KExpr.collectSpine, KExpr.collectSpine.go] at hspine; rw [hspine.2] at harg; simp at harg
  | letE name ty value body nondep info => simp [KExpr.collectSpine, KExpr.collectSpine.go] at hspine; rw [hspine.2] at harg; simp at harg
  | prj id field value info => simp [KExpr.collectSpine, KExpr.collectSpine.go] at hspine; rw [hspine.2] at harg; simp at harg
  | nat value blob info => simp [KExpr.collectSpine, KExpr.collectSpine.go] at hspine; rw [hspine.2] at harg; simp at harg
  | str value blob info => simp [KExpr.collectSpine, KExpr.collectSpine.go] at hspine; rw [hspine.2] at harg; simp at harg

end WhnfCoreInputSupport

/-- State and finite-result closure of the exact projection tail in the
production no-acceleration layer. -/
theorem tryProjReduceTail_noAccel_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (hinputs : WhnfCoreInputSupport support)
    (hfault : ∀ uvars Delta,
      TcM.LazyFaultPreserves
        (WhnfStateInv .noAccel semantics trProj world support uvars Delta))
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {id : KId .anon} {field : UInt64} {value : KExpr .anon}
    (hvalue : support value) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryProjReduceTail id field value)
      (fun result _ => match result with
        | none => True
        | some reduced => support reduced) := by
  intro methods hmethods
  rcases hspine : value.collectSpine with ⟨head, args⟩
  unfold tryProjReduceTail
  simp only [hspine]
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (Q₁ := fun result _ => result = none)
  · intro hI
    rw [tryReduceFinValDecidableRec_noAccel hI.2.2.1]
    exact ⟨hI, rfl⟩
  · intro result after hresult
    subst result
    simp only [ReaderT.run, pure_bind]
    cases head with
    | const ctorId us info =>
        simp only
        change TcM.WF _ after (TcM.tryGetConst ctorId >>= _) _
        apply TcM.WF.bind
          (TcM.tryGetConst_wf (hfault uvars Delta) ctorId after)
        intro found afterLookup _
        cases found with
        | none => exact TcM.WF.pure fun _ => trivial
        | some decl =>
            cases decl <;> try exact TcM.WF.pure (fun _ => trivial)
            case ctor name levelParams isUnsafe lvls induct cidx params fields ty =>
              cases hfield : args[params.toNat + field.toNat]? with
              | none =>
                  simp only [hfield]
                  exact TcM.WF.pure fun _ => trivial
              | some selected =>
                  simp only [hfield]
                  exact TcM.WF.pure fun _ =>
                    hinputs.spineArg hvalue hspine
                      (Array.mem_toList_iff.mpr
                        (Array.mem_of_getElem? hfield))
    | _ =>
        simp only
        exact TcM.WF.pure fun _ => trivial

namespace ProjectionStringPrelude

/-- The only projection prelude that is not state-pure.  Its scope is
strictly smaller than `ProjectionHelper.WF`: it owns constructor expansion
and the one recursive WHNF callback, but no projection lookup or field
selection. -/
structure WF (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Prop where
  run : ∀ {uvars Delta s value blob info},
    support (.str value blob info) →
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryProjPrepare (.str value blob info))
      (fun result _ => support result)

end ProjectionStringPrelude

namespace ProjectionPrelude

/-- State and finite-support closure of the named production preprocessing
seam. -/
def WF (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Prop :=
  ∀ {uvars Delta s value},
    support value →
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryProjPrepare value) (fun prepared _ => support prepared)

/-- Every non-String branch of the production prelude is definitionally
state-pure and returns its supported input unchanged. -/
theorem nonString
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {value : KExpr .anon}
    (hshape : match value with | .str .. => False | _ => True)
    (hvalue : support value) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryProjPrepare value) (fun prepared _ => support prepared) := by
  cases value with
  | str value blob info => simp at hshape
  | var idx name info =>
      rw [tryProjPrepare_eq]
      exact RecM.WF.pure fun _ => hvalue
  | fvar id name info =>
      rw [tryProjPrepare_eq]
      exact RecM.WF.pure fun _ => hvalue
  | sort u info =>
      rw [tryProjPrepare_eq]
      exact RecM.WF.pure fun _ => hvalue
  | const id us info =>
      rw [tryProjPrepare_eq]
      exact RecM.WF.pure fun _ => hvalue
  | app f arg info =>
      rw [tryProjPrepare_eq]
      exact RecM.WF.pure fun _ => hvalue
  | lam name bi ty body info =>
      rw [tryProjPrepare_eq]
      exact RecM.WF.pure fun _ => hvalue
  | all name bi ty body info =>
      rw [tryProjPrepare_eq]
      exact RecM.WF.pure fun _ => hvalue
  | letE name ty value body nondep info =>
      rw [tryProjPrepare_eq]
      exact RecM.WF.pure fun _ => hvalue
  | prj id field value info =>
      rw [tryProjPrepare_eq]
      exact RecM.WF.pure fun _ => hvalue
  | nat value blob info =>
      rw [tryProjPrepare_eq]
      exact RecM.WF.pure fun _ => hvalue

/-- The String case of the uniform prelude is exactly the separately named
effectful boundary. -/
theorem string
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (hstring : ProjectionStringPrelude.WF semantics trProj world support)
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {value : String} {blob : Address} {info : ExprInfo .anon}
    (hvalue : support (.str value blob info)) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryProjPrepare (.str value blob info))
      (fun prepared _ => support prepared) :=
  hstring.run hvalue

/-- Assemble the uniform prelude from its only effectful String case. -/
theorem ofString
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (hstring : ProjectionStringPrelude.WF semantics trProj world support) :
    ProjectionPrelude.WF semantics trProj world support := by
  intro uvars Delta s value hvalue
  cases value with
  | str value blob info => exact string hstring hvalue
  | var idx name info => exact nonString trivial hvalue
  | fvar id name info => exact nonString trivial hvalue
  | sort u info => exact nonString trivial hvalue
  | const id us info => exact nonString trivial hvalue
  | app f arg info => exact nonString trivial hvalue
  | lam name bi ty body info => exact nonString trivial hvalue
  | all name bi ty body info => exact nonString trivial hvalue
  | letE name ty value body nondep info => exact nonString trivial hvalue
  | prj id field value info => exact nonString trivial hvalue
  | nat value blob info => exact nonString trivial hvalue

end ProjectionPrelude

/-- Compose the proved production tail with the named preprocessing seam in
`tryProjReduce`. -/
theorem tryProjReduce_noAccel_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (hinputs : WhnfCoreInputSupport support)
    (hfault : ∀ uvars Delta,
      TcM.LazyFaultPreserves
        (WhnfStateInv .noAccel semantics trProj world support uvars Delta))
    (hprepare : ProjectionPrelude.WF semantics trProj world support)
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {projId : KId .anon} {projField : UInt64} {value : KExpr .anon}
    (hvalue : support value) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryProjReduce projId projField value)
      (fun result _ => match result with
        | none => True
        | some reduced => support reduced) := by
  rw [tryProjReduce_eq]
  apply RecM.WF.bind (Q₁ := fun prepared _ => support prepared)
  · exact hprepare hvalue
  · intro prepared after hprepared
    exact tryProjReduceTail_noAccel_wf hinputs hfault
      (uvars := uvars) (Delta := Delta) (s := after)
      (id := projId) (field := projField) hprepared

namespace ProjectionHelper

/- Concrete `.noAccel` projection-helper closure.  The former monolithic
helper premise is reduced to String preprocessing plus the installed lazy
ingress contract. -/
theorem noAccelOfPrelude
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (hinputs : WhnfCoreInputSupport support)
    (hfault : ∀ uvars Delta,
      TcM.LazyFaultPreserves
        (WhnfStateInv .noAccel semantics trProj world support uvars Delta))
    (hprepare : ProjectionPrelude.WF semantics trProj world support) :
    ProjectionHelper.WF .noAccel semantics trProj world support := by
  intro uvars Delta methods s id field value hmethods hvalue
  exact tryProjReduce_noAccel_wf hinputs hfault hprepare
    (uvars := uvars) (Delta := Delta) (s := s) (projId := id)
    (projField := field) hvalue methods hmethods

/-- Public concrete projection-helper constructor: all non-String control
flow is proved, so only String preprocessing and lazy ingress are supplied. -/
theorem noAccel
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (hinputs : WhnfCoreInputSupport support)
    (hfault : ∀ uvars Delta,
      TcM.LazyFaultPreserves
        (WhnfStateInv .noAccel semantics trProj world support uvars Delta))
    (hstring : ProjectionStringPrelude.WF semantics trProj world support) :
    ProjectionHelper.WF .noAccel semantics trProj world support :=
  noAccelOfPrelude hinputs hfault (ProjectionPrelude.ofString hstring)

end ProjectionHelper

end RecM
end Ix.Tc
