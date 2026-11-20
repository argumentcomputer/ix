import IxVMRefinement.Assembly.NativeAliasStep
import IxVMRefinement.Assembly.NativeAliasInstallOut
import IxVMRefinement.Binding.ClauseInvariant
import IxVMRefinement.Binding.UnitDefn

/-! # The step of a block whose former is declared at a definition, in the binding fold's form

The step is stated once (`Typing.AliasUnitStep`, `Assembly/NativeAliasStep.lean`): from the
clause at the store and the limit of the block's check, new constants and one family, with the
clause kept at every admitted store, every limit and every registry. The binding fold carries
the clause with one registry at every record store for its store `R` and every carried limit
within its groups; its unit step is `Binding.OverUnitStep`.

* `holdsBlock_of_recordsFor`: a record store for `R` holds the block's records and the run's
  blobs when `R` does.
* `AliasUnitStep.overUnitStep`: **the binding fold's step.** The block's check is read at one
  record store for `R` and one carried limit within the groups; the registry after the step is
  the registry before, extended by the one family, at every store and limit. Nothing is asked
  of the circuit's dispatch at another store.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Ix.Kernel.Semantics (NativeFam)

/-- **A record store for `R` holds the block's records and the run's blobs when `R` does.** -/
theorem holdsBlock_of_recordsFor {R E₀ E : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} (hE : RecordsFor R E) (hblock : recordOf R B = some cb)
    (hformer : recordOf R (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)))
    (hctors : ∀ j < ind.ctors.size,
      recordOf R (ctorAddr B 0 j) = some (constructorProjection B 0 j))
    (hblobs : ∀ x b, E₀.blobs.get? x = some b → R.blobs.get? x = some b) :
    HoldsBlock E₀ E B cb ind where
  decoded := hE.1
  block := recordOf_of_recordsFor hE hblock
  former := recordOf_of_recordsFor hE hformer
  ctors := fun j hj => recordOf_of_recordsFor hE (hctors j hj)
  blobs := blob_of_recordsFor hE hblobs

/-- **The binding fold's step of a block whose former is declared at a definition** (module
docstring). `Ec` is a record store for `R` the block's check is read at, at a carried limit
`lc` within `G`; the clause is kept at every record store for `R`; the keys of the record's
constant addresses are free. -/
theorem _root_.IxVM.Refinement.Typing.AliasUnitStep.overUnitStep {t : Ix.Kernel.RoleTable}
    {G : Nat → Prop} {R E₀ Ec : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {Stores : Ixon.Env → Prop} {lc : Option Nat} {B : _root_.Address} {cb : Ixon.Constant}
    (hRc : RecordsFor R Ec) (hc : Carried lc) (hl : LimWithin G t lc)
    (hStores : ∀ E, RecordsFor R E → Stores E)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (h : AliasUnitStep.{u} t envT E₀ Stores Ec lc B cb) :
    OverUnitStep.{u} FormerOpenTraceAt t G R envT E₀ B cb := by
  intro env Reg hext hnd hcl href hfresh
  obtain ⟨new, fam, hnd', hfr, hkeep, hnamed, hreads⟩ :=
    h env Reg hext hnd (hcl Ec hRc lc hc hl) href hfresh
  refine ⟨new, fun f => Reg f ∨ f = fam, hnd', hfr,
    fun E hE lim hc' hl' => hkeep E lim Reg (hStores E hE) (hcl E hE lim hc' hl'), ?_, hreads, ?_,
    Ix.Kernel.EnvExt.append hfr fun ci hci _ _ _ _ => by
      obtain ⟨x, -, hn⟩ := hnamed ci hci
      rw [hn]
      exact Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t x)⟩
  · intro ci hci
    obtain ⟨x, hx, hn⟩ := hnamed ci hci
    rw [hn]
    exact not_mem_opNames_of_keyFree (hfree x hx)
  · intro ci hci
    obtain ⟨x, hx, hn⟩ := hnamed ci hci
    exact Or.inl ⟨x, hx, hn⟩


/-- **The binding fold's step of a block whose former is declared at a definition, from the
walk's facts.** The member's check is the walk's, observed under the role context at the limit
`lim` (a carried limit within `G`); `Ec` is a record store for `R` the check is read at; `R`
holds the block's records and every blob the run loaded. `hliterals` separates the family's
key from the four literal-function keys. -/
theorem overUnitStep_nativeBlockAlias {calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
    {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R E₀ Ec : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {bAddr B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {lim : Option Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hRc : RecordsFor R Ec) (hst : StepStore calls t E₀ Ec)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hRblock : recordOf R B = some cb)
    (hRformer : recordOf R (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)))
    (hRctors : ∀ j < ind.ctors.size,
      recordOf R (ctorAddr B 0 j) = some (constructorProjection B 0 j))
    (hblobs : ∀ x b, E₀.blobs.get? x = some b → R.blobs.get? x = some b)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (hcn : Carried lim) (hln : LimWithin G t lim)
    (hnat : NativeRouteAt calls B) (halias : FormerAtAlias t E₀ B cb ind)
    (hliterals : Core.keyOf t (memberAddr B 0 (.indc ind)) ≠ Ix.Kernel.stringOfListName ∧
      Core.keyOf t (memberAddr B 0 (.indc ind)) ≠ Ix.Kernel.listNilName ∧
      Core.keyOf t (memberAddr B 0 (.indc ind)) ≠ Ix.Kernel.listConsName ∧
      Core.keyOf t (memberAddr B 0 (.indc ind)) ≠ Ix.Kernel.charOfNatName)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hcov : Ingress.CanonicalHashCoverage Ec calls) :
    OverUnitStep.{u} FormerOpenTraceAt t G R envT E₀ B cb :=
  AliasUnitStep.overUnitStep hRc hcn hln
    (fun E hE => holdsBlock_of_recordsFor hE hRblock hRformer hRctors hblobs) hfree
    (aliasUnitStep_of_member ht hS hst hrec hchk hnat halias hliterals hfree hinert hcover hcov)

end IxVM.Refinement.Binding
