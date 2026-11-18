import IxVMRefinement.Assembly.NativeAliasStep
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
    fun E hE lim hc' hl' => hkeep E lim Reg (hStores E hE) (hcl E hE lim hc' hl'), ?_, hreads, ?_⟩
  · intro ci hci
    obtain ⟨x, hx, hn⟩ := hnamed ci hci
    rw [hn]
    exact not_mem_opNames_of_keyFree (hfree x hx)
  · intro ci hci
    obtain ⟨x, hx, hn⟩ := hnamed ci hci
    exact Or.inl ⟨x, hx, hn⟩

end IxVM.Refinement.Binding
