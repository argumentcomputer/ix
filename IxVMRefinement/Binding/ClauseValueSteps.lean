import IxVMRefinement.Assembly.ValueUnitStep
import IxVMRefinement.Binding.ClauseInvariant
import IxVMRefinement.Binding.UnitDefn

/-! # The step of a value record, in the binding fold's form

The step of a value record is stated once (`Typing.ValueUnitStep`,
`Assembly/ValueUnitStep.lean`): from the clause at the store and the limit of the record's
check, new constants, with the clause kept at every store of a family, every limit and every
registry. The binding fold carries the clause with one registry at every record store for its
witness store `R` and every carried limit within its groups; its unit step is
`Binding.OverUnitStep`.

* `ValueUnitStep.overUnitStep`: **the binding fold's step.** The record's check is read at one
  record store for `R` and one carried limit within the groups; the registry after the step is
  the registry before, at every store and limit.
* `overUnitStep_value`: the step of a standalone definition, theorem or opaque record, from the
  walk's observed check at a carried limit within the groups, validating or assuming.
* `overUnitStep_defnBlock`: the step of a block of definitions, from the walk's observed check
  of every member at such a limit.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)

/-- **The binding fold's step of a value record** (module docstring). `Ec` is a record store
for `R` the record's check is read at, at a carried limit `lc` within `G`; the clause is kept at
every record store for `R`; the keys of the record's constant addresses are free. -/
theorem _root_.IxVM.Refinement.Typing.ValueUnitStep.overUnitStep
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {t : Ix.Kernel.RoleTable}
    {G : Nat → Prop} {R E₀ Ec : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {Stores : Ixon.Env → Prop} {lc : Option Nat} {A : _root_.Address} {c : Ixon.Constant}
    (hRc : RecordsFor R Ec) (hc : Carried lc) (hl : LimWithin G t lc)
    (hStores : ∀ E, RecordsFor R E → Stores E)
    (hfree : ∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x))
    (h : ValueUnitStep.{u} L t envT E₀ Stores Ec lc A c) :
    OverUnitStep.{u} L t G R envT E₀ A c := by
  intro env Reg hext hnd hcl href hfresh
  obtain ⟨new, hnd', hfr, hkeep, hnamed, hreads⟩ :=
    h env Reg hext hnd (hcl Ec hRc lc hc hl) href hfresh
  refine ⟨new, Reg, hnd', hfr,
    fun E hE lim hc' hl' => hkeep E lim Reg (hStores E hE) (hcl E hE lim hc' hl'), ?_, hreads,
    ?_⟩
  · intro ci hci
    obtain ⟨x, hx, hn⟩ := hnamed ci hci
    rw [hn]
    exact not_mem_opNames_of_keyFree (hfree x hx)
  · intro ci hci
    obtain ⟨x, hx, hn⟩ := hnamed ci hci
    exact Or.inl ⟨x, hx, hn⟩

/-- **The step of a standalone definition, theorem or opaque record, over the fold's clause.**
The record's check is the walk's, observed under the role context at the limit `lc` (a carried
limit within `G`, validating or assuming); `Ec` is a record store for `R` the check is read at;
`R` holds the record, only records the run loaded, and every blob the run loaded. One constant
is installed, the declaration of the record's canonical annotations at the record's key; the
clause is kept with the same registry at every record store for `R` and every carried limit
within `G`. -/
theorem overUnitStep_value {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {G : Nat → Prop}
    {R E₀ Ec : Ixon.Env} {envT : Ix.Kernel.Env .anon} {bAddr A : _root_.Address}
    {c : Ixon.Constant} {d : Ixon.Definition} {lc : Option Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hRc : RecordsFor R Ec) (hst : StepStore calls t E₀ Ec)
    (hR : recordOf R A = some c)
    (hloaded : ∀ a lr, R.consts.get? a = some lr → E₀.consts.get? a = some lr)
    (hblobs : ∀ x b, E₀.blobs.get? x = some b → R.blobs.get? x = some b)
    (hinfo : c.info = .defn d) (hlogic : InLogic c)
    (hchk : Claim.CheckedLimAt calls bAddr t A lc)
    (hcn : Carried lc) (hln : LimWithin G t lc)
    (hkeys : ∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c) :
    OverUnitStep.{u} L t G R envT E₀ A c := by
  have hheld : ∀ E, RecordsFor R E → recordOf E A = some c ∧
      ∀ x b, E₀.blobs.get? x = some b → E.blobs.get? x = some b :=
    fun E hE => ⟨recordOf_of_recordsFor hE hR, blob_of_recordsFor hE hblobs⟩
  exact ValueUnitStep.overUnitStep (Stores := RecordsFor R) hRc hcn hln (fun _ hE => hE) hkeys
    (valueUnitStep_defn (Stores := RecordsFor R) hL ht hS hst (recordOf_of_loaded hloaded hR)
      hinfo hlogic hchk hheld hkeys hinert hcover)

/-- **The step of a block of definitions, over the fold's clause.** Every member's check is the
walk's, observed under the role context at the limit `lc` (a carried limit within `G`,
validating or assuming); `Ec` is a record store for `R` the checks are read at; `R` holds the
block record at `B` and a record at each member's address, only records the run loaded, and
every blob the run loaded. One constant is installed for each member, in index order; the
clause is kept with the same registry at every record store for `R` and every carried limit
within `G`. -/
theorem overUnitStep_defnBlock {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {G : Nat → Prop}
    {R E₀ Ec : Ixon.Env} {envT : Ix.Kernel.Env .anon} {bAddr B : _root_.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {lc : Option Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hRc : RecordsFor R Ec) (hst : StepStore calls t E₀ Ec)
    (hR : recordOf R B = some cb)
    (hRm : ∀ i mi, ms[i]? = some mi → (recordOf R (memberAddr B i mi)).isSome = true)
    (hloaded : ∀ a lr, R.consts.get? a = some lr → E₀.consts.get? a = some lr)
    (hblobs : ∀ x b, E₀.blobs.get? x = some b → R.blobs.get? x = some b)
    (hmuts : cb.info = .muts ms) (hlogic : InLogic cb) (hdefs : DefnBlock ms)
    (hchk : ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t B ms k lc)
    (hcn : Carried lc) (hln : LimWithin G t lc)
    (hkeys : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb) :
    OverUnitStep.{u} L t G R envT E₀ B cb := by
  have hbound : Bounded calls := (hst.good envT none).2
  have hRm' : ∀ i mi, ms[i]? = some mi →
      recordOf R (memberAddr B i mi) = some (memberProjection B i mi) := by
    intro i mi h
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (hRm i mi h)
    have h1 := recordOf_of_loaded hloaded hc'
    rw [hS.recordOf_of_recordAt (LoadedReads.memberCheckedLimAt_record hbound hS hcov
      (hchk i (Array.getElem?_eq_some_iff.mp h).1) h).2] at h1
    exact hc'.trans h1.symm
  have hheld : ∀ E, RecordsFor R E → recordOf E B = some cb ∧
      (∀ i mi, ms[i]? = some mi →
        recordOf E (memberAddr B i mi) = some (memberProjection B i mi)) ∧
      ∀ x b, E₀.blobs.get? x = some b → E.blobs.get? x = some b :=
    fun E hE => ⟨recordOf_of_recordsFor hE hR,
      fun i mi h => recordOf_of_recordsFor hE (hRm' i mi h), blob_of_recordsFor hE hblobs⟩
  exact ValueUnitStep.overUnitStep (Stores := RecordsFor R) hRc hcn hln (fun _ hE => hE) hkeys
    (valueUnitStep_defnBlock (Stores := RecordsFor R) hL ht hS hcov hst hRc
      (recordOf_of_loaded hloaded hR) hmuts hlogic hdefs hchk hheld hkeys hinert hcover)

end IxVM.Refinement.Binding
