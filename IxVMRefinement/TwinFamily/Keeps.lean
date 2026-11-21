import IxVMRefinement.TwinFamily.Target
import IxVMRefinement.FamilyGraph.Graph
import IxVMRefinement.Assembly.NativeBlockInv

/-! # A plain unit step keeps the clause that hands a twin its block's family record

The twin's step needs the family record of its block installed: each of its recursors stored
with a model companion. The fold carries that as `FamilyRecsModeled` (a stored constant at a
constant address of a claimed family record is a recursor with a model companion), beside its
clause `X`. The family step establishes it; this module proves that every other step keeps it:

* `unitStep_keepsFamilyRecsModeled_of_apart`: a unit step for `X` at a record none of whose
  constant addresses is one of a claimed family record is a unit step for
  `X ∧ FamilyRecsModeled`. Its new constants are at the record's own constant addresses, or at
  derived keys, which are the key of no address; the constants stored before keep their
  companions.
* `unitStep_keepsFamilyRecsModeled`: so does the unit step of every checked record that no
  block claims, every unit of the family fold among them: a constant address two checked
  records share makes them one record (`walked_eq_famRecord`).

So the clause `X ∧ FamilyRecsModeled` is carried over the family graph with the plain kinds
stated at `X`, and no clause of the fold's own is changed. -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal RecRule)
open Ix.Kernel.Model (HasModel)

set_option linter.unusedVariables false

/-- **A unit step at a record that owns no constant address of a claimed family record keeps
the clause** (module docstring). -/
theorem unitStep_keepsFamilyRecsModeled_of_apart {X : Ix.Kernel.Env .anon → Prop}
    {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env} {lim : Option Nat}
    {fam : _root_.Address → Option _root_.Address} {A : _root_.Address} {c : Ixon.Constant}
    (hroles : (t.bound.toList.map (·.1)).Nodup)
    (hnr : ∀ (B rb x : _root_.Address) (crb : Ixon.Constant), fam B = some rb →
      recordOf E₀ rb = some crb → ConstAddrOf rb crb x → ¬ ConstAddrOf A c x)
    (h : UnitStep.{u} X t envT E₀ E lim A c) :
    UnitStep.{u} (fun env => X env ∧ FamilyRecsModeled t E₀ fam env) t envT E₀ E lim A c := by
  intro env hext hnd hinv hXe href hfresh
  obtain ⟨hX, hfm⟩ := hXe
  obtain ⟨new, hnd', hfr, hinv', hX', hreads, hnames⟩ := h env hext hnd hinv hX href hfresh
  have hgrow : Ix.Kernel.Grows (fun k => env.find? k = none) env ⟨new ++ env.consts⟩ :=
    ⟨new, rfl, fun ci hci => ⟨hfr ci hci, hfr ci hci⟩, hnd'⟩
  have hfind : ∀ {k : Ix.Kernel.Key .anon} {c' : ConstantInfo .anon},
      env.find? k = some c' →
        (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k = some c' := by
    intro k c' hk
    rw [hgrow.find_eq (by show ¬ (env.find? k = none); rw [hk]; simp)]
    exact hk
  refine ⟨new, hnd', hfr, hinv', ⟨hX', FamilyRecsModeled.step hfm hfind ?_⟩, hreads, hnames⟩
  intro B rb x crb hrb hcrb hx hs hnone
  exfalso
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hs
  rcases find?_append_cases new hci with hm | hold
  · have hname : ci.name = keyOf t x := Core.WhnfAux.name_of_find hci
    rcases hnames _ hm with ⟨x', hx', hn⟩ | ⟨k, s, haux⟩
    · have hxx : x = x' := keyOf_inj hroles (hname.symm.trans hn)
      rw [← hxx] at hx'
      exact hnr B rb x crb hrb hcrb hx hx'
    · exact keyOf_nonAux t x k s (hname.symm.trans haux)
  · rw [hnone] at hold
    cases hold

/-- **The unit step of a checked record that no block claims keeps the clause**: a constant
address of a claimed family record that is a constant address of the record would make the
record that family record. -/
theorem unitStep_keepsFamilyRecsModeled {X : Ix.Kernel.Env .anon → Prop}
    {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env} {lim : Option Nat}
    {seeds : List _root_.Address} {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    (hroles : (t.bound.toList.map (·.1)).Nodup)
    {A : _root_.Address} {c : Ixon.Constant} (hW : Walked Top Inner A)
    (hU : Unclaimed fam A) (hc : recordOf E₀ A = some c)
    (h : UnitStep.{u} X t envT E₀ E lim A c) :
    UnitStep.{u} (fun env => X env ∧ FamilyRecsModeled t E₀ fam env) t envT E₀ E lim A c := by
  refine unitStep_keepsFamilyRecsModeled_of_apart hroles ?_ h
  intro B rb x crb hrb hcrb hx hxA
  have hAr : A = rb := walked_eq_famRecord hG hF hW hc hxA hrb hcrb hx
  rw [← hAr] at hrb
  exact hU B hrb

/-- **The clause holds at the witness's environment**: it stores no constant address of a
family record (`FamilyGraph.famFresh`). -/
theorem familyRecsModeled_start {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon}
    {E₀ : Ixon.Env} {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner) :
    FamilyRecsModeled t E₀ fam envT :=
  familyRecsModeled_of_fresh fun B rb crb x hrb hcrb hx => hF.famFresh B rb crb x hrb hcrb hx

end IxVM.Refinement.Typing.TwinFamily
