import IxVMRefinement.TwinFamily.Target
import IxVMRefinement.FamilyGraph.Graph
import IxVMRefinement.Assembly.NativeBlockInv

/-! # A plain unit step keeps the clause that hands a twin its block's family record

The twin's step needs the family record of its block installed: each of its recursors stored
with a model companion. The fold carries that as `FamilyRecsModeled` (every stored recursor at a
member of a block of recursors has a model companion), beside its clause `X`. The family step
establishes it and the twin's step keeps it; this module proves that every other step keeps it:

* `unitStep_keepsFamilyRecsModeled_of_apart`: a unit step for `X` at a record none of whose constant
  addresses is a member of a block of recursors is a unit step for `X ∧ FamilyRecsModeled`. Its
  new constants are at the record's own constant addresses, or at derived keys, which are the
  key of no address; the constants stored before keep their companions.
* `unitStep_keepsFamilyRecsModeled`: so does the unit step of every checked record that is no
  block of recursors: a constant address two records share makes them one record.

So the clause `X ∧ FamilyRecsModeled` is carried over the family graph with the plain kinds
stated at `X`, and no clause of the fold's own is changed. -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal RecRule)
open Ix.Kernel.Model (HasModel)

set_option linter.unusedVariables false

/-- **A unit step at a record that owns no member of a block of recursors keeps the family
recursors' companions** (module docstring). -/
theorem unitStep_keepsFamilyRecsModeled_of_apart {X : Ix.Kernel.Env .anon → Prop}
    {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env} {lim : Option Nat}
    {A : _root_.Address} {c : Ixon.Constant}
    (hroles : (t.bound.toList.map (·.1)).Nodup)
    (hnr : ∀ (rb x : _root_.Address) (crb : Ixon.Constant) (rs : Array Ixon.MutConst),
      FamRecRecord E₀ rb crb rs → ConstAddrOf rb crb x → ¬ ConstAddrOf A c x)
    (h : UnitStep.{u} X t envT E₀ E lim A c) :
    UnitStep.{u} (fun env => X env ∧ FamilyRecsModeled t E₀ env) t envT E₀ E lim A c := by
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
  refine ⟨new, hnd', hfr, hinv', ⟨hX', ?_⟩, hreads, hnames⟩
  intro rb x crb rs cv mI rP rules hR hx hf
  rcases find?_append_cases new hf with hm | hold
  · exfalso
    have hname : (ConstantInfo.recInfo cv mI rP rules).name = keyOf t x :=
      Core.WhnfAux.name_of_find hf
    rcases hnames _ hm with ⟨x', hx', hn⟩ | ⟨k, s, haux⟩
    · have hxx : x = x' := keyOf_inj hroles (hname.symm.trans hn)
      rw [← hxx] at hx'
      exact hnr rb x crb rs hR hx hx'
    · exact keyOf_nonAux t x k s (hname.symm.trans haux)
  · exact (hfm rb x crb rs cv mI rP rules hR hx hold).mono hfind

/-- **The unit step of a checked record that is no block of recursors keeps the family
recursors' companions**: a member of a block of recursors that is a constant address of the
record would make the record that block. -/
theorem unitStep_keepsFamilyRecsModeled {X : Ix.Kernel.Env .anon → Prop}
    {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env} {lim : Option Nat}
    {seeds : List _root_.Address} {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    (hroles : (t.bound.toList.map (·.1)).Nodup)
    {A : _root_.Address} {c : Ixon.Constant} (hW : Walked Top Inner A)
    (hc : recordOf E₀ A = some c)
    (hnb : ∀ rs : Array Ixon.MutConst, c.info = .muts rs →
      ¬ ∀ m ∈ rs.toList, ∃ r, m = Ixon.MutConst.recr r)
    (h : UnitStep.{u} X t envT E₀ E lim A c) :
    UnitStep.{u} (fun env => X env ∧ FamilyRecsModeled t E₀ env) t envT E₀ E lim A c := by
  refine unitStep_keepsFamilyRecsModeled_of_apart hroles ?_ h
  intro rb x crb rs hR hx hxA
  obtain ⟨P, hP, hPp, hPo⟩ := hR.constAddr hx
  rcases walked_constAddr_cases hG hF hW hc hxA with ⟨h1, hs⟩ | ⟨-, P', hP', -, hPo'⟩
  · rw [h1, hc] at hP
    have hcP : c = P := Option.some.inj hP
    rw [hcP] at hs
    exact standalone_not_proj hs hPp
  · have hPP : P' = P := Option.some.inj (hP'.symm.trans hP)
    rw [hPP] at hPo'
    have hAr : A = rb := hPo'.symm.trans hPo
    rw [hAr] at hc
    have hcc : c = crb := Option.some.inj (hc.symm.trans hR.record)
    exact hnb rs (by rw [hcc]; exact hR.muts) hR.recrs

end IxVM.Refinement.Typing.TwinFamily
