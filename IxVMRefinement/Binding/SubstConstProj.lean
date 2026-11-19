import IxVMRefinement.Core.Rekey
import IxVMRefinement.Lib.Bytes
import IxVMRefinement.Obs.KernelSubst1

/-! # Projection heads inspected by constant substitution

`subst_const` tests the structure address of every projection reachable from its input pointer,
including children under binding and let nodes. The reading below works at any heap extending
its output, as required when inspecting the cells of a certificate after substitution.
-/

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core

/-- One step of a projection witness after loading its root cell. -/
private def ProjectingCell (H : Heap F) (b : Bytes.Address) : SourceValue F → Prop
  | .construct _ "Proj" [s, _, x] => Bytes.RepAddressRef addrTy H b s ∨ ProjIn H x b
  | .construct _ "App" [f, x] => ProjIn H f b ∨ ProjIn H x b
  | .construct _ "Lam" [t, x, _] | .construct _ "Forall" [t, x, _] => ProjIn H t b ∨ ProjIn H x b
  | .construct _ "Let" [t, x, y] => ProjIn H t b ∨ ProjIn H x b ∨ ProjIn H y b
  | _ => False

private theorem projectingCell_of_load {H : Heap F} {e node : SourceValue F} {b : Bytes.Address}
    (pr : ProjIn H e b) (ld : loadValue H e = .ok node) : ProjectingCell H b node := by
  cases pr with
  | head cell rep => rw [loadValue_enum_cell cell] at ld; cases ld; exact Or.inl rep
  | projArg cell sub => rw [loadValue_enum_cell cell] at ld; cases ld; exact Or.inr sub
  | appFn cell sub | lamTy cell sub | forallTy cell sub | letTy cell sub =>
    rw [loadValue_enum_cell cell] at ld; cases ld; exact Or.inl sub
  | appArg cell sub | lamBody cell sub | forallBody cell sub =>
    rw [loadValue_enum_cell cell] at ld; cases ld; exact Or.inr sub
  | letVal cell sub => rw [loadValue_enum_cell cell] at ld; cases ld; exact Or.inr (Or.inl sub)
  | letBody cell sub => rw [loadValue_enum_cell cell] at ld; cases ld; exact Or.inr (Or.inr sub)

private theorem noProjectionAtOther {H : Heap F} {e node : SourceValue F} {b : Bytes.Address}
    (ld : loadValue H e = .ok node)
    (app : ∀ xs : List (SourceValue F), xs.length = 2 → node ≠ .construct kexprEnum "App" xs)
    (lam : ∀ xs : List (SourceValue F), xs.length = 3 → node ≠ .construct kexprEnum "Lam" xs)
    (all : ∀ xs : List (SourceValue F), xs.length = 3 → node ≠ .construct kexprEnum "Forall" xs)
    (letE : ∀ xs : List (SourceValue F), xs.length = 3 → node ≠ .construct kexprEnum "Let" xs)
    (proj : ∀ xs : List (SourceValue F), xs.length = 3 → node ≠ .construct kexprEnum "Proj" xs) :
    ¬ ProjIn H e b := by
  intro pr
  cases pr with
  | head cell _ | projArg cell _ =>
    exact proj _ rfl (Except.ok.inj (ld.symm.trans (loadValue_enum_cell cell)))
  | appFn cell _ | appArg cell _ =>
    exact app _ rfl (Except.ok.inj (ld.symm.trans (loadValue_enum_cell cell)))
  | lamTy cell _ | lamBody cell _ =>
    exact lam _ rfl (Except.ok.inj (ld.symm.trans (loadValue_enum_cell cell)))
  | forallTy cell _ | forallBody cell _ =>
    exact all _ rfl (Except.ok.inj (ld.symm.trans (loadValue_enum_cell cell)))
  | letTy cell _ | letVal cell _ | letBody cell _ =>
    exact letE _ rfl (Except.ok.inj (ld.symm.trans (loadValue_enum_cell cell)))

/-- An address represented in a later heap was already represented when its pointer loaded. -/
private theorem address_before_load {h H : Heap F} {p val : SourceValue F} {b : Bytes.Address}
    (ext : Heap.Extends h H) (ld : loadValue h p = .ok val)
    (rep : Bytes.RepAddressRef addrTy H b p) : Bytes.RepAddressRef addrTy h b p := by
  obtain ⟨i, cell, rfl, hH, hr⟩ := rep
  cases hh : h[i]? with
  | none => simp [loadValue, hh] at ld
  | some u =>
    have hu := Option.some.inj ((ext.getElem?_eq hh).symm.trans hH)
    subst u
    exact ⟨i, cell, rfl, hh, hr⟩

private theorem address_eq_zero_separates {h h' H : Heap F} {cs : List (Call F)}
    {s a q : SourceValue F} {b : Bytes.Address} (ext : Heap.Extends h H)
    (ev : ObsFn W "Bytes::address_eq" [s, a] h q h' cs) (zero : q = .field 0)
    (rs : Bytes.RepAddressRef addrTy H b s) (ra : Bytes.RepAddressRef addrTy H b a) : False := by
  have loads : ∃ x y, loadValue h s = .ok x ∧ loadValue h a = .ok y := by
    match Obs.«Bytes::address_eq».obs ev with
    | .n0 (ld11 := ls) (ld23 := la) .. | .other (ld11 := ls) (ld23 := la) .. =>
      exact ⟨_, _, ls, la⟩
  obtain ⟨_, _, ls, la⟩ := loads
  have eq := (Lib.address_eq_spec ev (address_before_load ext ls rs) (address_before_load ext la ra)).1
  rw [ite_eq_left (rfl : b = b)] at eq
  exact zero_ne_one (Value.field.inj (zero.symm.trans eq))

/-- **A successful `subst_const` path excludes its operation address from the input's projection
heads.** The input pointer and both address representations can be inspected at any extension
of the path's output heap. -/
theorem subst_const_path_noProj {e a v r : SourceValue F} {h h' H : Heap F} {cs : List (Call F)}
    {b : Bytes.Address} (path : Obs.«KernelSubst::subst_const».Path e a v h r h' cs)
    (ext : Heap.Extends h' H) (ra : Bytes.RepAddressRef addrTy H b a) : ¬ ProjIn H e b := by
  intro pr
  have atLoad {m : Heap F} {node : SourceValue F} (hm : Heap.Extends h m)
      (hmH : Heap.Extends m H) (ld : loadValue h e = .ok node) :=
    projectingCell_of_load pr ((hm.trans hmH).loadValue_eq ld)
  match path with
  | .Const_n1_Nil (ld12 := ld) (ev44 := eq) (he86 := hh) .. =>
    subst hh
    exact atLoad eq.heap_extends ext ld
  | .Const_n1_Cons (heq132 := z) .. => exact zero_ne_one (Value.field.inj z)
  | .Const_other (ld12 := ld) (ev44 := eq) (he144 := hh) .. =>
    subst hh
    exact atLoad eq.heap_extends ext ld
  | .App (ld12 := ld) (hm166 := hh) (ev184 := first) (ev220 := second) (hc245 := hc) .. =>
    subst hh
    have endH := (Heap.Extends.snoc _ _).trans ext
    have middle := second.heap_extends.trans endH
    have sub := atLoad first.heap_extends middle ld
    change ProjIn H _ b ∨ ProjIn H _ b at sub
    rcases sub with sub | sub
    · exact subst_const_path_noProj (Obs.«KernelSubst::subst_const».obs first) middle ra sub
    · exact subst_const_path_noProj (Obs.«KernelSubst::subst_const».obs second) endH ra sub
  | .Lam (ld12 := ld) (hm271 := hh) (ev290 := first) (ev326 := second) (hc358 := hc) .. =>
    subst hh
    have endH := (Heap.Extends.snoc _ _).trans ext
    have middle := second.heap_extends.trans endH
    have sub := atLoad first.heap_extends middle ld
    change ProjIn H _ b ∨ ProjIn H _ b at sub
    rcases sub with sub | sub
    · exact subst_const_path_noProj (Obs.«KernelSubst::subst_const».obs first) middle ra sub
    · exact subst_const_path_noProj (Obs.«KernelSubst::subst_const».obs second) endH ra sub
  | .Forall (ld12 := ld) (hm384 := hh) (ev403 := first) (ev439 := second) (hc471 := hc) .. =>
    subst hh
    have endH := (Heap.Extends.snoc _ _).trans ext
    have middle := second.heap_extends.trans endH
    have sub := atLoad first.heap_extends middle ld
    change ProjIn H _ b ∨ ProjIn H _ b at sub
    rcases sub with sub | sub
    · exact subst_const_path_noProj (Obs.«KernelSubst::subst_const».obs first) middle ra sub
    · exact subst_const_path_noProj (Obs.«KernelSubst::subst_const».obs second) endH ra sub
  | .Let (ld12 := ld) (hm497 := hh) (ev516 := first) (ev552 := second) (ev588 := third)
      (hc613 := hc) .. =>
    subst hh
    have endH := (Heap.Extends.snoc _ _).trans ext
    have secondH := third.heap_extends.trans endH
    have firstH := second.heap_extends.trans secondH
    have sub := atLoad first.heap_extends firstH ld
    change ProjIn H _ b ∨ ProjIn H _ b ∨ ProjIn H _ b at sub
    rcases sub with sub | sub | sub
    · exact subst_const_path_noProj (Obs.«KernelSubst::subst_const».obs first) firstH ra sub
    · exact subst_const_path_noProj (Obs.«KernelSubst::subst_const».obs second) secondH ra sub
    · exact subst_const_path_noProj (Obs.«KernelSubst::subst_const».obs third) endH ra sub
  | .Proj (ld12 := ld) (ev_fcagpdzw := eq) (heq_fqyhtvgf := zero) (hm639 := hh)
      (ev672 := child) (hc697 := hc) .. =>
    subst hh
    have endH := (Heap.Extends.snoc _ _).trans ext
    have compareH := child.heap_extends.trans endH
    have branches := atLoad eq.heap_extends compareH ld
    change Bytes.RepAddressRef addrTy H b _ ∨ ProjIn H _ b at branches
    rcases branches with rs | sub
    · exact address_eq_zero_separates (eq.heap_extends.trans compareH) eq zero rs ra
    · exact subst_const_path_noProj (Obs.«KernelSubst::subst_const».obs child) endH ra sub
  | .other (ld12 := ld) (hne246 := app) (hne359 := lam) (hne472 := all) (hne614 := letE)
      (hne698 := proj) (he704 := hh) .. =>
    subst hh
    exact noProjectionAtOther (ext.loadValue_eq ld) app lam all letE proj pr
termination_by cs.length
decreasing_by
  all_goals
    rw [hc]
    simp only [List.length_cons, List.length_append]
    omega

/-- The certificate consumer observes the substitution and knows the operation's address before
it starts. Every projection reachable through its input pointer at the output heap is unequal. -/
theorem subst_const_proj_ne {e a v r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {b x : Bytes.Address} (ev : ObsFn W "KernelSubst::subst_const" [e, a, v] h r h' cs)
    (ra : Bytes.RepAddressRef addrTy h b a) (pr : ProjIn h' e x) : x ≠ b := by
  rintro rfl
  exact subst_const_path_noProj (Obs.«KernelSubst::subst_const».obs ev) (Heap.Extends.refl _)
    (Bytes.repAddressRef_heapMono₂ addrTy ev.heap_extends ra) pr

end IxVM.Refinement.Binding
