import IxVMRefinement.Core.Registry
import IxVMRefinement.Core.Open
import IxVMRefinement.Core.RomBound
import IxVMRefinement.Core.Steps.Whnf
import IxVMRefinement.Obs.KernelInfer
import IxVMRefinement.Obs.KernelInferOnly
import IxVMRefinement.Subst.Inst
import IxVMRefinement.Nat.Basic

/-! # Inference: shared facts of the step lemmas

* **A loaded constant's head fields** (`CIRep.head`): every `KConstantInfo` IxVM loads holds the
  constant's level count first and its positional type second, whatever its kind.
* **The context list as a list** (`segEntries_getElem?`): the entry `i` of a segment of the ghost
  context ending at `d` is the opened variable `d - 1 - i` with its type.
* **A context lookup** (`lookup_lift`): `Lists::lookup(types, i)` followed by
  `expr_lift(_, i + 1, 0)` is the type of the opened variable `BVar i` stands for, at depth `d`
  (`types_lookup` and its infer-only twin). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)

set_option linter.unusedVariables false

/-- **A loaded constant's level count and type are its first two fields.** -/
theorem CIRep.head {κ : _root_.Address → KKey} {h : Heap F} {v : SourceValue F}
    {ci : Ix.Kernel.ConstantInfo .anon} (r : CIRep κ h v ci) :
    ∃ (cn : String) (nl ty : SourceValue F) (rest : List (SourceValue F)),
      v = .construct kciEnum cn (nl :: ty :: rest) ∧ ValRep κ h nl ty ci.toConstantVal := by
  cases r with
  | axio hv => exact ⟨_, _, _, _, rfl, hv⟩
  | opaq hv => exact ⟨_, _, _, _, rfl, hv⟩
  | defn hv _ => exact ⟨_, _, _, _, rfl, hv⟩
  | thm hv _ => exact ⟨_, _, _, _, rfl, hv⟩
  | quot hv _ => exact ⟨_, _, _, _, rfl, hv⟩
  | induct hv _ _ => exact ⟨_, _, _, _, rfl, hv⟩
  | ctor hv _ _ _ _ => exact ⟨_, _, _, _, rfl, hv⟩
  | recr hv _ _ _ _ _ _ _ _ _ => exact ⟨_, _, _, _, rfl, hv⟩

/-- The first field of a loaded constant is its level count. -/
theorem CIRep.nl_of_eq {κ : _root_.Address → KKey} {h : Heap F} {v : SourceValue F}
    {ci : Ix.Kernel.ConstantInfo .anon} (r : CIRep κ h v ci) {k : String}
    {x : SourceValue F} {xs : List (SourceValue F)}
    (hv : v = .construct "KernelTypes::KConstantInfo" k (x :: xs)) :
    x = .field (ci.toConstantVal.levelParams.length : F) := by
  obtain ⟨cn, nl, ty, rest, he, hval⟩ := r.head
  rw [he] at hv
  injection hv with _ _ hl
  injection hl with hx
  rw [← hx]
  exact hval.1

/-- The second field of a loaded constant is its type, at positional level parameters. -/
theorem CIRep.ty_of_eq {κ : _root_.Address → KKey} {h : Heap F} {v : SourceValue F}
    {ci : Ix.Kernel.ConstantInfo .anon} (r : CIRep κ h v ci) {k : String}
    {w x : SourceValue F} {xs : List (SourceValue F)}
    (hv : v = .construct "KernelTypes::KConstantInfo" k (w :: x :: xs)) :
    TmC κ h (posOf ci.toConstantVal.levelParams ci.toConstantVal.type) x := by
  obtain ⟨cn, nl, ty, rest, he, hval⟩ := r.head
  rw [he] at hv
  injection hv with _ _ hl
  injection hl with _ hl'
  injection hl' with hx
  rw [← hx]
  exact hval.2.2.2

/-- **The entry `i` of a segment** of the ghost context ending at `d`. -/
theorem segEntries_getElem? {Γ : Nat → KExpr} {d n i : Nat} {x : Nat × KExpr}
    (hx : (segEntries Γ d n)[i]? = some x) : i < n ∧ x = (d - 1 - i, Γ (d - 1 - i)) := by
  obtain ⟨hlt, hxe⟩ := List.getElem?_eq_some_iff.mp hx
  have hlt' : i < n := by simpa [segEntries] using hlt
  refine ⟨hlt', ?_⟩
  rw [← hxe]
  simp [segEntries]

/-- **A context lookup, lifted to the current depth**: the shared body of `types_lookup` and
`io_types_lookup`. The entry is represented at the depth its variable was opened at, `d - 1 - i`;
lifting it by `i + 1` opened variables reads it at `d`. -/
theorem lookup_lift (c : Ctx) {calls cs12 cs34 : List (Call F)} (ih : IH c calls)
    {types v1 v38 r : SourceValue F} {i : F} {h m2 h' : Heap F} (good : Good c calls)
    (ev14 : ObsFn W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [types, .field i] h v1 m2
      cs12)
    (op60 : evalBinOp .add (.field i : SourceValue F) (.field 1) = .ok v38)
    (ev36 : ObsFn W "KernelSubst::expr_lift" [v1, v38, .field 0] m2 r h' cs34)
    (hc : calls = (⟨Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>», [types, .field i], h⟩ :
      Call F) :: (cs12 ++ ((⟨"KernelSubst::expr_lift", [v1, v38, .field 0], m2⟩ : Call F) :: cs34))) :
    ∀ d Γ, c.types Γ h d types →
      ZMod.val i < d ∧ c.tm d Γ h' (Γ (fvIdx d 0 (ZMod.val i))) r := by
  intro d Γ htypes
  subst hc
  obtain ⟨n, hnd, hl⟩ := htypes.1.toRepList
  obtain ⟨⟨x, hx, hxr⟩, hm⟩ := SubstAux.klookup ev14 hl
  rw [hm] at ev36
  obtain ⟨hlt, rfl⟩ := segEntries_getElem? hx
  have hb : n < 549755813888 := by
    have := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>», [types, .field i], h⟩)
      (by simp) (by simp) hl
    simpa [segEntries] using this
  have hv38 : v38 = .field (i + 1) := NatAux.add_ok op60
  subst hv38
  have hi1 : ZMod.val (i + 1) = ZMod.val i + 1 := NatAux.val_add_one (by omega)
  have hE : c.tmk (d - 1 - ZMod.val i) Γ (ZMod.val (0 : F)) h (Γ (d - 1 - ZMod.val i)) v1 := by
    rw [ZMod.val_zero]; exact hxr
  have hlift := ih.get (.subst .expr_lift) (by lt_calls) ev36 v1 (i + 1) 0 rfl
    (good.sub fun x hx => by simp [hx]) (by rw [hi1]; omega) 0 (ZMod.val i + 1)
    (by rw [hi1]; omega) (d - 1 - ZMod.val i) Γ (Γ (d - 1 - ZMod.val i)) hE
  refine ⟨by omega, ?_⟩
  have e1 : d - 1 - ZMod.val i + (ZMod.val i + 1) = d := by omega
  have e2 : fvIdx d 0 (ZMod.val i) = d - 1 - ZMod.val i := by simp [fvIdx]
  rw [e2]
  rw [e1, ZMod.val_zero] at hlift
  exact hlift

/-- `pw_eq`'s answer `1` is equality of the data. -/
theorem zeroness_eq_of_one {la lb : KLevel}
    (hr : (Value.field (1 : F) : SourceValue F) =
      .field (if la.zeronessOf = lb.zeronessOf then 1 else 0)) :
    la.zeronessOf = lb.zeronessOf := by
  by_contra hne
  rw [ite_eq_right hne] at hr
  exact field_one_ne_zero hr

end IxVM.Refinement.Core
