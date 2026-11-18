import IxVMRefinement.Decl.Modeled
import IxVMRefinement.FamilyAlias.Check

/-! # The family check's renaming is its advice's renaming

`KernelModeled::check_family` renames every member of the block and of its family record to its
model with `KernelModeled::rename` over the address lists `src` (the types, the constructors, the
recursors) and `dst` (their models, read from the payload in the same order). The facts of the check
(`Decl.FamilyAlias.FamilyCheckFacts`) state the renaming as the advice's (`FamilyAdvice.ren`, the
`aliasMap` of the members' keys paired with their models' keys). This module joins the two, at the
table's keying:

* `renameKeyList_eq_aliasMap`: the key renaming of two parallel lists (`Decl.renameKeyList`, which
  `rename_addr` refines) is the `aliasMap` of the lists zipped; the first pair at a key decides in
  both;
* `renameMap_aliasMap`: the check's two lists represent that `aliasMap` (`Decl.RenameMap` at the
  table's keying on both sides);
* `rename_aliasMap`, `rename_aliasMap_consts`: a term the check renames, represented exactly at the
  table's keying, is represented after the renaming as its `renameAll` by the `aliasMap`, and as its
  `renameConsts` where no projection names a member. -/

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open IxVM (F)
open IxVM.Refinement.Decl.FamilyAlias (aliasMap)

/-- **The key renaming of two parallel lists is the `aliasMap` of the lists zipped.** -/
theorem renameKeyList_eq_aliasMap (k : KKey) :
    ∀ (ks ds : List KKey), Decl.renameKeyList k ks ds = aliasMap (ks.zip ds) k
  | [], _ => rfl
  | _ :: _, [] => rfl
  | s :: ss, d :: ds => by
    simp only [Decl.renameKeyList, List.zip_cons_cons, aliasMap, renameKeyList_eq_aliasMap k ss ds]

/-- **The check's address lists represent the `aliasMap` of their keys**, at the table's keying on
both sides. -/
theorem renameMap_aliasMap {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {srcAs dstAs : List Bytes.Address} {src dst : SourceValue F} {h : Heap F}
    (hlen : srcAs.length = dstAs.length)
    (hsrc : RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs src)
    (hdst : RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst) :
    Decl.RenameMap (Core.keyOf t) (Core.keyOf t)
      (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b)))) h src dst := by
  have hm := Decl.renameMap_of_lists hwf hlen hsrc hdst
  simp only [renameKeyList_eq_aliasMap] at hm
  exact hm

/-- **A term the check renames, after the renaming**: represented exactly at the table's keying
before, it is represented exactly after as its `renameAll` by the `aliasMap` of the lists. -/
theorem rename_aliasMap {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {srcAs dstAs : List Bytes.Address} {Γ₁ Γ₂ : Nat → KExpr}
    {e src dst r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {k : Nat} {E : KExpr}
    (ev : ObsFn W "KernelModeled::rename" [e, src, dst] h r h' cs)
    (hlen : srcAs.length = dstAs.length)
    (hsrc : RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs src)
    (hdst : RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst)
    (he : TmExact (Core.keyOf t) 0 Γ₁ h k E e) :
    TmExact (Core.keyOf t) 0 Γ₂ h' k
      (Decl.renameAll (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b)))) E) r :=
  Decl.rename_exact ev he (renameMap_aliasMap hwf hlen hsrc hdst)

/-- **The same, as `renameConsts`**, where no projection of the term names a member (the
circuit's `rename` renames a projection's structure, IxC's `renameConsts` does not). -/
theorem rename_aliasMap_consts {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {srcAs dstAs : List Bytes.Address} {Γ₁ Γ₂ : Nat → KExpr}
    {e src dst r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {k : Nat} {E : KExpr}
    (ev : ObsFn W "KernelModeled::rename" [e, src, dst] h r h' cs)
    (hlen : srcAs.length = dstAs.length)
    (hsrc : RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs src)
    (hdst : RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst)
    (he : TmExact (Core.keyOf t) 0 Γ₁ h k E e)
    (hnp : Decl.NoProjIn (srcAs.map fun b => Core.keyOf t (ixAddr b)) E = true) :
    TmExact (Core.keyOf t) 0 Γ₂ h' k
      (E.renameConsts (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b))))) r := by
  have hout : ∀ k', (srcAs.map fun b => Core.keyOf t (ixAddr b)).contains k' = false →
      aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b))) k' = k' := by
    intro k' hk
    rw [← renameKeyList_eq_aliasMap]
    exact Decl.renameKeyList_out k' _ _ hk
  rw [← Decl.renameAll_eq_renameConsts_of_noProjIn hout hnp]
  exact rename_aliasMap hwf ev hlen hsrc hdst he

end IxVM.Refinement.Typing.FamilyAlias
