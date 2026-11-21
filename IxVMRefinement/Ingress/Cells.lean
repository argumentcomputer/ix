import IxVMRefinement.Ingress.Convert
import IxVMRefinement.Core.Rekey

/-! # The cells of a converted record are its used references

A `Const` or `Proj` cell of a heap term that `Convert` built from a record expression carries the
address at one of the expression's reference indices (`IxVM.Consistency.exprRefIdxs`), at a
reference index of a shared subexpression, or a recursion address of the record. The types of
`let` binders are subterms of the heap term and are covered: `exprRefIdxs` reads them.
The structure of a `Proj` cell is at a reference index, never a recursion address
(`RawConvExpr.projIn_used`): the permission to project is asked at used references only.

`RawDefnValRep.ciAddrIn_used` lifts this to a converted definition: every cell address of its
type and value is at a reference index the record uses (`IxVM.Consistency.usedRefIdxs`), or is
a recursion address. -/

namespace IxVM.Refinement.Ingress

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.Core (AddrIn ProjIn CIAddrIn)
open IxVM.Consistency (exprRefIdxs usedRefIdxs)

/-- Two cells at one heap address are the same constructor with the same arguments. -/
private theorem cell_args {h : Heap F} {addr : Nat} {e n n' : String}
    {xs ys : List (SourceValue F)}
    (c₁ : h[addr]? = some (.construct e n xs)) (c₂ : h[addr]? = some (.construct e n' ys)) :
    n = n' ∧ xs = ys := by
  have := Option.some.inj (c₁.symm.trans c₂)
  injection this with _ hn hx
  exact ⟨hn, hx⟩

/-- **The address of a cell is used**: it is at a reference index of the expression or of a
shared subexpression, or it is a recursion address. -/
def CellUsed (refs recurAddrs : List _root_.Address) (sharing : List Ixon.Expr) (e : Ixon.Expr)
    (x : _root_.Address) : Prop :=
  (∃ i, (i ∈ exprRefIdxs e ∨ ∃ s ∈ sharing, i ∈ exprRefIdxs s) ∧ refs[i]? = some x) ∨
    x ∈ recurAddrs

private theorem CellUsed.lift {refs recurAddrs : List _root_.Address} {sharing : List Ixon.Expr}
    {e e' : Ixon.Expr} {x : _root_.Address}
    (hsub : ∀ i, i ∈ exprRefIdxs e → i ∈ exprRefIdxs e')
    (h : CellUsed refs recurAddrs sharing e x) : CellUsed refs recurAddrs sharing e' x := by
  rcases h with ⟨i, hi | hs, hr⟩ | hr
  · exact Or.inl ⟨i, Or.inl (hsub i hi), hr⟩
  · exact Or.inl ⟨i, Or.inr hs, hr⟩
  · exact Or.inr hr

/-- **The address is at a reference the expression uses**: at a reference index of the
expression or of a shared subexpression. A used cell that is no recursion address. -/
abbrev RefUsed (refs : List _root_.Address) (sharing : List Ixon.Expr) (e : Ixon.Expr)
    (x : _root_.Address) : Prop :=
  ∃ i, (i ∈ exprRefIdxs e ∨ ∃ s ∈ sharing, i ∈ exprRefIdxs s) ∧ refs[i]? = some x

/-- An address at a used reference is the address of a used cell. -/
theorem RefUsed.cellUsed {refs recurAddrs : List _root_.Address} {sharing : List Ixon.Expr}
    {e : Ixon.Expr} {x : _root_.Address} (h : RefUsed refs sharing e x) :
    CellUsed refs recurAddrs sharing e x :=
  Or.inl h

private theorem RefUsed.lift {refs : List _root_.Address} {sharing : List Ixon.Expr}
    {e e' : Ixon.Expr} {x : _root_.Address}
    (hsub : ∀ i, i ∈ exprRefIdxs e → i ∈ exprRefIdxs e')
    (h : RefUsed refs sharing e x) : RefUsed refs sharing e' x := by
  obtain ⟨i, hi | hs, hr⟩ := h
  · exact ⟨i, Or.inl (hsub i hi), hr⟩
  · exact ⟨i, Or.inr hs, hr⟩

/-- **The cells of a converted expression are used references.** -/
theorem RawConvExpr.addrIn_used {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)} {h : Heap F}
    {bound : Nat} {e : Ixon.Expr} {p : SourceValue F}
    (raw : RawConvExpr refs recurAddrs univs sharing blobs h bound e p) :
    ∀ a : Bytes.Address, AddrIn h p a →
      CellUsed refs recurAddrs sharing e (Core.ixAddr a) := by
  induction raw with
  | var hidx cell =>
    intro a hin
    cases hin with
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | sort huIdx hu rl cell =>
    intro a hin
    cases hin with
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | @ref bound addr rIdx uIdxs x d ap lsp ls hrIdx href hd ra hls rls cell =>
    intro a hin
    cases hin with
    | const c' ra' =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at ra'
      have hda : d = a := Bytes.repAddressRef_inj U32.Goldilocks.compatible ra ra'
      refine Or.inl ⟨rIdx.toNat, Or.inl (List.mem_singleton.mpr rfl), ?_⟩
      rw [← hda, hd]
      exact href
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | @recur bound addr rIdx uIdxs x d ap lsp ls hrIdx hrec hd ra hls rls cell =>
    intro a hin
    cases hin with
    | const c' ra' =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at ra'
      have hda : d = a := Bytes.repAddressRef_inj U32.Goldilocks.compatible ra ra'
      refine Or.inr ?_
      rw [← hda, hd]
      exact List.mem_of_getElem? hrec
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | @prj bound addr tIdx fIdx inner x d ap ip htIdx hfIdx href hd ra rin cell ih =>
    intro a hin
    cases hin with
    | projHead c' ra' =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at ra'
      have hda : d = a := Bytes.repAddressRef_inj U32.Goldilocks.compatible ra ra'
      refine Or.inl ⟨tIdx.toNat, Or.inl (List.mem_cons.mpr (Or.inl rfl)), ?_⟩
      rw [← hda, hd]
      exact href
    | projArg c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with _ hrest
      injection hrest with _ hrest'
      injection hrest' with h3 _
      rw [← h3] at sub
      exact (ih a sub).lift fun i hi => List.mem_cons_of_mem _ hi
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | str hbIdx href hmem rbs hs cell =>
    intro a hin
    cases hin with
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | nat hbIdx href hmem hcanon rlimbs hlast hval cell =>
    intro a hin
    cases hin with
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | app rf ra cell ihf iha =>
    intro a hin
    cases hin with
    | appFn c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at sub
      exact (ihf a sub).lift fun i hi => List.mem_append_left _ hi
    | appArg c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with _ hrest
      injection hrest with h2 _
      rw [← h2] at sub
      exact (iha a sub).lift fun i hi => List.mem_append_right _ hi
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | lam rl rt rb cell iht ihb =>
    intro a hin
    cases hin with
    | lamTy c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at sub
      exact (iht a sub).lift fun i hi => List.mem_append_left _ hi
    | lamBody c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with _ hrest
      injection hrest with h2 _
      rw [← h2] at sub
      exact (ihb a sub).lift fun i hi => List.mem_append_right _ hi
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | all rl rt rb cell iht ihb =>
    intro a hin
    cases hin with
    | forallTy c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at sub
      exact (iht a sub).lift fun i hi => List.mem_append_left _ hi
    | forallBody c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with _ hrest
      injection hrest with h2 _
      rw [← h2] at sub
      exact (ihb a sub).lift fun i hi => List.mem_append_right _ hi
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | letE rt rv rb cell iht ihv ihb =>
    intro a hin
    cases hin with
    | letTy c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at sub
      exact (iht a sub).lift fun i hi =>
        List.mem_append_left _ (List.mem_append_left _ hi)
    | letVal c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with _ hrest
      injection hrest with h2 _
      rw [← h2] at sub
      exact (ihv a sub).lift fun i hi =>
        List.mem_append_left _ (List.mem_append_right _ hi)
    | letBody c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with _ hrest
      injection hrest with _ hrest'
      injection hrest' with h3 _
      rw [← h3] at sub
      exact (ihb a sub).lift fun i hi => List.mem_append_right _ hi
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | @share bound idx s kp hidx hsh rs ih =>
    intro a hin
    rcases ih a hin with ⟨i, hi | hs, hr⟩ | hr
    · exact Or.inl ⟨i, Or.inr ⟨s, List.mem_of_getElem? hsh, hi⟩, hr⟩
    · exact Or.inl ⟨i, Or.inr hs, hr⟩
    · exact Or.inr hr

/-- **The structure of a `Proj` cell of a converted expression is at a used reference**, never
at a recursion address: conversion writes at a `Proj` node the address at the node's reference
index. -/
theorem RawConvExpr.projIn_used {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)} {h : Heap F}
    {bound : Nat} {e : Ixon.Expr} {p : SourceValue F}
    (raw : RawConvExpr refs recurAddrs univs sharing blobs h bound e p) :
    ∀ a : Bytes.Address, ProjIn h p a → RefUsed refs sharing e (Core.ixAddr a) := by
  induction raw with
  | var hidx cell =>
    intro a hin
    cases hin with
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | sort huIdx hu rl cell =>
    intro a hin
    cases hin with
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | @ref bound addr rIdx uIdxs x d ap lsp ls hrIdx href hd ra hls rls cell =>
    intro a hin
    cases hin with
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | @recur bound addr rIdx uIdxs x d ap lsp ls hrIdx hrec hd ra hls rls cell =>
    intro a hin
    cases hin with
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | @prj bound addr tIdx fIdx inner x d ap ip htIdx hfIdx href hd ra rin cell ih =>
    intro a hin
    cases hin with
    | head c' ra' =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at ra'
      have hda : d = a := Bytes.repAddressRef_inj U32.Goldilocks.compatible ra ra'
      refine ⟨tIdx.toNat, Or.inl (List.mem_cons.mpr (Or.inl rfl)), ?_⟩
      rw [← hda, hd]
      exact href
    | projArg c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with _ hrest
      injection hrest with _ hrest'
      injection hrest' with h3 _
      rw [← h3] at sub
      exact (ih a sub).lift fun i hi => List.mem_cons_of_mem _ hi
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | str hbIdx href hmem rbs hs cell =>
    intro a hin
    cases hin with
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | nat hbIdx href hmem hcanon rlimbs hlast hval cell =>
    intro a hin
    cases hin with
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | app rf ra cell ihf iha =>
    intro a hin
    cases hin with
    | appFn c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at sub
      exact (ihf a sub).lift fun i hi => List.mem_append_left _ hi
    | appArg c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with _ hrest
      injection hrest with h2 _
      rw [← h2] at sub
      exact (iha a sub).lift fun i hi => List.mem_append_right _ hi
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | lam rl rt rb cell iht ihb =>
    intro a hin
    cases hin with
    | lamTy c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at sub
      exact (iht a sub).lift fun i hi => List.mem_append_left _ hi
    | lamBody c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with _ hrest
      injection hrest with h2 _
      rw [← h2] at sub
      exact (ihb a sub).lift fun i hi => List.mem_append_right _ hi
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | all rl rt rb cell iht ihb =>
    intro a hin
    cases hin with
    | forallTy c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at sub
      exact (iht a sub).lift fun i hi => List.mem_append_left _ hi
    | forallBody c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with _ hrest
      injection hrest with h2 _
      rw [← h2] at sub
      exact (ihb a sub).lift fun i hi => List.mem_append_right _ hi
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | letE rt rv rb cell iht ihv ihb =>
    intro a hin
    cases hin with
    | letTy c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at sub
      exact (iht a sub).lift fun i hi =>
        List.mem_append_left _ (List.mem_append_left _ hi)
    | letVal c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with _ hrest
      injection hrest with h2 _
      rw [← h2] at sub
      exact (ihv a sub).lift fun i hi =>
        List.mem_append_left _ (List.mem_append_right _ hi)
    | letBody c' sub =>
      obtain ⟨-, hargs⟩ := cell_args cell c'
      injection hargs with _ hrest
      injection hrest with _ hrest'
      injection hrest' with h3 _
      rw [← h3] at sub
      exact (ihb a sub).lift fun i hi => List.mem_append_right _ hi
    | _ => rename_i c' _; exact absurd (cell_args cell c').1 (by decide)
  | @share bound idx s kp hidx hsh rs ih =>
    intro a hin
    obtain ⟨i, hi | hs, hr⟩ := ih a hin
    · exact ⟨i, Or.inr ⟨s, List.mem_of_getElem? hsh, hi⟩, hr⟩
    · exact ⟨i, Or.inr hs, hr⟩

/-- **A converted term under another keying**: one that agrees with the first on the references
the expression uses and on its recursion addresses, and that permits a projection at the
references the expression uses. -/
theorem RawConvExpr.tmC_rekey {κ₁ κ₂ : _root_.Address → Core.KKey}
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ} {sharing : List Ixon.Expr}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {bound : Nat} {e : Ixon.Expr}
    {p : SourceValue F} {X : Core.KExpr}
    (raw : RawConvExpr refs recurAddrs univs sharing blobs h bound e p)
    (rep : Core.TmC κ₁ h X p)
    (agree : ∀ x, CellUsed refs recurAddrs sharing e x → κ₂ x = κ₁ x)
    (perm : ∀ x, RefUsed refs sharing e x → Core.ProjPermitted κ₂ x) : Core.TmC κ₂ h X p :=
  Core.TmC.rekey rep (fun a m => agree _ (raw.addrIn_used a m))
    (fun a m _ => perm _ (raw.projIn_used a m))

/-- The cells of a loaded definition are those of its type and its value. -/
private theorem ciAddrIn_defn_inv {h : Heap F} {nl ty val sf hint : SourceValue F}
    {a : Bytes.Address}
    (hin : CIAddrIn h (.construct Core.kciEnum "Defn" [nl, ty, val, sf, hint]) a) :
    AddrIn h ty a ∨ AddrIn h val a := by
  generalize hv : (Value.construct Core.kciEnum "Defn" [nl, ty, val, sf, hint] :
    SourceValue F) = v at hin
  cases hin with
  | defnTy m =>
    injection hv with _ _ hargs
    injection hargs with _ hrest
    injection hrest with h2 _
    rw [h2]
    exact Or.inl m
  | defnVal m =>
    injection hv with _ _ hargs
    injection hargs with _ hrest
    injection hrest with _ hrest'
    injection hrest' with h3 _
    rw [h3]
    exact Or.inr m
  | _ => injection hv with _ htag _; exact absurd htag (by decide)

/-- The cells of a loaded opaque constant are those of its type. -/
private theorem ciAddrIn_opaq_inv {h : Heap F} {nl ty val u : SourceValue F} {a : Bytes.Address}
    (hin : CIAddrIn h (.construct Core.kciEnum "Opaque" [nl, ty, val, u]) a) : AddrIn h ty a := by
  generalize hv : (Value.construct Core.kciEnum "Opaque" [nl, ty, val, u] :
    SourceValue F) = v at hin
  cases hin with
  | opaq m =>
    injection hv with _ _ hargs
    injection hargs with _ hrest
    injection hrest with h2 _
    rw [h2]
    exact m
  | _ => injection hv with _ htag _; exact absurd htag (by decide)

/-- The cells of a loaded theorem are those of its type and its value. -/
private theorem ciAddrIn_thm_inv {h : Heap F} {nl ty val : SourceValue F} {a : Bytes.Address}
    (hin : CIAddrIn h (.construct Core.kciEnum "Thm" [nl, ty, val]) a) :
    AddrIn h ty a ∨ AddrIn h val a := by
  generalize hv : (Value.construct Core.kciEnum "Thm" [nl, ty, val] : SourceValue F) = v at hin
  cases hin with
  | thmTy m =>
    injection hv with _ _ hargs
    injection hargs with _ hrest
    injection hrest with h2 _
    rw [h2]
    exact Or.inl m
  | thmVal m =>
    injection hv with _ _ hargs
    injection hargs with _ hrest
    injection hrest with _ hrest'
    injection hrest' with h3 _
    rw [h3]
    exact Or.inr m
  | _ => injection hv with _ htag _; exact absurd htag (by decide)

/-- **The cells of a converted definition are references the record uses.** For the record `c`
whose payload is the definition `d`: every cell address of the converted type and value is at a
used reference index of `c`, or is a recursion address. -/
theorem RawDefnValRep.ciAddrIn_used {c : Ixon.Constant} {d : Ixon.Definition}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)} {h : Heap F}
    {v : SourceValue F} (hinfo : c.info = .defn d)
    (raw : RawDefnValRep c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h d v)
    {a : Bytes.Address} (hin : CIAddrIn h v a) :
    (∃ i ∈ usedRefIdxs c, c.refs.toList[i]? = some (Core.ixAddr a)) ∨
      Core.ixAddr a ∈ recurAddrs := by
  obtain ⟨-, tyPtr, valPtr, hint, rfl, hty, hval⟩ := raw
  have used : ∀ {e : Ixon.Expr},
      (∀ i, i ∈ exprRefIdxs e → i ∈ exprRefIdxs d.typ ++ exprRefIdxs d.value) →
      CellUsed c.refs.toList recurAddrs c.sharing.toList e (Core.ixAddr a) →
      (∃ i ∈ usedRefIdxs c, c.refs.toList[i]? = some (Core.ixAddr a)) ∨
        Core.ixAddr a ∈ recurAddrs := by
    intro e hsub hu
    rcases hu with ⟨i, hi | ⟨s, hs, his⟩, hr⟩ | hr
    · refine Or.inl ⟨i, ?_, hr⟩
      unfold usedRefIdxs
      rw [hinfo]
      exact List.mem_append_right _ (hsub i hi)
    · refine Or.inl ⟨i, ?_, hr⟩
      unfold usedRefIdxs
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
    · exact Or.inr hr
  have tyUsed := fun (m : AddrIn h tyPtr a) =>
    used (fun i hi => List.mem_append_left _ hi) (hty.addrIn_used a m)
  have valUsed := fun (m : AddrIn h valPtr a) =>
    used (fun i hi => List.mem_append_right _ hi) (hval.addrIn_used a m)
  cases hk : d.kind with
  | defn =>
    simp only [defnValShape, hk] at hin
    rcases ciAddrIn_defn_inv hin with m | m
    · exact tyUsed m
    · exact valUsed m
  | opaq =>
    simp only [defnValShape, hk] at hin
    exact tyUsed (ciAddrIn_opaq_inv hin)
  | thm =>
    simp only [defnValShape, hk] at hin
    rcases ciAddrIn_thm_inv hin with m | m
    · exact tyUsed m
    · exact valUsed m

end IxVM.Refinement.Ingress
