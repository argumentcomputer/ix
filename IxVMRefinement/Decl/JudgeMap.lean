import IxC.Kernel.Semantics.DeclIndJ

/-! # Maps between judgement packages

A map changes only the judgement premises of an inductive declaration run. Its environments,
lookups, stored constants, rule lists, and structural checks remain the same.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics

structure JudgementsMap {md : Mode} (J K : Judgements md) : Prop where
  annot : ∀ {env : Env md} {d : Nat} {e e' : Expr md},
    J.annot env d e e' → K.annot env d e e'
  infer : ∀ {env : Env md} {d : Nat} {e t : Expr md},
    J.infer env d e t → K.infer env d e t
  defeq : ∀ {env : Env md} {d : Nat} {a b : Expr md},
    J.defeq env d a b → K.defeq env d a b
  sort : ∀ {env : Env md} {d : Nat} {t : Expr md} {u : Level},
    J.sort env d t u → K.sort env d t u
  isZero : ∀ {u : Level}, J.isZero u → K.isZero u

namespace JudgementsMap

variable {md : Mode} {J K : Judgements md} (M : JudgementsMap J K)

include M

theorem constantValRun {env : Env md} {cv : ConstantVal md} {ty : Expr md}
    (h : ConstantValRunJ J env cv ty) : ConstantValRunJ K env cv ty := by
  obtain ⟨hfresh, hres, hshape, hnd, hlbb, hnfv, hann, hdef, hresolve, stype, level, hi, hs⟩ := h
  exact ⟨hfresh, hres, hshape, hnd, hlbb, hnfv, M.annot hann,
    hdef, hresolve, stype, level, M.infer hi, M.sort hs⟩

theorem valueFrontRun {env : Env md} {cv : ConstantVal md} {value ty value' : Expr md}
    (h : ValueFrontRunJ J env cv value ty value') : ValueFrontRunJ K env cv value ty value' := by
  obtain ⟨hlbb, hnfv, hann, hdef, hresolve, vtype, hi, hd⟩ := h
  exact ⟨hlbb, hnfv, M.annot hann, hdef, hresolve, vtype, M.infer hi, M.defeq hd⟩

theorem defEqList {env : Env md} {d : Nat} :
    ∀ {as bs : List (Expr md)}, DefEqListJ J env d as bs → DefEqListJ K env d as bs
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h => ⟨M.defeq h.1, defEqList h.2⟩

theorem typedList {env : Env md} {d : Nat} :
    ∀ {as bs : List (Expr md)}, TypedListJ J env d as bs → TypedListJ K env d as bs
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, ⟨⟨ty, hi, hd⟩, rest⟩ =>
    ⟨⟨ty, M.infer hi, M.defeq hd⟩, typedList rest⟩

theorem iotaRuns {env : Env md} {d : Nat}
    {idxL idxR domL domR preL preR lamL lamR : List (Expr md)}
    {rhsS rhsApplied alphaS lhsS : Expr md}
    (h : IotaRunsJ J env d idxL idxR domL domR preL preR lamL lamR
      rhsS rhsApplied alphaS lhsS) :
    IotaRunsJ K env d idxL idxR domL domR preL preR lamL lamR
      rhsS rhsApplied alphaS lhsS := by
  obtain ⟨hidx, hdom, hpre, hlam, hrhs, ⟨tl, hil, hdl⟩, ⟨tr, hir, hdr⟩⟩ := h
  exact ⟨M.defEqList hidx, M.defEqList hdom, M.defEqList hpre, M.defEqList hlam,
    M.defeq hrhs, ⟨tl, M.infer hil, M.defeq hdl⟩, ⟨tr, M.infer hir, M.defeq hdr⟩⟩

end JudgementsMap
end IxVM.Refinement.Decl
