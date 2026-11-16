import Ix.Cert.RecordTransfer
import IxVMRefinement.Assembly.ReaderAnalysisSupport

/-! # Successful expression reading on its used reference support

Unused reference-table entries need not remain in a pruned reader. Sharing entries may
also fail without affecting an expression that never reads them. This transport therefore
preserves successful sharing-table answers and requires keys only on syntactic support.
-/

namespace IxVM.Refinement.Assembly.UsedRecordTransfer

open Ix.Kernel Ix.Kernel.Reader
open Ix.Cert.RecordTransfer (bind_ok TblLe tblFold mk'_eq)
open IxVM.Consistency (exprRefIdxs)
open ReaderAnalysis (RefsIn)

variable {md : Mode}

structure RefsLeOn (P : Nat → Prop) (src : Ixon.Constant) (cx cx' : Ctx md) : Prop where
  keyAt : ∀ i, P i → ∀ a, src.refs[i]? = some a →
    ∀ k, cx.keyAt a = .ok k → cx'.keyAt a = .ok k
  blob : ∀ a ∈ src.refs, ∀ bytes, cx.blob a = some bytes → cx'.blob a = some bytes

section Expr

variable {P : Nat → Prop} {cx cx' : Ctx md} {src : Ixon.Constant} (h : RefsLeOn P src cx cx')
    (univs : Array CLevel) (self : Nat → Option (ReadM (CName md)))

include h in
theorem keyAt_le (i : UInt64) (used : P i.toNat) {k : CName md}
    (read : ECx.keyAt ⟨cx, src, univs, self⟩ i = .ok k) :
    ECx.keyAt ⟨cx', src, univs, self⟩ i = .ok k := by
  unfold ECx.keyAt at read ⊢
  cases address : src.refs[i.toNat]? with
  | none => simp only [address] at read; cases read
  | some a =>
    simp only [address] at read ⊢
    exact h.keyAt _ used a address k read

include h in
theorem blobAt_le (i : UInt64) {bytes : ByteArray}
    (read : ECx.blobAt ⟨cx, src, univs, self⟩ i = .ok bytes) :
    ECx.blobAt ⟨cx', src, univs, self⟩ i = .ok bytes := by
  unfold ECx.blobAt at read ⊢
  cases address : src.refs[i.toNat]? with
  | none => simp only [address] at read; cases read
  | some a =>
    simp only [address] at read ⊢
    cases found : cx.blob a with
    | none => simp only [found] at read; cases read
    | some value =>
      simp only [found] at read
      rw [h.blob a (Array.mem_of_getElem? address) value found]
      exact read

include h in
theorem natAt_le (i : UInt64) {n : Nat}
    (read : ECx.natAt ⟨cx, src, univs, self⟩ i = .ok n) :
    ECx.natAt ⟨cx', src, univs, self⟩ i = .ok n := by
  unfold ECx.natAt at read ⊢
  cases found : ECx.blobAt ⟨cx, src, univs, self⟩ i with
  | error err => rw [found] at read; cases read
  | ok bytes =>
    rw [found] at read
    rw [blobAt_le h univs self i found]
    exact read

include h in
theorem convExpr_le {tbl tbl' : Array (ReadM (CExpr md))} (tables : TblLe tbl tbl') :
    ∀ (raw : Ixon.Expr), RefsIn P raw → ∀ value,
      convExpr ⟨cx, src, univs, self⟩ tbl raw = .ok value →
      convExpr ⟨cx', src, univs, self⟩ tbl' raw = .ok value := by
  intro raw
  induction raw with
  | var i => intro _ _ read; exact read
  | sort i => intro _ _ read; exact read
  | recur i us => intro _ _ read; exact read
  | ref i us =>
    intro support value read
    simp only [convExpr] at read ⊢
    obtain ⟨key, keyed, read⟩ := bind_ok read
    rw [keyAt_le h univs self i (support _ (by simp [exprRefIdxs])) keyed]
    exact read
  | prj i field raw ih =>
    intro support value read
    simp only [convExpr] at read ⊢
    obtain ⟨key, keyed, read⟩ := bind_ok read
    obtain ⟨inner, innerRead, read⟩ := bind_ok read
    have child : RefsIn P raw := fun j member => support j (by simp [exprRefIdxs, member])
    rw [keyAt_le h univs self i (support _ (by simp [exprRefIdxs])) keyed,
      ih child inner innerRead]
    exact read
  | str i =>
    intro _ value read
    simp only [convExpr] at read ⊢
    obtain ⟨bytes, found, read⟩ := bind_ok read
    rw [blobAt_le h univs self i found]
    exact read
  | nat i =>
    intro _ value read
    simp only [convExpr] at read ⊢
    obtain ⟨n, found, read⟩ := bind_ok read
    rw [natAt_le h univs self i found]
    exact read
  | app left right ihl ihr | lam left right ihl ihr | all left right ihl ihr =>
    intro support value read
    simp only [convExpr] at read ⊢
    obtain ⟨leftValue, leftRead, read⟩ := bind_ok read
    obtain ⟨rightValue, rightRead, read⟩ := bind_ok read
    have leftSupport : RefsIn P left := fun j member => support j (by simp [exprRefIdxs, member])
    have rightSupport : RefsIn P right := fun j member => support j (by simp [exprRefIdxs, member])
    rw [ihl leftSupport leftValue leftRead, ihr rightSupport rightValue rightRead]
    exact read
  | letE nonDep mode ty val body iht ihv ihb =>
    intro support value read
    simp only [convExpr] at read ⊢
    obtain ⟨typeValue, typeRead, read⟩ := bind_ok read
    obtain ⟨valValue, valRead, read⟩ := bind_ok read
    obtain ⟨bodyValue, bodyRead, read⟩ := bind_ok read
    have typeSupport : RefsIn P ty := fun j member => support j (by simp [exprRefIdxs, member])
    have valSupport : RefsIn P val := fun j member => support j (by simp [exprRefIdxs, member])
    have bodySupport : RefsIn P body := fun j member => support j (by simp [exprRefIdxs, member])
    rw [iht typeSupport typeValue typeRead, ihv valSupport valValue valRead,
      ihb bodySupport bodyValue bodyRead]
    exact read
  | share i =>
    intro _ value read
    simp only [convExpr] at read ⊢
    cases found : tbl[i.toNat]? with
    | none => simp only [found] at read; cases read
    | some entry =>
      simp only [found] at read
      subst read
      rw [tables.2 _ _ found]

end Expr

theorem tblFold_le {P : Nat → Prop} {cx cx' : Ctx md} {src : Ixon.Constant}
    (h : RefsLeOn P src cx cx') (univs : Array CLevel)
    (self : Nat → Option (ReadM (CName md))) :
    ∀ (entries : List Ixon.Expr), (∀ raw ∈ entries, RefsIn P raw) →
      ∀ {tbl tbl' : Array (ReadM (CExpr md))}, TblLe tbl tbl' →
        TblLe (tblFold ⟨cx, src, univs, self⟩ entries tbl)
          (tblFold ⟨cx', src, univs, self⟩ entries tbl')
  | [], _, _, _, tables => tables
  | raw :: rest, support, _, _, tables => by
    simp only [tblFold, List.foldl_cons]
    apply tblFold_le h univs self rest (fun e he => support e (List.mem_cons_of_mem _ he))
    exact tables.push (convExpr_le h univs self tables raw (support raw List.mem_cons_self))

/-- A successful member reading uses keys only at its actual syntactic support, including
the sharing table. Failed unused sharing entries impose no transport obligation. -/
theorem read_le {P : Nat → Prop} {cx cx' : Ctx md} {src : Ixon.Constant}
    (h : RefsLeOn P src cx cx') (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md)))
    (sharing : ∀ raw ∈ src.sharing.toList, RefsIn P raw)
    {raw : Ixon.Expr} (support : RefsIn P raw) {value : CExpr md}
    (read : (MemberReader.mk' cx src param self).read raw = .ok value) :
    (MemberReader.mk' cx' src param self).read raw = .ok value := by
  rw [mk'_eq] at read ⊢
  exact convExpr_le h _ self (tblFold_le h _ self _ sharing ⟨rfl, fun _ _ h => h⟩)
    raw support value read

end IxVM.Refinement.Assembly.UsedRecordTransfer
