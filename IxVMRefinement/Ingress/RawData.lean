import IxVMRefinement.Ingress.ConvertExpr
import IxVMRefinement.Core.RawDet
import IxC.Kernel.Model.GuardClassifierErase

/-! # Scope-free physical expression data

This relation retains raw let syntax while ignoring binder metadata. It admits conversion's
56-bit universe parameters and does not require a typing context, bound-variable closure,
resolved semantic names or projection permission. It is a reader-data relation only.
-/

namespace IxVM.Refinement.Ingress

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open Ix.Kernel (Expr)

/-- Exact typed universe syntax also has the weaker raw conversion representation. -/
theorem rawLevel_of_exact {h : Heap F} {u : KLevel} {p : SourceValue F}
    (rep : RepKLevel h u p) : RawKLevel h u p := by
  induction rep with
  | zero cell => exact .zero cell
  | succ cell _ ih => exact .succ cell ih
  | max cell _ _ left right => exact .max cell left right
  | imax cell _ _ left right => exact .imax cell left right
  | param bound cell => exact .param (by omega) cell

theorem rawLevels_of_exact {h : Heap F} {us : List KLevel} {p : SourceValue F}
    (rep : RepKLevelList h us p) : RawKLevelList h us p := by
  unfold RawKLevelList
  rw [Core.klevelListEnum_eq]
  induction rep with
  | nil cell => exact .nil cell
  | cons cell level _ tail => exact .cons cell (rawLevel_of_exact level) tail

/-- Physical raw syntax with metadata erased and no semantic licensing assumptions. -/
inductive RawDataExpr (κ : _root_.Address → KKey) (h : Heap F) : KExpr → SourceValue F → Prop where
  | bvar {addr : Nat} {i : F}
      (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field i])) :
      RawDataExpr κ h (.bvar i.val) (.ptr (.enum kexprEnum) addr)
  | sort {addr : Nat} {p : SourceValue F} {u : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Srt" [p])) (level : RawKLevel h u p) :
      RawDataExpr κ h (.sort u) (.ptr (.enum kexprEnum) addr)
  | const {addr : Nat} {ap params : SourceValue F} {a : Bytes.Address} {us : List KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Const" [ap, params]))
      (address : Bytes.RepAddressRef addrTy h a ap) (levels : RawKLevelList h us params) :
      RawDataExpr κ h (.const (κ (ixAddr a)) us) (.ptr (.enum kexprEnum) addr)
  | app {addr : Nat} {fp ap : SourceValue F} {f a : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "App" [fp, ap]))
      (func : RawDataExpr κ h f fp) (arg : RawDataExpr κ h a ap) :
      RawDataExpr κ h (.app f a) (.ptr (.enum kexprEnum) addr)
  | lam {addr : Nat} {tp bp lp : SourceValue F} {T B : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "Lam" [tp, bp, lp]))
      (dom : RawDataExpr κ h T tp) (body : RawDataExpr κ h B bp) :
      RawDataExpr κ h (.lam T B default) (.ptr (.enum kexprEnum) addr)
  | forallE {addr : Nat} {tp bp lp : SourceValue F} {T B : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "Forall" [tp, bp, lp]))
      (dom : RawDataExpr κ h T tp) (body : RawDataExpr κ h B bp) :
      RawDataExpr κ h (.forallE T B default) (.ptr (.enum kexprEnum) addr)
  | letE {addr : Nat} {tp vp bp : SourceValue F} {T V B : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "Let" [tp, vp, bp]))
      (type : RawDataExpr κ h T tp) (value : RawDataExpr κ h V vp) (body : RawDataExpr κ h B bp) :
      RawDataExpr κ h (.letE T V B default) (.ptr (.enum kexprEnum) addr)
  | litNat {addr : Nat} {lp : SourceValue F} {limbs : List UInt64}
      (cell : h[addr]? = some (.construct kexprEnum "Lit" [.construct klitEnum "Nat" [lp]]))
      (represented : RepList limbListEnum RepU64 h limbs lp) :
      RawDataExpr κ h (.lit (.natVal (limbsVal limbs))) (.ptr (.enum kexprEnum) addr)
  | litStr {addr : Nat} {bp : SourceValue F} {bytes : List UInt8} {s : String}
      (cell : h[addr]? = some (.construct kexprEnum "Lit" [.construct klitEnum "Str" [bp]]))
      (represented : Bytes.RepByteStream byteListEnum h bytes bp) (string : StrBytes s bytes) :
      RawDataExpr κ h (.lit (.strVal s)) (.ptr (.enum kexprEnum) addr)
  | proj {addr : Nat} {ap ep : SourceValue F} {a : Bytes.Address} {i : F} {E : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "Proj" [ap, .field i, ep]))
      (address : Bytes.RepAddressRef addrTy h a ap) (inner : RawDataExpr κ h E ep) :
      RawDataExpr κ h (.proj (κ (ixAddr a)) i.val E) (.ptr (.enum kexprEnum) addr)

/-- The retained exact physical representation projects to the scope-free reader data. -/
theorem rawData_of_exact {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F}
    (rep : Decl.RawTmExact κ 0 Γ h k R E p) : RawDataExpr κ h R.eraseMeta p := by
  induction rep with
  | bvarLocal cell _ _ => exact .bvar cell
  | bvarFree _ _ _ impossible => omega
  | sort cell level => exact .sort cell (rawLevel_of_exact level)
  | const cell address levels => exact .const cell address (rawLevels_of_exact levels)
  | app cell _ _ func arg => exact .app cell func arg
  | lam cell _ _ _ dom body => exact .lam cell dom body
  | forallE cell _ _ _ dom body => exact .forallE cell dom body
  | letE cell _ _ _ type value body => exact .letE cell type value body
  | litNat cell represented _ => exact .litNat cell represented
  | litStr cell represented string => exact .litStr cell represented string
  | proj cell address _ inner => exact .proj cell address inner

end IxVM.Refinement.Ingress
