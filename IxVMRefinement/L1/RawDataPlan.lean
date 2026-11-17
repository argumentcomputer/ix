import IxVMRefinement.L1.RawDataRead
import IxVMRefinement.L1.CanonicalRawAnnotation

/-! # Canonical raw origins recovered from actual heap data and binder plans

The actual raw reading and serialized binder plan determine the complete raw AST. Reader
closure and universe coverage are not assumed; the physical exact representation already
supplies the raw expression used by runtime classifier operations.
-/

namespace IxVM.Refinement.L1

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open Ix.Kernel (Expr)

/-- Existing metadata is overwritten by raw annotation, including inside let cells. -/
theorem applyRawBinderTrace_erase_input (metadata : KLevel → Ix.Kernel.BinderMeta)
    (e : KExpr) : ∀ levels,
    applyRawBinderTrace metadata e.eraseMeta levels = applyRawBinderTrace metadata e levels := by
  induction e with
  | bvar | sort | const | lit => intro levels; rfl
  | fvar i ty ih => intro levels; simp only [Expr.eraseMeta, applyRawBinderTrace, ih]
  | app f a ihf iha => intro levels; simp only [Expr.eraseMeta, applyRawBinderTrace, ihf, iha]
  | lam dom body _ ihd ihb | forallE dom body _ ihd ihb =>
    intro levels
    cases levels <;> simp only [Expr.eraseMeta, applyRawBinderTrace, ihd, ihb]
  | letE type value body _ iht ihv ihb =>
    intro levels
    simp only [Expr.eraseMeta, applyRawBinderTrace, iht, ihv, ihb]
  | proj key index inner ih => intro levels; simp only [Expr.eraseMeta, applyRawBinderTrace, ih]

/-- The physical binder plan reconstructs the entire exact raw expression from erased data. -/
theorem raw_exact_plan {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F}
    (rep : Decl.RawTmExact κ 0 Γ h k R E p) :
    ∀ (plan : List KLevel), HeapBinderLevels h p plan → ∀ tail,
      applyRawBinderTrace bmeta R.eraseMeta (plan ++ tail) = some (R, tail) := by
  induction rep with
  | bvarLocal cell _ _ | sort cell _ | const cell _ _ | litNat cell _ _ | litStr cell _ _ =>
    intro plan levels tail
    have empty := HeapBinderLevels.leaf_inv (by simp) cell levels
    cases empty
    rfl
  | bvarFree _ _ _ impossible => omega
  | app cell _ _ func arg =>
    intro plan levels tail
    obtain ⟨funcPlan, argPlan, rfl, funcLevels, argLevels⟩ := HeapBinderLevels.app_inv cell levels
    simp [Expr.eraseMeta, applyRawBinderTrace, List.append_assoc,
      func funcPlan funcLevels (argPlan ++ tail), arg argPlan argLevels tail]
  | lam cell _ _ level dom body =>
    intro plan levels tail
    obtain ⟨domPlan, bodyPlan, rfl, domLevels, bodyLevels⟩ := HeapBinderLevels.lam_inv cell level levels
    simp [Expr.eraseMeta, applyRawBinderTrace, List.append_assoc,
      dom domPlan domLevels (bodyPlan ++ tail), body bodyPlan bodyLevels tail]
  | forallE cell _ _ level dom body =>
    intro plan levels tail
    obtain ⟨domPlan, bodyPlan, rfl, domLevels, bodyLevels⟩ := HeapBinderLevels.forall_inv cell level levels
    simp [Expr.eraseMeta, applyRawBinderTrace, List.append_assoc,
      dom domPlan domLevels (bodyPlan ++ tail), body bodyPlan bodyLevels tail]
  | letE cell _ _ _ type value body =>
    intro plan levels tail
    obtain ⟨typePlan, valuePlan, bodyPlan, rfl, typeLevels, valueLevels, bodyLevels⟩ :=
      HeapBinderLevels.let_inv cell levels
    simp [Expr.eraseMeta, applyRawBinderTrace, List.append_assoc,
      type typePlan typeLevels (valuePlan ++ (bodyPlan ++ tail)),
      value valuePlan valueLevels (bodyPlan ++ tail), body bodyPlan bodyLevels tail]
  | proj cell _ _ inner =>
    intro plan levels tail
    have innerLevels := HeapBinderLevels.proj_inv cell levels
    simp [Expr.eraseMeta, applyRawBinderTrace, inner plan innerLevels tail]

/-- Positional level parameters leave raw binder metadata unchanged. -/
theorem invPosLevel_range (n : Nat) (u : KLevel) : invPosLevel (List.range n) u = u := by
  induction u with
  | zero => rfl
  | succ _ ih => simp only [invPosLevel, ih]
  | max _ _ left right | imax _ _ left right => simp only [invPosLevel, left, right]
  | param index => simp [invPosLevel]

/-- Actual raw conversion and binder plans identify the exact runtime raw expression with the
canonical serialized-root answer, without reader-closure or parameter-coverage assumptions. -/
theorem RawConvExpr.canonical_raw_exact {κ : _root_.Address → KKey}
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (keyed : ∀ a key, cx.keyAt a = .ok key → key = κ a)
    (selfKeyed : ∀ i a m key, recurAddrs[i]? = some a → self i = some m → m = .ok key → key = κ a)
    (blobAgreement : ∀ a bytes, (a, bytes) ∈ blobs → cx.blob a = some bytes)
    {h : Heap F} {e : Ixon.Expr} {p : SourceValue F} {reader : KExpr}
    (converted : RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h 4294967295 e p)
    {tree : BinderTreeData} {root : F} {plan : List KLevel}
    (built : BinderTreeBuilt (binderLeavesData src.binders.toList) tree)
    (planned : binderRootPlan tree src.sharing.toList root e = some plan)
    (levels : HeapBinderLevels h p plan)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read e = .ok reader)
    {Γ : Nat → KExpr} {k : Nat} {R E : KExpr}
    (physical : Decl.RawTmExact κ 0 Γ h k R E p) (n : Nat) :
    canonicalRawAnnotation src (List.range n) root e reader = some R ∧
      R.eraseMeta = reader.eraseMeta := by
  have readerData := converted.memberReader_rawData keyed selfKeyed blobAgreement read
  have same := (rawData_of_exact physical).det readerData
  have trace := raw_exact_plan physical plan levels []
  simp only [List.append_nil] at trace
  rw [same, applyRawBinderTrace_erase_input] at trace
  refine ⟨?_, same⟩
  unfold canonicalRawAnnotation
  rw [canonicalRawTree_of_built built, planned]
  have metadata : (fun level => bmeta (invPosLevel (List.range n) level)) = bmeta := by
    funext level
    rw [invPosLevel_range]
  rw [metadata]
  change (applyRawBinderTrace bmeta reader plan).bind (fun result => some result.1) = some R
  rw [trace]
  rfl

end IxVM.Refinement.L1
