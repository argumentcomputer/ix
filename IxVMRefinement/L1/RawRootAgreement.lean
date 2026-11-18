import IxVMRefinement.L1.RawDataPlan
import IxVMRefinement.StatementRel.LoadedReads

/-! # Common raw annotations from actual hashed root conversions

The pairing result is scoped to two observations embedded in one collision-free root trace.
The conversion/plan inputs themselves remain reusable for comparisons across stores. It does
not assert that arbitrary future Good call lists belong to an earlier accepted trace.
-/

namespace IxVM.Refinement.L1

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency hiding keyOf
open IxVM.Refinement.Core

/-- Two actual byte strings hashed at one address agree when their common trace has no
collision. Neither string needs to have been present in the ambient stored environment. -/
theorem hashed_bytes_unique {env : Ixon.Env} {calls : List (Call F)}
    (noCollision : ¬ View.HashedCollision { env := env } [] calls)
    {address : _root_.Address} {first second : ByteArray}
    (firstHash : Hashed calls first) (firstAddress : Address.blake3Pure first = address)
    (secondHash : Hashed calls second) (secondAddress : Address.blake3Pure second = address) :
    first = second := by
  by_contra different
  exact noCollision (.inl ⟨address, first, second, .inr (.inr ⟨firstHash, firstAddress⟩),
    secondHash, Ne.symm different, secondAddress⟩)

private def traceBlobLookup : List (_root_.Address × ByteArray) → _root_.Address → Option ByteArray
  | [], _ => none
  | (address, bytes) :: rest, query =>
      if address == query then some bytes else traceBlobLookup rest query

private theorem traceBlobLookup_of_mem :
    ∀ entries : List (_root_.Address × ByteArray), ∀ {query : _root_.Address} {bytes : ByteArray},
      (∀ address first second, (address, first) ∈ entries → (address, second) ∈ entries → first = second) →
      (query, bytes) ∈ entries → traceBlobLookup entries query = some bytes
  | [], _, _, _, impossible => by cases impossible
  | (address, first) :: rest, query, bytes, consistent, member => by
    by_cases same : address = query
    · subst address
      have equal := consistent query first bytes (by simp) member
      simp [traceBlobLookup, equal]
    · have tail : (query, bytes) ∈ rest := by
        rcases List.mem_cons.mp member with equal | tail
        · exact (same (congrArg Prod.fst equal).symm).elim
        · exact tail
      have consistentTail : ∀ address first second,
          (address, first) ∈ rest → (address, second) ∈ rest → first = second :=
        fun address first second left right => consistent address first second
          (List.mem_cons_of_mem _ left) (List.mem_cons_of_mem _ right)
      simpa [traceBlobLookup, same] using traceBlobLookup_of_mem rest consistentTail tail

/-- Actual converted roots of the same serialized source/root, with their actual binder plans,
have one exact metadata-preserving raw expression. The blob reader is constructed from the
two observed hashed payload lists, whose overlaps agree by the shared collision escape. -/
theorem converted_roots_same_raw {t : Ix.Kernel.RoleTable} (checked : t.check = .ok ())
    {env : Ixon.Env} {rootCalls : List (Call F)}
    (noCollision : ¬ View.HashedCollision { env := env } [] rootCalls)
    {source : Ixon.Constant} {expression : Ixon.Expr} {root : F}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {recurAddrs : List _root_.Address}
    (selfComplete : ∀ i address, recurAddrs[i]? = some address →
      ∃ m key, self i = some m ∧ m = .ok key)
    (selfKeyed : ∀ i address m key, recurAddrs[i]? = some address →
      self i = some m → m = .ok key → key = keyOf t address)
    {blobs₁ blobs₂ : List (_root_.Address × ByteArray)}
    (hashed₁ : HashedPairs rootCalls blobs₁) (hashed₂ : HashedPairs rootCalls blobs₂)
    {h₁ h₂ : Heap F} {p₁ p₂ : SourceValue F}
    (first : RawConvExpr source.refs.toList recurAddrs source.univs.toList source.sharing.toList
      blobs₁ h₁ 4294967295 expression p₁)
    (second : RawConvExpr source.refs.toList recurAddrs source.univs.toList source.sharing.toList
      blobs₂ h₂ 4294967295 expression p₂)
    {tree₁ tree₂ : BinderTreeData} {plan₁ plan₂ : List KLevel}
    (built₁ : BinderTreeBuilt (binderLeavesData source.binders.toList) tree₁)
    (built₂ : BinderTreeBuilt (binderLeavesData source.binders.toList) tree₂)
    (planned₁ : binderRootPlan tree₁ source.sharing.toList root expression = some plan₁)
    (planned₂ : binderRootPlan tree₂ source.sharing.toList root expression = some plan₂)
    (levels₁ : HeapBinderLevels h₁ p₁ plan₁) (levels₂ : HeapBinderLevels h₂ p₂ plan₂)
    {Γ₁ Γ₂ : Nat → KExpr} {k₁ k₂ : Nat} {R₁ R₂ E₁ E₂ : KExpr}
    (physical₁ : Decl.RawTmExact (keyOf t) 0 Γ₁ h₁ k₁ R₁ E₁ p₁)
    (physical₂ : Decl.RawTmExact (keyOf t) 0 Γ₂ h₂ k₂ R₂ E₂ p₂) : R₁ = R₂ := by
  have allHashed : HashedPairs rootCalls (blobs₁ ++ blobs₂) := hashed₁.append hashed₂
  have consistent : ∀ address first second,
      (address, first) ∈ blobs₁ ++ blobs₂ → (address, second) ∈ blobs₁ ++ blobs₂ → first = second := by
    intro address first second left right
    exact hashed_bytes_unique noCollision (allHashed _ left).1 (allHashed _ left).2
      (allHashed _ right).1 (allHashed _ right).2
  let blob := traceBlobLookup (blobs₁ ++ blobs₂)
  have firstBlobs : ∀ address bytes, (address, bytes) ∈ blobs₁ → blob address = some bytes :=
    fun address bytes member => traceBlobLookup_of_mem _ consistent (List.mem_append_left _ member)
  have secondBlobs : ∀ address bytes, (address, bytes) ∈ blobs₂ → blob address = some bytes :=
    fun address bytes member => traceBlobLookup_of_mem _ consistent (List.mem_append_right _ member)
  obtain ⟨reader, read⟩ := LoadedReads.exprReader_read_ok (blob := blob) (param := id)
    checked first selfComplete firstBlobs
  have firstAnswer := first.canonical_raw_exact (LoadedReads.readCtx_keyAt_inv checked blob)
    selfKeyed firstBlobs built₁ planned₁ levels₁ read physical₁ 0
  have secondAnswer := second.canonical_raw_exact (LoadedReads.readCtx_keyAt_inv checked blob)
    selfKeyed secondBlobs built₂ planned₂ levels₂ read physical₂ 0
  exact Option.some.inj (firstAnswer.1.symm.trans secondAnswer.1)

end IxVM.Refinement.L1
