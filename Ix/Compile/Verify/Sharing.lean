import Ix.Compile.Verify.Catalog
import Ix.Sharing

/-!
# Proof-visible production sharing rewrite

The production rewrite replaces selected subterms by `share` leaves and
otherwise reconstructs the expression recursively. This module proves that
the rewrite cannot lengthen any encoded spine and therefore preserves the
expression codec's public wire domain.
-/

namespace Ix.Compile.Verify

local instance : LawfulBEq ByteArray where
  eq_of_beq {left right} h := by
    cases left
    cases right
    exact congrArg ByteArray.mk (eq_of_beq h)
  rfl {bytes} := beq_self_eq_true bytes.data

local instance : LawfulBEq Address where
  eq_of_beq {left right} h := by
    cases left
    cases right
    exact congrArg Address.mk (eq_of_beq h)
  rfl {addr} := by
    cases addr
    exact beq_self_eq_true (α := ByteArray) _

local instance : LawfulHashable Address where
  hash_eq left right h := by rw [eq_of_beq h]

/-- Every representative stored by sharing analysis is in the expression
codec's public wire domain. -/
def SharingInfoMapWireWF
    (infoMap : Std.HashMap Address Ix.Sharing.SubtermInfo) : Prop :=
  ∀ ⦃hash info⦄, infoMap.get? hash = some info → info.expr.wireWF

theorem SharingInfoMapWireWF.insert
    {infoMap : Std.HashMap Address Ix.Sharing.SubtermInfo}
    (hmap : SharingInfoMapWireWF infoMap) {hash info}
    (hinfo : info.expr.wireWF) :
    SharingInfoMapWireWF (infoMap.insert hash info) := by
  intro queried found hfound
  change (infoMap.insert hash info)[queried]? = some found at hfound
  rw [Std.HashMap.getElem?_insert] at hfound
  split at hfound
  next =>
    have : found = info := (Option.some.inj hfound).symm
    subst found
    exact hinfo
  next => exact hmap hfound

/-- The wire-safety invariant carried by the sharing analyzer. -/
def AnalyzeStateWireWF (state : Ix.Sharing.AnalyzeState) : Prop :=
  SharingInfoMapWireWF state.infoMap

theorem recordAnalyzedNode_wireWF (expr : Ixon.Expr)
    (childHashes : Array Address) (state : Ix.Sharing.AnalyzeState)
    (hstate : AnalyzeStateWireWF state) (hexpr : expr.wireWF) :
    AnalyzeStateWireWF
      ((Ix.Sharing.recordAnalyzedNode expr childHashes).run state).2 := by
  simp [Ix.Sharing.recordAnalyzedNode, StateT.run_bind, StateT.run_get,
    StateT.run_set]
  split
  · exact hstate
  · exact hstate.insert hexpr

/-- Recursive Merkle analysis preserves wire-safe representatives. -/
theorem hashAndAnalyze_wireWF (expr : Ixon.Expr)
    (state : Ix.Sharing.AnalyzeState) (hstate : AnalyzeStateWireWF state)
    (hexpr : expr.wireWF) :
    AnalyzeStateWireWF ((Ix.Sharing.hashAndAnalyze expr).run state).2 := by
  induction expr generalizing state with
  | sort idx | var idx | ref idx refs | recur idx refs | str idx | nat idx | share idx =>
    simp [Ix.Sharing.hashAndAnalyze, StateT.run_bind, StateT.run_get]
    split
    · exact hstate
    · exact recordAnalyzedNode_wireWF _ _ state hstate hexpr
  | prj typeRefIdx fieldIdx value ih =>
    unfold Ix.Sharing.hashAndAnalyze
    simp
    split
    · exact hstate
    · simp [StateT.run_bind]
      apply recordAnalyzedNode_wireWF
      · exact ih _ hstate (by simpa [Ixon.Expr.wireWF] using hexpr)
      · exact hexpr
  | app fn arg ihfn iharg =>
    unfold Ix.Sharing.hashAndAnalyze
    simp
    split
    · exact hstate
    · simp [StateT.run_bind]
      apply recordAnalyzedNode_wireWF
      · apply iharg
        · apply ihfn
          · exact hstate
          · exact hexpr.1
        · exact hexpr.2.1
      · exact hexpr
  | lam uses ty body ihty ihbody =>
    unfold Ix.Sharing.hashAndAnalyze
    simp
    split
    · exact hstate
    · simp [StateT.run_bind]
      apply recordAnalyzedNode_wireWF
      · apply ihbody
        · apply ihty
          · exact hstate
          · exact hexpr.1
        · exact hexpr.2.1
      · exact hexpr
  | all uses owned ty body ihty ihbody =>
    unfold Ix.Sharing.hashAndAnalyze
    simp
    split
    · exact hstate
    · simp [StateT.run_bind]
      apply recordAnalyzedNode_wireWF
      · apply ihbody
        · apply ihty
          · exact hstate
          · exact hexpr.1
        · exact hexpr.2.1
      · exact hexpr
  | letE nonDep ty value body ihty ihvalue ihbody =>
    unfold Ix.Sharing.hashAndAnalyze
    simp
    split
    · exact hstate
    · simp [StateT.run_bind]
      apply recordAnalyzedNode_wireWF
      · apply ihbody
        · apply ihvalue
          · apply ihty
            · exact hstate
            · exact hexpr.1
          · exact hexpr.2.1
        · exact hexpr.2.2
      · exact hexpr

/-- Every member of an expression array is in the expression codec's public
wire domain. -/
def ExprArrayWireWF (exprs : Array Ixon.Expr) : Prop :=
  ∀ expr ∈ exprs, expr.wireWF

/-- A safe array lookup remains safe when it falls back to a separately safe
expression. -/
theorem ExprArrayWireWF.getElem?_getD {exprs : Array Ixon.Expr}
    (hexprs : ExprArrayWireWF exprs) (idx : Nat) {fallback : Ixon.Expr}
    (hfallback : fallback.wireWF) :
    (exprs[idx]?.getD fallback).wireWF := by
  by_cases hidx : idx < exprs.size
  · rw [Array.getElem?_eq_getElem hidx, Option.getD_some]
    exact hexprs _ (Array.getElem_mem hidx)
  · rw [Array.getElem?_eq_none (Nat.le_of_not_gt hidx), Option.getD_none]
    exact hfallback

theorem SharingInfoMapWireWF.empty :
    SharingInfoMapWireWF
      ({} : Std.HashMap Address Ix.Sharing.SubtermInfo) := by
  intro hash info hget
  simp at hget

theorem analyzeExprs_wireWF (exprs : Array Ixon.Expr)
    (state : Ix.Sharing.AnalyzeState) (hstate : AnalyzeStateWireWF state)
    (hexprs : ExprArrayWireWF exprs) :
    AnalyzeStateWireWF (Ix.Sharing.analyzeExprs exprs state) := by
  unfold Ix.Sharing.analyzeExprs
  apply Array.foldl_induction
    (motive := fun _ state => AnalyzeStateWireWF state)
  · exact hstate
  · intro i state hstate
    apply hashAndAnalyze_wireWF
    · exact hstate
    · exact hexprs _ (Array.getElem_mem i.isLt)

theorem addUsage_wireWF
    (infoMap : Std.HashMap Address Ix.Sharing.SubtermInfo)
    (hash : Address) (count : Nat) (hmap : SharingInfoMapWireWF infoMap) :
    SharingInfoMapWireWF (Ix.Sharing.addUsage infoMap hash count) := by
  unfold Ix.Sharing.addUsage
  split
  next info hget =>
    apply hmap.insert
    exact hmap (info := info) hget
  next => exact hmap

theorem countRootUsages_wireWF (exprs : Array Ixon.Expr)
    (ptrToHash : Std.HashMap USize Address)
    (infoMap : Std.HashMap Address Ix.Sharing.SubtermInfo)
    (hmap : SharingInfoMapWireWF infoMap) :
    SharingInfoMapWireWF
      (Ix.Sharing.countRootUsages exprs ptrToHash infoMap) := by
  unfold Ix.Sharing.countRootUsages
  apply Array.foldl_induction
    (motive := fun _ infoMap => SharingInfoMapWireWF infoMap)
  · exact hmap
  · intro i infoMap hmap
    split
    · exact addUsage_wireWF _ _ _ hmap
    · exact hmap

theorem propagateUsage_wireWF
    (infoMap : Std.HashMap Address Ix.Sharing.SubtermInfo)
    (hash : Address) (hmap : SharingInfoMapWireWF infoMap) :
    SharingInfoMapWireWF (Ix.Sharing.propagateUsage infoMap hash) := by
  unfold Ix.Sharing.propagateUsage
  split
  next info hget =>
    apply Array.foldl_induction
      (motive := fun _ infoMap => SharingInfoMapWireWF infoMap)
    · exact hmap
    · intro i infoMap hmap
      exact addUsage_wireWF _ _ _ hmap
  next => exact hmap

theorem propagateUsageCounts_wireWF (topoOrder : Array Address)
    (infoMap : Std.HashMap Address Ix.Sharing.SubtermInfo)
    (hmap : SharingInfoMapWireWF infoMap) :
    SharingInfoMapWireWF
      (Ix.Sharing.propagateUsageCounts topoOrder infoMap) := by
  unfold Ix.Sharing.propagateUsageCounts
  apply Array.foldl_induction
    (motive := fun _ infoMap => SharingInfoMapWireWF infoMap)
  · exact hmap
  · intro i infoMap hmap
    exact propagateUsage_wireWF _ _ hmap

/-- Both usage-counting phases preserve the representatives established by
the recursive analyzer. -/
theorem analyzeBlock_wireWF (exprs : Array Ixon.Expr)
    (hexprs : ExprArrayWireWF exprs) :
    SharingInfoMapWireWF (Ix.Sharing.analyzeBlock exprs).infoMap := by
  unfold Ix.Sharing.analyzeBlock
  apply propagateUsageCounts_wireWF
  apply countRootUsages_wireWF
  apply analyzeExprs_wireWF
  · exact SharingInfoMapWireWF.empty
  · exact hexprs

/-- Replacing selected subterms by sharing leaves cannot increase an
application, lambda, or forall spine exposed at the root. -/
theorem rewriteWithSharing_spineCounts_le
    (expr : Ixon.Expr) (hashToIdx : Std.HashMap Address Nat)
    (ptrToHash : Std.HashMap USize Address) :
    (Ix.Sharing.rewriteWithSharing expr hashToIdx ptrToHash).appCount ≤
        expr.appCount ∧
      (Ix.Sharing.rewriteWithSharing expr hashToIdx ptrToHash).lamCount ≤
        expr.lamCount ∧
      (Ix.Sharing.rewriteWithSharing expr hashToIdx ptrToHash).allCount ≤
        expr.allCount := by
  induction expr <;>
    rw [Ix.Sharing.rewriteWithSharing] <;>
    split <;>
    simp_all [Ixon.Expr.appCount, Ixon.Expr.lamCount, Ixon.Expr.allCount]

/-- Production sharing rewriting preserves every structural count condition
required by the expression serializer. -/
theorem rewriteWithSharing_wireWF
    (expr : Ixon.Expr) (hashToIdx : Std.HashMap Address Nat)
    (ptrToHash : Std.HashMap USize Address) (h : expr.wireWF) :
    (Ix.Sharing.rewriteWithSharing expr hashToIdx ptrToHash).wireWF := by
  induction expr with
  | sort | var | str | nat | share =>
    rw [Ix.Sharing.rewriteWithSharing]
    split <;> simp [Ixon.Expr.wireWF]
  | ref refIdx indices | recur refIdx indices =>
    rw [Ix.Sharing.rewriteWithSharing]
    split <;> simp_all [Ixon.Expr.wireWF]
  | prj typeRefIdx fieldIdx value ih =>
    rw [Ix.Sharing.rewriteWithSharing]
    split
    · simp [Ixon.Expr.wireWF]
    · simpa [Ixon.Expr.wireWF] using ih h
  | app fn arg ihfn iharg =>
    rw [Ix.Sharing.rewriteWithSharing]
    split
    · simp [Ixon.Expr.wireWF]
    · rcases h with ⟨hfn, harg, hcount⟩
      refine ⟨ihfn hfn, iharg harg, ?_⟩
      have hle := (rewriteWithSharing_spineCounts_le
        fn hashToIdx ptrToHash).1
      omega
  | lam uses ty body ihty ihbody =>
    rw [Ix.Sharing.rewriteWithSharing]
    split
    · simp [Ixon.Expr.wireWF]
    · rcases h with ⟨hty, hbody, hcount⟩
      refine ⟨ihty hty, ihbody hbody, ?_⟩
      have hle := (rewriteWithSharing_spineCounts_le
        body hashToIdx ptrToHash).2.1
      omega
  | all uses owned ty body ihty ihbody =>
    rw [Ix.Sharing.rewriteWithSharing]
    split
    · simp [Ixon.Expr.wireWF]
    · rcases h with ⟨hty, hbody, hcount⟩
      refine ⟨ihty hty, ihbody hbody, ?_⟩
      have hle := (rewriteWithSharing_spineCounts_le
        body hashToIdx ptrToHash).2.2
      omega
  | letE nonDep ty value body ihty ihvalue ihbody =>
    rw [Ix.Sharing.rewriteWithSharing]
    split
    · simp [Ixon.Expr.wireWF]
    · rcases h with ⟨hty, hvalue, hbody⟩
      exact ⟨ihty hty, ihvalue hvalue, ihbody hbody⟩

/-- Every sharing entry accumulated so far is wire-safe. -/
def SharingBuildStateWireWF (state : Ix.Sharing.SharingBuildState) : Prop :=
  ExprArrayWireWF state.sharingVec

theorem SharingBuildStateWireWF.empty :
    SharingBuildStateWireWF ({} : Ix.Sharing.SharingBuildState) := by
  intro expr hmem
  simp at hmem

theorem addSharingEntry_wireWF
    (infoMap : Std.HashMap Address Ix.Sharing.SubtermInfo)
    (ptrToHash : Std.HashMap USize Address)
    (state : Ix.Sharing.SharingBuildState) (hash : Address)
    (hmap : SharingInfoMapWireWF infoMap)
    (hstate : SharingBuildStateWireWF state) :
    SharingBuildStateWireWF
      (Ix.Sharing.addSharingEntry infoMap ptrToHash state hash) := by
  unfold Ix.Sharing.addSharingEntry
  split
  next info hget =>
    intro expr hmem
    rw [Array.mem_push] at hmem
    rcases hmem with hmem | rfl
    · exact hstate _ hmem
    · apply rewriteWithSharing_wireWF
      exact hmap hget
  next => exact hstate

theorem buildSharingEntries_wireWF (hashes : Array Address)
    (infoMap : Std.HashMap Address Ix.Sharing.SubtermInfo)
    (ptrToHash : Std.HashMap USize Address)
    (hmap : SharingInfoMapWireWF infoMap) :
    SharingBuildStateWireWF
      (Ix.Sharing.buildSharingEntries hashes infoMap ptrToHash) := by
  unfold Ix.Sharing.buildSharingEntries
  apply Array.foldl_induction
    (motive := fun _ state => SharingBuildStateWireWF state)
  · exact SharingBuildStateWireWF.empty
  · intro i state hstate
    exact addSharingEntry_wireWF _ _ _ _ hmap hstate

theorem rewriteExprs_wireWF (exprs : Array Ixon.Expr)
    (hashToIdx : Std.HashMap Address Nat)
    (ptrToHash : Std.HashMap USize Address)
    (hexprs : ExprArrayWireWF exprs) :
    ExprArrayWireWF
      (Ix.Sharing.rewriteExprs exprs hashToIdx ptrToHash) := by
  intro rewritten hmem
  unfold Ix.Sharing.rewriteExprs at hmem
  obtain ⟨expr, hexprMem, rfl⟩ := Array.mem_map.mp hmem
  apply rewriteWithSharing_wireWF
  exact hexprs _ hexprMem

/-- Nonempty sharing construction preserves the wire domain for both block
roots and every emitted sharing-table entry. -/
theorem buildSharingVec_wireWF (exprs : Array Ixon.Expr)
    (sharedHashes : Array Address)
    (infoMap : Std.HashMap Address Ix.Sharing.SubtermInfo)
    (ptrToHash : Std.HashMap USize Address)
    (hexprs : ExprArrayWireWF exprs)
    (hmap : SharingInfoMapWireWF infoMap) :
    ExprArrayWireWF
        (Ix.Sharing.buildSharingVec
          exprs sharedHashes infoMap ptrToHash).1 ∧
      ExprArrayWireWF
        (Ix.Sharing.buildSharingVec
          exprs sharedHashes infoMap ptrToHash).2 := by
  unfold Ix.Sharing.buildSharingVec
  dsimp only
  constructor
  · apply rewriteExprs_wireWF
    exact hexprs
  · exact buildSharingEntries_wireWF _ _ _ hmap

theorem ExprArrayWireWF.empty : ExprArrayWireWF #[] := by
  intro expr hmem
  simp at hmem

theorem finishSharing_wireWF (exprs : Array Ixon.Expr)
    (result : Ix.Sharing.AnalyzeResult) (sharedHashes : Array Address)
    (hexprs : ExprArrayWireWF exprs)
    (hmap : SharingInfoMapWireWF result.infoMap) :
    ExprArrayWireWF
        (Ix.Sharing.finishSharing exprs result sharedHashes).1 ∧
      ExprArrayWireWF
        (Ix.Sharing.finishSharing exprs result sharedHashes).2 := by
  unfold Ix.Sharing.finishSharing
  split
  · exact ⟨hexprs, ExprArrayWireWF.empty⟩
  · dsimp only
    split
    · exact buildSharingVec_wireWF _ _ _ _ hexprs hmap
    · exact ⟨hexprs, ExprArrayWireWF.empty⟩

/-- The production overflow fallback makes the sharing-table count lossless
for the constant codec, independently of the logical `Array` model. -/
theorem finishSharing_capacity (exprs : Array Ixon.Expr)
    (result : Ix.Sharing.AnalyzeResult) (sharedHashes : Array Address) :
    (Ix.Sharing.finishSharing exprs result sharedHashes).2.size <
      UInt64.size := by
  unfold Ix.Sharing.finishSharing
  split
  · change 0 < UInt64.size
    exact UInt64.toNat_lt 0
  · dsimp only
    split
    · assumption
    · change 0 < UInt64.size
      exact UInt64.toNat_lt 0

/-- The default, non-debug production entry point reduces to the
proof-visible sharing core. -/
theorem applySharing_eq_core (exprs : Array Ixon.Expr) :
    Ix.Sharing.applySharing exprs = Ix.Sharing.applySharingCore exprs := by
  rw [Ix.Sharing.applySharing]
  simp

theorem applySharingCore_wireWF (exprs : Array Ixon.Expr)
    (hexprs : ExprArrayWireWF exprs) :
    ExprArrayWireWF (Ix.Sharing.applySharingCore exprs).1 ∧
      ExprArrayWireWF (Ix.Sharing.applySharingCore exprs).2 := by
  unfold Ix.Sharing.applySharingCore
  exact finishSharing_wireWF _ _ _ hexprs
    (analyzeBlock_wireWF _ hexprs)

theorem applySharingCore_capacity (exprs : Array Ixon.Expr) :
    (Ix.Sharing.applySharingCore exprs).2.size < UInt64.size := by
  unfold Ix.Sharing.applySharingCore
  exact finishSharing_capacity _ _ _

/-- Production sharing preserves the expression wire domain for rewritten
roots and for the complete sharing vector, including the nonempty branch. -/
theorem applySharing_wireWF (exprs : Array Ixon.Expr)
    (hexprs : ExprArrayWireWF exprs) :
    ExprArrayWireWF (Ix.Sharing.applySharing exprs).1 ∧
      ExprArrayWireWF (Ix.Sharing.applySharing exprs).2 := by
  rw [applySharing_eq_core]
  exact applySharingCore_wireWF _ hexprs

/-- The sharing vector returned by the default production entry point always
has a losslessly serializable `UInt64` count. -/
theorem applySharing_capacity (exprs : Array Ixon.Expr) :
    (Ix.Sharing.applySharing exprs).2.size < UInt64.size := by
  rw [applySharing_eq_core]
  exact applySharingCore_capacity _

end Ix.Compile.Verify
