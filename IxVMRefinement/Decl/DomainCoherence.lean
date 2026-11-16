import IxVMRefinement.Decl.DomainTransport
import IxVMRefinement.Decl.NativeDomainMotive

/-! # Checked domain origins and a syntactic transport specialization

The checked-sort law has no substitution or frame-transport assumption. A dependent proof
must produce the origin of each checked domain using its real old/new frame evidence.
The separate syntactic invariant constructs that transport for metadata-insensitive fragments;
its arbitrary-replacement closure is a sufficient specialization, not an all-domain contract.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model

/-- An origin property fixes zero-ness only when consumed by actual typing and sort evidence. -/
structure DomainSortLaw (env : Env .anon) (P : Expr .anon → Prop) (datum : PropWhen) : Prop where
  checked : ∀ {depth e inferred level}, P e → Rules.Infer env .full depth e inferred →
    Rules.Red env depth inferred (.sort level) → Level.zeronessOf level = datum

/-- The two checked domains may have different frames. Their origins must already have been
produced; this theorem does not prescribe an arbitrary substitution between those frames. -/
theorem DomainSortLaw.checked_pair {env : Env .anon} {P : Expr .anon → Prop} {datum : PropWhen}
    (law : DomainSortLaw env P datum) {depth : Nat} {original final originalType finalType : Expr .anon}
    {originalSort finalSort : Level}
    (originalOrigin : P original) (finalOrigin : P final)
    (originalTyped : Rules.Infer env .full depth original originalType)
    (originalSorted : Rules.Red env depth originalType (.sort originalSort))
    (finalTyped : Rules.Infer env .full depth final finalType)
    (finalSorted : Rules.Red env depth finalType (.sort finalSort)) :
    Level.zeronessOf originalSort = datum ∧ Level.zeronessOf finalSort = datum ∧
      Level.zeronessOf originalSort = Level.zeronessOf finalSort ∧
      (∀ leftDomain leftBody leftMeta rightDomain rightBody rightMeta,
        original = .forallE leftDomain leftBody leftMeta →
        final = .forallE rightDomain rightBody rightMeta → leftMeta.pw = rightMeta.pw) := by
  have originalZero := law.checked originalOrigin originalTyped originalSorted
  have finalZero := law.checked finalOrigin finalTyped finalSorted
  have equal := originalZero.trans finalZero.symm
  refine ⟨originalZero, finalZero, equal, ?_⟩
  intro leftDomain leftBody leftMeta rightDomain rightBody rightMeta leftShape rightShape
  have leftData := inferred_product_sort_metadata (by simpa only [leftShape] using originalTyped) originalSorted
  have rightData := inferred_product_sort_metadata (by simpa only [rightShape] using finalTyped) finalSorted
  exact leftData.trans (equal.trans rightData.symm)

/-- A sufficient syntax-only specialization. The actual evaluator is used for computational
closure; reannotation may change all metadata and earlier free-variable type annotations. -/
structure SyntacticDomainInvariant (env : Env .anon) (P : Expr .anon → Prop) (datum : PropWhen) : Prop
    extends DomainSortLaw env P datum where
  abstracts : ∀ e index cut, P e → P (e.abstract1 index cut)
  instantiates : ∀ e value cut, P e → P (e.instantiate1 value cut)
  annotates : ∀ {e out}, P e → IxVM.Consistency.Annotates out e → P out
  whnf_closed : ∀ {fuel depth e out}, P e → Ix.Kernel.whnf .verified env fuel depth e = .ok out → P out
  product_body : ∀ {domain body metadata}, P (.forallE domain body metadata) → P body
  product : ∀ domain body metadata, P body → P (.forallE domain body metadata)

/-- The actual normalizer preserves a produced syntactic invariant under each opened product. -/
theorem SyntacticDomainInvariant.normalized {env : Env .anon} {P : Expr .anon → Prop} {datum : PropWhen}
    (invariant : SyntacticDomainInvariant env P datum) {fuel steps depth : Nat} {T : Key .anon}
    {e out : Expr .anon} (origin : P e)
    (run : normPosDom (fueledOps .verified fuel) env T depth steps e = .ok out) : P out := by
  induction steps generalizing depth e out with
  | zero => cases run
  | succ steps ih =>
    simp only [normPosDom] at run
    split at run
    · obtain rfl := (Except.ok.inj run).symm
      exact origin
    · obtain ⟨head, reduced, rest⟩ := exceptBind_ok run
      change Ix.Kernel.whnf .verified env fuel depth e = .ok head at reduced
      have headOrigin := invariant.whnf_closed origin reduced
      split at rest
      · obtain rfl := (Except.ok.inj rest).symm
        exact headOrigin
      · cases head with
        | forallE domain body metadata =>
          dsimp only at rest
          split at rest
          · cases rest
          · obtain ⟨bodyOut, recursive, result⟩ := exceptBind_ok rest
            obtain rfl := (Except.ok.inj result).symm
            have bodyOrigin := invariant.instantiates body (.fvar depth domain) 0
              (invariant.product_body headOrigin)
            exact invariant.product _ _ _ (invariant.abstracts bodyOut depth 0 (ih bodyOrigin recursive))
        | _ =>
          obtain rfl := (Except.ok.inj rest).symm
          exact headOrigin

/-- The exact constructor rebuild supplies the second origin for the syntax-only specialization. -/
theorem SyntacticDomainInvariant.rebuilt_domain {env : Env .anon} {P : Expr .anon → Prop} {datum : PropWhen}
    (invariant : SyntacticDomainInvariant env P datum) {fuel nP nF slot : Nat} {T : Key .anon}
    {raw initial checked : ConstantVal .anon} {originalVars finalVars : List (Expr .anon)}
    {originalResidual finalResidual original final : Expr .anon}
    (normalized : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked)
    (originalOpen : openPisAtFvars (nP + nF) initial.type 0 = some (originalVars, originalResidual))
    (finalOpen : openPisAtFvars (nP + nF) checked.type 0 = some (finalVars, finalResidual))
    (originalAt : originalVars[nP + slot]? = some original) (finalAt : finalVars[nP + slot]? = some final)
    (origin : P original.fvarTypeD) : P final.fvarTypeD :=
  normCtorVal_domain_predicate invariant.abstracts invariant.instantiates invariant.annotates
    (fun h checked => invariant.normalized h checked) normalized originalOpen finalOpen originalAt finalAt origin

/-- One common two-check theorem consumes the constructed transport and derives sort/PW
agreement, retaining the executable inference and sort results at the actual paired domains. -/
theorem SyntacticDomainInvariant.checked_sorts {env : Env .anon} {P : Expr .anon → Prop} {datum : PropWhen}
    (invariant : SyntacticDomainInvariant env P datum) {fuel nP nF slot : Nat} {T : Key .anon}
    {raw initial checked : ConstantVal .anon} {originalVars finalVars : List (Expr .anon)}
    {originalResidual finalResidual original final : Expr .anon}
    (first : checkConstantVal (fueledOps .verified fuel) env raw = .ok initial)
    (normalized : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked)
    (originalOpen : openPisAtFvars (nP + nF) initial.type 0 = some (originalVars, originalResidual))
    (finalOpen : openPisAtFvars (nP + nF) checked.type 0 = some (finalVars, finalResidual))
    (originalAt : originalVars[nP + slot]? = some original) (finalAt : finalVars[nP + slot]? = some final)
    (origin : P original.fvarTypeD) :
    ∃ originalType originalSort finalType finalSort,
      inferTypeCore .verified env fuel (nP + slot) original.fvarTypeD = .ok originalType ∧
      ensureSortCore .verified env fuel (nP + slot) originalType = .ok originalSort ∧
      inferTypeCore .verified env fuel (nP + slot) final.fvarTypeD = .ok finalType ∧
      ensureSortCore .verified env fuel (nP + slot) finalType = .ok finalSort ∧
      Level.zeronessOf originalSort = datum ∧ Level.zeronessOf finalSort = datum ∧
      Level.zeronessOf originalSort = Level.zeronessOf finalSort ∧
      (∀ leftDomain leftBody leftMeta rightDomain rightBody rightMeta,
        original.fvarTypeD = .forallE leftDomain leftBody leftMeta →
        final.fvarTypeD = .forallE rightDomain rightBody rightMeta → leftMeta.pw = rightMeta.pw) := by
  have finalOrigin := invariant.rebuilt_domain normalized originalOpen finalOpen originalAt finalAt origin
  obtain ⟨rawFinal, lastCheck⟩ : ∃ rawFinal,
      checkConstantVal (fueledOps .verified fuel) env rawFinal = .ok checked := by
    obtain ⟨rebuilt, _, same | lastCheck⟩ := normCtorVal_rebuild_trace normalized
    · exact ⟨raw, by rw [same]; exact first⟩
    · exact ⟨{ raw with type := rebuilt }, lastCheck⟩
  obtain ⟨originalType, originalSort, originalInfer, originalSorted⟩ :=
    checked_type_domain_checks first originalOpen (nP + slot) original originalAt
  obtain ⟨finalType, finalSort, finalInfer, finalSorted⟩ :=
    checked_type_domain_checks lastCheck finalOpen (nP + slot) final finalAt
  exact ⟨originalType, originalSort, finalType, finalSort, originalInfer, originalSorted, finalInfer, finalSorted,
    invariant.toDomainSortLaw.checked_pair origin finalOrigin (Rules.inferTypeCore_bridge originalInfer)
      (Rules.whnf_bridge (ensureSortCore_inv originalSorted)) (Rules.inferTypeCore_bridge finalInfer)
      (Rules.whnf_bridge (ensureSortCore_inv finalSorted))⟩

end IxVM.Refinement.Decl
