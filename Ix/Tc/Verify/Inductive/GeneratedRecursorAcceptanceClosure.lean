import Ix.Tc.Verify.Inductive.GeneratedRecursorAcceptance
import Ix.Tc.Verify.Check.ScopedActiveBlock
import Ix.Tc.Verify.RecursiveMethods.ScopedCallDomains

/-!
# Run-scoped generated-recursor acceptance closure

The exhaustive recursor comparison retains exactly one type DefEq call and
one RHS DefEq call per positional rule.  This module interprets those calls
through K2S's finite successor-layer method contract.  It does not require a
global DefEq oracle or place every expression in an unbounded call domain.
-/

namespace Ix.Tc

open GeneratedRecursorSemantics

namespace Methods.ScopedWFAtOn

/-- Restrict a scoped successor-layer DefEq theorem to the exact artifact
calls named by `GeneratedArtifactCallPlan`. -/
theorem artifactDefEqContract
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {calls : Methods.CallDomain}
    {methods : Methods .anon}
    (successor : Methods.ScopedWFAtOn model layer semantics support calls
      (Methods.next methods)) :
    ArtifactDefEqContract world.venv model.keys.uvars world.nameOf trProj
      calls methods
        (ScopedWhnfStateInv model layer semantics support []) := by
  intro state final generated stored target storedV call initialInvariant
    generatedTranslation storedTranslation run
  have verified := successor.isDefEq (s := state) call
    generatedTranslation storedTranslation
  have post := verified initialInvariant
  simp only [Methods.next] at post
  rw [run] at post
  exact ⟨post.1, ⟨storedV, storedTranslation, (post.2 rfl).symm⟩⟩

end Methods.ScopedWFAtOn

namespace Methods.ActiveScopedWFAtOn

/-- Restrict an active-block successor-layer DefEq theorem to the exact
artifact calls named by `GeneratedArtifactCallPlan`.  This is semantically
identical to the stable adapter above; the stronger invariant prevents a
recursive generated-rule cache from being laundered through stable authority
before its recursor block has been admitted. -/
theorem artifactDefEqContract
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {members : Array (KId .anon)}
    {calls : Methods.CallDomain} {methods : Methods .anon}
    (successor : Methods.ActiveScopedWFAtOn model layer semantics support
      members calls (Methods.next methods)) :
    ArtifactDefEqContract world.venv model.keys.uvars world.nameOf trProj
      calls methods
        (ScopedActiveWhnfStateInv model layer semantics support members
          []) := by
  intro state final generated stored target storedV call initialInvariant
    generatedTranslation storedTranslation run
  have verified := successor.isDefEq (state := state) call
    generatedTranslation storedTranslation
  have post := verified initialInvariant
  simp only [Methods.next] at post
  rw [run] at post
  exact ⟨post.1, ⟨storedV, storedTranslation, (post.2 rfl).symm⟩⟩

end Methods.ActiveScopedWFAtOn

namespace RecM

/-- A successful selected-candidate comparison is semantically canonical
under the same finite K2S successor-layer contract used by the production
recursive-method knot. -/
theorem checkGeneratedRecursorCandidate_canonicalScoped
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {calls : Methods.CallDomain}
    {source : Lean4Lean.VInductDecl}
    {generation : source.GenerationChecked}
    {ty : KExpr .anon} {declaredLvls : UInt64}
    {declaredIsUnsafe : Bool} {params motives minors indices : UInt64}
    {storedRules : Array (RecRule .anon)}
    {generated : GeneratedRecursor .anon} {methods : Methods .anon}
    {initial final : TcState .anon}
    (uvars : generation.recursor.uvars = model.keys.uvars)
    (run : (checkGeneratedRecursorCandidate ty declaredLvls declaredIsUnsafe
      params motives minors indices storedRules generated).run methods initial =
        .ok () final)
    (canonical : CanonicalArtifactsS world.venv world.nameOf trProj generation
      generated)
    (translations : StoredArtifactTranslationPlan world.venv
      generation.recursor.uvars world.nameOf trProj ty storedRules)
    (callPlan : GeneratedArtifactCallPlan calls generated ty storedRules)
    (successor : Methods.ScopedWFAtOn model layer semantics support calls
      (Methods.next methods))
    (initialInvariant :
      ScopedWhnfStateInv model layer semantics support [] initial) :
    CanonicalCandidateAcceptance world.venv world.nameOf trProj generation ty
      declaredLvls declaredIsUnsafe params motives minors indices storedRules
      generated (ScopedWhnfStateInv model layer semantics support []) final := by
  have defEq : ArtifactDefEqContract world.venv
      generation.recursor.uvars world.nameOf trProj calls methods
        (ScopedWhnfStateInv model layer semantics support []) := by
    rw [uvars]
    exact successor.artifactDefEqContract
  exact checkGeneratedRecursorCandidate_canonical run canonical translations
    callPlan defEq initialInvariant

/-- Cache-level companion: exact selection plus exhaustive comparison yields
canonical stored artifacts at the candidate that production actually chose.
Selection's own stateful callbacks remain an explicit invariant obligation;
the candidate DefEq calls are discharged by the finite successor layer here. -/
theorem checkGeneratedRecursorFromCache_canonicalScoped
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {calls : Methods.CallDomain}
    {source : Lean4Lean.VInductDecl}
    {generation : source.GenerationChecked}
    {recBlock id : KId .anon} {ty : KExpr .anon}
    {declaredLvls : UInt64} {declaredIsUnsafe : Bool}
    {params motives minors indices : UInt64} {indId : KId .anon}
    {storedRules : Array (RecRule .anon)}
    {generated : Array (GeneratedRecursor .anon)}
    {methods : Methods .anon} {initial final : TcState .anon}
    (uvars : generation.recursor.uvars = model.keys.uvars)
    (run : (checkGeneratedRecursorFromCache recBlock id ty declaredLvls
      declaredIsUnsafe params motives minors indices indId storedRules
      generated).run methods initial = .ok () final)
    (canonicalAt : ∀ {index : Nat} {selected : GeneratedRecursor .anon},
      generated[index]? = some selected →
        CanonicalArtifactsS world.venv world.nameOf trProj generation selected)
    (translations : StoredArtifactTranslationPlan world.venv
      generation.recursor.uvars world.nameOf trProj ty storedRules)
    (callPlanAt : ∀ {index : Nat} {selected : GeneratedRecursor .anon},
      generated[index]? = some selected →
        GeneratedArtifactCallPlan calls selected ty storedRules)
    (selectionInvariant : ∀ {index : Nat}
        {selected : GeneratedRecursor .anon} {afterSelection : TcState .anon},
      (selectGeneratedRecursorIndex recBlock id ty params motives minors indId
        generated).run methods initial = .ok (some index) afterSelection →
      generated[index]? = some selected →
        ScopedWhnfStateInv model layer semantics support [] afterSelection)
    (successor : Methods.ScopedWFAtOn model layer semantics support calls
      (Methods.next methods)) :
    CanonicalCacheAcceptance world.venv world.nameOf trProj generation
      recBlock id ty declaredLvls declaredIsUnsafe params motives minors
      indices indId storedRules generated methods
        (ScopedWhnfStateInv model layer semantics support []) initial final := by
  have defEq : ArtifactDefEqContract world.venv
      generation.recursor.uvars world.nameOf trProj calls methods
        (ScopedWhnfStateInv model layer semantics support []) := by
    rw [uvars]
    exact successor.artifactDefEqContract
  exact checkGeneratedRecursorFromCache_canonical run canonicalAt translations
    callPlanAt selectionInvariant defEq

/-- Active-block counterpart of
`checkGeneratedRecursorCandidate_canonicalScoped`.  Recursive artifacts are
checked before their physical block becomes stably trusted, so the invariant
must retain the exact coordinated member authority throughout comparison. -/
theorem checkGeneratedRecursorCandidate_canonicalActiveScoped
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {members : Array (KId .anon)}
    {calls : Methods.CallDomain}
    {source : Lean4Lean.VInductDecl}
    {generation : source.GenerationChecked}
    {ty : KExpr .anon} {declaredLvls : UInt64}
    {declaredIsUnsafe : Bool} {params motives minors indices : UInt64}
    {storedRules : Array (RecRule .anon)}
    {generated : GeneratedRecursor .anon} {methods : Methods .anon}
    {initial final : TcState .anon}
    (uvars : generation.recursor.uvars = model.keys.uvars)
    (run : (checkGeneratedRecursorCandidate ty declaredLvls declaredIsUnsafe
      params motives minors indices storedRules generated).run methods initial =
        .ok () final)
    (canonical : CanonicalArtifactsS world.venv world.nameOf trProj generation
      generated)
    (translations : StoredArtifactTranslationPlan world.venv
      generation.recursor.uvars world.nameOf trProj ty storedRules)
    (callPlan : GeneratedArtifactCallPlan calls generated ty storedRules)
    (successor : Methods.ActiveScopedWFAtOn model layer semantics support
      members calls (Methods.next methods))
    (initialInvariant : ScopedActiveWhnfStateInv model layer semantics support
      members [] initial) :
    CanonicalCandidateAcceptance world.venv world.nameOf trProj generation ty
      declaredLvls declaredIsUnsafe params motives minors indices storedRules
      generated
        (ScopedActiveWhnfStateInv model layer semantics support members [])
        final := by
  have defEq : ArtifactDefEqContract world.venv
      generation.recursor.uvars world.nameOf trProj calls methods
        (ScopedActiveWhnfStateInv model layer semantics support members []) := by
    rw [uvars]
    exact successor.artifactDefEqContract
  exact checkGeneratedRecursorCandidate_canonical run canonical translations
    callPlan defEq initialInvariant

/-- Cache-level active-block companion.  Selection and all exhaustive
artifact comparisons retain temporary authority for exactly `members`; no
stable-trust premise for a self-referential recursive rule is introduced. -/
theorem checkGeneratedRecursorFromCache_canonicalActiveScoped
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {members : Array (KId .anon)}
    {calls : Methods.CallDomain}
    {source : Lean4Lean.VInductDecl}
    {generation : source.GenerationChecked}
    {recBlock id : KId .anon} {ty : KExpr .anon}
    {declaredLvls : UInt64} {declaredIsUnsafe : Bool}
    {params motives minors indices : UInt64} {indId : KId .anon}
    {storedRules : Array (RecRule .anon)}
    {generated : Array (GeneratedRecursor .anon)}
    {methods : Methods .anon} {initial final : TcState .anon}
    (uvars : generation.recursor.uvars = model.keys.uvars)
    (run : (checkGeneratedRecursorFromCache recBlock id ty declaredLvls
      declaredIsUnsafe params motives minors indices indId storedRules
      generated).run methods initial = .ok () final)
    (canonicalAt : ∀ {index : Nat} {selected : GeneratedRecursor .anon},
      generated[index]? = some selected →
        CanonicalArtifactsS world.venv world.nameOf trProj generation selected)
    (translations : StoredArtifactTranslationPlan world.venv
      generation.recursor.uvars world.nameOf trProj ty storedRules)
    (callPlanAt : ∀ {index : Nat} {selected : GeneratedRecursor .anon},
      generated[index]? = some selected →
        GeneratedArtifactCallPlan calls selected ty storedRules)
    (selectionInvariant : ∀ {index : Nat}
        {selected : GeneratedRecursor .anon} {afterSelection : TcState .anon},
      (selectGeneratedRecursorIndex recBlock id ty params motives minors indId
        generated).run methods initial = .ok (some index) afterSelection →
      generated[index]? = some selected →
        ScopedActiveWhnfStateInv model layer semantics support members []
          afterSelection)
    (successor : Methods.ActiveScopedWFAtOn model layer semantics support
      members calls (Methods.next methods)) :
    CanonicalCacheAcceptance world.venv world.nameOf trProj generation
      recBlock id ty declaredLvls declaredIsUnsafe params motives minors
      indices indId storedRules generated methods
        (ScopedActiveWhnfStateInv model layer semantics support members [])
        initial final := by
  have defEq : ArtifactDefEqContract world.venv
      generation.recursor.uvars world.nameOf trProj calls methods
        (ScopedActiveWhnfStateInv model layer semantics support members []) := by
    rw [uvars]
    exact successor.artifactDefEqContract
  exact checkGeneratedRecursorFromCache_canonical run canonicalAt translations
    callPlanAt selectionInvariant defEq

end RecM

end Ix.Tc
