import Ix.Tc.Verify.Inductive.GeneratedRecursorAcceptance
import Ix.Tc.Verify.Check.ScopedActiveBlock
import Ix.Tc.Verify.RecursiveMethods.ScopedCallDomains

/-!
# Generated-recursor selection callbacks

Production selects a generated recursor by comparing complete closed types.
It first checks the canonical stored block position, then uses an explicit
finite fold over the remaining entries as a fallback. Every stateful DefEq
call is tied to the exact generated array position and the frozen stored type;
metadata-only iterations are state-pure.
-/

namespace Ix.Tc

open GeneratedRecursorSemantics

namespace GeneratedRecursorSemantics

/-- Exact call-domain coverage for every array entry that selection could
compare with the frozen stored type. Metadata filtering, the positional short
circuit, and fallback filtering can only reduce this finite set. -/
def GeneratedSelectionCallPlan (calls : Methods.CallDomain)
    (generated : Array (GeneratedRecursor .anon))
    (ty : KExpr .anon) : Prop :=
  ∀ {index : Nat} {selected : GeneratedRecursor .anon},
    generated[index]? = some selected → calls.isDefEq selected.ty ty

/-- Closed translations for the stored type and every generated type that
the finite selection fold can reach. -/
structure GeneratedSelectionTranslationPlan
    (env : Lean4Lean.VEnv) (uvars : Nat)
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel)
    (generated : Array (GeneratedRecursor .anon))
    (ty : KExpr .anon) : Prop where
  stored : ∃ storedV,
    TrKExprS env uvars nameOf trProj [] ty storedV
  generatedAt : ∀ {index : Nat} {selected : GeneratedRecursor .anon},
    generated[index]? = some selected →
      ∃ generatedV,
        TrKExprS env uvars nameOf trProj [] selected.ty generatedV

/-- State preservation supplied for the exact DefEq calls made by one
selection array. -/
def GeneratedSelectionDefEqStateContract
    (calls : Methods.CallDomain) (methods : Methods .anon)
    (invariant : TcState .anon → Prop)
    (generated : Array (GeneratedRecursor .anon))
    (ty : KExpr .anon) : Prop :=
  ∀ {state : TcState .anon} {index : Nat}
      {selected : GeneratedRecursor .anon},
    generated[index]? = some selected →
    calls.isDefEq selected.ty ty →
    TcM.WF invariant state
      ((RecM.isDefEq selected.ty ty).run methods)
      (fun _ _ => True)

end GeneratedRecursorSemantics

namespace RecM

private theorem generatedRecursorSelectionStep_wf
    {calls : Methods.CallDomain} {methods : Methods .anon}
    {invariant : TcState .anon → Prop}
    {ty : KExpr .anon} {params motives minors : UInt64}
    {indId : KId .anon}
    {generated : Array (GeneratedRecursor .anon)}
    (callPlan : GeneratedSelectionCallPlan calls generated ty)
    (defEq : GeneratedSelectionDefEqStateContract calls methods invariant
      generated ty)
    (typeMatches : Array Nat) (index : Nat) (state : TcState .anon) :
    TcM.WF invariant state
      ((generatedRecursorSelectionStep ty params motives minors indId
        generated typeMatches index).run methods)
      (fun _ _ => True) := by
  unfold generatedRecursorSelectionStep
  cases lookup : generated[index]? with
  | none => exact TcM.WF.pure fun _ => trivial
  | some selected =>
      simp only
      split
      · exact TcM.WF.pure fun _ => trivial
      · rw [ReaderT.run_bind]
        apply TcM.WF.bind (defEq lookup (callPlan lookup))
        intro answer after _
        cases answer <;> exact TcM.WF.pure fun _ => trivial

private theorem selectGeneratedRecursorAtPosition_wf
    {calls : Methods.CallDomain} {methods : Methods .anon}
    {invariant : TcState .anon → Prop}
    {ty : KExpr .anon} {params motives minors : UInt64}
    {indId : KId .anon}
    {generated : Array (GeneratedRecursor .anon)}
    (callPlan : GeneratedSelectionCallPlan calls generated ty)
    (defEq : GeneratedSelectionDefEqStateContract calls methods invariant
      generated ty)
    (storedPos : Option Nat) (state : TcState .anon) :
    TcM.WF invariant state
      ((selectGeneratedRecursorAtPosition storedPos ty params motives minors
        indId generated).run methods)
      (fun _ _ => True) := by
  unfold selectGeneratedRecursorAtPosition
  cases storedPos with
  | none => exact TcM.WF.pure fun _ => trivial
  | some index =>
      simp only
      cases lookup : generated[index]? with
      | none => exact TcM.WF.pure fun _ => trivial
      | some selected =>
          simp only
          split
          · exact TcM.WF.pure fun _ => trivial
          · rw [ReaderT.run_bind]
            apply TcM.WF.bind (defEq lookup (callPlan lookup))
            intro answer after _
            cases answer <;> exact TcM.WF.pure fun _ => trivial

private theorem collectGeneratedRecursorTypeMatchesList_wf
    {calls : Methods.CallDomain} {methods : Methods .anon}
    {invariant : TcState .anon → Prop}
    {ty : KExpr .anon} {params motives minors : UInt64}
    {indId : KId .anon}
    {generated : Array (GeneratedRecursor .anon)}
    (callPlan : GeneratedSelectionCallPlan calls generated ty)
    (defEq : GeneratedSelectionDefEqStateContract calls methods invariant
      generated ty) :
    ∀ (indices : List Nat) (typeMatches : Array Nat)
        (state : TcState .anon),
      TcM.WF invariant state
        ((indices.foldlM
          (generatedRecursorSelectionStep ty params motives minors indId
            generated) typeMatches).run methods)
        (fun _ _ => True)
  | [], typeMatches, state => TcM.WF.pure fun _ => trivial
  | index :: indices, typeMatches, state => by
      rw [List.foldlM_cons, ReaderT.run_bind]
      apply TcM.WF.bind
        (generatedRecursorSelectionStep_wf callPlan defEq typeMatches index
          state)
      intro nextMatches after _
      exact collectGeneratedRecursorTypeMatchesList_wf callPlan defEq indices
        nextMatches after

/-- The complete finite type-match fold preserves the supplied checker
invariant on success and error. -/
theorem collectGeneratedRecursorTypeMatches_wf
    {calls : Methods.CallDomain} {methods : Methods .anon}
    {invariant : TcState .anon → Prop}
    {ty : KExpr .anon} {params motives minors : UInt64}
    {indId : KId .anon}
    {generated : Array (GeneratedRecursor .anon)}
    (callPlan : GeneratedSelectionCallPlan calls generated ty)
    (defEq : GeneratedSelectionDefEqStateContract calls methods invariant
      generated ty) (skip : Option Nat) (state : TcState .anon) :
    TcM.WF invariant state
      ((collectGeneratedRecursorTypeMatches ty params motives minors indId
        generated skip).run methods)
      (fun _ _ => True) := by
  unfold collectGeneratedRecursorTypeMatches
  exact collectGeneratedRecursorTypeMatchesList_wf callPlan defEq _ #[] state

/-- The outer stored-position read, complete positional comparison, and finite
fallback fold all preserve the supplied checker invariant. -/
theorem selectGeneratedRecursorIndex_wf
    {calls : Methods.CallDomain} {methods : Methods .anon}
    {invariant : TcState .anon → Prop}
    {recBlock id : KId .anon} {ty : KExpr .anon}
    {params motives minors : UInt64} {indId : KId .anon}
    {generated : Array (GeneratedRecursor .anon)}
    (callPlan : GeneratedSelectionCallPlan calls generated ty)
    (defEq : GeneratedSelectionDefEqStateContract calls methods invariant
      generated ty) (state : TcState .anon) :
    TcM.WF invariant state
      ((selectGeneratedRecursorIndex recBlock id ty params motives minors
        indId generated).run methods)
      (fun _ _ => True) := by
  unfold selectGeneratedRecursorIndex
  rw [ReaderT.run_bind]
  apply TcM.WF.bind
    (Q₁ := fun observed after => observed = after)
    (TcM.WF.get fun _ => rfl)
  intro observed after observedEq
  subst observed
  rw [ReaderT.run_bind]
  apply TcM.WF.bind
    (selectGeneratedRecursorAtPosition_wf callPlan defEq _ after)
  intro selected afterPosition _
  cases selected with
  | some index => exact TcM.WF.pure fun _ => trivial
  | none =>
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        (collectGeneratedRecursorTypeMatches_wf callPlan defEq _ afterPosition)
      intro typeMatches final _
      exact TcM.WF.pure fun _ => trivial

/-- A successful concrete selection therefore exposes an invariant-preserving
post-state, independently of which matching index its pure final choice
returns. -/
theorem selectGeneratedRecursorIndex_preserves
    {calls : Methods.CallDomain} {methods : Methods .anon}
    {invariant : TcState .anon → Prop}
    {recBlock id : KId .anon} {ty : KExpr .anon}
    {params motives minors : UInt64} {indId : KId .anon}
    {generated : Array (GeneratedRecursor .anon)}
    {initial final : TcState .anon} {result : Option Nat}
    (callPlan : GeneratedSelectionCallPlan calls generated ty)
    (defEq : GeneratedSelectionDefEqStateContract calls methods invariant
      generated ty)
    (initialInvariant : invariant initial)
    (run : (selectGeneratedRecursorIndex recBlock id ty params motives minors
      indId generated).run methods initial = .ok result final) :
    invariant final := by
  have post := selectGeneratedRecursorIndex_wf
    (recBlock := recBlock) (id := id) (ty := ty) (params := params)
    (motives := motives) (minors := minors) (indId := indId)
    callPlan defEq initial initialInvariant
  rw [run] at post
  exact post.1

/-- K2S's finite successor-layer contract supplies state preservation for
exactly the complete closed type calls named by a selection plan. -/
theorem selectGeneratedRecursorIndex_preservesScoped
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {calls : Methods.CallDomain}
    {methods : Methods .anon}
    {recBlock id : KId .anon} {ty : KExpr .anon}
    {params motives minors : UInt64} {indId : KId .anon}
    {generated : Array (GeneratedRecursor .anon)}
    {initial final : TcState .anon} {result : Option Nat}
    (callPlan : GeneratedSelectionCallPlan calls generated ty)
    (translations : GeneratedSelectionTranslationPlan world.venv
      model.keys.uvars world.nameOf trProj generated ty)
    (successor : Methods.ScopedWFAtOn model layer semantics support calls
      (Methods.next methods))
    (initialInvariant :
      ScopedWhnfStateInv model layer semantics support [] initial)
    (run : (selectGeneratedRecursorIndex recBlock id ty params motives minors
      indId generated).run methods initial = .ok result final) :
    ScopedWhnfStateInv model layer semantics support [] final := by
  have defEq : GeneratedSelectionDefEqStateContract calls methods
      (ScopedWhnfStateInv model layer semantics support []) generated ty := by
    intro state index selected lookup call
    obtain ⟨generatedV, generatedTr⟩ := translations.generatedAt lookup
    obtain ⟨storedV, storedTr⟩ := translations.stored
    have verified := successor.isDefEq (s := state) call generatedTr storedTr
    simp only [Methods.next] at verified
    exact TcM.WF.mono verified
      (fun _ _ _ => trivial) (fun _ _ _ => trivial)
  exact selectGeneratedRecursorIndex_preserves callPlan defEq initialInvariant
    run

/-- Active coordinated-block form of the finite selection theorem.  Only the
invariant changes: DefEq callbacks retain temporary authority for the exact
recursor member array until the atomic block transaction closes. -/
theorem selectGeneratedRecursorIndex_preservesActiveScoped
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {members : Array (KId .anon)}
    {calls : Methods.CallDomain} {methods : Methods .anon}
    {recBlock id : KId .anon} {ty : KExpr .anon}
    {params motives minors : UInt64} {indId : KId .anon}
    {generated : Array (GeneratedRecursor .anon)}
    {initial final : TcState .anon} {result : Option Nat}
    (callPlan : GeneratedSelectionCallPlan calls generated ty)
    (translations : GeneratedSelectionTranslationPlan world.venv
      model.keys.uvars world.nameOf trProj generated ty)
    (successor : Methods.ActiveScopedWFAtOn model layer semantics support
      members calls (Methods.next methods))
    (initialInvariant : ScopedActiveWhnfStateInv model layer semantics support
      members [] initial)
    (run : (selectGeneratedRecursorIndex recBlock id ty params motives minors
      indId generated).run methods initial = .ok result final) :
    ScopedActiveWhnfStateInv model layer semantics support members [] final := by
  have defEq : GeneratedSelectionDefEqStateContract calls methods
      (ScopedActiveWhnfStateInv model layer semantics support members [])
      generated ty := by
    intro state index selected lookup call
    obtain ⟨generatedV, generatedTr⟩ := translations.generatedAt lookup
    obtain ⟨storedV, storedTr⟩ := translations.stored
    have verified := successor.isDefEq (state := state) call generatedTr storedTr
    simp only [Methods.next] at verified
    exact TcM.WF.mono verified
      (fun _ _ _ => trivial) (fun _ _ _ => trivial)
  exact selectGeneratedRecursorIndex_preserves callPlan defEq initialInvariant
    run

end RecM

end Ix.Tc
