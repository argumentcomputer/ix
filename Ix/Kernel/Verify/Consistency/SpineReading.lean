/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Simultaneous
import Ix.Kernel.Verify.Support
import Ix.Kernel.Verify.Whnf.Beta.DirectStep
import Ix.Kernel.Verify.Whnf.Beta.LambdaPeeling
import Ix.Theory.Model.BetaSpine

/-! Read the actual application spine, peeled lambda body, and interned
suffix used by beta reduction. All resources concern concrete syntax. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

private theorem bind_success {α γ : Type _} {action : Option α}
    {next : α → Option γ} {result : γ} (run : action.bind next = some result) :
    ∃ intermediate, action = some intermediate ∧ next intermediate = some result := by
  cases action with
  | none => contradiction
  | some value => exact ⟨value, rfl, run⟩

theorem argumentsReading_get {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {raw : List (KExpr .anon)} {arguments : List (AExpr β)}
    (reading : raw.map (readScopedExpr? resolve locals ·) = arguments.map (some ·.erase))
    (index : Nat) (rawSmall : index < raw.length) (modelSmall : index < arguments.length) :
    readScopedExpr? resolve locals raw[index] = some arguments[index].erase := by
  have selected := congrArg (fun values => values[index]?) reading
  simpa only [List.getElem?_map, List.getElem?_eq_getElem rawSmall,
    List.getElem?_eq_getElem modelSmall, Option.map_some, Option.some.injEq] using selected

theorem argumentsReading_reverse_get {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {raw : Array (KExpr .anon)} {arguments : List (AExpr β)}
    (reading : raw.toList.map (readScopedExpr? resolve locals ·) = arguments.map (some ·.erase))
    (sizeAgrees : raw.size = arguments.length)
    (index : Nat) (small : index < raw.reverse.size) :
    readScopedExpr? resolve locals raw.reverse[index]! =
      some (arguments[arguments.length - index - 1]'(by simp only [Array.size_reverse] at small; omega)).erase := by
  rw [getElem!_pos raw.reverse index small, Array.getElem_reverse]
  have selected := argumentsReading_get reading (raw.size - 1 - index)
    (by simp only [Array.length_toList, Array.size_reverse] at *; omega)
    (by simp only [Array.size_reverse] at small; omega)
  simpa only [Array.getElem_toList, sizeAgrees,
    show arguments.length - 1 - index = arguments.length - index - 1 by omega] using selected

theorem readScopedExpr?_appN {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {rawHead : KExpr .anon} {head : AExpr β}
    {rawArguments : List (KExpr .anon)} {arguments : List (AExpr β)}
    (headReads : readScopedExpr? resolve locals rawHead = some head.erase)
    (argumentReads : rawArguments.map (readScopedExpr? resolve locals ·) =
      arguments.map (some ·.erase)) :
    readScopedExpr? resolve locals (rawArguments.foldl KExpr.mkApp rawHead) =
      some (head.appN arguments).erase := by
  induction rawArguments generalizing rawHead head arguments with
  | nil =>
      cases arguments <;> simp_all
  | cons argument rawArguments ih =>
      cases arguments with
      | nil => simp at argumentReads
      | cons model arguments =>
          simp only [List.map_cons, List.cons.injEq] at argumentReads
          apply ih _ argumentReads.2
          simp [headReads, argumentReads.1, AExpr.erase]

private theorem readScopedExpr?_appSpineView {β : Type u}
    (resolve : Address → Option (ConstRef β)) (locals : List FVarId) (source : KExpr .anon) :
    readScopedExpr? resolve locals source =
      readScopedExpr? resolve locals
        ((RecM.appSpineView source).2.foldl KExpr.mkApp (RecM.appSpineView source).1) := by
  induction source with
  | app fn arg info ihFn ihArg =>
      simp only [RecM.appSpineView, List.foldl_append, List.foldl_cons, List.foldl_nil,
        readScopedExpr?, readScopedExpr?_mkApp]
      rw [ihFn]
  | _ => rfl

theorem readScopedExpr?_collectSpine {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {source rawHead : KExpr .anon} {rawArguments : Array (KExpr .anon)}
    {head : AExpr β} {arguments : List (AExpr β)}
    (spine : source.collectSpine = (rawHead, rawArguments))
    (headReads : readScopedExpr? resolve locals rawHead = some head.erase)
    (argumentReads : rawArguments.toList.map (readScopedExpr? resolve locals ·) =
      arguments.map (some ·.erase)) :
    readScopedExpr? resolve locals source = some (head.appN arguments).erase := by
  have view := RecM.appSpineView_collectSpine source
  rw [spine] at view
  rw [readScopedExpr?_appSpineView, ← view.1, ← view.2]
  exact readScopedExpr?_appN headReads argumentReads

theorem betaPeel_readScopedExpr? {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {start result : KExpr .anon} {consumed : List (KExpr .anon)}
    {head : AExpr β} {depth : Nat}
    (peeling : RecM.BetaPeel start consumed result)
    (reading : readScopedExpr? resolve locals start depth = some head.erase) :
    ∃ body, LambdaPeel head consumed.length body ∧
      readScopedExpr? resolve locals result (depth + consumed.length) = some body.erase := by
  induction peeling with
  | nil => exact ⟨head, .zero _, reading⟩
  | snoc preceding ih =>
      obtain ⟨current, modelPeel, currentReads⟩ := ih
      rw [readScopedExpr?] at currentReads
      obtain ⟨domain, domainReads, currentReads⟩ := bind_success currentReads
      obtain ⟨body, bodyReads, currentReads⟩ := bind_success currentReads
      cases current <;> cases currentReads
      exact ⟨_, by simpa using modelPeel.snoc, by simpa [Nat.add_assoc] using bodyReads⟩

/-- Rebuilding a suffix needs collision freedom only for its finite chain
of application candidates and the current intern table. -/
theorem internAppChain_readScopedExpr? {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {rawHead : KExpr .anon} {head : AExpr β} {table : InternTable .anon}
    {rawArguments : List (KExpr .anon)} {arguments : List (AExpr β)}
    (coherent : table.WF)
    (faithful : KExpr.CollisionFree fun term => table.ExprSupport term ∨
      term ∈ cheapBetaChainList rawHead rawArguments)
    (headReads : readScopedExpr? resolve locals rawHead = some head.erase)
    (argumentReads : rawArguments.map (readScopedExpr? resolve locals ·) =
      arguments.map (some ·.erase)) :
    readScopedExpr? resolve locals (internAppChain rawHead rawArguments table).1 =
        some (head.appN arguments).erase ∧
      (internAppChain rawHead rawArguments table).2.WF := by
  induction rawArguments generalizing rawHead head table arguments with
  | nil =>
      cases arguments with
      | nil => exact ⟨headReads, coherent⟩
      | cons => simp at argumentReads
  | cons argument rawArguments ih =>
      cases arguments with
      | nil => simp at argumentReads
      | cons model arguments =>
          simp only [List.map_cons, List.cons.injEq] at argumentReads
          let candidate := KExpr.mkApp rawHead argument
          have candidateIn : candidate ∈ cheapBetaChainList rawHead (argument :: rawArguments) := by
            cases rawArguments <;> simp [cheapBetaChainList, candidate]
          have canonical : (table.internExpr candidate).1 = candidate := by
            have exactIntern := table.internExpr_eraseMeta coherent
              (KExpr.keyCollisionFree_anon.mpr (faithful.mono fun term member =>
                member.elim Or.inl fun same => Or.inr (same ▸ candidateIn)))
            simpa only [KExpr.eraseMeta_anon] using exactIntern
          have tailFaithful : KExpr.CollisionFree fun term =>
              (table.internExpr candidate).2.ExprSupport term ∨
                term ∈ cheapBetaChainList candidate rawArguments := by
            apply faithful.mono
            intro term member
            rcases member with resident | inTail
            · rcases InternTable.ExprSupport.of_internExpr resident with old | same
              · exact Or.inl old
              · exact Or.inr (same ▸ candidateIn)
            · exact Or.inr (List.mem_cons_of_mem _ inTail)
          have output := ih (head := head.app model) (coherent.internExpr candidate) tailFaithful
            (by simp [candidate, headReads, argumentReads.1, AExpr.erase]) argumentReads.2
          change readScopedExpr? resolve locals
              (internAppChain (table.internExpr candidate).1 rawArguments
                (table.internExpr candidate).2).1 = _ ∧
            (internAppChain (table.internExpr candidate).1 rawArguments
              (table.internExpr candidate).2).2.WF
          rw [canonical]
          exact output

theorem finishAppResult_readScopedExpr? {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {rawHead : KExpr .anon} {head : AExpr β} {before : TcState .anon}
    {rawArguments : Array (KExpr .anon)} {arguments : List (AExpr β)} {consumed : Nat}
    (coherent : before.env.intern.WF)
    (faithful : KExpr.CollisionFree fun term => before.env.intern.ExprSupport term ∨
      term ∈ cheapBetaChainList rawHead (rawArguments.extract consumed rawArguments.size).toList)
    (headReads : readScopedExpr? resolve locals rawHead = some head.erase)
    (argumentReads : (rawArguments.extract consumed rawArguments.size).toList.map
      (readScopedExpr? resolve locals ·) = arguments.map (some ·.erase))
    (methods : Methods .anon) :
    ∃ result after,
      (RecM.finishAppResult rawHead rawArguments consumed).run methods before = .ok result after ∧
      readScopedExpr? resolve locals result = some (head.appN arguments).erase ∧ after.env.intern.WF := by
  obtain ⟨reads, preserved⟩ := internAppChain_readScopedExpr? coherent faithful headReads argumentReads
  let output := internAppChain rawHead (rawArguments.extract consumed rawArguments.size).toList before.env.intern
  refine ⟨output.1, { before with env := { before.env with intern := output.2 } }, ?_, reads, preserved⟩
  rw [RecM.finishAppResult_eq_internAppChain]
  rfl

end Ix.Kernel.Consistency
