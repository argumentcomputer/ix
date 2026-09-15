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

private theorem readScopedExpr?_app_inv {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {source : KExpr .anon} {fn arg : VExpr β}
    (headLambda : ∃ name bi domain body info,
      (RecM.appSpineView source).1 = .lam name bi domain body info)
    (reading : readScopedExpr? resolve locals source = some (.app fn arg)) :
    ∃ rawFn rawArg info, source = .app rawFn rawArg info ∧
      readScopedExpr? resolve locals rawFn = some fn ∧
      readScopedExpr? resolve locals rawArg = some arg := by
  cases source with
  | app rawFn rawArg info => exact ⟨rawFn, rawArg, info, rfl, readScopedExpr?_app_parts reading⟩
  | var index name info => simp [readScopedExpr?] at reading
  | fvar id name info =>
      obtain ⟨_, _, same⟩ := Option.map_eq_some_iff.mp reading
      cases same
  | const id levels info =>
      obtain ⟨_, _, same⟩ := bind_success reading
      cases same
  | lam name bi domain body info | all name bi domain body info =>
      obtain ⟨_, _, reading⟩ := bind_success reading
      obtain ⟨_, _, same⟩ := bind_success reading
      cases same
  | prj id index value info =>
      obtain ⟨_, _, reading⟩ := bind_success reading
      obtain ⟨_, _, same⟩ := bind_success reading
      cases same
  | letE =>
      obtain ⟨_, _, _, _, _, same⟩ := headLambda
      cases same
  | _ => simp [readScopedExpr?] at reading

private theorem readScopedExpr?_lam_inv {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {source : KExpr .anon} {domain body : VExpr β}
    (headLambda : ∃ name bi domain body info,
      (RecM.appSpineView source).1 = .lam name bi domain body info)
    (reading : readScopedExpr? resolve locals source = some (.lam domain body)) :
    ∃ name bi rawDomain rawBody info, source = .lam name bi rawDomain rawBody info := by
  cases source with
  | lam name bi rawDomain rawBody info => exact ⟨name, bi, rawDomain, rawBody, info, rfl⟩
  | var index name info => simp [readScopedExpr?] at reading
  | fvar id name info =>
      obtain ⟨_, _, same⟩ := Option.map_eq_some_iff.mp reading
      cases same
  | const id levels info =>
      obtain ⟨_, _, same⟩ := bind_success reading
      cases same
  | app fn arg info | all _ _ fn arg info =>
      obtain ⟨_, _, reading⟩ := bind_success reading
      obtain ⟨_, _, same⟩ := bind_success reading
      cases same
  | prj id index value info =>
      obtain ⟨_, _, reading⟩ := bind_success reading
      obtain ⟨_, _, same⟩ := bind_success reading
      cases same
  | letE =>
      obtain ⟨_, _, _, _, _, same⟩ := headLambda
      cases same
  | _ => simp [readScopedExpr?] at reading

private theorem list_reverse_induction {α : Type u} {motive : List α → Prop}
    (nil : motive [])
    (append_singleton : ∀ tail last, motive tail → motive (tail ++ [last]))
    (values : List α) : motive values := by
  have reversed : ∀ items : List α, motive items.reverse := by
    intro items
    induction items with
    | nil => exact nil
    | cons item items ih =>
        simpa only [List.reverse_cons] using append_singleton items.reverse item ih
  simpa using reversed values.reverse

/-- When the production spine has a syntactic lambda head, its whole
reading determines the head and argument readings. A lambda hidden inside
a let does not establish this premise; the production planner supplies it. -/
theorem readScopedExpr?_lambda_spine {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {source : KExpr .anon} {condition : Certified.PropWhen} {domain body : AExpr β}
    {arguments : List (AExpr β)}
    (rawHeadLambda : ∃ name bi rawDomain rawBody info,
      source.collectSpine.1 = .lam name bi rawDomain rawBody info)
    (reading : readScopedExpr? resolve locals source =
      some ((AExpr.lam condition domain body).appN arguments).erase) :
    readScopedExpr? resolve locals source.collectSpine.1 =
        some (AExpr.lam condition domain body).erase ∧
      source.collectSpine.2.toList.map (readScopedExpr? resolve locals ·) =
        arguments.map (some ·.erase) := by
  have headLambda : ∃ name bi rawDomain rawBody info,
      (RecM.appSpineView source).1 = .lam name bi rawDomain rawBody info := by
    simpa only [(RecM.appSpineView_collectSpine source).1] using rawHeadLambda
  clear rawHeadLambda
  have view : readScopedExpr? resolve locals (RecM.appSpineView source).1 =
        some (AExpr.lam condition domain body).erase ∧
      (RecM.appSpineView source).2.map (readScopedExpr? resolve locals ·) =
        arguments.map (some ·.erase) := by
    induction arguments using list_reverse_induction generalizing source with
    | nil =>
        obtain ⟨_, _, _, _, _, rfl⟩ := readScopedExpr?_lam_inv headLambda reading
        exact ⟨reading, rfl⟩
    | append_singleton arguments argument ih =>
        simp only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil, AExpr.erase] at reading
        obtain ⟨fn, arg, info, rfl, fnReads, argReads⟩ := readScopedExpr?_app_inv headLambda reading
        obtain ⟨headReads, argumentReads⟩ := ih fnReads headLambda
        exact ⟨headReads, by simp only [RecM.appSpineView, List.map_append,
          List.map_cons, List.map_nil, argumentReads, argReads]⟩
  simpa only [(RecM.appSpineView_collectSpine source).1,
    (RecM.appSpineView_collectSpine source).2] using view

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

/-- The actual beta step reads as a model beta prefix. This representation
fact depends on the executed peel, substitution and suffix reconstruction;
it applies equally to source expressions and generated intermediate terms. -/
theorem beta_many_step_readScopedExpr? {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {rawFunction rawArgument : KExpr .anon} {appInfo : ExprInfo .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {rawDomain rawInner rawBody : KExpr .anon} {lambdaInfo : ExprInfo .anon}
    {rawArguments consumed : Array (KExpr .anon)}
    {condition : Certified.PropWhen} {domain inner : AExpr β} {arguments : List (AExpr β)}
    (spine : (KExpr.app rawFunction rawArgument appInfo).collectSpine =
      (.lam name bi rawDomain rawInner lambdaInfo, rawArguments))
    (headReads : readScopedExpr? resolve locals (.lam name bi rawDomain rawInner lambdaInfo) =
      some (AExpr.lam condition domain inner).erase)
    (argumentReads : rawArguments.toList.map (readScopedExpr? resolve locals ·) =
      arguments.map (some ·.erase))
    (peeling : RecM.consumeBetaLams (.lam name bi rawDomain rawInner lambdaInfo) rawArguments =
      (rawBody, consumed))
    (nonempty : (!consumed.isEmpty) = true)
    (before : TcState .anon) (reductionFuel : Nat) (flags : WhnfFlags)
    (walkerBounds : SimulSubstBounds rawBody consumed.reverse 0)
    (coherent : before.env.intern.WF)
    (walkerFaithful : KExpr.CollisionFree fun term => before.env.intern.ExprSupport term ∨
      KExpr.SimulSubstReach consumed.reverse rawBody 0 term)
    (suffixFaithful : KExpr.CollisionFree fun term =>
      (simulSubst rawBody consumed.reverse 0 before.env.intern).2.ExprSupport term ∨
        term ∈ cheapBetaChainList (simulSubst rawBody consumed.reverse 0 before.env.intern).1
          (rawArguments.extract consumed.size rawArguments.size).toList) :
    ∃ (result : KExpr .anon) (after : TcState .anon),
      (RecM.whnfCoreWithFlagsStep (.app rawFunction rawArgument appInfo) flags).run
        (methodsN (reductionFuel + 1)) before = .ok (.next result) after ∧
      readScopedExpr? resolve locals result =
        some (AExpr.betaPrefix consumed.size (.lam condition domain inner) arguments).erase ∧
      consumed.size ≤ inner.lambdaDepth + 1 ∧ after.env.intern.WF := by
  obtain ⟨rawPeel, consumedPrefix, consumedBound⟩ := RecM.BetaPeel.of_consume peeling
  obtain ⟨body, modelPeel, bodyReads⟩ := betaPeel_readScopedExpr? rawPeel headReads
  have sizeAgrees : rawArguments.size = arguments.length := by
    have lengths := congrArg List.length argumentReads
    simpa using lengths
  have consumedSize : (arguments.take consumed.size).length = consumed.size := by
    simp only [List.length_take]
    omega
  have consumedReads : consumed.toList.map (readScopedExpr? resolve locals ·) =
      (arguments.take consumed.size).map (some ·.erase) := by
    rw [consumedPrefix, List.map_take, argumentReads, List.map_take]
  have suffixReads : (rawArguments.extract consumed.size rawArguments.size).toList.map
      (readScopedExpr? resolve locals ·) = (arguments.drop consumed.size).map (some ·.erase) := by
    rw [RecM.BetaPeel.remaining_eq_drop peeling, List.map_drop, argumentReads, List.map_drop]
  obtain ⟨walkReads, walkCoherent⟩ := simulSubst_readScopedExpr?
    (by simpa only [Array.size_reverse] using consumedSize.symm)
    walkerBounds.1 walkerBounds.2.1 (by simpa using walkerBounds.2.2.2.1)
    walkerBounds.2.2.1 coherent walkerFaithful
    (by simpa only [Nat.zero_add, Array.length_toList, consumedSize] using bodyReads)
    (argumentsReading_reverse_get consumedReads consumedSize.symm)
  have peelingMeaning := LambdaPeel.betaPrefix (arguments := arguments.take consumed.size)
    (by simpa only [consumedSize, Array.length_toList] using modelPeel) (arguments.drop consumed.size)
  simp only [consumedSize, List.take_append_drop] at peelingMeaning
  let walk := simulSubst rawBody consumed.reverse 0 before.env.intern
  let middle := { before with env := { before.env with intern := walk.2 } }
  obtain ⟨result, after, finish, resultReads, preserved⟩ :=
    finishAppResult_readScopedExpr? (before := middle) walkCoherent suffixFaithful walkReads suffixReads
      (methodsN (reductionFuel + 1))
  refine ⟨result, after, ?_, ?_, ?_, preserved⟩
  · exact RecM.whnfCoreWithFlagsStep_betaMany spine rfl peeling nonempty rfl finish
  · simpa only [peelingMeaning] using resultReads
  · simpa only [Array.length_toList, AExpr.lambdaDepth] using modelPeel.length_bound


end Ix.Kernel.Consistency
