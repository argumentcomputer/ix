import Ix.CompileCert.Canon.PairedInitializer
import Ix.CompileCert.Canon.ExpandWalkers

/-!
Proof-only transport of the actual declaration reader and initial context.

The callbacks remain arbitrary functions. `ReadsRelated` records the raw
observations to be supplied by a paired source presentation; it is an internal
relation, not a new premise on a public canonicity endpoint. In particular this
file does not derive it from the comparator's `MRen` alone. The distinction
matters: the reader emits queried constructor names, whereas `MRen` describes
stored declaration names. Neither is silently identified with the other.

All constructor filtering, metadata stripping, short telescopes and initial
lookup errors retain their real behavior. The protection thunks in the two
contexts remain the actual supplied thunks. No finite environment, successful
queue run or aligned allocation history is assumed.

These declarations have not yet been elaborated or audited.
-/

namespace Ix.CompileCert.Canon.ReaderInitialization

open Ix.Compile.Canon
open Ix (Name Expr ConstantInfo InductiveVal ConstructorVal)
open PairedInitializer

/-- The constructor payload actually read by `IndView.ofConst?`. The stored
constructor name, owner and universe-parameter names are not consulted here. -/
structure ConstructorPayloadRelated (σ : Name → Name) (S : Name → Prop)
    (left right : ConstructorVal) : Prop where
  type : ERen σ S left.cnst.type right.cnst.type
  fields : right.numFields = left.numFields

/-- The old constructor-renaming relation supplies every payload fact the
reader needs, without equating a lookup query with the stored name. -/
theorem ConstructorPayloadRelated.ofCtorRen {σ : Name → Name} {S : Name → Prop}
    {left right : ConstructorVal} (related : CtorRen σ S left right) :
    ConstructorPayloadRelated σ S left right :=
  ⟨related.type, related.numFields⟩

/-- Raw inductive fields read by the actual view/context constructors.
Constructor-query support is explicit here because those are subsequent raw
reads. It must follow from the original presentation's source closure before
this relation can be used at the promised endpoint. -/
structure InductiveHeaderRelated (σ : Name → Name) (S : Name → Prop)
    (left right : InductiveVal) : Prop where
  type : ERen σ S left.cnst.type right.cnst.type
  levels : right.cnst.levelParams = left.cnst.levelParams
  params : right.numParams = left.numParams
  indices : right.numIndices = left.numIndices
  nested : right.numNested = left.numNested
  all : right.all = left.all.map σ
  ctorQueries : right.ctors = left.ctors.map σ
  ctorSupport : ∀ query ∈ left.ctors, S query
  safety : right.isUnsafe = left.isUnsafe

/-- Raw declarations preserve their kind. Only fields actually read on the
inductive/constructor branches constrain the payload. This imposes no rule on
stored-name/query agreement or on embedded cached hashes. -/
inductive DeclarationsRelated (σ : Name → Name) (S : Name → Prop) :
    ConstantInfo → ConstantInfo → Prop
  | axiomDecl (left right : Ix.AxiomVal) :
      DeclarationsRelated σ S (.axiomInfo left) (.axiomInfo right)
  | definitionDecl (left right : Ix.DefinitionVal) :
      DeclarationsRelated σ S (.defnInfo left) (.defnInfo right)
  | theoremDecl (left right : Ix.TheoremVal) :
      DeclarationsRelated σ S (.thmInfo left) (.thmInfo right)
  | opaqueDecl (left right : Ix.OpaqueVal) :
      DeclarationsRelated σ S (.opaqueInfo left) (.opaqueInfo right)
  | quotientDecl (left right : Ix.QuotVal) :
      DeclarationsRelated σ S (.quotInfo left) (.quotInfo right)
  | inductiveDecl {left right : InductiveVal} :
      InductiveHeaderRelated σ S left right →
      DeclarationsRelated σ S (.inductInfo left) (.inductInfo right)
  | constructorDecl {left right : ConstructorVal} :
      ConstructorPayloadRelated σ S left right →
      DeclarationsRelated σ S (.ctorInfo left) (.ctorInfo right)
  | recursorDecl (left right : Ix.RecursorVal) :
      DeclarationsRelated σ S (.recInfo left) (.recInfo right)

/-- No finite support is built into the callback domain. Unqueried names are
unconstrained. This is a raw-input simulation obligation, not its discharge. -/
def ReadsRelated (σ : Name → Name) (S : Name → Prop)
    (left right : Name → Option ConstantInfo) : Prop :=
  ∀ query, S query →
    TableResultRelated (DeclarationsRelated σ S) (left query) (right (σ query))

def inductiveAt (lookup : Name → Option ConstantInfo) (query : Name) : Option InductiveVal :=
  match lookup query with
  | some (.inductInfo value) => some value
  | _ => none

/-- The name in the result is the query, including when the stored record's
name differs. Missing and wrong-kind declarations both disappear. -/
def constructorAt (lookup : Name → Option ConstantInfo) (query : Name) :
    Option (Name × Expr × Nat) :=
  match lookup query with
  | some (.ctorInfo value) => some (query, value.cnst.type, value.numFields)
  | _ => none

/-- Exact factoring of the successful raw inductive branch. -/
def viewOf (lookup : Name → Option ConstantInfo) (query : Name)
    (value : InductiveVal) : IndView :=
  { name := query, levelParams := value.cnst.levelParams, type := value.cnst.type,
    numParams := value.numParams, numIndices := value.numIndices,
    numNested := value.numNested, all := value.all,
    ctors := value.ctors.filterMap (constructorAt lookup), isUnsafe := value.isUnsafe }

/-- Whole Option equality for the production reader, including all eight
constant kinds and missing declarations. -/
theorem ofConst_eq (lookup : Name → Option ConstantInfo) (query : Name) :
    IndView.ofConst? lookup query = (inductiveAt lookup query).map (viewOf lookup query) := by
  cases found : lookup query with
  | none => simp only [IndView.ofConst?, inductiveAt, found, Option.map_none]
  | some value =>
    cases value <;>
      simp only [IndView.ofConst?, inductiveAt, found, Option.map_none,
        Option.map_some, viewOf, constructorAt]

theorem inductiveAt_related {σ : Name → Name} {S : Name → Prop}
    {left right : Name → Option ConstantInfo} (reads : ReadsRelated σ S left right)
    {query : Name} (supported : S query) :
    TableResultRelated (InductiveHeaderRelated σ S)
      (inductiveAt left query) (inductiveAt right (σ query)) := by
  unfold inductiveAt
  cases reads query supported with
  | none => exact .none
  | some declarations =>
    cases declarations with
    | inductiveDecl headers => exact .some headers
    | _ => exact .none

theorem constructorAt_related {σ : Name → Name} {S : Name → Prop}
    {left right : Name → Option ConstantInfo} (reads : ReadsRelated σ S left right)
    {query : Name} (supported : S query) :
    TableResultRelated (SourceCtorRelated σ S)
      (constructorAt left query) (constructorAt right (σ query)) := by
  unfold constructorAt
  cases reads query supported with
  | none => exact .none
  | some declarations =>
    cases declarations with
    | constructorDecl payload => exact .some ⟨rfl, payload.type, payload.fields⟩
    | _ => exact .none

private theorem filterMap_related {α β γ δ : Type} {R : γ → δ → Prop}
    (rename : α → β) (leftRead : α → Option γ) (rightRead : β → Option δ)
    (queries : List α)
    (reads : ∀ query ∈ queries,
      TableResultRelated R (leftRead query) (rightRead (rename query))) :
    LRel R (queries.filterMap leftRead) ((queries.map rename).filterMap rightRead) := by
  induction queries with
  | nil => exact .nil
  | cons query rest ih =>
    have tail := ih (fun name member => reads name (List.mem_cons_of_mem _ member))
    have head := reads query List.mem_cons_self
    simp only [List.map_cons, List.filterMap_cons]
    cases head with
    | none => exact tail
    | some values => exact .cons values tail

/-- Constructor filtering preserves order, multiplicity and every actual
emitted query name. A wrong-kind or missing query is skipped on both sides. -/
theorem constructorArray_related {σ : Name → Name} {S : Name → Prop}
    {left right : Name → Option ConstantInfo} (reads : ReadsRelated σ S left right)
    (queries : Array Name) (supported : ∀ query ∈ queries, S query) :
    LRel (SourceCtorRelated σ S)
      (queries.filterMap (constructorAt left)).toList
      ((queries.map σ).filterMap (constructorAt right)).toList := by
  rw [Array.toList_filterMap, Array.toList_filterMap, Array.toList_map]
  apply filterMap_related σ (constructorAt left) (constructorAt right) queries.toList
  intro query member
  exact constructorAt_related reads (supported query (by simpa using member))

/-- All view fields are accounted for, rather than only the three fields
read by the member initializer. This also supplies the first-member context. -/
structure ReadViewsRelated (σ : Name → Name) (S : Name → Prop)
    (left right : IndView) : Prop extends ViewsRelated σ S left right where
  name : right.name = σ left.name
  levels : right.levelParams = left.levelParams
  params : right.numParams = left.numParams
  nested : right.numNested = left.numNested
  all : right.all = left.all.map σ
  safety : right.isUnsafe = left.isUnsafe

theorem viewOf_related {σ : Name → Name} {S : Name → Prop}
    {left right : Name → Option ConstantInfo} (reads : ReadsRelated σ S left right)
    (query : Name) {value value' : InductiveVal}
    (headers : InductiveHeaderRelated σ S value value') :
    ReadViewsRelated σ S (viewOf left query value) (viewOf right (σ query) value') := by
  refine ⟨⟨headers.type, headers.indices, ?_⟩,
    rfl, headers.levels, headers.params, headers.nested, headers.all, headers.safety⟩
  change LRel (SourceCtorRelated σ S)
    (value.ctors.filterMap (constructorAt left)).toList
    (value'.ctors.filterMap (constructorAt right)).toList
  rw [headers.ctorQueries]
  exact constructorArray_related reads value.ctors headers.ctorSupport

/-- The actual raw declaration callbacks establish the complete view
relation. No relation on already manufactured views is assumed. -/
theorem ofConst_related {σ : Name → Name} {S : Name → Prop}
    {left right : Name → Option ConstantInfo} (reads : ReadsRelated σ S left right)
    {query : Name} (supported : S query) :
    TableResultRelated (ReadViewsRelated σ S)
      (IndView.ofConst? left query) (IndView.ofConst? right (σ query)) := by
  rw [ofConst_eq, ofConst_eq]
  cases inductiveAt_related reads supported with
  | none => exact .none
  | some headers => exact .some (viewOf_related reads query headers)

/-- Forgetting the additional context fields gives the exact initializer
relation expected by the previously retained proof. -/
theorem ofConst_members_related {σ : Name → Name} {S : Name → Prop}
    {left right : Name → Option ConstantInfo} (reads : ReadsRelated σ S left right)
    {query : Name} (supported : S query) :
    TableResultRelated (ViewsRelated σ S)
      (IndView.ofConst? left query) (IndView.ofConst? right (σ query)) := by
  cases ofConst_related reads supported with
  | none => exact .none
  | some views => exact .some views.toViewsRelated

private theorem stripMdata_related {σ : Name → Name} {S : Name → Prop}
    {left right : Expr} (expressions : ERen σ S left right) :
    ERen σ S (stripMdata left) (stripMdata right) := by
  induction expressions with
  | mdata _ _ _ _ ih => exact ih
  | _ => simp only [stripMdata]; constructor <;> assumption

/-- The real telescope reader preserves short/non-forall results and strips
metadata exactly where production does. No well-formedness or lower bound on
the number of available binders is needed. -/
theorem peelForalls_related {σ : Name → Name} {S : Name → Prop}
    {left right : Expr} (expressions : ERen σ S left right)
    (count : Nat) {leftBinders rightBinders : Array Binder}
    (binders : LRel (BinderRen σ S) leftBinders.toList rightBinders.toList) :
    LRel (BinderRen σ S) (peelForalls count left leftBinders).1.toList
      (peelForalls count right rightBinders).1.toList ∧
      ERen σ S (peelForalls count left leftBinders).2
        (peelForalls count right rightBinders).2 := by
  induction count generalizing left right leftBinders rightBinders with
  | zero => exact ⟨binders, expressions⟩
  | succ count ih =>
    have heads := stripMdata_related expressions
    generalize leftHead : stripMdata left = leftValue at heads
    generalize rightHead : stripMdata right = rightValue at heads
    have retained := heads
    cases heads with
    | forallE name name' info info' _ _ types bodies =>
      have extended : LRel (BinderRen σ S)
          (leftBinders.push (name, _, info)).toList
          (rightBinders.push (name', _, info')).toList := by
        simpa only [Array.toList_push] using binders.append (.cons types .nil)
      simpa only [peelForalls, leftHead, rightHead] using ih bodies extended
    | _ => simpa only [peelForalls, leftHead, rightHead] using And.intro binders retained

/-- The non-callback fields selected from the first actual view. The
callbacks and protection thunks themselves remain the supplied functions;
this is not a claim that their later query results are already related. -/
structure FirstContextFieldsRelated (σ : Name → Name) (S : Name → Prop)
    (left right : ExpansionCore.Ctx) : Prop where
  anchor : right.all0 = σ left.all0
  levels : right.levelParams = left.levelParams
  blockLevels : right.blockLevels = left.blockLevels
  params : right.nParams = left.nParams
  binders : LRel (BinderRen σ S) left.paramBinders.toList right.paramBinders.toList

/-- Context fields come from the actual first-view reader, including the
empty-`all` fallback and the exact positional universe parameter order. -/
theorem context_fields_related {σ : Name → Name} {S : Name → Prop}
    {left right : IndView} (views : ReadViewsRelated σ S left right)
    (leftProtect rightProtect : Unit → List Lean.Name)
    (leftInd rightInd : Name → Option IndView) (dedup : Dedup)
    (leftGroups rightGroups : ExpansionCore.GroupCallback)
    (leftAddr rightAddr : Option (Name → Option _root_.Address)) (first : Name) :
    FirstContextFieldsRelated σ S
      (ExpansionHistory.context leftProtect leftInd dedup leftGroups leftAddr first left)
      (ExpansionHistory.context rightProtect rightInd dedup rightGroups rightAddr (σ first) right) := by
  refine ⟨?_, ?_, ?_, views.params, ?_⟩
  · change right.all[0]?.getD (σ first) = σ (left.all[0]?.getD first)
    rw [views.all, Array.getElem?_map]
    cases left.all[0]? <;> rfl
  · change right.levelParams.toList = left.levelParams.toList
    rw [views.levels]
  · change right.levelParams.map Ix.Level.mkParam = left.levelParams.map Ix.Level.mkParam
    rw [views.levels]
  · change LRel (BinderRen σ S)
      (peelForalls left.numParams left.type #[]).1.toList
      (peelForalls right.numParams right.type #[]).1.toList
    rw [views.params]
    exact (peelForalls_related views.type left.numParams (.nil)).1

/-- Raw lookup transport and the real class alias fold suffice for the
whole initializer. This derives the former view premise and parameter-count
agreement, retains its exact missing-query errors, and uses each side's own
unchanged protection/group/address callbacks. -/
theorem initialMembers_from_reads {σ : Name → Name} {S : Name → Prop}
    {leftSource rightSource : Name → Option ConstantInfo}
    (reads : ReadsRelated σ S leftSource rightSource)
    (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))
    (classes : Array (Array Name)) (classSupport : ∀ cls ∈ classes, ∀ name ∈ cls, S name)
    (ordered : Array Name) (orderedSupport : ∀ name ∈ ordered, S name)
    {first : Name} (firstSupport : S first) {leftFirst : IndView}
    (firstFound : IndView.ofConst? leftSource first = some leftFirst)
    (leftProtect rightProtect : Unit → List Lean.Name) (dedup : Dedup)
    (leftGroups rightGroups : ExpansionCore.GroupCallback)
    (leftAddr rightAddr : Option (Name → Option _root_.Address)) :
    ∃ rightFirst,
      IndView.ofConst? rightSource (σ first) = some rightFirst ∧
      ReadViewsRelated σ S leftFirst rightFirst ∧
      let leftCtx := ExpansionHistory.context leftProtect (IndView.ofConst? leftSource)
        dedup leftGroups leftAddr first leftFirst
      let rightCtx := ExpansionHistory.context rightProtect (IndView.ofConst? rightSource)
        dedup rightGroups rightAddr (σ first) rightFirst
      FirstContextFieldsRelated σ S leftCtx rightCtx ∧
      ResultRelated σ S (StatesRelated σ S)
        (ExpansionHistory.initialMembers leftCtx ordered (aliasesOf classes))
        (ExpansionHistory.initialMembers rightCtx (ordered.map σ)
          (aliasesOf (classes.map (fun cls => cls.map σ)))) := by
  have firstViews := ofConst_related reads firstSupport
  rw [firstFound] at firstViews
  cases targetFound : IndView.ofConst? rightSource (σ first) with
  | none => rw [targetFound] at firstViews; cases firstViews
  | some rightFirst =>
    rw [targetFound] at firstViews
    cases firstViews with
    | some views =>
      refine ⟨rightFirst, targetFound, views, ?_⟩
      dsimp only
      refine ⟨context_fields_related views leftProtect rightProtect _ _ dedup
        leftGroups rightGroups leftAddr rightAddr first, ?_⟩
      apply initialMembers_related hinj classes classSupport _ _ views.params ordered orderedSupport
      intro name member
      exact ofConst_members_related reads (orderedSupport name member)

/-- The exact data crossing from the actual initialization prefix into the
queue. The source view is retained for the final output's universe fields. -/
structure Prepared where
  first : Name
  view : IndView
  context : ExpansionCore.Ctx
  state : XSt

/-- Factoring of the existing prefix only; this is not a runtime replacement.
Both initial empty/missing cases and later member-read errors are preserved. -/
def prepare (protect : Unit → List Lean.Name) (ind? : Name → Option IndView)
    (dedup : Dedup) (ordered : Array Name) (aliases : Std.HashMap Name Name)
    (groups : ExpansionCore.GroupCallback) (keyAddr? : Option (Name → Option _root_.Address)) :
    Except String Prepared := do
  let some first := ordered[0]? | .error "expand: empty block"
  let some view := ind? first | .error (missing first)
  let context := ExpansionHistory.context protect ind? dedup groups keyAddr? first view
  let state ← ExpansionHistory.initialMembers context ordered aliases
  return { first, view, context, state }

/-- Every field of the final Expanded record comes from the same real prefix
and queue result as in production. No output projection is omitted. -/
def finish (prepared : Prepared) (finalState : XSt) : Expanded :=
  { types := finalState.types, auxToNested := finalState.auxToNested,
    auxCtorMap := finalState.auxCtorMap, nOriginals := prepared.state.types.size,
    levelParams := prepared.view.levelParams, nParams := prepared.view.numParams,
    all0 := prepared.context.all0, sourceNames := finalState.sourceNames?.getD [] }

/-- Whole computation equality with the actual generic expansion, including
empty/missing initialization, queue errors and all eight Expanded fields. -/
theorem expand_eq_prepare (protect : Unit → List Lean.Name) (ind? : Name → Option IndView)
    (dedup : Dedup) (ordered : Array Name) (aliases : Std.HashMap Name Name)
    (groups : ExpansionCore.GroupCallback) (keyAddr? : Option (Name → Option _root_.Address)) :
    ExpansionCore.expand protect ind? dedup ordered aliases groups keyAddr? = (do
      let prepared ← prepare protect ind? dedup ordered aliases groups keyAddr?
      let finalState ← ExpansionCore.walkQueue prepared.context expansionBound 0 prepared.state
      pure (finish prepared finalState)) := by
  cases firstFound : ordered[0]? with
  | none => simp only [ExpansionCore.expand, prepare, firstFound]
  | some first =>
    cases viewFound : ind? first with
    | none => simp only [ExpansionCore.expand, prepare, firstFound, viewFound, missing]
    | some view =>
      simp only [ExpansionCore.expand, prepare, firstFound, viewFound,
        ExpansionHistory.context, ExpansionHistory.initialMembers, finish,
        bind_assoc, pure_bind]

structure PreparedRelated (σ : Name → Name) (S : Name → Prop)
    (left right : Prepared) : Prop where
  first : right.first = σ left.first
  views : ReadViewsRelated σ S left.view right.view
  contexts : FirstContextFieldsRelated σ S left.context right.context
  states : StatesRelated σ S left.state right.state

/-- This prefix has exactly the real empty-block or missing-query errors.
It does not equate unrelated queue failures or assume the queue succeeds. -/
inductive PreparationResultRelated (σ : Name → Name) (S : Name → Prop) :
    Except String Prepared → Except String Prepared → Prop
  | ok {left right} : PreparedRelated σ S left right →
      PreparationResultRelated σ S (.ok left) (.ok right)
  | empty : PreparationResultRelated σ S
      (.error "expand: empty block") (.error "expand: empty block")
  | missing (query : Name) : S query → PreparationResultRelated σ S
      (.error (PairedInitializer.missing query)) (.error (PairedInitializer.missing (σ query)))

private theorem PreparationResultRelated.of_members {σ : Name → Name} {S : Name → Prop}
    (first : Name) {leftView rightView : IndView}
    (views : ReadViewsRelated σ S leftView rightView)
    {leftCtx rightCtx : ExpansionCore.Ctx}
    (contexts : FirstContextFieldsRelated σ S leftCtx rightCtx)
    {left right : Except String XSt}
    (members : ResultRelated σ S (StatesRelated σ S) left right) :
    PreparationResultRelated σ S
      (Except.map (fun state => { first, view := leftView, context := leftCtx, state }) left)
      (Except.map (fun state => { first := σ first, view := rightView,
        context := rightCtx, state }) right) := by
  cases members with
  | ok states => exact .ok ⟨rfl, views, contexts, states⟩
  | missing query supported => exact .missing query supported

/-- Complete actual initialization transport, with no first-lookup success,
precomputed alias agreement or initial-state agreement premise. Its raw read
relation remains an internal source-presentation obligation, not an added
premise on the final canonicity theorem. Both protection thunks and all group
and address callbacks remain the actual unrestricted supplied functions. -/
theorem prepare_from_reads {σ : Name → Name} {S : Name → Prop}
    {leftSource rightSource : Name → Option ConstantInfo}
    (reads : ReadsRelated σ S leftSource rightSource)
    (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))
    (classes : Array (Array Name)) (classSupport : ∀ cls ∈ classes, ∀ name ∈ cls, S name)
    (ordered : Array Name) (orderedSupport : ∀ name ∈ ordered, S name)
    (leftProtect rightProtect : Unit → List Lean.Name) (dedup : Dedup)
    (leftGroups rightGroups : ExpansionCore.GroupCallback)
    (leftAddr rightAddr : Option (Name → Option _root_.Address)) :
    PreparationResultRelated σ S
      (prepare leftProtect (IndView.ofConst? leftSource) dedup ordered
        (aliasesOf classes) leftGroups leftAddr)
      (prepare rightProtect (IndView.ofConst? rightSource) dedup (ordered.map σ)
        (aliasesOf (classes.map (fun cls => cls.map σ))) rightGroups rightAddr) := by
  cases firstFound : ordered[0]? with
  | none =>
    simpa only [prepare, firstFound, Array.getElem?_map, Option.map_none] using
      (PreparationResultRelated.empty (σ := σ) (S := S))
  | some first =>
    have supported := orderedSupport first (Array.mem_of_getElem? firstFound)
    have views := ofConst_related reads supported
    generalize leftRead : IndView.ofConst? leftSource first = leftView at views
    generalize rightRead : IndView.ofConst? rightSource (σ first) = rightView at views
    cases views with
    | none =>
      simpa only [prepare, firstFound, Array.getElem?_map, Option.map_some, leftRead, rightRead] using
        (PreparationResultRelated.missing (σ := σ) (S := S) first supported)
    | @some leftFirst rightFirst views =>
      let leftCtx := ExpansionHistory.context leftProtect (IndView.ofConst? leftSource)
        dedup leftGroups leftAddr first leftFirst
      let rightCtx := ExpansionHistory.context rightProtect (IndView.ofConst? rightSource)
        dedup rightGroups rightAddr (σ first) rightFirst
      have contexts : FirstContextFieldsRelated σ S leftCtx rightCtx :=
        context_fields_related views leftProtect rightProtect _ _ dedup
          leftGroups rightGroups leftAddr rightAddr first
      have members := initialMembers_related hinj classes classSupport leftCtx rightCtx
        contexts.params ordered orderedSupport
        (fun name member => ofConst_members_related reads (orderedSupport name member))
      simpa only [prepare, firstFound, Array.getElem?_map, Option.map_some, leftRead, rightRead] using
        (PreparationResultRelated.of_members first views contexts members)

/-- Each side's real initial allocator support is its own fixed protection
thunk; the transported member state cannot substitute a free forbidden set. -/
theorem PreparedRelated.protection {σ : Name → Name} {S : Name → Prop}
    {left right : Prepared} (prepared : PreparedRelated σ S left right) :
    ExpansionHistory.CacheCorrect left.context left.state ∧
      ExpansionHistory.CacheCorrect right.context right.state ∧
      left.state.allocatedNames ++ ExpansionCore.sourceNames left.context left.state =
        left.context.protect () ∧
      right.state.allocatedNames ++ ExpansionCore.sourceNames right.context right.state =
        right.context.protect () :=
  prepared.states.protection left.context right.context

end Ix.CompileCert.Canon.ReaderInitialization
