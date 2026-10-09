import Ix.CompileCert.Canon.QueryArguments
import Ix.CompileCert.Canon.AllocationSteps

/-!
Proof-only factoring and paired transport of the actual nested-query prefix.
Every early return is included. A selected query retains the full external
view and application spine; its continuation is the unchanged key/cache/class
operation, with the original context, state, errors and protection thunk.

The raw reader and name relations are internal simulation obligations, not
new hypotheses on a public canonicity theorem. No successful query, chosen
event alignment, finite callback support or replacement forbidden set is
assumed. This slice does not yet relate the selected continuations: allocation,
class/constructor/queue simulation, collapse and totality remain open.

Uncompiled and unaudited additive source checkpoint.
-/

namespace Ix.CompileCert.Canon.QuerySelection

open Ix.Compile.Canon
open Ix (Name Expr)
open PairedInitializer ReaderInitialization QueryArguments

/-- All data passed from the actual eligibility checks to the continuation.
The queried name is not identified with the external record's stored name. -/
structure Request where
  name : Name
  levels : Array Ix.Level
  args : Array Expr
  external : IndView

def Request.specs (request : Request) (depth : Nat) : Array Expr :=
  (request.args.extract 0 request.external.numParams).map (lowerLoose · depth)

def Request.occurrence (request : Request) (depth : Nat) : Expr :=
  mkAppN (Expr.mkConst request.name request.levels) (request.specs depth)

def Request.rest (request : Request) : Array Expr :=
  request.args.extract request.external.numParams request.args.size

/-- Exactly the six eligibility exits: nonconstant head, known type, absent
view, short spine, no nested reference, or an out-of-scope parameter. -/
def selectHead (ind? : Name → Option IndView) (names : NameSet)
    (head : Expr) (args : Array Expr) (depth : Nat) : Option Request :=
  match head with
  | .const name levels _ =>
    if names.contains name then none else
    match ind? name with
    | none => none
    | some external =>
      if args.size < external.numParams then none else
      if !(args.extract 0 external.numParams).any (mentionsName names.contains) then none else
      if !(args.extract 0 external.numParams).all (looseAtLeast · depth) then none else
      some { name, levels, args, external }
  | _ => none

def select (ind? : Name → Option IndView) (names : NameSet)
    (expression : Expr) (depth : Nat) : Option Request :=
  let (head,args) := getAppFnArgs expression
  selectHead ind? names head args depth

/-- The real continuation after the eligibility checks. In particular the
name predicate is captured before the class loop; key failures keep the first
error, cache hits keep the entire state, and misses run every class attempt.
The actual lazy protection computation stays inside classStep. -/
def resume (cx : ExpansionCore.Ctx) (np : Nat) (owner : Name) (depth : Nat)
    (st : XSt) (request : Request) : Option Expr × XSt := Id.run do
  let specs := request.specs depth
  let original := request.occurrence depth
  let repl := fun aux => mkAppN
    (mkAppN (Expr.mkConst aux cx.blockLevels) (paramArgs np depth)) request.rest
  let names := st.typeNames
  let keyOf := fun expression => match cx.keyAddr? with
    | some addr => addrOccurrence cx.levelParams addr names.contains expression
    | none => .ok (sourceOccurrence expression)
  match keyOf original with
  | .error message => return (none,{ st with keyError := st.keyError.or (some message) })
  | .ok key =>
    if let some aux := st.seen.get? key then return (some (repl aux),st)
    let result ← forIn (m := Id) (cx.groupOf request.external) (st,none)
      (ExpansionHistory.classStep cx owner request.external.numParams request.levels
        specs original keyOf request.name repl)
    return (result.2,result.1)

/-- Full query equality for arbitrary callbacks and arbitrary carried state.
This includes all rejected inputs and every successful/error continuation;
no cache correctness or source/protection premise is needed for factoring. -/
theorem replaceIfNested_eq_select (cx : ExpansionCore.Ctx) (np : Nat) (owner : Name)
    (expression : Expr) (depth : Nat) (st : XSt) :
    ExpansionCore.replaceIfNested cx np owner expression depth st =
      match select cx.ind? st.typeNames expression depth with
      | none => (none,st)
      | some request => resume cx np owner depth st request := by
  rw [ExpansionHistory.replaceIfNested_class_def]
  unfold select
  generalize getAppFnArgs expression = spine
  rcases spine with ⟨head,args⟩
  cases head <;> dsimp only [selectHead]
  all_goals repeat' (first | rfl | split)

/-- The retained source entry is connected to the same full-result factoring,
using its actual source-derived protection thunk rather than new support data. -/
theorem source_replaceIfNested_eq_select (cx : XCtx) (np : Nat) (owner : Name)
    (expression : Expr) (depth : Nat) (st : XSt) :
    replaceIfNested cx np owner expression depth st =
      match select cx.ind? st.typeNames expression depth with
      | none => (none,st)
      | some request => resume (ExpansionCore.Ctx.ofSource cx) np owner depth st request := by
  rw [CoreBridge.replaceIfNested_eq_core]
  exact replaceIfNested_eq_select (ExpansionCore.Ctx.ofSource cx) np owner expression depth st

/-- A rejected eligibility check leaves every state field unchanged, including
warm occurrence/protection caches and an already recorded error. -/
theorem replaceIfNested_rejected (cx : ExpansionCore.Ctx) (np : Nat) (owner : Name)
    (expression : Expr) (depth : Nat) (st : XSt)
    (rejected : select cx.ind? st.typeNames expression depth = none) :
    ExpansionCore.replaceIfNested cx np owner expression depth st = (none,st) := by
  rw [replaceIfNested_eq_select, rejected]

/-- Every selected field and every argument check is related. No successful
reader or query-alignment hypothesis is hidden in this data relation. -/
structure RequestsRelated (σ : Name → Name) (S : Name → Prop)
    (leftNames rightNames : NameSet) (depth : Nat) (left right : Request) : Prop where
  name : right.name = σ left.name
  supported : S left.name
  levels : right.levels = left.levels
  external : ReadViewsRelated σ S left.external right.external
  args : LRel (ERen σ S) left.args.toList right.args.toList
  checks : ArgumentsRelated σ S leftNames.contains rightNames.contains
    left.external.numParams right.external.numParams depth left.args right.args

/-- The relation on all possible callback answers and complete spines derives
the selection relation, including every failed eligibility check. -/
theorem selectHead_related {σ : Name → Name} {S : Name → Prop}
    {R : Lean.Name → Lean.Name → Prop} (names : NameCorrespondence R)
    {leftNames rightNames : NameSet}
    (tables : NameTablesRelated R (fun (_ _ : Unit) => True) leftNames rightNames)
    (references : ∀ name, S name → R (keyName name) (keyName (σ name)))
    {leftRead rightRead : Name → Option IndView}
    (reads : ∀ name, S name → TableResultRelated (ReadViewsRelated σ S)
      (leftRead name) (rightRead (σ name)))
    {leftHead rightHead : Expr} (heads : ERen σ S leftHead rightHead)
    {leftArgs rightArgs : Array Expr}
    (arguments : LRel (ERen σ S) leftArgs.toList rightArgs.toList) (depth : Nat) :
    TableResultRelated (RequestsRelated σ S leftNames rightNames depth)
      (selectHead leftRead leftNames leftHead leftArgs depth)
      (selectHead rightRead rightNames rightHead rightArgs depth) := by
  cases heads with
  | const name levels hash hash' supported =>
    dsimp only [selectHead]
    have membership := tables.contains names (references name supported)
    rw [← membership]
    cases leftNames.contains name with
    | true => exact .none
    | false =>
      dsimp only
      cases reads name supported with
      | none => exact .none
      | @some leftView rightView views =>
        have checks : ArgumentsRelated σ S leftNames.contains rightNames.contains
            leftView.numParams rightView.numParams depth leftArgs rightArgs := by
          rw [views.params]
          exact arguments_related leftNames.contains rightNames.contains
            (fun query member => tables.contains names (references query member))
            arguments leftView.numParams depth
        dsimp only
        simp only [← checks.short, ← checks.mentions, ← checks.scoped]
        split
        · exact .none
        · split
          · exact .none
          · split
            · exact .none
            · exact .some ⟨rfl,supported,rfl,views,arguments,checks⟩
  | _ => exact .none

/-- Actual getAppFnArgs and selection, not a post-hoc chosen pair of successful
queries. The complete Option relation is derived from whole input expressions. -/
theorem select_related {σ : Name → Name} {S : Name → Prop}
    {R : Lean.Name → Lean.Name → Prop} (names : NameCorrespondence R)
    {leftNames rightNames : NameSet}
    (tables : NameTablesRelated R (fun (_ _ : Unit) => True) leftNames rightNames)
    (references : ∀ name, S name → R (keyName name) (keyName (σ name)))
    {leftRead rightRead : Name → Option IndView}
    (reads : ∀ name, S name → TableResultRelated (ReadViewsRelated σ S)
      (leftRead name) (rightRead (σ name)))
    {left right : Expr} (expressions : ERen σ S left right) (depth : Nat) :
    TableResultRelated (RequestsRelated σ S leftNames rightNames depth)
      (select leftRead leftNames left depth) (select rightRead rightNames right depth) := by
  obtain ⟨heads,arguments⟩ := expressions.getAppFnArgs
  exact selectHead_related names tables references reads heads arguments depth

/-- The actual ConstantInfo readers discharge view correspondence, including
missing declarations and each wrong-kind result. Callback support is unrestricted. -/
theorem select_from_reads {σ : Name → Name} {S : Name → Prop}
    {R : Lean.Name → Lean.Name → Prop} (names : NameCorrespondence R)
    {leftNames rightNames : NameSet}
    (tables : NameTablesRelated R (fun (_ _ : Unit) => True) leftNames rightNames)
    (references : ∀ name, S name → R (keyName name) (keyName (σ name)))
    {leftRead rightRead : Name → Option Ix.ConstantInfo}
    (reads : ReadsRelated σ S leftRead rightRead)
    {left right : Expr} (expressions : ERen σ S left right) (depth : Nat) :
    TableResultRelated (RequestsRelated σ S leftNames rightNames depth)
      (select (IndView.ofConst? leftRead) leftNames left depth)
      (select (IndView.ofConst? rightRead) rightNames right depth) :=
  select_related names tables references (fun _ supported => ofConst_related reads supported)
    expressions depth

/-- The actual initializer push folds discharge the name-table relation too.
Raw-source/reference correspondence is retained as an internal enclosing
obligation; it is not asserted to follow from MRen alone. -/
theorem initial_select_from_reads {σ : Name → Name} {S : Name → Prop}
    {R : Lean.Name → Lean.Name → Prop} (names : NameCorrespondence R)
    (references : ∀ name, S name → R (keyName name) (keyName (σ name)))
    {leftState rightState : XSt} (states : StatesRelated σ S leftState rightState)
    {leftRead rightRead : Name → Option Ix.ConstantInfo}
    (reads : ReadsRelated σ S leftRead rightRead)
    {left right : Expr} (expressions : ERen σ S left right) (depth : Nat) :
    TableResultRelated (RequestsRelated σ S leftState.typeNames rightState.typeNames depth)
      (select (IndView.ofConst? leftRead) leftState.typeNames left depth)
      (select (IndView.ofConst? rightRead) rightState.typeNames right depth) :=
  select_from_reads names (states.typeNames names references) references reads expressions depth

/-- Derive the exact lowered occurrence expressions passed to keyOf. This
does not identify raw keys whose binder annotations differ; canonical key
transport and the raw-source case retain their distinct remaining obligations. -/
theorem RequestsRelated.occurrence {σ : Name → Name} {S : Name → Prop}
    {leftNames rightNames : NameSet} {depth : Nat} {left right : Request}
    (requests : RequestsRelated σ S leftNames rightNames depth left right) :
    ERen σ S (left.occurrence depth) (right.occurrence depth) := by
  unfold Request.occurrence Request.specs
  rw [requests.name, requests.levels]
  exact requests.checks.occurrence left.name requests.supported left.levels

/-- The paired query prefix yields either two exact no-op results or two
related requests with their exact complete continuations. No final event,
successful selection or continuation alignment is assumed. The second case
is the concrete remaining interface for allocation/class simulation. -/
theorem paired_query_front {σ : Name → Name} {S : Name → Prop}
    {R : Lean.Name → Lean.Name → Prop} (names : NameCorrespondence R)
    (leftCx rightCx : ExpansionCore.Ctx) (leftNp rightNp : Nat)
    (leftOwner rightOwner : Name) (depth : Nat)
    {leftState rightState : XSt}
    (tables : NameTablesRelated R (fun (_ _ : Unit) => True)
      leftState.typeNames rightState.typeNames)
    (references : ∀ name, S name → R (keyName name) (keyName (σ name)))
    (reads : ∀ name, S name → TableResultRelated (ReadViewsRelated σ S)
      (leftCx.ind? name) (rightCx.ind? (σ name)))
    {left right : Expr} (expressions : ERen σ S left right) :
    (select leftCx.ind? leftState.typeNames left depth = none ∧
      select rightCx.ind? rightState.typeNames right depth = none ∧
      ExpansionCore.replaceIfNested leftCx leftNp leftOwner left depth leftState = (none,leftState) ∧
      ExpansionCore.replaceIfNested rightCx rightNp rightOwner right depth rightState = (none,rightState)) ∨
    ∃ leftRequest rightRequest,
      select leftCx.ind? leftState.typeNames left depth = some leftRequest ∧
      select rightCx.ind? rightState.typeNames right depth = some rightRequest ∧
      RequestsRelated σ S leftState.typeNames rightState.typeNames depth leftRequest rightRequest ∧
      ERen σ S (leftRequest.occurrence depth) (rightRequest.occurrence depth) ∧
      ExpansionCore.replaceIfNested leftCx leftNp leftOwner left depth leftState =
        resume leftCx leftNp leftOwner depth leftState leftRequest ∧
      ExpansionCore.replaceIfNested rightCx rightNp rightOwner right depth rightState =
        resume rightCx rightNp rightOwner depth rightState rightRequest := by
  have selected := select_related names tables references reads expressions depth
  cases leftSelection : select leftCx.ind? leftState.typeNames left depth with
  | none =>
    cases rightSelection : select rightCx.ind? rightState.typeNames right depth with
    | none =>
      exact .inl ⟨rfl,rfl,
        replaceIfNested_rejected leftCx leftNp leftOwner left depth leftState leftSelection,
        replaceIfNested_rejected rightCx rightNp rightOwner right depth rightState rightSelection⟩
    | some request =>
      rw [leftSelection,rightSelection] at selected
      cases selected
  | some leftRequest =>
    cases rightSelection : select rightCx.ind? rightState.typeNames right depth with
    | none =>
      rw [leftSelection,rightSelection] at selected
      cases selected
    | some rightRequest =>
      rw [leftSelection,rightSelection] at selected
      cases selected with
      | some requests =>
        refine .inr ⟨leftRequest,rightRequest,rfl,rfl,requests,requests.occurrence,?_,?_⟩
        · rw [replaceIfNested_eq_select, leftSelection]
        · rw [replaceIfNested_eq_select, rightSelection]

end Ix.CompileCert.Canon.QuerySelection
