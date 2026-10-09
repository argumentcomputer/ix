import Ix.CompileCert.Canon.InitialSourceSupport

/-!
Proof-only transport of the actual nested-query membership and argument
checks. The production walker is `mentionsName` over structural NameTable
lookup; the older HashSet/isEmpty lemma is not used as its replacement.

Every argument position, the short-spine branch, both Boolean tests, lowered
specialization arguments and the remaining application spine are retained.
The raw reader endpoint preserves both missing/wrong-kind and present views.
It does not assume a successful query or aligned allocation events.

The name correspondence and raw source relation remain internal obligations
of the paired run, not new premises on a public endpoint. This slice neither
derives them from MRen alone nor proves the full query/queue/collapse theorem.
Protection thunks, callbacks and all public theorem domains are unchanged.
Uncompiled and unaudited source checkpoint.
-/

namespace Ix.CompileCert.Canon.QueryArguments

open Ix.Compile.Canon
open Ix (Name Expr)
open PairedInitializer ReaderInitialization

private theorem map_related {α β γ δ : Type} {R : α → β → Prop}
    {T : γ → δ → Prop} {left : List α} {right : List β}
    (related : LRel R left right) (f : α → γ) (g : β → δ)
    (each : ∀ a b, R a b → T (f a) (g b)) :
    LRel T (left.map f) (right.map g) := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (each _ _ head) ih

private theorem take_related {α β : Type} {R : α → β → Prop}
    {left : List α} {right : List β} (related : LRel R left right) (count : Nat) :
    LRel R (left.take count) (right.take count) := by
  induction related generalizing count with
  | nil => simpa only [List.take_nil] using (LRel.nil (Rel := R))
  | cons head tail ih =>
    cases count with
    | zero => exact .nil
    | succ count => exact .cons head (ih count)

private theorem drop_related {α β : Type} {R : α → β → Prop}
    {left : List α} {right : List β} (related : LRel R left right) (count : Nat) :
    LRel R (left.drop count) (right.drop count) := by
  induction related generalizing count with
  | nil => simpa only [List.drop_nil] using (LRel.nil (Rel := R))
  | cons head tail ih =>
    cases count with
    | zero => exact .cons head tail
    | succ count => exact ih count

private theorem extract_related {α β : Type} {R : α → β → Prop}
    {left : Array α} {right : Array β}
    (related : LRel R left.toList right.toList) (start stop : Nat) :
    LRel R (left.extract start stop).toList (right.extract start stop).toList := by
  simp only [Array.toList_extract, List.extract_eq_take_drop]
  exact take_related (drop_related related start) (stop - start)

private theorem any_related {α β : Type} {R : α → β → Prop}
    {left : List α} {right : List β} (related : LRel R left right)
    (p : α → Bool) (q : β → Bool) (each : ∀ a b, R a b → p a = q b) :
    left.any p = right.any q := by
  induction related with
  | nil => rfl
  | cons head tail ih => simp only [List.any_cons, each _ _ head, ih]

private theorem all_related {α β : Type} {R : α → β → Prop}
    {left : List α} {right : List β} (related : LRel R left right)
    (p : α → Bool) (q : β → Bool) (each : ∀ a b, R a b → p a = q b) :
    left.all p = right.all q := by
  induction related with
  | nil => rfl
  | cons head tail ih => simp only [List.all_cons, each _ _ head, ih]

/-- The real production traversal reads constant and projection heads and
recurses through every body, retaining the source ERen domain. It needs no
HashSet emptiness or expression-hash fact. -/
theorem mentionsName_related {σ : Name → Name} {S : Name → Prop}
    {left right : Expr} (expressions : ERen σ S left right)
    (leftPresent rightPresent : Name → Bool)
    (names : ∀ n, S n → leftPresent n = rightPresent (σ n)) :
    mentionsName leftPresent left = mentionsName rightPresent right := by
  induction expressions <;> simp only [mentionsName, *]

/-- Actual structural table lookup supplies the pointwise name test above.
Neither table's cached hash hint is assumed to agree with the other. -/
theorem mentionsName_tables {σ : Name → Name} {S : Name → Prop}
    {R : Lean.Name → Lean.Name → Prop} (names : NameCorrespondence R)
    {leftTable rightTable : NameSet}
    (tables : NameTablesRelated R (fun (_ _ : Unit) => True) leftTable rightTable)
    (references : ∀ n, S n → R (keyName n) (keyName (σ n)))
    {left right : Expr} (expressions : ERen σ S left right) :
    mentionsName leftTable.contains left = mentionsName rightTable.contains right :=
  mentionsName_related expressions leftTable.contains rightTable.contains
    (fun n supported => tables.contains names (references n supported))

/-- The exact argument facts consumed by replaceIfNested. A too-short input
is included; no telescope/arity lower bound is a premise. -/
structure ArgumentsRelated (σ : Name → Name) (S : Name → Prop)
    (leftPresent rightPresent : Name → Bool) (leftCount rightCount depth : Nat)
    (left right : Array Expr) : Prop where
  count : rightCount = leftCount
  size : right.size = left.size
  short : (left.size < leftCount) ↔ (right.size < rightCount)
  mentions : (left.extract 0 leftCount).any (mentionsName leftPresent) =
    (right.extract 0 rightCount).any (mentionsName rightPresent)
  scoped : (left.extract 0 leftCount).all (looseAtLeast · depth) =
    (right.extract 0 rightCount).all (looseAtLeast · depth)
  specs : LRel (ERen σ S)
    ((left.extract 0 leftCount).map (lowerLoose · depth)).toList
    ((right.extract 0 rightCount).map (lowerLoose · depth)).toList
  rest : LRel (ERen σ S) (left.extract leftCount left.size).toList
    (right.extract rightCount right.size).toList

/-- Related whole spines derive every query argument check and every emitted
argument. Extraction truncates in exactly the same way on both sides. -/
theorem arguments_related {σ : Name → Name} {S : Name → Prop}
    (leftPresent rightPresent : Name → Bool)
    (names : ∀ n, S n → leftPresent n = rightPresent (σ n))
    {left right : Array Expr} (arguments : LRel (ERen σ S) left.toList right.toList)
    (count depth : Nat) :
    ArgumentsRelated σ S leftPresent rightPresent count count depth left right := by
  have sizes : right.size = left.size := by simpa using arguments.length
  have params := extract_related arguments 0 count
  refine ⟨rfl, sizes, by rw [sizes], ?_, ?_, ?_, ?_⟩
  · rw [← Array.any_toList, ← Array.any_toList]
    exact any_related params (mentionsName leftPresent) (mentionsName rightPresent)
      (fun _ _ related => mentionsName_related related leftPresent rightPresent names)
  · rw [← Array.all_toList, ← Array.all_toList]
    exact all_related params (looseAtLeast · depth) (looseAtLeast · depth)
      (fun _ _ related => related.looseAtLeast depth)
  · simp only [Array.toList_map]
    exact map_related params (lowerLoose · depth) (lowerLoose · depth)
      (fun _ _ related => related.lowerLoose depth 0)
  · rw [sizes]
    exact extract_related arguments count left.size

/-- The real getAppFnArgs supplies the complete spine relation, not a zipped
prefix chosen after successful allocation. The head relation is retained. -/
theorem spine_arguments_related {σ : Name → Name} {S : Name → Prop}
    {R : Lean.Name → Lean.Name → Prop} (names : NameCorrespondence R)
    {leftTable rightTable : NameSet}
    (tables : NameTablesRelated R (fun (_ _ : Unit) => True) leftTable rightTable)
    (references : ∀ n, S n → R (keyName n) (keyName (σ n)))
    {left right : Expr} (expressions : ERen σ S left right) (count depth : Nat) :
    ERen σ S (getAppFnArgs left).1 (getAppFnArgs right).1 ∧
      ArgumentsRelated σ S leftTable.contains rightTable.contains count count depth
        (getAppFnArgs left).2 (getAppFnArgs right).2 := by
  obtain ⟨head, arguments⟩ := expressions.getAppFnArgs
  exact ⟨head, arguments_related leftTable.contains rightTable.contains
    (fun n supported => tables.contains names (references n supported)) arguments count depth⟩

/-- The actual raw reader derives the external parameter count as well as the
complete argument relation. Missing and wrong-kind declarations remain paired
None; there is no accepted-view/parameter-equality premise. -/
theorem read_arguments_related {σ : Name → Name} {S : Name → Prop}
    {R : Lean.Name → Lean.Name → Prop} (names : NameCorrespondence R)
    {leftTable rightTable : NameSet}
    (tables : NameTablesRelated R (fun (_ _ : Unit) => True) leftTable rightTable)
    (references : ∀ n, S n → R (keyName n) (keyName (σ n)))
    {leftRead rightRead : Name → Option Ix.ConstantInfo}
    (reads : ReadsRelated σ S leftRead rightRead) {query : Name} (supported : S query)
    {leftArgs rightArgs : Array Expr}
    (arguments : LRel (ERen σ S) leftArgs.toList rightArgs.toList) (depth : Nat) :
    TableResultRelated (fun left right => ReadViewsRelated σ S left right ∧
      ArgumentsRelated σ S leftTable.contains rightTable.contains
        left.numParams right.numParams depth leftArgs rightArgs)
      (IndView.ofConst? leftRead query) (IndView.ofConst? rightRead (σ query)) := by
  cases ofConst_related reads supported with
  | none => exact .none
  | some views =>
    refine .some ⟨views, ?_⟩
    rw [views.params]
    exact arguments_related leftTable.contains rightTable.contains
      (fun n member => tables.contains names (references n member)) arguments _ depth

/-- Name-table correspondence is derived from the actual initializer push
fold before it is used by the raw-reader/query facts. The remaining reference
correspondence is explicitly the original-source bridge still to discharge. -/
theorem initial_read_arguments_related {σ : Name → Name} {S : Name → Prop}
    {R : Lean.Name → Lean.Name → Prop} (names : NameCorrespondence R)
    (references : ∀ n, S n → R (keyName n) (keyName (σ n)))
    {leftState rightState : XSt} (states : StatesRelated σ S leftState rightState)
    {leftRead rightRead : Name → Option Ix.ConstantInfo}
    (reads : ReadsRelated σ S leftRead rightRead) {query : Name} (supported : S query)
    {leftArgs rightArgs : Array Expr}
    (arguments : LRel (ERen σ S) leftArgs.toList rightArgs.toList) (depth : Nat) :
    TableResultRelated (fun left right => ReadViewsRelated σ S left right ∧
      ArgumentsRelated σ S leftState.typeNames.contains rightState.typeNames.contains
        left.numParams right.numParams depth leftArgs rightArgs)
      (IndView.ofConst? leftRead query) (IndView.ofConst? rightRead (σ query)) :=
  read_arguments_related names (states.typeNames names references) references
    reads supported arguments depth

/-- Reconstruct the actual key input from the lowered parameter slice. The
normalization/captured-address proof can consume this ERen directly. -/
theorem ArgumentsRelated.occurrence {σ : Name → Name} {S : Name → Prop}
    {leftPresent rightPresent : Name → Bool} {leftCount rightCount depth : Nat}
    {left right : Array Expr}
    (arguments : ArgumentsRelated σ S leftPresent rightPresent leftCount rightCount depth left right)
    (query : Name) (supported : S query) (levels : Array Ix.Level) :
    ERen σ S
      (mkAppN (Expr.mkConst query levels) ((left.extract 0 leftCount).map (lowerLoose · depth)))
      (mkAppN (Expr.mkConst (σ query) levels) ((right.extract 0 rightCount).map (lowerLoose · depth))) :=
  (ERen.const query levels _ _ supported).mkAppN arguments.specs

end Ix.CompileCert.Canon.QueryArguments
