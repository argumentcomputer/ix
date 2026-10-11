import Ix.CompileCert.Canon.Rename
import Ix.CompileCert.Canon.SourceAliasScope
import Batteries.Tactic.OpenPrivate

open private Ix.Compile.Canon.canonicalizeConstNames.go from Ix.Compile.Canon.Expr

/-!
Uncompiled proof-only transport of the actual initial alias maps and their
expression walker. The Boolean equality hypothesis is exactly the one already
used by `sortClasses_rename`; there is no structural/cache-faithfulness premise.
Classes may contain empty classes, repeated keys and overlapping classes.

The mapped presentation below fixes class and representative order. Relating
the representatives actually selected by two sorting runs is a separate open
obligation, not a premise discharged by these lemmas.
-/

namespace Ix.CompileCert.Canon.AliasInitialization

open Ix.Compile.Canon
open Ix (Name Expr)

/-- Lookup transport together with the support of values returned on the
original side. Queries outside `S` are unrestricted. -/
structure MapsRelated (σ : Name → Name) (S : Name → Prop)
    (left right : Std.HashMap Name Name) : Prop where
  lookup : ∀ n, S n → right.get? (σ n) = (left.get? n).map σ
  range : ∀ n value, S n → left.get? n = some value → S value

theorem MapsRelated.empty (σ : Name → Name) (S : Name → Prop) :
    MapsRelated σ S ({} : Std.HashMap Name Name) ({} : Std.HashMap Name Name) := by
  constructor
  · intro n member
    simp
  · intro n value member found
    simp at found

/-- Actual hash-map insertions, including overwrite, commute with the
already-promised Boolean equality preservation. No hash equality is inferred
from a structural name comparison. -/
theorem MapsRelated.insert {σ : Name → Name} {S : Name → Prop}
    (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))
    {left right : Std.HashMap Name Name} (maps : MapsRelated σ S left right)
    {name value : Name} (nameIn : S name) (valueIn : S value) :
    MapsRelated σ S (left.insert name value) (right.insert (σ name) (σ value)) := by
  constructor
  · intro query queryIn
    change (right.insert (σ name) (σ value))[σ query]? =
      ((left.insert name value)[query]?).map σ
    rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert,
      hinj name query nameIn queryIn]
    split
    · rfl
    · exact maps.lookup query queryIn
  · intro query output queryIn found
    change (left.insert name value)[query]? = some output at found
    rw [Std.HashMap.getElem?_insert] at found
    split at found
    · cases found
      exact valueIn
    · exact maps.range query output queryIn found

private theorem list_fold_pair {α β γ δ : Type}
    (P : β → δ → Prop) (f : β → α → β) (g : δ → γ → δ) (rename : α → γ)
    (xs : List α) {left : β} {right : δ} (initial : P left right)
    (step : ∀ x ∈ xs, ∀ l r, P l r → P (f l x) (g r (rename x))) :
    P (xs.foldl f left) ((xs.map rename).foldl g right) := by
  induction xs generalizing left right with
  | nil => exact initial
  | cons x xs ih =>
    exact ih (step x List.mem_cons_self left right initial)
      (fun y member l r related => step y (List.mem_cons_of_mem _ member) l r related)

private theorem array_fold_pair {α β γ δ : Type}
    (P : β → δ → Prop) (f : β → α → β) (g : δ → γ → δ) (rename : α → γ)
    (xs : Array α) {left : β} {right : δ} (initial : P left right)
    (step : ∀ x ∈ xs, ∀ l r, P l r → P (f l x) (g r (rename x))) :
    P (xs.foldl f left) ((xs.map rename).foldl g right) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map]
  exact list_fold_pair P f g rename xs.toList initial
    (fun x member l r related => step x (by simpa using member) l r related)

theorem MapsRelated.insertMany {σ : Name → Name} {S : Name → Prop}
    (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))
    {left right : Std.HashMap Name Name} (maps : MapsRelated σ S left right)
    (names : Array Name) (supported : ∀ name ∈ names, S name)
    {value : Name} (valueIn : S value) :
    MapsRelated σ S
      (names.foldl (fun m n => m.insert n value) left)
      ((names.map σ).foldl (fun m n => m.insert n (σ value)) right) := by
  apply array_fold_pair (MapsRelated σ S) _ _ σ names maps
  intro name member l r related
  exact related.insert hinj (supported name member) valueIn

/-- Proof-side factoring of the two actual class folds. `false` excludes the
representative (`aliasesOf`); `true` also inserts it (`origToCanonOf`). -/
private def classStep (includeRep : Bool) (m : Std.HashMap Name Name)
    (cls : Array Name) : Std.HashMap Name Name :=
  match cls[0]? with
  | some rep =>
    let names := if includeRep then cls else cls.extract 1 cls.size
    names.foldl (fun table n => table.insert n rep) m
  | none => m

private theorem classStep_related {σ : Name → Name} {S : Name → Prop}
    (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))
    (includeRep : Bool) (cls : Array Name) (supported : ∀ n ∈ cls, S n)
    {left right : Std.HashMap Name Name} (maps : MapsRelated σ S left right) :
    MapsRelated σ S (classStep includeRep left cls)
      (classStep includeRep right (cls.map σ)) := by
  cases first : cls[0]? with
  | none =>
    simpa only [classStep, first, Array.getElem?_map, Option.map_none] using maps
  | some rep =>
    have repIn : S rep := supported rep (Array.mem_of_getElem? first)
    have selected :
        (if includeRep then cls.map σ else (cls.map σ).extract 1 (cls.map σ).size) =
        (if includeRep then cls else cls.extract 1 cls.size).map σ := by
      cases includeRep <;> simp only [Bool.false_eq_true, ↓reduceIte,
        Array.size_map, Array.map_extract]
    have inClass : ∀ n ∈ (if includeRep then cls else cls.extract 1 cls.size), S n := by
      intro n member
      cases includeRep with
      | true => exact supported n member
      | false =>
        obtain ⟨i, bound, equal⟩ := Array.mem_extract_iff_getElem.mp member
        rw [← equal]
        exact supported _ (Array.getElem_mem (by omega))
    simpa only [classStep, first, Array.getElem?_map, Option.map_some, selected] using
      maps.insertMany hinj (if includeRep then cls else cls.extract 1 cls.size) inClass repIn

private theorem classFold_related {σ : Name → Name} {S : Name → Prop}
    (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))
    (includeRep : Bool) (classes : Array (Array Name))
    (supported : ∀ cls ∈ classes, ∀ n ∈ cls, S n) :
    MapsRelated σ S
      (classes.foldl (classStep includeRep) {})
      ((classes.map (fun cls => cls.map σ)).foldl (classStep includeRep) {}) := by
  apply array_fold_pair (MapsRelated σ S) _ _ (fun cls => cls.map σ)
    classes (MapsRelated.empty σ S)
  intro cls member left right maps
  exact classStep_related hinj includeRep cls (supported cls member) maps

/-- The production alias builder itself establishes lookup correspondence;
there is no alias-map correspondence premise. Ordered class overlap and
repeated aliases retain the real last-insertion behavior. -/
theorem aliasesOf_related {σ : Name → Name} {S : Name → Prop}
    (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))
    (classes : Array (Array Name)) (supported : ∀ cls ∈ classes, ∀ n ∈ cls, S n) :
    MapsRelated σ S (aliasesOf classes)
      (aliasesOf (classes.map (fun cls => cls.map σ))) := by
  exact classFold_related hinj false classes supported

/-- The same argument covers the actual map consumed by source-to-canonical
restoration, including its representative self-entries. -/
theorem origToCanonOf_related {σ : Name → Name} {S : Name → Prop}
    (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))
    (classes : Array (Array Name)) (supported : ∀ cls ∈ classes, ∀ n ∈ cls, S n) :
    MapsRelated σ S (origToCanonOf classes)
      (origToCanonOf (classes.map (fun cls => cls.map σ))) := by
  exact classFold_related hinj true classes supported

/-- A separate actual-producer specialization: every alias value is in the
precise protected list computed for this expansion. `S` above is not being
substituted for the allocator's forbidden set. The callback-generic transport
theorems neither need nor assert finite support for arbitrary callbacks. -/
theorem aliasValue_actualProtected (source : Ix.Environment)
    (groups : Std.HashMap Name (Array (Array Name))) (classes : Array (Array Name))
    {query value : Name} (found : (aliasesOf classes).get? query = some value) :
    keyName value ∈ (sourceContext source (repsOf classes) groups).protectedNames :=
  (sourceContext_reachable_done source (repsOf classes) groups
    (SourceReach.alias_value source groups classes found)).1

/-- On actual producer inputs, a transported alias value is protected on
both sides by those exact source contexts. This proves the alias-value part
of supported correspondence, not closure of all records read by expansion. -/
theorem aliasValue_pairedActualProtected {σ : Name → Name} {S : Name → Prop}
    (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))
    (classes : Array (Array Name)) (supported : ∀ cls ∈ classes, ∀ n ∈ cls, S n)
    (leftSource rightSource : Ix.Environment)
    (leftGroups rightGroups : Std.HashMap Name (Array (Array Name)))
    {query value : Name} (queryIn : S query)
    (found : (aliasesOf classes).get? query = some value) :
    (aliasesOf (classes.map (fun cls => cls.map σ))).get? (σ query) = some (σ value) ∧
      keyName value ∈ (sourceContext leftSource (repsOf classes) leftGroups).protectedNames ∧
      keyName (σ value) ∈ (sourceContext rightSource
        (repsOf (classes.map (fun cls => cls.map σ))) rightGroups).protectedNames := by
  have transported := (aliasesOf_related hinj classes supported).lookup query queryIn
  have found' : (aliasesOf (classes.map (fun cls => cls.map σ))).get? (σ query) =
      some (σ value) := by
    simpa only [found, Option.map_some] using transported
  exact ⟨found', aliasValue_actualProtected leftSource leftGroups classes found,
    aliasValue_actualProtected rightSource rightGroups
      (classes.map (fun cls => cls.map σ)) found'⟩

private theorem const_related {σ : Name → Name} {S : Name → Prop}
    {left right : Std.HashMap Name Name} (maps : MapsRelated σ S left right)
    (n : Name) (levels : Array Ix.Level) (h h' : Address) (member : S n) :
    ERen σ S (canonicalizeConstNames left (.const n levels h))
      (canonicalizeConstNames right (.const (σ n) levels h')) := by
  have transported := maps.lookup n member
  cases found : left.get? n with
  | none =>
    have found' : right.get? (σ n) = none := by simpa only [found, Option.map_none] using transported
    unfold canonicalizeConstNames
    cases leftEmpty : left.isEmpty <;> cases rightEmpty : right.isEmpty <;>
      simp only [Bool.false_eq_true, ↓reduceIte,
        Ix.Compile.Canon.canonicalizeConstNames.go, found, found']
    all_goals exact .const _ _ _ _ member
  | some value =>
    have found' : right.get? (σ n) = some (σ value) := by
      simpa only [found, Option.map_some] using transported
    have leftNotEmpty : left.isEmpty = false := by
      cases empty : left.isEmpty with
      | false => rfl
      | true =>
        have absent := Std.HashMap.getElem?_of_isEmpty (m := left) (a := n) empty
        change left.get? n = none at absent
        rw [found] at absent
        cases absent
    have rightNotEmpty : right.isEmpty = false := by
      cases empty : right.isEmpty with
      | false => rfl
      | true =>
        have absent := Std.HashMap.getElem?_of_isEmpty (m := right) (a := σ n) empty
        change right.get? (σ n) = none at absent
        rw [found'] at absent
        cases absent
    simp only [canonicalizeConstNames, leftNotEmpty, rightNotEmpty,
      Bool.false_eq_true, ↓reduceIte,
      Ix.Compile.Canon.canonicalizeConstNames.go, found, found']
    exact .const _ _ _ _ (maps.range n value member found)

/-- Transport the actual constant-only walker. Empty/nonempty map branches
may differ; unchanged projection heads, metadata, binder annotations, loose
variables, and the let nondependency bit retain the original `ERen` domain. -/
theorem canonicalize_related {σ : Name → Name} {S : Name → Prop}
    {left right : Std.HashMap Name Name} (maps : MapsRelated σ S left right)
    {e e' : Expr} (expressions : ERen σ S e e') :
    ERen σ S (canonicalizeConstNames left e) (canonicalizeConstNames right e') := by
  cases leftEmpty : left.isEmpty <;> cases rightEmpty : right.isEmpty
  all_goals
    induction expressions with
    | const n levels h h' member =>
      exact const_related maps n levels h h' member
    | _ =>
      simp only [canonicalizeConstNames, leftEmpty, rightEmpty,
        Bool.false_eq_true, ↓reduceIte,
        Ix.Compile.Canon.canonicalizeConstNames.go] at *
      constructor <;> assumption

/-- Raw related source bodies are still related after the initializer's
actual alias construction and actual expression rewrite. The old name
equality condition and class support discharge both map invariants above. -/
theorem canonicalAliases_related {σ : Name → Name} {S : Name → Prop}
    (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))
    (classes : Array (Array Name)) (supported : ∀ cls ∈ classes, ∀ n ∈ cls, S n)
    {e e' : Expr} (expressions : ERen σ S e e') :
    ERen σ S (canonicalizeConstNames (aliasesOf classes) e)
      (canonicalizeConstNames (aliasesOf (classes.map (fun cls => cls.map σ))) e') :=
  canonicalize_related (aliasesOf_related hinj classes supported) expressions

/-- For the classes the sorter actually returns, the alias support condition
is inherited from the original member/key support hypothesis. This is not a
new requirement on a caller-supplied alias table. -/
theorem sortClasses_supported {rules : Rules} (hpf : rules.portFixes = true)
    {addr? : Name → Option Address} (hA : AddrCongr addr?)
    {sources : List Ix.MutConst} (hk : KeysDistinct sources)
    {S : Name → Prop} (hS : ∀ m ∈ sources, ∀ n ∈ keysOf m, S n)
    {classes : List (List Ix.MutConst)} {stats : SortStats}
    (run : sortClasses rules addr? sources = .ok (classes, stats)) :
    ∀ cls ∈ classNames classes, ∀ n ∈ cls, S n := by
  have actual := sortClasses_eq hpf hA hk
  rw [run] at actual
  have pureRun : sortClassesP rules addr? sources = .ok classes := by
    simpa only [Except.map] using actual.symm
  have partition := (sortClassesP_coarsest rules hA hk pureRun).1
  intro cls classIn n nameIn
  change cls ∈ classes.toArray.map (fun c => c.toArray.map Ix.MutConst.name) at classIn
  obtain ⟨members, membersIn, rfl⟩ := Array.mem_map.mp classIn
  obtain ⟨member, memberIn, rfl⟩ := Array.mem_map.mp nameIn
  have memberOfSources : member ∈ sources := partition.1.mem_iff.mp
    (List.mem_flatten.mpr ⟨members, by simpa using membersIn, by simpa using memberIn⟩)
  exact hS member memberOfSources member.name (by simp only [keysOf, List.mem_cons_self])

/-- Actual sorter output plus the existing renaming hypotheses suffice for
the alias-normalized body relation. The second array is the ordered mapped
presentation; no result from a second sorting run is identified here. -/
theorem sortClasses_canonicalAliases_related
    {rules : Rules} (hpf : rules.portFixes = true)
    {addr? : Name → Option Address} (hA : AddrCongr addr?)
    {sources : List Ix.MutConst} (hk : KeysDistinct sources)
    {σ : Name → Name} {S : Name → Prop}
    (hS : ∀ m ∈ sources, ∀ n ∈ keysOf m, S n)
    (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))
    {classes : List (List Ix.MutConst)} {stats : SortStats}
    (run : sortClasses rules addr? sources = .ok (classes, stats))
    {e e' : Expr} (expressions : ERen σ S e e') :
    ERen σ S (canonicalizeConstNames (aliasesOf (classNames classes)) e)
      (canonicalizeConstNames
        (aliasesOf ((classNames classes).map (fun cls => cls.map σ))) e') :=
  canonicalAliases_related hinj (classNames classes)
    (sortClasses_supported hpf hA hk hS run) expressions

end Ix.CompileCert.Canon.AliasInitialization
