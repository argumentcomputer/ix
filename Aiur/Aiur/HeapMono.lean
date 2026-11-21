import Aiur.Memory.Encoding
import Aiur.Memory.Representation
import Aiur.Generic.SourceSemantics

/-!
# Heap Monotonicity for Concrete and Generic Source Semantics

In `Aiur`, heap memory is append-only (`store` appends a single cell to the end
of `Heap F` and returns `.ptr input.type middle.length`). Consequently:
1. Every concrete (`Aiur.EvalExpr`, `Aiur.EvalArgs`, `Aiur.EvalFn`) and generic
   (`Generic.SourceSemantics.EvalExpr`, `EvalArgs`, `EvalFn`, `EvalExit`,
   `EvalArgsExit`) evaluation satisfies `Heap.Extends before after`.
2. Any representation predicate built from constants, conjunctions,
   disjunctions, quantifiers, pointer dereferences (`h[addr]? = some v`),
   and inductive heap data structures (linked lists, binary trees) is
   monotone with respect to `Heap.Extends` (`HeapMono`).
-/

namespace Aiur

variable {F : Type}

/-! ### 1. `Heap.Extends` and Basic Properties -/

/-- `Heap.Extends h₁ h₂` holds when `h₂` is obtained by appending zero or more
newly allocated cells to `h₁`. -/
def Heap.Extends (h₁ h₂ : Heap F) : Prop :=
  ∃ s : Heap F, h₂ = h₁ ++ s

namespace Heap.Extends

theorem iff_isPrefix {h₁ h₂ : Heap F} :
    Heap.Extends h₁ h₂ ↔ h₁ <+: h₂ := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl⟩

@[refl]
theorem refl (h : Heap F) : Heap.Extends h h :=
  ⟨[], (List.append_nil h).symm⟩

theorem trans {h₁ h₂ h₃ : Heap F}
    (e₁₂ : Heap.Extends h₁ h₂) (e₂₃ : Heap.Extends h₂ h₃) :
    Heap.Extends h₁ h₃ := by
  rcases e₁₂ with ⟨s₁, rfl⟩
  rcases e₂₃ with ⟨s₂, rfl⟩
  exact ⟨s₁ ++ s₂, List.append_assoc h₁ s₁ s₂⟩

theorem append_right (h s : Heap F) : Heap.Extends h (h ++ s) :=
  ⟨s, rfl⟩

theorem snoc (h : Heap F) (v : SourceValue F) : Heap.Extends h (h ++ [v]) :=
  ⟨[v], rfl⟩

theorem nil (h : Heap F) : Heap.Extends [] h :=
  ⟨h, rfl⟩

theorem length_le {h₁ h₂ : Heap F} (ext : Heap.Extends h₁ h₂) :
    h₁.length ≤ h₂.length := by
  rcases ext with ⟨s, rfl⟩
  simp

theorem getElem?_eq {h₁ h₂ : Heap F} {i : Nat} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (found : h₁[i]? = some v) :
    h₂[i]? = some v :=
  heap_get_of_prefix (iff_isPrefix.mp ext) found

theorem loadValue_eq {h₁ h₂ : Heap F} {ptr v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (loaded : loadValue h₁ ptr = .ok v) :
    loadValue h₂ ptr = .ok v := by
  cases ptr with
  | field | tuple | construct => cases loaded
  | ptr target addr =>
      cases found : h₁[addr]? with
      | none => simp [loadValue, found] at loaded
      | some stored =>
          have found₂ := ext.getElem?_eq found
          simpa [loadValue, found, found₂] using loaded

end Heap.Extends

/-! ### 2. Concrete Evaluation Heap Monotonicity (`Aiur.Semantics`) -/

theorem EvalExpr.heap_extends [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F Nat} {expr : Expr F} {before after : Heap F} {value : SourceValue F}
    (evaluated : EvalExpr program locals expr before value after) :
    Heap.Extends before after :=
  Heap.Extends.iff_isPrefix.mpr evaluated.grows

theorem EvalArgs.heap_extends [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F Nat} {exprs : List (Expr F)} {before after : Heap F}
    {values : List (SourceValue F)}
    (evaluated : EvalArgs program locals exprs before values after) :
    Heap.Extends before after :=
  Heap.Extends.iff_isPrefix.mpr evaluated.grows

theorem EvalFn.heap_extends [Field F] [DecidableEq F] {program : Program F}
    {name : String} {args : List (SourceValue F)} {before after : Heap F} {value : SourceValue F}
    (evaluated : EvalFn program name args before value after) :
    Heap.Extends before after :=
  Heap.Extends.iff_isPrefix.mpr evaluated.grows

/-! ### 3. Generic Source Evaluation Heap Monotonicity (`Aiur.Generic.SourceSemantics`) -/

namespace Generic.SourceSemantics

variable [Field F] [DecidableEq F] {world : World F}

theorem EvalExpr.heap_extends
    {types : Types} {locals : Environment F Nat} {expr : Expr F}
    {before after : Heap F} {result : SourceValue F}
    (evaluated : EvalExpr world types locals expr before result after) :
    Heap.Extends before after := by
  induction evaluated using EvalExpr.rec
    (motive_2 := fun _ _ _ before _ after _ => Heap.Extends before after)
    (motive_3 := fun _ _ before _ after _ => Heap.Extends before after)
    (motive_4 := fun _ _ _ before _ _ after _ => Heap.Extends before after)
    (motive_5 := fun _ _ _ before _ _ after _ => Heap.Extends before after) with
  | literal | var | nil =>
      exact Heap.Extends.refl _
  | block _ ih
  | blockExit _ ih
  | global _ _ _ ih
  | tuple _ ih
  | array _ ih
  | «repeat» _ ih
  | index _ _ ih
  | slice _ _ ih
  | builtin _ _ ih
  | update _ _ ih
  | record _ ih
  | member _ _ ih
  | construct _ ih
  | constructAs _ ih
  | project _ _ ih
  | load _ _ ih
  | hint _ _ ih
  | neg _ _ ih
  | intro _ _ ih
  | returned _ _ ih
  | exit _ ih
  | exitPayload _ ih
  | fromBlock _ _ ih
  | fromGlobal _ _ _ ih
  | fromTuple _ ih
  | fromArray _ ih
  | fromRepeat _ ih
  | fromIndex _ ih
  | fromSlice _ ih
  | fromBuiltin _ ih
  | fromUpdate _ ih
  | fromRecord _ ih
  | fromMember _ ih
  | fromConstruct _ ih
  | fromConstructAs _ ih
  | fromProject _ ih
  | fromLetValue _ ih
  | fromStore _ ih
  | fromLoad _ ih
  | fromHint _ ih
  | fromNeg _ ih
  | binaryLeft _ ih
  | fromCall _ ih
  | fromMatchValue _ ih
  | head _ ih =>
      exact ih
  | letValue _ _ _ ih₁ ih₂
  | binary _ _ _ ih₁ ih₂
  | call _ _ ih₁ ih₂
  | matchValue _ _ _ ih₁ ih₂
  | cons _ _ ih₁ ih₂
  | letBody _ _ _ ih₁ ih₂
  | binaryRight _ _ ih₁ ih₂
  | matchBody _ _ _ ih₁ ih₂
  | tail _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | store _ ih =>
      exact ih.trans (Heap.Extends.snoc _ _)

theorem EvalArgs.heap_extends
    {types : Types} {locals : Environment F Nat} {exprs : List (Expr F)}
    {before after : Heap F} {values : List (SourceValue F)}
    (evaluated : EvalArgs world types locals exprs before values after) :
    Heap.Extends before after :=
  (EvalExpr.tuple evaluated).heap_extends

theorem EvalExit.heap_extends
    {types : Types} {locals : Environment F Nat} {expr : Expr F}
    {before after : Heap F} {target : ExitTarget} {result : SourceValue F}
    (evaluated : EvalExit world types locals expr before target result after) :
    Heap.Extends before after := by
  induction evaluated using EvalExit.rec
    (motive_1 := fun _ _ _ before _ after _ => Heap.Extends before after)
    (motive_2 := fun _ _ _ before _ after _ => Heap.Extends before after)
    (motive_3 := fun _ _ before _ after _ => Heap.Extends before after)
    (motive_5 := fun _ _ _ before _ _ after _ => Heap.Extends before after) with
  | literal | var | nil =>
      exact Heap.Extends.refl _
  | block _ ih
  | blockExit _ ih
  | global _ _ _ ih
  | tuple _ ih
  | array _ ih
  | «repeat» _ ih
  | index _ _ ih
  | slice _ _ ih
  | builtin _ _ ih
  | update _ _ ih
  | record _ ih
  | member _ _ ih
  | construct _ ih
  | constructAs _ ih
  | project _ _ ih
  | load _ _ ih
  | hint _ _ ih
  | neg _ _ ih
  | intro _ _ ih
  | returned _ _ ih
  | exit _ ih
  | exitPayload _ ih
  | fromBlock _ _ ih
  | fromGlobal _ _ _ ih
  | fromTuple _ ih
  | fromArray _ ih
  | fromRepeat _ ih
  | fromIndex _ ih
  | fromSlice _ ih
  | fromBuiltin _ ih
  | fromUpdate _ ih
  | fromRecord _ ih
  | fromMember _ ih
  | fromConstruct _ ih
  | fromConstructAs _ ih
  | fromProject _ ih
  | fromLetValue _ ih
  | fromStore _ ih
  | fromLoad _ ih
  | fromHint _ ih
  | fromNeg _ ih
  | binaryLeft _ ih
  | fromCall _ ih
  | fromMatchValue _ ih
  | head _ ih =>
      exact ih
  | letValue _ _ _ ih₁ ih₂
  | binary _ _ _ ih₁ ih₂
  | call _ _ ih₁ ih₂
  | matchValue _ _ _ ih₁ ih₂
  | cons _ _ ih₁ ih₂
  | letBody _ _ _ ih₁ ih₂
  | binaryRight _ _ ih₁ ih₂
  | matchBody _ _ _ ih₁ ih₂
  | tail _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | store _ ih =>
      exact ih.trans (Heap.Extends.snoc _ _)

theorem EvalFn.heap_extends
    {name : String} {args : List (SourceValue F)}
    {before after : Heap F} {result : SourceValue F}
    (evaluated : EvalFn world name args before result after) :
    Heap.Extends before after := by
  cases evaluated with
  | intro _ body => exact body.heap_extends
  | returned _ body => exact body.heap_extends

theorem EvalArgsExit.heap_extends
    {types : Types} {locals : Environment F Nat} {exprs : List (Expr F)}
    {before after : Heap F} {target : ExitTarget} {result : SourceValue F}
    (evaluated : EvalArgsExit world types locals exprs before target result after) :
    Heap.Extends before after :=
  (EvalExit.fromTuple evaluated).heap_extends

abbrev EvalList := @EvalArgs
abbrev EvalFields := @EvalArgs
abbrev EvalPath := @EvalArgs

theorem EvalList.heap_extends
    {types : Types} {locals : Environment F Nat} {exprs : List (Expr F)}
    {before after : Heap F} {values : List (SourceValue F)}
    (evaluated : EvalList world types locals exprs before values after) :
    Heap.Extends before after :=
  EvalArgs.heap_extends evaluated

theorem EvalFields.heap_extends
    {types : Types} {locals : Environment F Nat} {exprs : List (Expr F)}
    {before after : Heap F} {values : List (SourceValue F)}
    (evaluated : EvalFields world types locals exprs before values after) :
    Heap.Extends before after :=
  EvalArgs.heap_extends evaluated

theorem EvalPath.heap_extends
    {types : Types} {locals : Environment F Nat} {exprs : List (Expr F)}
    {before after : Heap F} {values : List (SourceValue F)}
    (evaluated : EvalPath world types locals exprs before values after) :
    Heap.Extends before after :=
  EvalArgs.heap_extends evaluated

end Generic.SourceSemantics

/-! ### 4. `HeapMono` Predicate Combinators and Inductive Heap Structures -/

/-- A heap-indexed predicate `P : Heap F → α → Prop` is monotone (`HeapMono P`) if
extending the heap preserves `P`. -/
def HeapMono {α : Type*} (P : Heap F → α → Prop) : Prop :=
  ∀ ⦃h₁ h₂ : Heap F⦄ ⦃x : α⦄, Heap.Extends h₁ h₂ → P h₁ x → P h₂ x

/-- A binary heap-indexed relation `R : Heap F → α → β → Prop` (such as a representation
relation between a mathematical value `x : α` and a `SourceValue F` `v : β`) is
monotone (`HeapMono₂ R`) if extending the heap preserves `R`. -/
def HeapMono₂ {α β : Type*} (R : Heap F → α → β → Prop) : Prop :=
  ∀ ⦃h₁ h₂ : Heap F⦄ ⦃x : α⦄ ⦃y : β⦄, Heap.Extends h₁ h₂ → R h₁ x y → R h₂ x y

namespace HeapMono

variable {α β : Type*}

theorem of_heapMono₂ {R : Heap F → α → β → Prop} (hR : HeapMono₂ R) (x : α) :
    HeapMono (fun h y => R h x y) :=
  fun _ _ _ ext h => hR ext h

theorem const (Q : α → Prop) : HeapMono (fun (_ : Heap F) x => Q x) :=
  fun _ _ _ _ h => h

theorem and {P Q : Heap F → α → Prop} (hP : HeapMono P) (hQ : HeapMono Q) :
    HeapMono (fun h x => P h x ∧ Q h x) :=
  fun _ _ _ ext ⟨hp, hq⟩ => ⟨hP ext hp, hQ ext hq⟩

theorem or {P Q : Heap F → α → Prop} (hP : HeapMono P) (hQ : HeapMono Q) :
    HeapMono (fun h x => P h x ∨ Q h x) := by
  intro h₁ h₂ x ext h
  rcases h with hp | hq
  · exact Or.inl (hP ext hp)
  · exact Or.inr (hQ ext hq)

theorem ex {P : β → Heap F → α → Prop} (hP : ∀ b, HeapMono (P b)) :
    HeapMono (fun h x => ∃ b, P b h x) := by
  intro h₁ h₂ x ext ⟨b, hb⟩
  exact ⟨b, hP b ext hb⟩

theorem all {P : β → Heap F → α → Prop} (hP : ∀ b, HeapMono (P b)) :
    HeapMono (fun h x => ∀ b, P b h x) :=
  fun _ _ _ ext h b => hP b ext (h b)

theorem comp {P : Heap F → β → Prop} (f : α → β) (hP : HeapMono P) :
    HeapMono (fun h x => P h (f x)) :=
  fun _ _ _ ext h => hP ext h

theorem forall₂ {R : Heap F → α → β → Prop} (hR : HeapMono₂ R) (xs : List α) :
    HeapMono (fun h ys => List.Forall₂ (R h) xs ys) := by
  intro h₁ h₂ ys ext h
  exact h.imp (fun _ _ hab => hR ext hab)

end HeapMono

/-- Pointer dereference combinator: `ptr` is a pointer of type `ty` whose heap cell
satisfies `P`. -/
def DerefTyped (ty : Ty) (P : Heap F → SourceValue F → Prop)
    (h : Heap F) (ptr : SourceValue F) : Prop :=
  ∃ addr v, ptr = .ptr ty addr ∧ h[addr]? = some v ∧ P h v

/-- Untyped pointer dereference combinator: `ptr` is a pointer (of some type `ty`)
whose heap cell satisfies `P`. -/
def Deref (P : Heap F → SourceValue F → Prop)
    (h : Heap F) (ptr : SourceValue F) : Prop :=
  ∃ ty addr v, ptr = .ptr ty addr ∧ h[addr]? = some v ∧ P h v

theorem HeapMono.derefTyped {ty : Ty} {P : Heap F → SourceValue F → Prop}
    (hP : HeapMono P) : HeapMono (DerefTyped ty P) := by
  intro h₁ h₂ ptr ext ⟨addr, v, hptr, hget, hp⟩
  exact ⟨addr, v, hptr, ext.getElem?_eq hget, hP ext hp⟩

theorem HeapMono.deref {P : Heap F → SourceValue F → Prop}
    (hP : HeapMono P) : HeapMono (Deref P) := by
  intro h₁ h₂ ptr ext ⟨ty, addr, v, hptr, hget, hp⟩
  exact ⟨ty, addr, v, hptr, ext.getElem?_eq hget, hP ext hp⟩

theorem Represents.heapMono (rom : ROM F) (source : SourceValue F) :
    HeapMono (fun h target => Represents rom h source target) := by
  intro h₁ h₂ target ext hrep
  exact hrep.mono (Heap.Extends.iff_isPrefix.mp ext)

/-- Inductive heap-allocated linked list representation for any nominal node enum `enumName`
with constructors `nilCtor` (`Nil`) and `consCtor` (`Cons(head, tail)`). -/
inductive RepLinkedList {α : Type*} (enumName nilCtor consCtor : String)
    (R : Heap F → α → SourceValue F → Prop) (h : Heap F) :
    List α → SourceValue F → Prop where
  | nil {addr : Nat}
      (cell : h[addr]? = some (.construct enumName nilCtor [])) :
      RepLinkedList enumName nilCtor consCtor R h [] (.ptr (.enum enumName) addr)
  | cons {x : α} {xs : List α} {addr : Nat} {headVal tailPtr : SourceValue F}
      (cell : h[addr]? = some (.construct enumName consCtor [headVal, tailPtr]))
      (headRep : R h x headVal)
      (tailRep : RepLinkedList enumName nilCtor consCtor R h xs tailPtr) :
      RepLinkedList enumName nilCtor consCtor R h (x :: xs) (.ptr (.enum enumName) addr)

theorem RepLinkedList.mono {α : Type*} {enumName nilCtor consCtor : String}
    {R : Heap F → α → SourceValue F → Prop} (hR : HeapMono₂ R)
    {h₁ h₂ : Heap F} {xs : List α} {ptr : SourceValue F}
    (ext : Heap.Extends h₁ h₂)
    (rep : RepLinkedList enumName nilCtor consCtor R h₁ xs ptr) :
    RepLinkedList enumName nilCtor consCtor R h₂ xs ptr := by
  induction rep with
  | nil cell =>
      exact .nil (ext.getElem?_eq cell)
  | cons cell headRep _ ih =>
      exact .cons (ext.getElem?_eq cell) (hR ext headRep) ih

theorem HeapMono.repLinkedList {α : Type*} (enumName nilCtor consCtor : String)
    {R : Heap F → α → SourceValue F → Prop} (hR : HeapMono₂ R) (xs : List α) :
    HeapMono (fun h ptr => RepLinkedList enumName nilCtor consCtor R h xs ptr) :=
  fun _ _ _ ext rep => rep.mono hR ext

/-- Inductive binary tree for heap-allocated tree structures. -/
inductive BinaryTree (α : Type*) where
  | leaf : BinaryTree α
  | branch (label : α) (left right : BinaryTree α) : BinaryTree α
  deriving Repr, DecidableEq

/-- Inductive heap-allocated binary tree representation for a nominal tree enum `enumName`
with constructors `leafCtor` and `branchCtor(label, left, right)`. -/
inductive RepBinaryTree {α : Type*} (enumName leafCtor branchCtor : String)
    (R : Heap F → α → SourceValue F → Prop) (h : Heap F) :
    BinaryTree α → SourceValue F → Prop where
  | leaf {addr : Nat}
      (cell : h[addr]? = some (.construct enumName leafCtor [])) :
      RepBinaryTree enumName leafCtor branchCtor R h .leaf (.ptr (.enum enumName) addr)
  | branch {x : α} {l r : BinaryTree α} {addr : Nat} {val leftPtr rightPtr : SourceValue F}
      (cell : h[addr]? = some (.construct enumName branchCtor [val, leftPtr, rightPtr]))
      (labelRep : R h x val)
      (leftRep : RepBinaryTree enumName leafCtor branchCtor R h l leftPtr)
      (rightRep : RepBinaryTree enumName leafCtor branchCtor R h r rightPtr) :
      RepBinaryTree enumName leafCtor branchCtor R h (.branch x l r) (.ptr (.enum enumName) addr)

theorem RepBinaryTree.mono {α : Type*} {enumName leafCtor branchCtor : String}
    {R : Heap F → α → SourceValue F → Prop} (hR : HeapMono₂ R)
    {h₁ h₂ : Heap F} {t : BinaryTree α} {ptr : SourceValue F}
    (ext : Heap.Extends h₁ h₂)
    (rep : RepBinaryTree enumName leafCtor branchCtor R h₁ t ptr) :
    RepBinaryTree enumName leafCtor branchCtor R h₂ t ptr := by
  induction rep with
  | leaf cell =>
      exact .leaf (ext.getElem?_eq cell)
  | branch cell labelRep _ _ ihl ihr =>
      exact .branch (ext.getElem?_eq cell) (hR ext labelRep) ihl ihr

theorem HeapMono.repBinaryTree {α : Type*} (enumName leafCtor branchCtor : String)
    {R : Heap F → α → SourceValue F → Prop} (hR : HeapMono₂ R) (t : BinaryTree α) :
    HeapMono (fun h ptr => RepBinaryTree enumName leafCtor branchCtor R h t ptr) :=
  fun _ _ _ ext rep => rep.mono hR ext

end Aiur
