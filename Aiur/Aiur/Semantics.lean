import Aiur.Eval

namespace Aiur

/-- Structural value equivalence unfolding pointers through an immutable heap.
Two pointers are `HeapValueEq` when they refer to cells of the same type whose
contents are themselves `HeapValueEq`. Used for the one-way-sound `ptr_eq`
semantics (`equal = true → HeapValueEq`). -/
inductive HeapValueEq (heap : Heap F) : SourceValue F → SourceValue F → Prop where
  | refl (v : SourceValue F) : HeapValueEq heap v v
  | tuple (items : List.Forall₂ (HeapValueEq heap) xs ys) :
      HeapValueEq heap (.tuple xs) (.tuple ys)
  | construct (items : List.Forall₂ (HeapValueEq heap) xs ys) :
      HeapValueEq heap (.construct name ctor xs) (.construct name ctor ys)
  | ptr {target : Ty} {s₁ s₂ : SourceValue F} {a₁ a₂ : Nat}
      (h₁ : heap[a₁]? = some s₁) (h₂ : heap[a₂]? = some s₂)
      (ht₁ : s₁.type = target) (ht₂ : s₂.type = target)
      (contents : HeapValueEq heap s₁ s₂) :
      HeapValueEq heap (.ptr target a₁) (.ptr target a₂)

theorem HeapValueEq.mono {heap larger : Heap F} {x y : SourceValue F}
    (grows : heap <+: larger) (eq : HeapValueEq heap x y) : HeapValueEq larger x y := by
  induction eq using HeapValueEq.rec
    (motive_2 := fun xs ys _ => List.Forall₂ (HeapValueEq larger) xs ys) with
  | refl v => exact .refl v
  | tuple _ ih => exact .tuple ih
  | construct _ ih => exact .construct ih
  | ptr h₁ h₂ ht₁ ht₂ _ ih =>
      obtain ⟨rest, rfl⟩ := grows
      exact .ptr
        (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h₁).1]; exact h₁)
        (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h₂).1]; exact h₂)
        ht₁ ht₂ ih
  | nil => exact .nil
  | cons _ _ h t => exact .cons h t

theorem HeapValueEq.symm {heap : Heap F} {x y : SourceValue F}
    (eq : HeapValueEq heap x y) : HeapValueEq heap y x := by
  induction eq using HeapValueEq.rec
    (motive_2 := fun xs ys _ => List.Forall₂ (HeapValueEq heap) ys xs) with
  | refl v => exact .refl v
  | tuple _ ih => exact .tuple ih
  | construct _ ih => exact .construct ih
  | ptr h₁ h₂ ht₁ ht₂ _ ih => exact .ptr h₂ h₁ ht₂ ht₁ ih
  | nil => exact .nil
  | cons _ _ h t => exact .cons h t

theorem HeapValueEq.load [DecidableEq F] {heap : Heap F} {target : Ty} {a₁ a₂ : Nat}
    {v₁ v₂ : SourceValue F}
    (eq : HeapValueEq heap (.ptr target a₁) (.ptr target a₂))
    (l₁ : loadValue heap (.ptr target a₁) = .ok v₁)
    (l₂ : loadValue heap (.ptr target a₂) = .ok v₂) :
    HeapValueEq heap v₁ v₂ := by
  cases eq with
  | refl => rw [l₁] at l₂; cases l₂; exact .refl _
  | ptr h₁ h₂ ht₁ ht₂ contents =>
      simp only [loadValue, h₁, h₂, ht₁, ht₂, ne_eq, not_true_eq_false, ↓reduceIte,
        bind, Except.bind, pure, Except.pure] at l₁ l₂
      cases l₁; cases l₂; exact contents

theorem HeapValueEq.eq_of_pointerFree {heap : Heap F} {x y : SourceValue F}
    (eq : HeapValueEq heap x y) (free : x.pointerFree = true) : x = y := by
  induction eq using HeapValueEq.rec
    (motive_2 := fun xs ys _ => (∀ v ∈ xs, v.pointerFree = true) → xs = ys) with
  | refl => rfl
  | tuple _ ih =>
      congr 1; apply ih
      simpa [Value.pointerFree] using free
  | construct _ ih =>
      congr 1; apply ih
      simpa [Value.pointerFree] using free
  | ptr => simp [Value.pointerFree] at free
  | nil => rfl
  | cons _ _ h t =>
      rename_i hall
      exact congrArg₂ List.cons (h (hall _ (by simp))) (t (fun v hv => hall v (by simp [hv])))

mutual
  /-- Finite source evaluation threads a fresh-allocation heap, with no fuel. -/
  inductive EvalExpr [Field F] [DecidableEq F] (program : Program F) :
      Environment F Nat → Expr F → Heap F → SourceValue F → Heap F → Prop where
    | literal : EvalExpr program locals (.literal value) heap (.field value) heap
    | var (lookup : locals.find? (·.1 == name) = some (name, value)) :
        EvalExpr program locals (.var name) heap value heap
    | tuple (items : EvalArgs program locals exprs before values after) :
        EvalExpr program locals (.tuple exprs) before (.tuple values) after
    | construct (items : EvalArgs program locals exprs before values after) :
        EvalExpr program locals (.construct name ctor exprs) before (.construct name ctor values) after
    | project (value : EvalExpr program locals expr before input after)
        (projected : projectValue input index = .ok result) :
        EvalExpr program locals (.project expr index) before result after
    | letValue (value : EvalExpr program locals expr before input middle)
        (matched : pattern.bindings input = some bindings)
        (body : EvalExpr program (bindings ++ locals) rest middle result after) :
        EvalExpr program locals (.letValue pattern expr rest) before result after
    | store (value : EvalExpr program locals expr before input middle) :
        EvalExpr program locals (.store expr) before (.ptr input.type middle.length) (middle ++ [input])
    | load (pointer : EvalExpr program locals expr before input after)
        (loaded : loadValue after input = .ok result) :
        EvalExpr program locals (.load expr) before result after
    | hint (key : EvalExpr program locals expr before input after)
        {value : Constant F} (typed : value.WellTyped program.enums type) :
        EvalExpr program locals (.hint type expr channel) before value.toValue after
    | neg (value : EvalExpr program locals expr before input after)
        (operation : evalNeg input = .ok result) :
        EvalExpr program locals (.neg expr) before result after
    | assertEq (left : EvalExpr program locals lhs before x middle)
        (right : EvalExpr program locals rhs middle y after)
        (operation : evalAssertEq op x y = .ok result) :
        EvalExpr program locals (.assertEq op lhs rhs) before result after
    | ptrEq {target : Ty} {a₁ a₂ : Nat} {equal : Bool}
        (left : EvalExpr program locals lhs before (.ptr target a₁) middle)
        (right : EvalExpr program locals rhs middle (.ptr target a₂) after)
        (inBounds₁ : a₁ < after.length)
        (inBounds₂ : a₂ < after.length)
        (sound : equal = true → HeapValueEq after (.ptr target a₁) (.ptr target a₂)) :
        EvalExpr program locals (.ptrEq lhs rhs) before (.field (if equal then 1 else 0)) after
    | binary (left : EvalExpr program locals lhs before x middle)
        (right : EvalExpr program locals rhs middle y after)
        (operation : evalBinOp op x y = .ok result) :
        EvalExpr program locals (.binary op lhs rhs) before result after
    | call (arguments : EvalArgs program locals args before values middle)
        (callee : EvalFn program name values middle result after) :
        EvalExpr program locals (.call name args) before result after
    | matchValue (value : EvalExpr program locals expr before input middle)
        (selected : selectArm input arms = some (bindings, body))
        (branch : EvalExpr program (bindings ++ locals) body middle result after) :
        EvalExpr program locals (.matchValue expr arms) before result after

  inductive EvalArgs [Field F] [DecidableEq F] (program : Program F) :
      Environment F Nat → List (Expr F) → Heap F → List (SourceValue F) → Heap F → Prop where
    | nil : EvalArgs program locals [] heap [] heap
    | cons (head : EvalExpr program locals expr before value middle)
        (tail : EvalArgs program locals exprs middle values after) :
        EvalArgs program locals (expr :: exprs) before (value :: values) after

  /-- Internal calls share the caller's heap and may receive pointers. -/
  inductive EvalFn [Field F] [DecidableEq F] (program : Program F) :
      String → List (SourceValue F) → Heap F → SourceValue F → Heap F → Prop where
    | intro (prepared : prepareCall program name args = .ok (locals, expr))
        (body : EvalExpr program locals expr before result after) :
        EvalFn program name args before result after
end

mutual
  /-- Exact-address big-step evaluation: identical to `EvalExpr` except that every
  `ptr_eq` step returns `1` iff the two heap addresses are literally equal (matching
  the reference evaluator `evalExprWith` and `ROM.ofHeap` completeness). -/
  inductive ExactEvalExpr [Field F] [DecidableEq F] (program : Program F) :
      Environment F Nat → Expr F → Heap F → SourceValue F → Heap F → Prop where
    | literal : ExactEvalExpr program locals (.literal value) heap (.field value) heap
    | var (found : locals.find? (·.1 == name) = some (name, value)) :
        ExactEvalExpr program locals (.var name) heap value heap
    | tuple (items : ExactEvalArgs program locals exprs before values after) :
        ExactEvalExpr program locals (.tuple exprs) before (.tuple values) after
    | construct (items : ExactEvalArgs program locals exprs before values after) :
        ExactEvalExpr program locals (.construct name ctor exprs) before (.construct name ctor values) after
    | project (value : ExactEvalExpr program locals expr before input after)
        (projected : projectValue input index = .ok result) :
        ExactEvalExpr program locals (.project expr index) before result after
    | letValue (value : ExactEvalExpr program locals expr before input middle)
        (matched : pattern.bindings input = some bindings)
        (body : ExactEvalExpr program (bindings ++ locals) rest middle result after) :
        ExactEvalExpr program locals (.letValue pattern expr rest) before result after
    | store (value : ExactEvalExpr program locals expr before input middle) :
        ExactEvalExpr program locals (.store expr) before (.ptr input.type middle.length) (middle ++ [input])
    | load (pointer : ExactEvalExpr program locals expr before input after)
        (loaded : loadValue after input = .ok result) :
        ExactEvalExpr program locals (.load expr) before result after
    | neg (value : ExactEvalExpr program locals expr before input after)
        (negated : evalNeg input = .ok result) :
        ExactEvalExpr program locals (.neg expr) before result after
    | hint (key : ExactEvalExpr program locals keyExpr before keyValue after)
        {value : Constant F} (typed : value.WellTyped program.enums type) :
        ExactEvalExpr program locals (.hint type keyExpr channel) before value.toValue after
    | assertEq (left : ExactEvalExpr program locals lhs before leftValue middle)
        (right : ExactEvalExpr program locals rhs middle rightValue after)
        (equal : evalAssertEq op leftValue rightValue = .ok result) :
        ExactEvalExpr program locals (.assertEq op lhs rhs) before result after
    | ptrEq {target : Ty} {a₁ a₂ : Nat}
        (left : ExactEvalExpr program locals lhs before (.ptr target a₁) middle)
        (right : ExactEvalExpr program locals rhs middle (.ptr target a₂) after)
        (inBounds₁ : a₁ < after.length) (inBounds₂ : a₂ < after.length) :
        ExactEvalExpr program locals (.ptrEq lhs rhs) before (.field (if a₁ = a₂ then 1 else 0)) after
    | binary (left : ExactEvalExpr program locals lhs before leftValue middle)
        (right : ExactEvalExpr program locals rhs middle rightValue after)
        (computed : evalBinOp op leftValue rightValue = .ok result) :
        ExactEvalExpr program locals (.binary op lhs rhs) before result after
    | call (arguments : ExactEvalArgs program locals args before values middle)
        (callee : ExactEvalFn program name values middle result after) :
        ExactEvalExpr program locals (.call name args) before result after
    | matchValue (value : ExactEvalExpr program locals expr before input middle)
        (selected : selectArm input arms = some (bindings, body))
        (branch : ExactEvalExpr program (bindings ++ locals) body middle result after) :
        ExactEvalExpr program locals (.matchValue expr arms) before result after

  inductive ExactEvalArgs [Field F] [DecidableEq F] (program : Program F) :
      Environment F Nat → List (Expr F) → Heap F → List (SourceValue F) → Heap F → Prop where
    | nil : ExactEvalArgs program locals [] heap [] heap
    | cons (head : ExactEvalExpr program locals expr before value middle)
        (tail : ExactEvalArgs program locals exprs middle values after) :
        ExactEvalArgs program locals (expr :: exprs) before (value :: values) after

  inductive ExactEvalFn [Field F] [DecidableEq F] (program : Program F) :
      String → List (SourceValue F) → Heap F → SourceValue F → Heap F → Prop where
    | intro (prepared : prepareCall program name args = .ok (locals, expr))
        (body : ExactEvalExpr program locals expr before result after) :
        ExactEvalFn program name args before result after
end

theorem ExactEvalExpr.toEvalExpr [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F Nat} {expr : Expr F} {before after : Heap F} {result : SourceValue F}
    (h : ExactEvalExpr program locals expr before result after) :
    EvalExpr program locals expr before result after := by
  induction h using ExactEvalExpr.rec
    (motive_2 := fun l es b vs a _ => EvalArgs program l es b vs a)
    (motive_3 := fun n as b r a _ => EvalFn program n as b r a) with
  | literal => exact .literal
  | var found => exact .var found
  | tuple _ ih => exact .tuple ih
  | construct _ ih => exact .construct ih
  | project _ p ih => exact .project ih p
  | letValue _ m _ vIH bIH => exact .letValue vIH m bIH
  | store _ ih => exact .store ih
  | load _ l ih => exact .load ih l
  | neg _ n ih => exact .neg ih n
  | hint _ t ih => exact .hint ih t
  | assertEq _ _ eq lIH rIH => exact .assertEq lIH rIH eq
  | ptrEq _ _ h1 h2 lIH rIH =>
      split_ifs with heq
      · subst heq
        exact EvalExpr.ptrEq (equal := true) lIH rIH h1 h2 (fun _ => .refl _)
      · exact EvalExpr.ptrEq (equal := false) lIH rIH h1 h2 (fun h => by cases h)
  | binary _ _ op lIH rIH => exact .binary lIH rIH op
  | call _ _ aIH cIH => exact .call aIH cIH
  | matchValue _ sel _ vIH bIH => exact .matchValue vIH sel bIH
  | nil => exact .nil
  | cons _ _ hIH tIH => exact .cons hIH tIH
  | intro prep _ bIH => exact .intro prep bIH

theorem ExactEvalFn.toEvalFn [Field F] [DecidableEq F] {program : Program F}
    {name : String} {args : List (SourceValue F)} {before after : Heap F} {result : SourceValue F}
    (h : ExactEvalFn program name args before result after) :
    EvalFn program name args before result after := by
  cases h with
  | intro prep body => exact .intro prep body.toEvalExpr

/-- Public entry calls start with an empty heap and well-formed arguments of pointer-free types. -/
def EvalCall [Field F] [DecidableEq F] (program : Program F)
    (name : String) (args : List (SourceValue F)) (result : SourceValue F) : Prop :=
  checkEntry program name = .ok () ∧ ∃ heap, EvalFn program name args [] result heap

end Aiur
