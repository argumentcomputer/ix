import Aiur.EvalCorrectness

namespace Aiur.Generic.Engine

/-- An open runtime resolves calls on demand. The expression language and all
heap operations are the same as in the monomorphic core. -/
structure World (F : Type) where
  prepare : String → List (SourceValue F) → Except EvalError (Environment F Nat × Aiur.Expr F)
  typed : Aiur.Ty → Constant F → Bool

abbrev HintProvider (w : World F) := String → SourceValue F → (type : Aiur.Ty) →
  Except HintError { value : Constant F // w.typed type value = true }

def unavailable : HintProvider w := fun _ _ _ => .error .unavailable

def World.ofProgram [DecidableEq F] (p : Aiur.Program F) : World F :=
  ⟨prepareCall p, fun t v => v.hasType p.enums t⟩

/-- Eager evaluation threads the allocation heap through operands and internal calls. -/
def evalExprWith [Field F] [DecidableEq F] (world : World F) (hints : HintProvider world)
    (locals : Environment F Nat) : Nat → Expr F → Evaluation F (SourceValue F)
  | 0, _ => throw .outOfFuel
  | fuel + 1, expr => do
      match expr with
      | .literal value => return .field value
      | .var name =>
          let some (_, value) := locals.find? (·.1 == name) | throw (.unboundVariable name)
          return value
      | .tuple items => return .tuple (← items.mapM (evalExprWith world hints locals fuel))
      | .construct name ctor args =>
          return .construct name ctor (← args.mapM (evalExprWith world hints locals fuel))
      | .project value index => liftM (projectValue (← evalExprWith world hints locals fuel value) index)
      | .letValue pattern value body =>
          let value ← evalExprWith world hints locals fuel value
          let some bindings := pattern.bindings value | throw .patternMismatch
          evalExprWith world hints (bindings ++ locals) fuel body
      | .store value =>
          let value ← evalExprWith world hints locals fuel value
          let heap ← get
          set (heap ++ [value])
          return .ptr value.type heap.length
      | .load pointer =>
          let pointer ← evalExprWith world hints locals fuel pointer
          liftM (loadValue (← get) pointer)
      | .hint type key channel =>
          let key ← evalExprWith world hints locals fuel key
          let value ← liftM ((hints channel key type).mapError EvalError.hint)
          return value.val.toValue
      | .neg value => liftM (evalNeg (← evalExprWith world hints locals fuel value))
      | .assertEq op left right =>
          liftM (evalAssertEq op (← evalExprWith world hints locals fuel left) (← evalExprWith world hints locals fuel right))
      | .binary op left right =>
          liftM (evalBinOp op (← evalExprWith world hints locals fuel left) (← evalExprWith world hints locals fuel right))
      | .call name args =>
          let values ← args.mapM (evalExprWith world hints locals fuel)
          let (bindings, body) ← liftM (world.prepare name values)
          evalExprWith world hints bindings fuel body
      | .matchValue scrutinee arms =>
          let value ← evalExprWith world hints locals fuel scrutinee
          let some (bindings, body) := selectArm value arms | throw .noMatchingArm
          evalExprWith world hints (bindings ++ locals) fuel body


mutual
  /-- Finite source evaluation threads a fresh-allocation heap, with no fuel. -/
  inductive EvalExpr [Field F] [DecidableEq F] (world : World F) :
      Environment F Nat → Expr F → Heap F → SourceValue F → Heap F → Prop where
    | literal : EvalExpr world locals (.literal value) heap (.field value) heap
    | var (lookup : locals.find? (·.1 == name) = some (name, value)) :
        EvalExpr world locals (.var name) heap value heap
    | tuple (items : EvalArgs world locals exprs before values after) :
        EvalExpr world locals (.tuple exprs) before (.tuple values) after
    | construct (items : EvalArgs world locals exprs before values after) :
        EvalExpr world locals (.construct name ctor exprs) before (.construct name ctor values) after
    | project (value : EvalExpr world locals expr before input after)
        (projected : projectValue input index = .ok result) :
        EvalExpr world locals (.project expr index) before result after
    | letValue (value : EvalExpr world locals expr before input middle)
        (matched : pattern.bindings input = some bindings)
        (body : EvalExpr world (bindings ++ locals) rest middle result after) :
        EvalExpr world locals (.letValue pattern expr rest) before result after
    | store (value : EvalExpr world locals expr before input middle) :
        EvalExpr world locals (.store expr) before (.ptr input.type middle.length) (middle ++ [input])
    | load (pointer : EvalExpr world locals expr before input after)
        (loaded : loadValue after input = .ok result) :
        EvalExpr world locals (.load expr) before result after
    | hint (key : EvalExpr world locals expr before input after)
        {value : Constant F} (typed : world.typed type value = true) :
        EvalExpr world locals (.hint type expr channel) before value.toValue after
    | neg (value : EvalExpr world locals expr before input after)
        (operation : evalNeg input = .ok result) :
        EvalExpr world locals (.neg expr) before result after
    | assertEq (left : EvalExpr world locals lhs before x middle)
        (right : EvalExpr world locals rhs middle y after)
        (operation : evalAssertEq op x y = .ok result) :
        EvalExpr world locals (.assertEq op lhs rhs) before result after
    | binary (left : EvalExpr world locals lhs before x middle)
        (right : EvalExpr world locals rhs middle y after)
        (operation : evalBinOp op x y = .ok result) :
        EvalExpr world locals (.binary op lhs rhs) before result after
    | call (arguments : EvalArgs world locals args before values middle)
        (callee : EvalFn world name values middle result after) :
        EvalExpr world locals (.call name args) before result after
    | matchValue (value : EvalExpr world locals expr before input middle)
        (selected : selectArm input arms = some (bindings, body))
        (branch : EvalExpr world (bindings ++ locals) body middle result after) :
        EvalExpr world locals (.matchValue expr arms) before result after

  inductive EvalArgs [Field F] [DecidableEq F] (world : World F) :
      Environment F Nat → List (Expr F) → Heap F → List (SourceValue F) → Heap F → Prop where
    | nil : EvalArgs world locals [] heap [] heap
    | cons (head : EvalExpr world locals expr before value middle)
        (tail : EvalArgs world locals exprs middle values after) :
        EvalArgs world locals (expr :: exprs) before (value :: values) after

  /-- Internal calls share the caller's heap and may receive pointers. -/
  inductive EvalFn [Field F] [DecidableEq F] (world : World F) :
      String → List (SourceValue F) → Heap F → SourceValue F → Heap F → Prop where
    | intro (prepared : world.prepare name args = .ok (locals, expr))
        (body : EvalExpr world locals expr before result after) :
        EvalFn world name args before result after
end


variable {F : Type} {world : World F} {hints : HintProvider world}

private theorem evalArgs_of_mapM [Field F] [DecidableEq F]
    {locals : Environment F Nat} {fuel : Nat}
    (sound : ∀ expr before result after,
      evalExprWith world hints locals fuel expr before = .ok (result, after) →
        EvalExpr world locals expr before result after)
    {args : List (Expr F)} {values : List (SourceValue F)} {before after : Heap F}
    (executed : args.mapM (evalExprWith world hints locals fuel) before = .ok (values, after)) :
    EvalArgs world locals args before values after := by
  induction args generalizing before values with
  | nil =>
      obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp executed
      exact .nil
  | cons head tail ih =>
      rw [List.mapM_cons] at executed
      obtain ⟨value, middle, headRun, rest⟩ := Evaluation.bind_ok.mp executed
      obtain ⟨results, last, tailRun, finished⟩ := Evaluation.bind_ok.mp rest
      obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp finished
      exact .cons (sound head before value middle headRun) (ih tailRun)

/-- Every successful run, including its final heap, has a fuel-free evaluation proof. -/
theorem evalExpr_spec [Field F] [DecidableEq F]
    {locals : Environment F Nat} {fuel : Nat} {expr : Expr F}
    {before after : Heap F} {result : SourceValue F}
    (executed : evalExprWith world hints locals fuel expr before = .ok (result, after)) :
    EvalExpr world locals expr before result after := by
  induction fuel generalizing locals expr before result after with
  | zero => simp [evalExprWith] at executed
  | succ fuel ih =>
      cases expr with
      | literal value =>
          obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp executed
          exact .literal
      | var name =>
          cases found : locals.find? (·.1 == name) with
          | none => simp [evalExprWith, found, Evaluation.throw_apply] at executed
          | some binding =>
              rcases binding with ⟨key, value⟩
              have same : key = name := by simpa using List.find?_some found
              subst key
              simp only [evalExprWith, found] at executed
              obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp executed
              exact .var found
      | tuple items =>
          simp only [evalExprWith] at executed
          obtain ⟨values, middle, itemsRun, finished⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp finished
          exact .tuple (evalArgs_of_mapM (fun _ _ _ _ h => ih h) itemsRun)
      | construct name ctor items =>
          simp only [evalExprWith] at executed
          obtain ⟨values, middle, itemsRun, finished⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp finished
          exact .construct (evalArgs_of_mapM (fun _ _ _ _ h => ih h) itemsRun)
      | project value index =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, operation⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨projected, rfl⟩ := Evaluation.lift_ok.mp operation
          exact .project (ih operand) projected
      | hint type key channel =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, keyRun, rest⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨value, last, supplied, finished⟩ := Evaluation.bind_ok.mp rest
          obtain ⟨_, rfl⟩ := Evaluation.lift_ok.mp supplied
          obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp finished
          exact .hint (ih keyRun) value.property
      | neg value =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, operation⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨negated, rfl⟩ := Evaluation.lift_ok.mp operation
          exact .neg (ih operand) negated
      | store value =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, stored⟩ := Evaluation.bind_ok.mp executed
          have same : (.ptr input.type middle.length, middle ++ [input]) = (result, after) := by
            simpa [bind, StateT.bind, Evaluation.get_apply, set, StateT.set,
              pure, StateT.pure, Except.pure, Except.bind] using stored
          cases same
          exact .store (ih operand)
      | load value =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, loaded⟩ := Evaluation.bind_ok.mp executed
          have lifted : (liftM (loadValue middle input) : Evaluation F _) middle = .ok (result, after) := by
            simpa [bind, StateT.bind, Evaluation.get_apply, Except.bind] using loaded
          obtain ⟨loadOK, rfl⟩ := Evaluation.lift_ok.mp lifted
          exact .load (ih operand) loadOK
      | assertEq op left right =>
          simp only [evalExprWith] at executed
          obtain ⟨leftValue, middle, leftRun, rest⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨rightValue, last, rightRun, operation⟩ := Evaluation.bind_ok.mp rest
          obtain ⟨operationOK, rfl⟩ := Evaluation.lift_ok.mp operation
          exact .assertEq (ih leftRun) (ih rightRun) operationOK
      | binary op left right =>
          simp only [evalExprWith] at executed
          obtain ⟨leftValue, middle, leftRun, rest⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨rightValue, last, rightRun, operation⟩ := Evaluation.bind_ok.mp rest
          obtain ⟨operationOK, rfl⟩ := Evaluation.lift_ok.mp operation
          exact .binary (ih leftRun) (ih rightRun) operationOK
      | letValue pattern value body =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, rest⟩ := Evaluation.bind_ok.mp executed
          cases matched : pattern.bindings input with
          | none => simp [matched] at rest
          | some bindings =>
              exact .letValue (ih operand) matched (ih (by simpa only [matched] using rest))
      | matchValue scrutinee arms =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, rest⟩ := Evaluation.bind_ok.mp executed
          cases selected : selectArm input arms with
          | none => simp [selected] at rest
          | some binding =>
              rcases binding with ⟨bindings, body⟩
              exact .matchValue (ih operand) selected (ih (by simpa only [selected] using rest))
      | call name args =>
          simp only [evalExprWith] at executed
          obtain ⟨values, middle, arguments, rest⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨⟨bindings, body⟩, last, prepared, called⟩ := Evaluation.bind_ok.mp rest
          obtain ⟨prepareOK, rfl⟩ := Evaluation.lift_ok.mp prepared
          exact .call (evalArgs_of_mapM (fun _ _ _ _ h => ih h) arguments) (.intro prepareOK (ih called))


end Aiur.Generic.Engine
