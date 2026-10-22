import Aiur.Generic.Builtin
import Aiur.Generic.Update
import Aiur.Generic.Consts
import Aiur.EvalCorrectness

/-! Evaluation is defined on the checked source AST. Type arguments are carried
in an environment; bodies are neither specialized nor lowered before execution.
The existing structured values and allocation heap are shared with the core. -/

namespace Aiur.Generic.SourceSemantics

abbrev Types := List (String × Ty)

def instanceName (types : Types) (name : String) (args : Option (List Ty)) : String :=
  (Instance.mk name ((args.getD []).map (Ty.subst types))).symbol

def constructorName (types : Types) (type : Ty) : String :=
  match (type.subst types).toCore with
  | .enum name => name
  | _ => "$invalid"

structure World (F : Type) where
  prepare : String → List (SourceValue F) → Except EvalError (Types × Environment F Nat × Expr F)
  typed : Aiur.Ty → Constant F → Bool
  /-- A single declaration lookup, with its use-site type information. -/
  constant : String → Ty → Except EvalError (Pattern F) :=
    fun name _ => .error (.unboundVariable ("::" ++ name))
  /-- The checked acyclic declaration graph bounds reference traversal. -/
  constDepth : Nat := 0

/-- Ordered, short-circuiting matching of a sequence. No later read is made
once an earlier pattern has failed. -/
def matchListWith (matchOne : A → SourceValue F → Except EvalError (Option (Environment F Nat))) :
    List A → List (SourceValue F) → Except EvalError (Option (Environment F Nat))
  | [], [] => pure (some [])
  | p :: ps, value :: values => do
      let some bindings ← matchOne p value | return none
      let some rest ← matchListWith matchOne ps values | return none
      return some (bindings ++ rest)
  | _, _ => pure none

/-- Pattern matching only reads the heap. A failed test returns `none`; a bad
load is an error, and cannot select a later arm. Bindings are installed only
after the whole pattern succeeds. -/
def matchPatternWith [DecidableEq F] (constant : String → Ty → Except EvalError (Pattern F))
    (depth : Nat) (types : Types) (heap : Heap F) :
    Pattern F → SourceValue F → Except EvalError (Option (Environment F Nat))
  | .literal x, value => pure ((Aiur.Pattern.literal x).bindings value)
  | .wildcard, _ => pure (some [])
  | .bind name, value => pure (some [(name, value)])
  | .global name annotation, value => do
      let some type := annotation | throw (.unboundVariable ("::" ++ name))
      match depth with
      | 0 => throw (.unboundVariable ("::" ++ name))
      | depth + 1 =>
          let body ← constant name (type.subst types)
          matchPatternWith constant depth [] heap body value
  | .orElse left right layout, value => do
      let (selected, positions) ← match ← matchPatternWith constant depth types heap left value with
        | some bindings => pure (some bindings, List.range layout.names.length)
        | none => (matchPatternWith constant depth types heap right value).map (fun result => (result, layout.rightOrder))
      let some bindings := selected | return none
      let some ordered := reorderBindings layout.names positions bindings | throw .patternMismatch
      return some ordered
  | .load pat, value => do matchPatternWith constant depth types heap pat (← loadValue heap value)
  | .tuple ps, value | .array ps, value => do
      let .tuple values := value | return none
      if ps.length != values.length then return none
      matchListWith (fun pat value => matchPatternWith constant depth types heap pat.val value) ps.attach values
  | .repeat pat n, value => do
      let .tuple values := value | return none
      if values.length != n then return none
      matchListWith (fun (_ : Unit) value => matchPatternWith constant depth types heap pat value)
        (List.replicate n ()) values
  | .record head ps, value => do
      let .construct name ctor values := value | return none
      if name != constructorName types head.type || ctor != structConstructor then return none
      let children := head.order (ps.attach.map some) none
      if children.length != values.length then return none
      matchListWith (fun child value => match child with
        | some pat => matchPatternWith constant depth types heap pat.val value
        | none => pure (some [])) children values
  | .construct t c ps, value | .constructAs _ t c ps, value => do
      let .construct name ctor values := value | return none
      if name != constructorName types t || ctor != c || ps.length != values.length then return none
      matchListWith (fun pat value => matchPatternWith constant depth types heap pat.val value) ps.attach values
termination_by pat _ => (depth, sizeOf pat)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | skip
  all_goals try have := List.sizeOf_lt_of_mem pat.property
  all_goals try simp_all only [Pattern.tuple.sizeOf_spec, Pattern.array.sizeOf_spec,
    Pattern.construct.sizeOf_spec, Pattern.constructAs.sizeOf_spec, Pattern.record.sizeOf_spec]
  all_goals omega

def World.matchPattern [DecidableEq F] (world : World F) :=
  matchPatternWith world.constant world.constDepth

/-- Matching without global declarations, useful for standalone patterns. -/
def matchPattern [DecidableEq F] :=
  matchPatternWith (F := F) (fun name _ => .error (.unboundVariable ("::" ++ name))) 0

def selectArm [DecidableEq F] (world : World F) (types : Types) (heap : Heap F) (value : SourceValue F) :
    List (Pattern F × Expr F) → Except EvalError (Option (Environment F Nat × Expr F))
  | [] => pure none
  | (pat, body) :: arms => do
      match ← world.matchPattern types heap pat value with
      | some bindings => return some (bindings, body)
      | none => selectArm world types heap value arms

/-- Bounds are source naturals. Slicing makes a value and never allocates. -/
def sliceValue (value : SourceValue F) (start : Nat) (stop : Option Nat) : Except EvalError (SourceValue F) := do
  let .tuple values := value | throw .expectedTuple
  let stop := stop.getD values.length
  if start > stop || stop > values.length then throw (.projectionBounds stop values.length)
  return .tuple ((values.drop start).take (stop - start))


/-- Read one field of a checked nominal product; no address is observed. -/
def memberValue (types : Types) (field : FieldRef) (value : SourceValue F) : Except EvalError (SourceValue F) := do
  let name := constructorName types (field.owner.getD (.named "$invalid" []))
  let .construct actual ctor values := value | throw (.malformedValue (.enum name))
  if actual != name || ctor != structConstructor || values.length != field.arity then
    throw (.malformedValue (.enum name))
  match values[field.index]? with
  | some value => return value
  | none => throw (.projectionBounds field.index field.arity)

abbrev HintProvider (world : World F) := String → SourceValue F → (type : Aiur.Ty) →
  Except HintError { value : Constant F // world.typed type value = true }

def unavailable : HintProvider world := fun _ _ _ => .error .unavailable


mutual
  inductive EvalExpr [Field F] [DecidableEq F] (world : World F) :
      Types → Environment F Nat → Expr F → Heap F → SourceValue F → Heap F → Prop where
    | block (body : EvalExpr world types locals expr before result after) :
        EvalExpr world types locals (.control (.block label) expr) before result after
    | blockExit (body : EvalExit world types locals expr before (.block label) result after) :
        EvalExpr world types locals (.control (.block label) expr) before result after
    | literal : EvalExpr world types locals (.literal value) heap (.field value) heap
    | var (lookup : locals.find? (·.1 == name) = some (name, value)) :
        EvalExpr world types locals (.var name) heap value heap
    | global
        (lookup : world.constant name (type.subst types) = .ok pattern)
        (interpreted : Consts.toExpr pattern = .ok body)
        (value : EvalExpr world [] [] body before result after) :
        EvalExpr world types locals (.global name (some type)) before result after
    | tuple (items : EvalArgs world types locals exprs before values after) :
        EvalExpr world types locals (.tuple exprs) before (.tuple values) after
    | array (items : EvalArgs world types locals exprs before values after) :
        EvalExpr world types locals (.array exprs) before (.tuple values) after
    | «repeat» (value : EvalExpr world types locals expr before input after) :
        EvalExpr world types locals (.repeat expr length) before (.tuple (List.replicate length input)) after
    | index (value : EvalExpr world types locals expr before input after)
        (projected : projectValue input index = .ok result) :
        EvalExpr world types locals (.index expr index) before result after
    | slice (value : EvalExpr world types locals expr before input after)
        (sliced : sliceValue input start stop = .ok result) :
        EvalExpr world types locals (.slice expr start stop) before result after
    | builtin (items : EvalArgs world types locals exprs before values after)
        (applied : operation.apply values = .ok result) :
        EvalExpr world types locals (.builtin operation exprs) before result after
    | update (items : EvalArgs world types locals exprs before values after)
        (updated : Update.value types paths values = .ok result) :
        EvalExpr world types locals (.update paths exprs) before result after
    | record (items : EvalArgs world types locals exprs before values after) :
        EvalExpr world types locals (.record head exprs) before
          (.construct (constructorName types head.type) structConstructor (head.order values (.tuple []))) after
    | member (value : EvalExpr world types locals expr before input after)
        (projected : memberValue types field input = .ok result) :
        EvalExpr world types locals (.member expr field) before result after
    | construct (items : EvalArgs world types locals exprs before values after) :
        EvalExpr world types locals (.construct name args ctor exprs) before (.construct (instanceName types name args) ctor values) after
    | constructAs (items : EvalArgs world types locals exprs before values after) :
        EvalExpr world types locals (.constructAs params t ctor exprs) before (.construct (constructorName types t) ctor values) after
    | project (value : EvalExpr world types locals expr before input after)
        (projected : projectValue input index = .ok result) :
        EvalExpr world types locals (.project expr index) before result after
    | letValue (value : EvalExpr world types locals expr before input middle)
        (matched : world.matchPattern types middle pattern input = .ok (some bindings))
        (body : EvalExpr world types (bindings ++ locals) rest middle result after) :
        EvalExpr world types locals (.letValue pattern expr rest) before result after
    | store (value : EvalExpr world types locals expr before input middle) :
        EvalExpr world types locals (.store expr) before (.ptr input.type middle.length) (middle ++ [input])
    | load (pointer : EvalExpr world types locals expr before input after)
        (loaded : loadValue after input = .ok result) :
        EvalExpr world types locals (.load expr) before result after
    | hint (key : EvalExpr world types locals expr before input after)
        {value : Constant F} (typed : world.typed (t.subst types).toCore value = true) :
        EvalExpr world types locals (.hint t expr channel) before value.toValue after
    | neg (value : EvalExpr world types locals expr before input after)
        (operation : evalNeg input = .ok result) :
        EvalExpr world types locals (.neg expr) before result after
    | binary (left : EvalExpr world types locals lhs before x middle)
        (right : EvalExpr world types locals rhs middle y after)
        (operation : evalBinOp op x y = .ok result) :
        EvalExpr world types locals (.binary op lhs rhs) before result after
    | call (arguments : EvalArgs world types locals args before values middle)
        (callee : EvalFn world (instanceName types name typeArgs) values middle result after) :
        EvalExpr world types locals (.call name typeArgs args) before result after
    | matchValue (value : EvalExpr world types locals expr before input middle)
        (selected : selectArm world types middle input arms = .ok (some (bindings, body)))
        (branch : EvalExpr world types (bindings ++ locals) body middle result after) :
        EvalExpr world types locals (.matchValue expr arms) before result after

  inductive EvalArgs [Field F] [DecidableEq F] (world : World F) :
      Types → Environment F Nat → List (Expr F) → Heap F → List (SourceValue F) → Heap F → Prop where
    | nil : EvalArgs world types locals [] heap [] heap
    | cons (head : EvalExpr world types locals expr before value middle)
        (tail : EvalArgs world types locals exprs middle values after) :
        EvalArgs world types locals (expr :: exprs) before (value :: values) after

  inductive EvalFn [Field F] [DecidableEq F] (world : World F) :
      String → List (SourceValue F) → Heap F → SourceValue F → Heap F → Prop where
    | intro (prepared : world.prepare name args = .ok (types, locals, expr))
        (body : EvalExpr world types locals expr before result after) :
        EvalFn world name args before result after
    | returned (prepared : world.prepare name args = .ok (types, locals, expr))
        (body : EvalExit world types locals expr before .function result after) :
        EvalFn world name args before result after

  /-- Abrupt evaluation preserves the heap prefix already executed. It carries
  a lexical target and is caught only by that block or the current function. -/
  inductive EvalExit [Field F] [DecidableEq F] (world : World F) :
      Types → Environment F Nat → Expr F → Heap F → ExitTarget → SourceValue F → Heap F → Prop where
    | exit (value : EvalExpr world types locals expr before result after) :
        EvalExit world types locals (.control (.exit target) expr) before target result after
    | exitPayload (value : EvalExit world types locals expr before target result after) :
        EvalExit world types locals (.control (.exit outer) expr) before target result after
    | fromBlock (different : target ≠ .block label)
        (body : EvalExit world types locals expr before target result after) :
        EvalExit world types locals (.control (.block label) expr) before target result after
    | fromGlobal (lookup : world.constant name (type.subst types) = .ok pattern)
        (interpreted : Consts.toExpr pattern = .ok body)
        (value : EvalExit world [] [] body before target result after) :
        EvalExit world types locals (.global name (some type)) before target result after
    | fromTuple (items : EvalArgsExit world types locals exprs before target result after) :
        EvalExit world types locals (.tuple exprs) before target result after
    | fromArray (items : EvalArgsExit world types locals exprs before target result after) :
        EvalExit world types locals (.array exprs) before target result after
    | fromRepeat (value : EvalExit world types locals expr before target result after) :
        EvalExit world types locals (.repeat expr length) before target result after
    | fromIndex (value : EvalExit world types locals expr before target result after) :
        EvalExit world types locals (.index expr index) before target result after
    | fromSlice (value : EvalExit world types locals expr before target result after) :
        EvalExit world types locals (.slice expr start stop) before target result after
    | fromBuiltin (items : EvalArgsExit world types locals exprs before target result after) :
        EvalExit world types locals (.builtin operation exprs) before target result after
    | fromUpdate (items : EvalArgsExit world types locals exprs before target result after) :
        EvalExit world types locals (.update paths exprs) before target result after
    | fromRecord (items : EvalArgsExit world types locals exprs before target result after) :
        EvalExit world types locals (.record head exprs) before target result after
    | fromMember (value : EvalExit world types locals expr before target result after) :
        EvalExit world types locals (.member expr field) before target result after
    | fromConstruct (items : EvalArgsExit world types locals exprs before target result after) :
        EvalExit world types locals (.construct name args ctor exprs) before target result after
    | fromConstructAs (items : EvalArgsExit world types locals exprs before target result after) :
        EvalExit world types locals (.constructAs params t ctor exprs) before target result after
    | fromProject (value : EvalExit world types locals expr before target result after) :
        EvalExit world types locals (.project expr index) before target result after
    | fromLetValue (value : EvalExit world types locals expr before target result after) :
        EvalExit world types locals (.letValue pattern expr rest) before target result after
    | letBody (value : EvalExpr world types locals expr before input middle)
        (matched : world.matchPattern types middle pattern input = .ok (some bindings))
        (body : EvalExit world types (bindings ++ locals) rest middle target result after) :
        EvalExit world types locals (.letValue pattern expr rest) before target result after
    | fromStore (value : EvalExit world types locals expr before target result after) :
        EvalExit world types locals (.store expr) before target result after
    | fromLoad (value : EvalExit world types locals expr before target result after) :
        EvalExit world types locals (.load expr) before target result after
    | fromHint (value : EvalExit world types locals expr before target result after) :
        EvalExit world types locals (.hint t expr channel) before target result after
    | fromNeg (value : EvalExit world types locals expr before target result after) :
        EvalExit world types locals (.neg expr) before target result after
    | binaryLeft (value : EvalExit world types locals left before target result after) :
        EvalExit world types locals (.binary op left right) before target result after
    | binaryRight (left : EvalExpr world types locals lhs before input middle)
        (right : EvalExit world types locals rhs middle target result after) :
        EvalExit world types locals (.binary op lhs rhs) before target result after
    | fromCall (arguments : EvalArgsExit world types locals args before target result after) :
        EvalExit world types locals (.call name typeArgs args) before target result after
    | fromMatchValue (value : EvalExit world types locals expr before target result after) :
        EvalExit world types locals (.matchValue expr arms) before target result after
    | matchBody (value : EvalExpr world types locals expr before input middle)
        (selected : selectArm world types middle input arms = .ok (some (bindings, body)))
        (branch : EvalExit world types (bindings ++ locals) body middle target result after) :
        EvalExit world types locals (.matchValue expr arms) before target result after

  inductive EvalArgsExit [Field F] [DecidableEq F] (world : World F) :
      Types → Environment F Nat → List (Expr F) → Heap F → ExitTarget → SourceValue F → Heap F → Prop where
    | head (value : EvalExit world types locals expr before target result after) :
        EvalArgsExit world types locals (expr :: rest) before target result after
    | tail (head : EvalExpr world types locals expr before value middle)
        (tail : EvalArgsExit world types locals rest middle target result after) :
        EvalArgsExit world types locals (expr :: rest) before target result after
end

end Aiur.Generic.SourceSemantics
