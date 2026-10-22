import Aiur.Generic.OpenCore
import Aiur.Generic.SourceSemantics

/-! Native expression and exit evaluation with function calls left as premises.
Closing those premises recovers the authoritative source predicate exactly. -/
namespace Aiur.Generic.OpenSource
open SourceSemantics

mutual
  inductive EvalExpr [Field F] [DecidableEq F] (world : SourceSemantics.World F) (calls : CallRelation F) :
      Types → Environment F Nat → Expr F → Heap F → SourceValue F → Heap F → Prop where
    | block (body : EvalExpr world calls types locals expr before result after) :
        EvalExpr world calls types locals (.control (.block label) expr) before result after
    | blockExit (body : EvalExit world calls types locals expr before (.block label) result after) :
        EvalExpr world calls types locals (.control (.block label) expr) before result after
    | literal : EvalExpr world calls types locals (.literal value) heap (.field value) heap
    | var (lookup : locals.find? (·.1 == name) = some (name, value)) :
        EvalExpr world calls types locals (.var name) heap value heap
    | global
        (lookup : world.constant name (type.subst types) = .ok pattern)
        (interpreted : Consts.toExpr pattern = .ok body)
        (value : EvalExpr world calls [] [] body before result after) :
        EvalExpr world calls types locals (.global name (some type)) before result after
    | tuple (items : EvalArgs world calls types locals exprs before values after) :
        EvalExpr world calls types locals (.tuple exprs) before (.tuple values) after
    | array (items : EvalArgs world calls types locals exprs before values after) :
        EvalExpr world calls types locals (.array exprs) before (.tuple values) after
    | «repeat» (value : EvalExpr world calls types locals expr before input after) :
        EvalExpr world calls types locals (.repeat expr length) before (.tuple (List.replicate length input)) after
    | index (value : EvalExpr world calls types locals expr before input after)
        (projected : projectValue input index = .ok result) :
        EvalExpr world calls types locals (.index expr index) before result after
    | slice (value : EvalExpr world calls types locals expr before input after)
        (sliced : sliceValue input start stop = .ok result) :
        EvalExpr world calls types locals (.slice expr start stop) before result after
    | builtin (items : EvalArgs world calls types locals exprs before values after)
        (applied : operation.apply values = .ok result) :
        EvalExpr world calls types locals (.builtin operation exprs) before result after
    | update (items : EvalArgs world calls types locals exprs before values after)
        (updated : Update.value types paths values = .ok result) :
        EvalExpr world calls types locals (.update paths exprs) before result after
    | record (items : EvalArgs world calls types locals exprs before values after) :
        EvalExpr world calls types locals (.record head exprs) before
          (.construct (constructorName types head.type) structConstructor (head.order values (.tuple []))) after
    | member (value : EvalExpr world calls types locals expr before input after)
        (projected : memberValue types field input = .ok result) :
        EvalExpr world calls types locals (.member expr field) before result after
    | construct (items : EvalArgs world calls types locals exprs before values after) :
        EvalExpr world calls types locals (.construct name args ctor exprs) before (.construct (instanceName types name args) ctor values) after
    | constructAs (items : EvalArgs world calls types locals exprs before values after) :
        EvalExpr world calls types locals (.constructAs params t ctor exprs) before (.construct (constructorName types t) ctor values) after
    | project (value : EvalExpr world calls types locals expr before input after)
        (projected : projectValue input index = .ok result) :
        EvalExpr world calls types locals (.project expr index) before result after
    | letValue (value : EvalExpr world calls types locals expr before input middle)
        (matched : world.matchPattern types middle pattern input = .ok (some bindings))
        (body : EvalExpr world calls types (bindings ++ locals) rest middle result after) :
        EvalExpr world calls types locals (.letValue pattern expr rest) before result after
    | store (value : EvalExpr world calls types locals expr before input middle) :
        EvalExpr world calls types locals (.store expr) before (.ptr input.type middle.length) (middle ++ [input])
    | load (pointer : EvalExpr world calls types locals expr before input after)
        (loaded : loadValue after input = .ok result) :
        EvalExpr world calls types locals (.load expr) before result after
    | hint (key : EvalExpr world calls types locals expr before input after)
        {value : Constant F} (typed : world.typed (t.subst types).toCore value = true) :
        EvalExpr world calls types locals (.hint t expr channel) before value.toValue after
    | neg (value : EvalExpr world calls types locals expr before input after)
        (operation : evalNeg input = .ok result) :
        EvalExpr world calls types locals (.neg expr) before result after
    | binary (left : EvalExpr world calls types locals lhs before x middle)
        (right : EvalExpr world calls types locals rhs middle y after)
        (operation : evalBinOp op x y = .ok result) :
        EvalExpr world calls types locals (.binary op lhs rhs) before result after
    | call (arguments : EvalArgs world calls types locals args before values middle)
        (callee : calls (instanceName types name typeArgs) values middle result after) :
        EvalExpr world calls types locals (.call name typeArgs args) before result after
    | matchValue (value : EvalExpr world calls types locals expr before input middle)
        (selected : SourceSemantics.selectArm world types middle input arms = .ok (some (bindings, body)))
        (branch : EvalExpr world calls types (bindings ++ locals) body middle result after) :
        EvalExpr world calls types locals (.matchValue expr arms) before result after

  inductive EvalArgs [Field F] [DecidableEq F] (world : SourceSemantics.World F) (calls : CallRelation F) :
      Types → Environment F Nat → List (Expr F) → Heap F → List (SourceValue F) → Heap F → Prop where
    | nil : EvalArgs world calls types locals [] heap [] heap
    | cons (head : EvalExpr world calls types locals expr before value middle)
        (tail : EvalArgs world calls types locals exprs middle values after) :
        EvalArgs world calls types locals (expr :: exprs) before (value :: values) after

  /-- Abrupt evaluation preserves the heap prefix already executed. It carries
  a lexical target and is caught only by that block or the current function. -/
  inductive EvalExit [Field F] [DecidableEq F] (world : SourceSemantics.World F) (calls : CallRelation F) :
      Types → Environment F Nat → Expr F → Heap F → ExitTarget → SourceValue F → Heap F → Prop where
    | exit (value : EvalExpr world calls types locals expr before result after) :
        EvalExit world calls types locals (.control (.exit target) expr) before target result after
    | exitPayload (value : EvalExit world calls types locals expr before target result after) :
        EvalExit world calls types locals (.control (.exit outer) expr) before target result after
    | fromBlock (different : target ≠ .block label)
        (body : EvalExit world calls types locals expr before target result after) :
        EvalExit world calls types locals (.control (.block label) expr) before target result after
    | fromGlobal (lookup : world.constant name (type.subst types) = .ok pattern)
        (interpreted : Consts.toExpr pattern = .ok body)
        (value : EvalExit world calls [] [] body before target result after) :
        EvalExit world calls types locals (.global name (some type)) before target result after
    | fromTuple (items : EvalArgsExit world calls types locals exprs before target result after) :
        EvalExit world calls types locals (.tuple exprs) before target result after
    | fromArray (items : EvalArgsExit world calls types locals exprs before target result after) :
        EvalExit world calls types locals (.array exprs) before target result after
    | fromRepeat (value : EvalExit world calls types locals expr before target result after) :
        EvalExit world calls types locals (.repeat expr length) before target result after
    | fromIndex (value : EvalExit world calls types locals expr before target result after) :
        EvalExit world calls types locals (.index expr index) before target result after
    | fromSlice (value : EvalExit world calls types locals expr before target result after) :
        EvalExit world calls types locals (.slice expr start stop) before target result after
    | fromBuiltin (items : EvalArgsExit world calls types locals exprs before target result after) :
        EvalExit world calls types locals (.builtin operation exprs) before target result after
    | fromUpdate (items : EvalArgsExit world calls types locals exprs before target result after) :
        EvalExit world calls types locals (.update paths exprs) before target result after
    | fromRecord (items : EvalArgsExit world calls types locals exprs before target result after) :
        EvalExit world calls types locals (.record head exprs) before target result after
    | fromMember (value : EvalExit world calls types locals expr before target result after) :
        EvalExit world calls types locals (.member expr field) before target result after
    | fromConstruct (items : EvalArgsExit world calls types locals exprs before target result after) :
        EvalExit world calls types locals (.construct name args ctor exprs) before target result after
    | fromConstructAs (items : EvalArgsExit world calls types locals exprs before target result after) :
        EvalExit world calls types locals (.constructAs params t ctor exprs) before target result after
    | fromProject (value : EvalExit world calls types locals expr before target result after) :
        EvalExit world calls types locals (.project expr index) before target result after
    | fromLetValue (value : EvalExit world calls types locals expr before target result after) :
        EvalExit world calls types locals (.letValue pattern expr rest) before target result after
    | letBody (value : EvalExpr world calls types locals expr before input middle)
        (matched : world.matchPattern types middle pattern input = .ok (some bindings))
        (body : EvalExit world calls types (bindings ++ locals) rest middle target result after) :
        EvalExit world calls types locals (.letValue pattern expr rest) before target result after
    | fromStore (value : EvalExit world calls types locals expr before target result after) :
        EvalExit world calls types locals (.store expr) before target result after
    | fromLoad (value : EvalExit world calls types locals expr before target result after) :
        EvalExit world calls types locals (.load expr) before target result after
    | fromHint (value : EvalExit world calls types locals expr before target result after) :
        EvalExit world calls types locals (.hint t expr channel) before target result after
    | fromNeg (value : EvalExit world calls types locals expr before target result after) :
        EvalExit world calls types locals (.neg expr) before target result after
    | binaryLeft (value : EvalExit world calls types locals left before target result after) :
        EvalExit world calls types locals (.binary op left right) before target result after
    | binaryRight (left : EvalExpr world calls types locals lhs before input middle)
        (right : EvalExit world calls types locals rhs middle target result after) :
        EvalExit world calls types locals (.binary op lhs rhs) before target result after
    | fromCall (arguments : EvalArgsExit world calls types locals args before target result after) :
        EvalExit world calls types locals (.call name typeArgs args) before target result after
    | fromMatchValue (value : EvalExit world calls types locals expr before target result after) :
        EvalExit world calls types locals (.matchValue expr arms) before target result after
    | matchBody (value : EvalExpr world calls types locals expr before input middle)
        (selected : SourceSemantics.selectArm world types middle input arms = .ok (some (bindings, body)))
        (branch : EvalExit world calls types (bindings ++ locals) body middle target result after) :
        EvalExit world calls types locals (.matchValue expr arms) before target result after

  inductive EvalArgsExit [Field F] [DecidableEq F] (world : SourceSemantics.World F) (calls : CallRelation F) :
      Types → Environment F Nat → List (Expr F) → Heap F → ExitTarget → SourceValue F → Heap F → Prop where
    | head (value : EvalExit world calls types locals expr before target result after) :
        EvalArgsExit world calls types locals (expr :: rest) before target result after
    | tail (head : EvalExpr world calls types locals expr before value middle)
        (tail : EvalArgsExit world calls types locals rest middle target result after) :
        EvalArgsExit world calls types locals (expr :: rest) before target result after
end

variable [Field F] [DecidableEq F] {world : SourceSemantics.World F} {calls other : CallRelation F}

theorem EvalExpr.mapCalls
    (h : EvalExpr world calls types locals expr before result after)
    (transfer : ∀ n args b v a, calls n args b v a → other n args b v a) :
    EvalExpr world other types locals expr before result after := by
  induction h using EvalExpr.rec
    (motive_2 := fun ts ls es b vs a _ => EvalArgs world other ts ls es b vs a)
    (motive_3 := fun ts ls e b target v a _ => EvalExit world other ts ls e b target v a)
    (motive_4 := fun ts ls es b target v a _ => EvalArgsExit world other ts ls es b target v a)
  all_goals first
    | solve | apply EvalExpr.block; assumption
    | solve | apply EvalExpr.blockExit; assumption
    | solve | apply EvalExpr.call; assumption; apply transfer; assumption
    | solve | apply EvalExit.letBody <;> assumption
    | solve | apply EvalExit.binaryRight <;> assumption
    | solve | apply EvalExit.matchBody <;> assumption
    | solve | apply EvalArgsExit.tail <;> assumption
    | solve | constructor <;> assumption

theorem EvalExpr.close
    (h : EvalExpr world (SourceSemantics.EvalFn world) types locals expr before result after) :
    SourceSemantics.EvalExpr world types locals expr before result after := by
  induction h using EvalExpr.rec
    (motive_2 := fun ts ls es b vs a _ => SourceSemantics.EvalArgs world ts ls es b vs a)
    (motive_3 := fun ts ls e b target v a _ => SourceSemantics.EvalExit world ts ls e b target v a)
    (motive_4 := fun ts ls es b target v a _ => SourceSemantics.EvalArgsExit world ts ls es b target v a)
  all_goals first
    | solve | apply SourceSemantics.EvalExpr.block; assumption
    | solve | apply SourceSemantics.EvalExpr.blockExit; assumption
    | solve | apply SourceSemantics.EvalExit.letBody <;> assumption
    | solve | apply SourceSemantics.EvalExit.binaryRight <;> assumption
    | solve | apply SourceSemantics.EvalExit.matchBody <;> assumption
    | solve | apply SourceSemantics.EvalArgsExit.tail <;> assumption
    | solve | constructor <;> assumption

theorem of_closed
    (h : SourceSemantics.EvalExpr world types locals expr before result after) :
    EvalExpr world (SourceSemantics.EvalFn world) types locals expr before result after := by
  induction h using SourceSemantics.EvalExpr.rec
    (motive_2 := fun ts ls es b vs a _ => EvalArgs world (SourceSemantics.EvalFn world) ts ls es b vs a)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (motive_4 := fun ts ls e b target v a _ => EvalExit world (SourceSemantics.EvalFn world) ts ls e b target v a)
    (motive_5 := fun ts ls es b target v a _ => EvalArgsExit world (SourceSemantics.EvalFn world) ts ls es b target v a)
  all_goals first
    | solve | apply EvalExpr.block; assumption
    | solve | apply EvalExpr.blockExit; assumption
    | solve | apply EvalExit.letBody <;> assumption
    | solve | apply EvalExit.binaryRight <;> assumption
    | solve | apply EvalExit.matchBody <;> assumption
    | solve | apply EvalArgsExit.tail <;> assumption
    | solve | constructor <;> assumption

theorem EvalExit.mapCalls
    (h : EvalExit world calls types locals expr before target result after)
    (transfer : ∀ n args b v a, calls n args b v a → other n args b v a) :
    EvalExit world other types locals expr before target result after := by
  induction h using EvalExit.rec
    (motive_1 := fun ts ls e b v a _ => EvalExpr world other ts ls e b v a)
    (motive_2 := fun ts ls es b vs a _ => EvalArgs world other ts ls es b vs a)
    (motive_4 := fun ts ls es b target v a _ => EvalArgsExit world other ts ls es b target v a)
  all_goals first
    | solve | apply EvalExpr.block; assumption
    | solve | apply EvalExpr.blockExit; assumption
    | solve | apply EvalExpr.call; assumption; apply transfer; assumption
    | solve | apply EvalExit.letBody <;> assumption
    | solve | apply EvalExit.binaryRight <;> assumption
    | solve | apply EvalExit.matchBody <;> assumption
    | solve | apply EvalArgsExit.tail <;> assumption
    | solve | constructor <;> assumption

theorem EvalExit.close
    (h : EvalExit world (SourceSemantics.EvalFn world) types locals expr before target result after) :
    SourceSemantics.EvalExit world types locals expr before target result after := by
  induction h using EvalExit.rec
    (motive_1 := fun ts ls e b v a _ => SourceSemantics.EvalExpr world ts ls e b v a)
    (motive_2 := fun ts ls es b vs a _ => SourceSemantics.EvalArgs world ts ls es b vs a)
    (motive_4 := fun ts ls es b target v a _ => SourceSemantics.EvalArgsExit world ts ls es b target v a)
  all_goals first
    | solve | apply SourceSemantics.EvalExpr.block; assumption
    | solve | apply SourceSemantics.EvalExpr.blockExit; assumption
    | solve | apply SourceSemantics.EvalExit.letBody <;> assumption
    | solve | apply SourceSemantics.EvalExit.binaryRight <;> assumption
    | solve | apply SourceSemantics.EvalExit.matchBody <;> assumption
    | solve | apply SourceSemantics.EvalArgsExit.tail <;> assumption
    | solve | constructor <;> assumption

theorem exit_of_closed
    (h : SourceSemantics.EvalExit world types locals expr before target result after) :
    EvalExit world (SourceSemantics.EvalFn world) types locals expr before target result after := by
  induction h using SourceSemantics.EvalExit.rec
    (motive_1 := fun ts ls e b v a _ => EvalExpr world (SourceSemantics.EvalFn world) ts ls e b v a)
    (motive_2 := fun ts ls es b vs a _ => EvalArgs world (SourceSemantics.EvalFn world) ts ls es b vs a)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun ts ls es b target v a _ => EvalArgsExit world (SourceSemantics.EvalFn world) ts ls es b target v a)
  all_goals first
    | solve | apply EvalExpr.block; assumption
    | solve | apply EvalExpr.blockExit; assumption
    | solve | apply EvalExit.letBody <;> assumption
    | solve | apply EvalExit.binaryRight <;> assumption
    | solve | apply EvalExit.matchBody <;> assumption
    | solve | apply EvalArgsExit.tail <;> assumption
    | solve | constructor <;> assumption

theorem closed_iff :
    EvalExpr world (SourceSemantics.EvalFn world) types locals expr before result after ↔
      SourceSemantics.EvalExpr world types locals expr before result after :=
  ⟨EvalExpr.close, of_closed⟩

theorem exit_closed_iff :
    EvalExit world (SourceSemantics.EvalFn world) types locals expr before target result after ↔
      SourceSemantics.EvalExit world types locals expr before target result after :=
  ⟨EvalExit.close, exit_of_closed⟩

end Aiur.Generic.OpenSource
