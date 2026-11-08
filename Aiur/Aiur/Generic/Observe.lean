import Aiur.Generic.SourceSemantics
import Aiur.Modules.Correctness

/-! # Observed source evaluation

The source semantics (`Aiur.Generic.SourceSemantics.EvalFn`) with every
function call recorded: `ObsFn world name args before result after calls`
holds when `EvalFn world name args before result after` has a derivation whose
calls, in evaluation order, are `calls`. Each `Call` is the callee's instance
name, its argument values and the heap when it is entered (after its
arguments are evaluated). The relation mirrors the five inductives of the
source semantics constructor for constructor; the only new datum is the call
list, which every rule concatenates from its premises and the `call` rule
extends with its own call.

The refinement statement (`Ix.IxVM.Refinement.Statement`) reads off the calls
the byte strings a derivation hashed: its collision escape must be one of
them.

* `ObsFn.erase`: an observed derivation is a derivation (the instrumentation
  adds no behaviour).
* `EvalFn.observe`: every derivation has an observed counterpart.

Both are proved, by mutual induction. They are stated in the source
semantics' namespace because they are about it; nothing here is specific to
IxVM. -/

namespace Aiur.Generic.SourceSemantics

variable {F : Type}

/-- **A recorded call**: the callee's instance name, its arguments, and the
heap when it is entered. -/
structure Call (F : Type) where
  name : String
  args : List (SourceValue F)
  heap : Heap F

mutual
  /-- `EvalExpr` with its calls. -/
  inductive ObsExpr [Field F] [DecidableEq F] (world : World F) :
      Types → Environment F Nat → Expr F → Heap F → SourceValue F → Heap F → List (Call F) → Prop where
    | block (body : ObsExpr world types locals expr before result after calls) :
        ObsExpr world types locals (.control (.block label) expr) before result after calls
    | blockExit (body : ObsExit world types locals expr before (.block label) result after calls) :
        ObsExpr world types locals (.control (.block label) expr) before result after calls
    | literal : ObsExpr world types locals (.literal value) heap (.field value) heap []
    | var (lookup : locals.find? (·.1 == name) = some (name, value)) :
        ObsExpr world types locals (.var name) heap value heap []
    | global
        (lookup : world.constant name (type.subst types) = .ok pattern)
        (interpreted : Consts.toExpr pattern = .ok body)
        (value : ObsExpr world [] [] body before result after calls) :
        ObsExpr world types locals (.global name (some type)) before result after calls
    | tuple (items : ObsArgs world types locals exprs before values after calls) :
        ObsExpr world types locals (.tuple exprs) before (.tuple values) after calls
    | array (items : ObsArgs world types locals exprs before values after calls) :
        ObsExpr world types locals (.array exprs) before (.tuple values) after calls
    | «repeat» (value : ObsExpr world types locals expr before input after calls) :
        ObsExpr world types locals (.repeat expr length) before (.tuple (List.replicate length input)) after calls
    | index (value : ObsExpr world types locals expr before input after calls)
        (projected : projectValue input index = .ok result) :
        ObsExpr world types locals (.index expr index) before result after calls
    | slice (value : ObsExpr world types locals expr before input after calls)
        (sliced : sliceValue input start stop = .ok result) :
        ObsExpr world types locals (.slice expr start stop) before result after calls
    | builtin (items : ObsArgs world types locals exprs before values after calls)
        (applied : operation.apply values = .ok result) :
        ObsExpr world types locals (.builtin operation exprs) before result after calls
    | update (items : ObsArgs world types locals exprs before values after calls)
        (updated : Update.value types paths values = .ok result) :
        ObsExpr world types locals (.update paths exprs) before result after calls
    | record (items : ObsArgs world types locals exprs before values after calls) :
        ObsExpr world types locals (.record head exprs) before
          (.construct (constructorName types head.type) structConstructor (head.order values (.tuple []))) after calls
    | member (value : ObsExpr world types locals expr before input after calls)
        (projected : memberValue types field input = .ok result) :
        ObsExpr world types locals (.member expr field) before result after calls
    | construct (items : ObsArgs world types locals exprs before values after calls) :
        ObsExpr world types locals (.construct name args ctor exprs) before
          (.construct (instanceName types name args) ctor values) after calls
    | constructAs (items : ObsArgs world types locals exprs before values after calls) :
        ObsExpr world types locals (.constructAs params t ctor exprs) before
          (.construct (constructorName types t) ctor values) after calls
    | project (value : ObsExpr world types locals expr before input after calls)
        (projected : projectValue input index = .ok result) :
        ObsExpr world types locals (.project expr index) before result after calls
    | letValue (value : ObsExpr world types locals expr before input middle calls₁)
        (matched : world.matchPattern types middle pattern input = .ok (some bindings))
        (body : ObsExpr world types (bindings ++ locals) rest middle result after calls₂) :
        ObsExpr world types locals (.letValue pattern expr rest) before result after (calls₁ ++ calls₂)
    | store (value : ObsExpr world types locals expr before input middle calls) :
        ObsExpr world types locals (.store expr) before (.ptr input.type middle.length) (middle ++ [input]) calls
    | load (pointer : ObsExpr world types locals expr before input after calls)
        (loaded : loadValue after input = .ok result) :
        ObsExpr world types locals (.load expr) before result after calls
    | hint (key : ObsExpr world types locals expr before input after calls)
        {value : Constant F} (typed : world.typed (t.subst types).toCore value = true) :
        ObsExpr world types locals (.hint t expr channel) before value.toValue after calls
    | neg (value : ObsExpr world types locals expr before input after calls)
        (operation : evalNeg input = .ok result) :
        ObsExpr world types locals (.neg expr) before result after calls
    | binary (left : ObsExpr world types locals lhs before x middle calls₁)
        (right : ObsExpr world types locals rhs middle y after calls₂)
        (operation : evalBinOp op x y = .ok result) :
        ObsExpr world types locals (.binary op lhs rhs) before result after (calls₁ ++ calls₂)
    | call (arguments : ObsArgs world types locals args before values middle calls₁)
        (callee : ObsFn world (instanceName types name typeArgs) values middle result after calls₂) :
        ObsExpr world types locals (.call name typeArgs args) before result after
          (calls₁ ++ ⟨instanceName types name typeArgs, values, middle⟩ :: calls₂)
    | matchValue (value : ObsExpr world types locals expr before input middle calls₁)
        (selected : selectArm world types middle input arms = .ok (some (bindings, body)))
        (branch : ObsExpr world types (bindings ++ locals) body middle result after calls₂) :
        ObsExpr world types locals (.matchValue expr arms) before result after (calls₁ ++ calls₂)

  /-- `EvalArgs` with its calls. -/
  inductive ObsArgs [Field F] [DecidableEq F] (world : World F) :
      Types → Environment F Nat → List (Expr F) → Heap F → List (SourceValue F) → Heap F →
        List (Call F) → Prop where
    | nil : ObsArgs world types locals [] heap [] heap []
    | cons (head : ObsExpr world types locals expr before value middle calls₁)
        (tail : ObsArgs world types locals exprs middle values after calls₂) :
        ObsArgs world types locals (expr :: exprs) before (value :: values) after (calls₁ ++ calls₂)

  /-- `EvalFn` with its calls. -/
  inductive ObsFn [Field F] [DecidableEq F] (world : World F) :
      String → List (SourceValue F) → Heap F → SourceValue F → Heap F → List (Call F) → Prop where
    | intro (prepared : world.prepare name args = .ok (types, locals, expr))
        (body : ObsExpr world types locals expr before result after calls) :
        ObsFn world name args before result after calls
    | returned (prepared : world.prepare name args = .ok (types, locals, expr))
        (body : ObsExit world types locals expr before .function result after calls) :
        ObsFn world name args before result after calls

  /-- `EvalExit` with its calls. -/
  inductive ObsExit [Field F] [DecidableEq F] (world : World F) :
      Types → Environment F Nat → Expr F → Heap F → ExitTarget → SourceValue F → Heap F →
        List (Call F) → Prop where
    | exit (value : ObsExpr world types locals expr before result after calls) :
        ObsExit world types locals (.control (.exit target) expr) before target result after calls
    | exitPayload (value : ObsExit world types locals expr before target result after calls) :
        ObsExit world types locals (.control (.exit outer) expr) before target result after calls
    | fromBlock (different : target ≠ .block label)
        (body : ObsExit world types locals expr before target result after calls) :
        ObsExit world types locals (.control (.block label) expr) before target result after calls
    | fromGlobal (lookup : world.constant name (type.subst types) = .ok pattern)
        (interpreted : Consts.toExpr pattern = .ok body)
        (value : ObsExit world [] [] body before target result after calls) :
        ObsExit world types locals (.global name (some type)) before target result after calls
    | fromTuple (items : ObsArgsExit world types locals exprs before target result after calls) :
        ObsExit world types locals (.tuple exprs) before target result after calls
    | fromArray (items : ObsArgsExit world types locals exprs before target result after calls) :
        ObsExit world types locals (.array exprs) before target result after calls
    | fromRepeat (value : ObsExit world types locals expr before target result after calls) :
        ObsExit world types locals (.repeat expr length) before target result after calls
    | fromIndex (value : ObsExit world types locals expr before target result after calls) :
        ObsExit world types locals (.index expr index) before target result after calls
    | fromSlice (value : ObsExit world types locals expr before target result after calls) :
        ObsExit world types locals (.slice expr start stop) before target result after calls
    | fromBuiltin (items : ObsArgsExit world types locals exprs before target result after calls) :
        ObsExit world types locals (.builtin operation exprs) before target result after calls
    | fromUpdate (items : ObsArgsExit world types locals exprs before target result after calls) :
        ObsExit world types locals (.update paths exprs) before target result after calls
    | fromRecord (items : ObsArgsExit world types locals exprs before target result after calls) :
        ObsExit world types locals (.record head exprs) before target result after calls
    | fromMember (value : ObsExit world types locals expr before target result after calls) :
        ObsExit world types locals (.member expr field) before target result after calls
    | fromConstruct (items : ObsArgsExit world types locals exprs before target result after calls) :
        ObsExit world types locals (.construct name args ctor exprs) before target result after calls
    | fromConstructAs (items : ObsArgsExit world types locals exprs before target result after calls) :
        ObsExit world types locals (.constructAs params t ctor exprs) before target result after calls
    | fromProject (value : ObsExit world types locals expr before target result after calls) :
        ObsExit world types locals (.project expr index) before target result after calls
    | fromLetValue (value : ObsExit world types locals expr before target result after calls) :
        ObsExit world types locals (.letValue pattern expr rest) before target result after calls
    | letBody (value : ObsExpr world types locals expr before input middle calls₁)
        (matched : world.matchPattern types middle pattern input = .ok (some bindings))
        (body : ObsExit world types (bindings ++ locals) rest middle target result after calls₂) :
        ObsExit world types locals (.letValue pattern expr rest) before target result after
          (calls₁ ++ calls₂)
    | fromStore (value : ObsExit world types locals expr before target result after calls) :
        ObsExit world types locals (.store expr) before target result after calls
    | fromLoad (value : ObsExit world types locals expr before target result after calls) :
        ObsExit world types locals (.load expr) before target result after calls
    | fromHint (value : ObsExit world types locals expr before target result after calls) :
        ObsExit world types locals (.hint t expr channel) before target result after calls
    | fromNeg (value : ObsExit world types locals expr before target result after calls) :
        ObsExit world types locals (.neg expr) before target result after calls
    | binaryLeft (value : ObsExit world types locals left before target result after calls) :
        ObsExit world types locals (.binary op left right) before target result after calls
    | binaryRight (left : ObsExpr world types locals lhs before input middle calls₁)
        (right : ObsExit world types locals rhs middle target result after calls₂) :
        ObsExit world types locals (.binary op lhs rhs) before target result after (calls₁ ++ calls₂)
    | fromCall (arguments : ObsArgsExit world types locals args before target result after calls) :
        ObsExit world types locals (.call name typeArgs args) before target result after calls
    | fromMatchValue (value : ObsExit world types locals expr before target result after calls) :
        ObsExit world types locals (.matchValue expr arms) before target result after calls
    | matchBody (value : ObsExpr world types locals expr before input middle calls₁)
        (selected : selectArm world types middle input arms = .ok (some (bindings, body)))
        (branch : ObsExit world types (bindings ++ locals) body middle target result after calls₂) :
        ObsExit world types locals (.matchValue expr arms) before target result after (calls₁ ++ calls₂)

  /-- `EvalArgsExit` with its calls. -/
  inductive ObsArgsExit [Field F] [DecidableEq F] (world : World F) :
      Types → Environment F Nat → List (Expr F) → Heap F → ExitTarget → SourceValue F → Heap F →
        List (Call F) → Prop where
    | head (value : ObsExit world types locals expr before target result after calls) :
        ObsArgsExit world types locals (expr :: rest) before target result after calls
    | tail (head : ObsExpr world types locals expr before value middle calls₁)
        (tail : ObsArgsExit world types locals rest middle target result after calls₂) :
        ObsArgsExit world types locals (expr :: rest) before target result after (calls₁ ++ calls₂)
end

variable [Field F] [DecidableEq F] {world : World F}

/-- **An observed derivation is a derivation**: erasing the calls gives the
source semantics' derivation. -/
theorem ObsFn.erase {name : String} {args : List (SourceValue F)} {before after : Heap F}
    {result : SourceValue F} {calls : List (Call F)}
    (observed : ObsFn world name args before result after calls) :
    EvalFn world name args before result after := by
  induction observed using ObsFn.rec
    (motive_1 := fun types locals expr before result after _ _ =>
      EvalExpr world types locals expr before result after)
    (motive_2 := fun types locals exprs before values after _ _ =>
      EvalArgs world types locals exprs before values after)
    (motive_4 := fun types locals expr before target result after _ _ =>
      EvalExit world types locals expr before target result after)
    (motive_5 := fun types locals exprs before target result after _ _ =>
      EvalArgsExit world types locals exprs before target result after) with
  | block _ ih => exact .block ih
  | blockExit _ ih => exact .blockExit ih
  | literal => exact .literal
  | var lookup => exact .var lookup
  | global lookup interpreted _ ih => exact .global lookup interpreted ih
  | tuple _ ih => exact .tuple ih
  | array _ ih => exact .array ih
  | «repeat» _ ih => exact .«repeat» ih
  | index _ projected ih => exact .index ih projected
  | slice _ sliced ih => exact .slice ih sliced
  | builtin _ applied ih => exact .builtin ih applied
  | update _ updated ih => exact .update ih updated
  | record _ ih => exact .record ih
  | member _ projected ih => exact .member ih projected
  | construct _ ih => exact .construct ih
  | constructAs _ ih => exact .constructAs ih
  | project _ projected ih => exact .project ih projected
  | letValue _ matched _ ih₁ ih₂ => exact .letValue ih₁ matched ih₂
  | store _ ih => exact .store ih
  | load _ loaded ih => exact .load ih loaded
  | hint _ typed ih => exact .hint ih typed
  | neg _ operation ih => exact .neg ih operation
  | binary _ _ operation ih₁ ih₂ => exact .binary ih₁ ih₂ operation
  | call _ _ ih₁ ih₂ => exact .call ih₁ ih₂
  | matchValue _ selected _ ih₁ ih₂ => exact .matchValue ih₁ selected ih₂
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂
  | intro prepared _ ih => exact .intro prepared ih
  | returned prepared _ ih => exact .returned prepared ih
  | exit _ ih => exact .exit ih
  | exitPayload _ ih => exact .exitPayload ih
  | fromBlock different _ ih => exact .fromBlock different ih
  | fromGlobal lookup interpreted _ ih => exact .fromGlobal lookup interpreted ih
  | fromTuple _ ih => exact .fromTuple ih
  | fromArray _ ih => exact .fromArray ih
  | fromRepeat _ ih => exact .fromRepeat ih
  | fromIndex _ ih => exact .fromIndex ih
  | fromSlice _ ih => exact .fromSlice ih
  | fromBuiltin _ ih => exact .fromBuiltin ih
  | fromUpdate _ ih => exact .fromUpdate ih
  | fromRecord _ ih => exact .fromRecord ih
  | fromMember _ ih => exact .fromMember ih
  | fromConstruct _ ih => exact .fromConstruct ih
  | fromConstructAs _ ih => exact .fromConstructAs ih
  | fromProject _ ih => exact .fromProject ih
  | fromLetValue _ ih => exact .fromLetValue ih
  | letBody _ matched _ ih₁ ih₂ => exact .letBody ih₁ matched ih₂
  | fromStore _ ih => exact .fromStore ih
  | fromLoad _ ih => exact .fromLoad ih
  | fromHint _ ih => exact .fromHint ih
  | fromNeg _ ih => exact .fromNeg ih
  | binaryLeft _ ih => exact .binaryLeft ih
  | binaryRight _ _ ih₁ ih₂ => exact .binaryRight ih₁ ih₂
  | fromCall _ ih => exact .fromCall ih
  | fromMatchValue _ ih => exact .fromMatchValue ih
  | matchBody _ selected _ ih₁ ih₂ => exact .matchBody ih₁ selected ih₂
  | head _ ih => exact .head ih
  | tail _ _ ih₁ ih₂ => exact .tail ih₁ ih₂

/-- **Every derivation has an observed counterpart**: the same derivation
with its calls recorded. -/
theorem EvalFn.observe {name : String} {args : List (SourceValue F)} {before after : Heap F}
    {result : SourceValue F}
    (evaluated : EvalFn world name args before result after) :
    ∃ calls, ObsFn world name args before result after calls := by
  induction evaluated using EvalFn.rec
    (motive_1 := fun types locals expr before result after _ =>
      ∃ calls, ObsExpr world types locals expr before result after calls)
    (motive_2 := fun types locals exprs before values after _ =>
      ∃ calls, ObsArgs world types locals exprs before values after calls)
    (motive_4 := fun types locals expr before target result after _ =>
      ∃ calls, ObsExit world types locals expr before target result after calls)
    (motive_5 := fun types locals exprs before target result after _ =>
      ∃ calls, ObsArgsExit world types locals exprs before target result after calls) with
  | block _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .block h⟩
  | blockExit _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .blockExit h⟩
  | literal => exact ⟨[], .literal⟩
  | var lookup => exact ⟨[], .var lookup⟩
  | global lookup interpreted _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .global lookup interpreted h⟩
  | tuple _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .tuple h⟩
  | array _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .array h⟩
  | «repeat» _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .«repeat» h⟩
  | index _ projected ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .index h projected⟩
  | slice _ sliced ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .slice h sliced⟩
  | builtin _ applied ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .builtin h applied⟩
  | update _ updated ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .update h updated⟩
  | record _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .record h⟩
  | member _ projected ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .member h projected⟩
  | construct _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .construct h⟩
  | constructAs _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .constructAs h⟩
  | project _ projected ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .project h projected⟩
  | letValue _ matched _ ih₁ ih₂ =>
      obtain ⟨c₁, h₁⟩ := ih₁; obtain ⟨c₂, h₂⟩ := ih₂; exact ⟨_, .letValue h₁ matched h₂⟩
  | store _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .store h⟩
  | load _ loaded ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .load h loaded⟩
  | hint _ typed ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .hint h typed⟩
  | neg _ operation ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .neg h operation⟩
  | binary _ _ operation ih₁ ih₂ =>
      obtain ⟨c₁, h₁⟩ := ih₁; obtain ⟨c₂, h₂⟩ := ih₂; exact ⟨_, .binary h₁ h₂ operation⟩
  | call _ _ ih₁ ih₂ =>
      obtain ⟨c₁, h₁⟩ := ih₁; obtain ⟨c₂, h₂⟩ := ih₂; exact ⟨_, .call h₁ h₂⟩
  | matchValue _ selected _ ih₁ ih₂ =>
      obtain ⟨c₁, h₁⟩ := ih₁; obtain ⟨c₂, h₂⟩ := ih₂; exact ⟨_, .matchValue h₁ selected h₂⟩
  | nil => exact ⟨[], .nil⟩
  | cons _ _ ih₁ ih₂ => obtain ⟨c₁, h₁⟩ := ih₁; obtain ⟨c₂, h₂⟩ := ih₂; exact ⟨_, .cons h₁ h₂⟩
  | intro prepared _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .intro prepared h⟩
  | returned prepared _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .returned prepared h⟩
  | exit _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .exit h⟩
  | exitPayload _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .exitPayload h⟩
  | fromBlock different _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromBlock different h⟩
  | fromGlobal lookup interpreted _ ih =>
      obtain ⟨c, h⟩ := ih; exact ⟨c, .fromGlobal lookup interpreted h⟩
  | fromTuple _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromTuple h⟩
  | fromArray _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromArray h⟩
  | fromRepeat _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromRepeat h⟩
  | fromIndex _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromIndex h⟩
  | fromSlice _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromSlice h⟩
  | fromBuiltin _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromBuiltin h⟩
  | fromUpdate _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromUpdate h⟩
  | fromRecord _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromRecord h⟩
  | fromMember _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromMember h⟩
  | fromConstruct _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromConstruct h⟩
  | fromConstructAs _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromConstructAs h⟩
  | fromProject _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromProject h⟩
  | fromLetValue _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromLetValue h⟩
  | letBody _ matched _ ih₁ ih₂ =>
      obtain ⟨c₁, h₁⟩ := ih₁; obtain ⟨c₂, h₂⟩ := ih₂; exact ⟨_, .letBody h₁ matched h₂⟩
  | fromStore _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromStore h⟩
  | fromLoad _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromLoad h⟩
  | fromHint _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromHint h⟩
  | fromNeg _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromNeg h⟩
  | binaryLeft _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .binaryLeft h⟩
  | binaryRight _ _ ih₁ ih₂ =>
      obtain ⟨c₁, h₁⟩ := ih₁; obtain ⟨c₂, h₂⟩ := ih₂; exact ⟨_, .binaryRight h₁ h₂⟩
  | fromCall _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromCall h⟩
  | fromMatchValue _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .fromMatchValue h⟩
  | matchBody _ selected _ ih₁ ih₂ =>
      obtain ⟨c₁, h₁⟩ := ih₁; obtain ⟨c₂, h₂⟩ := ih₂; exact ⟨_, .matchBody h₁ selected h₂⟩
  | head _ ih => obtain ⟨c, h⟩ := ih; exact ⟨c, .head h⟩
  | tail _ _ ih₁ ih₂ => obtain ⟨c₁, h₁⟩ := ih₁; obtain ⟨c₂, h₂⟩ := ih₂; exact ⟨_, .tail h₁ h₂⟩

end Aiur.Generic.SourceSemantics

namespace Aiur.Modules

open Generic.SourceSemantics

variable {F : Type} [Field F] [DecidableEq F] {program : Program F}

/-- **`Prepared.EvalFn` with its calls**: the entry is selected, and its
derivation from the empty heap records `calls`. -/
def Prepared.ObsFn (p : Prepared program) (name : String) (args : List (SourceValue F))
    (value : SourceValue F) (heap : Heap F) (calls : List (Call F)) : Prop :=
  ∃ entry, p.find? name = some entry ∧
    Generic.SourceSemantics.ObsFn p.environment.source.world entry.resolved.name args [] value heap calls

theorem Prepared.ObsFn.erase {p : Prepared program} {name : String} {args : List (SourceValue F)}
    {value : SourceValue F} {heap : Heap F} {calls : List (Call F)}
    (observed : p.ObsFn name args value heap calls) : p.EvalFn name args value heap := by
  obtain ⟨entry, selected, h⟩ := observed
  exact ⟨entry, selected, h.erase⟩

theorem Prepared.EvalFn.observe {p : Prepared program} {name : String} {args : List (SourceValue F)}
    {value : SourceValue F} {heap : Heap F}
    (evaluated : p.EvalFn name args value heap) : ∃ calls, p.ObsFn name args value heap calls := by
  obtain ⟨entry, selected, h⟩ := evaluated
  obtain ⟨calls, h⟩ := h.observe
  exact ⟨calls, entry, selected, h⟩

end Aiur.Modules
