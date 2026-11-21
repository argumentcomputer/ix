import Aiur.Generic.SourceSemantics
import Aiur.Modules.Correctness
import Aiur.Memory.Cells

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

The IxVM refinement statement (Track B, `Ix.IxVM.Refinement.Statement`) reads
off the calls the byte strings a derivation hashed: its collision escape must
be one of them. This module moved here from that branch unchanged, so that the
backend headline can conclude it.

* `ObsFn.erase`: an observed derivation is a derivation (the instrumentation
  adds no behaviour).
* `EvalFn.observe`: every derivation has an observed counterpart.
* `ObsFn.represented`, `ObsFn.callsInROM`: if every cell of the final heap is
  a cell of a ROM (`HeapInROM`), every value the derivation handles, in
  particular every argument of every recorded call, inline calls included, is
  represented in that ROM relative to the heap at that point (`CallsInROM`).
  The world must bind function parameters to the call's arguments
  (`PreparesFromArgs`); `Source.world` does (`Source.world_preparesFromArgs`).

All are proved by mutual induction; nothing here is specific to IxVM. -/

namespace Aiur.Generic.SourceSemantics

variable {F : Type}

/-- **A recorded call**: the callee's instance name, its arguments, and the
heap when it is entered. -/
structure Call (F : Type) where
  name : String
  args : List (SourceValue F)
  heap : Heap F
/-! ## Calls carried by a ROM -/

/-- **The calls are carried by a ROM**: every argument of every call is
represented in `rom` relative to the heap at the call. -/
def CallsInROM (rom : ROM F) (calls : List (Call F)) : Prop :=
  ∀ c ∈ calls, ∀ v ∈ c.args, ∃ w, Aiur.Represents rom c.heap v w

/-- A value represented in `rom` relative to `heap`. -/
def Represented (rom : ROM F) (heap : Heap F) (value : SourceValue F) : Prop :=
  ∃ target, Aiur.Represents rom heap value target

/-- The world binds a function's parameters to the call's arguments. -/
def PreparesFromArgs (world : World F) : Prop :=
  ∀ name args types locals expr, world.prepare name args = .ok (types, locals, expr) →
    ∀ binding ∈ locals, binding.2 ∈ args


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

section Representation

variable {rom : ROM F} {heap : Heap F}

theorem CallsInROM.nil : CallsInROM rom ([] : List (Call F)) := by simp [CallsInROM]

theorem CallsInROM.append {left right : List (Call F)} (first : CallsInROM rom left)
    (second : CallsInROM rom right) : CallsInROM rom (left ++ right) := by
  intro c member
  rcases List.mem_append.mp member with member | member
  · exact first c member
  · exact second c member

theorem Represented.mono {value : SourceValue F} (holds : Represented rom heap value)
    {larger : Heap F} (grows : heap <+: larger) : Represented rom larger value :=
  let ⟨target, related⟩ := holds
  ⟨target, related.mono grows⟩

theorem Represented.ofPointerFree (value : SourceValue F) (free : value.pointerFree = true) :
    Represented rom heap value :=
  ⟨_, Aiur.Represents.of_pointerFree value free (fun _ => (0 : F))⟩

theorem Represented.field (x : F) : Represented rom heap (.field x) := ⟨_, .field⟩

private theorem represented_forall₂ :
    ∀ {values : List (SourceValue F)}, (∀ v ∈ values, Represented rom heap v) →
      ∃ targets, List.Forall₂ (Aiur.Represents rom heap) values targets
  | [], _ => ⟨[], .nil⟩
  | v :: vs, all => by
      obtain ⟨target, related⟩ := all v List.mem_cons_self
      obtain ⟨targets, rest⟩ := represented_forall₂ (fun w member => all w (List.mem_cons_of_mem _ member))
      exact ⟨target :: targets, .cons related rest⟩

private theorem forall₂_represented {values : List (SourceValue F)} {targets : List (Value F)}
    (related : List.Forall₂ (Aiur.Represents rom heap) values targets) :
    ∀ v ∈ values, Represented rom heap v := by
  induction related with
  | nil => simp
  | cons head _ ih =>
      intro v member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, head⟩
      · exact ih v member

theorem Represented.tuple_iff {values : List (SourceValue F)} :
    Represented rom heap (.tuple values) ↔ ∀ v ∈ values, Represented rom heap v := by
  constructor
  · rintro ⟨target, related⟩
    cases related with
    | tuple items => exact forall₂_represented items
  · intro all
    obtain ⟨targets, related⟩ := represented_forall₂ all
    exact ⟨_, .tuple related⟩

theorem Represented.construct_iff {name ctor : String} {values : List (SourceValue F)} :
    Represented rom heap (.construct name ctor values) ↔ ∀ v ∈ values, Represented rom heap v := by
  constructor
  · rintro ⟨target, related⟩
    cases related with
    | construct items => exact forall₂_represented items
  · intro all
    obtain ⟨targets, related⟩ := represented_forall₂ all
    exact ⟨_, .construct related⟩

theorem Represented.unit : Represented rom heap (.tuple [] : SourceValue F) :=
  Represented.tuple_iff.mpr (by simp)

theorem Represented.load {value result : SourceValue F} (holds : Represented rom heap value)
    (loaded : loadValue heap value = .ok result) : Represented rom heap result := by
  obtain ⟨target, related⟩ := holds
  cases related with
  | field => simp [loadValue, throw, throwThe, MonadExceptOf.throw] at loaded
  | tuple => simp [loadValue, throw, throwThe, MonadExceptOf.throw] at loaded
  | construct => simp [loadValue, throw, throwThe, MonadExceptOf.throw] at loaded
  | ptr source cell contents =>
      simp [loadValue, source, bind, Except.bind, pure, Except.pure] at loaded
      subst loaded
      exact ⟨_, contents⟩

/-- A fresh cell of a heap whose cells are ROM cells is represented. -/
theorem Represented.store {H middle : Heap F} {value : SourceValue F} (cells : HeapInROM rom H)
    (grows : middle ++ [value] <+: H) :
    Represented rom (middle ++ [value]) (.ptr value.type middle.length) := by
  have found : H[middle.length]? = some value := heap_get_of_prefix grows (by simp)
  obtain ⟨address, encoded, cell, related⟩ := cells middle.length value (Nat.zero_le _) found
  have take : H.take (middle.length + 1) = middle ++ [value] := by
    obtain ⟨rest, rfl⟩ := grows
    rw [List.take_append_of_le_length (by simp)]
    simp
  rw [take] at related
  exact ⟨_, .ptr (by simp) cell related⟩

theorem Represented.project {value result : SourceValue F} {index : Nat}
    (holds : Represented rom heap value) (projected : projectValue value index = .ok result) :
    Represented rom heap result := by
  cases value with
  | tuple items =>
      cases found : items[index]? with
      | none => simp [projectValue, found, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at projected
      | some item =>
          simp [projectValue, found, bind, Except.bind, pure, Except.pure] at projected
          subst projected
          exact Represented.tuple_iff.mp holds _ (List.mem_of_getElem? found)
  | field | ptr | construct => simp [projectValue, throw, throwThe, MonadExceptOf.throw] at projected

theorem Represented.slice {value result : SourceValue F} {start : Nat} {stop : Option Nat}
    (holds : Represented rom heap value) (sliced : sliceValue value start stop = .ok result) :
    Represented rom heap result := by
  cases value with
  | tuple items =>
      simp only [sliceValue] at sliced
      split at sliced
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at sliced
      · simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at sliced
        subst sliced
        apply Represented.tuple_iff.mpr
        intro v member
        exact Represented.tuple_iff.mp holds v (List.mem_of_mem_drop (List.mem_of_mem_take member))
  | field | ptr | construct => simp [sliceValue, throw, throwThe, MonadExceptOf.throw] at sliced

theorem Represented.member {value result : SourceValue F} {types : Types} {field : FieldRef}
    (holds : Represented rom heap value) (projected : memberValue types field value = .ok result) :
    Represented rom heap result := by
  cases value with
  | construct actual ctor items =>
      simp only [memberValue] at projected
      split at projected
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at projected
      · cases found : items[field.index]? with
        | none => simp [found, throw, throwThe, MonadExceptOf.throw] at projected
        | some item =>
            simp [found, pure, Except.pure, bind, Except.bind] at projected
            subst projected
            exact Represented.construct_iff.mp holds _ (List.mem_of_getElem? found)
  | field | ptr | tuple => simp [memberValue, throw, throwThe, MonadExceptOf.throw] at projected

theorem Represented.builtin {op : Builtin} {values : List (SourceValue F)}
    {result : SourceValue F} (all : ∀ v ∈ values, Represented rom heap v)
    (applied : op.apply values = .ok result) : Represented rom heap result := by
  cases op with
  | ascribe =>
      simp only [Builtin.apply] at applied
      split at applied
      · cases applied
        exact all _ (by simp)
      · cases applied
  | debug =>
      simp only [Builtin.apply, Except.ok.injEq] at applied
      subst applied
      exact Represented.unit
  | assertEq message =>
      simp only [Builtin.apply] at applied
      split at applied
      · simp only [evalAssertEq] at applied
        split at applied
        · split at applied
          · cases applied
            exact Represented.unit
          · cases applied
        · cases applied
      · cases applied

theorem Represented.neg {value result : SourceValue F}
    (operation : evalNeg value = .ok result) : Represented rom heap result := by
  cases value <;> simp only [evalNeg] at operation <;> cases operation
  exact Represented.field _

theorem Represented.binary {op : BinOp} {left right result : SourceValue F}
    (operation : evalBinOp op left right = .ok result) : Represented rom heap result := by
  cases left <;> cases right <;> simp only [evalBinOp] at operation <;> try cases operation
  cases op <;> simp only at operation
  all_goals first
    | (cases operation; exact Represented.field _)
    | (split at operation
       · cases operation
       · cases operation
         exact Represented.field _)

theorem Represented.order {head : RecordHead} {values : List (SourceValue F)}
    (all : ∀ v ∈ values, Represented rom heap v) :
    ∀ v ∈ head.order values (.tuple []), Represented rom heap v := by
  intro v member
  simp only [RecordHead.order, List.mem_map] at member
  obtain ⟨slot, _, rfl⟩ := member
  cases slot with
  | none => exact Represented.unit
  | some index =>
      cases found : values[index]? with
      | none => simp [found]; exact Represented.unit
      | some value => simp [found]; exact all value (List.mem_of_getElem? found)

/-! ### Updates -/

private theorem mem_of_mapM_some {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = some y
  | [], ys, mapped => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at mapped
      subst mapped
      simp
  | x :: xs, ys, mapped => by
      simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at mapped
      obtain ⟨y, first, rest, mapped, rfl⟩ := mapped
      intro z member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨x, List.mem_cons_self, first⟩
      · obtain ⟨w, inside, same⟩ := mem_of_mapM_some mapped z member
        exact ⟨w, List.mem_cons_of_mem _ inside, same⟩

private theorem unpack_represented {types : Types} {step : UpdateStep} {value : SourceValue F}
    {values : List (SourceValue F)} (holds : Represented rom heap value)
    (unpacked : Update.unpack types step value = some values) : ∀ v ∈ values, Represented rom heap v := by
  unfold Update.unpack at unpacked
  split at unpacked
  · split at unpacked
    · cases unpacked
      exact Represented.tuple_iff.mp holds
    · cases unpacked
  · split at unpacked
    · cases unpacked
      exact Represented.construct_iff.mp holds
    · cases unpacked
  · cases unpacked

private theorem pack_represented {types : Types} {step : UpdateStep} {values : List (SourceValue F)}
    (all : ∀ v ∈ values, Represented rom heap v) : Represented rom heap (Update.pack types step values) := by
  unfold Update.pack
  split
  · exact Represented.tuple_iff.mpr all
  · exact Represented.construct_iff.mpr all

private theorem replace_represented {types : Types} :
    ∀ (path : UpdatePath) (base replacement result : SourceValue F),
      Represented rom heap base → Represented rom heap replacement →
      Update.replace types path base replacement = some result → Represented rom heap result
  | [], _, _, result, _, replacement, replaced => by
      simp only [Update.replace, Option.some.injEq] at replaced
      subst replaced
      exact replacement
  | step :: path, base, replacement, result, holds, replacing, replaced => by
      simp only [Update.replace, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at replaced
      obtain ⟨values, unpacked, updated, mapped, rfl⟩ := replaced
      have parts := unpack_represented holds unpacked
      apply pack_represented
      intro v member
      obtain ⟨⟨original, index⟩, inside, same⟩ := mem_of_mapM_some mapped v member
      have source : Represented rom heap original := by
        obtain ⟨_, _, same⟩ := List.mem_zipIdx inside
        rw [same]
        exact parts _ (List.getElem_mem _)
      dsimp only at same
      split at same
      · exact replace_represented path original replacement v source replacing same
      · cases same
        exact source

private theorem apply_represented {types : Types} :
    ∀ (paths : List UpdatePath) (base : SourceValue F) (replacements : List (SourceValue F))
      (result : SourceValue F), Represented rom heap base →
      (∀ v ∈ replacements, Represented rom heap v) →
      Update.apply types paths base replacements = some result → Represented rom heap result
  | [], base, [], result, holds, _, applied => by
      simp only [Update.apply, Option.some.injEq] at applied
      subst applied
      exact holds
  | path :: paths, base, replacement :: rest, result, holds, all, applied => by
      simp only [Update.apply, bind, Option.bind_eq_some_iff] at applied
      obtain ⟨updated, replaced, applied⟩ := applied
      exact apply_represented paths updated rest result
        (replace_represented path base replacement updated holds (all _ List.mem_cons_self) replaced)
        (fun v member => all v (List.mem_cons_of_mem _ member)) applied
  | [], _, _ :: _, _, _, _, applied | _ :: _, _, [], _, _, _, applied => by
      simp [Update.apply] at applied

theorem Represented.update {types : Types} {paths : List UpdatePath} {values : List (SourceValue F)}
    {result : SourceValue F} (all : ∀ v ∈ values, Represented rom heap v)
    (updated : Update.value types paths values = .ok result) : Represented rom heap result := by
  cases values with
  | nil => simp [Update.value] at updated
  | cons base replacements =>
      simp only [Update.value] at updated
      split at updated
      · rename_i applied
        cases updated
        exact apply_represented paths base replacements _ (all base List.mem_cons_self)
          (fun v member => all v (List.mem_cons_of_mem _ member)) applied
      · cases updated

/-! ### Patterns -/

private theorem reorderBindings_values {V : Type} :
    ∀ (names : List String) (positions : List Nat) (bindings ordered : List (String × V)),
      reorderBindings names positions bindings = some ordered →
      ∀ b ∈ ordered, ∃ b' ∈ bindings, b'.2 = b.2
  | [], [], _, ordered, reordered => by
      simp only [reorderBindings, Option.some.injEq] at reordered
      subst reordered
      simp
  | name :: names, index :: positions, bindings, ordered, reordered => by
      simp only [reorderBindings, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at reordered
      obtain ⟨⟨first, value⟩, found, tail, rest, rfl⟩ := reordered
      intro b member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨(first, value), List.mem_of_getElem? found, rfl⟩
      · exact reorderBindings_values names positions bindings tail rest b member
  | [], _ :: _, _, _, reordered | _ :: _, [], _, _, reordered => by
      simp [reorderBindings] at reordered

private theorem matchListWith_closed {P : SourceValue F → Prop}
    {matchOne : A → SourceValue F → Except EvalError (Option (Environment F Nat))} :
    ∀ (items : List A) (values : List (SourceValue F)) (bindings : Environment F Nat),
      (∀ a ∈ items, ∀ v ∈ values, ∀ found, matchOne a v = .ok (some found) → ∀ b ∈ found, P b.2) →
      matchListWith matchOne items values = .ok (some bindings) → ∀ b ∈ bindings, P b.2
  | [], [], bindings, _, matched => by
      simp only [matchListWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at matched
      subst matched
      simp
  | a :: items, v :: values, bindings, one, matched => by
      simp only [matchListWith] at matched
      obtain ⟨first, head, rest⟩ := except_bind_ok.mp matched
      cases first with
      | none => simp [pure, Except.pure] at rest
      | some found =>
          simp only at rest
          obtain ⟨second, tail, finish⟩ := except_bind_ok.mp rest
          cases second with
          | none => simp [pure, Except.pure] at finish
          | some others =>
              simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at finish
              subst finish
              intro b member
              rcases List.mem_append.mp member with member | member
              · exact one a List.mem_cons_self v List.mem_cons_self found head b member
              · exact matchListWith_closed items values others
                  (fun a' ha v' hv => one a' (List.mem_cons_of_mem _ ha) v' (List.mem_cons_of_mem _ hv))
                  tail b member
  | [], _ :: _, _, _, matched | _ :: _, [], _, _, matched => by
      simp [matchListWith, pure, Except.pure] at matched

/-- Pattern bindings are parts of the matched value or of cells it points to. -/
theorem matchPatternWith_closed {P : SourceValue F → Prop}
    (tuples : ∀ values, P (.tuple values) → ∀ v ∈ values, P v)
    (constructs : ∀ name ctor values, P (.construct name ctor values) → ∀ v ∈ values, P v)
    (loads : ∀ v s, P v → loadValue heap v = .ok s → P s)
    (constant : String → Ty → Except EvalError (Pattern F)) :
    ∀ (depth : Nat) (types : Types) (pat : Pattern F) (value : SourceValue F)
      (bindings : Environment F Nat),
      P value → matchPatternWith constant depth types heap pat value = .ok (some bindings) →
      ∀ b ∈ bindings, P b.2
  | depth, types, .literal x, value, bindings, _, matched => by
      have empty : bindings = [] := by
        cases value <;> simp only [matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure,
          Except.ok.injEq] at matched
        · split at matched
          · simp at matched
            first | exact matched | exact matched.symm
          · cases matched
        all_goals cases matched
      subst empty
      simp
  | depth, types, .wildcard, value, bindings, _, matched => by
      simp only [matchPatternWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at matched
      subst matched
      simp
  | depth, types, .bind name, value, bindings, holds, matched => by
      simp only [matchPatternWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at matched
      subst matched
      simpa using holds
  | depth, types, .global name annotation, value, bindings, holds, matched => by
      cases annotation with
      | none => simp [matchPatternWith, throw, throwThe, MonadExceptOf.throw] at matched
      | some type =>
          cases depth with
          | zero => simp [matchPatternWith, throw, throwThe, MonadExceptOf.throw] at matched
          | succ depth =>
              simp only [matchPatternWith] at matched
              obtain ⟨body, _, matched⟩ := except_bind_ok.mp matched
              exact matchPatternWith_closed tuples constructs loads constant depth [] body value
                bindings holds matched
  | depth, types, .load pat, value, bindings, holds, matched => by
      simp only [matchPatternWith] at matched
      obtain ⟨loaded, load, matched⟩ := except_bind_ok.mp matched
      exact matchPatternWith_closed tuples constructs loads constant depth types pat loaded bindings
        (loads value loaded holds load) matched
  | depth, types, .orElse left right layout, value, bindings, holds, matched => by
      simp only [matchPatternWith] at matched
      obtain ⟨leftResult, leftMatched, rest⟩ := except_bind_ok.mp matched
      cases leftResult with
      | some found =>
          have closed := matchPatternWith_closed tuples constructs loads constant depth types left
            value found holds leftMatched
          simp only [pure, Except.pure, bind, Except.bind] at rest
          cases reordered : reorderBindings layout.names (List.range layout.names.length) found with
          | none => simp [reordered, throw, throwThe, MonadExceptOf.throw] at rest
          | some ordered =>
              simp only [reordered, Except.ok.injEq, Option.some.injEq] at rest
              subst rest
              intro b member
              obtain ⟨b', inside, same⟩ := reorderBindings_values _ _ _ _ reordered b member
              rw [← same]
              exact closed b' inside
      | none =>
          simp only at rest
          obtain ⟨pair, mapped, rest⟩ := except_bind_ok.mp rest
          cases rightMatched : matchPatternWith constant depth types heap right value with
          | error e => simp [rightMatched, Except.map] at mapped
          | ok result =>
              simp only [rightMatched, Except.map, Except.ok.injEq] at mapped
              subst mapped
              cases result with
              | none => simp [pure, Except.pure] at rest
              | some found =>
                  have closed := matchPatternWith_closed tuples constructs loads constant depth types
                    right value found holds rightMatched
                  simp only at rest
                  cases reordered : reorderBindings layout.names layout.rightOrder found with
                  | none => simp [reordered, throw, throwThe, MonadExceptOf.throw] at rest
                  | some ordered =>
                      simp only [reordered, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at rest
                      subst rest
                      intro b member
                      obtain ⟨b', inside, same⟩ := reorderBindings_values _ _ _ _ reordered b member
                      rw [← same]
                      exact closed b' inside
  | depth, types, .tuple ps, value, bindings, holds, matched => by
      cases value with
      | tuple values =>
          simp only [matchPatternWith] at matched
          split at matched
          · simp [pure, Except.pure, bind, Except.bind] at matched
          · exact matchListWith_closed ps.attach values bindings
              (fun pat _ v member found one => matchPatternWith_closed tuples constructs loads constant
                depth types pat.val v found (tuples values holds v member) one) matched
      | field | ptr | construct => simp [matchPatternWith, pure, Except.pure] at matched
  | depth, types, .array ps, value, bindings, holds, matched => by
      cases value with
      | tuple values =>
          simp only [matchPatternWith] at matched
          split at matched
          · simp [pure, Except.pure, bind, Except.bind] at matched
          · exact matchListWith_closed ps.attach values bindings
              (fun pat _ v member found one => matchPatternWith_closed tuples constructs loads constant
                depth types pat.val v found (tuples values holds v member) one) matched
      | field | ptr | construct => simp [matchPatternWith, pure, Except.pure] at matched
  | depth, types, .repeat pat n, value, bindings, holds, matched => by
      cases value with
      | tuple values =>
          simp only [matchPatternWith] at matched
          split at matched
          · simp [pure, Except.pure, bind, Except.bind] at matched
          · exact matchListWith_closed (List.replicate n ()) values bindings
              (fun _ _ v member found one => matchPatternWith_closed tuples constructs loads constant
                depth types pat v found (tuples values holds v member) one) matched
      | field | ptr | construct => simp [matchPatternWith, pure, Except.pure] at matched
  | depth, types, .record head ps, value, bindings, holds, matched => by
      cases value with
      | construct name ctor values =>
          simp only [matchPatternWith] at matched
          split at matched
          · simp [pure, Except.pure, bind, Except.bind] at matched
          · split at matched
            · simp [pure, Except.pure, bind, Except.bind] at matched
            · exact matchListWith_closed _ values bindings
                (fun child _ v member found one => by
                  cases child with
                  | none =>
                      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at one
                      subst one
                      simp
                  | some pat =>
                      exact matchPatternWith_closed tuples constructs loads constant depth types pat.val v
                        found (constructs _ _ values holds v member) one) matched
      | field | ptr | tuple => simp [matchPatternWith, pure, Except.pure] at matched
  | depth, types, .construct t c ps, value, bindings, holds, matched => by
      cases value with
      | construct name ctor values =>
          simp only [matchPatternWith] at matched
          split at matched
          · simp [pure, Except.pure, bind, Except.bind] at matched
          · exact matchListWith_closed ps.attach values bindings
              (fun pat _ v member found one => matchPatternWith_closed tuples constructs loads constant
                depth types pat.val v found (constructs _ _ values holds v member) one) matched
      | field | ptr | tuple => simp [matchPatternWith, pure, Except.pure] at matched
  | depth, types, .constructAs params t c ps, value, bindings, holds, matched => by
      cases value with
      | construct name ctor values =>
          simp only [matchPatternWith] at matched
          split at matched
          · simp [pure, Except.pure, bind, Except.bind] at matched
          · exact matchListWith_closed ps.attach values bindings
              (fun pat _ v member found one => matchPatternWith_closed tuples constructs loads constant
                depth types pat.val v found (constructs _ _ values holds v member) one) matched
      | field | ptr | tuple => simp [matchPatternWith, pure, Except.pure] at matched
termination_by depth _ pat _ _ _ _ => (depth, sizeOf pat)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | skip
  all_goals try have := List.sizeOf_lt_of_mem pat.property
  all_goals try simp_all only [Pattern.tuple.sizeOf_spec, Pattern.array.sizeOf_spec,
    Pattern.construct.sizeOf_spec, Pattern.constructAs.sizeOf_spec, Pattern.record.sizeOf_spec]
  all_goals omega

theorem Represented.matchPattern {world : World F} {types : Types}
    {pattern : Pattern F} {value : SourceValue F} {bindings : Environment F Nat}
    (holds : Represented rom heap value)
    (matched : world.matchPattern types heap pattern value = .ok (some bindings)) :
    ∀ b ∈ bindings, Represented rom heap b.2 :=
  matchPatternWith_closed (P := Represented rom heap)
    (fun _ whole => Represented.tuple_iff.mp whole)
    (fun _ _ _ whole => Represented.construct_iff.mp whole)
    (fun _ _ holds loaded => holds.load loaded)
    world.constant world.constDepth types pattern value bindings holds matched

theorem Represented.selectArm {world : World F} {types : Types}
    {value : SourceValue F} (holds : Represented rom heap value) :
    ∀ (arms : List (Pattern F × Expr F)) (bindings : Environment F Nat) (body : Expr F),
      selectArm world types heap value arms = .ok (some (bindings, body)) →
      ∀ b ∈ bindings, Represented rom heap b.2
  | [], _, _, selected => by simp [SourceSemantics.selectArm, pure, Except.pure] at selected
  | (pat, arm) :: arms, bindings, body, selected => by
      simp only [SourceSemantics.selectArm] at selected
      obtain ⟨result, matched, rest⟩ := except_bind_ok.mp selected
      cases result with
      | some found =>
          simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at rest
          obtain ⟨rfl, _⟩ := rest
          exact Represented.matchPattern holds matched
      | none => exact Represented.selectArm holds arms bindings body rest

end Representation

/-! ## Values of an observed derivation are represented -/

section Observed

variable {rom : ROM F}

private theorem env_mono {locals : Environment F Nat} {heap larger : Heap F}
    (env : ∀ b ∈ locals, Represented rom heap b.2) (grows : heap <+: larger) :
    ∀ b ∈ locals, Represented rom larger b.2 :=
  fun b member => (env b member).mono grows

private theorem env_append {bindings locals : Environment F Nat} {heap : Heap F}
    (first : ∀ b ∈ bindings, Represented rom heap b.2) (second : ∀ b ∈ locals, Represented rom heap b.2) :
    ∀ b ∈ bindings ++ locals, Represented rom heap b.2 := by
  intro b member
  rcases List.mem_append.mp member with member | member
  · exact first b member
  · exact second b member

/-- Along an observed derivation the heap only grows. When the final heap's
cells are ROM cells, every value computed and every argument of every call is
represented relative to the heap at that point. -/
theorem ObsFn.represented (prepares : PreparesFromArgs world) {H : Heap F} (cells : HeapInROM rom H)
    {name : String} {args : List (SourceValue F)} {before after : Heap F} {result : SourceValue F}
    {calls : List (Call F)} (observed : ObsFn world name args before result after calls) :
    before <+: after ∧ (after <+: H → (∀ v ∈ args, Represented rom before v) →
      Represented rom after result ∧ CallsInROM rom calls) := by
  induction observed using ObsFn.rec
    (motive_1 := fun types locals expr before result after calls _ =>
      before <+: after ∧ (after <+: H → (∀ b ∈ locals, Represented rom before b.2) →
        Represented rom after result ∧ CallsInROM rom calls))
    (motive_2 := fun types locals exprs before values after calls _ =>
      before <+: after ∧ (after <+: H → (∀ b ∈ locals, Represented rom before b.2) →
        (∀ v ∈ values, Represented rom after v) ∧ CallsInROM rom calls))
    (motive_4 := fun types locals expr before target result after calls _ =>
      before <+: after ∧ (after <+: H → (∀ b ∈ locals, Represented rom before b.2) →
        Represented rom after result ∧ CallsInROM rom calls))
    (motive_5 := fun types locals exprs before target result after calls _ =>
      before <+: after ∧ (after <+: H → (∀ b ∈ locals, Represented rom before b.2) →
        Represented rom after result ∧ CallsInROM rom calls)) with
  | block _ ih => exact ih
  | blockExit _ ih => exact ih
  | literal => exact ⟨List.prefix_refl _, fun _ _ => ⟨Represented.field _, CallsInROM.nil⟩⟩
  | var lookup =>
      exact ⟨List.prefix_refl _, fun _ env =>
        ⟨env _ (List.mem_of_find?_eq_some lookup), CallsInROM.nil⟩⟩
  | global _ _ _ ih => exact ⟨ih.1, fun bound _ => ih.2 bound (by simp)⟩
  | tuple _ ih =>
      exact ⟨ih.1, fun bound env =>
        ⟨Represented.tuple_iff.mpr (ih.2 bound env).1, (ih.2 bound env).2⟩⟩
  | array _ ih =>
      exact ⟨ih.1, fun bound env =>
        ⟨Represented.tuple_iff.mpr (ih.2 bound env).1, (ih.2 bound env).2⟩⟩
  | «repeat» _ ih =>
      refine ⟨ih.1, fun bound env => ⟨?_, (ih.2 bound env).2⟩⟩
      apply Represented.tuple_iff.mpr
      intro v member
      rw [List.eq_of_mem_replicate member]
      exact (ih.2 bound env).1
  | index _ projected ih =>
      exact ⟨ih.1, fun bound env => ⟨(ih.2 bound env).1.project projected, (ih.2 bound env).2⟩⟩
  | slice _ sliced ih =>
      exact ⟨ih.1, fun bound env => ⟨(ih.2 bound env).1.slice sliced, (ih.2 bound env).2⟩⟩
  | builtin _ applied ih =>
      exact ⟨ih.1, fun bound env =>
        ⟨Represented.builtin (ih.2 bound env).1 applied, (ih.2 bound env).2⟩⟩
  | update _ updated ih =>
      exact ⟨ih.1, fun bound env =>
        ⟨Represented.update (ih.2 bound env).1 updated, (ih.2 bound env).2⟩⟩
  | record _ ih =>
      exact ⟨ih.1, fun bound env =>
        ⟨Represented.construct_iff.mpr (Represented.order (ih.2 bound env).1), (ih.2 bound env).2⟩⟩
  | member _ projected ih =>
      exact ⟨ih.1, fun bound env => ⟨(ih.2 bound env).1.member projected, (ih.2 bound env).2⟩⟩
  | construct _ ih =>
      exact ⟨ih.1, fun bound env =>
        ⟨Represented.construct_iff.mpr (ih.2 bound env).1, (ih.2 bound env).2⟩⟩
  | constructAs _ ih =>
      exact ⟨ih.1, fun bound env =>
        ⟨Represented.construct_iff.mpr (ih.2 bound env).1, (ih.2 bound env).2⟩⟩
  | project _ projected ih =>
      exact ⟨ih.1, fun bound env => ⟨(ih.2 bound env).1.project projected, (ih.2 bound env).2⟩⟩
  | letValue _ matched _ ih₁ ih₂ =>
      refine ⟨ih₁.1.trans ih₂.1, fun bound env => ?_⟩
      have first := ih₁.2 (ih₂.1.trans bound) env
      have second := ih₂.2 bound
        (env_append (first.1.matchPattern matched) (env_mono env ih₁.1))
      exact ⟨second.1, first.2.append second.2⟩
  | store _ ih =>
      refine ⟨ih.1.trans (List.prefix_append _ _), fun bound env => ?_⟩
      have first := ih.2 ((List.prefix_append _ _).trans bound) env
      exact ⟨Represented.store cells bound, first.2⟩
  | load _ loaded ih =>
      exact ⟨ih.1, fun bound env => ⟨(ih.2 bound env).1.load loaded, (ih.2 bound env).2⟩⟩
  | hint _ _ ih =>
      exact ⟨ih.1, fun bound env =>
        ⟨Represented.ofPointerFree _ (Constant.toValue_pointerFree _), (ih.2 bound env).2⟩⟩
  | neg _ operation ih =>
      exact ⟨ih.1, fun bound env => ⟨Represented.neg operation, (ih.2 bound env).2⟩⟩
  | binary _ _ operation ih₁ ih₂ =>
      refine ⟨ih₁.1.trans ih₂.1, fun bound env => ?_⟩
      have first := ih₁.2 (ih₂.1.trans bound) env
      have second := ih₂.2 bound (env_mono env ih₁.1)
      exact ⟨Represented.binary operation, first.2.append second.2⟩
  | call _ _ ih₁ ih₂ =>
      refine ⟨ih₁.1.trans ih₂.1, fun bound env => ?_⟩
      have first := ih₁.2 (ih₂.1.trans bound) env
      have second := ih₂.2 bound first.1
      refine ⟨second.1, first.2.append ?_⟩
      intro c member
      rcases List.mem_cons.mp member with rfl | member
      · exact first.1
      · exact second.2 c member
  | matchValue _ selected _ ih₁ ih₂ =>
      refine ⟨ih₁.1.trans ih₂.1, fun bound env => ?_⟩
      have first := ih₁.2 (ih₂.1.trans bound) env
      have second := ih₂.2 bound
        (env_append (first.1.selectArm _ _ _ selected) (env_mono env ih₁.1))
      exact ⟨second.1, first.2.append second.2⟩
  | nil => exact ⟨List.prefix_refl _, fun _ _ => ⟨by simp, CallsInROM.nil⟩⟩
  | cons _ _ ih₁ ih₂ =>
      refine ⟨ih₁.1.trans ih₂.1, fun bound env => ?_⟩
      have first := ih₁.2 (ih₂.1.trans bound) env
      have second := ih₂.2 bound (env_mono env ih₁.1)
      refine ⟨?_, first.2.append second.2⟩
      intro v member
      rcases List.mem_cons.mp member with rfl | member
      · exact first.1.mono ih₂.1
      · exact second.1 v member
  | intro prepared _ ih =>
      exact ⟨ih.1, fun bound args => ih.2 bound
        (fun b member => args b.2 (prepares _ _ _ _ _ prepared b member))⟩
  | returned prepared _ ih =>
      exact ⟨ih.1, fun bound args => ih.2 bound
        (fun b member => args b.2 (prepares _ _ _ _ _ prepared b member))⟩
  | exit _ ih => exact ih
  | exitPayload _ ih => exact ih
  | fromBlock _ _ ih => exact ih
  | fromGlobal _ _ _ ih => exact ⟨ih.1, fun bound _ => ih.2 bound (by simp)⟩
  | fromTuple _ ih => exact ih
  | fromArray _ ih => exact ih
  | fromRepeat _ ih => exact ih
  | fromIndex _ ih => exact ih
  | fromSlice _ ih => exact ih
  | fromBuiltin _ ih => exact ih
  | fromUpdate _ ih => exact ih
  | fromRecord _ ih => exact ih
  | fromMember _ ih => exact ih
  | fromConstruct _ ih => exact ih
  | fromConstructAs _ ih => exact ih
  | fromProject _ ih => exact ih
  | fromLetValue _ ih => exact ih
  | letBody _ matched _ ih₁ ih₂ =>
      refine ⟨ih₁.1.trans ih₂.1, fun bound env => ?_⟩
      have first := ih₁.2 (ih₂.1.trans bound) env
      have second := ih₂.2 bound
        (env_append (first.1.matchPattern matched) (env_mono env ih₁.1))
      exact ⟨second.1, first.2.append second.2⟩
  | fromStore _ ih => exact ih
  | fromLoad _ ih => exact ih
  | fromHint _ ih => exact ih
  | fromNeg _ ih => exact ih
  | binaryLeft _ ih => exact ih
  | binaryRight _ _ ih₁ ih₂ =>
      refine ⟨ih₁.1.trans ih₂.1, fun bound env => ?_⟩
      have first := ih₁.2 (ih₂.1.trans bound) env
      have second := ih₂.2 bound (env_mono env ih₁.1)
      exact ⟨second.1, first.2.append second.2⟩
  | fromCall _ ih => exact ih
  | fromMatchValue _ ih => exact ih
  | matchBody _ selected _ ih₁ ih₂ =>
      refine ⟨ih₁.1.trans ih₂.1, fun bound env => ?_⟩
      have first := ih₁.2 (ih₂.1.trans bound) env
      have second := ih₂.2 bound
        (env_append (first.1.selectArm _ _ _ selected) (env_mono env ih₁.1))
      exact ⟨second.1, first.2.append second.2⟩
  | head _ ih => exact ih
  | tail _ _ ih₁ ih₂ =>
      refine ⟨ih₁.1.trans ih₂.1, fun bound env => ?_⟩
      have first := ih₁.2 (ih₂.1.trans bound) env
      have second := ih₂.2 bound (env_mono env ih₁.1)
      exact ⟨second.1, first.2.append second.2⟩

/-- **The ROM carries the calls**: an observed derivation from the empty heap
on pointer-free arguments, whose final heap's cells are ROM cells, has every
argument of every recorded call represented in that ROM. -/
theorem ObsFn.callsInROM (prepares : PreparesFromArgs world) {H : Heap F} (cells : HeapInROM rom H)
    {name : String} {args : List (SourceValue F)} {result : SourceValue F} {calls : List (Call F)}
    (free : ∀ v ∈ args, v.pointerFree = true)
    (observed : ObsFn world name args [] result H calls) : CallsInROM rom calls :=
  ((observed.represented prepares cells).2 (List.prefix_refl H)
    (fun v member => Represented.ofPointerFree v (free v member))).2

end Observed

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

namespace Aiur.Generic

open SourceSemantics

variable {F : Type} [Field F] [DecidableEq F]

/-- A source program's world binds a function's parameters to the call's
arguments; a fixed map call binds nothing. -/
theorem Source.world_preparesFromArgs (s : Source F) : PreparesFromArgs s.world := by
  intro name args types locals expr prepared binding member
  simp only [Source.world, sourceWorld] at prepared
  cases found : s.program.sourceFunction? name with
  | none =>
      simp only [found] at prepared
      obtain ⟨constant, _, finished⟩ := except_bind_ok.mp prepared
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at finished
      obtain ⟨_, rfl, _⟩ := finished
      cases member
  | some fn =>
      simp only [found, SourceFunction.prepare] at prepared
      split at prepared
      · simp only [Except.ok.injEq, Prod.mk.injEq] at prepared
        obtain ⟨_, rfl, _⟩ := prepared
        exact (List.of_mem_zip member).2
      · cases prepared

end Aiur.Generic
