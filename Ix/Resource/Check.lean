module

public import Ix.Resource.Basic

/-!
# Deterministic checking of the resource fragment

The address adapter supplies a closed, globally indexed program. Interfaces
of recursive definitions are checked simultaneously. Definitions never acquire
an optimistic no-capture summary: calls use the declared interface and retain
all permitted argument/closure origins. An external interface or special
primitive is an explicit profile assumption, not auxiliary source metadata.

Erased typing is a separate prerequisite. This module also compares the full
resource structure of types, so erased definitional equality cannot launder a
different higher-order contract. Unsupported reductions exhaust a fixed bound
or report an error instead of silently discarding modes.
-/

@[expose] public section

namespace Ix.Resource

open Ixon

inductive DeclKind where
  | definition
  | assumption
  | constructor
  | typeConstructor
  deriving BEq, Repr, Inhabited

structure Declaration where
  type : Ixon.Expr
  body : Option Ixon.Expr := none
  kind : DeclKind := .definition
  deriving BEq, Repr, Inhabited

/-- Checked transparent fields. The adapter derives these from the addressed
constructor interface; an unknown projection has no default resource rule. -/
structure Field where
  typeRef : UInt64
  index : UInt64
  type : Ixon.Expr
  contract : ValueContract
  deriving BEq, Repr, Inhabited

structure Program where
  declarations : Array Declaration
  /-- Members and constructors addressed by the same mutual block. -/
  groups : Array (Array Nat) := #[]
  /-- Additional addressed executable syntax, currently recursor rules.
  These participate in dependency/relevance scanning even when the interface
  requires a profile assumption instead of ordinary lambda checking. -/
  auxiliary : Array (Nat × Ixon.Expr) := #[]
  sharing : Array Ixon.Expr := #[]
  fields : Array Field := #[]
  natType : Option Ixon.Expr := none
  stringType : Option Ixon.Expr := none
  /-- Types whose shared views have a checked, duplicable representation.
  Abstract type parameters are deliberately absent from this list. -/
  shareableTypes : Array UInt64 := #[]
  /-- Profile-bound non-strict selection primitives, with exactly selector,
  left alternative, and right alternative as their three arguments. -/
  choices : Array UInt64 := #[]
  deriving BEq, Repr, Inhabited

structure Context where
  program : Program
  /-- Oldest binding first; Ixon variables still count from the innermost. -/
  vars : Array OwnerId := #[]
  scope : ScopeId := 0
  deriving Inhabited

def declaration (program : Program) (index : UInt64) : CheckM Declaration :=
  match program.declarations[index.toNat]? with
  | some d => pure d
  | none => throw (.badReference index.toNat)

def expansion (program : Program) (index : UInt64) : CheckM Ixon.Expr :=
  match program.sharing[index.toNat]? with
  | some e => pure e
  | none => throw (.unresolvedSharing index.toNat)

def literalType (type : Option Ixon.Expr) : CheckM Ixon.Expr :=
  match type with
  | some type => pure type
  | none => throw (.unsupported "literal type is absent from the addressed profile")

def checkedIndex (n : Nat) : CheckM UInt64 :=
  if n < UInt64.size then pure n.toUInt64 else throw (.unsupported "readVariable index overflow")

def shift (program : Program) : Nat → Ixon.Expr → Nat → Nat → CheckM Ixon.Expr
  | 0, _, _, _ => throw .budget
  | fuel + 1, e, amount, cutoff => do
    tick
    match e with
    | .var idx =>
      if idx.toNat < cutoff then return e
      else return .var (← checkedIndex (idx.toNat + amount))
    | .app fn arg =>
      return .app (← shift program fuel fn amount cutoff) (← shift program fuel arg amount cutoff)
    | .lam c ty body =>
      return .lam c (← shift program fuel ty amount cutoff)
        (← shift program fuel body amount (cutoff + 1))
    | .all c r ty body =>
      return .all c r (← shift program fuel ty amount cutoff)
        (← shift program fuel body amount (cutoff + 1))
    | .letE c ty val body =>
      return .letE c (← shift program fuel ty amount cutoff)
        (← shift program fuel val amount cutoff)
        (← shift program fuel body amount (cutoff + 1))
    | .prj t i val => return .prj t i (← shift program fuel val amount cutoff)
    | .share idx => shift program fuel (← expansion program idx) amount cutoff
    | .recur .. => throw (.unsupported "unresolved recursive reference")
    | _ => return e

def substitute (program : Program) : Nat → Ixon.Expr → Ixon.Expr → Nat → CheckM Ixon.Expr
  | 0, _, _, _ => throw .budget
  | fuel + 1, e, value, depth => do
    tick
    match e with
    | .var idx =>
      if idx.toNat == depth then shift program fuel value depth 0
      else if idx.toNat > depth then return .var (idx - 1)
      else return e
    | .app fn arg =>
      return .app (← substitute program fuel fn value depth)
        (← substitute program fuel arg value depth)
    | .lam c ty body =>
      return .lam c (← substitute program fuel ty value depth)
        (← substitute program fuel body value (depth + 1))
    | .all c r ty body =>
      return .all c r (← substitute program fuel ty value depth)
        (← substitute program fuel body value (depth + 1))
    | .letE c ty val body =>
      return .letE c (← substitute program fuel ty value depth)
        (← substitute program fuel val value depth)
        (← substitute program fuel body value (depth + 1))
    | .prj t i val => return .prj t i (← substitute program fuel val value depth)
    | .share idx => substitute program fuel (← expansion program idx) value depth
    | .recur .. => throw (.unsupported "unresolved recursive reference")
    | _ => return e

/-- This reduction is only for resource interfaces. The ordinary typechecker
separately validates universes, dependent types, and definitional equality. -/
def whnf (program : Program) : Nat → Ixon.Expr → CheckM Ixon.Expr
  | 0, _ => throw .budget
  | fuel + 1, e => do
    tick
    match e with
    | .share idx => whnf program fuel (← expansion program idx)
    | .letE _ _ value body =>
      whnf program fuel (← substitute program fuel body value 0)
    | .app fn arg =>
      let fn ← whnf program fuel fn
      match fn with
      | .lam _ _ body => whnf program fuel (← substitute program fuel body arg 0)
      | _ => return .app fn arg
    | .ref idx _ =>
      let d ← declaration program idx
      match d.body with
      | some body => whnf program fuel body
      | none => return e
    | .recur .. => throw (.unsupported "unresolved recursive reference")
    | _ => return e

def compatible (program : Program) : Nat → Ixon.Expr → Ixon.Expr → CheckM Bool
  | 0, _, _ => throw .budget
  | fuel + 1, left, right => do
    tick
    -- Exact syntax is safe even when an opaque type has no reduction rule.
    if left == right then return true
    let left ← whnf program fuel left
    let right ← whnf program fuel right
    match left, right with
    | .all c r a b, .all c' r' a' b' =>
      if c != c' || r != r' then return false
      if !(← compatible program fuel a a') then return false
      compatible program fuel b b'
    | .lam c a b, .lam c' a' b' =>
      if c != c' then return false
      if !(← compatible program fuel a a') then return false
      compatible program fuel b b'
    | .app f a, .app f' a' =>
      if !(← compatible program fuel f f') then return false
      compatible program fuel a a'
    | .prj t i v, .prj t' i' v' =>
      if t != t' || i != i' then return false
      compatible program fuel v v'
    | .sort _, .sort _ => return true
    | .ref i _, .ref j _ => return i == j
    | _, _ => return left == right

def requireType (program : Program) (fuel : Nat) (actual expected : Ixon.Expr) : CheckM Unit := do
  if !(← compatible program fuel actual expected) then throw .typeMismatch

def arrow (program : Program) (fuel : Nat) (type : Ixon.Expr) :
    CheckM (BinderContract × ValueContract × Ixon.Expr × Ixon.Expr) := do
  match ← whnf program fuel type with
  | .all input result domain codomain => return (input, result, domain, codomain)
  | _ => throw (.unsupported "a callable interface must expose its arrow contracts")

def isShareable (program : Program) (fuel : Nat) (type : Ixon.Expr) : CheckM Bool := do
  let type ← whnf program fuel type
  match type with
  | .ref idx _ => return program.shareableTypes.contains idx
  | .sort _ => return true
  | _ => return false

def readVariable (ctx : Context) (fuel : Nat) (index : UInt64) (uses : Uses) : CheckM Value := do
  let n := index.toNat
  if n >= ctx.vars.size then throw (.unbound n)
  let id := ctx.vars[ctx.vars.size - 1 - n]!
  let b ← binding id
  charge id uses
  if let some root := b.value.loanRoot then
    let owner ← binding root
    if !owner.owner.live then throw (.moved root)
  let type ← shift ctx.program fuel b.value.type (n + 1) 0
  return { b.value with
    type
    place := some id
    owned := if b.owner.unique then .unique else .shared }

/-- Resolve a borrow place without charging a consumption. Every projection
must have a checked field rule; all projected loans suspend the whole root. -/
def place (ctx : Context) : Nat → Ixon.Expr → CheckM Value
  | 0, _ => throw .budget
  | fuel + 1, e => do
    tick
    match e with
    | .var idx =>
      let value ← readVariable ctx fuel idx .erased
      let some id := value.place | throw .invalidPlace
      if (← binding id).contract.uses == .erased then
        throw (.unsupported "an erased binding cannot be borrowed")
      return value
    | .share idx => place ctx fuel (← expansion ctx.program idx)
    | .prj t i value =>
      let value ← place ctx fuel value
      let some field := ctx.program.fields.find? (fun f => f.typeRef == t && f.index == i)
        | throw (.unsupported "projection has no checked field rule")
      let duplicable ← if field.contract.owned == .shared then pure true
        else isShareable ctx.program fuel field.type
      return { value with
        type := field.type
        duplicable
        owned := if value.owned == .unique && field.contract.owned == .unique then .unique else .shared }
    | _ => throw .invalidPlace

/-- Infer the interface before executing any resource transition. Calls need
the actual result locality to choose their scope: a call returning an
unrestricted value may inspect a short-lived view even when its result will
subsequently be narrowed to an outer local scope. -/
def typeOf : Nat → Context → Ixon.Expr → CheckM Ixon.Expr
  | 0, _, _ => throw .budget
  | fuel + 1, ctx, e => do
    tick
    match e with
    | .var index =>
      let n := index.toNat
      if n >= ctx.vars.size then throw (.unbound n)
      let b ← binding ctx.vars[ctx.vars.size - 1 - n]!
      shift ctx.program fuel b.value.type (n + 1) 0
    | .ref index _ => return (← declaration ctx.program index).type
    | .share index => typeOf fuel ctx (← expansion ctx.program index)
    | .recur .. => throw (.unsupported "unresolved recursive reference")
    | .sort _ | .all .. => return .sort 0
    | .nat _ => literalType ctx.program.natType
    | .str _ => literalType ctx.program.stringType
    | .prj typeRef index _ =>
      let some field := ctx.program.fields.find? (fun f => f.typeRef == typeRef && f.index == index)
        | throw (.unsupported "projection has no checked field rule")
      return field.type
    | .app fn arg =>
      let (_, _, _, codomain) ← arrow ctx.program fuel (← typeOf fuel ctx fn)
      substitute ctx.program fuel codomain arg 0
    | .lam input domain body =>
      let before ← get
      let id ← pushBinding input { type := domain }
      let codomain ← typeOf fuel { ctx with vars := ctx.vars.push id } body
      modify fun s => { s with bindings := before.bindings }
      return .all input .shared domain codomain
    | .letE contract type initializer body =>
      let before ← get
      let id ← pushBinding contract.binder { type }
      let type ← typeOf fuel { ctx with vars := ctx.vars.push id } body
      modify fun s => { s with bindings := before.bindings }
      substitute ctx.program fuel type initializer 0

def splitApp (program : Program) :
    Nat → Ixon.Expr → List Ixon.Expr → CheckM (Ixon.Expr × List Ixon.Expr)
  | 0, _, _ => throw .budget
  | fuel + 1, e, args => do
    tick
    match e with
    | .app fn arg => splitApp program fuel fn (arg :: args)
    | .share index => splitApp program fuel (← expansion program index) args
    | _ => return (e, args)

def finishValue (ctx : Context) (fuel : Nat) (destination : ScopeId)
    (expected : Option (Ixon.Expr × ValueContract)) (value : Value) : CheckM Value := do
  match expected with
  | none => return value
  | some (type, contract) =>
    requireType ctx.program fuel value.type type
    consumeAs contract destination value

/-- Join only bindings that existed before an alternative. Branch-local
bindings cannot escape: returned places have already been consumed, and
retained local origins are checked before their lexical scopes close. -/
def joinBindings (count : Nat) (left right : State) : CheckM (Array Binding) := do
  let mut result := #[]
  for i in [0:count] do
    let some a := left.bindings[i]? | throw (.unbound i)
    let some b := right.bindings[i]? | throw (.unbound i)
    result := result.push { a with
      owner := joinOwner a.owner b.owner
      demand := a.demand.join b.demand
      touched := a.touched || b.touched }
  return result

def analyze : Nat → Context → Ixon.Expr → Option (Ixon.Expr × ValueContract) →
    ScopeId → Uses → CheckM Value
  | 0, _, _, _, _, _ => throw .budget
  | fuel + 1, ctx, e, expected, destination, grade => do
    tick
    -- Zero computation is checked by the prerequisite erased typechecker.
    -- It has no ownership events, captures, or runtime origins.
    if grade == .erased then
      let type ← typeOf fuel ctx e
      if let some (expectedType, _) := expected then
        requireType ctx.program fuel type expectedType
      return { type, owned := .unique }
    if let some (type, _) := expected then
      if let .sort _ ← whnf ctx.program fuel type then
        return { type, owned := .unique }
    if grade != .linear then
      let before ← get
      set { before with bindings := before.bindings.map fun (b : Binding) =>
        { b with demand := .erased, touched := false } }
      let output ← analyze fuel ctx e expected destination .linear
      let after ← get
      let mut bindings := after.bindings
      for id in [0:before.bindings.size] do
        let old := before.bindings[id]!
        let used := after.bindings[id]!
        bindings := bindings.set! id { used with
          demand := old.demand.add (grade.mul used.demand)
          touched := old.touched || used.touched }
      set { after with bindings }
      return output
    let value ← match e with
      | .share idx => analyze fuel ctx (← expansion ctx.program idx) expected destination grade
      | .var idx => readVariable ctx fuel idx grade
      | .ref idx _ =>
        if ctx.program.choices.contains idx then
          throw (.unsupported "selection primitives cannot escape as function values")
        let d ← declaration ctx.program idx
        pure { type := d.type }
      | .recur .. => throw (.unsupported "unresolved recursive reference")
      | .sort _ | .all .. => pure { type := .sort 0, owned := .unique }
      | .nat _ => pure { type := ← literalType ctx.program.natType, owned := .unique }
      | .str _ => pure { type := ← literalType ctx.program.stringType, owned := .unique }
      | .lam input domain body => do
        let (result, codomain) ← match expected with
          | some (type, _) => do
            let (declared, result, ty, codomain) ← arrow ctx.program fuel type
            if input != declared then throw .binderMismatch
            requireType ctx.program fuel domain ty
            pure (result, some codomain)
          | none => pure (.shared, none)
        let before ← get
        -- Deferred closure checking gets fresh per-invocation demands.
        set { before with bindings := before.bindings.map fun (b : Binding) =>
          { b with demand := .erased, touched := false } }
        let callerScope ← newScope ctx.scope
        let bodyScope ← newScope callerScope
        let origins := if input.value.locality == .local then [callerScope] else []
        let duplicable ← if input.value.owned == .shared then pure true
          else isShareable ctx.program fuel domain
        let parameter ← pushBinding input {
          type := domain
          owned := input.value.owned
          origins
          duplicable }
        let bodyCtx := { ctx with vars := ctx.vars.push parameter, scope := bodyScope }
        let bodyExpected := codomain.map (fun ty => (ty, result))
        let output ← analyze fuel bodyCtx body bodyExpected callerScope .linear
        let output ← if bodyExpected.isSome then pure output else consumeAs result callerScope output
        validateUsage parameter
        let after ← get
        let mut origins := []
        let mut duplicable := true
        let mut bindings := before.bindings
        for id in [0:before.bindings.size] do
          let old := before.bindings[id]!
          let used := after.bindings[id]!
          let mut owner := used.owner
          let mut demand := used.demand
          if used.touched then
            origins := unionOrigins origins old.value.origins
            if old.contract.uses != .many || !old.value.duplicable then duplicable := false
            if old.owner.unique then
              -- Capturing an owner transfers its availability even when the
              -- body only borrows it. An explicit outer view permits reusable
              -- local closures without transferring that owner.
              let _ ← liftExcept (moveOwner id old.owner)
              owner := { owner with live := false }
              if demand == .erased then demand := .linear
              duplicable := false
          bindings := bindings.set! id { old with
            owner
            demand := old.demand.add (grade.mul demand)
            touched := old.touched || used.touched }
        set { after with bindings }
        let codomain := codomain.getD output.type
        pure {
          type := .all input result domain codomain
          owned := .unique
          origins
          duplicable }
      | .letE contract type initializer body => do
        let scope ← newScope ctx.scope
        let inner := { ctx with scope }
        let initialized ← match contract.kind with
          | .value =>
            analyze fuel ctx initializer (some (type, contract.binder.value))
              (if contract.binder.value.locality == .local then scope else destination)
              (grade.mul contract.binder.uses)
          | .borrowShared => do
            if contract.binder.value != .localShared then throw .invalidBorrow
            let v ← place ctx fuel initializer
            requireType ctx.program fuel v.type type
            if !(← isShareable ctx.program fuel type) && !v.duplicable then throw .nonduplicable
            let some ownerPlace := v.place | throw .invalidPlace
            let root := v.loanRoot.getD ownerPlace
            let b ← binding root
            let owner ← liftExcept (beginLoan root scope b.owner)
            setBinding root { b with owner }
            pure { v with
              owned := .shared
              duplicable := true
              origins := unionOrigins v.origins [scope]
              place := none
              loanRoot := some root }
        let id ← pushBinding contract.binder { initialized with type }
        let bodyCtx := { inner with vars := inner.vars.push id }
        let bodyExpected ← match expected with
          | none => pure none
          | some (ty, mode) => pure (some (← shift ctx.program fuel ty 1 0, mode))
        let output ← analyze fuel bodyCtx body bodyExpected destination grade
        validateUsage id
        let output ← materialize output
        closeScope scope output
        let type ← substitute ctx.program fuel output.type initializer 0
        pure { output with type }
      | .prj typeRef index value => do
        let value ← analyze fuel ctx value none destination grade
        let some field := ctx.program.fields.find? (fun f => f.typeRef == typeRef && f.index == index)
          | throw (.unsupported "projection has no checked field rule")
        let duplicable ← if field.contract.owned == .shared then pure true
          else isShareable ctx.program fuel field.type
        pure { value with
          type := field.type
          duplicable
          owned := if value.owned == .unique && field.contract.owned == .unique then .unique else .shared }
      | .app fn arg => do
        let ordinary : CheckM Value := do
          let fnType ← typeOf fuel ctx fn
          let (input, result, domain, codomain) ← arrow ctx.program fuel fnType
          let callScope := if result.locality == .local then destination else ctx.scope
          let fnValue ← analyze fuel ctx fn none callScope grade
          requireType ctx.program fuel fnValue.type fnType
          invoke fnValue
          let argValue ← analyze fuel ctx arg (some (domain, input.value)) callScope (grade.mul input.uses)
          let type ← substitute ctx.program fuel codomain arg 0
          let origins := if result.locality == .local then
            unionOrigins (unionOrigins fnValue.origins argValue.origins) [callScope] else []
          let duplicable ← if result.owned == .shared then pure true
            else isShareable ctx.program fuel type
          pure {
            type
            owned := result.owned
            origins
            duplicable }
        let (head, arguments) ← splitApp ctx.program fuel e []
        match head, arguments with
        | .ref index _, [selector, left, right] =>
          if ctx.program.choices.contains index then
            let decl ← declaration ctx.program index
            let (c, _, selectorType, tail) ← arrow ctx.program fuel decl.type
            let _ ← analyze fuel ctx selector (some (selectorType, c.value)) ctx.scope (grade.mul c.uses)
            let tail ← substitute ctx.program fuel tail selector 0
            let (_, _, leftType, tail) ← arrow ctx.program fuel tail
            let tail ← substitute ctx.program fuel tail left 0
            let (_, result, rightType, outputType) ← arrow ctx.program fuel tail
            let outputType ← substitute ctx.program fuel outputType right 0
            requireType ctx.program fuel leftType rightType
            requireType ctx.program fuel leftType outputType
            let before ← get
            let left ← analyze fuel ctx left (some (leftType, result)) destination grade
            let leftState ← get
            -- Preserve fresh scope identities and charge the shared budget
            -- while restoring the pre-branch owner/use state.
            set { leftState with bindings := before.bindings }
            let right ← analyze fuel ctx right (some (rightType, result)) destination grade
            let rightState ← get
            let bindings ← joinBindings before.bindings.size leftState rightState
            set { rightState with bindings }
            pure { joinValue left right with type := outputType }
          else ordinary
        | _, _ =>
          if let .ref index _ := head then
            if ctx.program.choices.contains index then
              throw (.unsupported "selection primitives require a complete application")
          ordinary
    finishValue ctx fuel destination expected value

def checkDefinition (program : Program) (index : Nat) (limits : Limits := {}) : Except Error Unit := do
  let some declaration := program.declarations[index]? | throw (.badReference index)
  let some body := declaration.body | throw (.unsupported "definition has no body")
  let action : CheckM Unit := do
    let scope ← newScope 0
    let _ ← analyze limits.depth { program, scope } body
      (some (declaration.type, .shared)) scope .linear
    pure ()
  match action.run { remaining := limits.steps } with
  | .ok _ _ => pure ()
  | .error error _ => throw error

end Ix.Resource

end

