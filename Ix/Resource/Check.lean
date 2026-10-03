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
  /-- A safe theorem. Its proof is erased computation that no backend runs,
  so admission checks no resource obligation in it. Its statement still takes
  part in relevance, and callers still use it as an interface. -/
  | theorem
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
  /-- `0` when `type` is closed. Otherwise `type` is open over the
  constructor telescope: the structure's parameters, then the fields before
  this one (innermost last), `binders` variables in all. -/
  binders : Nat := 0
  deriving BEq, Repr, Inhabited

/-- The shape of an addressed recursor of a single, non-mutual inductive type,
as the case-split rule needs it. -/
structure RecursorInfo where
  index : UInt64
  params : Nat
  motives : Nat
  minors : Nat
  indices : Nat
  /-- Constructor fields of each minor premise, in minor order. -/
  fields : Array Nat
  /-- Leading binders of each minor's declared domain: its fields, then its
  induction hypotheses. -/
  binders : Array Nat
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
  /-- Profile-bound non-strict selection primitives. A choice is applied to
  exactly as many arguments as its type has leading arrows (more are passed
  on to both alternatives). Its last two arguments are the alternatives,
  evaluated by need; the others are strict. An alternative expecting a proof
  (`dite`) is entered with a fresh proof binder. -/
  choices : Array UInt64 := #[]
  /-- The sort index that denotes `Prop`. The address adapter rewrites every
  sort to `0` (some type universe) or this index (literally `Sort 0`). An
  argument whose domain is a proposition is erased computation. Without this
  index no type is recognized as a proposition. -/
  propSort : Option UInt64 := none
  /-- Recursors the case-split rule can read. -/
  recursors : Array RecursorInfo := #[]
  /-- Profile behavior: a recursor application whose minor premises ignore
  their induction hypotheses is a case split, a bound case definition
  (`caseDefinitions`) is unfolded, and a β-redex binds its arguments strictly.
  The consumer must compile these without closures. -/
  cases : Bool := false
  /-- Profile-bound case definitions (`casesOn`, matchers): unannotated
  definitions that only wrap a case split. Only these are unfolded, and only
  the alternatives they take are bound by need; every other definition is an
  ordinary call, however match-shaped its body. -/
  caseDefinitions : Array UInt64 := #[]
  /-- Admitted resource interfaces: callers see this type in place of the
  declaration's own. The profile must also list the declaration as an
  assumption. -/
  interfaces : Array (UInt64 × Ixon.Expr) := #[]
  /-- The `Eq` type, when the profile names unfolding equations. -/
  eqType : Option UInt64 := none
  /-- Profile-bound unfolding equations `(definition, equation)`: a definition
  with one is checked through the right-hand side of the theorem's statement
  `∀ xs, f xs = rhs` instead of its own body (for example a `brecOn` or
  `WellFounded.fix` encoding). The consumer must run the definition by that
  equation. -/
  equations : Array (UInt64 × UInt64) := #[]
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

/-- The interface callers see: an admitted interface, or the declared type. -/
def interfaceType (program : Program) (index : UInt64) : CheckM Ixon.Expr := do
  match program.interfaces.find? (·.1 == index) with
  | some (_, type) => pure type
  | none => return (← declaration program index).type

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

def splitApp (program : Program) :
    Nat → Ixon.Expr → List Ixon.Expr → CheckM (Ixon.Expr × List Ixon.Expr)
  | 0, _, _ => throw .budget
  | fuel + 1, e, args => do
    tick
    match e with
    | .app fn arg => splitApp program fuel fn (arg :: args)
    | .share index => splitApp program fuel (← expansion program index) args
    | _ => return (e, args)

def fieldRule (program : Program) (typeRef index : UInt64) : CheckM Field :=
  match program.fields.find? (fun f => f.typeRef == typeRef && f.index == index) with
  | some field => pure field
  | none => throw (.unsupported "projection has no checked field rule")

/-- The type of `field` projected from `value`, whose type is `valueType`.
An open field rule is instantiated with the structure's type arguments, taken
from `valueType`, and with the earlier fields as projections of `value`. -/
def fieldType (program : Program) (fuel : Nat) (field : Field) (valueType value : Ixon.Expr) :
    CheckM Ixon.Expr := do
  if field.binders == 0 then return field.type
  let index := field.index.toNat
  let params := field.binders - index
  let (head, args) ← splitApp program fuel (← whnf program fuel valueType) []
  let structural := match head with
    | .ref i _ => i == field.typeRef && args.length == params
    | _ => false
  unless structural && params + index == field.binders do
    throw (.unsupported "projected value does not have the field's structure type")
  let values := args ++ (List.range index).map fun j => Ixon.Expr.prj field.typeRef j.toUInt64 value
  let mut type := field.type
  let mut depth := values.length
  for x in values do
    depth := depth - 1
    type ← substitute program fuel type x depth
  return type

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
    | .prj t i projected =>
      let value ← place ctx fuel projected
      let field ← fieldRule ctx.program t i
      let type ← fieldType ctx.program fuel field value.type projected
      let duplicable ← if field.contract.owned == .shared then pure true
        else isShareable ctx.program fuel type
      return { value with
        type
        duplicable
        freezable := false
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
    | .ref index _ => interfaceType ctx.program index
    | .share index => typeOf fuel ctx (← expansion ctx.program index)
    | .recur .. => throw (.unsupported "unresolved recursive reference")
    | .sort _ | .all .. => return .sort 0
    | .nat _ => literalType ctx.program.natType
    | .str _ => literalType ctx.program.stringType
    | .prj typeRef index value =>
      let field ← fieldRule ctx.program typeRef index
      if field.binders == 0 then return field.type
      fieldType ctx.program fuel field (← typeOf fuel ctx value) value
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

/-- Whether the bounded inference types `type` as the sort `prop`. An
expression it cannot type is not. -/
def hasSort (fuel : Nat) (ctx : Context) (type : Ixon.Expr) (prop : UInt64) : CheckM Bool := do
  let before ← get
  let sort ← tryCatch (some <$> (do whnf ctx.program fuel (← typeOf fuel ctx type)))
    fun error => match error with
      | .budget => throw .budget
      | _ => pure none
  modify fun s => { s with bindings := before.bindings }
  return match sort with
    | some (.sort s) => s == prop
    | _ => false

/-- Whether `type` is a proposition, so that its values are erased proofs.
A `∀` is a proposition when its body is (impredicativity); otherwise the
type's own type must reduce to the program's `Prop` sort. The unreduced type
is tried first: reduction can unfold a proposition such as `a ≤ b` to a class
projection that has no field rule. Anything this bounded inference cannot
type is conservatively not a proposition. -/
def isProposition : Nat → Context → Ixon.Expr → CheckM Bool
  | 0, _, _ => throw .budget
  | fuel + 1, ctx, type => do
    let some prop := ctx.program.propSort | return false
    tick
    match ← whnf ctx.program fuel type with
    | .all input _ domain body =>
      let before ← get
      let id ← pushBinding input { type := domain }
      let result ← isProposition fuel { ctx with vars := ctx.vars.push id } body
      modify fun s => { s with bindings := before.bindings }
      return result
    | .sort _ | .lam .. => return false
    | reduced =>
      if ← hasSort fuel ctx type prop then return true
      hasSort fuel ctx reduced prop

/-- Argument demand at a call. A callee's multiplicity does not scale the
demand on a value of a profile-shareable (immediate) type: the callee
receives a copy that holds no resource, so passing it is one consumption.
The caller's own reads still count, and a zero-use input still has zero
demand. -/
def argumentGrade (program : Program) (fuel : Nat) (grade input : Uses)
    (domain : Ixon.Expr) : CheckM Uses := do
  if input != .erased && (← isShareable program fuel domain) then return grade
  return grade.mul input

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

/-- Expand sharing at the head of an expression. -/
def unshare (program : Program) : Nat → Ixon.Expr → CheckM Ixon.Expr
  | 0, _ => throw .budget
  | fuel + 1, e => do
    tick
    match e with
    | .share index => unshare program fuel (← expansion program index)
    | _ => return e

/-- Whether an expression carries no resource contract (every binder, arrow
and let has the default contract). -/
def plain (program : Program) : Nat → Ixon.Expr → CheckM Bool
  | 0, _ => throw .budget
  | fuel + 1, e => do
    tick
    match e with
    | .share index => plain program fuel (← expansion program index)
    | .app f a => return (← plain program fuel f) && (← plain program fuel a)
    | .lam c t b => return c == .many && (← plain program fuel t) && (← plain program fuel b)
    | .all c r t b =>
      return c == .many && r == .shared && (← plain program fuel t) && (← plain program fuel b)
    | .letE c t v b =>
      return c.binder == .many && c.kind == .value && (← plain program fuel t) &&
        (← plain program fuel v) && (← plain program fuel b)
    | .prj _ _ v => plain program fuel v
    | _ => return true

/-- The head constant of a type's final codomain. -/
def resultHead (program : Program) : Nat → Ixon.Expr → CheckM (Option UInt64)
  | 0, _ => throw .budget
  | fuel + 1, type => do
    match ← whnf program fuel type with
    | .all _ _ _ body => resultHead program fuel body
    | other =>
      let (head, _) ← splitApp program fuel other []
      match head with
      | .ref i _ => pure (some i)
      | _ => pure none

/-- Whether a type is plain data: an inductive type of an addressed block whose
constructors all carry only default contracts, so that a value of it holds
nothing finite-use or unique. Functions, type parameters and types without a
known block are not. -/
def plainData (program : Program) (fuel : Nat) (type : Ixon.Expr) : CheckM Bool := do
  let (head, _) ← splitApp program fuel (← whnf program fuel type) []
  let .ref t _ := head | return false
  let some d := program.declarations[t.toNat]? | return false
  unless d.kind == .typeConstructor do return false
  let some group := program.groups.find? (·.contains t.toNat) | return false
  for c in group do
    let some cd := program.declarations[c]? | return false
    if cd.kind == .constructor then
      if (← resultHead program fuel cd.type) == some t then
        unless ← plain program fuel cd.type do return false
  return true

/-- Whether variable `index` occurs in `e`. -/
def occurs (program : Program) : Nat → Ixon.Expr → Nat → CheckM Bool
  | 0, _, _ => throw .budget
  | fuel + 1, e, index => do
    tick
    match e with
    | .var i => return i.toNat == index
    | .share i => occurs program fuel (← expansion program i) index
    | .app f a => return (← occurs program fuel f index) || (← occurs program fuel a index)
    | .lam _ t b | .all _ _ t b =>
      return (← occurs program fuel t index) || (← occurs program fuel b (index + 1))
    | .letE _ t v b =>
      return (← occurs program fuel t index) || (← occurs program fuel v index) ||
        (← occurs program fuel b (index + 1))
    | .prj _ _ v => occurs program fuel v index
    | _ => return false

/-- Number of leading arrows of a type. -/
def arity (program : Program) : Nat → Ixon.Expr → CheckM Nat
  | 0, _ => throw .budget
  | fuel + 1, type => do
    match ← whnf program fuel type with
    | .all _ _ _ body => return (← arity program fuel body) + 1
    | _ => return 0

def recursorInfo (program : Program) (index : UInt64) : Option RecursorInfo :=
  program.recursors.find? (·.index == index)

def RecursorInfo.arity (info : RecursorInfo) : Nat :=
  info.params + info.motives + info.minors + info.indices + 1

/-- Whether a minor premise ignores its induction hypotheses: it binds all
of the minor's binders and its body mentions none of the hypotheses. -/
def ignoresHypotheses (program : Program) (fuel : Nat) (minor : Ixon.Expr)
    (fields binders : Nat) : CheckM Bool := do
  if binders == fields then return true
  let mut body := minor
  for _ in [0:binders] do
    match ← unshare program fuel body with
    | .lam _ _ b => body := b
    | _ => return false
  for k in [0:binders - fields] do
    if ← occurs program fuel body k then return false
  return true

/-- How an occurrence of a parameter sits in an alternative argument. -/
inductive Occurrence where
  /-- The parameter does not occur. -/
  | absent
  /-- The parameter is the head of an application to this many arguments,
  none of which mention it, and nothing else in the alternative does. -/
  | applied (arguments : Nat)
  /-- Any other occurrence (under a closure, as an argument, more than once). -/
  | other
  deriving BEq, Repr, Inhabited

/-- How variable `index` occurs in the alternative argument `e` of a case,
after entering at most `strip` of its leading lambdas (the binders the case
itself supplies: constructor fields, hypotheses, further arguments). -/
def alternativeOccurrence (program : Program) (fuel : Nat) (e : Ixon.Expr) (index strip : Nat) :
    CheckM Occurrence := do
  let mut body := e
  let mut index := index
  for _ in [0:strip] do
    match ← unshare program fuel body with
    | .lam _ t b =>
      if ← occurs program fuel t index then return .other
      body := b
      index := index + 1
    | _ => break
  if !(← occurs program fuel body index) then return .absent
  let (head, args) ← splitApp program fuel body []
  match ← unshare program fuel head with
  | .var i =>
    if i.toNat != index then return .other
    for arg in args do
      if ← occurs program fuel arg index then return .other
    return .applied args.length
  | _ => return .other

/-- The shape of a bound case definition: its parameter count, and for each
parameter `some k` when it is taken by need (it occurs only as the head of
alternatives, applied to at least `k` arguments) or `none` when it is strict. -/
structure CaseShape where
  arity : Nat
  byNeed : Array (Option Nat)
  deriving BEq, Repr, Inhabited

/-- The shape of a profile-bound case definition (`casesOn`, a matcher): an
unannotated definition whose body is a lambda telescope around a full
application of a case recursor whose minors ignore their induction
hypotheses, or of another bound case definition. A parameter is by need when
every occurrence of it lies in an alternative of that application (a minor
premise, or a by-need position of the inner definition), after at most the
binders the case enters there, as the head of an application whose arguments
do not mention it; occurrences in different alternatives are allowed (at most
one alternative runs). A parameter occurring anywhere else (a discriminant,
under a closure, twice in one alternative), or nowhere, is strict. A
definition that is not bound, or not of this shape, or wraps a choice, is an
ordinary function. -/
def caseDefinition (program : Program) (fuel : Nat) : Nat → UInt64 → CheckM (Option CaseShape)
  | 0, _ => pure none
  | depth + 1, index => do
    if !program.cases || !program.caseDefinitions.contains index || program.choices.contains index then
      return none
    let some d := program.declarations[index.toNat]? | return none
    let some body := d.body | return none
    unless d.kind == .definition && (← plain program fuel d.type) && (← plain program fuel body) do
      return none
    let mut inner := body
    let mut params := 0
    repeat
      match ← unshare program fuel inner with
      | .lam _ _ b => inner := b; params := params + 1
      | other => inner := other; break
    let (head, args) ← splitApp program fuel inner []
    let .ref target _ := head | return none
    -- The alternative positions of the application, with the binders entered there.
    let mut alternatives : Array (Option Nat) := Array.replicate args.length none
    if let some info := recursorInfo program target then
      if args.length < info.arity then return none
      for j in [0:info.minors] do
        let minor := args[info.params + info.motives + j]!
        unless ← ignoresHypotheses program fuel minor info.fields[j]! info.binders[j]! do
          return none
        alternatives := alternatives.set! (info.params + info.motives + j)
          (some (info.binders[j]! + (args.length - info.arity)))
    else
      let some shape ← caseDefinition program fuel depth target | return none
      if args.length < shape.arity then return none
      for i in [0:shape.arity] do
        alternatives := alternatives.set! i
          (shape.byNeed[i]!.map (· + (args.length - shape.arity)))
    let mut byNeed := #[]
    for p in [0:params] do
      let index := params - 1 - p
      let mut applied : Option Nat := none
      let mut lazy := true
      for j in [0:args.length] do
        match alternatives[j]! with
        | none => if ← occurs program fuel args[j]! index then lazy := false
        | some strip =>
          match ← alternativeOccurrence program fuel args[j]! index strip with
          | .absent => pure ()
          | .applied k => applied := some (min k (applied.getD k))
          | .other => lazy := false
      byNeed := byNeed.push (if lazy then applied else none)
    return some { arity := params, byNeed }

/-- Whether a type is a sort or an arrow into a sort. -/
def typeFormer (program : Program) (fuel : Nat) : Nat → Ixon.Expr → CheckM Bool
  | 0, _ => pure false
  | n + 1, t => do
    match ← whnf program fuel t with
    | .sort _ => pure true
    | .all _ _ _ b => typeFormer program fuel n b
    | _ => pure false

/-- Whether `e` has no loose variable at or above `depth`. -/
def closedAt (program : Program) : Nat → Nat → Ixon.Expr → CheckM Bool
  | 0, _, _ => throw .budget
  | fuel + 1, depth, e => do
    tick
    match e with
    | .var i => return i.toNat < depth
    | .share i => closedAt program fuel depth (← expansion program i)
    | .recur .. => return false
    | .app f a => return (← closedAt program fuel depth f) && (← closedAt program fuel depth a)
    | .lam _ t b | .all _ _ t b =>
      return (← closedAt program fuel depth t) && (← closedAt program fuel (depth + 1) b)
    | .letE _ t v b =>
      return (← closedAt program fuel depth t) && (← closedAt program fuel depth v) &&
        (← closedAt program fuel (depth + 1) b)
    | .prj _ _ v => closedAt program fuel depth v
    | _ => return true

/-- Whether a strict argument may be substituted into a lambda telescope
because evaluating it has no effect: a variable (a place; its reads are
charged where it is used), a sort or `∀`, a constant that is not a nullary
constructor (no allocation), a closed lambda (it captures and moves nothing),
or a type or proof (erased computation). Literals, constructor applications,
nullary constructors (fresh values) and every other computation are not. -/
def substitutable (ctx : Context) (fuel : Nat) (arg domain : Ixon.Expr) : CheckM Bool := do
  match ← unshare ctx.program fuel arg with
  | .var _ | .sort _ | .all .. => return true
  | .ref index _ =>
    let d ← declaration ctx.program index
    if d.kind == .constructor then return (← arity ctx.program fuel d.type) != 0
    return true
  | lam@(.lam ..) =>
    if ← closedAt ctx.program fuel 0 lam then return true
    if ← typeFormer ctx.program fuel 16 domain then return true
    isProposition fuel ctx domain
  | _ =>
    if ← typeFormer ctx.program fuel 16 domain then return true
    isProposition fuel ctx domain

/-- Apply a lambda telescope to arguments, as `let`s. Arguments are strict:
an argument of a binder with the default contract is substituted only when
evaluating it has no effect (`substitutable`); any other argument is bound by
a `let` carrying the binder's own contract, so it is analysed exactly once,
before the body, whether or not the binder occurs, as a call evaluates it.
The only exception are the by-need positions of a bound case definition
(`byNeed`, from `caseDefinition`): their arguments are substituted, so each
is evaluated in the alternative that uses it. Arguments beyond the telescope
are applied to the body. -/
def bindArguments (ctx : Context) (fuel : Nat) (telescope : Ixon.Expr) (args : List Ixon.Expr)
    (byNeed : Array (Option Nat) := #[]) : CheckM Ixon.Expr := do
  let before ← get
  let mut term := telescope
  let mut lets : Array (Ixon.LetContract × Ixon.Expr × Ixon.Expr) := #[]
  let mut inner := ctx
  let mut rest := args
  let mut position := 0
  repeat
    match rest with
    | [] => break
    | arg :: more =>
      match ← unshare ctx.program fuel term with
      | .lam c domain body =>
        let arg ← shift ctx.program fuel arg lets.size 0
        let lazy := (byNeed[position]?.bind id).isSome
        if c == .many && (lazy || (← substitutable inner fuel arg domain)) then
          term ← substitute ctx.program fuel body arg 0
        else
          lets := lets.push ({ nonDep := false, binder := c }, domain, arg)
          let id ← pushBinding c { type := domain }
          inner := { inner with vars := inner.vars.push id }
          term := body
        rest := more
        position := position + 1
      | _ => break
  for arg in rest do
    term := .app term (← shift ctx.program fuel arg lets.size 0)
  modify fun s => { s with bindings := before.bindings }
  let mut result := term
  for (c, domain, value) in lets.reverse do
    result := .letE c domain value result
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
        let type ← interfaceType ctx.program idx
        -- A nullary constructor is a fresh value: unique.
        if d.kind == .constructor && (← arity ctx.program fuel d.type) == 0 then
          let duplicable ← isShareable ctx.program fuel type
          let freezable ← if duplicable then pure false else plainData ctx.program fuel type
          pure { type, owned := .unique, duplicable, freezable }
        else pure { type }
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
        let freezable ← if input.value.owned == .unique && !duplicable then
            plainData ctx.program fuel domain
          else pure false
        let parameter ← pushBinding input {
          type := domain
          owned := input.value.owned
          origins
          duplicable
          freezable }
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
            -- A captured immediate (a value of a profile-shareable type) is
            -- copied into the closure, as at a call boundary: neither its
            -- finite use nor its uniqueness makes the closure one-shot.
            let immediate ← isShareable ctx.program fuel old.value.type
            if (old.contract.uses != .many && !immediate) || !old.value.duplicable then
              duplicable := false
            if old.owner.unique then
              -- Capturing an owner transfers its availability even when the
              -- body only borrows it. An explicit outer view permits reusable
              -- local closures without transferring that owner.
              let _ ← liftExcept (moveOwner id old.owner)
              owner := { owner with live := false }
              if demand == .erased then demand := .linear
              if !immediate then duplicable := false
          bindings := bindings.set! id { old with
            owner
            demand := old.demand.add (grade.mul demand)
            touched := old.touched || used.touched }
        modify fun s => { s with bindings }
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
            if !(← isShareable ctx.program fuel type) && !v.duplicable && !v.freezable then
              throw .nonduplicable
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
      | .prj typeRef index projected => do
        let value ← analyze fuel ctx projected none destination grade
        let field ← fieldRule ctx.program typeRef index
        let type ← fieldType ctx.program fuel field value.type projected
        let duplicable ← if field.contract.owned == .shared then pure true
          else isShareable ctx.program fuel type
        pure { value with
          type
          duplicable
          freezable := false
          owned := if value.owned == .unique && field.contract.owned == .unique then .unique else .shared }
      | .app fn arg => do
        let (head, arguments) ← splitApp ctx.program fuel e []
        let args := arguments.toArray
        -- A fully applied constructor allocates a fresh value: unique,
        -- whatever its declared result contract.
        let fresh ← match head with
          | .ref index _ => do
            let d ← declaration ctx.program index
            if d.kind == .constructor then pure (args.size == (← arity ctx.program fuel d.type))
            else pure false
          | _ => pure false
        let ordinary : CheckM Value := do
          let fnType ← typeOf fuel ctx fn
          let (input, result, domain, codomain) ← arrow ctx.program fuel fnType
          -- Applying a proof (a function whose type is a proposition) yields
          -- a proof: erased computation, as a proof argument is.
          if ← isProposition fuel ctx fnType then
            return { type := ← substitute ctx.program fuel codomain arg 0, owned := .unique }
          let callScope := if result.locality == .local then destination else ctx.scope
          let fnValue ← analyze fuel ctx fn none callScope grade
          requireType ctx.program fuel fnValue.type fnType
          invoke fnValue
          -- A proof argument is erased computation: no demand, transfer, or origin.
          let argValue ← if ← isProposition fuel ctx domain then
              pure { type := domain, owned := .unique }
            else
              analyze fuel ctx arg (some (domain, input.value)) callScope
                (← argumentGrade ctx.program fuel grade input.uses domain)
          let type ← substitute ctx.program fuel codomain arg 0
          let origins := if result.locality == .local then
            unionOrigins (unionOrigins fnValue.origins argValue.origins) [callScope] else []
          let owned := if fresh then .unique else result.owned
          let duplicable ← if owned == .shared then pure true
            else isShareable ctx.program fuel type
          let freezable ← if owned == .unique && !duplicable then plainData ctx.program fuel type
            else pure false
          pure {
            type
            owned
            origins
            duplicable
            freezable }
        -- Analyze alternatives from the same state and join them. Each
        -- alternative first binds the values the primitive supplies to it
        -- (one per flag in its array; `true` marks an induction hypothesis,
        -- which must stay unused), then is analyzed with the given contract.
        let alternatives (branches : Array (Ixon.Expr × Ixon.Expr × Array Bool))
            (supplied : Nat → Nat → Ixon.Expr → BinderContract → CheckM Value)
            (extra : Array Ixon.Expr) (contract : Option ValueContract)
            (outputType : Ixon.Expr) : CheckM Value := do
          let before ← get
          let count := before.bindings.size
          let mut joined : Option (Array Binding) := none
          let mut result : Option Value := none
          for j in [0:branches.size] do
            let (alternative, alternativeType, hypotheses) := branches[j]!
            modify fun s => { s with bindings := before.bindings }
            let mut body := alternative
            let mut type := alternativeType
            let mut inner := ctx
            let mut entered : Array (OwnerId × Bool) := #[]
            for k in [0:hypotheses.size] do
              let (field, _, domain, codomain) ← arrow ctx.program fuel type
              let (c, rest) ← match ← unshare ctx.program fuel body with
                | .lam c _ b => pure (c, b)
                | other => pure (BinderContract.many, Ixon.Expr.app (← shift ctx.program fuel other 1 0) (.var 0))
              let value ← supplied j k domain field
              let id ← pushBinding c value
              entered := entered.push (id, hypotheses[k]!)
              inner := { inner with vars := inner.vars.push id }
              body := rest
              type := codomain
            for x in extra do
              let x ← shift ctx.program fuel x entered.size 0
              let (_, _, _, codomain) ← arrow ctx.program fuel type
              type ← substitute ctx.program fuel codomain x 0
              body := .app body x
            let output ← analyze fuel inner body (contract.map (type, ·)) destination grade
            for (id, hypothesis) in entered do
              if hypothesis then
                if (← binding id).touched then
                  throw (.unsupported "a case split uses an induction hypothesis")
              else validateUsage id
            let output := match output.place with
              | some p => if p < count then output else { output with place := none }
              | none => output
            let after ← get
            let bindings := after.bindings.extract 0 count
            joined ← match joined with
              | none => pure (some bindings)
              | some acc => some <$> joinBindings count { after with bindings := acc } { after with bindings }
            result := some (match result with | none => output | some v => joinValue v output)
          modify fun s => { s with bindings := joined.getD before.bindings }
          return { (result.getD { type := outputType, owned := .unique }) with type := outputType }
        match head with
        | .ref index _ =>
          if ctx.program.choices.contains index then
            -- A choice: strict leading arguments, then two alternatives
            -- evaluated by need. Proof binders of an alternative (`dite`)
            -- are supplied by the primitive.
            let declared := (← declaration ctx.program index).type
            let n ← arity ctx.program fuel declared
            if args.size < n then
              throw (.unsupported "selection primitives require a complete application")
            if n < 2 then throw (.unsupported "a selection primitive needs two alternatives")
            let mut tail := declared
            for i in [0:n - 2] do
              let (c, _, domain, codomain) ← arrow ctx.program fuel tail
              unless ← isProposition fuel ctx domain do
                let _ ← analyze fuel ctx args[i]! (some (domain, c.value)) ctx.scope
                  (← argumentGrade ctx.program fuel grade c.uses domain)
              tail ← substitute ctx.program fuel codomain args[i]! 0
            let left := args[n - 2]!
            let right := args[n - 1]!
            let (_, _, leftType, afterLeft) ← arrow ctx.program fuel tail
            let afterLeft ← substitute ctx.program fuel afterLeft left 0
            let (_, result, rightType, afterRight) ← arrow ctx.program fuel afterLeft
            let mut outputType ← substitute ctx.program fuel afterRight right 0
            let extra := args.extract n args.size
            for x in extra do
              let (_, _, _, codomain) ← arrow ctx.program fuel outputType
              outputType ← substitute ctx.program fuel codomain x 0
            -- The proof binders an alternative expects (`dite`).
            let proofs (type : Ixon.Expr) : CheckM (Array Bool) := do
              let mut type := type
              let mut found := #[]
              let mut inner := ctx
              repeat
                match ← whnf ctx.program fuel type with
                | .all c _ domain body =>
                  if ← isProposition fuel inner domain then
                    found := found.push false
                    let id ← pushBinding c { type := domain }
                    inner := { inner with vars := inner.vars.push id }
                    type := body
                  else break
                | _ => break
              return found
            let before ← get
            let leftProofs ← proofs leftType
            let rightProofs ← proofs rightType
            modify fun s => { s with bindings := before.bindings }
            if leftProofs.isEmpty && rightProofs.isEmpty && extra.isEmpty then
              requireType ctx.program fuel leftType rightType
              requireType ctx.program fuel leftType outputType
            -- The chosen alternative is the result: the caller's contract
            -- applies to it, or else the primitive's own result contract.
            let contract := match expected with
              | some (_, c) => c
              | none => result
            alternatives #[(left, leftType, leftProofs), (right, rightType, rightProofs)]
              (fun _ _ domain _ => pure { type := domain }) extra (some contract) outputType
          else
            match (if ctx.program.cases then recursorInfo ctx.program index else none) with
            | some info =>
              if args.size < info.arity then ordinary else do
                -- A case split. Parameters, motives and indices have no run-time
                -- demand; the major premise is inspected, not consumed; each
                -- minor binds the constructor's fields, which keep the major's
                -- origins and are unique only when both the major and the field
                -- binder are.
                let mut tail := (← declaration ctx.program index).type
                let mut minorTypes := #[]
                for i in [0:info.arity] do
                  let (_, _, domain, codomain) ← arrow ctx.program fuel tail
                  if info.params + info.motives ≤ i && i < info.params + info.motives + info.minors then
                    minorTypes := minorTypes.push domain
                  tail ← substitute ctx.program fuel codomain args[i]! 0
                let mut outputType := tail
                let extra := args.extract info.arity args.size
                for x in extra do
                  let (_, _, _, codomain) ← arrow ctx.program fuel outputType
                  outputType ← substitute ctx.program fuel codomain x 0
                let major ← analyze fuel ctx args[info.arity - 1]! none ctx.scope grade
                let branches := (List.range info.minors).toArray.map fun j =>
                  (args[info.params + info.motives + j]!, minorTypes[j]!,
                    (List.range info.binders[j]!).toArray.map (fun k => decide (k ≥ info.fields[j]!)))
                let supplied (j k : Nat) (domain : Ixon.Expr) (c : BinderContract) : CheckM Value :=
                  if k < info.fields[j]! then
                    pure { type := domain
                           owned := if major.owned == .unique && c.value.owned == .unique then .unique else .shared
                           origins := major.origins
                           loanRoot := major.loanRoot }
                  else pure { type := domain }
                alternatives branches supplied extra (expected.map (·.2)) outputType
            | none =>
              match ← caseDefinition ctx.program fuel 4 index with
              | some shape =>
                if args.size < shape.arity then ordinary else do
                  -- A bound case definition is unfolded: its alternatives by
                  -- need, every other argument strictly.
                  match (← declaration ctx.program index).body with
                  | some body =>
                    analyze fuel ctx (← bindArguments ctx fuel body arguments shape.byNeed)
                      expected destination grade
                  | none => ordinary
              | none => ordinary
        | .lam .. =>
          if ctx.program.cases then
            -- A β-redex binds its arguments strictly.
            analyze fuel ctx (← bindArguments ctx fuel head arguments) expected destination grade
          else ordinary
        | _ => ordinary
    finishValue ctx fuel destination expected value

/-- The body an annotated recursive definition is checked through: the
right-hand side of its unfolding equation `∀ xs, f xs = rhs`, abstracted over
the equation's binders with the definition's own input contracts. The
statement must be an equality whose left side is the definition applied to
exactly those binders, in order. -/
def equationBody (program : Program) (fuel : Nat) (index equation : UInt64) : CheckM Ixon.Expr := do
  let some eq := program.eqType
    | throw (.unsupported "the equality type is absent from the profile")
  let d ← declaration program index
  let t ← declaration program equation
  unless t.kind == .theorem do throw (.unsupported "an unfolding equation must be a theorem")
  let mut statement := t.type
  let mut type := d.type
  let mut binders : Array (BinderContract × Ixon.Expr) := #[]
  repeat
    match ← whnf program fuel statement with
    | .all _ _ domain body =>
      let (input, _, _, codomain) ← arrow program fuel type
      binders := binders.push (input, domain)
      statement := body
      type := codomain
    | other => statement := other; break
  let (head, args) ← splitApp program fuel statement []
  let (lhs, rhs) ← match head, args with
    | .ref e _, [_, lhs, rhs] =>
      if e == eq then pure (lhs, rhs)
      else throw (.unsupported "an unfolding equation must state an equality")
    | _, _ => throw (.unsupported "an unfolding equation must state an equality")
  let (fn, fargs) ← splitApp program fuel lhs []
  let unfolds ← match fn with
    | .ref f _ =>
      if f == index && fargs.length == binders.size then do
        let mut ok := true
        let mut k := binders.size
        for arg in fargs do
          k := k - 1
          match ← unshare program fuel arg with
          | .var i => ok := ok && i.toNat == k
          | _ => ok := false
        pure ok
      else pure false
    | _ => pure false
  unless unfolds do throw (.unsupported "an unfolding equation must unfold its definition")
  let mut body := rhs
  for (input, domain) in binders.reverse do
    body := .lam input domain body
  return body

def checkDefinition (program : Program) (index : Nat) (limits : Limits := {}) : Except Error Unit := do
  let some declaration := program.declarations[index]? | throw (.badReference index)
  let action : CheckM Unit := do
    let body ← match program.equations.find? (·.1 == index.toUInt64) with
      | some (_, equation) => equationBody program limits.depth index.toUInt64 equation
      | none => match declaration.body with
        | some body => pure body
        | none => throw (.unsupported "definition has no body")
    let scope ← newScope 0
    let _ ← analyze limits.depth { program, scope } body
      (some (declaration.type, .shared)) scope .linear
    pure ()
  match action.run { remaining := limits.steps } with
  | .ok _ _ => pure ()
  | .error error _ => throw error

end Ix.Resource

end

