import IxCC.Ixon.V3.Resource.State

/-! Adapted from an earlier ix (a revision outside this repository's history)
(`Ix/Resource/Check.lean`, identical to the merge base `3d725c8c0`), with the
local expression type and namespaces. This resource check retains the upstream
erased-typing prerequisite. Changes since, kept in step with ix's
`Ix/Resource/Check.lean`:

- safe theorems are a declaration kind of their own: admission checks a marked
  theorem's proof against its statement with contracts but without usage,
  ownership or locality obligations (`conform`, `checkTheorem`), and terms in
  erased positions are checked the same way. Typing (the certified kernel's
  acceptance) does not compare result contracts, so a proof it accepts can
  equate types that differ only in a contract. A proof of an equation between values of a literal type is not
  inspected (`dataEquation`; the adapter supplies the kernel's `Eq`);
- projections of single-constructor structures with parameters and dependent
  fields: `Field.binders`, `fieldType`, and projection reduction in `whnf`;
- a loose-index bound per sharing entry (`sharingBounds`), which lets `shift`
  and `substitute` keep a `.share` node unchanged; `exprEq`, a structural
  equality charging a step per node pair; binding bookkeeping charged by the
  bindings it touches; `checkDefinitionCounted`. Every walk of an expression
  costs a step per node visited and every pass over the bindings a step per
  binding; not charged per element are field and projection rule lookups and
  operations on origin and loan lists, bounded by the scopes created so far.

Unlike ix's copy, `whnf` unfolds every declaration with a body (ix unfolds only
safe definitions, not theorems or unsafe and partial definitions), `fieldType`
requires the owner type to supply exactly the field rule's parameters (ix
accepts fewer), and a closed field's type is used without inferring its owner's
type. -/

namespace IxCC.Ixon.V3.Resource

open IxCC.Ixon.V3

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
  type : Expr
  body : Option Expr := none
  kind : DeclKind := .definition
  deriving BEq, Repr, Inhabited

/-- Checked transparent fields. The adapter derives these from the addressed
constructor interface; an unknown projection has no default resource rule.
`binders` is zero for closed field types and otherwise counts the leading
constructor telescope binders (`params + index`) over which `type` is open. -/
structure Field where
  typeRef : UInt64
  index : UInt64
  type : Expr
  contract : ValueContract
  binders : Nat := 0
  deriving BEq, Repr, Inhabited

/-- Canonical projection reduction for a safe, single-constructor structure.
The addressed adapter supplies the owner and constructor together; a field
number alone never authorizes a projection reduction. -/
structure ProjectionInfo where
  typeRef : UInt64
  constructor : UInt64
  params : Nat
  fields : Nat
  deriving BEq, Repr, Inhabited

structure Program where
  declarations : Array Declaration
  /-- Members and constructors addressed by the same mutual block. -/
  groups : Array (Array Nat) := #[]
  /-- Additional addressed executable syntax, currently recursor rules.
  These participate in dependency/relevance scanning even when the interface
  requires a profile assumption instead of ordinary lambda checking. -/
  auxiliary : Array (Nat × Expr) := #[]
  sharing : Array Expr := #[]
  /-- `computeSharingBounds sharing`: a strict upper bound on the loose de Bruijn
  indices of each entry's expansion, or `none` when unknown. `shift` and
  `substitute` use it only to leave a `.share` node unchanged. Empty disables
  that shortcut. The address adapter fills it; a hand-built program must
  either leave it empty or compute it with `computeSharingBounds`. -/
  sharingBounds : Array (Option Nat) := #[]
  fields : Array Field := #[]
  projections : Array ProjectionInfo := #[]
  natType : Option Expr := none
  stringType : Option Expr := none
  /-- The kernel's equality type `Eq`, when the closure contains it. The
  address adapter resolves it by its pinned primitive address. `conform` does
  not inspect a proof of an equation between values of a literal type
  (`dataEquation`). -/
  equality : Option UInt64 := none
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

def expansion (program : Program) (index : UInt64) : CheckM Expr :=
  match program.sharing[index.toNat]? with
  | some e => pure e
  | none => throw (.unresolvedSharing index.toNat)

def literalType (type : Option Expr) : CheckM Expr :=
  match type with
  | some type => pure type
  | none => throw (.unsupported "literal type is absent from the addressed profile")

def checkedIndex (n : Nat) : CheckM UInt64 :=
  if n < UInt64.size then pure n.toUInt64 else throw (.unsupported "readVariable index overflow")

/-- A strict upper bound on the loose de Bruijn indices of a sharing entry's
expansion, read from the entry's own syntax. A `.share j` inside it contributes
the bound already computed for an earlier entry `j`; a forward or unknown
reference, or `.recur`, gives `none`. Nothing is expanded, so filling the whole
table visits each node of its syntax once. -/
def sharingEntryBound (bounds : Array (Option Nat)) : Expr → Option Nat
  | .var idx => some (idx.toNat + 1)
  | .sort _ | .ref .. | .nat _ | .str _ => some 0
  | .recur .. => none
  | .share idx => bounds[idx.toNat]?.join
  | .prj _ _ v => sharingEntryBound bounds v
  | .app f a => do
    return max (← sharingEntryBound bounds f) (← sharingEntryBound bounds a)
  | .lam _ t b | .all _ _ t b => do
    return max (← sharingEntryBound bounds t) ((← sharingEntryBound bounds b) - 1)
  | .letE _ t v b => do
    return max (max (← sharingEntryBound bounds t) (← sharingEntryBound bounds v))
      ((← sharingEntryBound bounds b) - 1)

/-- `Program.sharingBounds` for a sharing table, in time linear in its syntax. -/
def computeSharingBounds (sharing : Array Expr) : Array (Option Nat) :=
  sharing.foldl (fun bounds e => bounds.push (sharingEntryBound bounds e)) #[]

/-- The bound `computeSharingBounds` recorded for a `.share` entry, if any. -/
def sharingBound? (program : Program) (index : UInt64) : Option Nat :=
  program.sharingBounds[index.toNat]?.join

def shift (program : Program) : Nat → Expr → Nat → Nat → CheckM Expr
  | 0, _, _, _ => throw .budget
  | fuel + 1, e, amount, cutoff => do
    tick
    -- Shifting by zero is the identity. The result may be physically shared,
    -- which costs nothing here: every later walk pays a step per node visited.
    if amount == 0 then return e
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
    | .share idx =>
      -- An entry with no loose index at or above `cutoff` is unchanged: keep
      -- the `.share` node, never its expansion.
      if let some bound := sharingBound? program idx then
        if bound ≤ cutoff then return e
      shift program fuel (← expansion program idx) amount cutoff
    | .recur .. => throw (.unsupported "unresolved recursive reference")
    | _ => return e

def substitute (program : Program) : Nat → Expr → Expr → Nat → CheckM Expr
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
    | .share idx =>
      -- No loose index of the entry reaches `depth`: it is unchanged.
      if let some bound := sharingBound? program idx then
        if bound ≤ depth then return e
      substitute program fuel (← expansion program idx) value depth
    | .recur .. => throw (.unsupported "unresolved recursive reference")
    | _ => return e

def splitApp (program : Program) :
    Nat → Expr → List Expr → CheckM (Expr × List Expr)
  | 0, _, _ => throw .budget
  | fuel + 1, e, args => do
    tick
    match e with
    | .app fn arg => splitApp program fuel fn (arg :: args)
    | .share index => splitApp program fuel (← expansion program index) args
    | _ => return (e, args)

/-- Syntactic equality charging one step per pair of nodes compared. Unlike
the derived `==`, it cannot walk a physically shared value as a tree for free.
`.share` nodes compare by index, as in `==`. -/
def exprEq : Expr → Expr → CheckM Bool
  | .app f a, .app f' a' => do
    tick
    return (← exprEq f f') && (← exprEq a a')
  | .lam c t b, .lam c' t' b' => do
    tick
    return c == c' && (← exprEq t t') && (← exprEq b b')
  | .all c r t b, .all c' r' t' b' => do
    tick
    return c == c' && r == r' && (← exprEq t t') && (← exprEq b b')
  | .letE c t v b, .letE c' t' v' b' => do
    tick
    return c == c' && (← exprEq t t') && (← exprEq v v') && (← exprEq b b')
  | .prj t i v, .prj t' i' v' => do
    tick
    return t == t' && i == i' && (← exprEq v v')
  | left, right => do
    tick
    -- Remaining cases: leaves, and nodes of different shapes (`==` is then
    -- false after inspecting only the constructors).
    match left, right with
    | .app .., _ | .lam .., _ | .all .., _ | .letE .., _ | .prj .., _ => return false
    | _, _ => return left == right

/-- This reduction is only for resource interfaces. The ordinary typechecker
separately validates universes, dependent types, and definitional equality. -/
def whnf (program : Program) : Nat → Expr → CheckM Expr
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
    | .prj typeRef field value =>
      let value ← whnf program fuel value
      let (head, args) ← splitApp program fuel value []
      if let .ref constructor _ := head then
        if let some info := program.projections.find? fun info =>
            info.typeRef == typeRef && info.constructor == constructor then
          if field.toNat < info.fields && args.length == info.params + info.fields then
            return ← whnf program fuel args[info.params + field.toNat]!
      return .prj typeRef field value
    | .recur .. => throw (.unsupported "unresolved recursive reference")
    | _ => return e

def compatible (program : Program) : Nat → Expr → Expr → CheckM Bool
  | 0, _, _ => throw .budget
  | fuel + 1, left, right => do
    tick
    -- Exact syntax is safe even when an opaque type has no reduction rule.
    if ← exprEq left right then return true
    let left ← whnf program fuel left
    let right ← whnf program fuel right
    if ← exprEq left right then return true
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
    | _, _ => exprEq left right

def requireType (program : Program) (fuel : Nat) (actual expected : Expr) : CheckM Unit := do
  if !(← compatible program fuel actual expected) then throw .typeMismatch

def arrow (program : Program) (fuel : Nat) (type : Expr) :
    CheckM (BinderContract × ValueContract × Expr × Expr) := do
  match ← whnf program fuel type with
  | .all input result domain codomain => return (input, result, domain, codomain)
  | _ => throw (.unsupported "a callable interface must expose its arrow contracts")

def isShareable (program : Program) (fuel : Nat) (type : Expr) : CheckM Bool := do
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

def fieldRule (program : Program) (typeRef index : UInt64) : CheckM Field :=
  match program.fields.find? (fun f => f.typeRef == typeRef && f.index == index) with
  | some field => pure field
  | none => throw (.unsupported "projection has no checked field rule")

/-- Instantiate a checked field rule against the projected aggregate and its
reduced nominal type application. Closed field rules need no type inspection;
open rules substitute type parameters and earlier projections from outermost
constructor binder to innermost. -/
def fieldType (program : Program) (fuel : Nat) (field : Field)
    (value valueType : Expr) : CheckM Expr := do
  if field.binders == 0 then return field.type
  let index := field.index.toNat
  if index > field.binders then
    throw (.unsupported "projection field rule has inconsistent binder count")
  let params := field.binders - index
  let valueType ← whnf program fuel valueType
  let (head, args) ← splitApp program fuel valueType []
  match head with
  | .ref ref _ =>
    unless ref == field.typeRef && args.length == params do
      throw .typeMismatch
  | _ => throw .typeMismatch
  let priors := (List.range index).map fun i => Expr.prj field.typeRef i.toUInt64 value
  let values := args ++ priors
  let mut result := field.type
  for offset in [0:values.length] do
    let depth := values.length - 1 - offset
    result ← substitute program fuel result values[offset]! depth
  return result

/-- Resolve a borrow place without charging a consumption. Every projection
must have a checked field rule; all projected loans suspend the whole root. -/
def place (ctx : Context) : Nat → Expr → CheckM Value
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
      let rawValue := value
      let value ← place ctx fuel value
      let field ← fieldRule ctx.program t i
      let type ← fieldType ctx.program fuel field rawValue value.type
      let duplicable ← if field.contract.owned == .shared then pure true
        else isShareable ctx.program fuel type
      return { value with
        type
        duplicable
        owned := if value.owned == .unique && field.contract.owned == .unique then .unique else .shared }
    | _ => throw .invalidPlace

/-- Infer the interface before executing any resource transition. Calls need
the actual result locality to choose their scope: a call returning an
unrestricted value may inspect a short-lived view even when its result will
subsequently be narrowed to an outer local scope. -/
def typeOf : Nat → Context → Expr → CheckM Expr
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
    | .prj typeRef index value =>
      let field ← fieldRule ctx.program typeRef index
      if field.binders == 0 then return field.type
      let valueType ← typeOf fuel ctx value
      fieldType ctx.program fuel field value valueType
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

/-- Whether `type` is `∀ Δ, @Eq C a b` for the kernel's `Eq`
(`Program.equality`) and a literal type `C` (`Program.natType`,
`Program.stringType`). Such a statement relates two values of a type whose
values are data. Contracts do not change how a term computes, so two such
values are equal with contracts exactly when they are equal without, and a
proof the kernel accepts proves it. A transport along it replaces one
such value by the other inside a type; this checker never selects a type by
computing with a value (it has no recursor or literal reduction), so no
contract it reads changes. -/
def dataEquation (program : Program) : Nat → Expr → CheckM Bool
  | 0, _ => throw .budget
  | fuel + 1, type => do
    tick
    let some equality := program.equality | return false
    match ← whnf program fuel type with
    | .all _ _ _ body => dataEquation program fuel body
    | statement =>
      let (head, args) ← splitApp program fuel statement []
      let .ref index _ := head | return false
      let [carrier, _, _] := args | return false
      if index != equality then return false
      let carrier ← whnf program fuel carrier
      let literal (expected : Option Expr) : CheckM Bool := match expected with
        | some literalType => exprEq carrier literalType
        | none => pure false
      return (← literal program.natType) || (← literal program.stringType)

/-- Contract-aware typing of a term the analysis does not run: a theorem's
proof, and a term in an erased (`0`) position. `typeOf` computes a type from
declared interfaces without looking at arguments, and the certified kernel
compares binders' input contracts but not result contracts, so a proof it
accepts can state an
equality between types that differ in a contract (`rfl : ((~ x : A) → ~ B) =
((~ x : A) → B)`). A transport (`cast`, `Eq.mpr`, `▸`, `Eq.rec`) along such a
proof would change a contract. `conform` checks the term the way `analyze`
would, without usage, ownership or locality obligations: every argument,
initializer and λ is compared with the type it is used at by `compatible`,
contracts included.

Two kinds of term are not inspected. A term whose type is a sort is a type; it
is compared wherever it is used as one. A proof of an equation between values
of a literal type (`dataEquation`) proves its statement with or without
contracts; such proofs, like the equation theorems of recursive definitions,
often need recursor reduction, which `compatible` lacks. Returns the term's
type. -/
def conform : Nat → Context → Expr → Option Expr → CheckM Expr
  | 0, _, _, _ => throw .budget
  | fuel + 1, ctx, e, expected => do
    tick
    if let some type := expected then
      match ← whnf ctx.program fuel type with
      | .sort _ => return type
      | reduced => if ← dataEquation ctx.program fuel reduced then return type
    let inferred ← match e with
      | .var index => do
        let n := index.toNat
        if n >= ctx.vars.size then throw (.unbound n)
        let b ← binding ctx.vars[ctx.vars.size - 1 - n]!
        shift ctx.program fuel b.value.type (n + 1) 0
      | .ref index _ => do pure (← declaration ctx.program index).type
      | .share index => do conform fuel ctx (← expansion ctx.program index) none
      | .recur .. => throw (.unsupported "unresolved recursive reference")
      | .sort _ | .all .. => pure (.sort 0)
      | .nat _ => literalType ctx.program.natType
      | .str _ => literalType ctx.program.stringType
      | .prj typeRef index value => do
        let field ← fieldRule ctx.program typeRef index
        let ownerType ← conform fuel ctx value none
        fieldType ctx.program fuel field value ownerType
      | .app fn arg => do
        let (_, _, domain, codomain) ← arrow ctx.program fuel (← conform fuel ctx fn none)
        let _ ← conform fuel ctx arg (some domain)
        substitute ctx.program fuel codomain arg 0
      | .lam input domain body => do
        -- A λ carries no result contract; it takes its expected arrow's.
        let (result, codomain) ← match expected with
          | some type => do
            let (declared, result, declaredDomain, codomain) ← arrow ctx.program fuel type
            if input != declared then throw .binderMismatch
            requireType ctx.program fuel domain declaredDomain
            pure (result, some codomain)
          | none => pure (.shared, none)
        let before ← get
        let id ← pushBinding input { type := domain }
        let bodyType ← conform fuel { ctx with vars := ctx.vars.push id } body codomain
        modify fun s => { s with bindings := before.bindings }
        pure (.all input result domain bodyType)
      | .letE contract type initializer body => do
        let _ ← conform fuel ctx initializer (some type)
        let before ← get
        let id ← pushBinding contract.binder { type }
        let bodyType ← conform fuel { ctx with vars := ctx.vars.push id } body none
        modify fun s => { s with bindings := before.bindings }
        substitute ctx.program fuel bodyType initializer 0
    if let some type := expected then
      requireType ctx.program fuel inferred type
    return inferred

def finishValue (ctx : Context) (fuel : Nat) (destination : ScopeId)
    (expected : Option (Expr × ValueContract)) (value : Value) : CheckM Value := do
  match expected with
  | none => return value
  | some (type, contract) =>
    requireType ctx.program fuel value.type type
    consumeAs contract destination value

/-- Join only bindings that existed before an alternative. Branch-local
bindings cannot escape: returned places have already been consumed, and
retained local origins are checked before their lexical scopes close. -/
def joinBindings (count : Nat) (left right : State) : CheckM (Array Binding) := do
  tickN count
  let mut result := #[]
  for i in [0:count] do
    let some a := left.bindings[i]? | throw (.unbound i)
    let some b := right.bindings[i]? | throw (.unbound i)
    result := result.push { a with
      owner := joinOwner a.owner b.owner
      demand := a.demand.join b.demand
      touched := a.touched || b.touched }
  return result

def analyze : Nat → Context → Expr → Option (Expr × ValueContract) →
    ScopeId → Uses → CheckM Value
  | 0, _, _, _, _, _ => throw .budget
  | fuel + 1, ctx, e, expected, destination, grade => do
    tick
    -- Zero computation has no ownership events, captures, or runtime origins,
    -- but its type is checked with contracts (`conform`): an erased proof can
    -- still state a type equality that a later transport relies on.
    if grade == .erased then
      let type ← conform fuel ctx e (expected.map (·.1))
      return { type, owned := .unique }
    if let some (type, _) := expected then
      if let .sort _ ← whnf ctx.program fuel type then
        return { type, owned := .unique }
    if grade != .linear then
      -- Resetting and then rescaling every binding's demand touches each once.
      tickN (2 * (← get).bindings.size)
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
        -- Resetting and then merging every outer binding touches each once.
        tickN (2 * (← get).bindings.size)
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
        let rawValue := value
        let value ← analyze fuel ctx value none destination grade
        let field ← fieldRule ctx.program typeRef index
        let type ← fieldType ctx.program fuel field rawValue value.type
        let duplicable ← if field.contract.owned == .shared then pure true
          else isShareable ctx.program fuel type
        pure { value with
          type
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

/-- `checkDefinition` with the number of steps it consumed. Running out of
`limits.steps` reports `budget` after consuming all of them; running out of
`limits.depth` reports `budget` too, possibly earlier. -/
def checkDefinitionCounted (program : Program) (index : Nat) (limits : Limits := {}) :
    Except Error Unit × Nat :=
  let action : CheckM Unit := do
    let some declaration := program.declarations[index]? | throw (.badReference index)
    let some body := declaration.body | throw (.unsupported "definition has no body")
    let scope ← newScope 0
    let _ ← analyze limits.depth { program, scope } body
      (some (declaration.type, .shared)) scope .linear
    pure ()
  match action.run { remaining := limits.steps } with
  | .ok _ s => (.ok (), limits.steps - s.remaining)
  | .error error s => (.error error, limits.steps - s.remaining)

def checkDefinition (program : Program) (index : Nat) (limits : Limits := {}) : Except Error Unit :=
  (checkDefinitionCounted program index limits).1

/-- Check a theorem's proof against its statement with `conform`. A proof is
never run, so it has no usage, ownership or locality obligations; but the
statement is trusted wherever the theorem is used, and a transport along it
would carry any contract difference the proof glossed over. The proof of an
equation between values of a literal type (`dataEquation`), such as the
equation theorem of a recursive definition returning a `Nat`, is not
inspected. -/
def checkTheorem (program : Program) (index : Nat) (limits : Limits := {}) : Except Error Unit :=
  let action : CheckM Unit := do
    let some declaration := program.declarations[index]? | throw (.badReference index)
    let some body := declaration.body | throw (.unsupported "theorem has no proof")
    let scope ← newScope 0
    let _ ← conform limits.depth { program, scope } body (some declaration.type)
    pure ()
  match action.run { remaining := limits.steps } with
  | .ok _ _ => .ok ()
  | .error error _ => .error error

end IxCC.Ixon.V3.Resource
