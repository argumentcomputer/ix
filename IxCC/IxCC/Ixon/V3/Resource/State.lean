import IxCC.Ixon.V3.Expr

/-! Adapted from ix `0a31c8dbc63755924c645bf1afedc563e395e88a`.
Only the import, expression namespace, and surrounding namespace are changed.
This resource check retains the upstream erased-typing prerequisite. -/

namespace IxCC.Ixon.V3.Resource

open IxCC.Ixon.V3

abbrev ScopeId := Nat
abbrev OwnerId := Nat

inductive Error where
  | budget
  | unbound (index : Nat)
  | badReference (index : Nat)
  | unresolvedSharing (index : Nat)
  | unsupported (operation : String)
  | typeMismatch
  | binderMismatch
  | usage (owner : OwnerId) (declared actual : Uses)
  | moved (owner : OwnerId)
  | sharedToUnique
  | activeLoan (owner : OwnerId)
  | escape (origin destination : ScopeId)
  | unrestrictedEscape (origin : ScopeId)
  | nonduplicable
  | invalidBorrow
  | invalidPlace
  | invalidScope
  deriving BEq, Repr, Inhabited

structure Limits where
  depth : Nat := 256
  steps : Nat := 100000
  deriving BEq, Repr, Inhabited

/-- A value retains every origin in this list, including origins inherited
through a closure, aggregate, projection, alias, or reborrow. -/
structure Value where
  type : Expr
  owned : Owned := .shared
  origins : List ScopeId := []
  /-- Shared values must be safe to duplicate. In particular a shared closure
  cannot conceal a finite-use or uniquely consumed capture. -/
  duplicable : Bool := true
  /-- An unevaluated transfer from this binding; conversion consumes it once. -/
  place : Option OwnerId := none
  /-- Shared views keep the identity of their root owner through aliases. -/
  loanRoot : Option OwnerId := none
  deriving BEq, Repr, Inhabited

structure Owner where
  live : Bool := true
  unique : Bool := false
  loans : List ScopeId := []
  deriving BEq, Repr, Inhabited

structure Binding where
  contract : BinderContract
  value : Value
  owner : Owner := { unique := value.owned == .unique }
  demand : Uses := .erased
  /-- Borrow creation captures an owner without consuming its quantity. -/
  touched : Bool := false
  deriving BEq, Repr, Inhabited

structure State where
  /-- Opt-in conversion cache for a single immutable Program. Only the fresh
  definition-checking entry point enables it; mixed-program typing actions
  leave it disabled. Entries record completed reductions, never pending ones. -/
  resourceWhnfMemoEnabled : Bool := false
  resourceWhnfMemo : Array (Expr × Expr) := #[]
  bindings : Array Binding := #[]
  /-- Root 0 has no parent. Every new parent precedes its child. -/
  parents : Array (Option ScopeId) := #[none]
  remaining : Nat := 100000
  deriving BEq, Repr, Inhabited

abbrev CheckM := EStateM Error State

def liftExcept : Except Error α → CheckM α
  | .ok a => pure a
  | .error e => throw e

def tick : CheckM Unit := do
  let s ← get
  match s.remaining with
  | 0 => throw .budget
  | n + 1 => set { s with remaining := n }

def binding (id : OwnerId) : CheckM Binding := do
  match (← get).bindings[id]? with
  | some b => return b
  | none => throw (.unbound id)

def setBinding (id : OwnerId) (b : Binding) : CheckM Unit := do
  let s ← get
  if id < s.bindings.size then
    set { s with bindings := s.bindings.set! id b }
  else throw (.unbound id)

def pushBinding (contract : BinderContract) (value : Value) : CheckM OwnerId := do
  let s ← get
  let id := s.bindings.size
  set { s with bindings := s.bindings.push { contract, value } }
  return id

def newScope (parent : ScopeId) : CheckM ScopeId := do
  let s ← get
  if parent < s.parents.size then
    let id := s.parents.size
    set { s with parents := s.parents.push (some parent) }
    return id
  else throw .invalidScope

/-- Bounded traversal also rejects malformed/cyclic state supplied to this
low-level function. Generated states always have decreasing parent indices. -/
def outlivesAux (parents : Array (Option ScopeId)) (origin : ScopeId) :
    Nat → ScopeId → Bool
  | 0, _ => false
  | fuel + 1, destination =>
    if origin >= parents.size || destination >= parents.size then false
    else if origin == destination then true
    else match parents[destination]? with
      | some (some parent) => outlivesAux parents origin fuel parent
      | _ => false

def outlives (parents : Array (Option ScopeId)) (origin destination : ScopeId) : Bool :=
  outlivesAux parents origin (parents.size + 1) destination

def checkOrigins (parents : Array (Option ScopeId)) :
    List ScopeId → ScopeId → Except Error Unit
  | [], _ => .ok ()
  | origin :: rest, destination =>
    if outlives parents origin destination then checkOrigins parents rest destination
    else .error (.escape origin destination)

def checkUnrestricted (origins : List ScopeId) : Except Error Unit :=
  match origins with
  | [] => .ok ()
  | origin :: _ => .error (.unrestrictedEscape origin)

def unionOrigins (a b : List ScopeId) : List ScopeId :=
  b.foldl (fun acc origin => if acc.contains origin then acc else acc ++ [origin]) a

def charge (id : OwnerId) (uses : Uses) : CheckM Unit := do
  let b ← binding id
  if !b.owner.live then throw (.moved id)
  setBinding id { b with demand := b.demand.add uses, touched := true }

def checkDemand (id : OwnerId) (declared actual : Uses) : Except Error Unit :=
  if declared.covers actual then .ok () else .error (.usage id declared actual)

def validateUsage (id : OwnerId) : CheckM Unit := do
  let b ← binding id
  liftExcept (checkDemand id b.contract.uses b.demand)

/-- A move requires both exclusive availability and the absence of every
active loan. There is no transition that restores a moved owner. -/
def moveOwner (id : OwnerId) (owner : Owner) : Except Error Owner :=
  if !owner.live then .error (.moved id)
  else if !owner.unique then .error .sharedToUnique
  else if !owner.loans.isEmpty then .error (.activeLoan id)
  else .ok { owner with live := false }

def shareOwner (id : OwnerId) (owner : Owner) : Except Error Owner :=
  if !owner.live then .error (.moved id)
  else .ok { owner with unique := false }

def beginLoan (id : OwnerId) (scope : ScopeId) (owner : Owner) : Except Error Owner :=
  if !owner.live then .error (.moved id)
  else .ok { owner with loans := scope :: owner.loans }

/-- Removing a loan preserves both liveness and the permanent sharing state. -/
def endLoan (scope : ScopeId) (owner : Owner) : Owner :=
  { owner with loans := owner.loans.filter (· != scope) }

/-- Perform a place's ownership action once. Scope exit materializes its
result before ending loans, even when the result is being inferred. -/
def materialize (v : Value) : CheckM Value := do
  if let some id := v.place then
    let b ← binding id
    let owner ← liftExcept <| match v.owned with
      | .unique => moveOwner id b.owner
      | .shared => shareOwner id b.owner
    setBinding id { b with owner }
  return { v with place := none }

/-- Check a conversion and perform the transfer or permanent alias. Local
conversion is relative to the inferred destination scope; it narrows an
unrestricted value and preserves all earlier restrictions. -/
def consumeAs (required : ValueContract) (destination : ScopeId) (v : Value) :
    CheckM Value := do
  let parents := (← get).parents
  match required.locality with
  | .unrestricted => liftExcept (checkUnrestricted v.origins)
  | .local => liftExcept (checkOrigins parents v.origins destination)
  if required.owned == .unique && v.owned != .unique then
    throw .sharedToUnique
  if required.owned == .shared && !v.duplicable then
    throw .nonduplicable
  let v ← materialize { v with owned := required.owned }
  let origins := match required.locality with
    | .unrestricted => v.origins
    | .local => unionOrigins v.origins [destination]
  return { v with origins }

def invoke (v : Value) : CheckM Unit := do
  if v.owned == .shared && !v.duplicable then throw .nonduplicable
  if let some id := v.place then
    let b ← binding id
    if v.owned == .unique then
      let owner ← liftExcept (moveOwner id b.owner)
      setBinding id { b with owner }
    else if !b.owner.live then throw (.moved id)

def closeScope (scope : ScopeId) (result : Value) : CheckM Unit := do
  let s ← get
  let some (some parent) := s.parents[scope]? | throw .invalidScope
  liftExcept (checkOrigins s.parents result.origins parent)
  set { s with bindings := s.bindings.map fun (b : Binding) =>
    { b with owner := endLoan scope b.owner } }

def joinOwner (left right : Owner) : Owner :=
  { live := left.live && right.live
    unique := left.unique && right.unique
    loans := unionOrigins left.loans right.loans }

def joinValue (left right : Value) : Value :=
  { type := left.type
    owned := if left.owned == .unique && right.owned == .unique then .unique else .shared
    origins := unionOrigins left.origins right.origins
    duplicable := left.duplicable && right.duplicable
    place := if left.place == right.place then left.place else none
    loanRoot := if left.loanRoot == right.loanRoot then left.loanRoot else none }

end IxCC.Ixon.V3.Resource
