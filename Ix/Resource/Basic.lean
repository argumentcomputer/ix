module

public import Ix.Ixon

/-!
# Resource checking state

Scope identifiers and owner identities are internal to one checking run. They
are never lifetime parameters in an Ixon interface. All primitive transitions
are total and fail closed; successful scope exit never restores ownership by
assignment. Ending a loan only removes that particular loan.
-/

@[expose] public section

namespace Ix.Resource

open Ixon

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
  type : Ixon.Expr
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

/-- The meaning of an internal scope bound, independent of the executable
fuel-bounded ancestor walk. -/
inductive Ancestor (parents : Array (Option ScopeId)) (origin : ScopeId) : ScopeId → Prop
  | here (h : origin < parents.size) : Ancestor parents origin origin
  | parent {scope parent : ScopeId} (h : parents[scope]? = some (some parent))
      (outer : Ancestor parents origin parent) : Ancestor parents origin scope

/-- Generated parent tables point strictly backwards. -/
def ScopeTree (parents : Array (Option ScopeId)) : Prop :=
  ∀ (scope parent : ScopeId), parents[scope]? = some (some parent) → parent < scope

theorem root_scopeTree : ScopeTree #[none] := by
  intro scope parent h
  cases scope <;> simp at h

theorem push_scopeTree (parents : Array (Option ScopeId)) (parent : ScopeId)
    (tree : ScopeTree parents) (valid : parent < parents.size) :
    ScopeTree (parents.push (some parent)) := by
  intro scope outer h
  rw [Array.getElem?_push] at h
  split at h
  · rename_i same
    cases h
    simpa [same] using valid
  · exact tree scope outer h

theorem ancestor_older (parents : Array (Option ScopeId)) (origin destination : ScopeId)
    (tree : ScopeTree parents) (h : Ancestor parents origin destination) : origin ≤ destination := by
  induction h with
  | here => exact Nat.le_refl _
  | parent lookup _ ih =>
    have older := tree _ _ lookup
    exact Nat.le_trans ih (Nat.le_of_lt older)

theorem outlivesAux_sound (parents : Array (Option ScopeId)) (origin fuel destination : Nat)
    (h : outlivesAux parents origin fuel destination = true) :
    Ancestor parents origin destination := by
  induction fuel generalizing destination with
  | zero => simp [outlivesAux] at h
  | succ fuel ih =>
    simp only [outlivesAux] at h
    split at h
    · simp at h
    · rename_i valid
      split at h
      · rename_i same
        have eq : origin = destination := by simpa using same
        subst destination
        apply Ancestor.here
        have inside : ¬ origin >= parents.size := by
          intro outside
          exact valid (by simp [outside])
        exact Nat.lt_of_not_ge inside
      · split at h
        · rename_i parent hp
          exact Ancestor.parent hp (ih parent h)
        · simp at h

theorem outlives_sound (parents : Array (Option ScopeId)) (origin destination : Nat)
    (h : outlives parents origin destination = true) : Ancestor parents origin destination :=
  outlivesAux_sound parents origin _ destination h

theorem fresh_scope_cannot_escape (parents : Array (Option ScopeId)) (parent destination : ScopeId)
    (tree : ScopeTree parents) (valid : parent < parents.size) (older : destination < parents.size) :
    outlives (parents.push (some parent)) parents.size destination = false := by
  cases result : outlives (parents.push (some parent)) parents.size destination with
  | false => rfl
  | true =>
    have ancestor := outlives_sound _ _ _ result
    have order := ancestor_older _ _ _ (push_scopeTree parents parent tree valid) ancestor
    exact False.elim ((Nat.not_le_of_lt older) order)

theorem checkOrigins_sound (parents : Array (Option ScopeId)) (origins : List ScopeId)
    (destination : ScopeId) (h : checkOrigins parents origins destination = .ok ()) :
    ∀ origin ∈ origins, Ancestor parents origin destination := by
  induction origins with
  | nil => simp
  | cons origin rest ih =>
    simp only [checkOrigins] at h
    split at h
    · rename_i allowed
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact outlives_sound parents x destination allowed
      · exact ih h x hx
    · simp at h

@[simp] theorem endLoan_live (scope : ScopeId) (owner : Owner) :
    (endLoan scope owner).live = owner.live := rfl

@[simp] theorem endLoan_unique (scope : ScopeId) (owner : Owner) :
    (endLoan scope owner).unique = owner.unique := rfl

theorem moveOwner_requires (id : OwnerId) (before after : Owner)
    (h : moveOwner id before = .ok after) :
    before.live = true ∧ before.unique = true ∧ before.loans = [] ∧ after.live = false := by
  rcases before with ⟨live, unique, loans⟩
  cases live <;> cases unique <;> cases loans <;>
    simp_all [moveOwner]
  cases h
  rfl

theorem shareOwner_permanent (id : OwnerId) (before after : Owner)
    (h : shareOwner id before = .ok after) : after.unique = false := by
  rcases before with ⟨live, unique, loans⟩
  cases live <;> simp_all [shareOwner]
  cases h
  rfl

theorem checkUnrestricted_sound (origins : List ScopeId)
    (h : checkUnrestricted origins = .ok ()) : origins = [] := by
  cases origins <;> simp_all [checkUnrestricted]

theorem joinOwner_live (left right : Owner)
    (h : (joinOwner left right).live = true) : left.live = true ∧ right.live = true := by
  simpa [joinOwner] using h

theorem joinOwner_unique (left right : Owner)
    (h : (joinOwner left right).unique = true) :
    left.unique = true ∧ right.unique = true := by
  simpa [joinOwner] using h

theorem checkDemand_sound (id : OwnerId) (declared actual : Uses) (count : Nat)
    (accepted : checkDemand id declared actual = .ok ()) (demand : actual.admits count) :
    declared.admits count := by
  simp only [checkDemand] at accepted
  split at accepted
  · rename_i covers
    exact Uses.covers_sound declared actual count covers demand
  · simp at accepted

end Ix.Resource

end
