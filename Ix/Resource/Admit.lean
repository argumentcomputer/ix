module

public import Ix.Resource.Check

/-!
# Resource admission for a resolved program

Ordinary components have no resource promise beyond shared, unrestricted,
arbitrary-use access. They can use the ordinary typechecking path. A fixed
point marks every declaration that contains, refers to, or shares a mutual
block with a resource contract. Marked definitions are checked, marked
external interfaces require an explicit profile assumption, and constructors
must preserve their captures in every intermediate and final result.
-/

@[expose] public section

namespace Ix.Resource

open Ixon

structure Scan where
  annotated : Bool := false
  dependencies : Array Nat := #[]
  deriving Inhabited, Repr

def Scan.merge (a b : Scan) : Scan :=
  { annotated := a.annotated || b.annotated
    dependencies := a.dependencies ++ b.dependencies }

/-- Context-free reachability uses a DAG walk, not a tree expansion. The
active set rejects sharing cycles; the finished set records only scanned
syntax, never validity under a scope or ownership context. -/
def scanExpr (program : Program) (fuel : Nat) (top : Ixon.Expr) : CheckM Scan := do
  if fuel == 0 then throw .budget
  let mut finished : Std.HashSet Ixon.Expr := {}
  let mut active : Std.HashSet Ixon.Expr := {}
  let mut stack := #[(top, false)]
  let mut scan : Scan := {}
  while !stack.isEmpty do
    let (e, closing) := stack.back!
    stack := stack.pop
    if closing then
      active := active.erase e
      finished := finished.insert e
      continue
    if active.contains e then throw (.unsupported "cyclic sharing")
    if finished.contains e then continue
    tick
    active := active.insert e
    stack := stack.push (e, true)
    match e with
    | .ref index _ =>
      let _ ← declaration program index
      scan := { scan with dependencies := scan.dependencies.push index.toNat }
    | .recur .. => throw (.unsupported "unresolved recursive reference")
    | .share index => stack := stack.push (← expansion program index, false)
    | .prj index _ value =>
      let _ ← declaration program index
      scan := { scan with dependencies := scan.dependencies.push index.toNat }
      stack := stack.push (value, false)
    | .app fn arg => stack := stack.push (arg, false) |>.push (fn, false)
    | .lam input type body =>
      scan := { scan with annotated := scan.annotated || input != .many }
      stack := stack.push (body, false) |>.push (type, false)
    | .all input result type body =>
      scan := { scan with annotated := scan.annotated || input != .many || result != .shared }
      stack := stack.push (body, false) |>.push (type, false)
    | .letE contract type value body =>
      scan := { scan with annotated := scan.annotated || contract.binder != .many || contract.kind != .value }
      stack := stack.push (body, false) |>.push (value, false) |>.push (type, false)
    | _ => pure ()
  return scan

def runCheck (limits : Limits) (action : CheckM α) : Except Error α :=
  match action.run { remaining := limits.steps } with
  | .ok result _ => .ok result
  | .error error _ => .error error

def relevance (program : Program) (limits : Limits := {}) : Except Error (Array Bool) := do
  let size := program.declarations.size
  let mut reverse : Array (Array Nat) := Array.replicate size #[]
  let mut marked := Array.replicate size false
  let mut queue := #[]
  for i in [0:size] do
    let d := program.declarations[i]!
    let scan ← runCheck limits do
      let type ← scanExpr program limits.depth d.type
      match d.body with
      | none => return type
      | some value => return type.merge (← scanExpr program limits.depth value)
    if scan.annotated then
      marked := marked.set! i true
      queue := queue.push i
    for dependency in scan.dependencies do
      if dependency >= size then throw (.badReference dependency)
      reverse := reverse.set! dependency (reverse[dependency]!.push i)
  for (i, expression) in program.auxiliary do
    if i >= size then throw (.badReference i)
    let scan ← runCheck limits (scanExpr program limits.depth expression)
    if scan.annotated && !marked[i]! then
      marked := marked.set! i true
      queue := queue.push i
    for dependency in scan.dependencies do
      if dependency >= size then throw (.badReference dependency)
      reverse := reverse.set! dependency (reverse[dependency]!.push i)
  for field in program.fields do
    let i := field.typeRef.toNat
    if i >= size then throw (.badReference i)
    if field.contract != .shared && !marked[i]! then
      marked := marked.set! i true
      queue := queue.push i
  for group in program.groups do
    if let some first := group[0]? then
      if first >= size then throw (.badReference first)
      for member in group do
        if member >= size then throw (.badReference member)
        reverse := reverse.set! first (reverse[first]!.push member)
        reverse := reverse.set! member (reverse[member]!.push first)
  let mut cursor := 0
  while cursor < queue.size do
    let i := queue[cursor]!
    cursor := cursor + 1
    for dependent in reverse[i]! do
      if !marked[dependent]! then
        marked := marked.set! dependent true
        queue := queue.push dependent
  return marked

/-- Constructors retain runtime fields. Finite/unique captures require a
unique result, and local captures require a local result. This applies to
partial applications as well as the final aggregate. Type arguments and
explicitly erased fields have no runtime capture. -/
def checkConstructorType (program : Program) :
    Nat → Ixon.Expr → Bool → Bool → CheckM Unit
  | 0, _, _, _ => throw .budget
  | fuel + 1, type, hasFinite, hasLocal => do
    tick
    let type ← whnf program fuel type
    match type with
    | .all input result domain codomain =>
      let domain ← whnf program fuel domain
      let erased := input.uses == .erased || (match domain with | .sort _ => true | _ => false)
      if !input.uses.covers (if erased then .erased else .linear) then
        throw (.unsupported "constructor input quantity does not cover its stored occurrence")
      let finite := hasFinite || (!erased && (input.uses != .many || input.value.owned == .unique))
      let localCapture := hasLocal || (!erased && input.value.locality == .local)
      if finite && result.owned != .unique then
        throw (.unsupported "constructor result drops a finite or unique capture")
      if localCapture && result.locality != .local then
        throw (.unsupported "constructor result drops a local capture")
      checkConstructorType program fuel codomain finite localCapture
    | _ => pure ()

structure Policy where
  /-- Resolved indices of externally admitted, addressed resource interfaces.
  The address adapter obtains this list from the bound primitive profile. -/
  assumptions : Array Nat := #[]
  shareableTypes : Array Nat := #[]
  choices : Array Nat := #[]
  deriving Inhabited, Repr

structure AdmissionError where
  declaration : Option Nat
  error : Error
  deriving Repr

def admitProgram (program : Program) (policy : Policy := {}) (limits : Limits := {}) :
    Except AdmissionError Unit := do
  for index in program.choices do
    unless policy.choices.contains index.toNat && policy.assumptions.contains index.toNat do
      throw ⟨some index.toNat, .unsupported "selection behavior is absent from the bound profile"⟩
    let some d := program.declarations[index.toNat]?
      | throw ⟨none, .badReference index.toNat⟩
    unless d.kind == .assumption do
      throw ⟨some index.toNat, .unsupported "selection behavior requires an external primitive interface"⟩
  for index in program.shareableTypes do
    unless policy.shareableTypes.contains index.toNat do
      throw ⟨some index.toNat, .unsupported "shareable representation is absent from the bound profile"⟩
  let marked ← (relevance program limits).mapError (⟨none, ·⟩)
  for i in [0:program.declarations.size] do
    if marked[i]! then
      let d := program.declarations[i]!
      let checked : Except Error Unit := match d.kind with
        | .definition => checkDefinition program i limits
        | .assumption =>
          if policy.assumptions.contains i then .ok ()
          else .error (.unsupported "external resource interface is absent from the bound profile")
        | .constructor => runCheck limits (checkConstructorType program limits.depth d.type false false)
        | .typeConstructor => .ok ()
      checked.mapError (⟨some i, ·⟩)

end Ix.Resource

end


