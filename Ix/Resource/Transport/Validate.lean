module
public import Ix.Resource.Transport.Check
public import Ix.Resource.Admit

/-! Source-contract validation is an additional judgment over the exact
canonical environment checked by erased typing. It cannot replace erased
typing or resource admission. No source body may evade this judgment by
appearing in a runtime profile's assumption list. -/
@[expose] public section
namespace Ix.Resource.Transport

structure Request where
  /-- Initial resource-relevant declarations and bound equation proofs. -/
  roots : Array Nat
  /-- Exact original bodies already covered by successful ownership runs.
  Checking an unfolding equation does not cover the original body. -/
  runtimeCovered : Array Nat := #[]
  /-- Explicit addressed axiomatic assumptions; never body exemptions. -/
  assumptions : Array Nat := #[]
  equations : Array (Nat × Nat) := #[]
  deriving Inhabited

def runTyping (m : Metadata) (limits : Limits) (action : CheckM α) : Except Error α :=
  match action.run { remaining := limits.steps, transportUniverses := m.universes } with
  | .ok value _ => .ok value
  | .error error _ => .error error

def resourceSensitivity (logical runtime : Program) (limits : Limits) : Except Error (Array Bool) := do
  let (sourceGraph, sourceMarks) ← dependencyGraph logical limits
  let (runtimeGraph, runtimeMarks) ← dependencyGraph runtime limits
  unless sourceGraph.size == runtimeGraph.size do throw (.unsupported "transport: source/runtime declaration mismatch")
  let graph := sourceGraph.zipWith (· ++ ·) runtimeGraph
  let marks := sourceMarks.zipWith (· || ·) runtimeMarks
  return propagate graph marks

/-- A resource equation is universally about the original declaration, not
one convenient universe instance. Its proof being valid is insufficient. -/
def validateEquation (p runtime : Program) (m : Metadata) (fuel : Nat)
    (definition equation : Nat) : CheckM Nat := do
  let some eq := m.eqType | throw (.unsupported "transport: canonical equality identity absent")
  let some levels := m.levelArities[definition]? | throw (.badReference definition)
  unless m.levelArities[equation]? == some levels do
    throw (.unsupported "transport: equation universe arity differs from definition")
  let mut statement := (← declaration p equation.toUInt64).type
  let mut expected := (← declaration p definition.toUInt64).type
  let mut ctx : Context := { program := p }
  let mut count := 0
  for _ in [:fuel] do
    let reduced ← whnf p m fuel statement
    let .all _ _ domain body := reduced | statement := reduced; break
    let (input, _, sourceDomain, sourceBody) ← arrow p m fuel expected
    unless ← compatible m runtime fuel ctx domain sourceDomain do throw .typeMismatch
    let id ← pushBinding input { type := sourceDomain }
    ctx := { ctx with vars := ctx.vars.push id }
    expected := sourceBody
    statement := body
    count := count + 1
  let (head, args) ← splitApp p fuel statement []
  unless (match head with | .ref i _ => i == eq | _ => false) && args.length == 3 do
    throw (.unsupported "transport: equation has no canonical equality statement")
  let (function, arguments) ← splitApp p fuel args[1]! []
  let .ref index us := function | throw (.unsupported "transport: equation lhs is not a declaration")
  unless index.toNat == definition && us.size == levels && arguments.length == count do
    throw (.unsupported "transport: equation lhs does not apply its original declaration")
  for i in [:levels] do
    unless (← readUniverse us[i]!) == .var i.toUInt64 do
      throw (.unsupported "transport: equation specializes a declaration universe")
  for i in [:count] do
    unless (← unshare p fuel arguments[i]!) == .var (count - 1 - i).toUInt64 do
      throw (.unsupported "transport: equation lhs argument telescope differs")
  return count

/-- The graph includes source theorem bodies, all auxiliary rule syntax,
and mutual families. Traversing only the caller's marked subgraph is unsafe. -/
def forwardClosure (p : Program) (limits : Limits) (roots : Array Nat) :
    Except Error (Array Bool) := do
  let (reverse, _) ← dependencyGraph p limits
  let mut forward := Array.replicate p.declarations.size #[]
  for dependency in [:reverse.size] do
    for caller in reverse[dependency]! do
      forward := forward.set! caller (forward[caller]!.push dependency)
  let mut selected := Array.replicate p.declarations.size false
  for root in roots do
    unless root < selected.size do throw (.badReference root)
    selected := selected.set! root true
  return propagate forward selected

def primitive : Kind → Bool
  | .inductiveType | .constructor | .recursor | .quotient => true
  | _ => false

/-- Conservative primitive rule: its complete forward dependency family
must be the default-contract fragment. Together with canonical erased
family/rule validation this permits ordinary indexed eliminators without
inventing annotated constructor or recursor typing rules. -/
def validatePrimitiveFragment (p : Program) (m : Metadata) (limits : Limits)
    (selected : Array Bool) : Except Error Unit := do
  let mut roots := #[]
  for i in [:selected.size] do
    if selected[i]! && primitive (m.kinds[i]?.getD .opaqueDecl) then
      roots := roots.push i
  let primitiveDependencies ← forwardClosure p limits roots
  let (_, marked) ← dependencyGraph p limits
  for i in [:marked.size] do
    if primitiveDependencies[i]! && m.unsafePrimitives.contains i then
      throw (.unsupported "transport: unsafe primitive family is outside the validated fragment")
    if primitiveDependencies[i]! && marked[i]! then
      throw (.unsupported "transport: annotated primitive family requires contract-sensitive primitive rules")
  -- Absence of a metadata record never authorizes a primitive operation.
  for i in roots do
    match m.kinds[i]! with
    | .inductiveType =>
      let some ind := m.inductive? i.toUInt64
        | throw (.unsupported "transport: incomplete inductive metadata")
      for c in ind.constructors do
        let some ctor := m.constructor? c
          | throw (.unsupported "transport: incomplete constructor family")
        unless ctor.family == i.toUInt64 && ctor.params == ind.params do
          throw (.unsupported "transport: mismatched constructor family")
    | .constructor =>
      let some ctor := m.constructor? i.toUInt64
        | throw (.unsupported "transport: incomplete constructor metadata")
      let some ind := m.inductive? ctor.family
        | throw (.unsupported "transport: constructor owner missing")
      unless ind.constructors[ctor.position]? == some ctor.index do
        throw (.unsupported "transport: constructor ordinal mismatch")
    | .recursor =>
      let some rec := m.recursor? i.toUInt64
        | throw (.unsupported "transport: incomplete recursor metadata")
      let some ind := m.inductive? rec.family
        | throw (.unsupported "transport: recursor family missing")
      unless rec.rules.size == ind.constructors.size do
        throw (.unsupported "transport: incomplete recursor rules")
      for j in [:rec.rules.size] do
        let some ctor := m.constructor? ind.constructors[j]!
          | throw (.unsupported "transport: recursor constructor missing")
        unless rec.rules[j]!.fields == ctor.fields do
          throw (.unsupported "transport: recursor rule field mismatch")
    | _ => pure ()

/-- Requires same-byte erased validation and ownership admission by the
caller. Internal adapter API: `Request.runtimeCovered` is derived from the
actual successful ownership traversal, never accepted from a profile. -/
def validate (logical runtime : Program) (m : Metadata) (request : Request)
    (limits : Limits := {}) : Except Failure Unit := do
  let p := sourceProgram m logical
  let sensitive ← (resourceSensitivity p runtime limits).mapError (⟨none, ·⟩)
  let m := { m with resourceSensitive := sensitive }
  unless m.kinds.size == p.declarations.size && m.levelArities.size == p.declarations.size do
    throw ⟨none, .unsupported "transport: incomplete declaration metadata"⟩
  let roots := request.roots ++ request.equations.flatMap (fun (d, t) => #[d, t])
  let selected ← (forwardClosure p limits roots).mapError (⟨none, ·⟩)
  (validatePrimitiveFragment p m limits selected).mapError (⟨none, ·⟩)
  let runtimeMarked ← (relevance runtime limits).mapError (⟨none, ·⟩)
  let mut replacements := #[]
  for (d, t) in request.equations do
    let count ← (runTyping m limits (validateEquation p runtime m limits.depth d t)).mapError (⟨some t, ·⟩)
    -- This is precisely Admit.admitProgramCrossed's definition branch.
    -- A profile-assumed or unmarked definition did not run its RHS through
    -- analyze, so membership in the equation list gives it no exemption.
    if runtimeMarked[d]?.getD false && !request.assumptions.contains d &&
        runtime.declarations[d]?.any (fun decl => decl.kind == .definition) &&
        runtime.equations.contains (d.toUInt64, t.toUInt64) then
      replacements := replacements.push (d, count)
  for i in [:p.declarations.size] do
    unless selected[i]! do continue
    let d := p.declarations[i]!
    let action : CheckM Unit := do
      let ctx : Context := { program := p, scope := 0 }
      requireSort m limits.depth ctx (← infer m runtime limits.depth ctx d.type .uncovered)
      match d.body with
      | some body =>
        -- Includes every theorem, opaque body and profile-assumed definition.
        let coverage := if let some (_, count) := replacements.find? (·.1 == i) then .replacement count
          else if request.runtimeCovered.contains i then .runtime else .uncovered
        check m runtime limits.depth ctx body d.type coverage
      | none =>
        match m.kinds[i]! with
        | .inductiveType | .constructor | .recursor | .quotient => pure ()
        | .axiomDecl standard =>
          unless standard || request.assumptions.contains i do
            throw (.unsupported "transport: untrusted source axiom")
        | _ => throw (.unsupported "transport: source declaration has no checked body")
    (runTyping m limits action).mapError (⟨some i, ·⟩)

end Ix.Resource.Transport
end
