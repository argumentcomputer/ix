module
public import Ix.Resource.Transport.Convert
public import Ix.Resource.Admit

/-! Bidirectional source-contract typing. The ordinary resource checker
remains responsible for runtime ownership events. Coverage here follows its
argument/alternative traversal; proof and type expressions are checked too,
but cannot inherit a runtime check which skipped them. -/
@[expose] public section
namespace Ix.Resource.Transport
open Ixon

inductive Coverage where
  | uncovered
  | runtime
  | alternative (supplied : Nat)
  /-- Only the public header promises are discharged by a validated RHS.
  No original-body subtree inherits runtime coverage from the replacement. -/
  | replacement (headers : Nat)
  /-- Ghost computation at an authenticated equality endpoint. Proof
  descendants reset this role. It never asserts runtime coverage. -/
  | equalityEndpoint
  deriving BEq, Repr, Inhabited

def underBinder (ctx : Context) (c : BinderContract) (ty : Ixon.Expr)
    (action : Context → CheckM α) : CheckM α := do
  let before ← get
  let id ← pushBinding c { type := ty }
  let result ← action { ctx with vars := ctx.vars.push id }
  modify fun s => { s with bindings := before.bindings }
  return result

def getSort (m : Metadata) (fuel : Nat) (ctx : Context) (type : Ixon.Expr) : CheckM UInt64 := do
  match ← whnf ctx.program m fuel type with
  | .sort u => pure u
  | _ => throw (.unsupported "transport: expected a sort")

def requireSort (m : Metadata) (fuel : Nat) (ctx : Context) (type : Ixon.Expr) : CheckM Unit := do
  discard <| getSort m fuel ctx type

/-- Ordinary projection inference, including fields whose types only expose
their structure after an indexed computation. Resource field ownership rules
are a separate judgment and are not used as logical typing metadata. -/
def projectionType (m : Metadata) (fuel : Nat) (ctx : Context)
    (owner field : UInt64) (value valueType : Ixon.Expr) : CheckM Ixon.Expr := do
  let some ind := m.inductive? owner
    | throw (.unsupported "transport: projection family metadata missing")
  unless ind.constructors.size == 1 do
    throw (.unsupported "transport: projection family is not a structure")
  let some ctor := m.constructor? ind.constructors[0]!
    | throw (.unsupported "transport: projection constructor metadata missing")
  unless field.toNat < ctor.fields do
    throw (.unsupported "transport: projection field is out of bounds")
  let (head, args) ← splitApp ctx.program fuel (← whnf ctx.program m fuel valueType) []
  unless (match head with | .ref i _ => i == owner | _ => false) &&
      args.length == ind.params + ind.indices do
    throw (.unsupported "transport: projected value has no exposed structure type")
  let .ref _ levels := head | throw .typeMismatch
  let mut telescope ← instantiateDeclaration ctx.program m fuel ctor.index levels
    (← declaration ctx.program ctor.index).type
  for argument in args.toArray.extract 0 ctor.params do
    let (_, _, _, body) ← arrow ctx.program m fuel telescope
    telescope ← substitute ctx.program fuel body argument 0
  for k in [:field.toNat] do
    let (_, _, _, body) ← arrow ctx.program m fuel telescope
    telescope ← substitute ctx.program fuel body (.prj owner k.toUInt64 value) 0
  let (_, _, domain, _) ← arrow ctx.program m fuel telescope
  return domain

/-- A syntactically and transitively closed default-contract fragment. -/
def defaultClosed (m : Metadata) (runtime : Program) (fuel : Nat) (ctx : Context)
    (term expected : Ixon.Expr) : CheckM Bool := do
  unless m.resourceSensitive.size == runtime.declarations.size do return false
  let mut expressions := #[term, expected]
  for id in ctx.vars do
    let b ← binding id
    unless b.contract == .many do return false
    expressions := expressions.push b.value.type
  for e in expressions do
    let scan ← scanExpr ctx.program fuel e
    if scan.annotated then return false
    for dependency in scan.dependencies do
      if m.resourceSensitive[dependency]?.getD true then return false
  return true

/-- Check a whole computational witness in fresh ownership state. Each
lexical parameter gets the same owner/origin/duplicability setup as an
analyzed lambda binder, without inventing intermediate closure captures
between proof telescope parameters. Outer linear demand becomes affine:
an erased telescope imposes no exact runtime demand, but duplicate use is
still forbidden. Local lets were zeta-substituted before reaching here.
Returns true only if analyze visited this exact expression; defaultClosed
is a separate typing exemption, never a runtime-coverage assertion. -/
def checkWitness (m : Metadata) (runtime : Program) (fuel : Nat) (ctx : Context)
    (term expected : Ixon.Expr) : CheckM Bool := do
  if ← defaultClosed m runtime fuel ctx term expected then return false
  let some prop := runtime.propSort
    | throw (.unsupported "transport: ownership Prop metadata absent")
  let typeSort := if prop == 0 then 1 else 0
  let term ← eraseLevels ctx.program prop typeSort fuel term
  let type ← eraseLevels ctx.program prop typeSort fuel expected
  let telescope ← ctx.vars.mapM fun id => do
    let b ← binding id
    let c := if b.contract.uses == .linear then { b.contract with uses := .affine } else b.contract
    return (c, ← eraseLevels ctx.program prop typeSort fuel b.value.type)
  let before ← get
  -- The inner checker uses only the remaining budget; consumed work is
  -- charged to this typing run rather than reset for every witness.
  let limits : Limits := { depth := fuel, steps := before.remaining }
  let action : CheckM Unit := do
    if let .sort _ ← Resource.whnf runtime fuel type then
      throw (.unsupported "transport: runtime type erasure would skip a computational witness")
    let caller ← newScope 0
    let scope ← newScope caller
    let mut inner : Context := { program := runtime, scope }
    for (c, domain) in telescope do
      let duplicable ← if c.value.owned == .shared then pure true
        else pure ((← isShareable runtime fuel domain) || (← isScalar runtime fuel domain))
      let freezable ← if c.value.owned == .unique && !duplicable then plainData runtime fuel domain else pure false
      let id ← pushBinding c {
        type := domain, owned := c.value.owned, duplicable, freezable
        origins := if c.value.locality == .local then [caller] else [] }
      inner := { inner with vars := inner.vars.push id }
    let _ ← analyze fuel inner term (some (type, .shared)) caller .linear
    for id in inner.vars do validateBinder runtime fuel id
  match action.run { remaining := limits.steps } with
  | .error error state =>
    modify fun s => { s with remaining := state.remaining }
    throw error
  | .ok _ state =>
    modify fun s => { s with remaining := state.remaining }
    return true

/-- Runtime coverage for an argument is derived from the exact addressed
case/choice interfaces used by `analyze`. It is not based on source names. -/
def alternativeCoverageRuntime (runtime : Program) (fuel : Nat) (ctx : Context)
    (head : Ixon.Expr) (args : Array Ixon.Expr) (position : Nat) (domain : Ixon.Expr) :
    CheckM (Option Coverage) := do
  let .ref index _ := head | return none
  let runtimeCtx := { ctx with program := runtime }
  if runtime.choices.contains index then
    let n ← Resource.arity runtime fuel (← declaration runtime index).type
    if args.size < n || n < 2 || position < n - 2 || position ≥ n then return none
    let before ← get
    let mut inner := runtimeCtx
    let mut type := domain
    let mut count := 0
    repeat
      match ← Resource.whnf runtime fuel type with
      | .all c _ a b =>
        unless ← isProposition fuel inner a do break
        let id ← pushBinding c { type := a }
        inner := { inner with vars := inner.vars.push id }
        type := b
        count := count + 1
      | _ => break
    modify fun s => { s with bindings := before.bindings }
    return some (.alternative count)
  if runtime.cases then
    if let some r := recursorInfo runtime index then
      if args.size < r.arity then return none
      if r.params + r.motives ≤ position && position < r.params + r.motives + r.minors then
        return some (.alternative r.binders[position - r.params - r.motives]!)
      if position < r.arity - 1 then return some .uncovered
      return none
  if let some shape ← caseDefinition runtime fuel 4 index then
    if args.size < shape.arity then return none
    if let some supplied := shape.byNeed[position]?.bind id then
      -- This is the same eligibility check as the runtime substitution path.
      if ← alternativeArgument runtimeCtx fuel supplied args[position]! domain then
        return some (.alternative supplied)
  return none

def alternativeCoverage (runtime : Program) (fuel : Nat) (ctx : Context)
    (head : Ixon.Expr) (args : Array Ixon.Expr) (position : Nat) :
    CheckM Coverage := do
  let some prop := runtime.propSort
    | throw (.unsupported "transport: ownership Prop metadata absent")
  let typeSort := if prop == 0 then 1 else 0
  let before ← get
  let bindings ← before.bindings.mapM fun b => do
    return { b with value := { b.value with
      type := ← eraseLevels ctx.program prop typeSort fuel b.value.type } }
  let head ← eraseLevels ctx.program prop typeSort fuel head
  let args ← args.mapM (eraseLevels ctx.program prop typeSort fuel)
  modify fun s => { s with bindings }
  let runtimeCtx := { ctx with program := runtime }
  let mut fnType ← typeOf fuel runtimeCtx head
  if let .ref index _ := head then
    let special := runtime.choices.contains index ||
      (runtime.cases && (recursorInfo runtime index).any fun r => args.size ≥ r.arity)
    if special then fnType := (← declaration runtime index).type
  for j in [:position] do
    let (_, _, _, codomain) ← Resource.arrow runtime fuel fnType
    fnType ← substitute runtime fuel codomain args[j]! 0
  let (input, _, domain, _) ← Resource.arrow runtime fuel fnType
  let result ← match ← alternativeCoverageRuntime runtime fuel ctx head args position domain with
    | some coverage => pure coverage
    | none => do
      if input.uses == .erased || (← isProposition fuel runtimeCtx fnType) ||
          (← isProposition fuel runtimeCtx domain) then pure .uncovered
      else match ← Resource.whnf runtime fuel domain with
        | .sort _ => pure .uncovered
        | _ => pure .runtime
  modify fun s => { s with
    bindings := before.bindings
    parents := before.parents
    crossed := before.crossed
    plainHeads := before.plainHeads }
  return result

/- Type synthesis used only inside conversion/classification. Application
arguments are not revalidated here: the enclosing bidirectional traversal
checks every argument, and admission checks every declaration signature and
body in the forward closure. This is never an admission judgment or a way
to skip a proof argument. It retains source contracts and full universes. -/
mutual

def conversionType (m : Metadata) : Nat → Context → Ixon.Expr → CheckM Ixon.Expr
  | 0, _, _ => throw .budget
  | fuel + 1, ctx, e => do
    tick
    let telescope ← ctx.vars.mapM fun id => do
      let b ← binding id
      pure (b.contract, b.value.type)
    let key := (e, telescope)
    if let some type := (← get).transportTypes[key]? then return type
    let type ← conversionTypeCore m (fuel + 1) ctx e
    modify fun s => { s with transportTypes := s.transportTypes.insert key type }
    return type

def conversionTypeCore (m : Metadata) : Nat → Context → Ixon.Expr → CheckM Ixon.Expr
  | 0, _, _ => throw .budget
  | fuel + 1, ctx, e => do
    tick
    match e with
    | .var _ | .nat _ | .str _ => typeOf (fuel + 1) ctx e
    | .ref i levels => instantiateDeclaration ctx.program m fuel i levels (← declaration ctx.program i).type
    | .share i => conversionType m fuel ctx (← expansion ctx.program i)
    | .sort u => return .sort (← internUniverse (.succ (← readUniverse u)))
    | .all c _ a b =>
      let u ← getSort m fuel ctx (← conversionType m fuel ctx a)
      let v ← underBinder ctx c a fun inner => do
        getSort m fuel inner (← conversionType m fuel inner b)
      return .sort (← internUniverse (.imax (← readUniverse u) (← readUniverse v)))
    | .lam c a b =>
      let bodyType ← underBinder ctx c a fun inner => conversionType m fuel inner b
      return .all c .shared a bodyType
    | .app f a =>
      let (_, _, _, b) ← arrow ctx.program m fuel (← conversionType m fuel ctx f)
      substitute ctx.program fuel b a 0
    | .letE _ _ value body => conversionType m fuel ctx (← substitute ctx.program fuel body value 0)
    | .prj i field value => projectionType m fuel ctx i field value (← conversionType m fuel ctx value)
    | .recur .. => throw (.unsupported "transport: unresolved recursive reference")

end

def canonicalEquality (m : Metadata) (fuel : Nat) (ctx : Context)
    (expected : Ixon.Expr) : CheckM Bool := do
  let some eq := m.eqType | return false
  let (head, args) ← splitApp ctx.program fuel (← whnf ctx.program m fuel expected) []
  return args.length == 3 && (match head with | .ref i _ => i == eq | _ => false)

def naturalValue (m : Metadata) (p : Program) : Nat → Ixon.Expr → CheckM (Option Nat)
  | 0, _ => throw .budget
  | fuel + 1, value => do
    tick
    let some (.ref family _) := m.natType | return none
    let some ind := m.inductive? family | return none
    unless ind.constructors.size == 2 && ind.params == 0 && ind.indices == 0 do return none
    let value ← whnf p m fuel value
    if let .nat payload := value then return m.natural? payload
    let (head, args) ← splitApp p fuel value []
    let .ref ctor _ := head | return none
    if ctor == ind.constructors[0]! && args.isEmpty then return some 0
    if ctor == ind.constructors[1]! && args.length == 1 then
      return (← naturalValue m p fuel args[0]!).map (· + 1)
    return none

/-- Roles of the canonical, erased-validated Eq family only. In particular,
the recursor's minor and major proofs are never endpoint computations. -/
def equalityArgument (m : Metadata) (head : Ixon.Expr) (position : Nat) : Bool := Id.run do
  let some eq := m.eqType | return false
  let .ref i _ := head | return false
  if i == eq then return position == 1 || position == 2
  if (m.constructor? i).any (·.family == eq) then return position == 1
  if let some rec := m.recursor? i then
    if rec.family == eq then
      return position == 1 || position == rec.params ||
        (rec.params + rec.motives + rec.minors ≤ position && position < rec.major)
  return false

mutual

def infer (m : Metadata) (runtime : Program) :
    Nat → Context → Ixon.Expr → Coverage → CheckM Ixon.Expr
  | 0, _, _, _ => throw .budget
  | fuel + 1, ctx, term, coverage => do
    tick
    let mut coverage := coverage
    if coverage == .equalityEndpoint || coverage == .replacement 0 then
      let type ← conversionType m fuel ctx term
      if ← proofType m runtime fuel ctx type then
        coverage := .uncovered
      else if let .sort _ ← whnf ctx.program m fuel type then
        coverage := .uncovered
    match term with
    | .ref i levels => instantiateDeclaration ctx.program m fuel i levels (← declaration ctx.program i).type
    | .var _ | .nat _ | .str _ => typeOf (fuel + 1) ctx term
    | .sort u => return .sort (← internUniverse (.succ (← readUniverse u)))
    | .recur .. => throw (.unsupported "transport: unresolved recursive reference")
    | .share i => infer m runtime fuel ctx (← expansion ctx.program i) coverage
    | .all c _ domain body =>
      let u ← getSort m fuel ctx (← infer m runtime fuel ctx domain .uncovered)
      let v ← underBinder ctx c domain fun inner => do
        getSort m fuel inner (← infer m runtime fuel inner body .uncovered)
      return .sort (← internUniverse (.imax (← readUniverse u) (← readUniverse v)))
    | .lam c domain body =>
      requireSort m fuel ctx (← infer m runtime fuel ctx domain .uncovered)
      let next := match coverage with
        | .alternative (n + 1) => .alternative n
        | .replacement (n + 1) => .replacement n
        | other => other
      let result ← underBinder ctx c domain fun inner => infer m runtime fuel inner body next
      let expected := .all c .shared domain result
      unless ← proofType m runtime fuel ctx expected do
        if coverage == .uncovered || coverage == .replacement 0 then
          discard <| checkWitness m runtime fuel ctx term expected
      pure expected
    | .letE _ domain value body =>
      requireSort m fuel ctx (← infer m runtime fuel ctx domain .uncovered)
      let ghost ← canonicalEquality m fuel ctx (← conversionType m fuel ctx term)
      check m runtime fuel ctx value domain
        (if ghost then .equalityEndpoint else if coverage == .replacement 0 then coverage else .uncovered)
      infer m runtime fuel ctx (← substitute ctx.program fuel body value 0) coverage
    | .prj owner field value =>
      let valueType ← infer m runtime fuel ctx value coverage
      projectionType m fuel ctx owner field value valueType
    | .app .. =>
      let (head, arguments) ← splitApp ctx.program fuel term []
      let args := arguments.toArray
      -- A direct beta-redex building a canonical Eq type has no escaping
      -- function value. Check the actual domain/argument, then the complete
      -- substituted body; nested proofs retain their witness guards.
      if let .lam _ domain body := head then
        if !args.isEmpty && (← canonicalEquality m fuel ctx term) then
          requireSort m fuel ctx (← infer m runtime fuel ctx domain .uncovered)
          check m runtime fuel ctx args[0]! domain .equalityEndpoint
          let body ← substitute ctx.program fuel body args[0]! 0
          return ← infer m runtime fuel ctx (applyArgs body (args.extract 1 args.size)) .uncovered
      let runtimeCovered := match coverage with | .runtime | .alternative _ => true | _ => false
      let mut expanded : Option Ixon.Expr := none
      let applicationType ← conversionType m fuel ctx term
      if !runtimeCovered && (← canonicalEquality m fuel ctx applicationType) &&
          !(← defaultClosed m runtime fuel ctx term applicationType) then
        if let .ref i levels := head then
          if m.kinds[i.toNat]? == some .definition || m.kinds[i.toNat]? == some .theorem then
            if let some body := (← declaration ctx.program i).body then
              let body ← instantiateDeclaration ctx.program m fuel i levels body
              expanded := some (applyArgs body args)
      let headCoverage := if runtimeCovered || coverage == .equalityEndpoint || coverage == .replacement 0
        then coverage else .uncovered
      let mut type ← infer m runtime fuel ctx head headCoverage
      for position in [:args.size] do
        let (input, _, domain, body) ← arrow ctx.program m fuel type
        let mut argumentCoverage := if expanded.isSome || coverage == .equalityEndpoint ||
            equalityArgument m head position then Coverage.equalityEndpoint
          else if coverage == .replacement 0 && input.uses != .erased then coverage else .uncovered
        if runtimeCovered then
          argumentCoverage ← alternativeCoverage runtime fuel ctx head args position
        check m runtime fuel ctx args[position]! domain argumentCoverage
        type ← substitute ctx.program fuel body args[position]! 0
      if let some body := expanded then
        -- Deferred computational arguments are discharged at their actual
        -- uses in this instantiated proof, not by checking an abstract body.
        check m runtime fuel ctx (← whnf ctx.program m fuel body) type .uncovered
      return type

def check (m : Metadata) (runtime : Program) :
    Nat → Context → Ixon.Expr → Ixon.Expr → Coverage → CheckM Unit
  | 0, _, _, _, _ => throw .budget
  | fuel + 1, ctx, term, expected, requested => do
    tick
    let telescope ← ctx.vars.mapM fun id => do
      let b ← binding id
      pure (b.contract, b.value.type)
    let (tag, count) := match requested with
      | .uncovered => (0, 0) | .runtime => (1, 0)
      | .alternative n => (2, n) | .replacement n => (3, n)
      | .equalityEndpoint => (4, 0)
    let key := (term, expected, telescope, tag, count)
    if (← get).transportChecked.contains key then return
    checkCore m runtime (fuel + 1) ctx term expected requested
    modify fun s => { s with transportChecked := s.transportChecked.insert key () }

def checkCore (m : Metadata) (runtime : Program) :
    Nat → Context → Ixon.Expr → Ixon.Expr → Coverage → CheckM Unit
  | 0, _, _, _, _ => throw .budget
  | fuel + 1, ctx, term, expected, requested => do
    tick
    let requested := match term, requested with
      | .lam .., .replacement 0 => .uncovered
      | _, other => other
    let isProof ← proofType m runtime fuel ctx expected
    let mut coverage ← if isProof then pure Coverage.uncovered else
      match ← whnf ctx.program m fuel expected with
      | .sort _ => pure Coverage.uncovered
      | _ => pure requested
    if !isProof && coverage != .uncovered then
      let some prop := runtime.propSort
        | throw (.unsupported "transport: ownership Prop metadata absent")
      let erased ← eraseLevels ctx.program prop (if prop == 0 then 1 else 0) fuel expected
      if let .sort _ ← Resource.whnf runtime fuel erased then
        throw (.unsupported "transport: inherited runtime coverage skipped a computational type")
    if !isProof && coverage == .uncovered then
      match ← whnf ctx.program m fuel expected with
      | .sort _ => pure ()
      | _ =>
        if ← checkWitness m runtime fuel ctx term expected then coverage := .runtime
    match term with
    | .share i => check m runtime fuel ctx (← expansion ctx.program i) expected coverage
    | .lam input domain body =>
      let (declared, _, expectedDomain, codomain) ← arrow ctx.program m fuel expected
      unless input == declared do throw .binderMismatch
      requireSort m fuel ctx (← infer m runtime fuel ctx domain .uncovered)
      unless ← compatible m runtime fuel ctx domain expectedDomain do throw .typeMismatch
      let next := match coverage with
        | .alternative (n + 1) => .alternative n
        | .replacement (n + 1) => .replacement n
        | other => other
      underBinder ctx input domain fun inner => check m runtime fuel inner body codomain next
    | .letE _ domain value body =>
      requireSort m fuel ctx (← infer m runtime fuel ctx domain .uncovered)
      let ghost ← canonicalEquality m fuel ctx expected
      check m runtime fuel ctx value domain
        (if ghost then .equalityEndpoint else if coverage == .replacement 0 then coverage else .uncovered)
      check m runtime fuel ctx (← substitute ctx.program fuel body value 0) expected coverage
    | _ =>
      let actual ← infer m runtime fuel ctx term coverage
      unless ← compatible m runtime fuel ctx actual expected do throw .typeMismatch

/-- Positive proposition classification under the strengthened local types.
Unknown types fail rather than inherit proof erasure from the host kernel. -/
def proofType (m : Metadata) (runtime : Program) : Nat → Context → Ixon.Expr → CheckM Bool
  | 0, _, _ => throw .budget
  | fuel + 1, ctx, type => do
    tick
    match ← whnf ctx.program m fuel type with
    | .sort _ => pure false
    | .all c _ domain body => underBinder ctx c domain fun inner => proofType m runtime fuel inner body
    | reduced =>
      let type ← conversionType m fuel ctx reduced
      match ← whnf ctx.program m fuel type with
      | .sort s => universeZero fuel s
      | _ => throw (.unsupported "transport: type has no exposed sort")

def compatible (m : Metadata) (runtime : Program) :
    Nat → Context → Ixon.Expr → Ixon.Expr → CheckM Bool
  | 0, _, _, _ => throw .budget
  | fuel + 1, ctx, left, right => do
    tick
    let telescope ← ctx.vars.mapM fun id => do
      let b ← binding id
      pure (b.contract, b.value.type)
    let key := (left, right, telescope)
    if let some result := (← get).transportCompatible[key]? then return result
    let result ← compatibleCore m runtime (fuel + 1) ctx left right
    modify fun s => { s with transportCompatible := s.transportCompatible.insert key result }
    return result

def compatibleCore (m : Metadata) (runtime : Program) :
    Nat → Context → Ixon.Expr → Ixon.Expr → CheckM Bool
  | 0, _, _, _ => throw .budget
  | fuel + 1, ctx, left, right => do
    tick
    if left == right then return true
    let left ← whnf ctx.program m fuel left
    let right ← whnf ctx.program m fuel right
    if left == right then return true
    let numeric := match left, right with | .nat _, _ | _, .nat _ => true | _, _ => false
    if numeric then
      if let some lhs ← naturalValue m ctx.program fuel left then
        if let some rhs ← naturalValue m ctx.program fuel right then return lhs == rhs
    match left, right with
    | .sort i, .sort j => return ← universeEqual fuel i j
    | .ref i us, .ref j vs =>
      if i == j && us.size == vs.size then
        let mut same := true
        for (u, v) in us.zip vs do same := same && (← universeEqual fuel u v)
        if same then return true
    | .all c r a b, .all c' r' a' b' =>
      unless c == c' && r == r' && (← compatible m runtime fuel ctx a a') do return false
      return ← underBinder ctx c a fun inner => compatible m runtime fuel inner b b'
    | .lam c a b, .lam c' a' b' =>
      unless c == c' && (← compatible m runtime fuel ctx a a') do return false
      return ← underBinder ctx c a fun inner => compatible m runtime fuel inner b b'
    | .app f a, .app g b =>
      if (← compatible m runtime fuel ctx f g) && (← compatible m runtime fuel ctx a b) then return true
    | .prj t i v, .prj u j w =>
      if t == u && i == j && (← compatible m runtime fuel ctx v w) then return true
    | _, _ => pure ()
    -- Typed proof irrelevance uses synthesized full proposition types.
    -- The enclosing full traversal (not conversionType itself) checks every
    -- argument and all source signatures/bodies before admission succeeds.
    let leftType ← conversionType m fuel ctx left
    let rightType ← conversionType m fuel ctx right
    if (← proofType m runtime fuel ctx leftType) && (← proofType m runtime fuel ctx rightType) then
      return ← compatible m runtime fuel ctx leftType rightType
    -- Function eta uses a checked common full-contract arrow. It never
    -- erases a lambda input contract or invents its result promise.
    match left, right with
    | .lam c a body, other =>
      match ← whnf ctx.program m fuel rightType with
      | .all d _ domain _ =>
        if c != d || !(← compatible m runtime fuel ctx a domain) then return false
        check m runtime fuel ctx left rightType .uncovered
        let shifted ← shift ctx.program fuel other 1 0
        return ← underBinder ctx c a fun inner =>
          compatible m runtime fuel inner body (.app shifted (.var 0))
      | _ => return false
    | _, .lam .. => compatible m runtime fuel ctx right left
    | _, _ => return false

end
end Ix.Resource.Transport
end
