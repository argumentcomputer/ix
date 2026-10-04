module
public import Ix.Resource.Transport.Core

/-! Source universes retain parameter identity and are instantiated at every
constant use. The resource adapter's two-sort abstraction is not a typing
representation. The independent erased check still validates readUniverse
constraints; this layer retains them when classifying computational terms. -/
@[expose] public section
namespace Ix.Resource.Transport

def readUniverse (i : UInt64) : CheckM Ixon.Univ := do
  let some u := (← get).transportUniverses[i.toNat]?
    | throw (.unsupported "transport: readUniverse index out of bounds")
  return u

def internUniverse (u : Ixon.Univ) : CheckM UInt64 := do
  tick
  let s ← get
  if let some i := s.transportUniverses.findIdx? (· == u) then return i.toUInt64
  unless s.transportUniverses.size < UInt64.size do throw .budget
  set { s with transportUniverses := s.transportUniverses.push u }
  return s.transportUniverses.size.toUInt64

def neverZeroUniverse : Nat → Ixon.Univ → CheckM Bool
  | 0, _ => throw .budget
  | fuel + 1, u => do
    tick
    match u with
    | .zero | .var _ => return false
    | .succ _ => return true
    | .max a b => return (← neverZeroUniverse fuel a) || (← neverZeroUniverse fuel b)
    | .imax _ b => neverZeroUniverse fuel b

def offsetUniverse : Nat → Ixon.Univ → CheckM (Ixon.Univ × Nat)
  | 0, _ => throw .budget
  | fuel + 1, .succ a => do
    tick
    let (base, n) ← offsetUniverse fuel a
    return (base, n + 1)
  | _ + 1, a => pure (a, 0)

def maxUniverse (fuel : Nat) (a b : Ixon.Univ) : CheckM Ixon.Univ := do
  tick
  if a == b || b == .zero then return a
  if a == .zero then return b
  if (match b with | .max x y => a == x || a == y | _ => false) then return b
  if (match a with | .max x y => b == x || b == y | _ => false) then return a
  let (baseA, n) ← offsetUniverse fuel a
  let (baseB, k) ← offsetUniverse fuel b
  if baseA == baseB then return if n ≥ k then a else b
  return .max a b

/-- Bounded local level simplifications. This deliberately does not perform
exponential imax distribution, and has no erased-equality fallback. -/
def normalizeUniverse : Nat → Ixon.Univ → CheckM Ixon.Univ
  | 0, _ => throw .budget
  | fuel + 1, u => do
    tick
    match u with
    | .zero | .var _ => return u
    | .succ a => return .succ (← normalizeUniverse fuel a)
    | .max a b => maxUniverse fuel (← normalizeUniverse fuel a) (← normalizeUniverse fuel b)
    | .imax a b =>
      let a ← normalizeUniverse fuel a
      let b ← normalizeUniverse fuel b
      if ← neverZeroUniverse fuel b then return ← maxUniverse fuel a b
      if b == .zero || a == .zero || a == .succ .zero || a == b then return b
      return .imax a b

/-- Max/successor normal form: collect each base with its greatest offset.
`succ (max a b)` distributes without duplicating a subtree traversal. All
base levels are natural-valued, so a constant offset is subsumed by an
equal or greater offset on any other base. Conditional imax atoms remain
opaque unless the bounded local simplifier eliminated them. -/
def levelAtoms : Nat → Ixon.Univ → Nat → Array (Ixon.Univ × Nat) →
    CheckM (Array (Ixon.Univ × Nat))
  | 0, _, _, _ => throw .budget
  | fuel + 1, u, offset, atoms => do
    tick
    match u with
    | .succ a => levelAtoms fuel a (offset + 1) atoms
    | .max a b => levelAtoms fuel b offset (← levelAtoms fuel a offset atoms)
    | base =>
      let mut found := false
      let mut output := #[]
      for (other, n) in atoms do
        tick
        if other == base then
          found := true
          output := output.push (base, max n offset)
        else output := output.push (other, n)
      return if found then output else output.push (base, offset)

def simplifyAtoms (atoms : Array (Ixon.Univ × Nat)) : CheckM (Array (Ixon.Univ × Nat)) := do
  let mut output := #[]
  for (base, n) in atoms do
    let mut subsumed := false
    if base == .zero then
      for (other, k) in atoms do
        tick
        if other != .zero && n ≤ k then subsumed := true
    unless subsumed do output := output.push (base, n)
  return output

def universeEqual (fuel : Nat) (i j : UInt64) : CheckM Bool := do
  if i == j then return true
  let a ← normalizeUniverse fuel (← readUniverse i)
  let b ← normalizeUniverse fuel (← readUniverse j)
  if a == b then return true
  let left ← simplifyAtoms (← levelAtoms fuel a 0 #[])
  let right ← simplifyAtoms (← levelAtoms fuel b 0 #[])
  unless left.size == right.size do return false
  for atom in left do
    let mut found := false
    for other in right do
      tick
      if atom == other then found := true
    unless found do return false
  return true

def zeroUniverse : Nat → Ixon.Univ → CheckM Bool
  | 0, _ => throw .budget
  | fuel + 1, u => do
    tick
    match u with
    | .zero => return true
    | .succ _ | .var _ => return false
    | .max a b => return (← zeroUniverse fuel a) && (← zeroUniverse fuel b)
    | .imax _ b => zeroUniverse fuel b

def universeZero (fuel : Nat) (i : UInt64) : CheckM Bool := do
  zeroUniverse fuel (← readUniverse i)

def instantiateUniverse (values : Array Ixon.Univ) : Nat → Ixon.Univ → CheckM Ixon.Univ
  | 0, _ => throw .budget
  | fuel + 1, u => do
    tick
    match u with
    | .zero => pure .zero
    | .var i =>
      let some u := values[i.toNat]? | throw (.unsupported "transport: unbound readUniverse parameter")
      return u
    | .succ a => return .succ (← instantiateUniverse values fuel a)
    | .max a b => return .max (← instantiateUniverse values fuel a) (← instantiateUniverse values fuel b)
    | .imax a b => return .imax (← instantiateUniverse values fuel a) (← instantiateUniverse values fuel b)

/- Sharing is expanded before substitution because its table belongs to
the original generic declaration. Exact caches include the full universe
substitution; they never reuse a generic share across different instances. -/
mutual

def instantiateLevels (p : Program) (values : Array Ixon.Univ) :
    Nat → Ixon.Expr → CheckM Ixon.Expr
  | 0, _ => throw .budget
  | fuel + 1, e => do
    tick
    let key := (e, values)
    if let some result := (← get).transportInstances[key]? then return result
    let result ← instantiateLevelsCore p values (fuel + 1) e
    modify fun s => { s with transportInstances := s.transportInstances.insert key result }
    return result

def instantiateLevelsCore (p : Program) (values : Array Ixon.Univ) :
    Nat → Ixon.Expr → CheckM Ixon.Expr
  | 0, _ => throw .budget
  | fuel + 1, e => do
    tick
    let level := fun i => do
      internUniverse (← instantiateUniverse values fuel (← readUniverse i))
    match e with
    | .sort i => return .sort (← level i)
    | .ref i ls => return .ref i (← ls.mapM level)
    | .share i => instantiateLevels p values fuel (← expansion p i)
    | .all c r a b => return .all c r (← instantiateLevels p values fuel a) (← instantiateLevels p values fuel b)
    | .lam c a b => return .lam c (← instantiateLevels p values fuel a) (← instantiateLevels p values fuel b)
    | .app f a => return .app (← instantiateLevels p values fuel f) (← instantiateLevels p values fuel a)
    | .letE c a v b =>
      return .letE c (← instantiateLevels p values fuel a)
        (← instantiateLevels p values fuel v) (← instantiateLevels p values fuel b)
    | .prj i f v => return .prj i f (← instantiateLevels p values fuel v)
    | .recur .. => throw (.unsupported "transport: unresolved recursive reference")
    | _ => pure e

end

def instantiateDeclaration (p : Program) (m : Metadata) (fuel : Nat)
    (i : UInt64) (levels : Array UInt64) (term : Ixon.Expr) : CheckM Ixon.Expr := do
  unless m.levelArities[i.toNat]? == some levels.size do
    throw (.unsupported "transport: readUniverse argument arity mismatch")
  instantiateLevels p (← levels.mapM readUniverse) fuel term

/-- The ownership interpreter uses a two-sort representation. Expanded
source expressions cross that boundary only after classifying instantiated
levels; source typing itself never reads the collapsed representation. -/
def eraseLevels (p : Program) (prop type : UInt64) : Nat → Ixon.Expr → CheckM Ixon.Expr
  | 0, _ => throw .budget
  | fuel + 1, e => do
    tick
    match e with
    | .sort u => return .sort (if ← universeZero fuel u then prop else type)
    | .share i => eraseLevels p prop type fuel (← expansion p i)
    | .all c r a b => return .all c r (← eraseLevels p prop type fuel a) (← eraseLevels p prop type fuel b)
    | .lam c a b => return .lam c (← eraseLevels p prop type fuel a) (← eraseLevels p prop type fuel b)
    | .app f a => return .app (← eraseLevels p prop type fuel f) (← eraseLevels p prop type fuel a)
    | .letE c a v b =>
      return .letE c (← eraseLevels p prop type fuel a)
        (← eraseLevels p prop type fuel v) (← eraseLevels p prop type fuel b)
    | .prj i f v => return .prj i f (← eraseLevels p prop type fuel v)
    | _ => return e

end Ix.Resource.Transport
end
