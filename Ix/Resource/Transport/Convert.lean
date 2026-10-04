module
public import Ix.Resource.Transport.Universe

/-! Contract-preserving reduction. The metadata must have passed the
transport primitive-family check; erased typing of the original bytes is
also required. No branch falls back to erased definitional equality. -/
@[expose] public section
namespace Ix.Resource.Transport
open Ixon

def applyArgs (fn : Ixon.Expr) (args : Array Ixon.Expr) : Ixon.Expr :=
  args.foldl Ixon.Expr.app fn

/-- A bounded constructor spelling for a numeric major premise. This is
used only when iota needs a constructor, never as eager numeral expansion. -/
def naturalConstructor (p : Program) (m : Metadata) : Nat → Nat → CheckM Ixon.Expr
  | 0, _ => throw .budget
  | fuel + 1, value => do
    tick
    let some (.ref family _) := p.natType
      | throw (.unsupported "transport: numeric reduction has no natural type")
    let some ind := m.inductive? family
      | throw (.unsupported "transport: natural constructor metadata missing")
    unless ind.params == 0 && ind.indices == 0 && ind.constructors.size == 2 do
      throw (.unsupported "transport: invalid natural constructor metadata")
    match value with
    | 0 => pure (.ref ind.constructors[0]! #[])
    | n + 1 => return .app (.ref ind.constructors[1]! #[]) (← naturalConstructor p m fuel n)

mutual

def whnf (p : Program) (m : Metadata) : Nat → Ixon.Expr → CheckM Ixon.Expr
  | 0, _ => throw .budget
  | fuel + 1, e => do
    tick
    if let some result := (← get).transportWhnf[e]? then return result
    let result ← whnfCore p m (fuel + 1) e
    modify fun s => { s with transportWhnf := s.transportWhnf.insert e result }
    return result

def whnfCore (p : Program) (m : Metadata) : Nat → Ixon.Expr → CheckM Ixon.Expr
  | 0, _ => throw .budget
  | fuel + 1, e => do
    tick
    match e with
    | .share i => whnf p m fuel (← expansion p i)
    | .letE _ _ value body => whnf p m fuel (← substitute p fuel body value 0)
    | .ref i levels =>
      -- Unsafe/opaque source bodies do not become logical definitions just
      -- because the runtime profile supplies an external implementation.
      if m.kinds[i.toNat]? == some .opaqueDecl then return e
      match (← declaration p i).body with
      | some body => whnf p m fuel (← instantiateDeclaration p m fuel i levels body)
      | none => pure e
    | .prj owner field value =>
      let value ← whnf p m fuel value
      let (head, args) ← splitApp p fuel value []
      if let .ref c _ := head then
        if let some ctor := m.constructor? c then
          unless ctor.family == owner do
            throw (.unsupported "transport: projection constructor owner mismatch")
          if field.toNat < ctor.fields && args.length == ctor.params + ctor.fields then
            return ← whnf p m fuel args[ctor.params + field.toNat]!
      return .prj owner field value
    | .app fn arg =>
      let fn ← whnf p m fuel fn
      if let .lam _ _ body := fn then
        return ← whnf p m fuel (← substitute p fuel body arg 0)
      let rebuilt := .app fn arg
      let (head, args) ← splitApp p fuel rebuilt []
      let .ref i levels := head | return rebuilt
      let some recursor := m.recursor? i | return rebuilt
      let args := args.toArray
      if args.size ≤ recursor.major then return rebuilt
      let mut major ← whnf p m fuel args[recursor.major]!
      if let .nat payload := major then
        let some n := m.natural? payload
          | throw (.unsupported "transport: numeric payload metadata missing")
        major ← naturalConstructor p m fuel n
      let (ctorHead, ctorArgs) ← splitApp p fuel major []
      let .ref c _ := ctorHead | return rebuilt
      let some ctor := m.constructor? c | return rebuilt
      unless ctor.family == recursor.family do
        throw (.unsupported "transport: recursor constructor family mismatch")
      let some rule := recursor.rules[ctor.position]?
        | throw (.unsupported "transport: recursor rule missing")
      unless rule.fields == ctor.fields && ctorArgs.length == ctor.params + ctor.fields do
        throw (.unsupported "transport: recursor constructor arity mismatch")
      let leading := args.extract 0 (recursor.params + recursor.motives + recursor.minors)
      let fields := ctorArgs.toArray.extract ctor.params ctorArgs.length
      let trailing := args.extract (recursor.major + 1) args.size
      let rhs ← instantiateDeclaration p m fuel i levels rule.rhs
      whnf p m fuel (applyArgs rhs (leading ++ fields ++ trailing))
    | .recur .. => throw (.unsupported "transport: unresolved recursive reference")
    | _ => pure e

end

def arrow (p : Program) (m : Metadata) (fuel : Nat) (type : Ixon.Expr) :
    CheckM (BinderContract × ValueContract × Ixon.Expr × Ixon.Expr) := do
  match ← whnf p m fuel type with
  | .all c r a b => pure (c, r, a, b)
  | _ => throw (.unsupported "transport: expected a dependent arrow")

/-- Context-free conversion rules. Typed proof irrelevance and eta are
handled by the typing layer, which has the necessary local type context. -/
def structurallyCompatible (p : Program) (m : Metadata) :
    Nat → Ixon.Expr → Ixon.Expr → CheckM Bool
  | 0, _, _ => throw .budget
  | fuel + 1, left, right => do
    tick
    if left == right then return true
    let left ← whnf p m fuel left
    let right ← whnf p m fuel right
    if left == right then return true
    match left, right with
    | .all c r a b, .all c' r' a' b' =>
      return c == c' && r == r' && (← structurallyCompatible p m fuel a a') &&
        (← structurallyCompatible p m fuel b b')
    | .lam c a b, .lam c' a' b' =>
      return c == c' && (← structurallyCompatible p m fuel a a') &&
        (← structurallyCompatible p m fuel b b')
    | .app f a, .app g b =>
      return (← structurallyCompatible p m fuel f g) && (← structurallyCompatible p m fuel a b)
    | .prj t i v, .prj u j w =>
      return t == u && i == j && (← structurallyCompatible p m fuel v w)
    | .sort i, .sort j => universeEqual fuel i j
    | .ref i us, .ref j vs =>
      if i != j || us.size != vs.size then return false
      for (u, v) in us.zip vs do
        unless ← universeEqual fuel u v do return false
      return true
    | _, _ => return false

end Ix.Resource.Transport
end
