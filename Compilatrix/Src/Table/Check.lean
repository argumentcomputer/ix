import Compilatrix.Src.Pinned

/-! # Unfolding-table checks

Each check decides one untrusted proposal on the resolved declarations
(design note 01 §4.1). Equality is `Term.eqv`: syntactic, ignoring
contracts, modes and annotations. A check returns the entry it justifies or
a reason; `Table.Build` drops refused proposals with a `hint` diagnostic. -/

namespace Compilatrix.Src.Table

open Compilatrix.Ixon

/-- `param 0 … param (n-1)`. -/
def paramUnivs (n : Nat) : List Univ := (List.range n).map fun i => .var i.toUInt64

/-- `#(k-1) … #0`. -/
def boundVars (k : Nat) : List Term := (List.range k).reverse.map Term.var

def safeDefn? (p : Program) (c : CId) : Option (Nat × Term × Term) :=
  match p.decl? c with
  | some (.defn .defn .safe lvls type value) => some (lvls, type, value)
  | _ => none

/-- Match `app* (const Eq [l]) [B, lhs, rhs]` over the pinned `Eq`. -/
def eqApp? (p : Program) (t : Term) : Option (Term × Term × Term) :=
  match t.spine with
  | (.const c [_], #[(ty, _), (lhs, _), (rhs, _)]) =>
    if some c == p.known.eq then some (ty, lhs, rhs) else none
  | _ => none

/-- Peel exactly `k` leading Π binders. -/
def peelPis : Nat → Term → Option (List (Binder × Term) × Term)
  | 0, t => some ([], t)
  | k + 1, .pi b _ d t => do
    let (bs, body) ← peelPis k t
    return ((b, d) :: bs, body)
  | _ + 1, _ => none

/-! ## Binder wrappers

Lean's `eq_def` states its binders without the `autoParam`/`optParam`
wrappers the definition's type may carry. A wrapper is recognised by its
body, not its address: a safe definition whose value is exactly `λ _. #0` or
`λ _ _. #1`, so one δ step and β give its first argument, and the two domains
are definitionally equal (the bridge's R6 step takes that δ step). -/

/-- Arity of an identity-like wrapper definition. -/
def wrapperArity? (p : Program) (c : CId) : Option Nat :=
  match safeDefn? p c with
  | some (_, _, .lam _ _ (.var 0)) => some 1
  | some (_, _, .lam _ _ (.lam _ _ (.var 1))) => some 2
  | _ => none

/-- Contract an application node whose (already stripped) spine is a
wrapper applied to exactly its arity. -/
def contractWrapper (p : Program) (t : Term) : Term :=
  match t.spine with
  | (.const c _, args) =>
    match wrapperArity? p c, args[0]? with
    | some n, some (first, _) => if args.size == n then first else t
    | _, _ => t
  | _ => t

/-- Remove saturated wrapper applications everywhere, bottom-up. -/
def stripWrappers (p : Program) : Term → Term
  | .app f a m => contractWrapper p (.app (stripWrappers p f) (stripWrappers p a) m)
  | .lam b d t => .lam b (stripWrappers p d) (stripWrappers p t)
  | .pi b r d t => .pi b r (stripWrappers p d) (stripWrappers p t)
  | .letE c r ty v b => .letE c r (stripWrappers p ty) (stripWrappers p v) (stripWrappers p b)
  | .proj s i e => .proj s i (stripWrappers p e)
  | t => t

/-- Domain agreement of check 3: equal once binder wrappers are removed. -/
def domainEqv (p : Program) (a b : Term) : Bool :=
  a.eqv b || (stripWrappers p a).eqv (stripWrappers p b)

/-! ## `eqn` -/

/-- Check `eqn f thm` and build the entry body `λ xs. rhs` (§4.1, checks 1–5). -/
def checkEqn (p : Program) (f thm : CId) : Except String Resolve := do
  let some (n, tf, vf) := safeDefn? p f
    | throw "eqn: the subject is not a safe definition"
  let some (.defn .thm .safe n' tθ _) := p.decl? thm
    | throw "eqn: the equation is not a safe theorem"
  unless n == n' do throw "eqn: universe parameter counts differ"
  let (binders, body) := tθ.pis
  let some (b, lhs, rhs) := eqApp? p body
    | throw "eqn: the theorem is not a Π-telescope over Eq"
  let k := binders.size
  let expectedLhs := Term.mkApps (.const f (paramUnivs n))
    ((boundVars k).toArray.map (·, Mode.strict))
  unless lhs.eqv expectedLhs do
    throw "eqn: the left-hand side is not f applied to the bound variables in order"
  let some (fBinders, fBody) := peelPis k tf
    | throw "eqn: the subject's type has fewer binders than the equation"
  unless (fBinders.zip binders.toList).all (fun ((_, a), (_, a')) => domainEqv p a a') do
    throw "eqn: binder domains differ from the subject's type"
  unless domainEqv p fBody b do throw "eqn: the equation's type differs from the subject's result"
  unless vf.leanFragment do
    throw "eqn-drops-contracts: the subject's body carries written contracts"
  let body := binders.foldr (fun (bnd, dom) acc =>
    Term.lam { bnd with contract := {} } dom acc) rhs
  return .eqn thm body

/-! ## `csimp` -/

/-- Check `csimp f g thm`: `thm : @f = @g` exactly. The target's own
admissibility and acyclicity are checked by `Table.Build`. -/
def checkCsimp (p : Program) (f g thm : CId) : Except String Resolve := do
  let some (n, tf, _) := safeDefn? p f
    | throw "csimp: the subject is not a safe definition"
  let some (.defn .thm .safe n' tθ _) := p.decl? thm
    | throw "csimp: the theorem is not a safe theorem"
  unless n == n' do throw "csimp: universe parameter counts differ"
  unless g != f do throw "csimp: the target is the subject"
  let some (ty, lhs, rhs) := eqApp? p tθ
    | throw "csimp: the theorem is not an equation between constants"
  unless ty.eqv tf do throw "csimp: the equation's type is not the subject's type"
  unless lhs.eqv (.const f (paramUnivs n)) do throw "csimp: the left side is not @f"
  match rhs with
  | .const g' vs =>
    if g' == g then return .csimp g vs thm
    else throw "csimp: the right side is not @g"
  | _ => throw "csimp: the right side is not a constant"

/-! ## `case` -/

/-- IH count of a recursor rule: its `rhs` is `λ ps motives minors fields.
app* #minor (fields ++ ihs)`. -/
def ruleIhs (np nmot nmin j : Nat) (rule : Rule) : Option Nat :=
  let (binders, body) := rule.rhs.lams
  let total := np + nmot + nmin + rule.fields
  if binders.size != total then none else
  let (head, args) := body.spine
  -- The minor for rule `j` is binder `np + nmot + j`.
  match head with
  | .var i =>
    if i == total - 1 - (np + nmot + j) && args.size ≥ rule.fields then
      some (args.size - rule.fields)
    else none
  | _ => none

/-- Check `case T` with key `T.casesOn` (§4.1). Returns the recursor. -/
def checkCase (p : Program) (key : CId) : Except String Resolve := do
  let some (n, _, value) := safeDefn? p key
    | throw "case: the key is not a safe definition"
  let (binders, body) := value.lams
  let (head, args) := body.spine
  let .const r us := head | throw "case: the body is not a recursor spine"
  let some (.recr _ _ rl np nmot nmin ni _ rules _) := p.decl? r
    | throw "case: the head is not a recursor"
  unless nmot == 1 do throw "case: mutual casesOn stays on δ"
  unless rl == n && us == paramUnivs n do throw "case: recursor levels are not the key's"
  unless rules.size == nmin do throw "case: rules and minors differ"
  let m := nmin
  let total := np + 1 + ni + 1 + m
  unless binders.size == total do throw "case: wrong binder count"
  unless args.size == total do throw "case: wrong argument count"
  let bvar := fun (q : Nat) => Term.var (total - 1 - q)
  let argAt := fun (i : Nat) => (args[i]?.map (·.1)).getD (.natLit 0)
  for i in [0:np] do
    unless (argAt i).eqv (bvar i) do throw s!"case: parameter {i} out of place"
  unless (argAt np).eqv (bvar np) do throw "case: motive out of place"
  for i in [0:ni] do
    unless (argAt (np + 1 + m + i)).eqv (bvar (np + 1 + i)) do
      throw s!"case: index {i} out of place"
  unless (argAt (np + 1 + m + ni)).eqv (bvar (np + 1 + ni)) do
    throw "case: major out of place"
  for j in [0:m] do
    let some rule := rules[j]? | throw "case: missing rule"
    let some ihs := ruleIhs np 1 m j rule | throw s!"case: rule {j} has no minor-application shape"
    let f := rule.fields
    let (wBinders, wBody) := (argAt (np + 1 + j)).lams
    unless wBinders.size == f + ihs do throw s!"case: minor wrapper {j} has the wrong arity"
    let minorIdx := (total - 1 - (np + 1 + ni + 1 + j)) + f + ihs
    let expected := Term.mkApps (.var minorIdx)
      ((List.range f).toArray.map fun i => (Term.var (f + ihs - 1 - i), Mode.strict))
    unless wBody.eqv expected do throw s!"case: minor wrapper {j} is not the minor on its fields"
  return .case r

/-! ## `lazy`, `inline`, `prim` -/

def checkLazy (p : Program) (f : CId) (arity : Nat) : Except String Unit := do
  let some (_, _, value) := safeDefn? p f | throw "lazy: not a safe definition"
  unless arity ≥ 1 && value.lamCount ≥ arity do throw "lazy: too few leading λs"

def checkInline (p : Program) (f : CId) (cap : Nat) : Except String Unit := do
  let some (_, _, value) := safeDefn? p f | throw "inline: not a safe definition"
  if value.mentions f then throw "inline: self-referential"
  unless value.nodes ≤ cap do throw "inline: over the size cap"

/-- `Nat → Nat → Nat`, `Nat → Nat → Bool` or `Nat → Nat` over the pinned
types, by the operation's arity and result. -/
def checkPrim (p : Program) (f : CId) (op : PrimOp) (enabled : List PrimOp) :
    Except String Unit := do
  unless enabled.contains op do throw s!"prim: {op.name} is not in the configured set"
  unless Pinned.primAddr op == p.addr f do throw "prim: the address is not the pinned one"
  let some natId := p.known.nat | throw "prim: Nat is absent"
  let nat := Term.const natId []
  let result ← if op.isPredicate then
      match p.known.bool with
      | some b => pure (Term.const b [])
      | none => throw "prim: Bool is absent"
    else pure nat
  let expected := if op.arity == 1 then Term.pi {} {} nat result
    else Term.pi {} {} nat (Term.pi {} {} nat result)
  let some d := p.decl? f | throw "prim: missing declaration"
  unless d.type.eqv expected do throw s!"prim: {op.name} does not have the primitive type"

/-! ## Derived `RecKind` -/

/-- Whether a type is a Π-telescope ending syntactically in `sort zero`. -/
def endsInProp (t : Term) : Bool :=
  match t.pis.2 with
  | .sort .zero => true
  | _ => false

/-- Derive a recursor's kind (§4.1): `empty` with no rules; `subsingleton`
for a single-rule recursor of a family whose type ends in `sort zero`, with
each field read from the constructor index that is exactly that field, or a
proof; `ordinary` otherwise. -/
def deriveRecKind (p : Program) (r : CId) : Option RecKind := do
  let .recr _ _ _ _ _ _ _ ind rules _ ← p.decl? r | none
  if rules.isEmpty then return .empty
  let .induct _ _ _ _ indTy _ ← p.decl? ind | none
  unless endsInProp indTy && rules.size == 1 do return .ordinary
  let rule ← rules[0]?
  let .ctor _ _ _ _ np nf ctorTy ← p.decl? rule.ctor | none
  let (_, result) := ctorTy.pis
  let resultArgs := result.spine.2.map (·.1)
  let indices := resultArgs.extract np resultArgs.size
  let fields := (Array.range nf).map fun j =>
    match indices.findIdx? (·.eqv (.var (nf - 1 - j))) with
    | some i => FieldSrc.index i
    | none => FieldSrc.proof
  return .subsingleton fields

end Compilatrix.Src.Table
