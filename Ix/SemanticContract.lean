module

public import Ix.Ixon

/-!
# Contracts inside the source expression pipeline

Resolved source occurrences are decorated before canonicalization. This
reserved metadata frame is an intermediate semantic node: its fields affect
equality, ordering, and compilation, and are consumed into the Ixon binder.
It is never an optional presentation hint or a resource-validity certificate.
-/

@[expose] public section

namespace Ix.SemanticContract

def key : Lean.Name := `ix.contract

def toLeanName : Ix.Name → Lean.Name
  | .anonymous _ => .anonymous
  | .str parent text _ => .str (toLeanName parent) text
  | .num parent index _ => .num (toLeanName parent) index

def reserved (name : Ix.Name) : Bool := key.isPrefixOf (toLeanName name)

def hasMetadata (data : Array (Ix.Name × Ix.DataValue)) : Bool :=
  data.any fun (name, _) => reserved name

def leanFields (data : Lean.MData) : List (Lean.Name × Lean.DataValue) :=
  data.entries.filter fun (name, _) => key.isPrefixOf name

inductive Kind where
  | lam | all | letE
  deriving BEq, Repr, Inhabited

structure Contract where
  kind : Kind
  binder : Ixon.BinderContract
  result : Ixon.ValueContract := .shared
  letKind : Ixon.LetKind := .value
  deriving BEq, Repr, Inhabited

def Contract.kindCode (contract : Contract) : Nat :=
  match contract.kind with | .lam => 0 | .all => 1 | .letE => 2

def Contract.code (contract : Contract) : Nat :=
  match contract.kind with
  | .lam => contract.binder.toBits.toNat
  | .all => (Ixon.packAllContract contract.binder contract.result).toNat
  | .letE => contract.binder.toBits.toNat + (if contract.letKind == .borrowShared then 16 else 0)

def Contract.orderKey (contract : Contract) : Nat := contract.kindCode * 64 + contract.code

def Contract.metadata (contract : Contract) : Lean.MData :=
  ({} : Lean.MData) |>.setNat key 3
    |>.setNat `ix.contract.kind contract.kindCode
    |>.setNat `ix.contract.code contract.code

def Contract.attach (contract : Contract) (expr : Lean.Expr) : Lean.Expr :=
  .mdata contract.metadata expr

def Contract.isOrdinary (contract : Contract) : Bool :=
  contract.binder == .many && contract.result == .shared && contract.letKind == .value

def decode (kind code : Nat) : Except String Contract := do
  let k ← match kind with
    | 0 => pure Kind.lam | 1 => pure Kind.all | 2 => pure Kind.letE
    | _ => throw "invalid semantic contract kind"
  let limit := match k with | .lam => 16 | .all => 64 | .letE => 32
  if code >= limit then throw "reserved semantic contract bits"
  let some binder := Ixon.BinderContract.ofBits? (code % 16).toUInt8
    | throw "invalid semantic binder contract"
  let result ← if k == .all then do
    let some result := Ixon.ValueContract.ofBits? (code / 16).toUInt8
      | throw "invalid semantic result contract"
    pure result
  else pure .shared
  let letKind := if k == .letE && code >= 16 then Ixon.LetKind.borrowShared else .value
  if letKind == .borrowShared && binder.value != .localShared then
    throw "shared borrow requires a shared local view"
  return { kind := k, binder, result, letKind }

/-- A semantic frame has exactly these three fields. Other metadata may wrap
it in separate frames, keeping native Lean hints independent. -/
def read (data : Array (Ix.Name × Ix.DataValue)) : Except String Contract := do
  if data.size != 3 then throw "malformed semantic contract frame"
  let mut version : Option Nat := none
  let mut kind : Option Nat := none
  let mut code : Option Nat := none
  for (name, value) in data do
    let .ofNat value := value | throw "semantic contract fields must be natural numbers"
    let name := toLeanName name
    if name == key && version.isNone then version := some value
    else if name == `ix.contract.kind && kind.isNone then kind := some value
    else if name == `ix.contract.code && code.isNone then code := some value
    else throw "unknown or duplicate semantic contract field"
  unless version == some 3 do throw "unsupported semantic contract version"
  let some kindValue := kind | throw "missing semantic contract kind"
  let some codeValue := code | throw "missing semantic contract code"
  decode kindValue codeValue

def Contract.lower (contract : Contract) (source : Ix.Expr) (compiled : Ixon.Expr) :
    Except String Ixon.Expr := do
  match contract.kind, source, compiled with
  | .lam, .lam .., .lam _ type body => return .lam contract.binder type body
  | .all, .forallE .., .all _ _ type body => return .all contract.binder contract.result type body
  | .letE, .letE .., .letE c type value body =>
    return .letE { c with binder := contract.binder, kind := contract.letKind } type value body
  | _, _, _ => throw "semantic contract is not attached to its original binder"

/-- Inspect an entire source expression before rewrites can remove subterms. -/
def inspect (top : Ix.Expr) : Except String Bool := do
  let mut seen : Std.HashSet Ix.Expr := {}
  let mut stack := #[top]
  let mut annotated := false
  while !stack.isEmpty do
    let e := stack.back!
    stack := stack.pop
    if seen.contains e then continue
    seen := seen.insert e
    match e with
    | .app fn arg _ => stack := stack.push fn |>.push arg
    | .lam _ type body _ _ | .forallE _ type body _ _ =>
      stack := stack.push type |>.push body
    | .letE _ type value body _ _ => stack := stack.push type |>.push value |>.push body
    | .proj _ _ value _ => stack := stack.push value
    | .mdata data inner _ =>
      if hasMetadata data then
        let contract ← read data
        let valid := match contract.kind, inner with
          | .lam, .lam .. | .all, .forallE .. | .letE, .letE .. => true
          | _, _ => false
        unless valid do throw "semantic contract is not attached to its original binder"
        annotated := true
      stack := stack.push inner
    | _ => pure ()
  return annotated

/-- Reconstruct only committed binder fields; optional metadata cannot
supply or replace semantic contracts. -/
def ofIxon? : Ixon.Expr → Option Contract
  | .lam binder _ _ =>
    if binder == .many then none else some { kind := .lam, binder }
  | .all binder result _ _ =>
    if binder == .many && result == .shared then none
    else some { kind := .all, binder, result }
  | .letE c _ _ _ =>
    if c.binder == .many && c.kind == .value then none
    else some { kind := .letE, binder := c.binder, letKind := c.kind }
  | _ => none

def Contract.ixMetadata (contract : Contract) : Array (Ix.Name × Ix.DataValue) :=
  let key := Ix.Name.mkStr (Ix.Name.mkStr Ix.Name.mkAnon "ix") "contract"
  #[ (key, .ofNat 3),
     (Ix.Name.mkStr key "kind", .ofNat contract.kindCode),
     (Ix.Name.mkStr key "code", .ofNat contract.code) ]

/-- Read-only presence scan used to reject optional structural rewrites that
would remove contracts, including contracts hidden behind sharing. -/
def containsIxon (sharing : Array Ixon.Expr) (top : Ixon.Expr) : Except String Bool := do
  let mut seen : Std.HashSet Ixon.Expr := {}
  let mut stack := #[top]
  while !stack.isEmpty do
    let e := stack.back!
    stack := stack.pop
    if seen.contains e then continue
    seen := seen.insert e
    if (ofIxon? e).isSome then return true
    match e with
    | .share index =>
      let some value := sharing[index.toNat]? | throw "semantic scan: invalid sharing index"
      stack := stack.push value
    | .app f a => stack := stack.push f |>.push a
    | .lam _ t b | .all _ _ t b => stack := stack.push t |>.push b
    | .letE _ t v b => stack := stack.push t |>.push v |>.push b
    | .prj _ _ v => stack := stack.push v
    | _ => pure ()
  return false

end Ix.SemanticContract

end
