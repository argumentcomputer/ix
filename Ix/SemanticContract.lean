module

public import Ix.Ixon
public import Ix.Compile.ExactKey

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

/-- Whether the frame sits directly on a binder of its kind. -/
def Contract.attachedTo (contract : Contract) (source : Ix.Expr) : Bool :=
  match contract.kind, source with
  | .lam, .lam .. => true
  | .all, .forallE .. => true
  | .letE, .letE .. => true
  | _, _ => false

/-- Convert a surface value contract to an Ixon v5 result mode. -/
def toResultMode (v : Ixon.ValueContract) : Ixon.ResultMode :=
  match v.owned, v.locality with
  | .shared, .unrestricted => .shared
  | .shared, .local => .borrowed
  | .unique, .unrestricted => .unique
  | .unique, .local => .uniqueBorrowed

/-- Convert a surface binder contract to an Ixon v5 binder mode, if representable.
Erased binders carry no ownership or local lifetime in v5. -/
def toBinderMode? (b : Ixon.BinderContract) : Option Ixon.BinderMode :=
  if b.uses == .erased then
    if b.value == .shared then some .erased else none
  else
    match b.value.owned, b.value.locality, b.uses with
    | .unique, .unrestricted, _ => some .unique
    | .unique, .local, _ => some .uniqueBorrowed
    | .shared, .unrestricted, .many => some .many
    | .shared, .local, .many => some .borrowed
    | .shared, .unrestricted, .linear | .shared, .unrestricted, .affine => some .once
    | .shared, .local, .linear | .shared, .local, .affine => some .onceBorrowed
    | _, _, _ => none

/-- The Ixon v5 binder-and-result mode of a `lam` or `all` contract frame, if valid. -/
def Contract.toAllMode? (contract : Contract) : Option Ixon.AllMode := do
  return { input := ← toBinderMode? contract.binder, result := toResultMode contract.result }

/-- The Ixon v5 let mode of a `letE` contract frame, if valid. -/
def Contract.toLetMode? (contract : Contract) : Option Ixon.LetMode :=
  if contract.letKind == .borrowShared then
    if contract.binder.uses != .erased && contract.binder.value == .localShared then
      some .borrow
    else none
  else
    Ixon.LetMode.value <$> toBinderMode? contract.binder

/-- Whether the contract frame represents a valid Ixon v5 mode for its binder kind. -/
def Contract.validMode (contract : Contract) : Bool :=
  match contract.kind with
  | .lam | .all => contract.toAllMode?.isSome
  | .letE => contract.toLetMode?.isSome

/-- Whether the compiler lowers the frame: a valid v5 contract on a binder of
its kind. -/
def Contract.admits (contract : Contract) (source : Ix.Expr) : Bool :=
  contract.validMode && contract.attachedTo source

/-- Lower a contract frame onto the binder it annotates. A `lam` or `all` frame
leaves the compiled binder term unchanged (its `AllMode` is written into the
record's binder-data section); a `letE` frame writes its `LetMode` onto the
compiled `Ixon.Expr.letE`. -/
def Contract.lower (contract : Contract) (source : Ix.Expr) (compiled : Ixon.Expr) :
    Except String Ixon.Expr :=
  if !contract.attachedTo source then
    .error "semantic contract is not attached to its original binder"
  else
    match contract.kind with
    | .lam | .all =>
      if contract.toAllMode?.isSome then .ok compiled
      else .error "unsupported semantic contract mode"
    | .letE =>
      match contract.toLetMode? with
      | none => .error "unsupported semantic contract mode"
      | some mode =>
        match compiled with
        | .letE nonDep _ ty val body => .ok (.letE nonDep mode ty val body)
        | _ => .error "semantic contract is not attached to its original binder"

/-- Inspect an entire source expression before rewrites can remove subterms. -/
def inspect (top : Ix.Expr) : Except String Bool := do
  let mut seen : Std.HashSet Ix.Compile.ExactKey.ExprKey := {}
  let mut stack := #[top]
  let mut annotated := false
  while !stack.isEmpty do
    let e := stack.back!
    stack := stack.pop
    if seen.contains ⟨e⟩ then continue
    seen := seen.insert ⟨e⟩
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
        unless contract.validMode do throw "unsupported semantic contract mode"
        annotated := true
      stack := stack.push inner
    | _ => pure ()
  return annotated

def Contract.ixMetadata (contract : Contract) : Array (Ix.Name × Ix.DataValue) :=
  let key := Ix.Name.mkStr (Ix.Name.mkStr Ix.Name.mkAnon "ix") "contract"
  #[ (key, .ofNat 3),
     (Ix.Name.mkStr key "kind", .ofNat contract.kindCode),
     (Ix.Name.mkStr key "code", .ofNat contract.code) ]

end Ix.SemanticContract

end
