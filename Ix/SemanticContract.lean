module

public import Ix.Ixon
public import Ix.Compile.ExactKey

/-!
# Contracts inside the source expression pipeline

Resolved source occurrences are decorated before canonicalization. This
reserved metadata frame is an intermediate semantic node: its fields affect
equality, ordering, and compilation, and are consumed into Ixon v5 modes
(`AllMode`, `LetMode`, `FieldMode`, `DefAsserts`).
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
  | lam
  | all
  | letE
  | field
  | defAsserts
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A v5 semantic contract carried on a prepared source expression. Every value
represents a legal Ixon v5 mode with no side condition. -/
inductive Contract where
  | lam (input : Ixon.BinderMode)
  | all (mode : Ixon.AllMode)
  | letE (mode : Ixon.LetMode)
  | field (mode : Ixon.FieldMode)
  | defAsserts (asserts : Ixon.DefAsserts)
  deriving BEq, DecidableEq, Repr, Inhabited

def Contract.kind : Contract → Kind
  | .lam _ => .lam
  | .all _ => .all
  | .letE _ => .letE
  | .field _ => .field
  | .defAsserts _ => .defAsserts

def Contract.kindCode (contract : Contract) : Nat :=
  match contract.kind with
  | .lam => 0
  | .all => 1
  | .letE => 2
  | .field => 3
  | .defAsserts => 4

def Contract.code : Contract → Nat
  | .lam m => m.toCode.toNat
  | .all m => m.toCode.toNat
  | .letE m => m.toCode.toNat
  | .field m => m.toCode.toNat
  | .defAsserts a => a.toCode.toNat

def Contract.orderKey (contract : Contract) : Nat := contract.kindCode * 64 + contract.code

def Contract.metadata (contract : Contract) : Lean.MData :=
  ({} : Lean.MData) |>.setNat key 4
    |>.setNat `ix.contract.kind contract.kindCode
    |>.setNat `ix.contract.code contract.code

def Contract.attach (contract : Contract) (expr : Lean.Expr) : Lean.Expr :=
  .mdata contract.metadata expr

def Contract.isOrdinary : Contract → Bool
  | .lam m => m == .many
  | .all m => m == {}
  | .letE m => m == .value .many
  | .field m => m == .inherited
  | .defAsserts a => a == {}

def decode (kind code : Nat) : Except String Contract := do
  if code >= 256 then throw "reserved semantic contract bits"
  let b := code.toUInt8
  match kind with
  | 0 =>
    match Ixon.BinderMode.ofCode? b with
    | some m => pure (.lam m)
    | none => throw "reserved semantic contract bits"
  | 1 =>
    match Ixon.AllMode.ofCode? b with
    | some m => pure (.all m)
    | none => throw "reserved semantic contract bits"
  | 2 =>
    match Ixon.LetMode.ofCode? b with
    | some m => pure (.letE m)
    | none => throw "reserved semantic contract bits"
  | 3 =>
    match Ixon.FieldMode.ofCode? b with
    | some m => pure (.field m)
    | none => throw "reserved semantic contract bits"
  | 4 =>
    match Ixon.DefAsserts.ofCode? b with
    | some a => pure (.defAsserts a)
    | none => throw "reserved semantic contract bits"
  | _ => throw "invalid semantic contract kind"

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
  unless version == some 4 do throw "unsupported semantic contract version"
  let some kindValue := kind | throw "missing semantic contract kind"
  let some codeValue := code | throw "missing semantic contract code"
  decode kindValue codeValue

/-- Whether the frame sits directly on a node of its expected kind. -/
def Contract.attachedTo (contract : Contract) (source : Ix.Expr) : Bool :=
  match contract.kind, source with
  | .lam, .lam .. => true
  | .all, .forallE .. => true
  | .letE, .letE .. => true
  | .field, .forallE .. => true
  | .defAsserts, _ => true
  | _, _ => false

/-- The Ixon v5 binder-and-result mode of a `lam` or `all` contract frame, if applicable. -/
def Contract.toAllMode? : Contract → Option Ixon.AllMode
  | .lam input => some { input, result := .shared }
  | .all mode => some mode
  | _ => none

/-- The Ixon v5 let mode of a `letE` contract frame, if applicable. -/
def Contract.toLetMode? : Contract → Option Ixon.LetMode
  | .letE mode => some mode
  | _ => none

/-- The Ixon v5 constructor field mode of a `field` contract frame, if applicable. -/
def Contract.toFieldMode? : Contract → Option Ixon.FieldMode
  | .field mode => some mode
  | _ => none

/-- The Ixon v5 definition assertions of a `defAsserts` contract frame, if applicable. -/
def Contract.toDefAsserts? : Contract → Option Ixon.DefAsserts
  | .defAsserts asserts => some asserts
  | _ => none

/-- Every decoded `Contract` represents a valid Ixon v5 mode. -/
def Contract.validMode (_ : Contract) : Bool := true

/-- Whether the compiler lowers the frame: a valid v5 contract attached to its target node. -/
def Contract.admits (contract : Contract) (source : Ix.Expr) : Bool :=
  contract.validMode && contract.attachedTo source

/-- Lower a contract frame onto the node it annotates. A `lam`, `all`, `field`,
or `defAsserts` frame leaves the compiled expression unchanged (their modes live
in the record's binder-data section, constructor `fieldModes`, or definition
`asserts`); a `letE` frame writes its `LetMode` onto the compiled `Ixon.Expr.letE`. -/
def Contract.lower (contract : Contract) (source : Ix.Expr) (compiled : Ixon.Expr) :
    Except String Ixon.Expr :=
  if !contract.attachedTo source then
    .error "semantic contract is not attached to its original binder"
  else
    match contract with
    | .lam _ | .all _ | .field _ | .defAsserts _ => .ok compiled
    | .letE mode =>
      match compiled with
      | .letE nonDep _ ty val body => .ok (.letE nonDep mode ty val body)
      | _ => .error "semantic contract is not attached to its original binder"

/-- Extract `DefAsserts` from outer semantic metadata frames on a definition's type.
A theorem always carries default assertions (`{}`). -/
def defAsserts (kind : Ix.DefKind) (type : Ix.Expr) : Ixon.DefAsserts :=
  match kind with
  | .thm => {}
  | _ => go type
where
  go : Ix.Expr → Ixon.DefAsserts
    | .mdata d inner _ =>
      if hasMetadata d then
        match read d with
        | .ok (.defAsserts a) => a
        | _ => go inner
      else go inner
    | _ => {}

/-- Extract the `FieldModes` of a constructor with `numParams` parameters and
`numFields` fields from its decorated type expression. -/
def ctorFieldModes (numParams : Nat) (numFields : UInt64) (type : Ix.Expr) :
    Ixon.FieldModes numFields.toNat :=
  Ixon.FieldModes.ofArray (collectFields numFields.toNat .inherited #[] (skipParams numParams type))
where
  skipParams (rem : Nat) (e : Ix.Expr) : Ix.Expr :=
    match rem, e with
    | 0, e => e
    | n + 1, .mdata _ inner _ => skipParams (n + 1) inner
    | n + 1, .forallE _ _ body _ _ => skipParams n body
    | _ + 1, e => e
  collectFields (rem : Nat) (cur : Ixon.FieldMode) (acc : Array Ixon.FieldMode) :
      Ix.Expr → Array Ixon.FieldMode
    | .mdata d inner _ =>
      let cur' := if hasMetadata d then
          match read d with
          | .ok (.field m) => m
          | _ => cur
        else cur
      collectFields rem cur' acc inner
    | .forallE _ _ body _ _ =>
      match rem with
      | 0 => acc
      | n + 1 => collectFields n .inherited (acc.push cur) body
    | _ => acc

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
        unless contract.attachedTo inner do
          throw "semantic contract is not attached to its original binder"
        annotated := true
      stack := stack.push inner
    | _ => pure ()
  return annotated

def Contract.ixMetadata (contract : Contract) : Array (Ix.Name × Ix.DataValue) :=
  let key := Ix.Name.mkStr (Ix.Name.mkStr Ix.Name.mkAnon "ix") "contract"
  #[ (key, .ofNat 4),
     (Ix.Name.mkStr key "kind", .ofNat contract.kindCode),
     (Ix.Name.mkStr key "code", .ofNat contract.code) ]

end Ix.SemanticContract

end
