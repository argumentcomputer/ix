import Compilatrix.Ixon.Expr
import Compilatrix.Ixon.V3.Contracts

/-! Ixon v3 expressions retain all committed source contracts. Byte framing
uses the existing canonical tag primitives; the v2 expression decoder is not
used to interpret v3 mode bytes. The published ix fixture corpus supplies an
independent wire oracle. -/

namespace Compilatrix.Ixon.V3

def wireFormatId : String := "ixon-v3"
def upstreamRevision : String := "2afb4eac340cd4cbe94ed9e507561f3ad8375ebd"

inductive Expr where
  | sort : UInt64 → Expr
  | var : UInt64 → Expr
  | ref : UInt64 → Array UInt64 → Expr
  | recur : UInt64 → Array UInt64 → Expr
  | prj : UInt64 → UInt64 → Expr → Expr
  | str : UInt64 → Expr
  | nat : UInt64 → Expr
  | app : Expr → Expr → Expr
  | lam : BinderContract → Expr → Expr → Expr
  | all : BinderContract → ValueContract → Expr → Expr → Expr
  | letE : LetContract → Expr → Expr → Expr → Expr
  | share : UInt64 → Expr
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace Expr

def codecSize : Expr → Nat
  | .sort _ | .var _ | .ref _ _ | .recur _ _ | .str _ | .nat _ | .share _ => 1
  | .prj _ _ e => e.codecSize + 1
  | .app f a => f.codecSize + a.codecSize + 1
  | .lam _ d b | .all _ _ d b => d.codecSize + b.codecSize + 1
  | .letE _ t v b => t.codecSize + v.codecSize + b.codecSize + 1

/-- Wire telescopes can contain many AST binders at one parser depth.
Check semantic depth with bounded recursion before canonical reencoding. -/
def withinDepth : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e => match e with
    | .prj _ _ e => withinDepth fuel e
    | .app f a => withinDepth fuel f && withinDepth fuel a
    | .lam _ t b | .all _ _ t b => withinDepth fuel t && withinDepth fuel b
    | .letE _ t v b => withinDepth fuel t && withinDepth fuel v && withinDepth fuel b
    | _ => true

def appCount : Expr → Nat
  | .app f _ => f.appCount + 1
  | _ => 0

def lamCount : Expr → Nat
  | .lam _ _ b => b.lamCount + 1
  | _ => 0

def allCount : Expr → Nat
  | .all _ _ _ b => b.allCount + 1
  | _ => 0

/-- Ordinary source has many/shared/unrestricted inputs and results, with
ordinary lets. An erased/implicit binder is not inferred from its position. -/
def leanFragment : Expr → Bool
  | .lam c d b => c == .many && leanFragment d && leanFragment b
  | .all c r d b => c == .many && r == .shared && leanFragment d && leanFragment b
  | .letE c t v b => c.kind == .value && c.binder == .many &&
      leanFragment t && leanFragment v && leanFragment b
  | .app f a => leanFragment f && leanFragment a
  | .prj _ _ e => leanFragment e
  | _ => true

def collectLam : Expr → List (BinderContract × Expr) × Expr
  | .lam c t b =>
    let (binders, body) := collectLam b
    ((c, t) :: binders, body)
  | e => ([], e)

end Expr

mutual
  def exprBytes : Expr → ByteArray
    | .sort i => tag4Bytes ⟨0, i⟩
    | .var i => tag4Bytes ⟨1, i⟩
    | .ref i levels => tag4Bytes ⟨2, levels.size.toUInt64⟩ ++
        tag0Bytes ⟨i⟩ ++ tag0ListBytes levels.toList
    | .recur i levels => tag4Bytes ⟨3, levels.size.toUInt64⟩ ++
        tag0Bytes ⟨i⟩ ++ tag0ListBytes levels.toList
    | .prj i field value => tag4Bytes ⟨4, field⟩ ++ tag0Bytes ⟨i⟩ ++ exprBytes value
    | .str i => tag4Bytes ⟨5, i⟩
    | .nat i => tag4Bytes ⟨6, i⟩
    | .app f a => tag4Bytes ⟨7, (f.appCount + 1).toUInt64⟩ ++
        appSpineBytes f ++ exprBytes a
    | .lam c t b => tag4Bytes ⟨8, (b.lamCount + 1).toUInt64⟩ ++
        u8Bytes c.toBits ++ exprBytes t ++ lamTailBytes b
    | .all c r t b => tag4Bytes ⟨9, (b.allCount + 1).toUInt64⟩ ++
        u8Bytes (packAllContract c r) ++ exprBytes t ++ allTailBytes b
    | .letE c t v b => tag4Bytes ⟨10, c.flags⟩ ++ u8Bytes c.binder.toBits ++
        exprBytes t ++ exprBytes v ++ exprBytes b
    | .share i => tag4Bytes ⟨11, i⟩
  termination_by e => (e.codecSize, 0)
  decreasing_by
    all_goals apply Prod.Lex.left <;> simp [Expr.codecSize] <;> omega

  def appSpineBytes : Expr → ByteArray
    | .app f a => appSpineBytes f ++ exprBytes a
    | e => exprBytes e
  termination_by e => (e.codecSize, 1)
  decreasing_by
    all_goals first
      | apply Prod.Lex.left <;> simp [Expr.codecSize] <;> omega
      | apply Prod.Lex.right <;> omega

  def lamTailBytes : Expr → ByteArray
    | .lam c t b => u8Bytes c.toBits ++ exprBytes t ++ lamTailBytes b
    | e => exprBytes e
  termination_by e => (e.codecSize, 1)
  decreasing_by
    all_goals first
      | apply Prod.Lex.left <;> simp [Expr.codecSize] <;> omega
      | apply Prod.Lex.right <;> omega

  def allTailBytes : Expr → ByteArray
    | .all c r t b => u8Bytes (packAllContract c r) ++ exprBytes t ++ allTailBytes b
    | e => exprBytes e
  termination_by e => (e.codecSize, 1)
  decreasing_by
    all_goals first
      | apply Prod.Lex.left <;> simp [Expr.codecSize] <;> omega
      | apply Prod.Lex.right <;> omega
end

def getBinder : GetM BinderContract := do
  let byte ← getU8
  match BinderContract.ofBits? byte with
  | some contract => return contract
  | none => throw s!"ixon-v3: invalid binder contract {byte}"

def getAllContract : GetM (BinderContract × ValueContract) := do
  let byte ← getU8
  match unpackAllContract? byte with
  | some contract => return contract
  | none => throw s!"ixon-v3: invalid arrow contract {byte}"

/-- Reject impossible counted lists before recursion or preallocation. Every
entry in these lists consumes at least one byte. -/
def checkedCount (count : UInt64) (bound : Nat) : GetM Nat := do
  let state ← get
  let count := count.toNat
  if count > bound || count > state.bytes.size - state.idx then
    throw "ixon-v3: count exceeds decoder budget or remaining bytes"
  return count

def getAppRun (recur : GetM Expr) (count : Nat) : GetM Expr := do
  if count == 0 then throw "ixon-v3: empty application spine"
  let mut result ← recur
  if let .app .. := result then throw "ixon-v3: nonmaximal application spine"
  for _ in [:count] do result := .app result (← recur)
  return result

def getLamRun (recur : GetM Expr) (count : Nat) : GetM Expr := do
  if count == 0 then throw "ixon-v3: empty lambda telescope"
  let mut binders := #[]
  for _ in [:count] do
    let contract ← getBinder
    binders := binders.push (contract, ← recur)
  let body ← recur
  if let .lam .. := body then throw "ixon-v3: nonmaximal lambda telescope"
  return binders.foldr (fun (c, t) b => .lam c t b) body

def getAllRun (recur : GetM Expr) (count : Nat) : GetM Expr := do
  if count == 0 then throw "ixon-v3: empty forall telescope"
  let mut binders := #[]
  for _ in [:count] do
    let (input, result) ← getAllContract
    binders := binders.push (input, result, ← recur)
  let body ← recur
  if let .all .. := body then throw "ixon-v3: nonmaximal forall telescope"
  return binders.foldr (fun (c, r, t) b => .all c r t b) body

def getExprFuel : Nat → GetM Expr
  | 0 => throw "ixon-v3: expression depth budget exhausted"
  | fuel + 1 => do
    let tag ← getTag4
    let recur := getExprFuel fuel
    match tag.flag with
    | 0 => return .sort tag.size
    | 1 => return .var tag.size
    | 2 | 3 =>
      let index := (← getTag0).size
      let count ← checkedCount tag.size 4096
      let levels := (← getTag0List count).toArray
      return if tag.flag == 2 then .ref index levels else .recur index levels
    | 4 => return .prj (← getTag0).size tag.size (← recur)
    | 5 => return .str tag.size
    | 6 => return .nat tag.size
    | 7 => getAppRun recur (← checkedCount tag.size (fuel + 1))
    | 8 => getLamRun recur (← checkedCount tag.size (fuel + 1))
    | 9 => getAllRun recur (← checkedCount tag.size (fuel + 1))
    | 10 =>
      if tag.size > 3 then throw "ixon-v3: invalid let flags"
      let binder ← getBinder
      let some contract := LetContract.ofFlags? tag.size binder
        | throw "ixon-v3: invalid let contract"
      let type ← recur
      let value ← recur
      return .letE contract type value (← recur)
    | 11 => return .share tag.size
    | _ => throw "ixon-v3: invalid expression tag"

def getExpr : GetM Expr := do
  let value ← getExprFuel 256
  unless value.withinDepth 256 do throw "ixon-v3: expanded expression depth exceeded"
  return value

instance : Serialize Expr where
  put e := putBytes (exprBytes e)
  get := getExpr

/-- Full-object canonicality is retained as evidence rather than trusting a
decoded value to stand for the bytes that supplied it. -/
structure DecodedExpr (bytes : ByteArray) where
  value : Expr
  canonical : exprBytes value = bytes

def decodeExpr (bytes : ByteArray) (maxBytes : Nat := 1024 * 1024)
    (depth : Nat := 256) : Except String (DecodedExpr bytes) := do
  if bytes.size > maxBytes then throw "ixon-v3: expression byte budget exceeded"
  let value ← runGet (getExprFuel depth) bytes
  unless value.withinDepth depth do throw "ixon-v3: expanded expression depth exceeded"
  if canonical : exprBytes value = bytes then return ⟨value, canonical⟩
  else throw "ixon-v3: noncanonical expression"

end Compilatrix.Ixon.V3
