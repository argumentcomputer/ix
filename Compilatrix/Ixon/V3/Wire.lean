import Ix.Ixon.Canonical
import Compilatrix.Ixon.V4.Convert

/-!
# The Ixon v4 wire for our Ixon data

Canonical bytes of universes, expressions and constants are ix's Ixon v4
encodings (`Ix.Ixon.Codec`, TagN integers), computed through the structural
correspondence of `Compilatrix.Ixon.V4.Convert`. Decoding uses ix's bounded,
canonical constant decoder (`Ixon.Canonical.deConstant`: an input-byte and
universe-expansion budget, the wire domain check, and re-encoding to exactly
the supplied bytes), then the consumer budgets below, and keeps the
canonicality of the converted value as evidence (`constantBytes value =
bytes`), as the v3 decoder did.

The names (`exprBytes`, `constantBytes`, `decodeExpr`, `decodeConstant`) are
those of the retired v3 codec, so every consumer (erased typing, ingress,
resource admission, projection addresses) reads and commits to v4 bytes.
-/

namespace Compilatrix.Ixon.V3

open Compilatrix.Ixon

def wireFormatId : String := _root_.Ixon.wireFormatId

def univBytes (u : Univ) : ByteArray := _root_.Ixon.serUniv (V4.univToIx u)

def exprBytes (e : Expr) : ByteArray := _root_.Ixon.serExpr (V4.exprToIx e)

def constantBytes (c : Constant) : ByteArray := _root_.Ixon.serConstant (V4.constantToIx c)

/-! ## Consumer budgets

The limits the strict v3 decoder enforced while reading, now checked on the
decoded value: at most 4,096 entries in any counted list, expression depth
256 (a `share` node is a leaf), and the byte budget of each object. -/

def countLimit : Nat := 4096

def exprDepthLimit : Nat := 256

/-- Aggregate expanded universe constructors per constant (ix's bounded
decoder charges succ chains by their length). -/
def univNodeLimit : Nat := 65536

def Expr.withinCounts : Expr → Bool
  | .ref _ levels | .recur _ levels => levels.size ≤ countLimit
  | .prj _ _ e => e.withinCounts
  | .app f a => f.withinCounts && a.withinCounts
  | .lam _ t b | .all _ _ t b => t.withinCounts && b.withinCounts
  | .letE _ t v b => t.withinCounts && v.withinCounts && b.withinCounts
  | _ => true

def Expr.withinBudget (e : Expr) : Bool :=
  e.withinDepth exprDepthLimit && e.withinCounts

def Constant.withinBudget (c : Constant) : Bool :=
  let infoCounts := match c.info with
    | .muts ms => ms.size ≤ countLimit && ms.all fun
        | .indc i => i.ctors.size ≤ countLimit
        | .recr r => r.rules.size ≤ countLimit
        | .defn _ => true
    | .recr r => r.rules.size ≤ countLimit
    | _ => true
  infoCounts && c.sharing.size ≤ countLimit && c.refs.size ≤ countLimit &&
    c.univs.size ≤ countLimit &&
    (c.info.exprs ++ c.sharing.toList).all Expr.withinBudget

/-! ## Decoding with canonicality evidence -/

/-- Full-object canonicality is retained as evidence rather than trusting a
decoded value to stand for the bytes that supplied it. -/
structure DecodedExpr (bytes : ByteArray) where
  value : Expr
  canonical : exprBytes value = bytes

def decodeExpr (bytes : ByteArray) (maxBytes : Nat := 1024 * 1024)
    (depth : Nat := exprDepthLimit) : Except String (DecodedExpr bytes) := do
  if bytes.size > maxBytes then throw "ixon-v4: expression byte budget exceeded"
  let value := V4.exprOfIx (← _root_.Ixon.deExpr bytes)
  unless value.withinDepth depth && value.withinCounts do
    throw "ixon-v4: expression exceeds the consumer budget"
  if canonical : exprBytes value = bytes then return ⟨value, canonical⟩
  else throw "ixon-v4: noncanonical expression"

structure DecodedConstant (bytes : ByteArray) where
  value : Constant
  canonical : constantBytes value = bytes

def decodeConstant (bytes : ByteArray) (maxBytes : Nat := 1024 * 1024) :
    Except String (DecodedConstant bytes) := do
  if bytes.size > maxBytes then throw "ixon-v4: constant byte budget exceeded"
  let decoded ← _root_.Ixon.Canonical.deConstant maxBytes univNodeLimit bytes
  let value ← V4.constantOfIx decoded
  unless value.withinBudget do throw "ixon-v4: constant exceeds the consumer budget"
  if canonical : constantBytes value = bytes then return ⟨value, canonical⟩
  else throw "ixon-v4: noncanonical constant"

end Compilatrix.Ixon.V3
