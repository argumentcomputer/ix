import IxCK.Ixon.Canonical
import IxCC.Ixon.V4.Convert
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# The Ixon v4 wire for our Ixon data

Canonical bytes of universes, expressions and constants are ix's Ixon v4
encodings (`IxCK.Ixon.Codec`, TagN integers), computed through the structural
correspondence of `IxCC.Ixon.V4.Convert`. Decoding uses ix's bounded,
canonical constant decoder (`Ixon.Canonical.deConstant`: an input-byte and
universe-expansion budget, the wire domain check, and re-encoding to exactly
the supplied bytes), then the consumer budgets below, and keeps the
canonicality of the converted value as evidence (`constantBytes value =
bytes`), as the v3 decoder did.

The names (`exprBytes`, `constantBytes`, `decodeExpr`, `decodeConstant`) are
those of the retired v3 codec, so every consumer (ingress, resource
admission, projection addresses) reads and commits to v4 bytes.
-/

namespace IxCC.Ixon.V3

open IxCC.Ixon

def wireFormatId : String := _root_.Ixon.wireFormatId

def univBytes (u : Univ) : ByteArray := _root_.Ixon.serUniv (V4.univToIx u)

def exprBytes (e : Expr) : ByteArray := _root_.Ixon.serExpr (V4.exprToIx e)

def constantBytes (c : Constant) : ByteArray := _root_.Ixon.serConstant (V4.constantToIx c)

/-! ## Consumer budgets

The limits the strict v3 decoder enforced while reading, now checked on the
decoded value: at most 4,096 entries in any counted list, expression depth
256 (a `share` node is a leaf), and the byte budget of each object. They are
IxCC's own limits on what it reads: ingress applies them to the records the
seeds reach (`Src.Ingress.reach`), not to every record of an artifact; the
envelope (`decodeAnonymousEnv`) checks every record with the kernel's
canonical decoder only. -/

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

/-- The counts of a constant's payload: its block's members, an inductive's
constructors, a recursor's rules. -/
def ConstantInfo.withinCounts : ConstantInfo → Bool
  | .muts ms => ms.size ≤ countLimit && ms.all fun
      | .indc i => i.ctors.size ≤ countLimit
      | .recr r => r.rules.size ≤ countLimit
      | .defn _ => true
  | .recr r => r.rules.size ≤ countLimit
  | _ => true

def Constant.withinBudget (c : Constant) : Bool :=
  c.info.withinCounts && c.sharing.size ≤ countLimit && c.refs.size ≤ countLimit &&
    c.univs.size ≤ countLimit &&
    (c.info.exprs ++ c.sharing.toList).all Expr.withinBudget

/-! ## The depth the kernel walks

The certified kernel's reader and typing core recurse natively on a record's
expressions with every `share` expanded, so one stored record deep enough
overflows the thread's stack before the kernel declines anything (measured on
generated chains, shared and flat, reached and unreached: the kernel's
acceptance survives an expanded depth of 3,000 on a 2 MiB stack and 10,000 on
8 MiB, and overflows at 4,096 on 2 MiB and at 30,000 to 100,000 on 8 MiB, by
shape). Since ingress reads only the records the seeds reach, IxCC's own
budgets (`Constant.withinBudget`) no longer see every record, so the envelope
bounds every record's expressions before the kernel runs (`withinKernelDepth`):
each, with its shares expanded, at most `kernelDepthLimit` deep, computed
without recursion, each sharing entry's height once. A record whose sharing
reaches itself, which no canonical record has, is refused too.

What this does not do: it limits records as stored, after the kernel package's
decoder (`Ixon.Canonical.deConstant`, which recurses on unshared nesting before
it runs), and not the terms the kernel builds while typing, so unfolding across
records and shared chains can still take the kernel's conversion past its stack
(the roadmap's "Hardening"). Universe depth is not bounded here, as IxCC never
bounded it before; the kernel package's decoder bounds universe nodes
(`univNodeLimit`). Real artifacts: the deepest record of IxCC's committed
closures is 775 deep with shares expanded, of an Init+Std artifact 325, of
Mathlib 1,221 (2026-11-12). -/

/-- The deepest a record's expressions (shares expanded) may nest for the
kernel to read it: within what its acceptance was measured to survive on a
2 MiB stack (a quarter of the verifier's), above IxCC's own bound on a term it
converts (`Src.maxTermDepth`, 2,048), so that a reached term past that bound is
refused by IxCC's conversion as before, and twice Mathlib's deepest record
(1,221). -/
def kernelDepthLimit : Nat := 2560

/-- The children of a kernel-codec expression node. -/
def ixonChildren : _root_.Ixon.Expr → List _root_.Ixon.Expr
  | .prj _ _ b => [b]
  | .app f a => [f, a]
  | .lam _ t b | .all _ _ t b => [t, b]
  | .letE _ t v b => [t, v, b]
  | _ => []

/-- The expressions of a kernel-codec record's payload. -/
def ixonExprs (c : _root_.Ixon.Constant) : Array _root_.Ixon.Expr :=
  let defn := fun (d : _root_.Ixon.Definition) => #[d.typ, d.value]
  let recr := fun (r : _root_.Ixon.Recursor) => #[r.typ] ++ r.rules.map (·.rhs)
  let indc := fun (i : _root_.Ixon.Inductive) => #[i.typ] ++ i.ctors.map (·.typ)
  match c.info with
  | .defn d => defn d
  | .recr r => recr r
  | .axio a => #[a.typ]
  | .quot q => #[q.typ]
  | .muts ms => ms.flatMap fun
      | .defn d => defn d
      | .indc i => indc i
      | .recr r => recr r
  | _ => #[]

/-- Whether every expression in `roots`, with the shares of `sharing`
expanded, is at most `limit` deep: an explicit post-order, each sharing entry's
height memoized, so linear in the stored expressions; false on a sharing entry
that reaches itself. -/
def expandedWithin (sharing : Array _root_.Ixon.Expr) (limit : Nat)
    (roots : Array _root_.Ixon.Expr) : Bool := Id.run do
  let mut memo : Std.HashMap UInt64 Nat := {}
  let mut active : Std.HashSet UInt64 := {}
  for e0 in roots do
    let mut stack : Array (_root_.Ixon.Expr × Bool) := #[(e0, false)]
    let mut vals : Array Nat := #[]
    while !stack.isEmpty do
      let some (x, after) := stack.back? | break
      stack := stack.pop
      match x with
      | .share i =>
        if after then
          memo := memo.insert i (vals.back?.getD 0)
          active := active.erase i
        else if let some h := memo[i]? then
          vals := vals.push h
        else if active.contains i then
          return false
        else
          match sharing[i.toNat]? with
          | some s =>
            active := active.insert i
            stack := (stack.push (x, true)).push (s, false)
          | none => vals := vals.push 1
      | _ =>
        let cs := ixonChildren x
        if cs.isEmpty then
          vals := vals.push 1
        else if after then
          let k := cs.length
          let h := (vals.extract (vals.size - k) vals.size).foldl max 0 + 1
          if h > limit then return false
          vals := (vals.extract 0 (vals.size - k)).push h
        else
          stack := stack.push (x, true)
          for c in cs do stack := stack.push (c, false)
    if vals.back?.getD 0 > limit then return false
  return true

/-- **A record within the depth the kernel walks**: every expression of its
payload and of its sharing table, shares expanded, at most `kernelDepthLimit`
deep. Universes are not bounded here (the kernel's decoder bounds their nodes). -/
def withinKernelDepth (c : _root_.Ixon.Constant) : Bool :=
  expandedWithin c.sharing kernelDepthLimit (ixonExprs c ++ c.sharing)

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

end IxCC.Ixon.V3
