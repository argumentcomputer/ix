import Benchmarks.FrontendMatchedRaw
import Ix.Aiur.Interpret
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FrontendMatchedTests
open Aiur FrontendWire
def deref (s : Store) (v : Value) : Except String Value := do
  let .pointer _ i := v | throw s!"not ptr: {v}"
  let some (vs, _) := s.getByIdx i | throw "missing ptr"
  let some v := vs[0]? | throw "empty ptr"
  return v
partial def values (s : Store) (v : Value) : Except String (List Value) := do
  let .ctor n vs ← deref s v | throw "not list"
  if n.toName == `ListNode.Nil then return []
  unless n.toName == `ListNode.Cons do throw "not cons"
  return vs[0]! :: (← values s vs[1]!)
partial def wire (s : Store) (v : Value) : Except String Wire := do
  let .ctor n vs ← deref s v | throw "not W"
  if n.toName == `WNode.Num then
    let .field g := vs[0]! | throw "not number"
    return .num g.val.toNat
  if n.toName == `WNode.Text then
    let bs ← (← values s vs[0]!).mapM fun v => do
      let .field g := v | throw "not byte"
      return g.val.toNat.toUInt8
    let some st := String.fromUTF8? ⟨bs.toArray⟩ | throw "bad utf8"
    return .text st
  let .field tag := vs[0]! | throw "not tag"
  return .node tag.val.toNat (← (← values s vs[1]!).mapM (wire s))
partial def difference (path : String) (a b : Wire) : Option String :=
  if a == b then none else
  match a,b with
  | .node i xs, .node j ys =>
    if i != j then some s!"{path}: tag {i} != {j}"
    else if xs.length != ys.length then some s!"{path}: length {xs.length} != {ys.length}"
    else ((xs.zip ys).zipIdx.findSome? fun ((a,b),i) => difference s!"{path}/{i}" a b)
  | _,_ => some s!"{path}: actual {repr a} expected {repr b}"

/-- Compare the full alpha-canonical output, or require both implementations
to reject. Returns whether this was a successful elaboration, for test counts. -/
def checkOutput (decls : Aiur.Source.Decls) (src : String) : IO Bool := do
  let bytes := src.toUTF8
  let dg := (Address.blake3 bytes).hash.data.map G.ofUInt8
  let io := (default : IOBuffer).extend 0 dg (bytes.data.map G.ofUInt8)
  let (result,state) := runFunction decls (Global.mk `matched_export) [.array (dg.map Value.field)] io
  match FrontendRepresentative.elaborate src, result with
  | .ok env, .ok value =>
    let actual ← IO.ofExcept (wire state.store value)
    if let some diff := difference "environment" actual (FrontendWire.ofEnv env) then
      throw (IO.userError diff)
    return true
  | .error _, .error _ => return false
  | .ok _, .error e => throw (IO.userError s!"raw rejected valid source: {e}")
  | .error e, .ok _ => throw (IO.userError s!"raw accepted invalid source: {e}")
end FrontendMatchedTests
