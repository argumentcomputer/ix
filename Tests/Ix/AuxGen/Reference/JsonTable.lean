import Lean

namespace Tests.Ix.AuxGen.Reference.JsonTable
open Lean

private def failIf (bad : Bool) (why : String) : Except String Unit := if bad then throw s!"table: {why}" else pure ()
private def n (i : Nat) : Json := .str (toString i)
private def idx (j : Json) : Except String Nat := do
  let s ← j.getStr?
  let some i := s.toNat? | throw "table: bad index"
  failIf (toString i != s) "noncanonical index"
  return i
private def metric (j : Json) (children : Array (Nat × Nat)) : Nat × Nat :=
  let total := children.foldl (fun s v => s + v.1) 0
  let height := 1 + children.foldl (fun s v => max s v.2) 0
  match j with
  | .arr xs => (2 + total + (xs.size - 1), height)
  | .obj xs => (2 + total + xs.toList.foldl (fun s (k, _) => s + (Json.str k).compress.utf8ByteSize + 1) 0 + (xs.size - 1), height)
  | _ => (j.compress.utf8ByteSize, 1)
private def wrap (nodes : Array Json) (root bytes depth : Nat) : Json := Json.mkObj [
  ("schema", .str "m7-json-table-v1"), ("count", n nodes.size), ("root", n root),
  ("expandedBytes", n bytes), ("depth", n depth), ("nodes", .arr nodes)]

def decode (limitBytes : Nat) (document : Json) : Except String Json := do
  let nodes ← (← document.getObjVal? "nodes").getArr?
  let root ← idx (← document.getObjVal? "root")
  let bytes ← idx (← document.getObjVal? "expandedBytes")
  let depth ← idx (← document.getObjVal? "depth")
  failIf (document != wrap nodes root bytes depth) "header shape differs"
  failIf (nodes.isEmpty || nodes.size > 100000 || root != nodes.size - 1) "root/count differs"
  failIf (bytes > limitBytes || depth > 1024) "declared bounds exceeded"
  let mut values : Array Json := #[]
  let mut metrics : Array (Nat × Nat) := #[]
  let mut used := Array.replicate nodes.size false
  for (node, i) in nodes.zipIdx do
    let ref (r : Json) : Except String Nat := do
      let k ← idx r
      failIf (k ≥ i) "reference is not backward"
      return k
    let (value, refs) : Json × Array Nat ← match node with
      | .arr #[.str "s", .str s] => pure (.str s, #[])
      | .arr #[.str "b", .bool b] => pure (.bool b, #[])
      | .arr #[.str "n"] => pure (.null, #[])
      | .arr #[.str "a", .arr rs] => do
        let refs ← rs.mapM ref
        pure (.arr (refs.map (values[·]!)), refs)
      | .arr #[.str "o", .arr kv] => do
        let mut entries := #[]
        let mut refs := #[]
        let mut last : Option String := none
        for item in kv do
          let .arr #[.str key, r] := item | throw "table: object entry shape differs"
          if let some prev := last then failIf (!(prev < key)) "object keys are not strictly ordered"
          let k ← ref r
          entries := entries.push (key, values[k]!); refs := refs.push k; last := some key
        pure (Json.mkObj entries.toList, refs)
      | _ => throw "table: node shape/tag differs"
    let m := metric value (refs.map (metrics[·]!))
    failIf (m.1 > limitBytes || m.2 > 1024) "expanded bounds exceeded"
    for k in refs do used := used.set! k true
    values := values.push value; metrics := metrics.push m
  failIf (!((used.extract 0 root).all id)) "unreachable node"
  failIf (metrics[root]! != (bytes, depth)) "expanded size/depth differs"
  return values[root]!

private def compareFull (actual expected : Json) (raw : String) : Except String Unit := do
  failIf (actual != expected || actual.compress != raw) "full reference differs"
private def rejects (r : Except String α) (want : String) : Except String Unit := do
  match r with
  | .error e => failIf (e != "table: " ++ want) s!"wrong refusal: {e}"
  | .ok _ => throw "table: malformed input was accepted"
def controls : Except String Unit := do
  let sub := Json.arr #[.str "x", .bool true, .null]
  let sample := Json.mkObj [("a", sub), ("b", sub)]
  -- Handwritten independent table; both object entries retain the same array.
  let table := wrap #[.arr #[.str "s", .str "x"], .arr #[.str "b", .bool true], .arr #[.str "n"],
    .arr #[.str "a", .arr #[n 0, n 1, n 2]], .arr #[.str "o", .arr #[.arr #[.str "a", n 3], .arr #[.str "b", n 3]]]] 4 41 3
  compareFull (← decode 1000000 table) sample sample.compress
  rejects (decode 100 (wrap #[.arr #[.str "s", .num ⟨0, 0⟩]] 0 1 1)) "node shape/tag differs"
  for bad in #["0", "1", "99999"] do
    rejects (decode 100 (wrap #[.arr #[.str "a", .arr #[.str bad]]] 0 2 1)) "reference is not backward"
  rejects (decode 100 (wrap #[.arr #[.str "a", .arr #[.str "00"]]] 0 2 1)) "noncanonical index"
  rejects (decode 100 (wrap #[.arr #[.str "s", .str "x", .str "extra"]] 0 3 1)) "node shape/tag differs"
  rejects (decode 100 (wrap #[.arr #[.str "unknown"]] 0 1 1)) "node shape/tag differs"
  rejects (decode 100 (wrap #[.arr #[.str "b", .str "false"]] 0 5 1)) "node shape/tag differs"
  rejects (decode 100 (wrap #[.arr #[.str "s", .str "x"]] 1 3 1)) "root/count differs"
  rejects (decode 100 (wrap #[.arr #[.str "s", .str "x"], .arr #[.str "s", .str "y"]] 1 3 1)) "unreachable node"
  for keys in #[#["a", "a"], #["b", "a"]] do
    let kv := keys.map fun k => Json.arr #[.str k, n 0]
    rejects (decode 100 (wrap #[.arr #[.str "s", .str "x"], .arr #[.str "o", .arr kv]] 1 20 2)) "object keys are not strictly ordered"
  rejects (decode 1 table) "declared bounds exceeded"
  rejects (decode 1 (table.setObjVal! "expandedBytes" (n 1))) "expanded bounds exceeded"
  rejects (decode 100 (wrap #[.arr #[.str "s", .str "x"]] 0 4 1)) "expanded size/depth differs"

end Tests.Ix.AuxGen.Reference.JsonTable
