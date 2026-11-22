import Aiur.Tiling.Lower
import Lean.Data.Json

/-!
JSON for graph fixtures and templates, in the format of the prototype's
comparison harness. Field elements are decimal strings of their canonical
representatives; `toNat` supplies that representative.
-/

namespace Aiur.Tiling.Export

open Lean (Json)

variable {F : Type} [CommRing F] [DecidableEq F]

def field (toNat : F → Nat) (x : F) : Json := Json.str (toString (toNat x))

def cell : Option Nat → Json
  | some s => Json.num s
  | none => Json.null

def term (toNat : F → Nat) : Term F → Json
  | .linear c s => Json.arr #["lin", field toNat c, Json.num s]
  | .product c a b => Json.arr #["prod", field toNat c, Json.num a, Json.num b]

def slot (toNat : F → Nat) : SlotDef F → Json
  | .column c => Json.mkObj [("column", Json.num c)]
  | .sum terms k => Json.mkObj [("sum", Json.mkObj [
      ("terms", Json.arr (terms.map (term toNat)).toArray), ("k", field toNat k)])]
  | .invocation => Json.mkObj [("invocation", Json.bool true)]
  | .key m => Json.mkObj [("key", Json.num m)]

def lane (toNat : F → Nat) (l : Lane F) : Json :=
  Json.mkObj [("qm", field toNat l.qm),
    ("q", Json.arr #[field toNat l.q0, field toNat l.q1, field toNat l.q2, field toNat l.q3]),
    ("qc", field toNat l.qc), ("qid", field toNat l.qid), ("cells", Json.arr #[cell l.c0, cell l.c1, cell l.c2, cell l.c3])]

def row (toNat : F → Nat) : Row F → Json
  | .gate lanes join _ => Json.mkObj [("gate", Json.mkObj [
      ("join", Json.bool join), ("lanes", Json.arr (lanes.map (lane toNat)).toArray)])]
  | .message sel tag sub cells => Json.mkObj [("message", Json.mkObj [
      ("sel", field toNat sel), ("tag", field toNat tag), ("sub", field toNat sub),
      ("cells", Json.arr (cells.map cell).toArray)])]

def template (toNat : F → Nat) (T : Template F) : Json :=
  Json.mkObj [("slots", Json.arr (T.slots.map (slot toNat)).toArray),
    ("rows", Json.arr (T.rows.map (row toNat)).toArray)]

def parseField (j : Json) : Except String F := do
  let s ← j.getStr?
  if s.startsWith "-" then
    let some n := (s.drop 1).toString.toNat? | throw s!"bad constant {s}"
    return -(n : F)
  let some n := s.toNat? | throw s!"bad constant {s}"
  return (n : F)

def parseNode (j : Json) : Except String (Node F) := do
  let op ← (← j.getArrVal? 0).getStr?
  let nat (i : Nat) : Except String Nat := do (← j.getArrVal? i).getNat?
  match op with
  | "const" => return .const (← parseField (← j.getArrVal? 1))
  | "var" => return .var (← nat 1)
  | "add" => return .add (← nat 1) (← nat 2)
  | "sub" => return .sub (← nat 1) (← nat 2)
  | "mul" => return .mul (← nat 1) (← nat 2)
  | "neg" => return .neg (← nat 1)
  | _ => throw s!"unknown node {op}"

def parseGraph (j : Json) : Except String (Graph F) := do
  let nodes ← (← (← j.getObjVal? "nodes").getArr?).mapM parseNode
  let zeros ← (← (← j.getObjVal? "zeros").getArr?).mapM (·.getNat?)
  let lookups ← (← (← j.getObjVal? "lookups").getArr?).mapM fun l => do
    let m ← (← l.getArrVal? 0).getNat?
    let args ← (← (← l.getArrVal? 1).getArr?).mapM (·.getNat?)
    return (m, args.toList)
  let width ← (← j.getObjVal? "width").getNat?
  return { width, nodes, zeros := zeros.toList, lookups := lookups.toList }

/-- Lower every fixture and record whether the checker accepts the template;
lowering failures become `{"error": …}`. -/
def run (toNat : F → Nat) (fixtures : Json) (width : Nat) : Except String Json := do
  let graphs ← (← fixtures.getArr?).mapM (parseGraph (F := F))
  return Json.arr <| graphs.map fun g =>
    match lower g width with
    | .ok T => (template toNat T).setObjVal! "checked" (Json.bool (T.check g.circuit))
    | .error e => Json.mkObj [("error", Json.str e)]

end Aiur.Tiling.Export
