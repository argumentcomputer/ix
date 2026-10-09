import Compilatrix.Cfg.Syntax
import Compilatrix.Own.Plain.Syntax

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc


abbrev Action := Own.Plain.Action
abbrev ActionTable := Src.NatMap Action

def marker (limit slot : Nat) : Action → Instr
  | .inc x n => .bind slot (.fir (.call limit [.var x, .lit (.nat n)]))
  | .dec x => .bind slot (.fir (.call (limit + 1) [.var x]))

def reserved (limit : Nat) : Instr → Bool
  | .bind _ (.fir (.call f _)) => f == limit || f == limit + 1
  | _ => false

def decode (limit : Nat) : Instr → Option (Nat × Action)
  | .bind slot (.fir (.call f args)) =>
    if f == limit then
      match args with
      | [.var x, .lit (.nat n)] => some (slot, .inc x n)
      | _ => none
    else if f == limit + 1 then
      match args with
      | [.var x] => some (slot, .dec x)
      | _ => none
    else none
  | _ => none

def collect (limit first : Nat) : List Instr → Option ActionTable
  | [] => some .leaf
  | i :: rest => do
    let table ← collect limit first rest
    if reserved limit i then
      let (slot, a) ← decode limit i
      if decide (slot < first) || table.contains slot then none else some (table.insert slot a)
    else
      match i with
      | .bind x (.fir (.call f _)) => if decide (x < first) && decide (f < limit) then some table else none
      | .bind x _ => if x < first then some table else none

def tableEq : ActionTable → ActionTable → Bool
  | .leaf, .leaf => true
  | .node v z o, .node v' z' o' => decide (v = v') && tableEq z z' && tableEq o o'
  | _, _ => false

def checkMarkers (limit first : Nat) (code : List Instr) (table : ActionTable) : Bool :=
  match collect limit first code with
  | none => false
  | some expected => tableEq expected table

end Compilatrix.Cfg.Rc
