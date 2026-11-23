import IxCC.Cfg.Syntax
import IxCC.Own.Plain.Syntax

set_option autoImplicit false
namespace IxCC.Cfg.Rc


abbrev Action := Own.Plain.Action
abbrev ActionTable := Src.NatMap Action

def marker (limit slot : Nat) : Action → Instr
  | .inc x n => .bind slot (.fir (.call limit [.var x, .lit (.nat n)]))
  | .dec x => .bind slot (.fir (.call (limit + 1) [.var x]))

def resetMarker (limit slotReg x ctorIdx mask : Nat) (uniq : Bool) : Instr :=
  .bind slotReg (.fir (.call (limit + 2)
    [.var x, .lit (.nat ctorIdx), .lit (.nat mask), .lit (.nat (if uniq then 1 else 0))]))

def reuseMarker (limit dst slotReg ctorIdx : Nat) (uniq : Bool) (args : List Fir.Arg) : Instr :=
  .bind dst (.fir (.call (limit + 3)
    (.var slotReg :: .lit (.nat ctorIdx) :: .lit (.nat (if uniq then 1 else 0)) :: args)))

def reserved (limit : Nat) : Instr → Bool
  | .bind _ (.fir (.call f _)) => f == limit || f == limit + 1
  | _ => false

def isReuseOp (limit : Nat) : Instr → Bool
  | .bind _ (.fir (.call f _)) => f == limit + 2 || f == limit + 3
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

/-- Decode a `reset` marker: `(slotReg, x, ctorIdx, mask, uniq)`. -/
def decodeReset (limit : Nat) : Instr → Option (Nat × Nat × Nat × Nat × Bool)
  | .bind slotReg (.fir (.call f args)) =>
    if f == limit + 2 then
      match args with
      | [.var x, .lit (.nat ctorIdx), .lit (.nat mask), .lit (.nat u)] =>
        if u == 0 || u == 1 then some (slotReg, x, ctorIdx, mask, u == 1) else none
      | _ => none
    else none
  | _ => none

/-- Decode a `reuse` marker: `(dst, slotReg, ctorIdx, uniq, args)`. -/
def decodeReuse (limit : Nat) : Instr → Option (Nat × Nat × Nat × Bool × List Fir.Arg)
  | .bind dst (.fir (.call f args)) =>
    if f == limit + 3 then
      match args with
      | .var slotReg :: .lit (.nat ctorIdx) :: .lit (.nat u) :: rest =>
        if u == 0 || u == 1 then some (dst, slotReg, ctorIdx, u == 1, rest) else none
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
    else if isReuseOp limit i then
      match decodeReset limit i, decodeReuse limit i with
      | some (slotReg, _, _, _, _), none => if slotReg < first then some table else none
      | none, some (dst, _, _, _, _) => if dst < first then some table else none
      | _, _ => none
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

end IxCC.Cfg.Rc
