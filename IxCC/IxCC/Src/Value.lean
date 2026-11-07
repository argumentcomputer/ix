import IxCC.Src.Syntax

/-! # SrcEval values

Values and slots of the clocked big-step semantics (design note 01 §3.1).
Thunks live only in environments (`Slot.name`) and are forced at each read:
call by name, not memoised. Types, proofs and irrelevant arguments are `irr`
values, which are never forced, applied or projected. -/

namespace IxCC.Src

/-- A special head, fired when saturated. -/
inductive Head where
  | ctor (c : CId)
  | quotMk (c : CId)
  | quotLift (c : CId)
  | recr (r : CId)
  /-- A `case` entry: the key `T.casesOn`. -/
  | cases (c : CId)
  | prim (op : PrimOp)
  deriving BEq, DecidableEq, Repr, Inhabited

mutual
inductive Value where
  /-- Every `Nat`, exact. -/
  | lit (n : Nat)
  /-- A string literal (stage S only). -/
  | str (s : String)
  /-- A constructor (or `Quot.mk`) with its parameter slots and fields. -/
  | con (c : CId) (ls : Levels) (params : List Slot) (fields : List Value)
  | clo (b : Binder) (dom body : Term) (ρ : List Slot) (ls : Levels)
  /-- An unsaturated special head. -/
  | pap (h : Head) (ls : Levels) (args : List Slot)
  /-- A type, proof or irrelevant argument; `none` is a proof field with no
  term (subsingleton recursor fields). -/
  | irr (t : Option Term) (ρ : List Slot) (ls : Levels)

inductive Slot where
  | val (v : Value)
  | name (t : Term) (ρ : List Slot) (ls : Levels)
end

instance : Inhabited Value := ⟨.lit 0⟩
instance : Inhabited Slot := ⟨.val (.lit 0)⟩

abbrev Env := List Slot

namespace Value

def isIrr : Value → Bool
  | .irr .. => true
  | _ => false

/-- Short shape name, for diagnostics and tests. -/
def shape : Value → String
  | .lit n => s!"lit {n}"
  | .str _ => "str"
  | .con c _ _ fs => s!"con {c}/{fs.length}"
  | .clo .. => "clo"
  | .pap .. => "pap"
  | .irr .. => "irr"

end Value

def Slot.irrNone (ls : Levels) : Slot := .val (.irr none [] ls)

end IxCC.Src
