module

public import Ix.Tc.Expr

/-!
Mirror: crates/kernel/src/constant.rs

Constant declarations parameterized by `Mode`. Each variant carries structural
fields plus metadata fields (`name`, `levelParams`, `leanAll`) for roundtrip
fidelity in meta mode.
-/

public section
@[expose] section

namespace Ix.Tc

/-- A recursor computation rule. `ctor` carries the Lean name of the
    constructor this rule dispatches on; the kernel dispatches on the
    positional `cidx` of `KConst.ctor`, but the name is preserved for
    ingress ↔ egress roundtrips. Erased (`Unit`) in anon mode. -/
structure RecRule (m : Mode) where
  ctor : m.F Name
  fields : UInt64
  rhs : KExpr m

instance : Inhabited (RecRule m) :=
  ⟨{ ctor := Mode.F.mkDefault, fields := 0, rhs := default }⟩

/-- A loaded constant. -/
inductive KConst (m : Mode) where
  | defn (name : m.F Name) (levelParams : m.F (Array Name))
      (kind : Ix.DefKind) (safety : Ix.DefinitionSafety)
      (hints : Lean.ReducibilityHints) (lvls : UInt64)
      (ty val : KExpr m) (leanAll : m.F (Array (KId m))) (block : KId m)
  | recr (name : m.F Name) (levelParams : m.F (Array Name))
      (k : Bool) (isUnsafe : Bool) (lvls params indices motives minors : UInt64)
      (block : KId m) (memberIdx : UInt64) (ty : KExpr m)
      (rules : Array (RecRule m)) (leanAll : m.F (Array (KId m)))
  | axio (name : m.F Name) (levelParams : m.F (Array Name))
      (isUnsafe : Bool) (lvls : UInt64) (ty : KExpr m)
  | quot (name : m.F Name) (levelParams : m.F (Array Name))
      (kind : Ix.QuotKind) (lvls : UInt64) (ty : KExpr m)
  | indc (name : m.F Name) (levelParams : m.F (Array Name))
      (lvls params indices : UInt64) (isUnsafe : Bool) (block : KId m)
      (memberIdx : UInt64) (ty : KExpr m) (ctors : Array (KId m))
      (leanAll : m.F (Array (KId m)))
  | ctor (name : m.F Name) (levelParams : m.F (Array Name))
      (isUnsafe : Bool) (lvls : UInt64) (induct : KId m)
      (cidx params fields : UInt64) (ty : KExpr m)

namespace KConst

def ty : KConst m → KExpr m
  | .defn (ty := t) .. => t
  | .recr (ty := t) .. => t
  | .axio (ty := t) .. => t
  | .quot (ty := t) .. => t
  | .indc (ty := t) .. => t
  | .ctor (ty := t) .. => t

def lvls : KConst m → UInt64
  | .defn (lvls := l) .. => l
  | .recr (lvls := l) .. => l
  | .axio (lvls := l) .. => l
  | .quot (lvls := l) .. => l
  | .indc (lvls := l) .. => l
  | .ctor (lvls := l) .. => l

def name : KConst m → m.F Name
  | .defn (name := n) .. => n
  | .recr (name := n) .. => n
  | .axio (name := n) .. => n
  | .quot (name := n) .. => n
  | .indc (name := n) .. => n
  | .ctor (name := n) .. => n

def levelParams : KConst m → m.F (Array Name)
  | .defn (levelParams := ps) .. => ps
  | .recr (levelParams := ps) .. => ps
  | .axio (levelParams := ps) .. => ps
  | .quot (levelParams := ps) .. => ps
  | .indc (levelParams := ps) .. => ps
  | .ctor (levelParams := ps) .. => ps

/-- Constructor tag name for diagnostics. -/
def kindName : KConst m → String
  | .defn .. => "definition"
  | .recr .. => "recursor"
  | .axio .. => "axiom"
  | .quot .. => "quotient"
  | .indc .. => "inductive"
  | .ctor .. => "constructor"

end KConst

end Ix.Tc

end
end
