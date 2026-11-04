import IxC.Kernel.Frontend.InModel

/-! # The in-model inferer's fuel on hand-built terms

The in-model generator's syntactic inferer (`Ix.Kernel.Frontend.InModel`:
`betaHeadE`, `inferTy`, `sortOf`, `sortCeil`) runs at a fuel (`inferFuel`, the
depth of its recursion). Running out of it is a named failure
(`inferFuelMsg`) and, through `generate`, the decline of the block whose model
it was generating:

* passed: terms the walks read as before, at the fuel;
* the fuel-out failure, named:
  - the head β-reduction of `Ω = (fun x => x x) (fun x => x x)`;
  - the type of an application whose function's declared type is `Ω`;
  - the sort of a type whose declared type is `Ω`;
  - a `let` chain deeper than the fuel;
  - `generate` at a mutual block with an index whose declared type is `Ω`
    (a stream may declare such a constant: the reader runs the generator at
    the block's record, before the fold reads the constant). -/

open Ix.Kernel Ix.Kernel.Frontend.InModel

namespace Tests.Ix.Kernel.InferFuelFixtures

abbrev E := Expr .source

def key (s : String) : Key .source := .id (.str .anonymous s)
def type0 : E := .sort (.succ .zero)
/-- `fun x => x x` -/
def selfApp : E := .lam type0 (.app (.bvar 0) (.bvar 0)) default
/-- `Ω`: its head β-reduction does not terminate. -/
def omega : E := .app selfApp selfApp

/-- Whether `r` is the answer `a`. -/
def okIs [BEq α] : Except String α → α → Bool
  | .ok b, a => b == a
  | .error _, _ => false

/-- Whether `r` is the fuel-out failure. -/
def fuelOut : Except String α → Bool
  | .error m => m == inferFuelMsg
  | .ok _ => false

/-- `c : Ω`, `A : Type`, `F : Type → Type`. -/
def tbl : ConstTable .source := fun k =>
  if k == key "c" then some ([], omega)
  else if k == key "A" then some ([], type0)
  else if k == key "F" then some ([], .forallE type0 type0 default)
  else none

/-- `let x₁ := A; …; let xₙ := A; A`. -/
def letChain : Nat → E
  | 0 => .const (key "A") []
  | n + 1 => .letE type0 (.const (key "A") []) (letChain n) default

/-! ## Passed -/

-- `(fun x => x) A` reduces to `A`.
#guard okIs (betaHeadE (.app (.lam type0 (.bvar 0) default) (.const (key "A") [])))
  (.const (key "A") [])
-- the agreement test's reading, where the fuel runs out: the term itself
#guard betaHead omega == omega
#guard okIs (inferTy tbl [] (.app (.const (key "F") []) (.const (key "A") []))) (some type0)
#guard okIs (sortOf tbl [] (.const (key "A") [])) (some (.succ .zero))
-- a constant the table does not declare has no reading, and no failure
#guard okIs (inferTy tbl [] (.const (key "B") [])) none
#guard okIs (inferTy tbl [] (letChain 100)) (some type0)
#guard okIs (idxSort tbl [] (.const (key "A") [])) (some (.succ .zero))

/-! ## The fuel-out failure -/

#guard fuelOut (betaHeadE omega)
-- `c A`: `c`'s declared type `Ω` is head-reduced to read a `∀`
#guard fuelOut (inferTy tbl [] (.app (.const (key "c") []) (.const (key "A") [])))
-- `c` as a type: its declared type `Ω` is head-reduced to read a sort
#guard fuelOut (sortOf tbl [] (.const (key "c") []))
#guard fuelOut (idxSort tbl [] (.const (key "c") []))
-- a `let` chain deeper than the fuel
#guard fuelOut (inferTy tbl [] (letChain inferFuel))
#guard inferFuelMsg == "the syntactic type inferer ran out of fuel (depth 4096): a head β-reduction that does not terminate, or a term deeper than the fuel"

/-! ## Through `generate`

A mutual block `T₀ : c → Type`, `T₁ : Type` (no constructors, a recursor per
member): the generator bounds the sort of `T₀`'s index domain `c` (the tag
family's universe), which reads `c`'s declared type. -/

def member (n : String) (ty : E) (nIdx : Nat) : IndTypeRec .source :=
  { cv := ⟨key n, [], ty⟩, nP := 0, nIdx, ctors := [], isRec := false, isReflexive := false,
    numNested := 0 }

def recOf (n : String) (nIdx : Nat) : IndRecRec .source :=
  { cv := ⟨key n, [], .sort .zero⟩, nP := 0, nM := 2, nm := 0, nI := nIdx, rules := [] }

/-- The block, its index domain `d`. -/
def block (d : E) : BlockRec .source :=
  ⟨[member "T0" (.forallE d type0 default) 1, member "T1" type0 0], [],
   [recOf "T0.rec" 1, recOf "T1.rec" 0]⟩

def ctx : Ctx .source := ⟨tbl, fun _ => 0, fun _ => none⟩

#guard wants (block (.const (key "c") []))
-- the block's decline is the fuel-out
#guard fuelOut (generate ctx (block (.const (key "c") [])))
-- at an index domain `A : Type`, it is not
#guard !fuelOut (generate ctx (block (.const (key "A") [])))

end Tests.Ix.Kernel.InferFuelFixtures
