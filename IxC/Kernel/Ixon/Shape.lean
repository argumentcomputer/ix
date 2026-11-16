module

public import IxC.Kernel.ExprOps
public import IxC.Ixon.Types

@[expose] public section

/-! # Syntactic shapes with sharing and let substitution

The recursor index needs binder and application structure before it knows which
record references denote inductive families. Distinct symbolic keys retain the
reference-table and recursive-member indices without consulting a store. Levels,
literal contents, and binder metadata do not affect this structure.

Sharing entries are converted in order, just as in the expression reader. Lets
use the kernel's capture-avoiding substitution; its proved memoized implementation
preserves sharing in the converted expression graph.
-/

namespace Ix.Kernel.Reader.Shape

abbrev Term := Expr .source

def refKey (i : Nat) : Key .source := .id (.num (.num .anonymous 0) i)
def recurKey (i : Nat) : Key .source := .id (.num (.num .anonymous 1) i)

/-- Convert shape against the already converted sharing entries. A bad entry
affects only expressions which refer to it. Let types disappear with their lets. -/
def convert (table : Array (Option Term)) : Ixon.Expr → Option Term
  | .var i => some (.bvar i.toNat)
  | .sort _ => some (.sort .zero)
  | .ref i _ => some (.const (refKey i.toNat) [])
  | .recur i _ => some (.const (recurKey i.toNat) [])
  | .prj i field value => do
    pure (.proj (refKey i.toNat) field.toNat (← convert table value))
  | .str _ => some (.lit (.strVal ""))
  | .nat _ => some (.lit (.natVal 0))
  | .app fn arg => do pure (.app (← convert table fn) (← convert table arg))
  | .lam type body => do
    pure (.lam (← convert table type) (← convert table body) BinderMeta.leanNever)
  | .all type body => do
    pure (.forallE (← convert table type) (← convert table body) BinderMeta.leanNever)
  | .letE _ _ _ value body => do
    pure ((← convert table body).instantiate1Lift (← convert table value))
  | .share i => table[i.toNat]?.join

def sharing (entries : Array Ixon.Expr) : Array (Option Term) :=
  entries.foldl (fun table entry => table.push (convert table entry)) #[]

def read (constant : Ixon.Constant) (expression : Ixon.Expr) : Option Term :=
  convert (sharing constant.sharing) expression

def stripAll : Nat → Term → Option (List Term × Term)
  | 0, expression => some ([], expression)
  | n + 1, .forallE type body _ => do
    let (types, result) ← stripAll n body
    pure (type :: types, result)
  | _ + 1, _ => none

def stripAllFull : Nat → Term → List Term × Term
  | 0, expression => ([], expression)
  | n + 1, .forallE type body _ =>
    let (types, result) := stripAllFull n body
    (type :: types, result)
  | _ + 1, expression => ([], expression)

def appHead : Nat → Term → Term
  | 0, expression => expression
  | n + 1, .app fn _ => appHead n fn
  | _ + 1, expression => expression

inductive Head where
  | ref (index : Nat)
  | recur (index : Nat)
  deriving DecidableEq, Repr, BEq

def head (fuel : Nat) (expression : Term) : Option Head :=
  match appHead fuel expression with
  | .const (.id (.num (.num .anonymous 0) i)) _ => some (.ref i)
  | .const (.id (.num (.num .anonymous 1) i)) _ => some (.recur i)
  | _ => none

/-- The motive position and carrier heads, before any store lookup. The caller
supplies the existing spine bound separately from this structural conversion. -/
def analyse (fuel : Nat) (constant : Ixon.Constant) (recursor : Ixon.Recursor) :
    Option (Nat × Array Head × Head) := do
  let nP := recursor.params.toNat
  let nM := recursor.motives.toNat
  let depth := nP + nM + recursor.minors.toNat + recursor.indices.toNat + 1
  let (domains, body) ← stripAll depth (← read constant recursor.typ)
  let .bvar k := appHead fuel body | none
  let pos := depth - 1 - k
  guard (k < depth && nP ≤ pos && pos < nP + nM)
  let carriers ← (domains.drop nP |>.take nM).toArray.mapM fun domain => do
    let (types, _) := stripAllFull fuel domain
    head fuel (← types.getLast?)
  let major ← head fuel (← domains.getLast?)
  pure (pos - nP, carriers, major)

end Ix.Kernel.Reader.Shape
