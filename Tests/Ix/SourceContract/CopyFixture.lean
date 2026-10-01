import Ix.Compile.SourceContract.Elab

/-!
# Marker copies made by Lean's elaborator

Each declaration makes Lean copy a marked binder domain somewhere else: a
numeral elaborated against a marked parameter type, a matcher motive that
generalizes a marked index, the packed domain of a well-founded `_unary`, and a
matcher binder over a marked let. The copies annotate nothing; the originals
keep their binder sites.
-/

namespace Tests.Ix.SourceContract.CopyFixture

def takesUnique (! acc : Nat) : Nat := acc

/-- `1` elaborates against `takesUnique`'s marked domain and copies its marker. -/
def passesNumeral (n : Nat) : Nat := takesUnique n + takesUnique 1

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

/-- The matcher motive generalizes the marked index `n`. -/
def vhead {0 α : Type} {0 n : Nat} : Vec α (n+1) → α
  | .cons a _ => a

/-- `countdown._unary` packs the marked proof domain into a `PSigma`. -/
def countdown (n : Nat) (0 h : 0 ≤ n) : Nat :=
  if hn : n = 0 then 0 else countdown (n - 1) (Nat.zero_le _) + 1
termination_by n
decreasing_by omega

/-- The matcher binder for the discriminant copies the let's marked type. -/
def viaLet (xs : List Nat) : Nat :=
  let (~ v : List Nat) := xs
  match v with
  | [] => 0
  | _ :: _ => 1

def viaBorrow (xs : List Nat) : Nat :=
  let borrow (~ v : List Nat) := xs
  match v with
  | [] => 0
  | _ :: _ => 1

end Tests.Ix.SourceContract.CopyFixture

