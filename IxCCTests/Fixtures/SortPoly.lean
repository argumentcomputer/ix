/-! Sort-polymorphic code instantiated at `Sort 0` (level-exact relevance,
D18; `plans/x86-v2/research/relevance-checker.md` §2.4). Each root is a
`Nat → Nat` function. Compiled by `lake exe pin-src-tables --sortpoly`; see
`README.md`. -/

namespace SortPoly

/-- The research note's `five`: `Function.comp` at `β := True` (`v = 0`).
Inside `comp`, the argument `g x : β` is a proof exactly when `v = 0`. -/
def comp (n : Nat) : Nat :=
  Function.comp (fun (_ : True) => n + 5) (fun (_ : Nat) => trivial) n

/-- The same shape, defined here: `g a : β` is a proof at `v = 0`. -/
def through {α : Sort u} {β : Sort v} {γ : Sort w} (g : α → β) (f : β → γ) (a : α) : γ :=
  f (g a)

def throughRoot (n : Nat) : Nat :=
  through (fun (_ : Nat) => Nat.le_refl n) (fun (_ : n ≤ n) => 2 * n) n

/-- `PUnit.{0}` is a proposition, so its eliminator is a subsingleton one at
`u = 0` (the major is a proof) and an ordinary one otherwise. (A `match`
on `PUnit` elaborates to no eliminator at all, so these name `casesOn` and
`rec` directly.) -/
def punitCases (n : Nat) : Nat :=
  @PUnit.casesOn.{1, 0} (fun _ => Nat) PUnit.unit (n + 3)

def punitCasesType (n : Nat) : Nat :=
  @PUnit.casesOn.{1, 1} (fun _ => Nat) PUnit.unit (n + 4)

/-- The recursor itself; Lean's code generator does not compile recursors. -/
noncomputable def punitRec (n : Nat) : Nat :=
  @PUnit.rec.{1, 0} (fun _ => Nat) (n + 5) PUnit.unit

/-- One constant reached at two universe profiles. -/
def unitCase (x : PUnit.{u}) (n : Nat) : Nat :=
  @PUnit.casesOn.{1, u} (fun _ => Nat) x (n + 1)

def unitBoth (n : Nat) : Nat :=
  unitCase (PUnit.unit : PUnit.{0}) n + unitCase (PUnit.unit : PUnit.{1}) n

/-- A structure whose first field is a proof at `u = 0`. -/
def sigmaRoot (n : Nat) : Nat :=
  let s : (_ : n = n) ×' Nat := ⟨rfl, n + 1⟩
  s.2 * 2

/-- A type in a relevant position of a type-polymorphic callee: `g a : β`
with `β := Type` is a type, which no universe condition makes irrelevant.
Level-exact relevance does not cover this case (see `README.md`). -/
def typeArg (n : Nat) : Nat :=
  through (fun (_ : Nat) => Nat) (fun (_ : Type) => n + 7) n

end SortPoly
