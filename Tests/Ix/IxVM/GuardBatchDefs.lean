import Lean

/-! # Shapes at the edge of the declaration checker's guards (fixtures)

Ordinary, kernel-checked Lean declarations for `Tests.Ix.IxVM.GuardBatch`.

* **Accepted**: a `let` in a constructor field's domain (`FieldLet`) and in a parameter's
  domain (`ParamLet`), which the recursor carries into a minor premise's domain and a
  parameter's domain; a type-annotation wrapper at a field's domain (`FieldWrapper`), which
  Lean's recursor drops from its minor premise, and at a parameter's domain
  (`ParamWrapper`); a recursive field ahead of ordinary fields that do not use it
  (`RecFirst`); a reflexive field of an indexed family (`ReflIdx`).
* **Declined**: a later field whose stored domain names an earlier recursive field
  (`UsedLater`). Lean accepts it, because the later domain reduces to a proposition that
  mentions neither the family nor the field.
* **A nested family** (`Rose`) and a structure that reaches one by reference (`WithTactic`,
  through `Lean.Syntax`): accepted as declared, with no model; the nested family's projection
  and its recursor are declined. -/

namespace Tests.Ix.IxVM.GuardBatchDefs

/-- A `let` in a field's domain. -/
structure FieldLet where
  n : Nat
  h : let m := n + 1; m = m

/-- A `let` in a parameter's domain. -/
inductive ParamLet (a : let T := Nat; T) : Type where
  | mk : ParamLet a

/-- A type-annotation wrapper at a field's domain. -/
inductive FieldWrapper where
  | mk (n : Nat := 0) : FieldWrapper

/-- A type-annotation wrapper at a parameter's domain. -/
class ParamWrapper (α : outParam Type) where
  val : α

/-- A recursive field ahead of ordinary fields that do not use it. -/
inductive RecFirst where
  | leaf : RecFirst
  | node : RecFirst → Nat → RecFirst → Bool → RecFirst

/-- A reflexive field of an indexed family. -/
inductive ReflIdx : Nat → Type where
  | base : ReflIdx 0
  | sup (n : Nat) : (Nat → ReflIdx n) → ReflIdx (n + 1)

/-- A nested family: its own type occurs under `List` in its constructor. Its projection
`Rose.children` is a definition by `Expr.proj`. -/
structure Rose where
  children : List Rose

/-- A structure with a field whose default is a tactic block: the field's domain names
`Lean.Syntax`, a nested family, through `autoParam`. -/
structure WithTactic where
  n : Nat
  h : n = n := by rfl

/-- A proposition that ignores its arguments. -/
def Erase (α : Type) (_ : α) : Prop := True

/-- A later field whose stored domain names an earlier recursive field. -/
inductive UsedLater where
  | leaf : UsedLater
  | node : (t : UsedLater) → Erase UsedLater t → UsedLater

end Tests.Ix.IxVM.GuardBatchDefs
