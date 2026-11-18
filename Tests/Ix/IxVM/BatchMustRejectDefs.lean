/-! # Lean sources of the declaration checker's must-reject cases

Ordinary Lean declarations, checked by Lean's kernel, that `ixvm-batch-must-reject`
(`Tests.Ix.IxVM.BatchMustReject`) reads from the test binary's environment and compiles
with Ix's compiler. -/

namespace BatchMR

/-- A type former that erases its first argument. -/
def K (_ b : Type) : Type := b

/-- Nested through `List` and through `Option`; the `Option` occurrence sits where
whnf erases it, so Lean's recursor family has a motive for `Option T1` that no
constructor field reaches after whnf. -/
inductive T1 where
  | node : List T1 → K (Option T1) Unit → T1

/-- `T1` with the erased field at another `Option` (one that does not mention the block): its
family has no `Option` motive, and `K` and `Option` are in its closure, as `T1`'s family
needs them. -/
inductive T2 where
  | node : List T2 → K (Option Bool) Unit → T2

/-- A plain enumeration for the recursor-type fixture. -/
inductive Two where
  | a | b

/-- `PUnit.rec` on a variable at a never-zero level: Lean reduces it by structure η; the
reference kernel by its 0-field rescue of the pinned `PUnit`. -/
theorem punitRecStuck (x : PUnit.{1}) : (PUnit.rec (motive := fun _ => Nat) 0 x : Nat) = 0 := rfl

/-- The same at `PUnit.{u+1}`. -/
theorem punitRecStuckU.{u} (x : PUnit.{u+1}) : (PUnit.rec (motive := fun _ => Nat) 0 x : Nat) = 0 :=
  rfl

/-- The witness of an existential, as `0` here; the case replaces the value by the projection
of the witness (field 0 of `Exists`, a proposition). -/
def exWitness (_ : ∃ x : Nat, x = x) : Nat := 0

/-- The first component of a conjunction: a projection of a proposition's propositional field. -/
theorem andFst (p q : Prop) (h : p ∧ q) : p := h.1

/-- A sort named by a definition. -/
abbrev MySort : Type 1 := Type

/-- An indexed family whose type is declared at a definition (`Two → MySort`). -/
inductive FI : Two → MySort where
  | mk : FI Two.a

/-- An index-free family whose type is declared at a definition. -/
inductive F0 : MySort where
  | mk : F0

end BatchMR
