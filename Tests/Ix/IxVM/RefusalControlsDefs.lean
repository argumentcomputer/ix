/-! # Lean sources of the refusal controls

Ordinary Lean declarations, checked by Lean's kernel, that `ixvm-refusal-controls`
(`Tests.Ix.IxVM.RefusalControls`) reads from the test binary's environment and compiles
with Ix's compiler. -/

namespace Tests.Ix.IxVM.RefusalControlsDefs

/-- A pair of sorts, as a value. -/
def propPair : Type × Type := (Prop, Prop)

/-- A proposition whose declared type is the pair's first component: a sort only after a
projection reduces. -/
def FstProp : propPair.1 := True

/-- A `Prop` structure whose field's type has that declared type. -/
structure HeadProj : Prop where
  h : FstProp

/-- A `Prop` structure with a field of data. -/
structure PropBox : Prop where
  n : Nat

/-- `0` here; the case replaces the value by the projection of the field out of the proof. -/
def boxValue (_ : PropBox) : Nat := 0

/-- The first component of a conjunction: a projection of a proposition's propositional
field. -/
theorem andFst (p q : Prop) (h : p ∧ q) : p := h.1

/-- A mutual pair in `Type`, with a reduction through its recursor. -/
mutual
inductive TA where
  | a : TA
  | b : TB → TA
inductive TB where
  | c : TA → TB
end

theorem taIota :
    @TA.rec (fun _ => Nat) (fun _ => Nat) 7 (fun _ n => n) (fun _ n => n) TA.a = 7 := rfl

end Tests.Ix.IxVM.RefusalControlsDefs
