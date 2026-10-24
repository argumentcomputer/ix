/-! `T.below` user definition that does not reference `T`: no scheduler edge
between T's block and the user constant, so which one registers `T.below`
last may depend on the schedule. -/
namespace FieldBelowRace
inductive T
  | a
  | b

def T.below : Nat → Type := fun _ => Unit

theorem t_below : T.below 3 = Unit := rfl

structure Cut where
  below : Nat → Prop

def Cut.full : Cut := ⟨fun _ => True⟩
theorem Cut.full_below (n : Nat) : Cut.full.below n := trivial
end FieldBelowRace
