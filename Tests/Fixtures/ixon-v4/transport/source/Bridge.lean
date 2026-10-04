import Ix.Compile.SourceContract.Elab

/- Independent regression candidate for any rule which ghosts all arguments
merely because an application's result is canonical Eq. These functions
must be selected independently when exporting: the negative must not poison
the positive closure. The paired committed closures accompany this source. -/
namespace IndependentR21EqBridge

abbrev UniqueFunction : Type := List Nat → ! List Nat

theorem bridge (f : UniqueFunction) : True = Nonempty UniqueFunction :=
  propext ⟨(fun _ => ⟨f⟩), (fun _ => True.intro)⟩

/-- The inline function returns shared static data under a unique-result
promise. It must not become an extractable witness through an Eq helper. -/
theorem rejectedWitness : Nonempty UniqueFunction :=
  Eq.mp (bridge (fun _ => [1, 2])) True.intro

theorem acceptedWitness : Nonempty UniqueFunction :=
  Eq.mp (bridge (fun xs => 0 :: xs)) True.intro

/-- Extraction makes the consequence explicit; exporting the witness theorem
alone can isolate the guard without requiring executable Classical.choice. -/
noncomputable def rejected : UniqueFunction :=
  Classical.choice rejectedWitness

/-- Same logical route with a function that allocates a fresh outer cons. -/
noncomputable def accepted : UniqueFunction :=
  Classical.choice acceptedWitness

end IndependentR21EqBridge
