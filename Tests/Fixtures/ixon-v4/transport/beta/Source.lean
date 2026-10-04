import Ix.Compile.SourceContract.Elab

namespace BetaControls
abbrev F : Type := List Nat → ! List Nat

theorem hiddenBad :
    ((fun r : List Nat => r = r)
      ((Classical.choice (show Nonempty F from ⟨fun _ => [1, 2]⟩)) [])) := rfl

theorem hiddenGood :
    ((fun r : List Nat => r = r)
      ((Classical.choice (show Nonempty F from ⟨fun xs => 0 :: xs⟩)) [])) := rfl

theorem deadBad :
    ((fun (_ : F) => (0 : Nat) = 0) (fun _ => [1, 2])) := rfl

def uniqueIdentity (! xs : List Nat) : ! List Nat := xs
def fresh (xs : List Nat) : ! List Nat := 0 :: xs

theorem changedInput :
    ((fun (f : List Nat → List Nat) => f = f) uniqueIdentity) := rfl
theorem changedResult :
    ((fun (f : List Nat → List Nat) => f = f) fresh) := rfl
theorem matchingResult : ((fun (f : F) => f = f) fresh) := rfl

theorem dependentGood :
    ((fun (α : Type) (x : α) => x = x) F fresh) := rfl

theorem aliasGood :
    (let g := fun r : F => r = r; g fresh) := rfl

theorem proofLetBad :
    ((fun r : List Nat =>
      let witness : Nonempty F := ⟨fun _ => [1, 2]⟩
      let ignored := (Classical.choice witness) []
      (r, ignored) = (r, ignored)) []) := by rfl

theorem bridge (f : F) : True = Nonempty F :=
  propext ⟨(fun _ => ⟨f⟩), (fun _ => True.intro)⟩
theorem directProofBad : Nonempty F :=
  Eq.mp ((fun f : F => bridge f) (fun _ => [1, 2])) True.intro
theorem directProofGood : Nonempty F :=
  Eq.mp ((fun f : F => bridge f) fresh) True.intro
theorem computationalBad : Nonempty F :=
  ⟨(fun f : F => f) (fun _ => [1, 2])⟩
theorem computationalGood : Nonempty F :=
  ⟨(fun f : F => f) fresh⟩

end BetaControls
