module

public import Ix.Compile.SourceContract.Elab
public meta import Ix.Compile.SourceContract.Registry

public section

namespace Tests.Ix.SourceContract.SyntaxFixture

def linear (1 x : Nat) : Nat := x
def unique (! x : Nat) : Nat := x
def uniqueAffine (!& x : Nat) : Nat := x
def erased (0 _x : Nat) : Nat := 7
def inferred (1 x : Nat) := x

def dependent {0 α : Type} (1 x : α) : α := x
def inferredImplicit (1 x : α) : α := x
def withInstance {0 α : Type} [& inst : Inhabited α] : α := default
def strictImplicit ⦃0 α : Type⦄ (1 x : α) : α := x
def shadowed (1 _x : Nat) (& _x : Nat) : Nat := _x

regions 'a in
def nativeBorrow (!&'a x : @& Nat) : Nat := x

regions 'a 'b in
def twoRegions (!&'a x : Nat) (1'b y : Nat) : Nat := x + y

regions 'renamed in
def renamedRegion (!&'renamed value : Nat) : Nat := value

regions 'left 'right in
def renamedTwoRegions (!&'left first : Nat) (1'right second : Nat) : Nat := first + second

regions 'a in
def unrestrictedRegion ('a x : Nat) : Nat := x

regions 'a in
def uniqueRegion (!'a x : Nat) : Nat := x

@[inline] private def privateIdentity (!1 x : Nat) : Nat := x

def privateDeclaration : Lean.Name := ``privateIdentity

-- Ordinary notation must still use Lean's parsers and elaborators.
def ordinaryChar : Char := 'a'
def ordinaryNumber : Nat := 1
def ordinaryBinder (x : Nat) : Nat := x
def ordinaryRegions (regions : Nat) : Nat := regions

run_cmd do
  let source ← Lean.getConstInfo ``linear
  match Ix.Compile.registerMeasureHint (← Lean.getEnv) ⟨source, .position 0, some 1⟩ with
  | .ok env => Lean.setEnv env
  | .error error => Lean.throwError m!"{error}"

example : linear 3 = 3 := rfl
example : twoRegions 2 5 = 7 := rfl
example : privateIdentity 4 = 4 := rfl
example : ordinaryChar = 'a' := rfl

end Tests.Ix.SourceContract.SyntaxFixture

end
