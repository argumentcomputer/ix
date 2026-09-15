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

def nativeBorrow (~!& x : @& Nat) : Nat := x

def twoLocal (~!& x : Nat) (1~ y : Nat) : Nat := x + y

def renamedLocal (~!& value : Nat) : Nat := value

def renamedTwoLocal (~!& first : Nat) (1~ second : Nat) : Nat := first + second

def localShared (~ x : Nat) : Nat := x

def localUnique (~! x : Nat) : Nat := x

@[inline] private def privateIdentity (!1 x : Nat) : Nat := x

def localResult (~ x : Nat) : ~ Nat := x
def localUniqueResult (~!1 x : Nat) : ~! Nat := x
def curriedResult (x y : Nat) : ~ Nat := x + y
def dependentArrow : (~ _x : Nat) → ~ Nat := fun x => x
def anonymousArrow : Nat → ~! Nat := fun x => x
def quantified : ∀ (~ _x : Nat), ~ Nat := fun x => x
def nestedLambda (x : Nat) : Nat := (fun (~1 y : Nat) => y) x
def lambdaDefinition := fun (~1 x : Nat) => x
def localLet (x : Nat) : Nat :=
  let (~!1 y : Nat) := x
  y
def sharedLoan (!1 owner : Nat) : Nat :=
  let borrow (~ view : Nat) := owner
  view

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
example : twoLocal 2 5 = 7 := rfl
example : privateIdentity 4 = 4 := rfl
example : ordinaryChar = 'a' := rfl

end Tests.Ix.SourceContract.SyntaxFixture

end
