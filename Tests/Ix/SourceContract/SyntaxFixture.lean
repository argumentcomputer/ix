module

public import Ix.Compile.SourceContract.Elab
public meta import Ix.Compile.SourceContract.Registry

public section

namespace Tests.Ix.SourceContract.SyntaxFixture

open scoped Ix.Modes

/-! ### Binder modes (all 7, composable, order-insensitive, all 4 bracket kinds) -/

def linear (@once x : Nat) : Nat := x
def unique (@unique x : Nat) : Nat := x
def uniqueAffine (@unique x : Nat) : Nat := x
def erased (@erased _x : Nat) : Nat := 7
def inferred (@once x : Nat) := x

def dependent {@erased α : Type} (@once x : α) : α := x
def inferredImplicit (@once x : α) : α := x
def withInstance {@erased α : Type} [@once inst : Inhabited α] : α := default
def withAnonInstance {@erased α : Type} [@borrowed Inhabited α] : α := default
def strictImplicit ⦃@erased α : Type⦄ (@once x : α) : α := x
def shadowed (@once _x : Nat) (@borrowed _x : Nat) : Nat := _x
def anonBinder (@erased _ : Nat) : Nat := 9

def nativeBorrow (@unique @borrowed x : @& Nat) : Nat := x
def nativeBorrowRev (@borrowed @unique x : @& Nat) : Nat := x

def twoLocal (@unique @borrowed x : Nat) (@once @borrowed y : Nat) : Nat := x + y
def twoLocalRev (@borrowed @unique x : Nat) (@borrowed @once y : Nat) : Nat := x + y

def renamedLocal (@unique @borrowed value : Nat) : Nat := value
def renamedTwoLocal (@unique @borrowed first : Nat) (@once @borrowed second : Nat) : Nat := first + second

def localShared (@borrowed x : Nat) : Nat := x
def localUnique (@unique @borrowed x : Nat) : Nat := x
def onceBorrowed (@once @borrowed x : Nat) : Nat := x
def onceBorrowedRev (@borrowed @once x : Nat) : Nat := x

def multiName (@unique x y : Nat) : Nat := x + y
def multiNameResult (@unique x y : Nat) : @unique Nat := x + y

@[inline] private def privateIdentity (@unique x : Nat) : Nat := x

/-! ### Result modes (4) on `def`, `abbrev`, `opaque`, `axiom`, `→`, `∀` -/

def localResult (@borrowed x : Nat) : @borrowed Nat := x
def uniqueResult (@unique x : Nat) : @unique Nat := x
def localUniqueResult (@unique @borrowed x : Nat) : @unique @borrowed Nat := x
def localUniqueResultRev (@borrowed @unique x : Nat) : @borrowed @unique Nat := x
def curriedResult (x y : Nat) : @borrowed Nat := x + y

abbrev abbrevUnique (@unique x : Nat) : @unique Nat := x
opaque opaqueBorrowed (@borrowed x : Nat) : @borrowed Nat := x
axiom axiomUnique (@unique _x : Nat) : @unique Nat

def dependentArrow : (@borrowed _x : Nat) → @borrowed Nat := fun x => x
def anonymousArrow : Nat → @unique @borrowed Nat := fun x => x
def arrowPrecedence : Nat → @unique Nat → Nat := fun x y => x + y
def arrowChain : (@borrowed _x : Nat) → @unique Nat → @borrowed Nat := fun x y => x + y
def quantified : ∀ (@borrowed _x : Nat), @borrowed Nat := fun x => x

/-! ### Lambdas (with and without `: T`, multi-name) -/

def nestedLambda (x : Nat) : Nat := (fun (@once @borrowed y : Nat) => y) x
def lambdaDefinition := fun (@once @borrowed x : Nat) => x
def lambdaNoType : (@unique _ : Nat) → Nat := fun (@unique x) => x + 1
def lambdaMultiNoType : (@unique _ : Nat) → (@unique _ : Nat) → Nat := fun (@unique x y) => x + y
def lambdaZeroLeak : (@unique _ : Nat) → Nat := fun (@unique x) =>
  let y := x
  y

/-! ### `let` and `do`-block `let` (all 8 modes, unparenthesized, optional `: T`) -/

def localLet (x : Nat) : Nat :=
  let @unique @borrowed y : Nat := x
  y

def localLetNoType (x : Nat) : Nat :=
  let @unique y := x
  let w := y
  w

def letAllModes (owner : Nat) : Nat :=
  let @borrowed a := owner
  let @unique b := a
  let @unique @borrowed c := b
  let @once f := c
  let @once @borrowed g := f
  let @erased _h := True.intro
  g

def sharedLoan (@unique owner : Nat) : Nat :=
  let @borrow view : Nat := owner
  view

def sharedLoanNoType (@unique owner : Nat) : Nat :=
  let @borrow view := owner
  view

def doBlockBorrow (@unique owner : Nat) : Id Nat := do
  let @borrow v := owner
  let w := v
  let @unique u : Nat := w + 1
  return u

def doBlockBorrowEscape (@unique owner : Nat) : Id Nat := do
  let @borrow v := owner
  return v

structure SyntaxBox where
  a : Nat
  b : Nat

def doBlockBorrowEscapeBox (@unique owner : SyntaxBox) : Id SyntaxBox := do
  let @borrow v := owner
  return v

def doBlockAllModes (owner : Nat) : Id Nat := do
  let @borrowed a := owner
  let @unique b := a
  let @borrowed @unique c := b
  let @once d := c
  let @borrowed @once e := d
  let @erased _h : True := trivial
  let @borrow v := e
  return v

/-! ### Structure & inductive fields (`@shared`, `@erased`, unmarked) -/

structure SharedBox (α : Type) where
  @shared item : α
  @erased inv : True
  payload : Nat

structure SharedOnly where
  @shared label : Nat

structure SharedDefault where
  @shared count : Nat := 0
  (@shared a b : Nat)

structure BasePair where
  first : Nat

structure ExtShared extends BasePair where
  @shared tag : Nat
  @erased witness : True

set_option linter.unusedVariables false in
inductive ModeList (α : Type) where
  | nil
  | cons (@shared head : α) (@erased proof : True) (tail : ModeList α)

set_option linter.unusedVariables false in
inductive ModeTree (α : Type) where
  | leaf
  | node (@shared label : α) (@erased proof : True) (left right : ModeTree α)

set_option linter.unusedVariables false in
inductive ArrowInd where
  | mk : Nat → (@shared x : Nat) → (@erased h : True) → ArrowInd

structure SharedPair (α : Type) where
  @shared item : α
  payload : Nat

set_option linter.unusedVariables false in
inductive SharedList (α : Type) where
  | nil
  | cons (@shared head : α) (tail : SharedList α)

set_option linter.unusedVariables false in
inductive SharedTree (α : Type) where
  | leaf
  | node (@shared label : α) (left right : SharedTree α)

set_option linter.unusedVariables false in
inductive SharedArrowInd where
  | mk : Nat → (@shared x : Nat) → SharedArrowInd

def readSharedBox (b : SharedBox Nat) : Nat :=
  match b with
  | .mk x _ p => x + p

/-! ### Native scoped `DefAsserts` attributes (`@[no_rc]`, `@[no_alloc]`, `@[bounded_stack]`) -/

@[no_rc] def defNoRc (x : Nat) : Nat := x + 1
@[no_alloc] def defNoAlloc (x : Nat) : Nat := x + 1
@[bounded_stack] def defBoundedStack (x : Nat) : Nat := x + 1
@[no_rc, bounded_stack] def defNoRcBounded (x : Nat) : Nat := x + 1
@[no_alloc, bounded_stack] def defNoAllocBounded (x : Nat) : Nat := x + 1
@[bounded_stack, no_alloc] def defBoundedNoAlloc (x : Nat) : Nat := x + 1
@[inline, no_rc] def defInlineNoRc (@unique x : Nat) : @unique Nat := x
@[no_alloc, bounded_stack] def defZeroArity : Nat := 42
@[no_rc] def defRecursive : Nat → Nat
  | 0 => 0
  | n + 1 => defRecursive n + 1

def privateDeclaration : Lean.Name := ``privateIdentity

/-! ### Non-interference with `open scoped Ix.Modes` active -/

def unique_fn {α : Type} (x : α) : α := x
def uniqueId {α : Type} (x : α) : α := x
def borrowed_fn {α : Type} (x : α) : α := x
def shared_fn {α : Type} (x : α) : α := x
def erased_fn {α : Type} (x : α) : α := x
def once_fn {α : Type} (x : α) : α := x
def borrow_fn {α : Type} (x : α) : α := x

def nonInterfExplicitApps (x : Nat) : Nat :=
  @unique_fn Nat x + @uniqueId Nat x + @id Nat x +
  @borrowed_fn Nat x + @shared_fn Nat x + @erased_fn Nat x +
  @once_fn Nat x + @borrow_fn Nat x

def nonInterfParenAscription (x : Nat) : Nat := (unique x : Nat)

def nonInterfLetPat (p : Nat × Nat) : Nat :=
  let @Prod.mk _ _ a b := p
  a + b

def nonInterfLetBorrowFn (owner : Nat) : Nat :=
  let borrow v := owner + v
  borrow 1

def nonInterfDoOrdinary (owner : Nat) (p : Nat × Nat) : Id Nat := do
  let @Prod.mk _ _ a b := p
  let borrow v := owner + v
  return a + b + borrow 1

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
example : nonInterfParenAscription 4 = 4 := rfl
example : nonInterfLetPat (2, 3) = 5 := rfl
example : nonInterfLetBorrowFn 10 = 11 := rfl
example : doBlockBorrow 5 = 6 := rfl

end Tests.Ix.SourceContract.SyntaxFixture

end
