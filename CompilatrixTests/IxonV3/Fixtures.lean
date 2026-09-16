import Compilatrix.Ixon.V3.Resource.Admit

/-! The explicit fixture program paired with the unchanged ix resource.tsv
corpus at 2afb4eac. Its external interfaces are test assumptions only. -/

namespace CompilatrixTests.IxonV3.Fixtures

open Compilatrix.Ixon Compilatrix.Ixon.V3 Compilatrix.Ixon.V3.Resource

abbrev E := Compilatrix.Ixon.V3.Expr

def natTy : E := .ref 0 #[]
def pairTy : E := .ref 7 #[]
def zero : E := .nat 0
def b (uses : Uses) (value : ValueContract := .shared) : BinderContract := ⟨uses, value⟩
def arr (input : BinderContract) (result : ValueContract := .shared)
    (domain : E := natTy) (codomain : E := natTy) : E := .all input result domain codomain
def lam (input : BinderContract) (body : E) (domain : E := natTy) : E := .lam input domain body
def v (n : UInt64) : E := .var n
def ref (n : UInt64) : E := .ref n #[]
def call (n : UInt64) (arg : E) : E := .app (ref n) arg
def bind (contract : BinderContract) (value body : E) (type : E := natTy) : E :=
  .letE { nonDep := false, binder := contract } type value body
def borrow (owner body : E) (uses : Uses := .many) (type : E := natTy) : E :=
  .letE (.borrow false uses) type owner body

def choiceType (result : ValueContract) : E :=
  arr (b .linear) .shared natTy
    (arr (b .affine result) .shared natTy (arr (b .affine result) result))

/-- Test-only explicit assumptions. Production admission must bind their
addresses and the special selection behavior in its checker profile. -/
def program : Program := {
  declarations := #[
    { type := .sort 0, kind := .typeConstructor },                            -- 0 Nat
    { type := arr (b .many .localShared), kind := .assumption },              -- 1 observe
    { type := arr (b .linear .localShared) .localShared,
      body := some (lam (b .linear .localShared) (v 0)) },                    -- 2 local id
    { type := arr (b .linear .unique) .unique,
      body := some (lam (b .linear .unique) (v 0)) },                         -- 3 unique id
    { type := arr (b .erased), kind := .assumption },                        -- 4 erased input
    { type := arr (b .many), kind := .assumption },                          -- 5 many input
    { type := choiceType .shared, kind := .assumption },                     -- 6 choice
    { type := .sort 0, kind := .typeConstructor },                            -- 7 Pair
    { type := arr (b .linear .localShared) .localShared natTy pairTy,
      kind := .assumption },                                               -- 8 retain in pair
    { type := choiceType .localShared, kind := .assumption },                -- 9 local choice
    { type := choiceType .unique, kind := .assumption }                      -- 10 unique choice
  ]
  fields := #[
    { typeRef := 7, index := 0, type := natTy, contract := .unique },
    { typeRef := 7, index := 1, type := arr (b .many), contract := .unique },
    { typeRef := 7, index := 2, type := arr (b .many), contract := .shared }
  ]
  natType := some natTy
  stringType := some natTy
  sharing := #[v 0, ref 6]
  shareableTypes := #[0, 7]
  choices := #[6, 9, 10]
}

def choose (which : UInt64) (left right : E) : E :=
  .app (.app (call which zero) left) right

def runCase (type value : E) (limits : Limits := {}) : Except Error Unit :=
  let p := { program with declarations := program.declarations.push { type, body := some value } }
  checkDefinition p program.declarations.size limits

def errorCode : Error → String
  | .budget => "budget"
  | .unbound _ => "unbound"
  | .badReference _ => "reference"
  | .unresolvedSharing _ => "sharing"
  | .unsupported _ => "unsupported"
  | .typeMismatch => "type"
  | .binderMismatch => "binder"
  | .usage .. => "usage"
  | .moved _ => "moved"
  | .sharedToUnique => "ownership"
  | .activeLoan _ => "loan"
  | .escape .. => "escape"
  | .unrestrictedEscape _ => "unrestricted"
  | .nonduplicable => "capture"
  | .invalidBorrow => "borrow"
  | .invalidPlace => "place"
  | .invalidScope => "scope"

end CompilatrixTests.IxonV3.Fixtures
