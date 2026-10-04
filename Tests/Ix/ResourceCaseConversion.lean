module
public import Ix.Resource.Check
public section

/- Independent, source-only unit controls for lexical case conversion.
These deliberately construct contexts; they do not establish authenticated
recursor admission or replace full-boundary Q06/R27 tests. -/
namespace Tests.ResourceCaseConversion
open Ixon Ix.Resource

def runCheck (action : CheckM α) : Except Error α :=
  match action.run { remaining := 10000 } with
  | .ok value _ => .ok value
  | .error error _ => .error error

def program : Program := { declarations := #[] }
def ctor : Ixon.Expr := .ref 0 #[]
def branch : Context := {
  program, vars := #[0, 1, 2]
  caseValues := #[{ owner := 0, contextSize := 3, value := .app (.app ctor (.var 1)) (.var 0) }] }

def expectExpr (label : String) (ctx : Context) (input expected : Ixon.Expr) : IO Unit :=
  match runCheck (expandLocalValues ctx 100 0 input) with
  | .ok actual => unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .error e => throw (IO.userError s!"{label}: unexpected {repr e}")

def expectError (label : String) (ctx : Context) (input : Ixon.Expr) : IO Unit :=
  match runCheck (expandLocalValues ctx 20 0 input) with
  | .error _ => pure ()
  | .ok value => throw (IO.userError s!"{label}: unexpectedly expanded to {repr value}")

def run : IO Unit := do
  let constructed := .app (.app ctor (.var 1)) (.var 0)
  expectExpr "two fields preserve order" branch (.var 2) constructed
  expectExpr "distinct lexical major" branch (.var 1) (.var 1)
  let deeper := { branch with vars := #[0, 1, 2, 3] }
  let lifted := .app (.app ctor (.var 2)) (.var 1)
  expectExpr "later lexical binder" deeper (.var 3) lifted
  expectExpr "lambda depth" branch (.lam .many (.sort 0) (.var 3))
    (.lam .many (.sort 0) lifted)
  expectExpr "bound variable untouched" branch (.lam .many (.sort 0) (.var 0))
    (.lam .many (.sort 0) (.var 0))
  let linear : BinderContract := { BinderContract.many with uses := .linear }
  expectExpr "full arrow contracts preserved" branch
    (.all linear .unique (.var 2) (.var 3))
    (.all linear .unique constructed lifted)
  let alias := { deeper with letValues := #[(3, .var 2)] }
  expectExpr "actual let exposes case major" alias (.var 0) lifted
  let priority := { branch with letValues := #[(0, .sort 0)] }
  expectExpr "case precedes initializer" priority (.var 2) constructed
  let sibling := { branch with caseValues := #[] }
  expectExpr "no sibling fact" sibling (.var 2) (.var 2)
  let escaped := { branch with vars := #[0] }
  expectError "escaped context" escaped (.var 0)
  let cyclic : Context := {
    program, vars := #[0]
    caseValues := #[{ owner := 0, contextSize := 1, value := .var 0 }] }
  expectError "cyclic fact bounded" cyclic (.var 0)
  let withIH : Context := {
    program, vars := #[0, 1, 2, 3]
    caseValues := #[{ owner := 0, contextSize := 4, value := .app (.app ctor (.var 2)) (.var 1) }] }
  expectExpr "field vector skips trailing IH" withIH (.var 3)
    (.app (.app ctor (.var 2)) (.var 1))
  IO.println "12 independent case-context controls passed"

end Tests.ResourceCaseConversion
