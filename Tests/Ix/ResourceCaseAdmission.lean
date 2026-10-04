module
public import Ix.Resource.Check
public section

/- Independent raw Resource admission regressions. Synthetic metadata is
intentional: these are not authenticated combined-validator certificates.
Source-only when authored; execute separately from compilation. -/
namespace Tests.ResourceCaseAdmission
open Ixon Ix.Resource

def r (i : UInt64) : Ixon.Expr := .ref i #[]
def arr (a b : Ixon.Expr) : Ixon.Expr := .all .many .shared a b
def app (f : Ixon.Expr) (args : List Ixon.Expr) : Ixon.Expr :=
  args.foldl Ixon.Expr.app f
def family (x : Ixon.Expr) : Ixon.Expr := .app (r 2) x

def canonical : ConversionRecursor := {
  index := 4
  leading := 2
  major := 2
  rules := #[{
    constructor := 1
    params := 0
    fields := 0
    rhs := .lam .many (.sort 0) (.lam .many (.sort 0) (.var 0)) }]
}

def base : Program := {
  propSort := some 1
  cases := true
  shareableTypes := #[0]
  declarations := #[
    { type := .sort 0, kind := .typeConstructor },
    { type := r 0, kind := .constructor },
    { type := arr (r 0) (.sort 0), kind := .assumption },
    { type := arr (r 0) (family (.var 0)), kind := .assumption },
    { type := arr (arr (r 0) (.sort 0))
        (arr (.app (.var 0) (r 1)) (arr (r 0) (.app (.var 2) (.var 0)))),
      kind := .assumption },
    { type := arr (family (r 1)) (r 0), kind := .assumption }]
  recursors := #[{
    index := 4
    params := 0
    motives := 1
    minors := 1
    indices := 0
    fields := #[0]
    binders := #[0] }]
  conversionRecursors := #[canonical]
}

def ordinary (fixed : Bool) : Declaration := {
  type := arr (r 0) (arr (family (if fixed then r 1 else .var 0)) (r 0))
  body := some <|
    .lam .many (r 0) (.lam .many (family (if fixed then r 1 else .var 0))
      (app (r 4) [
        .lam .many (r 0) (arr (family (.var 0)) (r 0)),
        .lam .many (family (r 1)) (.app (r 5) (.var 0)),
        if fixed then r 1 else .var 1,
        .var 0]))
}

/-- The extra argument depends on y, while the scrutinized major is x. -/
def independentMajor : Declaration := {
  type := arr (r 0) (arr (r 0) (arr (family (.var 0)) (r 0)))
  body := some <|
    .lam .many (r 0) (.lam .many (r 0) (.lam .many (family (.var 0))
      (app (r 4) [
        .lam .many (r 0) (arr (family (.var 0)) (r 0)),
        .lam .many (family (r 1)) (.app (r 5) (.var 0)),
        .var 2,
        .var 0])))
}

def callback (result : ValueContract) (index : Ixon.Expr) : Ixon.Expr :=
  .all .many result (r 0) (family (match index with
    | .var n => .var (n + 1)
    | other => other))

/-- Specialization must preserve the callback's resource result contract. -/
def higherOrder : Declaration := {
  type := arr (r 0) (arr (callback .shared (.var 0)) (r 0))
  body := some <|
    .lam .many (r 0) (.lam .many (callback .shared (.var 0))
      (app (r 4) [
        .lam .many (r 0) (arr (callback .shared (.var 0)) (r 0)),
        .lam .many (callback .shared (r 1)) (.app (r 6) (.var 0)),
        .var 1,
        .var 0]))
}

/-- The minor's written binder stays honest in both cases. The actual helper
call demands either the same shared-result callback or a different unique
result contract, so beta substitution cannot erase the tested obligation. -/
def higherProgram (bad : Bool) : Program := {
  base with
  declarations := base.declarations.push {
    type := arr (callback (if bad then .unique else .shared) (r 1)) (r 0)
    kind := .assumption }
}

def expect (label : String) (p : Program) (d : Declaration) (accept : Bool) : IO Unit := do
  let p := { p with declarations := p.declarations.push d }
  let result := checkDefinition p (p.declarations.size - 1)
  match result, accept with
  | .ok (), true => pure ()
  | .error .typeMismatch, false => pure ()
  | _, _ => throw (IO.userError s!"{label}: expected accept={accept}, got {repr result}")

def run : IO Unit := do
  expect "fixed major" base (ordinary true) true
  expect "variable major" base (ordinary false) true
  expect "different lexical major" base independentMajor false
  expect "no refinement metadata" { base with conversionRecursors := #[] } (ordinary false) false
  expect "wrong major position" { base with conversionRecursors := #[{ canonical with major := 1 }] }
    (ordinary false) false
  expect "wrong leading count" { base with conversionRecursors := #[{ canonical with leading := 1 }] }
    (ordinary false) false
  let badRule := { canonical.rules[0]! with params := 1 }
  expect "wrong constructor parameters" { base with conversionRecursors := #[{ canonical with rules := #[badRule] }] }
    (ordinary false) false
  let badFields := { canonical.rules[0]! with fields := 1 }
  expect "wrong constructor fields" { base with conversionRecursors := #[{ canonical with rules := #[badFields] }] }
    (ordinary false) false
  expect "dependent callback positive" (higherProgram false) higherOrder true
  expect "dependent callback result contract differs" (higherProgram true) higherOrder false
  IO.println "10 independent raw case-admission controls passed"

end Tests.ResourceCaseAdmission
