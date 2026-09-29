module

public import Tests.Ix.Resource
public import Ix.Resource.Admit

public section

namespace Tests.Resource

open Ixon Ix.Resource

def policy : Policy := {
  assumptions := #[1, 4, 6, 8, 9, 10]
  choices := #[6, 9, 10]
  shareableTypes := #[0, 7]
}

def checkAdmission (label : String) (p : Program) (allowed : Bool)
    (policy : Policy := policy) : IO Unit := do
  let result := admitProgram p policy
  unless result.toOption.isSome == allowed do
    throw <| IO.userError s!"resource admission {label}: expected {allowed}, got {repr result}"

def withConstructor (type : E) : Program :=
  { program with declarations := program.declarations.push { type, kind := .constructor } }

def runAdmission : IO Unit := do
  checkAdmission "explicit profile" program true
  checkAdmission "unadmitted external contract" program false { policy with assumptions := #[6, 9, 10] }
  checkAdmission "unadmitted selection behavior" program false { policy with choices := #[] }
  checkAdmission "unadmitted representation" program false { policy with shareableTypes := #[] }
  let alias := { program with declarations := program.declarations.push {
    type := arr (b .many)
    body := some (ref 2) } }
  checkAdmission "ordinary spelling cannot drop imported contracts" alias false
  let chain := { alias with declarations := alias.declarations.push {
    type := arr (b .many)
    body := some (ref 11) } }
  let marked ← match relevance chain with
    | .ok marked => pure marked
    | .error error => throw <| IO.userError s!"relevance: {repr error}"
  unless marked[11]! && marked[12]! do
    throw <| IO.userError "resource relevance did not reach transitive aliases"
  let group := { program with
    declarations := program.declarations.push { type := natTy, body := some zero }
    groups := #[#[2, 11]] }
  let marked ← match relevance group with
    | .ok marked => pure marked
    | .error error => throw <| IO.userError s!"group relevance: {repr error}"
  unless marked[11]! do throw <| IO.userError "resource relevance skipped a mutual sibling"
  checkAdmission "mutual sibling checked" group true
  checkAdmission "linear constructor capture cannot become reusable"
    (withConstructor (arr (b .linear))) false
  checkAdmission "linear constructor capture stays unique"
    (withConstructor (arr (b .linear) .unique)) true
  checkAdmission "local constructor capture cannot escape"
    (withConstructor (arr (b .many .localShared))) false
  checkAdmission "local constructor capture stays local"
    (withConstructor (arr (b .many .localShared) .localShared)) true
  checkAdmission "partial constructor cannot forget prior captures"
    (withConstructor (arr (b .linear) .unique natTy (arr (b .many)))) false
  checkAdmission "curried constructor preserves every capture"
    (withConstructor (arr (b .linear) .unique natTy (arr (b .many) .unique))) true
  checkAdmission "type argument has no constructor capture"
    (withConstructor (arr (b .erased) .shared (.sort 0) natTy)) true
  checkAdmission "type argument does not discharge linear consumption"
    (withConstructor (arr (b .linear) .unique (.sort 0) natTy)) false
  let mut sharing : Array Ixon.Expr := #[.sort 0]
  for i in [:40] do
    sharing := sharing.push (.app (.share i.toUInt64) (.share i.toUInt64))
  let dag : Program := { declarations := #[{ type := .sort 0, body := some (.share 40) }], sharing }
  unless (relevance dag { depth := 1, steps := 200 }).toOption == some #[false] do
    throw <| IO.userError "relevance expanded a shared DAG as a tree"
  let cyclic := { dag with sharing := #[.share 0], declarations := #[{ type := .sort 0, body := some (.share 0) }] }
  unless (relevance cyclic).toOption.isNone do throw <| IO.userError "cyclic sharing was admitted"
  IO.println "Resource admission: 18 profile, dependency, constructor, and DAG checks passed"

end Tests.Resource

end

