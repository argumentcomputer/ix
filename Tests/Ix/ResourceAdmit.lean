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
  let overlay : Program := {
    declarations := #[
      { type := .sort 0, kind := .typeConstructor },
      { type := arr (b .many), kind := .assumption },
      { type := arr (b .many), body := some (lam (b .many) (call 1 (v 0))) }]
    interfaces := #[(1, arr (b .many .unique))] }
  unless (relevance overlay).toOption == some #[false, true, true] do
    throw <| IO.userError "effective interface did not mark its plain caller"
  checkAdmission "interface-only unique input checks plain caller" overlay false { assumptions := #[1] }
  let uniqueCaller := { overlay with declarations := overlay.declarations.set! 2 {
    type := arr (b .many .unique), body := some (lam (b .many .unique) (call 1 (v 0))) } }
  checkAdmission "interface unique input positive" uniqueCaller true { assumptions := #[1] }
  checkAdmission "default overlay positive" { overlay with interfaces := #[(1, arr (b .many))] }
    true { assumptions := #[1] }
  let ctor := { overlay with declarations := #[overlay.declarations[0]!,
    { type := arr (b .many), kind := .constructor }] }
  checkAdmission "constructor overlay cannot drop unique capture" ctor false { assumptions := #[1] }
  checkAdmission "constructor overlay preserves unique capture"
    { ctor with interfaces := #[(1, arr (b .many .unique) .unique)] } true { assumptions := #[1] }
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
  -- A linear binder that is never consumed is rejected in a definition, but a
  -- theorem's proof is erased computation with no resource obligation.
  let unusedLinear : Declaration := { type := arr (b .linear), body := some (lam (b .linear) zero) }
  checkAdmission "theorem proof carries no obligation"
    { program with declarations := program.declarations.push { unusedLinear with kind := .theorem } } true
  checkAdmission "definition with the same body is checked"
    { program with declarations := program.declarations.push unusedLinear } false
  -- R15: an assumed definition is admitted, not checked; a choice may be an
  -- assumed definition; admitted interfaces and case behavior must be bound.
  let assumedDefinition := { program with declarations := program.declarations.push unusedLinear }
  checkAdmission "assumed definition is admitted by the profile" assumedDefinition true
    { policy with assumptions := policy.assumptions.push 11 }
  let definitionChoice := { assumedDefinition with
    declarations := assumedDefinition.declarations.push
      { type := choiceType .shared, body := some (lam (b .linear) (lam (b .affine) (lam (b .affine) (v 0)))) }
    choices := program.choices.push 12 }
  checkAdmission "assumed definition as a selection primitive" definitionChoice true
    { policy with assumptions := policy.assumptions ++ #[11, 12], choices := policy.choices.push 12 }
  checkAdmission "unassumed definition as a selection primitive" definitionChoice false
    { policy with assumptions := policy.assumptions.push 11, choices := policy.choices.push 12 }
  let interfaced := { program with interfaces := #[(5, arr (b .many .localShared))] }
  checkAdmission "admitted interface bound by the profile" interfaced true
    { policy with assumptions := policy.assumptions.push 5 }
  checkAdmission "admitted interface absent from the profile" interfaced false
  checkAdmission "case behavior absent from the profile" { program with cases := true } false
  checkAdmission "case behavior bound by the profile" { program with cases := true } true
    { policy with cases := true }
  -- Review F1: case definitions must be bound by the profile.
  let caseBound := { program with cases := true, caseDefinitions := #[5] }
  checkAdmission "case definition absent from the profile" caseBound false
    { policy with cases := true }
  checkAdmission "case definition bound by the profile" caseBound true
    { policy with cases := true, caseDefinitions := #[5] }
  -- R17: an annotated recursive definition is checked through its unfolding
  -- equation, a theorem `∀ r, f r = rhs` bound by the profile.
  let eqStatement (lhs rhs : E) : E :=
    arr (b .many) .shared natTy (.app (.app (.app (ref 11) natTy) lhs) rhs)
  let eqBase (statement : E) (kind : DeclKind := .theorem) (eqType : Option UInt64 := some 11) :
      Program := { program with
    declarations := program.declarations ++ #[
      { type := arr (b .many) .shared (.sort 0)
          (arr (b .many) .shared (v 0) (arr (b .many) .shared (v 1) (.sort 1))),
        kind := .typeConstructor },
      { type := statement, body := some (lam (b .many) zero), kind },
      { type := arr (b .linear), body := some (lam (b .linear) zero) } ]
    eqType, equations := #[(13, 12)] }
  let good := eqStatement (call 13 (v 0)) (v 0)
  checkAdmission "definition checked through its unfolding equation" (eqBase good) true
    { policy with equations := #[(13, 12)] }
  checkAdmission "unfolding equation absent from the profile" (eqBase good) false
  for (label, p) in #[("an equation must be a theorem", eqBase good .definition),
      ("an equation must state an equality", eqBase (arr (b .many) .shared natTy natTy)),
      ("an equation must unfold its definition", eqBase (eqStatement (call 5 (v 0)) (v 0))),
      ("an equation needs the equality type", eqBase good .theorem none)] do
    unless (checkDefinition p 13).toOption.isNone do
      throw <| IO.userError s!"resource equations: {label}"
  -- Review F3: an equation whose proof depends on an axiom other than the
  -- standard three (here 14, as `sorryAx`) is not admitted.
  let withAxiom (proof : E) : Program :=
    let base := eqBase good
    { base with
      declarations := (base.declarations.set! 12 { base.declarations[12]! with body := some proof }).push
        { type := natTy, kind := .assumption }
      axioms := #[14] }
  checkAdmission "an equation proved with a non-standard axiom" (withAxiom (lam (b .many) (ref 14))) false
    { policy with equations := #[(13, 12)] }
  checkAdmission "an equation that does not use a present axiom" (withAxiom (lam (b .many) zero)) true
    { policy with equations := #[(13, 12)] }
  IO.println "Resource admission: 42 profile, dependency, constructor, theorem, interface, equation, and DAG checks passed"

end Tests.Resource

end

