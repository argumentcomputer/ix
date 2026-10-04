/- Source-forward evidence for a matcher's exact eliminator argument flow. -/
module
public import Ix.Compile.Clique.WFSchema
public section

namespace Ix.Compile.Clique
open Ix (Expr Name ConstantInfo)
open Ix.Compile.Canon (mkAppN stripMdata)

/-- A declaration-checked Nat dispatcher. The zero expression comes from the
declared minor telescope, whose application is checked against Nat.casesOn.
No generated-name spelling or coincidentally equal instantiated type grants
this capability. -/
structure WFNatMatcher where
  zero : Expr

def decodeWFNatMatcher (const? : Name → Option ConstantInfo) (name : Name)
    (levels : Array Ix.Level) : TM WFNatMatcher := do
  let some declaration := (const? name).bind Decl.ofConstantInfo?
    | throw s!"WF matcher: source declaration {name} unavailable"
  unless declaration.name == name do throw "WF matcher: lookup returned another source declaration identity"
  unless levels.size == declaration.levelParams.size do
    throw "WF matcher: universe arity differs from source declaration"
  let value := Ix.Compile.Canon.substLevels declaration.levelParams levels declaration.value
  let (parameters, body) ← openBinders true 4 value
  let motive := parameters[0]!
  let major := parameters[1]!
  let zeroMinor := parameters[2]!
  let succMinor := parameters[3]!
  let nat := Expr.mkConst (leanName ``Nat) #[]
  let unit := Expr.mkConst (leanName ``Unit) #[]
  let (motiveArgs, motiveSort) ← openBinders false 1 motive.type
  unless alphaEq motiveArgs[0]!.type nat do throw "WF matcher: motive domain is not Nat"
  let .sort resultLevel _ := stripMdata motiveSort | throw "WF matcher: motive does not return a sort"
  unless alphaEq major.type nat do throw "WF matcher: major domain is not Nat"
  let (zeroArgs, zeroResult) ← openBinders false 1 zeroMinor.type
  unless alphaEq zeroArgs[0]!.type unit do throw "WF matcher: zero minor has a foreign argument"
  let .app zeroHead zero _ := stripMdata zeroResult | throw "WF matcher: zero minor does not return its motive"
  unless alphaEq zeroHead motive.expr && !(parameters ++ zeroArgs).any (fun p => mentionsFVar p.fvar zero) do
    throw "WF matcher: zero minor has a foreign motive or dependent index"
  let (succArgs, succResult) ← openBinders false 1 succMinor.type
  unless alphaEq succArgs[0]!.type nat && alphaEq succResult
      (Expr.mkApp motive.expr (Expr.mkApp (Expr.mkConst (leanName ``Nat.succ) #[]) succArgs[0]!.expr)) do
    throw "WF matcher: successor minor has a foreign motive or index"
  let expectedMotive := Ix.Compile.Image.mkLambda motiveArgs (Expr.mkApp motive.expr motiveArgs[0]!.expr)
  let expectedSucc := Ix.Compile.Image.mkLambda succArgs (Expr.mkApp succMinor.expr succArgs[0]!.expr)
  let expected := mkAppN (Expr.mkConst (leanName ``Nat.casesOn) #[resultLevel])
    #[expectedMotive, major.expr, Expr.mkApp zeroMinor.expr (Expr.mkConst (leanName ``Unit.unit) #[]), expectedSucc]
  unless alphaEq body expected do throw "WF matcher: body is not the exact symbolic Nat dispatch"
  let declaredType := Ix.Compile.Canon.substLevels declaration.levelParams levels declaration.type
  unless alphaEq declaredType (Ix.Compile.Image.mkForall parameters (Expr.mkApp motive.expr major.expr)) do
    throw "WF matcher: declaration telescope differs from the symbolic dispatch"
  return { zero }

end Ix.Compile.Clique
end
