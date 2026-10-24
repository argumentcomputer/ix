/-
  Ix.Compile.Pass.Clique.WFMatcher: source-forward evidence for a matcher's
  exact eliminator argument flow.

  A `match` on a `Nat` that threads the recursion variable through its
  minors is followed by the well-founded transport only when its declaration
  is, symbolically, exactly the `Nat.casesOn` dispatch (`decodeWFNatMatcher`).
-/
module
public import Ix.Compile.Pass.Clique.WFSchema
@[expose] public section

namespace Ix.Compile.Pass.Clique

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
  let #[motive, major, zeroMinor, succMinor] := parameters
    | throw "WF matcher: the dispatcher does not bind its motive, major and minors"
  let nat := Expr.mkConst (leanName ``Nat) #[]
  let unit := Expr.mkConst (leanName ``Unit) #[]
  let (motiveArgs, motiveSort) ← openBinders false 1 motive.type
  let #[motiveArg] := motiveArgs | throw "WF matcher: motive domain is not Nat"
  unless alphaEqSkipMdata motiveArg.type nat do throw "WF matcher: motive domain is not Nat"
  let .sort resultLevel _ := stripMdata motiveSort | throw "WF matcher: motive does not return a sort"
  unless alphaEqSkipMdata major.type nat do throw "WF matcher: major domain is not Nat"
  let (zeroArgs, zeroResult) ← openBinders false 1 zeroMinor.type
  let #[zeroArg] := zeroArgs | throw "WF matcher: zero minor has a foreign argument"
  unless alphaEqSkipMdata zeroArg.type unit do throw "WF matcher: zero minor has a foreign argument"
  let .app zeroHead zero _ := stripMdata zeroResult | throw "WF matcher: zero minor does not return its motive"
  unless alphaEqSkipMdata zeroHead motive.expr && !(parameters ++ zeroArgs).any (fun p => mentionsFVar p.fvar zero) do
    throw "WF matcher: zero minor has a foreign motive or dependent index"
  let (succArgs, succResult) ← openBinders false 1 succMinor.type
  let #[succArg] := succArgs | throw "WF matcher: successor minor has a foreign motive or index"
  unless alphaEqSkipMdata succArg.type nat && alphaEqSkipMdata succResult
      (Expr.mkApp motive.expr (Expr.mkApp (Expr.mkConst (leanName ``Nat.succ) #[]) succArg.expr)) do
    throw "WF matcher: successor minor has a foreign motive or index"
  let expectedMotive := mkLambda motiveArgs (Expr.mkApp motive.expr motiveArg.expr)
  let expectedSucc := mkLambda succArgs (Expr.mkApp succMinor.expr succArg.expr)
  let expected := mkAppN (Expr.mkConst (leanName ``Nat.casesOn) #[resultLevel])
    #[expectedMotive, major.expr, Expr.mkApp zeroMinor.expr (Expr.mkConst (leanName ``Unit.unit) #[]), expectedSucc]
  unless alphaEqSkipMdata body expected do throw "WF matcher: body is not the exact symbolic Nat dispatch"
  let declaredType := Ix.Compile.Canon.substLevels declaration.levelParams levels declaration.type
  unless alphaEqSkipMdata declaredType (mkForall parameters (Expr.mkApp motive.expr major.expr)) do
    throw "WF matcher: declaration telescope differs from the symbolic dispatch"
  return { zero }

end Ix.Compile.Pass.Clique

end
