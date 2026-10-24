module
public import LSpec
public import Ix.AuxGen.AuxKernel
public import Ix.AuxGen.IxcScope
public section
namespace Tests.AuxGen.AuxKernel
open LSpec Ix.AuxGen
open Ix.CompileM (CompileM CompileError)
open Ix (Name Level Expr ConstantInfo)
private def nm (s : String) : Name := Name.mkStr .mkAnon s
private def type0 : Expr := Expr.mkSort (Level.mkSucc Level.mkZero)
private def cnst (s : String) : Expr := Expr.mkConst (nm s) #[]
private def maps : AddrMaps := { nameToAddr := fun _ => none }
private def decl (s : String) (ty : Expr) : LocalDecl :=
  { fvarName := nm s, binderName := nm s, domain := ty, info := .default }
private def run (act : KBridgeM α) : Except CompileError α := do
  let ((value, _), _) ← CompileM.run default
    { all := {}, current := nm "test", mutCtx := default, univCtx := [] } {}
    (act.run AuxKernelCtx.new)
  return value

/-! ## The recursor route's lazy IxC scope: β and the overlay (AuxGen M5c)

aux-cert's `F5_SigmaNestedNested` (`T.node : (Σ _ : Nat, List T) → T`): in the
nested expansion, `Sigma.mk`'s `snd` has type `(fun _ => T._nested.List_2) fst`,
and `T._nested.List_2` exists only in the recursor generator's overlay. Its
`whnf` is the β-reduct, a stuck inductive, so the lazy scope answers it without
the service (here there is none, so any question that reaches it is refused). -/

/-- A synthetic auxiliary of a nested expansion: only the overlay holds it. -/
private def auxName : Name := Name.mkStr (Name.mkStr (nm "T") "_nested") "List_2"
private def aux : Expr := Expr.mkConst auxName #[]

private def auxOverlay (n : Name) : Option ConstantInfo :=
  if n == auxName then some (.inductInfo
    { cnst := { name := auxName, levelParams := #[], type := type0 }
      numParams := 0, numIndices := 0, all := #[nm "T"], ctors := #[], numNested := 0
      isRec := true, isUnsafe := false, isReflexive := false })
  else none

private def x : Expr := Expr.mkFVar (nm "x")
private def lam (n : String) (b : Expr) : Expr := Expr.mkLam (nm n) (cnst "Nat") b .default
/-- `(fun n => T._nested.List_2) x` -/
private def redex : Expr := Expr.mkApp (lam "n" aux) x

/-- A block's oracle with no service, the recursor generator on IxC. -/
private def noService : AuxOracle :=
  Ixc.oracleOf .failClosed false { recursors := true } none 1 fun _ => .error "no service"

private def namedWhnf (overlay : Name → Option ConstantInfo) (e : Expr) :
    Option (Expr × WhnfHow) :=
  match (noService.newLazyScope overlay #[] #[(nm "x", cnst "Nat")]).whnfNamed e with
  | .ok (w, how, _) => some (w, how)
  | .error _ => none

private def answers (r : Option (Expr × WhnfHow)) (w : Expr) (how : WhnfHow) : Bool :=
  match r with
  | some (w', how') => Ix.Compile.ExactKey.exprEq w' w && how' == how
  | none => false

private def lazyBetaOverlay : Bool :=
  answers (namedWhnf auxOverlay redex) aux .beta
    -- two β-steps
    && answers (namedWhnf auxOverlay (Expr.mkApp (Expr.mkApp (lam "a" (lam "b" aux)) x) x))
      aux .beta
    -- the auxiliary is a stuck inductive through the overlay
    && answers (namedWhnf auxOverlay aux) aux .stuck
    -- the decision-grade `whnf` takes the same step
    && (match (noService.newLazyScope auxOverlay #[] #[(nm "x", cnst "Nat")]).whnf redex with
        | .ok (w, _) => Ix.Compile.ExactKey.exprEq w aux
        | .error _ => false)
    -- without the overlay both escape the fast paths and reach the service
    && (namedWhnf (fun _ => none) redex).isNone && (namedWhnf (fun _ => none) aux).isNone
    -- a reduct whose head is not stuck still asks the service
    && (namedWhnf auxOverlay (Expr.mkApp (lam "n" (Expr.mkApp (cnst "g") (Expr.mkBVar 0))) x)).isNone

/-- The same through `AuxScope.new … (route := .recursor)` under `failClosed`:
    the overlay reaches the lazy scope, and without it IxC's refusal fails the
    query. -/
private def recursorRouteOverlay : Bool :=
  let k : AuxKernel := .ixc maps noService
  let ask (overlay : Name → Option ConstantInfo) : Except CompileError Expr := run do
    let s ← AuxScope.new k #[decl "x" (cnst "Nat")] #[] (route := .recursor) (overlay := overlay)
    s.whnfOrInput redex
  (match ask auxOverlay with
    | .ok w => Ix.Compile.ExactKey.exprEq w aux
    | .error _ => false)
    && (ask (fun _ => none)).toOption.isNone

def suite : List TestSeq := [
  test "AuxGen M5c: the lazy scope's β-step and overlay (a nested block's synthetic auxiliary)"
    lazyBetaOverlay
  ++ test "AuxGen M5c: the recursor route passes the overlay; without it IxC refuses"
    recursorRouteOverlay]
end Tests.AuxGen.AuxKernel
