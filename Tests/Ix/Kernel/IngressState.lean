module

public import LSpec
public import Ix.Kernel.Ingress

/-! Cyclic sharing and finite conversion regressions for anonymous ingress. -/

namespace Tests.Kernel.IngressState

open LSpec Ix.Kernel

private def context (sharing : Array Ixon.Expr) : IngressCtx :=
  { sharing, refs := #[], univs := #[.zero], mutCtx := #[] }

private def cacheKey : Address × Address :=
  (Address.blake3 "ingress-frame-key".toUTF8, emptyCtxAddr)

private def cachedType : KExpr .anon := .mkSort .mkZero

private def before : AnonEnv :=
  { nextFVarId := 77
    inferCache := ({} : Std.HashMap _ _).insert cacheKey cachedType
    inferOnlyCache := ({} : Std.HashMap _ _).insert cacheKey cachedType
    whnfCache := ({} : Std.HashMap _ _).insert cacheKey cachedType }

private def keptState (after : AnonEnv) : Bool :=
  after.nextFVarId == 77 && after.inferCache[cacheKey]? == some cachedType &&
  after.inferOnlyCache[cacheKey]? == some cachedType && after.whnfCache[cacheKey]? == some cachedType

private def rejects (root : Ixon.Expr) (sharing : Array Ixon.Expr) (message : String) : Bool :=
  match (ingressExpr {} (context sharing) root).run {} before with
  | .error error after => error == message && keptState after
  | .ok .. => false

private def accepts (root : Ixon.Expr) (sharing : Array Ixon.Expr) (expected : KExpr .anon) : Bool :=
  match (ingressExpr {} (context sharing) root).run {} before with
  | .ok (term, _) after => term == expected && keptState after
  | .error .. => false

private def sharingTests : TestSeq :=
  test "ingress: reject direct sharing cycle and preserve checker state"
    (rejects (.share 0) #[.share 0] "cyclic Share index 0")
  ++ test "ingress: reject mutual sharing cycle"
    (rejects (.share 0) #[.share 1, .share 0] "cyclic Share index 0")
  ++ test "ingress: reject nested cycle after partial interning"
    (rejects (.share 0) #[.app (.var 0) (.share 0)] "cyclic Share index 0")
  ++ test "ingress: forward and repeated sharing remain accepted"
    (accepts (.app (.share 0) (.share 0)) #[.share 1, .var 0]
      (.mkApp (.mkVar 0 ()) (.mkVar 0 ())))
  ++ test "ingress: unused cyclic sharing does not affect a valid root"
    (accepts (.var 0) #[.share 0] (.mkVar 0 ()))
  ++ test "ingress: invalid sharing index remains an error"
    (rejects (.share 2) #[.var 0] "invalid Share index 2")

private def conversionTests : TestSeq :=
  test "ingress: nested binders and lets fit the computed work bound"
    (accepts (.leanLam (.sort 0) (.letE false (.sort 0) (.var 0) (.var 1))) #[]
      (.mkLam () () cachedType (.mkLet () cachedType (.mkVar 0 ()) (.mkVar 1 ()) false)))
  ++ test "ingress: deep source work count uses an explicit stack"
    (let root := (List.range 2048).foldl (fun body _ => Ixon.Expr.leanLam (.sort 0) body) (.var 0)
     match (ingressExpr {} (context #[]) root).run {} before with
     | .ok (term, _) after => term.lbr == 0 && keptState after
     | .error .. => false : Bool)
  ++ test "ingress: universe traversal preserves simplification and checker state"
    (let level : Ixon.Univ := .imax (.succ (.var 0)) (.max .zero (.succ .zero))
     match ingressUnivTree level before with
     | .ok result after => result == ixonUnivToK level && keptState after
     | .error .. => false : Bool)

public def suite : List TestSeq := [sharingTests, conversionTests]

end Tests.Kernel.IngressState
