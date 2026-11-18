import Ix.Frontend.Elab.Command
import Lean

/-!
Representative frontend baseline: default grammar and seeded core prelude.
The theorem deliberately precedes the function it uses, exercising dependency
scheduling. Output checks include exact types/bodies and resource metadata;
this does not run the separate addressed resource checker or emit Ixon.
-/
namespace FrontendRepresentative

open Ix.Frontend Ix.Frontend.Parser Ix.Frontend.Elab

def sourceText : String := include_str "Fixtures/FrontendPair.ix"

private def nm (s : String) := Name.mkStr2 "Demo" s
private def localName (s : String) := Name.simple s
private def type0 := Expr.mkSort (Level.mkSucc Level.mkZero)
private def pair (a : Ix.Expr) := Expr.mkApp (Expr.mkConst (nm "Pair")) a
private def ctor (a x y : Ix.Expr) := Expr.mkAppN (Expr.mkConst (Name.mkStr (nm "Pair") "mk")) #[a, x, y]

def swapType : Ix.Expr :=
  Expr.mkForallE (localName "α") type0
    (Expr.mkForallE (localName "p") (pair (Expr.mkBVar 0))
      (pair (Expr.mkBVar 1))) .implicit

def swapValue : Ix.Expr :=
  Expr.mkLam (localName "α") type0
    (Expr.mkLam (localName "p") (pair (Expr.mkBVar 0))
      (Expr.mkLetE (localName "x") (Expr.mkBVar 1)
        (Expr.mkProj (nm "Pair") 0 (Expr.mkBVar 0))
        (ctor (Expr.mkBVar 2) (Expr.mkProj (nm "Pair") 1 (Expr.mkBVar 1)) (Expr.mkBVar 0)))) .implicit

private def theoremLhs : Ix.Expr :=
  Expr.mkProj (nm "Pair") 0
    (Expr.mkAppN (Expr.mkConst (nm "swap"))
      #[Expr.mkBVar 2, ctor (Expr.mkBVar 2) (Expr.mkBVar 1) (Expr.mkBVar 0)])

def theoremType : Ix.Expr :=
  Expr.mkForallE (localName "α") type0
    (Expr.mkForallE (localName "a") (Expr.mkBVar 0)
      (Expr.mkForallE (localName "b") (Expr.mkBVar 1)
        (Expr.mkAppN (Expr.mkConst (Name.simple "Eq") #[Level.mkSucc Level.mkZero])
          #[Expr.mkBVar 2, theoremLhs, Expr.mkBVar 0]))) .implicit

def theoremValue : Ix.Expr :=
  Expr.mkLam (localName "α") type0
    (Expr.mkLam (localName "a") (Expr.mkBVar 0)
      (Expr.mkLam (localName "b") (Expr.mkBVar 1)
        (Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Eq" "refl") #[Level.mkSucc Level.mkZero])
          #[Expr.mkBVar 2, theoremLhs]))) .implicit

def checkEnv (env : IxElabEnv) : Bool := Id.run do
  let some (.inductInfo ind) := env.find? (nm "Pair") | return false
  let ctorName := Name.mkStr (nm "Pair") "mk"
  unless ind.numParams == 1 && ind.numIndices == 0 && ind.ctors == #[ctorName] do return false
  let some (.ctorInfo ci) := env.find? ctorName | return false
  unless ci.numParams == 1 && ci.numFields == 2 do return false
  for suffix in ["rec", "recOn", "casesOn", "_ctorIdx", "fst", "snd"] do
    unless env.contains (Name.mkStr (nm "Pair") suffix) do return false
  let some (.defnInfo swap) := env.find? (nm "swap") | return false
  unless swap.cnst.type == swapType && swap.value == swapValue do return false
  let some (.thmInfo thm) := env.find? (nm "swap_fst") | return false
  unless thm.cnst.type == theoremType && thm.value == theoremValue do return false
  let some (.defnInfo keep) := env.find? (nm "keep") | return false
  let .forallE _ α (.mdata data (.forallE _ xTy resultTy bi _) _) αBi _ := keep.cnst.type | return false
  unless α == type0 && αBi == .implicit && bi == .default &&
      xTy == Expr.mkBVar 0 && resultTy == Expr.mkBVar 1 do return false
  let .ok contract := Ix.SemanticContract.read data | return false
  unless contract.kind == .all && contract.binder == { uses := .linear, value := .unique } &&
      contract.result == .unique do return false
  let .lam _ α (.mdata data (.lam _ xTy body bi _) _) αBi _ := keep.value | return false
  unless α == type0 && αBi == .implicit && bi == .default &&
      xTy == Expr.mkBVar 0 && body == Expr.mkBVar 0 do return false
  let .ok contract := Ix.SemanticContract.read data | return false
  return contract.kind == .lam && contract.binder == { uses := .linear, value := .unique }

def parseCheck (src : String) : Bool :=
  match parseModuleWithEnv src "FrontendPair.ix" defaultParserEnv with
  | .ok (stx, _) => (Syntax.getArgs stx).size == 6
  | .error _ => false

def elaborate (src : String) : Except String IxElabEnv := do
  let (stx, _) ← parseModuleWithEnv src "FrontendPair.ix" defaultParserEnv
  elabModuleSyntax stx IxElabEnv.empty true

def elabCheck (src : String) : Bool :=
  match elaborate src with
  | .ok env => checkEnv env
  | .error _ => false

def parseInput : Bool := parseCheck sourceText
def elabInput : Bool := elabCheck sourceText

end FrontendRepresentative
