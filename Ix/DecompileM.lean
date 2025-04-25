import Batteries.Data.RBMap
import Ix.TransportM
import Ix.Ixon.Metadata
import Ix.Ixon.Const
import Ix.Ixon.Serialize
import Ix.Common
import Ix.Store
import Ix.CompileM

open Batteries (RBMap)
open Batteries (RBSet)
open Ix.TransportM
open Ix.Compile

inductive DecompileError
| freeLevel : List Lean.Name -> Lean.Name -> Nat -> DecompileError
| mismatchedLevelName : List Lean.Name -> Lean.Name -> Lean.Name -> Nat -> DecompileError
| invalidBVarIndex : List Lean.Name -> Nat -> DecompileError
| mismatchedMutIdx : RBMap Lean.Name Nat compare -> Lean.Name -> Nat -> Nat -> DecompileError
| unknownMutual : RBMap Lean.Name Nat compare -> Lean.Name -> Nat -> DecompileError
| todo

abbrev DecompileM := ReaderT CompileEnv <| EStateM DecompileError CompileState

def DecompileM.run (env: CompileEnv) (stt: CompileState) (c : DecompileM α)
  : EStateM.Result DecompileError CompileState α
  := EStateM.run (ReaderT.run c env) stt

def decompileLevel : Ix.Univ → DecompileM Lean.Level
| .zero => pure .zero
| .succ u => .succ <$> decompileLevel u
| .max a b => Lean.Level.max  <$> decompileLevel a <*> decompileLevel b
| .imax a b => Lean.Level.imax <$> decompileLevel a <*> decompileLevel b
| .var n i => do
  match (<- read).univCtx[i]? with
  | some n' => 
    if n == n' then pure (Lean.Level.param n)
    else throw (.mismatchedLevelName (<- read).univCtx n' n i)
  | none => throw <| .freeLevel (<- read).univCtx n i

mutual

partial def decompileExpr : Ix.Expr → DecompileM Lean.Expr
| .var i      => do match (← read).bindCtx[i]? with
  | some _ => return .bvar i
  | none => throw $ .invalidBVarIndex (<-read).bindCtx i
| .sort u     => Lean.Expr.sort <$> decompileLevel u
| .lit l      => pure (.lit l)
| .app f a    => Lean.mkApp <$> decompileExpr f <*> decompileExpr a
| .lam n bi t b =>
    Lean.mkLambda n bi <$> decompileExpr t <*> withBinder n (decompileExpr b)
| .pi n bi t b =>
    Lean.mkForall n bi <$> decompileExpr t <*> withBinder n (decompileExpr b)
| .letE n t v b nd =>
    (@Lean.mkLet n) 
      <$> decompileExpr t
      <*> decompileExpr v 
      <*> withBinder n (decompileExpr b)
      <*> pure nd
| .proj n cont meta i e => do
    ensureConst n cont meta
    Lean.mkProj n i <$> decompileExpr e
| .const n cont meta us => do
    ensureConst n cont meta
    return Lean.mkConst n (<- us.mapM decompileLevel)
| .rec_ n i us => do match (<- read).mutCtx.find? n with
  | some i' =>
    if i == i' then do
      return Lean.mkConst n (<- us.mapM decompileLevel)
    else throw <| .mismatchedMutIdx (<- read).mutCtx n i i'
  | none => throw <| .unknownMutual (<- read).mutCtx n i

partial def ensureConst (name: Lean.Name) (cont meta: Address) : DecompileM Unit := do
  --match (<- get).names.find? n 
  sorry

partial def decompileConst (name: Lean.Name): Ix.Const -> DecompileM Lean.ConstantInfo
| .axiom x => sorry
  --return .axiomInfo ⟨name, levels, type⟩
| .theorem x => sorry
| .opaque x => sorry
| .definition x => sorry
| .quotient x => sorry
| .inductiveProj x => sorry
| .constructorProj x => sorry
| .recursorProj x => sorry
| .definitionProj x => sorry
| .mutDefBlock x => sorry
| .mutIndBlock x => sorry

end
