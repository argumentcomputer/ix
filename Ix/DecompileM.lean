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

def decompileLevel : Ix.Level → DecompileM Lean.Level
| .zero => pure .zero
| .succ u => .succ <$> decompileLevel u
| .max a b => Lean.Level.max  <$> decompileLevel a <*> decompileLevel b
| .imax a b => Lean.Level.imax <$> decompileLevel a <*> decompileLevel b
| .param n i => do
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

partial def decompileMutCtx (ctx: List (List Lean.Name)) 
  : DecompileM (RBMap Lean.Name Nat compare) := do
  let mut mutCtx : RBMap Lean.Name Nat compare := RBMap.empty
  for (ns, i) in List.zipIdx ctx do
    for n in ns do
      mutCtx := mutCtx.insert n i
  return mutCtx

partial def decompileConst (name: Lean.Name): Ix.Const -> DecompileM (List Lean.ConstantInfo)
| .axiom x => withLevels x.levelParams do
  let type <- decompileExpr x.type
  return [.axiomInfo (Lean.mkAxiomValEx name x.levelParams type false)]
| .definition x => List.singleton <$> decompileDefn name x
| .inductive x => decompileIndc x
| .quotient x => withLevels x.levelParams do
  let type <- decompileExpr x.type
  return [.quotInfo <| Lean.mkQuotValEx name x.levelParams type x.kind]
| .inductiveProj x => sorry
| .constructorProj x => sorry
| .recursorProj x => sorry
| .definitionProj x => sorry
| .mutDefBlock x => do
  let mutCtx <- decompileMutCtx x.ctx
  withMutCtx mutCtx do
    let mut vals := #[]
    for (defns, names) in List.zip x.defs x.ctx do
      for (defn, name) in List.zip defns names do
        let d <- decompileDefn name defn
        vals := vals.push d
    return vals.toList
| .mutIndBlock x => sorry
where
  decompileDefn (name: Lean.Name) (x: Ix.Definition) : DecompileM Lean.ConstantInfo := 
    withLevels x.levelParams do
      let type <- decompileExpr x.type
      let val <- decompileExpr x.type
      let safety := if x.isPartial then .«partial» else .safe
      match x.mode with
      | .definition => return .defnInfo <|
        Lean.mkDefinitionValEx name x.levelParams type val x.hints safety x.all
      | .opaque => return .opaqueInfo <|
        Lean.mkOpaqueValEx name x.levelParams type val true x.all
      | .theorem => return .thmInfo <|
        Lean.mkTheoremValEx name x.levelParams type val x.all
  decompileCtor (indcName: Lean.Name) (x: Ix.Constructor)
    : DecompileM Lean.ConstantInfo := do
    let type <- decompileExpr x.type
    return .ctorInfo <|
      Lean.mkConstructorValEx x.name x.levelParams type indcName 
        x.cidx x.numParams x.numFields false
  decompileRecrRule (x: Ix.RecursorRule) : DecompileM Lean.RecursorRule := do
    let rhs <- decompileExpr x.rhs
    return ⟨x.ctor, x.nfields, rhs⟩
  decompileRecr (indcAll: List Lean.Name) (x: Ix.Recursor)
    : DecompileM Lean.ConstantInfo := do
    let type <- decompileExpr x.type
    let rules <- x.rules.mapM decompileRecrRule
    return .recInfo <|
      Lean.mkRecursorValEx x.name x.levelParams type indcAll
        x.numParams x.numIndices x.numMotives x.numMinors rules x.k false
  decompileIndc (x: Ix.Inductive) : DecompileM (List Lean.ConstantInfo) := 
    withLevels x.levelParams do
      let type <- decompileExpr x.type
      let indc :=
        Lean.mkInductiveValEx name x.levelParams type x.numParams x.numIndices
          x.all (x.ctors.map (·.name)) x.numNested x.isRec false x.isReflexive
      let ctors <- x.ctors.mapM (decompileCtor name)
      let recrs <- x.recrs.mapM (decompileRecr x.all)
      return .inductInfo indc :: ctors ++ recrs

end
