import Ix.Compile.Verify.CompileExpr
import Ix.Compile.Verify.ExprSpineCodec

/-!
# Production expression compiler/codec bridge

This module composes the surgery-free ordinary-expression refinement with the
production expression codec. It is kept separate so the compiler refinement
and codec developments remain independently reusable.
-/

namespace Ix.Compile.Verify

/-- A bounded ordinary expression compiled by the production dispatcher lies
in the public expression wire domain and survives an exact production
serialize/deserialize round trip. -/
theorem compileExpr_run_ordinary_codec_roundtrip
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr}
    (hsource : SupportedOrdinaryExpr levelSupport source)
    (hbound : ExprWireBound source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      target.wireWF ∧
      Ixon.deExpr (Ixon.serExpr target) = .ok target := by
  obtain ⟨root, state', hrun, hstate', hwire⟩ :=
    compileExpr_run_ordinary_wireWF compileEnv blockEnv snapshot hfree hclosed
      hlevelFaithful hexprFaithful hsource hbound hstate href
  exact ⟨root, state', hrun, hstate', hwire, deExpr_serExpr target hwire⟩

end Ix.Compile.Verify
