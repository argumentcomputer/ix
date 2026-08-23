import Ix.Compile.Verify.IxonValue
import Ix.Environment

/-!
# Total ordinary-fragment compiler specification

The production compiler is stateful and currently uses `partial def` for its
stack/caching implementation.  This module supplies the small total reference
functions needed by the first semantic slice.  It covers ordinary Lean kernel
syntax, treats metadata as presentation-only, rejects free variables,
metavariables, and universe metavariables, and emits the conservative Ixon v2
binder modes.

Later refinement theorems connect the production state machine to this
specification.  No production correctness claim is assumed here.
-/

namespace Ix.Compile.Verify

/-- Compile a named Ix universe into positional Ixon syntax. -/
def compileUnivRef (paramIndex : Ix.Name → Option UInt64) :
    Ix.Level → Option Ixon.Univ
  | .zero _ => some .zero
  | .succ level _ => return .succ (← compileUnivRef paramIndex level)
  | .max left right _ =>
    return .max (← compileUnivRef paramIndex left)
      (← compileUnivRef paramIndex right)
  | .imax left right _ =>
    return .imax (← compileUnivRef paramIndex left)
      (← compileUnivRef paramIndex right)
  | .param name _ => return .var (← paramIndex name)
  | .mvar _ _ => none

/-- Independent Theory reading of a named Ix universe under the same
positional parameter assignment. -/
def sourceUnivValue (paramIndex : Ix.Name → Option UInt64) :
    Ix.Level → Option Lean4Lean.VLevel
  | .zero _ => some .zero
  | .succ level _ => return .succ (← sourceUnivValue paramIndex level)
  | .max left right _ =>
    return .max (← sourceUnivValue paramIndex left)
      (← sourceUnivValue paramIndex right)
  | .imax left right _ =>
    return .imax (← sourceUnivValue paramIndex left)
      (← sourceUnivValue paramIndex right)
  | .param name _ => return .param (← paramIndex name).toNat
  | .mvar _ _ => none

/-- The reference universe compiler preserves its independent Theory value. -/
theorem compileUnivRef_value {paramIndex : Ix.Name → Option UInt64}
    {source : Ix.Level} {target : Ixon.Univ}
    (h : compileUnivRef paramIndex source = some target) :
    sourceUnivValue paramIndex source = some (univToVLevel target) := by
  induction source generalizing target with
  | zero =>
    simp [compileUnivRef] at h
    subst target
    rfl
  | succ level _ ih =>
    simp [compileUnivRef] at h
    rcases h with ⟨u, hu, rfl⟩
    simp [sourceUnivValue, ih hu, univToVLevel]
  | max left right _ ihleft ihright =>
    simp [compileUnivRef] at h
    rcases h with ⟨a, ha, b, hb, rfl⟩
    simp [sourceUnivValue, ihleft ha, ihright hb, univToVLevel]
  | imax left right _ ihleft ihright =>
    simp [compileUnivRef] at h
    rcases h with ⟨a, ha, b, hb, rfl⟩
    simp [sourceUnivValue, ihleft ha, ihright hb, univToVLevel]
  | param name _ =>
    simp [compileUnivRef] at h
    rcases h with ⟨idx, hidx, rfl⟩
    simp [sourceUnivValue, hidx, univToVLevel]
  | mvar => simp [compileUnivRef] at h

/-- Finite-table decisions exposed to the total ordinary expression
compiler.  These are representation choices, not semantic assumptions. -/
structure RefCompileCtx where
  univIndex : Ix.Level → Option UInt64
  refIndex : Ix.Name → Option UInt64
  /-- `some idx` exactly for a reference to a member of the current block. -/
  mutIndex : Ix.Name → Option UInt64 := fun _ => none
  /-- Address-table slot of a literal's committed bytes. -/
  literalRef : Lean.Literal → Option UInt64

/-- Total reference compiler for the ordinary expression fragment. -/
def compileExprRef (ctx : RefCompileCtx) : Ix.Expr → Option Ixon.Expr
  | .bvar idx _ => some (.var idx.toUInt64)
  | .fvar _ _ | .mvar _ _ => none
  | .sort level _ => return .sort (← ctx.univIndex level)
  | .const name levels _ => do
    let univs ← levels.mapM ctx.univIndex
    match ctx.mutIndex name with
    | some idx => return .recur idx univs
    | none => return .ref (← ctx.refIndex name) univs
  | .app fn arg _ =>
    return .app (← compileExprRef ctx fn) (← compileExprRef ctx arg)
  | .lam _ ty body _ _ =>
    return .leanLam (← compileExprRef ctx ty) (← compileExprRef ctx body)
  | .forallE _ ty body _ _ =>
    return .leanAll (← compileExprRef ctx ty) (← compileExprRef ctx body)
  | .letE _ ty val body nonDep _ =>
    return .letE nonDep (← compileExprRef ctx ty) (← compileExprRef ctx val)
      (← compileExprRef ctx body)
  | .lit literal _ => do
    let refIdx ← ctx.literalRef literal
    return match literal with
    | .natVal _ => .nat refIdx
    | .strVal _ => .str refIdx
  | .mdata _ inner _ => compileExprRef ctx inner
  | .proj typeName field val _ =>
    return .prj (← ctx.refIndex typeName) field.toUInt64
      (← compileExprRef ctx val)

/-- Every successful ordinary reference compilation inhabits the conservative
`.many`/`.shared` fragment of Ixon v2. -/
theorem compileExprRef_leanFragment {ctx : RefCompileCtx}
    {source : Ix.Expr} {target : Ixon.Expr}
    (h : compileExprRef ctx source = some target) :
    target.leanFragment = true := by
  induction source generalizing target with
  | bvar =>
    simp [compileExprRef] at h
    subst target
    rfl
  | fvar | mvar => simp [compileExprRef] at h
  | sort level _ =>
    simp [compileExprRef] at h
    rcases h with ⟨idx, hidx, rfl⟩
    rfl
  | const name levels _ =>
    simp [compileExprRef] at h
    rcases h with ⟨univs, hunivs, h⟩
    split at h
    · simp at h
      subst target
      rfl
    · simp at h
      rcases h with ⟨idx, hidx, rfl⟩
      rfl
  | app fn arg _ ihfn iharg =>
    simp [compileExprRef] at h
    rcases h with ⟨fn', hfn, arg', harg, rfl⟩
    simp [Ixon.Expr.leanFragment, ihfn hfn, iharg harg]
  | lam _ ty body _ _ ihty ihbody =>
    simp [compileExprRef] at h
    rcases h with ⟨ty', hty, body', hbody, rfl⟩
    simp [Ixon.Expr.leanLam, Ixon.Expr.leanFragment, ihty hty, ihbody hbody]
  | forallE _ ty body _ _ ihty ihbody =>
    simp [compileExprRef] at h
    rcases h with ⟨ty', hty, body', hbody, rfl⟩
    simp [Ixon.Expr.leanAll, Ixon.Expr.leanFragment, ihty hty, ihbody hbody]
  | letE _ ty val body nonDep _ ihty ihval ihbody =>
    simp [compileExprRef] at h
    rcases h with ⟨ty', hty, val', hval, body', hbody, rfl⟩
    simp [Ixon.Expr.leanFragment, ihty hty, ihval hval, ihbody hbody]
  | lit literal _ =>
    cases literal <;> simp [compileExprRef] at h <;>
      rcases h with ⟨idx, hidx, rfl⟩ <;> rfl
  | mdata _ inner _ ih => exact ih h
  | proj typeName field val _ ih =>
    simp [compileExprRef] at h
    rcases h with ⟨typeIdx, htype, val', hval, rfl⟩
    simp [Ixon.Expr.leanFragment, ih hval]

/-- The compiler's chosen conservative representative is already a mode
erasure fixed point. -/
theorem compileExprRef_eraseModes {ctx : RefCompileCtx}
    {source : Ix.Expr} {target : Ixon.Expr}
    (h : compileExprRef ctx source = some target) :
    eraseBinderModes target = target :=
  eraseBinderModes_eq_self_of_leanFragment (compileExprRef_leanFragment h)

end Ix.Compile.Verify
