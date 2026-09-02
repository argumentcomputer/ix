import Ix.Compile.Verify.Catalog
import Ix.Environment
import Lean4Lean.Std.Basic

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

/-- Length of the application spine that the reference compiler exposes at
the root. Metadata is transparent because compilation erases it. -/
def sourceAppCount : Ix.Expr → Nat
  | .app fn _ _ => sourceAppCount fn + 1
  | .mdata _ inner _ => sourceAppCount inner
  | _ => 0

/-- Length of the lambda telescope that the reference compiler exposes at
the root. Metadata is transparent because compilation erases it. -/
def sourceLamCount : Ix.Expr → Nat
  | .lam _ _ body _ _ => sourceLamCount body + 1
  | .mdata _ inner _ => sourceLamCount inner
  | _ => 0

/-- Length of the forall telescope that the reference compiler exposes at
the root. Metadata is transparent because compilation erases it. -/
def sourceAllCount : Ix.Expr → Nat
  | .forallE _ _ body _ _ => sourceAllCount body + 1
  | .mdata _ inner _ => sourceAllCount inner
  | _ => 0

/-- Source-side representability conditions for every count that
`compileExprRef` can expose on the Ixon wire. -/
def ExprWireBound : Ix.Expr → Prop
  | .bvar _ _ | .fvar _ _ | .mvar _ _ | .sort _ _ | .lit _ _ => True
  | .const _ levels _ => levels.size < UInt64.size
  | .app fn arg _ =>
    ExprWireBound fn ∧ ExprWireBound arg ∧
      sourceAppCount fn + 1 < UInt64.size
  | .lam _ ty body _ _ =>
    ExprWireBound ty ∧ ExprWireBound body ∧
      sourceLamCount body + 1 < UInt64.size
  | .forallE _ ty body _ _ =>
    ExprWireBound ty ∧ ExprWireBound body ∧
      sourceAllCount body + 1 < UInt64.size
  | .letE _ ty value body _ _ =>
    ExprWireBound ty ∧ ExprWireBound value ∧ ExprWireBound body
  | .mdata _ inner _ => ExprWireBound inner
  | .proj _ _ value _ => ExprWireBound value

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

/-- A successful `Array.mapM` preserves the input length. -/
private theorem array_mapM_size_of_eq_some {f : α → Option β}
    {xs : Array α} {ys : Array β} (h : xs.mapM f = some ys) :
    ys.size = xs.size := by
  have hmapped := congrArg (Option.map Array.toList) h
  change Array.toList <$> xs.mapM f = Option.map Array.toList (some ys) at hmapped
  rw [Array.toList_mapM] at hmapped
  have hlength := Lean4Lean.List.Forall₂.length_eq
    (Lean4Lean.List.mapM_eq_some.mp hmapped)
  simpa using hlength.symm

/-- Reference compilation preserves the three root-spine lengths used by the
Ixon expression wire format. -/
theorem compileExprRef_spineCounts {ctx : RefCompileCtx}
    {source : Ix.Expr} {target : Ixon.Expr}
    (h : compileExprRef ctx source = some target) :
    target.appCount = sourceAppCount source ∧
      target.lamCount = sourceLamCount source ∧
      target.allCount = sourceAllCount source := by
  induction source generalizing target with
  | bvar =>
    simp [compileExprRef] at h
    subst target
    simp [Ixon.Expr.appCount, Ixon.Expr.lamCount, Ixon.Expr.allCount,
      sourceAppCount, sourceLamCount, sourceAllCount]
  | fvar | mvar => simp [compileExprRef] at h
  | sort level _ =>
    simp [compileExprRef] at h
    rcases h with ⟨idx, hidx, rfl⟩
    simp [Ixon.Expr.appCount, Ixon.Expr.lamCount, Ixon.Expr.allCount,
      sourceAppCount, sourceLamCount, sourceAllCount]
  | const name levels _ =>
    simp [compileExprRef] at h
    rcases h with ⟨univs, hunivs, h⟩
    split at h
    · simp at h
      subst target
      simp [Ixon.Expr.appCount, Ixon.Expr.lamCount, Ixon.Expr.allCount,
        sourceAppCount, sourceLamCount, sourceAllCount]
    · simp at h
      rcases h with ⟨idx, hidx, rfl⟩
      simp [Ixon.Expr.appCount, Ixon.Expr.lamCount, Ixon.Expr.allCount,
        sourceAppCount, sourceLamCount, sourceAllCount]
  | app fn arg _ ihfn iharg =>
    simp [compileExprRef] at h
    rcases h with ⟨fn', hfn, arg', harg, rfl⟩
    obtain ⟨happ, hlam, hall⟩ := ihfn hfn
    simp [Ixon.Expr.appCount, Ixon.Expr.lamCount, Ixon.Expr.allCount,
      sourceAppCount, sourceLamCount, sourceAllCount, happ]
  | lam _ ty body _ _ ihty ihbody =>
    simp [compileExprRef] at h
    rcases h with ⟨ty', hty, body', hbody, rfl⟩
    obtain ⟨happ, hlam, hall⟩ := ihbody hbody
    simp [Ixon.Expr.leanLam, Ixon.Expr.appCount, Ixon.Expr.lamCount,
      Ixon.Expr.allCount, sourceAppCount, sourceLamCount, sourceAllCount, hlam]
  | forallE _ ty body _ _ ihty ihbody =>
    simp [compileExprRef] at h
    rcases h with ⟨ty', hty, body', hbody, rfl⟩
    obtain ⟨happ, hlam, hall⟩ := ihbody hbody
    simp [Ixon.Expr.leanAll, Ixon.Expr.appCount, Ixon.Expr.lamCount,
      Ixon.Expr.allCount, sourceAppCount, sourceLamCount, sourceAllCount, hall]
  | letE _ ty value body nonDep _ ihty ihvalue ihbody =>
    simp [compileExprRef] at h
    rcases h with ⟨ty', hty, value', hvalue, body', hbody, rfl⟩
    simp [Ixon.Expr.appCount, Ixon.Expr.lamCount, Ixon.Expr.allCount,
      sourceAppCount, sourceLamCount, sourceAllCount]
  | lit literal _ =>
    cases literal <;> simp [compileExprRef] at h <;>
      rcases h with ⟨idx, hidx, rfl⟩ <;>
      simp [Ixon.Expr.appCount, Ixon.Expr.lamCount, Ixon.Expr.allCount,
        sourceAppCount, sourceLamCount, sourceAllCount]
  | mdata _ inner _ ih =>
    simpa [sourceAppCount, sourceLamCount, sourceAllCount] using ih h
  | proj typeName field value _ ih =>
    simp [compileExprRef] at h
    rcases h with ⟨typeIdx, htype, value', hvalue, rfl⟩
    simp [Ixon.Expr.appCount, Ixon.Expr.lamCount, Ixon.Expr.allCount,
      sourceAppCount, sourceLamCount, sourceAllCount]

/-- Every source expression whose exposed structural counts fit the wire
compiles, when compilation succeeds, to a wire-representable Ixon expression. -/
theorem compileExprRef_wireWF {ctx : RefCompileCtx}
    {source : Ix.Expr} {target : Ixon.Expr}
    (hbound : ExprWireBound source)
    (h : compileExprRef ctx source = some target) :
    target.wireWF := by
  induction source generalizing target with
  | bvar =>
    simp [compileExprRef] at h
    subst target
    simp [Ixon.Expr.wireWF]
  | fvar | mvar => simp [compileExprRef] at h
  | sort level _ =>
    simp [compileExprRef] at h
    rcases h with ⟨idx, hidx, rfl⟩
    simp [Ixon.Expr.wireWF]
  | const name levels _ =>
    simp [compileExprRef] at h
    rcases h with ⟨univs, hunivs, h⟩
    have hsize : univs.size = levels.size :=
      array_mapM_size_of_eq_some hunivs
    simp [ExprWireBound] at hbound
    split at h
    · simp at h
      subst target
      simpa [Ixon.Expr.wireWF, hsize] using hbound
    · simp at h
      rcases h with ⟨idx, hidx, rfl⟩
      simpa [Ixon.Expr.wireWF, hsize] using hbound
  | app fn arg _ ihfn iharg =>
    simp [compileExprRef] at h
    rcases h with ⟨fn', hfn, arg', harg, rfl⟩
    rcases hbound with ⟨hfnBound, hargBound, hcount⟩
    refine ⟨ihfn hfnBound hfn, iharg hargBound harg, ?_⟩
    rw [(compileExprRef_spineCounts hfn).1]
    exact hcount
  | lam _ ty body _ _ ihty ihbody =>
    simp [compileExprRef] at h
    rcases h with ⟨ty', hty, body', hbody, rfl⟩
    rcases hbound with ⟨htyBound, hbodyBound, hcount⟩
    refine ⟨ihty htyBound hty, ihbody hbodyBound hbody, ?_⟩
    rw [(compileExprRef_spineCounts hbody).2.1]
    exact hcount
  | forallE _ ty body _ _ ihty ihbody =>
    simp [compileExprRef] at h
    rcases h with ⟨ty', hty, body', hbody, rfl⟩
    rcases hbound with ⟨htyBound, hbodyBound, hcount⟩
    refine ⟨ihty htyBound hty, ihbody hbodyBound hbody, ?_⟩
    rw [(compileExprRef_spineCounts hbody).2.2]
    exact hcount
  | letE _ ty value body nonDep _ ihty ihvalue ihbody =>
    simp [compileExprRef] at h
    rcases h with ⟨ty', hty, value', hvalue, body', hbody, rfl⟩
    rcases hbound with ⟨htyBound, hvalueBound, hbodyBound⟩
    exact ⟨ihty htyBound hty, ihvalue hvalueBound hvalue,
      ihbody hbodyBound hbody⟩
  | lit literal _ =>
    cases literal <;> simp [compileExprRef] at h <;>
      rcases h with ⟨idx, hidx, rfl⟩ <;> simp [Ixon.Expr.wireWF]
  | mdata _ inner _ ih =>
    exact ih hbound h
  | proj typeName field value _ ih =>
    simp [compileExprRef] at h
    rcases h with ⟨typeIdx, htype, value', hvalue, rfl⟩
    change value'.wireWF
    exact ih hbound hvalue

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
