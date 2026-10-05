import Ix.CompileCert.Map
import Ix.IxonUniv
import Ix.Kernel.Verify.Level

/-! # Independent direct export into reader syntax

This is a total reference function over supplied source declarations. It
does not invoke the compiler, source-recovery metadata, or a target reader.
Its errors are coverage boundaries, not proofs that the source is invalid.
The semantic theorem for canonical universe normalization remains a distinct
obligation; direct-reader comparison alone makes no denotation claim.
-/

namespace Ix.CompileCert

abbrev ExportM := Except String

structure ExportContext where
  source : Source
  map : SourceMap
  pins : Kernel.Reader.Pins

def sourceName : Lean.Name → Kernel.Name
  | .anonymous => .anonymous
  | .str p s => .str (sourceName p) s
  | .num p i => .num (sourceName p) i

/-- Source identity is structural and injective; target address aliases do
not collapse the independent source installation's namespace. -/
theorem sourceName_injective : Function.Injective sourceName := by
  intro a
  induction a with
  | anonymous =>
    intro b same
    cases b <;> simp_all [sourceName]
  | str parent text ih =>
    intro b same
    cases b <;> simp_all [sourceName]
    exact ih rfl
  | num parent index ih =>
    intro b same
    cases b <;> simp_all [sourceName]
    exact ih rfl

def ExportContext.memberName (cx : ExportContext) (n : Lean.Name) : ExportM Kernel.Name := do
  let some r := cx.map.find n | throw s!"missing source map entry: {n}"
  return cx.pins.names.getD r (Kernel.Reader.keyName r)

def ExportContext.name (cx : ExportContext) (n : Lean.Name) : ExportM Kernel.Name := do
  let some ci := cx.source.find n | throw s!"missing source declaration: {n}"
  match ci with
  | .recInfo v =>
    match n with
    | .str p "rec" =>
      unless v.all.contains p do throw s!"recursor owner mismatch: {n}"
      return (← cx.memberName p).str "rec"
    | .str p suffix =>
      unless suffix.startsWith "rec_" && v.all.head? == some p do
        throw s!"unsupported recursor naming: {n}"
      return (← cx.memberName p).str suffix
    | _ => throw s!"unsupported recursor naming: {n}"
  | _ => cx.memberName n

def ExportContext.plainLevels (cx : ExportContext) (ci : Lean.ConstantInfo) :
    ExportM (List Kernel.Name) := do
  let some r := cx.map.find ci.name | throw s!"missing source map entry: {ci.name}"
  match cx.pins.levels[r]? with
  | none => return Kernel.Reader.levelNames ci.levelParams.length
  | some ns =>
    let expected := ci.levelParams.map sourceName
    unless ns == expected do throw s!"pinned level telescope mismatch: {ci.name}"
    return expected

def ExportContext.levels (cx : ExportContext) (ci : Lean.ConstantInfo) :
    ExportM (List Kernel.Name) := do
  match ci with
  | .ctorInfo v =>
    let some ind := cx.source.find v.induct | throw s!"missing constructor owner: {v.induct}"
    let levels ← cx.plainLevels ind
    unless levels.length == ci.levelParams.length do throw "constructor level arity mismatch"
    return levels
  | .recInfo v =>
    let some r := cx.map.find ci.name | throw s!"missing recursor map entry: {ci.name}"
    if cx.pins.levels[r]?.isSome then return ← cx.plainLevels ci
    let some first := v.all.head? | throw "empty recursor owner block"
    let some ind := cx.source.find first | throw s!"missing recursor owner: {first}"
    let levels ← cx.plainLevels ind
    if ci.levelParams.length == levels.length then return levels
    unless ci.levelParams.length == levels.length + 1 do throw "recursor level arity mismatch"
    let candidates := (List.range (levels.length + 2)).map Kernel.Reader.levelName
    let some fresh := candidates.find? (fun n => !levels.contains n)
      | throw "no fresh recursor elimination level"
    return fresh :: levels
  | _ => cx.plainLevels ci

def exportUniv (params : List Lean.Name) : Lean.Level → ExportM Ixon.Univ
  | .zero => return .zero
  | .succ u => return .succ (← exportUniv params u)
  | .max u v => return .max (← exportUniv params u) (← exportUniv params v)
  | .imax u v => return .imax (← exportUniv params u) (← exportUniv params v)
  | .param n => do
    let some i := params.idxOf? n | throw s!"unbound source universe: {n}"
    unless i < 2^64 do throw "source universe index exceeds wire range"
    return .var i.toUInt64
  | .mvar _ => throw "source universe metavariable"

def importUniv (params : List Kernel.Name) : Ixon.Univ → ExportM Kernel.Level
  | .zero => return .zero
  | .succ u => return .succ (← importUniv params u)
  | .max u v => return .max (← importUniv params u) (← importUniv params v)
  | .imax u v => return .imax (← importUniv params u) (← importUniv params v)
  | .var i => do
    let some n := params[i.toNat]? | throw "canonical universe index outside telescope"
    return .param n

/-- Mathematical wire-level evaluation uses unbounded naturals. In
particular it does not share the canonicalizer's UInt64 offset arithmetic. -/
def univEval (ρ : UInt64 → Nat) : Ixon.Univ → Nat
  | .zero => 0
  | .succ u => univEval ρ u + 1
  | .max u v => max (univEval ρ u) (univEval ρ v)
  | .imax u v => if univEval ρ v = 0 then 0 else max (univEval ρ u) (univEval ρ v)
  | .var i => ρ i

/-- Successful import preserves evaluation under an explicitly aligned
telescope valuation. Missing indices cannot acquire invented parameter names
or default values: the hypothesis is success of the bounds-checked importer. -/
theorem importUniv_eval (params : List Kernel.Name) (ρ : UInt64 → Nat)
    (φ : Kernel.Name → Nat)
    (aligned : ∀ i n, params[i.toNat]? = some n → ρ i = φ n)
    {u : Ixon.Univ} {value : Kernel.Level}
    (imported : importUniv params u = .ok value) :
    Kernel.Level.Geran.levelEval φ value = univEval ρ u := by
  induction u generalizing value with
  | zero =>
    simp [importUniv, pure, Except.pure] at imported
    subst value
    rfl
  | succ u ih =>
    cases hu : importUniv params u with
    | error reason => simp [importUniv, hu, bind, Except.bind] at imported
    | ok inner =>
      simp [importUniv, hu, bind, Except.bind, pure, Except.pure] at imported
      subst value
      simp only [Kernel.Level.Geran.levelEval, univEval, ih hu]
  | max u v ihu ihv =>
    cases hu : importUniv params u with
    | error reason => simp [importUniv, hu, bind, Except.bind] at imported
    | ok left =>
      cases hv : importUniv params v with
      | error reason => simp [importUniv, hu, hv, bind, Except.bind] at imported
      | ok right =>
        simp [importUniv, hu, hv, bind, Except.bind, pure, Except.pure] at imported
        subst value
        simp only [Kernel.Level.Geran.levelEval, univEval, ihu hu, ihv hv]
  | imax u v ihu ihv =>
    cases hu : importUniv params u with
    | error reason => simp [importUniv, hu, bind, Except.bind] at imported
    | ok left =>
      cases hv : importUniv params v with
      | error reason => simp [importUniv, hu, hv, bind, Except.bind] at imported
      | ok right =>
        simp [importUniv, hu, hv, bind, Except.bind, pure, Except.pure] at imported
        subst value
        simp only [Kernel.Level.Geran.levelEval, univEval, ihu hu, ihv hv]
  | var i =>
    cases hn : params[i.toNat]? with
    | none => simp [importUniv, hn] at imported
    | some n =>
      simp [importUniv, hn, pure, Except.pure] at imported
      subst value
      exact (aligned i n hn).symm

/-- Source universe semantics is partial only at metavariables, which export
also rejects. No value is fabricated for an unresolved source universe. -/
def sourceLevelEval (φ : Lean.Name → Nat) : Lean.Level → Option Nat
  | .zero => some 0
  | .succ u => return (← sourceLevelEval φ u) + 1
  | .max u v => return max (← sourceLevelEval φ u) (← sourceLevelEval φ v)
  | .imax u v => do
    let a ← sourceLevelEval φ u
    let b ← sourceLevelEval φ v
    return if b = 0 then 0 else max a b
  | .param n => some (φ n)
  | .mvar _ => none

theorem exportUniv_eval (params : List Lean.Name) (φ : Lean.Name → Nat)
    (ρ : UInt64 → Nat)
    (aligned : ∀ n i, params.idxOf? n = some i → φ n = ρ i.toUInt64)
    {u : Lean.Level} {wire : Ixon.Univ} (exported : exportUniv params u = .ok wire) :
    sourceLevelEval φ u = some (univEval ρ wire) := by
  induction u generalizing wire with
  | zero =>
    simp [exportUniv, pure, Except.pure] at exported
    subst wire
    rfl
  | succ u ih =>
    cases hu : exportUniv params u with
    | error reason => simp [exportUniv, hu, bind, Except.bind] at exported
    | ok inner =>
      simp [exportUniv, hu, bind, Except.bind, pure, Except.pure] at exported
      subst wire
      simp [sourceLevelEval, univEval, ih hu]
  | max u v ihu ihv =>
    cases hu : exportUniv params u with
    | error reason => simp [exportUniv, hu, bind, Except.bind] at exported
    | ok left =>
      cases hv : exportUniv params v with
      | error reason => simp [exportUniv, hu, hv, bind, Except.bind] at exported
      | ok right =>
        simp [exportUniv, hu, hv, bind, Except.bind, pure, Except.pure] at exported
        subst wire
        simp [sourceLevelEval, univEval, ihu hu, ihv hv]
  | imax u v ihu ihv =>
    cases hu : exportUniv params u with
    | error reason => simp [exportUniv, hu, bind, Except.bind] at exported
    | ok left =>
      cases hv : exportUniv params v with
      | error reason => simp [exportUniv, hu, hv, bind, Except.bind] at exported
      | ok right =>
        simp [exportUniv, hu, hv, bind, Except.bind, pure, Except.pure] at exported
        subst wire
        simp [sourceLevelEval, univEval, ihu hu, ihv hv]
  | param n =>
    cases hi : params.idxOf? n with
    | none => simp [exportUniv, hi] at exported
    | some i =>
      by_cases bound : i < 2^64
      · simp [exportUniv, hi, bound, pure, Except.pure] at exported
        subst wire
        simp only [sourceLevelEval, univEval, aligned n i hi]
      · simp [exportUniv, hi, bound, Functor.map, Except.map] at exported
  | mvar _ => simp [exportUniv] at exported

structure TermContext where
  context : ExportContext
  sourceLevels : List Lean.Name
  targetLevels : List Kernel.Name

/-- Independently check semantic equality using the certified kernel's total
Géran comparison, whose offsets are Nat rather than the producer's UInt64.
This is an acceptance guard, not a proof that canonUniv always passes it. -/
def checkedLevelImage (original candidate : Kernel.Level) : ExportM Kernel.Level :=
  if Kernel.Level.Geran.leq original candidate 0 && Kernel.Level.Geran.leq candidate original 0 then
    .ok candidate
  else .error "canonical universe failed independent semantic equivalence"

theorem checkedLevelImage_eval {original candidate result : Kernel.Level}
    (checked : checkedLevelImage original candidate = .ok result) (φ : Kernel.Name → Nat) :
    Kernel.Level.Geran.levelEval φ result = Kernel.Level.Geran.levelEval φ original := by
  unfold checkedLevelImage at checked
  split at checked
  next valid =>
    have bounds : Kernel.Level.Geran.leq original candidate 0 = true ∧
        Kernel.Level.Geran.leq candidate original 0 = true := by
      simpa only [Bool.and_eq_true] using valid
    have forward := Kernel.Level.Geran.leq_sound bounds.1 φ
    have backward := Kernel.Level.Geran.leq_sound bounds.2 φ
    cases checked
    omega
  next => contradiction

def exportLevel (cx : TermContext) (u : Lean.Level) : ExportM Kernel.Level := do
  let raw ← exportUniv cx.sourceLevels u
  let original ← importUniv cx.targetLevels raw
  let candidate ← importUniv cx.targetLevels (Ixon.canonUniv raw)
  checkedLevelImage original candidate

/-- Every accepted exported level preserves the exact independently exported
raw level under every valuation of the same target telescope. Source-level
evaluation is connected separately by the export/import valuation lemmas. -/
theorem exportLevel_preserves_raw {cx : TermContext} {u : Lean.Level} {result : Kernel.Level}
    (exported : exportLevel cx u = .ok result) :
    ∃ wire original, exportUniv cx.sourceLevels u = .ok wire ∧
      importUniv cx.targetLevels wire = .ok original ∧
      ∀ φ, Kernel.Level.Geran.levelEval φ result = Kernel.Level.Geran.levelEval φ original := by
  cases hw : exportUniv cx.sourceLevels u with
  | error reason => simp [exportLevel, hw, bind, Except.bind] at exported
  | ok wire =>
    cases ho : importUniv cx.targetLevels wire with
    | error reason => simp [exportLevel, hw, ho, bind, Except.bind] at exported
    | ok original =>
      cases hc : importUniv cx.targetLevels (Ixon.canonUniv wire) with
      | error reason => simp [exportLevel, hw, ho, hc, bind, Except.bind] at exported
      | ok candidate =>
        have checked : checkedLevelImage original candidate = .ok result := by
          simpa only [exportLevel, hw, ho, hc, bind, Except.bind] using exported
        exact ⟨wire, original, rfl, ho, checkedLevelImage_eval checked⟩

/-- End-to-end accepted level export preserves the independently stated
source evaluation under the explicit source/wire/target telescope relation.
The same wire valuation connects both directions, so inequalities cannot be
proved under one telescope and then reused under a different one. -/
theorem exportLevel_eval {cx : TermContext} {u : Lean.Level} {result : Kernel.Level}
    (exported : exportLevel cx u = .ok result)
    (φ : Lean.Name → Nat) (ρ : UInt64 → Nat) (ψ : Kernel.Name → Nat)
    (sourceAligned : ∀ n i, cx.sourceLevels.idxOf? n = some i → φ n = ρ i.toUInt64)
    (targetAligned : ∀ i n, cx.targetLevels[i.toNat]? = some n → ρ i = ψ n) :
    sourceLevelEval φ u = some (Kernel.Level.Geran.levelEval ψ result) := by
  obtain ⟨wire, original, hw, ho, same⟩ := exportLevel_preserves_raw exported
  rw [same ψ, importUniv_eval cx.targetLevels ρ ψ targetAligned ho]
  exact exportUniv_eval cx.sourceLevels φ ρ sourceAligned hw

/-- The checked equality survives the kernel's actual parameter substitution,
using its proved substitution-evaluation law, not syntactic equality of
canonicalized levels. -/
theorem checkedLevelImage_subst_eval {original candidate result : Kernel.Level}
    (checked : checkedLevelImage original candidate = .ok result)
    (φ : Kernel.Name → Nat) (keys : List Kernel.Name) (values : List Kernel.Level) :
    Kernel.Level.eval φ (Kernel.Level.subst keys values result) =
      Kernel.Level.eval φ (Kernel.Level.subst keys values original) := by
  rw [Kernel.Level.eval_subst, Kernel.Level.eval_subst,
    Kernel.Level.eval_eq_levelEval, Kernel.Level.eval_eq_levelEval]
  exact checkedLevelImage_eval checked (Kernel.Level.substFn φ keys values)

/-- Source evaluation after assigning the selected universe arguments agrees
with actual kernel-level instantiation. The alignment premise explicitly
uses `substFn`, including its specified behavior for unlisted parameters. -/
theorem exportLevel_instantiated_eval {cx : TermContext} {u : Lean.Level} {result : Kernel.Level}
    (exported : exportLevel cx u = .ok result)
    (φ : Lean.Name → Nat) (ρ : UInt64 → Nat) (ψ : Kernel.Name → Nat)
    (keys : List Kernel.Name) (values : List Kernel.Level)
    (sourceAligned : ∀ n i, cx.sourceLevels.idxOf? n = some i → φ n = ρ i.toUInt64)
    (targetAligned : ∀ i n, cx.targetLevels[i.toNat]? = some n →
      ρ i = Kernel.Level.substFn ψ keys values n) :
    sourceLevelEval φ u = some (Kernel.Level.eval ψ (Kernel.Level.subst keys values result)) := by
  rw [Kernel.Level.eval_subst, Kernel.Level.eval_eq_levelEval]
  exact exportLevel_eval exported φ ρ (Kernel.Level.substFn ψ keys values) sourceAligned targetAligned

/-- Binder names and binder-info are reader-erased. Metadata is refused
until its semantic/erasure classification is justified independently. -/
def exportExpr (cx : TermContext) : Lean.Expr → ExportM Kernel.Expr
  | .bvar i => return Kernel.Expr.mkBvar i
  | .sort u => return .sort (← exportLevel cx u)
  | .const n us => return .const (← cx.context.name n) (← us.mapM (exportLevel cx))
  | .app f a => return .app (← exportExpr cx f) (← exportExpr cx a)
  | .lam _ t b _ => return .lam (← exportExpr cx t) (← exportExpr cx b) ⟨.never⟩
  | .forallE _ t b _ => return .forallE (← exportExpr cx t) (← exportExpr cx b) ⟨.never⟩
  | .letE _ t v b _ => return .letE (← exportExpr cx t) (← exportExpr cx v) (← exportExpr cx b)
  | .lit (.natVal n) => return .lit (.natVal n)
  | .lit (.strVal s) => return .lit (.strVal s)
  | .proj n i e => return .proj (← cx.context.name n) i (← exportExpr cx e)
  | .mdata _ _ => throw "source metadata requires an erasure/semantic contract"
  | .fvar _ => throw "free source variable"
  | .mvar _ => throw "source metavariable"

/-- Exact structural loose-variable bound, independent of cached Lean/Ix
metadata and without the packed-field saturation used by fast operations. -/
def sourceBvarBound : Lean.Expr → Nat
  | .bvar i => i + 1
  | .app f a => max (sourceBvarBound f) (sourceBvarBound a)
  | .lam _ t b _ | .forallE _ t b _ => max (sourceBvarBound t) (sourceBvarBound b - 1)
  | .letE _ t v b _ => max (max (sourceBvarBound t) (sourceBvarBound v)) (sourceBvarBound b - 1)
  | .proj _ _ e | .mdata _ e => sourceBvarBound e
  | _ => 0

/-- Name/level-parametric form of the independent structural exporter. Its
target instantiation is proved equal to `exportExpr` below; its source
instantiation uses original source names and no target artifact or map. -/
def exportExprWith (levelOf : Lean.Level → ExportM Kernel.Level)
    (nameOf : Lean.Name → ExportM Kernel.Name) : Lean.Expr → ExportM Kernel.Expr
  | .bvar i => return Kernel.Expr.mkBvar i
  | .sort u => return .sort (← levelOf u)
  | .const n us => return .const (← nameOf n) (← us.mapM levelOf)
  | .app f a => return .app (← exportExprWith levelOf nameOf f) (← exportExprWith levelOf nameOf a)
  | .lam _ t b _ => return .lam (← exportExprWith levelOf nameOf t) (← exportExprWith levelOf nameOf b) ⟨.never⟩
  | .forallE _ t b _ => return .forallE (← exportExprWith levelOf nameOf t) (← exportExprWith levelOf nameOf b) ⟨.never⟩
  | .letE _ t v b _ => do
    return .letE (← exportExprWith levelOf nameOf t)
      (← exportExprWith levelOf nameOf v) (← exportExprWith levelOf nameOf b)
  | .lit (.natVal n) => return .lit (.natVal n)
  | .lit (.strVal s) => return .lit (.strVal s)
  | .proj n i e => return .proj (← nameOf n) i (← exportExprWith levelOf nameOf e)
  | .mdata _ _ => throw "source metadata requires an erasure/semantic contract"
  | .fvar _ => throw "free source variable"
  | .mvar _ => throw "source metavariable"

theorem exportExprWith_target (cx : TermContext) (source : Lean.Expr) :
    exportExprWith (exportLevel cx) cx.context.name source = exportExpr cx source := by
  induction source
  case lit literal => cases literal <;> rfl
  all_goals simp_all [exportExprWith, exportExpr]

theorem exportExprWith_bvarBound {levelOf : Lean.Level → ExportM Kernel.Level}
    {nameOf : Lean.Name → ExportM Kernel.Name} {source : Lean.Expr} {result : Kernel.Expr}
    (exported : exportExprWith levelOf nameOf source = .ok result) :
    result.bvarBound = sourceBvarBound source := by
  induction source generalizing result
  case lit literal =>
    cases literal <;> simp only [exportExprWith, pure, Except.pure, Except.ok.injEq] at exported <;>
      subst result <;> rfl
  all_goals try simp only [exportExprWith, bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals try simp only [Except.ok.injEq] at exported
  all_goals try subst result
  all_goals simp_all [sourceBvarBound, Kernel.Expr.bvarBound]

/-- Original source telescope, with the same independently proved semantic
guard. This function takes no target pins, name map, or bytes. -/
def exportSourceLevel (params : List Lean.Name) (u : Lean.Level) : ExportM Kernel.Level := do
  let wire ← exportUniv params u
  let original ← importUniv (params.map sourceName) wire
  let candidate ← importUniv (params.map sourceName) (Ixon.canonUniv wire)
  checkedLevelImage original candidate

def exportSourceExpr (params : List Lean.Name) : Lean.Expr → ExportM Kernel.Expr :=
  exportExprWith (exportSourceLevel params) (fun n => .ok (sourceName n))

theorem exportSourceExpr_bvarBound {params : List Lean.Name} {source : Lean.Expr}
    {result : Kernel.Expr} (exported : exportSourceExpr params source = .ok result) :
    result.bvarBound = sourceBvarBound source :=
  exportExprWith_bvarBound exported

/-- Source installation uses the already proved level bridge, instantiated
with the original source telescope rather than any target map's telescope. -/
theorem exportSourceLevel_eval {params : List Lean.Name} {u : Lean.Level}
    {result : Kernel.Level} (exported : exportSourceLevel params u = .ok result)
    (φ : Lean.Name → Nat) (ρ : UInt64 → Nat) (ψ : Kernel.Name → Nat)
    (sourceAligned : ∀ n i, params.idxOf? n = some i → φ n = ρ i.toUInt64)
    (targetAligned : ∀ i n, (params.map sourceName)[i.toNat]? = some n → ρ i = ψ n) :
    sourceLevelEval φ u = some (Kernel.Level.Geran.levelEval ψ result) := by
  let cx : TermContext := ⟨⟨⟨[]⟩, [], {}⟩, params, params.map sourceName⟩
  exact exportLevel_eval (cx := cx) exported φ ρ ψ sourceAligned targetAligned

/-- Accepted export preserves the exact scope bound, including under nested
binders and lets. Universe normalization cannot alter term-variable scope. -/
theorem exportExpr_bvarBound {cx : TermContext} {source : Lean.Expr} {result : Kernel.Expr}
    (exported : exportExpr cx source = .ok result) :
    result.bvarBound = sourceBvarBound source := by
  induction source generalizing result
  case lit literal =>
    cases literal <;> simp only [exportExpr, pure, Except.pure, Except.ok.injEq] at exported <;>
      subst result <;> rfl
  all_goals try simp only [exportExpr, bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals try simp only [Except.ok.injEq] at exported
  all_goals try subst result
  all_goals simp_all [sourceBvarBound, Kernel.Expr.bvarBound]

theorem exportExpr_scoped {cx : TermContext} {source : Lean.Expr} {result : Kernel.Expr}
    (exported : exportExpr cx source = .ok result) {depth : Nat}
    (scopeBound : sourceBvarBound source ≤ depth) : result.looseBVarsBounded depth = true := by
  apply Kernel.Expr.looseBVarsBounded_iff.mpr
  rw [exportExpr_bvarBound exported]
  exact scopeBound

theorem exportExpr_noFvar {cx : TermContext} {source : Lean.Expr} {result : Kernel.Expr}
    (exported : exportExpr cx source = .ok result) : result.hasFvar = false := by
  induction source generalizing result
  case lit literal =>
    cases literal <;> simp only [exportExpr, pure, Except.pure, Except.ok.injEq] at exported <;>
      subst result <;> rfl
  all_goals try simp only [exportExpr, bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals try simp only [Except.ok.injEq] at exported
  all_goals try subst result
  all_goals simp_all [Kernel.Expr.hasFvar]

/-- Structural lifting on the independent source view. This is a reference
operation, not an assumed refinement of the compiler's optimized rewrites. -/
def sourceLift (amount : Nat) : Nat → Lean.Expr → Lean.Expr
  | cutoff, .bvar i => if i ≥ cutoff then .bvar (i + amount) else .bvar i
  | cutoff, .app f a => .app (sourceLift amount cutoff f) (sourceLift amount cutoff a)
  | cutoff, .lam n t b bi =>
    .lam n (sourceLift amount cutoff t) (sourceLift amount (cutoff + 1) b) bi
  | cutoff, .forallE n t b bi =>
    .forallE n (sourceLift amount cutoff t) (sourceLift amount (cutoff + 1) b) bi
  | cutoff, .letE n t v b nd =>
    .letE n (sourceLift amount cutoff t) (sourceLift amount cutoff v)
      (sourceLift amount (cutoff + 1) b) nd
  | cutoff, .proj n i e => .proj n i (sourceLift amount cutoff e)
  | cutoff, .mdata md e => .mdata md (sourceLift amount cutoff e)
  | _, e => e

theorem exportExpr_lift {cx : TermContext} {source : Lean.Expr} {result : Kernel.Expr}
    (exported : exportExpr cx source = .ok result) (amount cutoff : Nat) :
    exportExpr cx (sourceLift amount cutoff source) =
      .ok (Kernel.Expr.liftLooseBVars amount cutoff result) := by
  induction source generalizing result cutoff
  case bvar i =>
    simp [exportExpr, pure, Except.pure] at exported
    subst result
    by_cases hi : i ≥ cutoff <;>
      simp [sourceLift, hi, exportExpr, Kernel.Expr.liftLooseBVars, pure, Except.pure]
  case lit literal =>
    cases literal <;> simp only [exportExpr, pure, Except.pure, Except.ok.injEq] at exported <;>
      subst result <;> rfl
  all_goals try simp only [exportExpr, bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals try simp only [Except.ok.injEq] at exported
  all_goals try subst result
  all_goals simp_all [sourceLift, Kernel.Expr.liftLooseBVars, exportExpr, bind,
    Except.bind, pure, Except.pure]

/-- Capture-avoiding substitution on the independent source view. The
replacement is lifted when crossing binders; open replacements are allowed. -/
def sourceInstantiate (replacement : Lean.Expr) : Nat → Lean.Expr → Lean.Expr
  | depth, .bvar i =>
    if i = depth then sourceLift depth 0 replacement
    else if i > depth then .bvar (i - 1) else .bvar i
  | depth, .app f a => .app (sourceInstantiate replacement depth f) (sourceInstantiate replacement depth a)
  | depth, .lam n t b bi =>
    .lam n (sourceInstantiate replacement depth t) (sourceInstantiate replacement (depth + 1) b) bi
  | depth, .forallE n t b bi =>
    .forallE n (sourceInstantiate replacement depth t) (sourceInstantiate replacement (depth + 1) b) bi
  | depth, .letE n t v b nd =>
    .letE n (sourceInstantiate replacement depth t) (sourceInstantiate replacement depth v)
      (sourceInstantiate replacement (depth + 1) b) nd
  | depth, .proj n i e => .proj n i (sourceInstantiate replacement depth e)
  | depth, .mdata md e => .mdata md (sourceInstantiate replacement depth e)
  | _, e => e

theorem exportExpr_instantiate {cx : TermContext} {source replacement : Lean.Expr}
    {result targetReplacement : Kernel.Expr}
    (exported : exportExpr cx source = .ok result)
    (replacementExported : exportExpr cx replacement = .ok targetReplacement) (depth : Nat) :
    exportExpr cx (sourceInstantiate replacement depth source) =
      .ok (Kernel.Expr.instantiate1Lift result targetReplacement depth) := by
  induction source generalizing result depth
  case bvar i =>
    simp [exportExpr, pure, Except.pure] at exported
    subst result
    by_cases equal : i = depth
    · simp [sourceInstantiate, equal, Kernel.Expr.instantiate1Lift,
        exportExpr_lift replacementExported]
    · by_cases greater : i > depth <;>
        simp [sourceInstantiate, equal, greater, Kernel.Expr.instantiate1Lift,
          exportExpr, pure, Except.pure]
  case lit literal =>
    cases literal <;> simp only [exportExpr, pure, Except.pure, Except.ok.injEq] at exported <;>
      subst result <;> rfl
  all_goals try simp only [exportExpr, bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals try simp only [Except.ok.injEq] at exported
  all_goals try subst result
  all_goals simp_all [sourceInstantiate, Kernel.Expr.instantiate1Lift, exportExpr, bind,
    Except.bind, pure, Except.pure]

/-- Rename constant and projection-owner identities, leaving binder labels
and universe parameters in their distinct namespaces. -/
def sourceRename (rename : Lean.Name → Lean.Name) : Lean.Expr → Lean.Expr
  | .const n us => .const (rename n) us
  | .app f a => .app (sourceRename rename f) (sourceRename rename a)
  | .lam n t b bi => .lam n (sourceRename rename t) (sourceRename rename b) bi
  | .forallE n t b bi => .forallE n (sourceRename rename t) (sourceRename rename b) bi
  | .letE n t v b nd => .letE n (sourceRename rename t) (sourceRename rename v) (sourceRename rename b) nd
  | .proj n i e => .proj (rename n) i (sourceRename rename e)
  | .mdata md e => .mdata md (sourceRename rename e)
  | e => e

/-- Name renaming commutes with successful export under an explicit map
square and unchanged universe telescopes. Neither renaming is assumed
injective; compatible many-to-one fibers remain a separate map obligation. -/
def kernelRenameAll (rename : Kernel.Name → Kernel.Name) : Kernel.Expr → Kernel.Expr
  | .bvar i => .bvar i
  | .fvar i t => .fvar i (kernelRenameAll rename t)
  | .sort u => .sort u
  | .const n us => .const (rename n) us
  | .app f a => .app (kernelRenameAll rename f) (kernelRenameAll rename a)
  | .lam t b m => .lam (kernelRenameAll rename t) (kernelRenameAll rename b) m
  | .forallE t b m => .forallE (kernelRenameAll rename t) (kernelRenameAll rename b) m
  | .letE t v b => .letE (kernelRenameAll rename t) (kernelRenameAll rename v) (kernelRenameAll rename b)
  | .lit l => .lit l
  | .proj n i e => .proj (rename n) i (kernelRenameAll rename e)

def ProjectionOwnersFixed (rename : Kernel.Name → Kernel.Name) : Kernel.Expr → Prop
  | .proj n _ e => rename n = n ∧ ProjectionOwnersFixed rename e
  | .fvar _ t => ProjectionOwnersFixed rename t
  | .app f a => ProjectionOwnersFixed rename f ∧ ProjectionOwnersFixed rename a
  | .lam t b _ | .forallE t b _ => ProjectionOwnersFixed rename t ∧ ProjectionOwnersFixed rename b
  | .letE t v b => ProjectionOwnersFixed rename t ∧ ProjectionOwnersFixed rename v ∧ ProjectionOwnersFixed rename b
  | _ => True

theorem kernelRenameAll_eq_renameConsts (rename : Kernel.Name → Kernel.Name) (e : Kernel.Expr)
    (stable : ProjectionOwnersFixed rename e) :
    kernelRenameAll rename e = Kernel.Expr.renameConsts rename e := by
  induction e <;> simp_all [ProjectionOwnersFixed, kernelRenameAll, Kernel.Expr.renameConsts]

/-- This uses full structural renaming. `Kernel.Expr.renameConsts` has a
different, deliberate contract: it leaves projection owners unchanged.
Reusing that kernel helper requires a projection-owner stability premise. -/
theorem exportExpr_rename {cx cy : TermContext} {source : Lean.Expr} {result : Kernel.Expr}
    (sourceNames : Lean.Name → Lean.Name) (targetNames : Kernel.Name → Kernel.Name)
    (names : ∀ n k, cx.context.name n = .ok k →
      cy.context.name (sourceNames n) = .ok (targetNames k))
    (sourceLevels : cy.sourceLevels = cx.sourceLevels)
    (targetLevels : cy.targetLevels = cx.targetLevels)
    (exported : exportExpr cx source = .ok result) :
    exportExpr cy (sourceRename sourceNames source) = .ok (kernelRenameAll targetNames result) := by
  have levels : exportLevel cy = exportLevel cx := by
    funext u
    simp only [exportLevel, sourceLevels, targetLevels]
  induction source generalizing result
  case lit literal =>
    cases literal <;> simp only [exportExpr, pure, Except.pure, Except.ok.injEq] at exported <;>
      subst result <;> rfl
  all_goals try simp only [exportExpr, bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals try simp only [Except.ok.injEq] at exported
  all_goals try subst result
  all_goals simp_all [sourceRename, kernelRenameAll, exportExpr, bind,
    Except.bind, pure, Except.pure]

/-- All fields emitted for one source-associated reader constant. Source
block membership and safety remain explicit source-domain obligations. -/
inductive DirectEntry where
  | axiom (val : Kernel.ConstantVal)
  | defn (val : Kernel.ConstantVal) (value : Kernel.Expr) (hint : Kernel.ReducibilityHint)
  | thm (val : Kernel.ConstantVal) (value : Kernel.Expr)
  | opaque (val : Kernel.ConstantVal) (value : Kernel.Expr)
  | quot (kind : Kernel.QuotKind) (val : Kernel.ConstantVal)
  | induct (val : Kernel.ConstantVal) (numParams : Nat)
  | ctor (val : Kernel.ConstantVal) (numParams numFields : Nat)
  | recursor (val : Kernel.ConstantVal) (majorIdx rulePrefix : Nat) (rules : List Kernel.RecRule)
  deriving DecidableEq

def exportHint : Lean.ReducibilityHints → Kernel.ReducibilityHint
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular h.toNat

def exportQuot : Lean.QuotKind → Kernel.QuotKind
  | .type => .type | .ctor => .ctor | .lift => .lift | .ind => .ind

def sourceSupported : Lean.ConstantInfo → Bool
  | .defnInfo v => match v.safety with | .safe => true | _ => false
  | .opaqueInfo v => !v.isUnsafe
  | .axiomInfo v => !v.isUnsafe
  | .inductInfo v => !v.isUnsafe
  | .ctorInfo v => !v.isUnsafe
  | .recInfo v => !v.isUnsafe
  | _ => true

def directExport (cx : ExportContext) (ci : Lean.ConstantInfo) : ExportM DirectEntry := do
  unless sourceSupported ci do throw s!"unsupported source safety: {ci.name}"
  unless ci.levelParams.eraseDups.length == ci.levelParams.length do
    throw s!"duplicate source universe parameters: {ci.name}"
  let levels ← cx.levels ci
  let tc : TermContext := ⟨cx, ci.levelParams, levels⟩
  let val : Kernel.ConstantVal := ⟨← cx.name ci.name, levels, ← exportExpr tc ci.type⟩
  match ci with
  | .axiomInfo _ => return .axiom val
  | .defnInfo v => return .defn val (← exportExpr tc v.value) (exportHint v.hints)
  | .thmInfo v => return .thm val (← exportExpr tc v.value)
  | .opaqueInfo v => return .opaque val (← exportExpr tc v.value)
  | .quotInfo v => return .quot (exportQuot v.kind) val
  | .inductInfo v => return .induct val v.numParams
  | .ctorInfo v => return .ctor val v.numParams v.numFields
  | .recInfo v =>
    let rules ← v.rules.mapM fun r => do
      return Kernel.RecRule.mk (← cx.name r.ctor) r.nfields 0 .inert
        (← exportExpr tc r.rhs) false false false
    return .recursor val (v.numParams + v.numMotives + v.numMinors + v.numIndices)
      (v.numParams + v.numMotives + v.numMinors) rules

/-! ## Independent source declaration export

This route has no target map, target records, reader state or target
projection rewrite. It preserves original source names and telescopes.
-/

def exportSourceRule (params : List Lean.Name) (rule : Lean.RecursorRule) : ExportM Kernel.RecRule := do
  return Kernel.RecRule.mk (sourceName rule.ctor) rule.nfields 0 .inert
    (← exportSourceExpr params rule.rhs) false false false

def SourceRuleImage (params : List Lean.Name) (source : Lean.RecursorRule)
    (target : Kernel.RecRule) : Prop :=
  target.ctor = sourceName source.ctor ∧ target.nfields = source.nfields ∧
  exportSourceExpr params source.rhs = .ok target.rhs ∧
  target.ctorParams = 0 ∧ target.fire = .inert ∧ target.k = false ∧
  target.eta = false ∧ target.paramsBlind = false

theorem exportSourceRule_sound {params : List Lean.Name} {source : Lean.RecursorRule}
    {target : Kernel.RecRule} (exported : exportSourceRule params source = .ok target) :
    SourceRuleImage params source target := by
  cases body : exportSourceExpr params source.rhs with
  | error reason => simp [exportSourceRule, body, bind, Except.bind] at exported
  | ok rhs =>
    simp only [exportSourceRule, body, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at exported
    subst target
    simp [SourceRuleImage, body]

/-- Rules are related in their original positions, not merely as sets. -/
inductive SourceRulesImage (params : List Lean.Name) :
    List Lean.RecursorRule → List Kernel.RecRule → Prop
  | nil : SourceRulesImage params [] []
  | cons {source target sources targets} : SourceRuleImage params source target →
      SourceRulesImage params sources targets → SourceRulesImage params (source :: sources) (target :: targets)

theorem exportSourceRules_positions {params : List Lean.Name} {source : List Lean.RecursorRule}
    {target : List Kernel.RecRule} (exported : source.mapM (exportSourceRule params) = .ok target) :
    SourceRulesImage params source target := by
  induction source generalizing target with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at exported
    subst target
    exact .nil
  | cons rule rules ih =>
    cases hr : exportSourceRule params rule <;> cases hs : rules.mapM (exportSourceRule params)
    all_goals simp only [List.mapM_cons, hr, hs, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at exported
    all_goals try contradiction
    subst target
    exact .cons (exportSourceRule_sound hr) (ih hs)

def exportSourceEntry (ci : Lean.ConstantInfo) : ExportM DirectEntry := do
  unless sourceSupported ci do throw s!"unsupported source safety: {ci.name}"
  unless ci.levelParams.eraseDups.length == ci.levelParams.length do
    throw s!"duplicate source universe parameters: {ci.name}"
  let cv : Kernel.ConstantVal := ⟨sourceName ci.name, ci.levelParams.map sourceName,
    ← exportSourceExpr ci.levelParams ci.type⟩
  match ci with
  | .axiomInfo _ => return .axiom cv
  | .defnInfo v => return .defn cv (← exportSourceExpr ci.levelParams v.value) (exportHint v.hints)
  | .thmInfo v => return .thm cv (← exportSourceExpr ci.levelParams v.value)
  | .opaqueInfo v => return .opaque cv (← exportSourceExpr ci.levelParams v.value)
  | .quotInfo v => return .quot (exportQuot v.kind) cv
  | .inductInfo v => return .induct cv v.numParams
  | .ctorInfo v => return .ctor cv v.numParams v.numFields
  | .recInfo v =>
    let rules ← v.rules.mapM (exportSourceRule ci.levelParams)
    return .recursor cv (v.numParams + v.numMotives + v.numMinors + v.numIndices)
      (v.numParams + v.numMotives + v.numMinors) rules

/-- The source-facing declaration header records original identity and
telescope plus an independently translated complete type. -/
def SourceValImage (source : Lean.ConstantVal) (target : Kernel.ConstantVal) : Prop :=
  target.name = sourceName source.name ∧
  target.levelParams = source.levelParams.map sourceName ∧
  exportSourceExpr source.levelParams source.type = .ok target.type

theorem exportSourceEntry_defn {source : Lean.DefinitionVal} {header : Kernel.ConstantVal}
    {body : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (exported : exportSourceEntry (.defnInfo source) = .ok (.defn header body hint)) :
    SourceValImage source.toConstantVal header ∧
      exportSourceExpr source.levelParams source.value = .ok body ∧ hint = exportHint source.hints := by
  cases ht : exportSourceExpr source.levelParams source.type <;>
    cases hb : exportSourceExpr source.levelParams source.value
  all_goals simp only [exportSourceEntry, Lean.ConstantInfo.levelParams,
    Lean.ConstantInfo.type, Lean.ConstantInfo.name, Lean.ConstantInfo.toConstantVal, ht, hb,
    bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals simp_all [SourceValImage]
  rcases exported with ⟨rfl, _, _⟩
  exact ⟨rfl, rfl, rfl⟩

/-- A theorem body is checked and related structurally; this does not make
it a transparent semantic definition in the installed model. -/
theorem exportSourceEntry_thm {source : Lean.TheoremVal} {header : Kernel.ConstantVal}
    {body : Kernel.Expr}
    (exported : exportSourceEntry (.thmInfo source) = .ok (.thm header body)) :
    SourceValImage source.toConstantVal header ∧
      exportSourceExpr source.levelParams source.value = .ok body := by
  cases ht : exportSourceExpr source.levelParams source.type <;>
    cases hb : exportSourceExpr source.levelParams source.value
  all_goals simp only [exportSourceEntry, Lean.ConstantInfo.levelParams,
    Lean.ConstantInfo.type, Lean.ConstantInfo.name, Lean.ConstantInfo.toConstantVal, ht, hb,
    bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals simp_all [SourceValImage]
  rcases exported with ⟨rfl, _⟩
  exact ⟨rfl, rfl, rfl⟩

/-- Opaque bodies remain checking evidence, not an unfolding equation. -/
theorem exportSourceEntry_opaque {source : Lean.OpaqueVal} {header : Kernel.ConstantVal}
    {body : Kernel.Expr}
    (exported : exportSourceEntry (.opaqueInfo source) = .ok (.opaque header body)) :
    SourceValImage source.toConstantVal header ∧
      exportSourceExpr source.levelParams source.value = .ok body := by
  cases ht : exportSourceExpr source.levelParams source.type <;>
    cases hb : exportSourceExpr source.levelParams source.value
  all_goals simp only [exportSourceEntry, Lean.ConstantInfo.levelParams,
    Lean.ConstantInfo.type, Lean.ConstantInfo.name, Lean.ConstantInfo.toConstantVal, ht, hb,
    bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals simp_all [SourceValImage]
  rcases exported with ⟨rfl, _⟩
  exact ⟨rfl, rfl, rfl⟩

theorem exportSourceEntry_recursor {source : Lean.RecursorVal} {header : Kernel.ConstantVal}
    {major rulePrefix : Nat} {rules : List Kernel.RecRule}
    (exported : exportSourceEntry (.recInfo source) = .ok (.recursor header major rulePrefix rules)) :
    SourceValImage source.toConstantVal header ∧
      major = source.numParams + source.numMotives + source.numMinors + source.numIndices ∧
      rulePrefix = source.numParams + source.numMotives + source.numMinors ∧
      SourceRulesImage source.levelParams source.rules rules := by
  cases ht : exportSourceExpr source.levelParams source.type <;>
    cases hr : source.rules.mapM (exportSourceRule source.levelParams)
  all_goals simp only [exportSourceEntry, Lean.ConstantInfo.levelParams,
    Lean.ConstantInfo.type, Lean.ConstantInfo.name, Lean.ConstantInfo.toConstantVal, ht, hr,
    bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals try contradiction
  all_goals simp at exported
  rcases exported with ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨⟨rfl, rfl, ht⟩, rfl, rfl, exportSourceRules_positions hr⟩

theorem exportSourceEntry_axiom {source : Lean.AxiomVal} {header : Kernel.ConstantVal}
    (exported : exportSourceEntry (.axiomInfo source) = .ok (.axiom header)) :
    SourceValImage source.toConstantVal header := by
  cases ht : exportSourceExpr source.levelParams source.type
  all_goals simp only [exportSourceEntry, Lean.ConstantInfo.levelParams,
    Lean.ConstantInfo.type, Lean.ConstantInfo.name, Lean.ConstantInfo.toConstantVal, ht,
    bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals try contradiction
  all_goals simp at exported
  subst header
  exact ⟨rfl, rfl, ht⟩

theorem exportSourceEntry_inductive {source : Lean.InductiveVal} {header : Kernel.ConstantVal}
    {numParams : Nat}
    (exported : exportSourceEntry (.inductInfo source) = .ok (.induct header numParams)) :
    SourceValImage source.toConstantVal header ∧ numParams = source.numParams := by
  cases ht : exportSourceExpr source.levelParams source.type
  all_goals simp only [exportSourceEntry, Lean.ConstantInfo.levelParams,
    Lean.ConstantInfo.type, Lean.ConstantInfo.name, Lean.ConstantInfo.toConstantVal, ht,
    bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals try contradiction
  all_goals simp at exported
  rcases exported with ⟨rfl, rfl⟩
  exact ⟨⟨rfl, rfl, ht⟩, rfl⟩

theorem exportSourceEntry_constructor {source : Lean.ConstructorVal} {header : Kernel.ConstantVal}
    {numParams numFields : Nat}
    (exported : exportSourceEntry (.ctorInfo source) = .ok (.ctor header numParams numFields)) :
    SourceValImage source.toConstantVal header ∧
      numParams = source.numParams ∧ numFields = source.numFields := by
  cases ht : exportSourceExpr source.levelParams source.type
  all_goals simp only [exportSourceEntry, Lean.ConstantInfo.levelParams,
    Lean.ConstantInfo.type, Lean.ConstantInfo.name, Lean.ConstantInfo.toConstantVal, ht,
    bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals try contradiction
  all_goals simp at exported
  rcases exported with ⟨rfl, rfl, rfl⟩
  exact ⟨⟨rfl, rfl, ht⟩, rfl, rfl⟩

theorem exportSourceEntry_quotient {source : Lean.QuotVal} {header : Kernel.ConstantVal}
    {kind : Kernel.QuotKind}
    (exported : exportSourceEntry (.quotInfo source) = .ok (.quot kind header)) :
    SourceValImage source.toConstantVal header ∧ kind = exportQuot source.kind := by
  cases ht : exportSourceExpr source.levelParams source.type
  all_goals simp only [exportSourceEntry, Lean.ConstantInfo.levelParams,
    Lean.ConstantInfo.type, Lean.ConstantInfo.name, Lean.ConstantInfo.toConstantVal, ht,
    bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals try contradiction
  all_goals simp at exported
  rcases exported with ⟨rfl, rfl⟩
  exact ⟨⟨rfl, rfl, ht⟩, rfl⟩

structure SourceDeclGroup where
  members : List Lean.Name
  dependencies : List Lean.Name
  declaration : Kernel.Declaration

/-- Scheduling uses genuine type/value/rule references. Source `.all` is
closure/group evidence, not an artificial cycle between acyclic definitions. -/
def sourceTermRefs (ci : Lean.ConstantInfo) : List Lean.Name :=
  exprRefs ci.type ++ match ci with
  | .defnInfo v => exprRefs v.value
  | .thmInfo v => exprRefs v.value
  | .opaqueInfo v => exprRefs v.value
  | .recInfo v => v.rules.flatMap (fun r => r.ctor :: exprRefs r.rhs)
  | .ctorInfo v => [v.induct]
  | _ => []

def sourceGroupDependencies (s : Source) (members : List Lean.Name) : ExportM (List Lean.Name) := do
  let refs ← members.mapM fun n => do
    let some ci := s.find n | throw s!"source group member is missing: {n}"
    return sourceTermRefs ci
  return (refs.flatten.filter fun n => !members.contains n).eraseDups

def exportSourceInductive (s : Source) (owner : Lean.InductiveVal) : ExportM SourceDeclGroup := do
  unless owner.all.contains owner.name do throw "source inductive is absent from its own group"
  let mut names := owner.all
  let mut types := []
  let mut ctors := []
  for n in owner.all do
    let some (.inductInfo iv) := s.find n | throw s!"source inductive member missing: {n}"
    unless iv.all == owner.all && iv.numParams == owner.numParams do
      throw s!"inconsistent source inductive group: {n}"
    let .induct cv _ ← exportSourceEntry (.inductInfo iv) | throw "source inductive kind mismatch"
    types := types ++ [Kernel.ConstantInfo.indInfo cv {}]
    names := names ++ iv.ctors
    for (name, index) in iv.ctors.zipIdx do
      let some (.ctorInfo ctor) := s.find name | throw s!"source constructor missing: {name}"
      unless ctor.induct == n && ctor.cidx == index && ctor.numParams == iv.numParams do
        throw s!"source constructor ownership mismatch: {name}"
      let .ctor cv np nf ← exportSourceEntry (.ctorInfo ctor) | throw "source constructor kind mismatch"
      ctors := ctors ++ [Kernel.ConstantInfo.ctorInfo cv np nf]
  let recNames := owner.all.map (·.str "rec") ++
    (List.range owner.numNested).filterMap (fun i => owner.all.head?.map (·.str s!"rec_{i + 1}"))
  let mut recs := []
  for n in recNames do
    let some (.recInfo rv) := s.find n | throw s!"source recursor missing: {n}"
    unless rv.all == owner.all do throw s!"source recursor group mismatch: {n}"
    let .recursor cv major numArgs rules ← exportSourceEntry (.recInfo rv)
      | throw "source recursor kind mismatch"
    recs := recs ++ [Kernel.ConstantInfo.recInfo cv major numArgs rules]
  names := names ++ recNames
  return ⟨names, ← sourceGroupDependencies s names, .indDecl (types ++ ctors ++ recs) owner.numParams⟩

def buildSourceGroups (s : Source) : ExportM (List SourceDeclGroup) := do
  let mut groups := []
  for ci in s.declarations do
    match ci with
    | .inductInfo iv =>
      if iv.all.head? == some iv.name then groups := groups ++ [← exportSourceInductive s iv]
    | .ctorInfo _ | .recInfo _ => pure ()
    | _ =>
      let entry ← exportSourceEntry ci
      let declaration ← match entry with
        | .axiom cv => pure (.axiomDecl cv)
        | .defn cv value hint => pure (.defnDecl cv value hint)
        | .thm cv value => pure (.thmDecl cv value)
        | .opaque cv value => pure (.opaqueDecl cv value)
        | .quot k cv => pure (.quotDecl k cv)
        | _ => throw "source singleton kind mismatch"
      groups := groups ++ [⟨[ci.name], ← sourceGroupDependencies s [ci.name], declaration⟩]
  return groups

/-- Every source name belongs to exactly one exported declaration group.
This concerns original identities; it imposes no target-address injectivity. -/
def SourceGroupsCover (s : Source) (groups : List SourceDeclGroup) : Prop :=
  let members := groups.flatMap SourceDeclGroup.members
  members.Nodup ∧ (∀ n ∈ s.names, n ∈ members) ∧ (∀ n ∈ members, n ∈ s.names) ∧
    ∀ group ∈ groups, group.declaration.names = group.members.map sourceName

instance (s : Source) (groups : List SourceDeclGroup) : Decidable (SourceGroupsCover s groups) :=
  inferInstanceAs (Decidable (
    (groups.flatMap SourceDeclGroup.members).Nodup ∧
    (∀ n ∈ s.names, n ∈ groups.flatMap SourceDeclGroup.members) ∧
    (∀ n ∈ groups.flatMap SourceDeclGroup.members, n ∈ s.names) ∧
    (∀ group ∈ groups, group.declaration.names = group.members.map sourceName)))

def validateSourceGroups (s : Source) (groups : List SourceDeclGroup) :
    ExportM (List SourceDeclGroup) :=
  if SourceGroupsCover s groups then .ok groups
  else .error "source declaration groups do not cover the exact source inventory"

theorem validateSourceGroups_sound {s : Source} {proposed result : List SourceDeclGroup}
    (accepted : validateSourceGroups s proposed = .ok result) : SourceGroupsCover s result := by
  unfold validateSourceGroups at accepted
  split at accepted
  next covered => cases accepted; exact covered
  next => contradiction

def exportSourceGroups (s : Source) : ExportM (List SourceDeclGroup) := do
  validateSourceGroups s (← buildSourceGroups s)

theorem exportSourceGroups_cover {s : Source} {groups : List SourceDeclGroup}
    (exported : exportSourceGroups s = .ok groups) : SourceGroupsCover s groups := by
  cases built : buildSourceGroups s with
  | error reason => simp [exportSourceGroups, built, bind, Except.bind] at exported
  | ok proposed =>
    exact validateSourceGroups_sound (by
      simpa only [exportSourceGroups, built, bind, Except.bind] using exported)

/-- Deterministic source-only dependency scheduling. An unresolved dependency
or cycle is reported, never repaired by consulting target order or bodies. -/
def orderSourceGroups : Nat → List SourceDeclGroup → List Lean.Name → List Kernel.Declaration →
    ExportM (List Kernel.Declaration)
  | _, [], _, output => .ok output
  | 0, _ :: _, _, _ => .error "source declaration scheduling budget exhausted"
  | fuel + 1, groups@(_ :: _), available, output => do
    let ready := groups.filter fun g => g.dependencies.all available.contains
    if ready.isEmpty then throw "source declaration dependencies are unresolved or cyclic"
    let pending := groups.filter fun g => !g.dependencies.all available.contains
    orderSourceGroups fuel pending (available ++ ready.flatMap SourceDeclGroup.members)
      (output ++ ready.map SourceDeclGroup.declaration)

/-- Successful scheduling preserves every complete declaration, including
all type/value/member/rule fields, with multiplicity. It only changes order. -/
theorem orderSourceGroups_perm {fuel : Nat} {groups : List SourceDeclGroup}
    {available : List Lean.Name} {output result : List Kernel.Declaration}
    (ordered : orderSourceGroups fuel groups available output = .ok result) :
    result.Perm (output ++ groups.map SourceDeclGroup.declaration) := by
  induction fuel generalizing groups available output result with
  | zero =>
    cases groups with
    | nil =>
      have same : output = result := by simpa [orderSourceGroups] using ordered
      subst result
      simp
    | cons group groups => simp [orderSourceGroups] at ordered
  | succ fuel ih =>
    cases groups with
    | nil =>
      have same : output = result := by simpa [orderSourceGroups] using ordered
      subst result
      simp
    | cons group groups =>
      simp only [orderSourceGroups, bind, Except.bind] at ordered
      split at ordered
      next => contradiction
      next =>
        have previous := ih ordered
        have partition := (List.filter_append_perm
          (fun g : SourceDeclGroup => g.dependencies.all available.contains)
          (group :: groups)).map SourceDeclGroup.declaration
        exact previous.trans (by
          simpa only [List.map_append, List.append_assoc] using
            (List.Perm.refl output).append partition)

def exportSourceDeclarations (s : Source) : ExportM (Array Kernel.Declaration) := do
  let groups ← exportSourceGroups s
  return (← orderSourceGroups (groups.length + 1) groups [] []).toArray

theorem exportSourceDeclarations_groups {s : Source} {declarations : Array Kernel.Declaration}
    (exported : exportSourceDeclarations s = .ok declarations) :
    ∃ groups, exportSourceGroups s = .ok groups ∧ SourceGroupsCover s groups ∧
      orderSourceGroups (groups.length + 1) groups [] [] = .ok declarations.toList := by
  cases hg : exportSourceGroups s with
  | error reason => simp [exportSourceDeclarations, hg, bind, Except.bind] at exported
  | ok groups =>
    cases ho : orderSourceGroups (groups.length + 1) groups [] [] with
    | error reason => simp [exportSourceDeclarations, hg, ho, bind, Except.bind] at exported
    | ok ordered =>
      have hd : ordered.toArray = declarations := by
        simpa only [exportSourceDeclarations, hg, ho, bind, Except.bind, pure,
          Except.pure, Except.ok.injEq] using exported
      subst declarations
      exact ⟨groups, rfl, exportSourceGroups_cover hg, by simpa using ho⟩

/-! ## Representation-bridge spike

These structural functions never consult cached hashes or the compiler's
hash-based equality. They define the initial supported representation
relation; substitution/renaming and semantic preservation remain separately
listed proof obligations. -/

def ixName : Ix.Name → Lean.Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (ixName p) s
  | .num p i _ => .num (ixName p) i

def ixLevel : Ix.Level → ExportM Lean.Level
  | .zero _ => return .zero
  | .succ u _ => return .succ (← ixLevel u)
  | .max u v _ => return .max (← ixLevel u) (← ixLevel v)
  | .imax u v _ => return .imax (← ixLevel u) (← ixLevel v)
  | .param n _ => return .param (ixName n)
  | .mvar .. => throw "Ix universe metavariable"

def ixLevelEval (φ : Lean.Name → Nat) : Ix.Level → Option Nat
  | .zero _ => some 0
  | .succ u _ => return (← ixLevelEval φ u) + 1
  | .max u v _ => return max (← ixLevelEval φ u) (← ixLevelEval φ v)
  | .imax u v _ => do
    let a ← ixLevelEval φ u
    let b ← ixLevelEval φ v
    return if b = 0 then 0 else max a b
  | .param n _ => some (φ (ixName n))
  | .mvar .. => none

theorem ixLevel_eval {source : Ix.Level} {result : Lean.Level}
    (translated : ixLevel source = .ok result) (φ : Lean.Name → Nat) :
    sourceLevelEval φ result = ixLevelEval φ source := by
  induction source generalizing result
  all_goals try simp only [ixLevel, bind, Except.bind, pure, Except.pure] at translated
  all_goals repeat' split at translated
  all_goals try simp only [Except.ok.injEq] at translated
  all_goals try subst result
  all_goals simp_all [sourceLevelEval, ixLevelEval]

/-- The cached Ix level participates in the same source/wire/target semantic
bridge through its structural view; no cached level or name hash is a proof. -/
theorem ixLevel_export_eval {cx : TermContext} {source : Ix.Level} {view : Lean.Level}
    {result : Kernel.Level} (translated : ixLevel source = .ok view)
    (exported : exportLevel cx view = .ok result)
    (φ : Lean.Name → Nat) (ρ : UInt64 → Nat) (ψ : Kernel.Name → Nat)
    (sourceAligned : ∀ n i, cx.sourceLevels.idxOf? n = some i → φ n = ρ i.toUInt64)
    (targetAligned : ∀ i n, cx.targetLevels[i.toNat]? = some n → ρ i = ψ n) :
    ixLevelEval φ source = some (Kernel.Level.Geran.levelEval ψ result) := by
  rw [← ixLevel_eval translated φ]
  exact exportLevel_eval exported φ ρ ψ sourceAligned targetAligned

def ixExpr : Ix.Expr → ExportM Lean.Expr
  | .bvar i _ => return .bvar i
  | .sort u _ => return .sort (← ixLevel u)
  | .const n us _ => return .const (ixName n) (← us.toList.mapM ixLevel)
  | .app f a _ => return .app (← ixExpr f) (← ixExpr a)
  | .lam n t b info _ => return .lam (ixName n) (← ixExpr t) (← ixExpr b) info
  | .forallE n t b info _ => return .forallE (ixName n) (← ixExpr t) (← ixExpr b) info
  | .letE n t v b nonDep _ => do
    return .letE (ixName n) (← ixExpr t) (← ixExpr v) (← ixExpr b) nonDep
  | .lit v _ => return .lit v
  | .proj n i e _ => return .proj (ixName n) i (← ixExpr e)
  | .mdata .. => throw "Ix metadata requires an erasure/semantic contract"
  | .fvar .. => throw "Ix free variable"
  | .mvar .. => throw "Ix metavariable"

def ixToKernel (cx : TermContext) (e : Ix.Expr) : ExportM Kernel.Expr := do
  exportExpr cx (← ixExpr e)

def ixBvarBound : Ix.Expr → Nat
  | .bvar i _ => i + 1
  | .app f a _ => max (ixBvarBound f) (ixBvarBound a)
  | .lam _ t b _ _ | .forallE _ t b _ _ => max (ixBvarBound t) (ixBvarBound b - 1)
  | .letE _ t v b _ _ => max (max (ixBvarBound t) (ixBvarBound v)) (ixBvarBound b - 1)
  | .proj _ _ e _ | .mdata _ e _ => ixBvarBound e
  | _ => 0

theorem ixExpr_bvarBound {source : Ix.Expr} {result : Lean.Expr}
    (exported : ixExpr source = .ok result) :
    sourceBvarBound result = ixBvarBound source := by
  induction source generalizing result
  all_goals try simp only [ixExpr, bind, Except.bind, pure, Except.pure] at exported
  all_goals repeat' split at exported
  all_goals try simp only [Except.ok.injEq] at exported
  all_goals try subst result
  all_goals simp_all [sourceBvarBound, ixBvarBound]

theorem ixToKernel_bvarBound {cx : TermContext} {source : Ix.Expr} {result : Kernel.Expr}
    (exported : ixToKernel cx source = .ok result) :
    result.bvarBound = ixBvarBound source := by
  cases hs : ixExpr source with
  | error reason => simp [ixToKernel, hs, bind, Except.bind] at exported
  | ok intermediate =>
    have final : exportExpr cx intermediate = .ok result := by
      simpa only [ixToKernel, hs, bind, Except.bind] using exported
    exact (exportExpr_bvarBound final).trans (ixExpr_bvarBound hs)

/-- Scope well-formedness is preserved and reflected by successful structural
translation. This statement concerns scope, not typing or installed binder
annotations, and does not inspect any cached Ix hash. -/
theorem ixToKernel_scoped_iff {cx : TermContext} {source : Ix.Expr} {result : Kernel.Expr}
    (exported : ixToKernel cx source = .ok result) (depth : Nat) :
    result.looseBVarsBounded depth = true ↔ ixBvarBound source ≤ depth := by
  rw [Kernel.Expr.looseBVarsBounded_iff, ixToKernel_bvarBound exported]

theorem ixExpr_bvar_hash_irrelevant (i : Nat) (a b : Address) :
    ixExpr (.bvar i a) = ixExpr (.bvar i b) := rfl

theorem ixExpr_app_hash_irrelevant (f a : Ix.Expr) (h k : Address) :
    ixExpr (.app f a h) = ixExpr (.app f a k) := rfl

end Ix.CompileCert
