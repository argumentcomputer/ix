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

theorem ixExpr_bvar_hash_irrelevant (i : Nat) (a b : Address) :
    ixExpr (.bvar i a) = ixExpr (.bvar i b) := rfl

theorem ixExpr_app_hash_irrelevant (f a : Ix.Expr) (h k : Address) :
    ixExpr (.app f a h) = ixExpr (.app f a k) := rfl

end Ix.CompileCert
