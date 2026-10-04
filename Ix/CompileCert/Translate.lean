import Ix.CompileCert.Map
import Ix.IxonUniv

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

structure TermContext where
  context : ExportContext
  sourceLevels : List Lean.Name
  targetLevels : List Kernel.Name

def exportLevel (cx : TermContext) (u : Lean.Level) : ExportM Kernel.Level := do
  importUniv cx.targetLevels (Ixon.canonUniv (← exportUniv cx.sourceLevels u))

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
