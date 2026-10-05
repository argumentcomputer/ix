import Ix.CompileCert.Translate
import Ix.Kernel.Ixon.ReaderSpec
import Ix.Kernel.Denotes
import Ix.Kernel.Verify.Subst
import Ix.Kernel.Verify.InferLeaves

/-! # Direct reader correspondence

This relation is about reader syntax, not installed annotations or source
denotation. Every source in the closed inventory is checked, including all
members of an alias fiber. A changed dependency cannot be hidden by asking
only for the root's statement. Extra target support is permitted and must
independently pass admission.
-/

namespace Ix.CompileCert

def readerEntries : Kernel.Declaration → List DirectEntry
  | .axiomDecl cv => [.axiom cv]
  | .defnDecl cv v h => [.defn cv v h]
  | .thmDecl cv v => [.thm cv v]
  | .opaqueDecl cv v => [.opaque cv v]
  | .quotDecl k cv => [.quot k cv]
  | .basisDecl _ => []
  | .indDecl block np => block.filterMap fun
    | .indInfo cv _ => some (.induct cv np)
    | .ctorInfo cv p f => some (.ctor cv p f)
    | .recInfo cv major rulePrefix rules => some (.recursor cv major rulePrefix rules)
    | _ => none

def streamEntries (decls : Array Kernel.Declaration) : List DirectEntry :=
  decls.toList.flatMap readerEntries

/-- Reducibility hints control search, not the definition's type or value.
Only this field is quotiented for correspondence. The exact hint supplied
to admission remains bound in `Input`; no checker-behavior equivalence is
claimed by this projection. -/
def DirectEntry.withoutHint : DirectEntry → DirectEntry
  | .defn cv value _ => .defn cv value .opaque
  | other => other

def EntryCompatible (actual expected : DirectEntry) : Prop :=
  actual.withoutHint = expected.withoutHint

instance (actual expected : DirectEntry) : Decidable (EntryCompatible actual expected) :=
  inferInstanceAs (Decidable (actual.withoutHint = expected.withoutHint))

/-- Quotienting hints cannot change either the statement or the body. This
is a syntactic field-preservation theorem, not semantic source pull-back. -/
theorem compatible_definition_fields {a b : Kernel.ConstantVal} {v w : Kernel.Expr}
    {h k : Kernel.ReducibilityHint}
    (same : EntryCompatible (.defn a v h) (.defn b w k)) : a = b ∧ v = w := by
  simpa [EntryCompatible, DirectEntry.withoutHint] using same

def compatibleEntries (entries : List DirectEntry) : List DirectEntry :=
  entries.map DirectEntry.withoutHint

/-- A source declaration agrees with an actual reader entry, including its
kind, complete type/value, universe telescope and every recursor-rule field.
Only definition hints are quotiented. There is no auxiliary exemption. -/
def DirectMatch (cx : ExportContext) (entries : List DirectEntry)
    (ci : Lean.ConstantInfo) : Prop :=
  match directExport cx ci with
  | .error _ => False
  | .ok e => e.withoutHint ∈ compatibleEntries entries

instance (cx : ExportContext) (entries : List DirectEntry) (ci : Lean.ConstantInfo) :
    Decidable (DirectMatch cx entries ci) :=
  match h : directExport cx ci with
  | .error _ => by simp only [DirectMatch, h]; infer_instance
  | .ok _ => by simp only [DirectMatch, h]; infer_instance

def DirectCorrespondence (cx : ExportContext) (decls : Array Kernel.Declaration) : Prop :=
  ∀ ci ∈ cx.source.declarations, DirectMatch cx (streamEntries decls) ci

instance (cx : ExportContext) (decls : Array Kernel.Declaration) :
    Decidable (DirectCorrespondence cx decls) :=
  inferInstanceAs (Decidable
    (∀ ci ∈ cx.source.declarations, DirectMatch cx (streamEntries decls) ci))

def checkDirect (cx : ExportContext) (decls : Array Kernel.Declaration) : Bool :=
  decide (DirectCorrespondence cx decls)

theorem checkDirect_sound {cx : ExportContext} {decls : Array Kernel.Declaration}
    (h : checkDirect cx decls = true) : DirectCorrespondence cx decls :=
  of_decide_eq_true h

/-- Every source member of a many-to-one fiber is compared independently;
no representative's success stands in for another source declaration. -/
theorem DirectCorrespondence.member {cx : ExportContext} {decls : Array Kernel.Declaration}
    (h : DirectCorrespondence cx decls) {ci : Lean.ConstantInfo}
    (hc : ci ∈ cx.source.declarations) :
    ∃ expected actual, directExport cx ci = .ok expected ∧
      actual ∈ streamEntries decls ∧ EntryCompatible actual expected := by
  have hm := h ci hc
  cases he : directExport cx ci with
  | error e => simp [DirectMatch, he] at hm
  | ok e =>
    have hm' : e.withoutHint ∈ compatibleEntries (streamEntries decls) := by
      simpa [DirectMatch, he] using hm
    obtain ⟨actual, ha, heq⟩ := List.mem_map.mp hm'
    exact ⟨e, actual, rfl, ha, heq⟩

/-- Ordered whole-block description. This retains the shape fields that
entry membership alone omits, and the separate recursor counts whose sums
occur in `Kernel.ConstantInfo.recInfo`. -/
structure DirectBlock where
  entries : List DirectEntry
  types : List (Nat × Nat × List Kernel.Name × Bool × Bool × Nat)
  recursors : List (Nat × Nat × Nat × Nat)
  deriving DecidableEq

def readerBlock (b : Kernel.Frontend.InModel.BlockRec) : DirectBlock :=
  { entries := b.types.map (fun t => .induct t.cv t.nP) ++
      b.ctors.map (fun c => .ctor c.cv c.nP c.nF) ++
      b.recs.map (fun r => .recursor r.cv (r.nP + r.nM + r.nm + r.nI)
        (r.nP + r.nM + r.nm) r.rules)
    types := b.types.map (fun t => (t.nP, t.nIdx, t.ctors, t.isRec, t.isReflexive, t.numNested))
    recursors := b.recs.map (fun r => (r.nP, r.nM, r.nm, r.nI)) }

/-- Independent export of a complete source inductive block. All member
and constructor ordering comes from the source, not target metadata. -/
def exportBlock (cx : ExportContext) (owner : Lean.InductiveVal) : ExportM DirectBlock := do
  unless owner.all.contains owner.name do throw "inductive is absent from its source block"
  let mut types := []
  let mut typeEntries := []
  let mut ctorEntries := []
  for n in owner.all do
    let some (.inductInfo iv) := cx.source.find n | throw s!"missing inductive member: {n}"
    unless iv.all == owner.all && iv.numParams == owner.numParams do
      throw s!"inconsistent source inductive membership: {n}"
    typeEntries := typeEntries ++ [← directExport cx (.inductInfo iv)]
    let ctorNames ← iv.ctors.mapM cx.name
    types := types ++ [(iv.numParams, iv.numIndices, ctorNames,
      iv.isRec, iv.isReflexive, iv.numNested)]
    for (ctor, index) in iv.ctors.zipIdx do
      let some (.ctorInfo cv) := cx.source.find ctor | throw s!"missing constructor: {ctor}"
      unless cv.induct == n && cv.cidx == index && cv.numParams == iv.numParams do
        throw s!"inconsistent constructor owner or position: {ctor}"
      ctorEntries := ctorEntries ++ [← directExport cx (.ctorInfo cv)]
  let nested := (List.range owner.numNested).filterMap
    (fun i => owner.all.head?.map (·.str s!"rec_{i + 1}"))
  let recNames := owner.all.map (·.str "rec") ++ nested
  let mut recEntries := []
  let mut recursors := []
  for recName in recNames do
    let some (.recInfo rv) := cx.source.find recName | throw s!"missing recursor: {recName}"
    unless rv.all == owner.all do throw s!"inconsistent recursor membership: {recName}"
    recEntries := recEntries ++ [← directExport cx (.recInfo rv)]
    recursors := recursors ++ [(rv.numParams, rv.numMotives, rv.numMinors, rv.numIndices)]
  return ⟨typeEntries ++ ctorEntries ++ recEntries, types, recursors⟩

def BlockMatch (cx : ExportContext) (state : Kernel.Reader.State)
    (ci : Lean.ConstantInfo) : Prop :=
  match ci with
  | .inductInfo iv =>
    match cx.name iv.name, exportBlock cx iv with
    | .ok name, .ok expected =>
      match state.indBlocks[name]? with
      | some actual => readerBlock actual = expected
      | none => False
    | _, _ => False
  | _ => True

instance (cx : ExportContext) (state : Kernel.Reader.State) (ci : Lean.ConstantInfo) :
    Decidable (BlockMatch cx state ci) := by
  unfold BlockMatch
  split
  · split
    · split <;> infer_instance
    · infer_instance
  · infer_instance

def BlockCorrespondence (cx : ExportContext) (state : Kernel.Reader.State) : Prop :=
  ∀ ci ∈ cx.source.declarations, BlockMatch cx state ci

instance (cx : ExportContext) (state : Kernel.Reader.State) :
    Decidable (BlockCorrespondence cx state) :=
  inferInstanceAs (Decidable (∀ ci ∈ cx.source.declarations, BlockMatch cx state ci))

/-- Preserve the source grouping verbatim. It need not equal a wire block:
SCC decomposition and compatible identity aliases can split or identify it. -/
def definitionGroup : Lean.ConstantInfo → List Lean.Name
  | .defnInfo v => v.all
  | .thmInfo v => v.all
  | .opaqueInfo v => v.all
  | _ => []

/-- The explicit image retains a row for every source member, including
repeated targets. It neither selects one representative nor sorts away the
source order. Actual installation order comes from `checked_declarations`. -/
def definitionGroupImage (cx : ExportContext) (ci : Lean.ConstantInfo) :
    Option (List (Lean.Name × Kernel.ConstRef Address)) :=
  (definitionGroup ci).mapM fun n => do return (n, ← cx.map.find n)

/-- Every indexed member of a touched definition block must have a source
fiber. Comparing each source separately would not establish this reverse
coverage. Extra untouched records remain subject to target admission. -/
def definitionBlockCovered (cx : ExportContext) (owner : Address) (record : Ixon.Constant) : Bool :=
  match record.info with
  | .muts members =>
    if members.all (fun | .defn _ => true | _ => false) &&
        cx.map.any (fun e => decide (e.target.block = owner)) then
      (List.range members.size).all fun index =>
        cx.map.any fun e => decide (e.target = .member owner index)
    else true
  | _ => true

/-- Quotient-aware definition grouping. Source member rows remain explicit;
wire partitions may differ, but no touched wire member is silently omitted.
Full kind/type/value comparison is separately required by correspondence. -/
def DefinitionGroupsCovered (cx : ExportContext) (constants : List (Address × Ixon.Constant)) : Prop :=
  (∀ ci ∈ cx.source.declarations, (definitionGroupImage cx ci).isSome = true) ∧
  (∀ row ∈ constants, definitionBlockCovered cx row.1 row.2 = true)

instance (cx : ExportContext) (constants : List (Address × Ixon.Constant)) :
    Decidable (DefinitionGroupsCovered cx constants) :=
  inferInstanceAs (Decidable (
    (∀ ci ∈ cx.source.declarations, (definitionGroupImage cx ci).isSome = true) ∧
    (∀ row ∈ constants, definitionBlockCovered cx row.1 row.2 = true)))

/-- Checked reverse coverage yields a concrete source-map fiber for every
indexed member, even when several source names share the same target. -/
theorem DefinitionGroupsCovered.member {cx : ExportContext}
    {constants : List (Address × Ixon.Constant)}
    (covered : DefinitionGroupsCovered cx constants)
    {owner : Address} {record : Ixon.Constant} {members : Array Ixon.MutConst}
    (present : (owner, record) ∈ constants) (info : record.info = .muts members)
    (definitions : members.all (fun | .defn _ => true | _ => false) = true)
    (touched : cx.map.any (fun e => decide (e.target.block = owner)) = true)
    {index : Nat} (valid : index < members.size) :
    ∃ e ∈ cx.map, e.target = .member owner index := by
  have checked := covered.2 (owner, record) present
  simp only [definitionBlockCovered, info, definitions, touched, Bool.true_and, ite_true] at checked
  have entry := List.all_eq_true.mp checked index (List.mem_range.mpr valid)
  obtain ⟨e, he, same⟩ := List.any_eq_true.mp entry
  exact ⟨e, he, of_decide_eq_true same⟩

/-! ## Source correspondence before the reader's specified normalization

A projection definition can be read as a recursor term. W must keep two
facts separate: independent source correspondence to the raw reader value,
and the reader's proved `DefinitionDecl` relation to its emitted declaration.
This layer establishes only the former; Entry composes the latter from the
actual admitted stream. Projection semantic preservation is still an S
obligation, not inferred from re-running `projRewrite`.
-/

def ResultIs {ε α : Type} (result : Except ε α) (expected : α) : Prop :=
  match result with
  | .error _ => False
  | .ok actual => actual = expected

instance {ε α : Type} [DecidableEq α] (result : Except ε α) (expected : α) :
    Decidable (ResultIs result expected) := by
  cases result <;> unfold ResultIs <;> infer_instance

theorem ResultIs.eq_result {ε α : Type} {result : Except ε α} {expected : α}
    (h : ResultIs result expected) : result = .ok expected := by
  cases result with
  | error _ => exact False.elim h
  | ok actual => exact congrArg Except.ok h

def RawDefinitionAgrees (reader : Kernel.Reader.Ctx) (owner : Address)
    (record : Ixon.Constant) (definition : Ixon.Definition)
    (cv : Kernel.ConstantVal) (value : Kernel.Expr) : Prop :=
  definition.kind = .defn ∧
  cv.name = reader.nameOf (.member owner 0) ∧
  cv.levelParams = Kernel.Reader.singletonLps reader owner definition.lvls ∧
  ResultIs ((Kernel.Reader.definitionReader reader owner record definition).read definition.typ) cv.type ∧
  ResultIs ((Kernel.Reader.definitionReader reader owner record definition).read definition.value) value

instance (reader : Kernel.Reader.Ctx) (owner : Address)
    (record : Ixon.Constant) (definition : Ixon.Definition)
    (cv : Kernel.ConstantVal) (value : Kernel.Expr) :
    Decidable (RawDefinitionAgrees reader owner record definition cv value) :=
  inferInstanceAs (Decidable (definition.kind = .defn ∧
    cv.name = reader.nameOf (.member owner 0) ∧
    cv.levelParams = Kernel.Reader.singletonLps reader owner definition.lvls ∧
    ResultIs ((Kernel.Reader.definitionReader reader owner record definition).read definition.typ) cv.type ∧
    ResultIs ((Kernel.Reader.definitionReader reader owner record definition).read definition.value) value))

def RawEntryMatch (reader : Kernel.Reader.Ctx) (owner : Address)
    (record : Ixon.Constant) (expected : DirectEntry) : Prop :=
  match record.info, expected with
  | .defn definition, .defn cv value _ => RawDefinitionAgrees reader owner record definition cv value
  | _, _ => False

instance (reader : Kernel.Reader.Ctx) (owner : Address)
    (record : Ixon.Constant) (expected : DirectEntry) :
    Decidable (RawEntryMatch reader owner record expected) := by
  unfold RawEntryMatch
  split <;> infer_instance

/-- The source record is selected by an explicit proposed source key and
must occur in the exact admitted byte stream. Prelude-only records continue
using strict direct correspondence rather than fabricated stream membership. -/
def rawSourceRecord (cx : ExportContext) (constants : List (Address × Ixon.Constant))
    (ci : Lean.ConstantInfo) : Option (Address × Ixon.Constant) := do
  let entry ← cx.map.find? (fun e => e.source == ci.name)
  constants.find? (fun p => decide (p.1 = entry.record))

def RawSourceMatch (cx : ExportContext) (reader : Kernel.Reader.Ctx)
    (constants : List (Address × Ixon.Constant)) (ci : Lean.ConstantInfo) : Prop :=
  match directExport cx ci, rawSourceRecord cx constants ci with
  | .ok expected, some (owner, record) => RawEntryMatch reader owner record expected
  | _, _ => False

instance (cx : ExportContext) (reader : Kernel.Reader.Ctx)
    (constants : List (Address × Ixon.Constant)) (ci : Lean.ConstantInfo) :
    Decidable (RawSourceMatch cx reader constants ci) := by
  unfold RawSourceMatch
  split <;> infer_instance

def SourceCorrespondence (cx : ExportContext) (reader : Kernel.Reader.Ctx)
    (constants : List (Address × Ixon.Constant)) (decls : Array Kernel.Declaration) : Prop :=
  ∀ ci ∈ cx.source.declarations,
    DirectMatch cx (streamEntries decls) ci ∨ RawSourceMatch cx reader constants ci

instance (cx : ExportContext) (reader : Kernel.Reader.Ctx)
    (constants : List (Address × Ixon.Constant)) (decls : Array Kernel.Declaration) :
    Decidable (SourceCorrespondence cx reader constants decls) :=
  inferInstanceAs (Decidable (∀ ci ∈ cx.source.declarations,
    DirectMatch cx (streamEntries decls) ci ∨ RawSourceMatch cx reader constants ci))

theorem rawSourceRecord_mem {cx : ExportContext} {constants : List (Address × Ixon.Constant)}
    {ci : Lean.ConstantInfo} {pair : Address × Ixon.Constant}
    (h : rawSourceRecord cx constants ci = some pair) : pair ∈ constants := by
  unfold rawSourceRecord at h
  cases he : cx.map.find? (fun e => e.source == ci.name) with
  | none => simp [he, bind, Option.bind] at h
  | some entry =>
    simp only [he, bind, Option.bind] at h
    exact List.mem_of_find?_eq_some h

/-- Compose independently checked raw source fields with the reader's
existing normalization specification. The resulting value is explicitly
`projRewrite ...`; this theorem does not assert semantic equality to it. -/
theorem RawDefinitionAgrees.reader_decl {reader : Kernel.Reader.Ctx} {state : Kernel.Reader.State}
    {owner : Address} {record : Ixon.Constant} {definition : Ixon.Definition}
    {cv : Kernel.ConstantVal} {value : Kernel.Expr} {decl : Kernel.Declaration}
    (info : record.info = .defn definition)
    (raw : RawDefinitionAgrees reader owner record definition cv value)
    (reading : Kernel.Reader.SingletonRead reader state owner record decl) :
    Kernel.Reader.DefinitionDecl cv value (Kernel.Reader.projRewrite state cv value) .defn decl := by
  obtain ⟨hkind, hname, hlevels, htype, hvalue⟩ := raw
  cases reading with
  | @defn d ty v decl hi ht hv hk =>
    have hd : definition = d := Ixon.ConstantInfo.defn.inj (info.symm.trans hi)
    subst d
    have hty : ty = cv.type := Except.ok.inj (ht.symm.trans htype.eq_result)
    have hval : v = value := Except.ok.inj (hv.symm.trans hvalue.eq_result)
    subst ty
    subst v
    have hcv : cv = ⟨reader.nameOf (.member owner 0),
        Kernel.Reader.singletonLps reader owner definition.lvls, cv.type⟩ := by
      cases cv
      simp_all
    rw [← hcv] at hk
    simpa only [hkind] using hk
  | axio hi _ _ => cases info.symm.trans hi
  | quot hi _ => cases info.symm.trans hi

/-! ### Semantic transport of installed expressions

This relation records the obligations after both installations. In particular
regime agreement is explicit; well-formed annotations alone do not imply it.
Constant instances may identify names, and their universe lists need not be
syntactically identical. Establishing this relation from the two annotation
runs, including eliminated lets and lowered source projections, is D11. -/

inductive InstalledExprImage {V : Type u} [Kernel.SetTheory V]
    (sourceValues targetValues : Kernel.Name → (Kernel.Name → Nat) → V)
    (sourceEnv targetEnv : Kernel.Env) (sourceLevels targetLevels : Kernel.Name → Nat) :
    Kernel.Expr → Kernel.Expr → Prop
  | bvar (index) : InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels
      (.bvar index) (.bvar index)
  | sort {source target} (levels : Kernel.Level.eval sourceLevels source = Kernel.Level.eval targetLevels target) :
      InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels
        (.sort source) (.sort target)
  | constant {sourceName targetName sourceUs targetUs sourceInfo targetInfo}
      (sourceLookup : sourceEnv.find? sourceName = some sourceInfo)
      (targetLookup : targetEnv.find? targetName = some targetInfo)
      (sourceArity : sourceUs.length = sourceInfo.toConstantVal.levelParams.length)
      (targetArity : targetUs.length = targetInfo.toConstantVal.levelParams.length)
      (values : sourceValues sourceName (Kernel.Level.substFn sourceLevels sourceInfo.toConstantVal.levelParams sourceUs) =
        targetValues targetName (Kernel.Level.substFn targetLevels targetInfo.toConstantVal.levelParams targetUs)) :
      InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels
        (.const sourceName sourceUs) (.const targetName targetUs)
  | app {sf sa tf ta}
      (function : InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels sf tf)
      (argument : InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels sa ta) :
      InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels (.app sf sa) (.app tf ta)
  | lam {st sb sm tt tb tm}
      (domain : InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels st tt)
      (body : InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels sb tb)
      (regimes : Kernel.regime sourceLevels sm.pw = Kernel.regime targetLevels tm.pw) :
      InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels (.lam st sb sm) (.lam tt tb tm)
  | forallE {st sb sm tt tb tm}
      (domain : InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels st tt)
      (body : InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels sb tb)
      (regimes : Kernel.regime sourceLevels sm.pw = Kernel.regime targetLevels tm.pw) :
      InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels (.forallE st sb sm) (.forallE tt tb tm)
  | projTable {sn si se tn ti te sourceEntry targetEntry}
      (sourceTable : sourceEnv.findProj? sn si = some sourceEntry)
      (targetTable : targetEnv.findProj? tn ti = some targetEntry)
      (position : si + sourceEntry.off = ti + targetEntry.off)
      (operand : InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels se te) :
      InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels (.proj sn si se) (.proj tn ti te)
  | projFst {sn se tn te}
      (sourceTable : sourceEnv.findProj? sn 0 = none)
      (targetTable : targetEnv.findProj? tn 0 = none)
      (operand : InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels se te) :
      InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels (.proj sn 0 se) (.proj tn 0 te)
  | projSnd {sn se tn te}
      (sourceTable : sourceEnv.findProj? sn 1 = none)
      (targetTable : targetEnv.findProj? tn 1 = none)
      (operand : InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels se te) :
      InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels (.proj sn 1 se) (.proj tn 1 te)
  | natLit {source target}
      (constructors : InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels
        (Kernel.natLitToConstructor source) (Kernel.natLitToConstructor target)) :
      InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels
        (.lit (.natVal source)) (.lit (.natVal target))
  | strLit {source target}
      (constructors : InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels
        (Kernel.strLitToConstructor source) (Kernel.strLitToConstructor target)) :
      InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels
        (.lit (.strVal source)) (.lit (.strVal target))

theorem InstalledExprImage.denotes {V : Type u} [Kernel.SetTheory V]
    {sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels source target}
    (image : InstalledExprImage (V := V) sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels source target)
    {ρ : Nat → V} {value : V}
    (denoted : Kernel.Denotes sourceValues sourceEnv sourceLevels ρ source value) :
    Kernel.Denotes targetValues targetEnv targetLevels ρ target value := by
  induction image generalizing ρ value with
  | bvar => cases denoted; exact .bvar
  | sort levels => cases denoted; rw [levels]; exact .sort
  | constant sourceLookup targetLookup sourceArity targetArity values =>
    cases denoted with
    | const lookup arity =>
      have same := Option.some.inj (lookup.symm.trans sourceLookup)
      cases same
      rw [values]
      exact .const targetLookup targetArity
  | app function argument ihf iha =>
    cases denoted with
    | app hf ha => exact .app (ihf hf) (iha ha)
  | lam domain body regimes ihd ihb =>
    cases denoted with
    | lam hA hF hP =>
      rw [regimes]
      exact .lam (ihd hA) (fun x hx => ihb (hF x hx))
        (fun h x hx => hP (regimes.trans h) x hx)
  | forallE domain body regimes ihd ihb =>
    cases denoted with
    | pi hA hB hP =>
      rw [regimes]
      exact .pi (ihd hA) (fun x hx => ihb (hB x hx))
        (fun h x hx => hP (regimes.trans h) x hx)
  | projTable sourceTable targetTable position operand ih =>
    cases denoted with
    | proj_table lookup he =>
      have same := Option.some.inj (lookup.symm.trans sourceTable)
      cases same
      rw [position]
      exact .proj_table targetTable (ih he)
    | proj_fst lookup _ => rw [sourceTable] at lookup; cases lookup
    | proj_snd lookup _ => rw [sourceTable] at lookup; cases lookup
  | projFst sourceTable targetTable operand ih =>
    cases denoted with
    | proj_table lookup _ => rw [sourceTable] at lookup; cases lookup
    | proj_fst _ he => exact .proj_fst targetTable (ih he)
  | projSnd sourceTable targetTable operand ih =>
    cases denoted with
    | proj_table lookup _ => rw [sourceTable] at lookup; cases lookup
    | proj_snd _ he => exact .proj_snd targetTable (ih he)
  | natLit constructors ih =>
    cases denoted with
    | natLit h => exact .natLit (ih h)
  | strLit constructors ih =>
    cases denoted with
    | strLit h => exact .strLit (ih h)

theorem InstalledExprImage.symm {V : Type u} [Kernel.SetTheory V]
    {sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels source target}
    (image : InstalledExprImage (V := V) sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels source target) :
    InstalledExprImage targetValues sourceValues targetEnv sourceEnv targetLevels sourceLevels target source := by
  induction image with
  | bvar i => exact .bvar i
  | sort levels => exact .sort levels.symm
  | constant hs ht ha hb values => exact .constant ht hs hb ha values.symm
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ regimes ihd ihb => exact .lam ihd ihb regimes.symm
  | forallE _ _ regimes ihd ihb => exact .forallE ihd ihb regimes.symm
  | projTable hs ht position _ ih => exact .projTable ht hs position.symm ih
  | projFst hs ht _ ih => exact .projFst ht hs ih
  | projSnd hs ht _ ih => exact .projSnd ht hs ih
  | natLit _ ih => exact .natLit ih
  | strLit _ ih => exact .strLit ih

theorem InstalledExprImage.denotes_iff {V : Type u} [Kernel.SetTheory V]
    {sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels source target}
    (image : InstalledExprImage (V := V) sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels source target)
    (ρ : Nat → V) (value : V) :
    Kernel.Denotes sourceValues sourceEnv sourceLevels ρ source value ↔
      Kernel.Denotes targetValues targetEnv targetLevels ρ target value :=
  ⟨image.denotes, image.symm.denotes⟩

open Kernel.SetTheory in
/-- Eliminate an actually denoted installed binder at a typed argument.
The regime-zero side condition comes from Denotes itself, so this works
for Prop and graph binders without silently treating proofs as functions. -/
theorem installed_forall_elim {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V}
    {domain body : Kernel.Expr} {binder : Kernel.BinderMeta} {type function A argument : V}
    (denoted : Kernel.Denotes values env levels ρ (.forallE domain body binder) type)
    (member : function ∈ˢ type)
    (domainDenoted : Kernel.Denotes values env levels ρ domain A)
    (argumentTyped : argument ∈ˢ A) :
    ∃ result, Kernel.Denotes values env levels (Kernel.push argument ρ) body result ∧
      app function argument ∈ˢ result := by
  cases denoted with
  | pi hA hB hP =>
    obtain rfl := Kernel.Denotes_functional domainDenoted hA
    exact ⟨_, hB argument argumentTyped,
      Kernel.SetModel.app_mem_piR member argumentTyped
        (by simpa only [univ_zero] using hP)⟩

/-- Exactly as many semantic fields as the immutable original constructor
declares. No default element is manufactured for a missing field. -/
abbrev SourceFieldValues {source : Source} (site : SourceProjectionSite source) (V : Type u) :=
  { fields : List V // fields.length = site.ctor.numFields }

def originalSelectedField {source : Source} (site : SourceProjectionSite source)
    {V : Type u} (fields : SourceFieldValues site V) : V :=
  fields.val[site.field]'(by rw [fields.property]; exact site.shape.2.2.2.2.2)

noncomputable def originalConstructorValue {source : Source} (site : SourceProjectionSite source)
    {V : Type u} [Kernel.SetTheory V] (values : Kernel.Name → (Kernel.Name → Nat) → V)
    (levels : Kernel.Name → Nat) (parameters : List V) (fields : SourceFieldValues site V) : V :=
  (parameters ++ fields.val).foldl Kernel.SetTheory.app (values (sourceName site.ctorName) levels)

/-- Original-source projection meaning, independent of a lowered term:
choose the specified original field from a typed constructor presentation.
`valid` is the original dependent field telescope's satisfaction predicate;
establishing it from actual source/coverage annotations is an open premise. -/
def OriginalProjectionValue {source : Source} (site : SourceProjectionSite source)
    {V : Type u} [Kernel.SetTheory V] (values : Kernel.Name → (Kernel.Name → Nat) → V)
    (levels : Kernel.Name → Nat) (parameters : List V)
    (valid : SourceFieldValues site V → Prop) (subject value : V) : Prop :=
  ∃ fields, valid fields ∧ originalConstructorValue site values levels parameters fields = subject ∧
    originalSelectedField site fields = value

open Kernel.SetTheory in
/-- The semantic proposition encoded by the arbitrary-subject certificate.
Connecting the checked syntax's actual annotated telescope to this predicate
is required; the definition does not assume that connection. -/
def SemanticConstructorCover {V : Type u} [Kernel.SetTheory V] {Fields : Type v}
    (valid : Fields → Prop) (constructor : Fields → V) (subject : V) : Prop :=
  ∀ proposition : V, proposition ∈ˢ univ 0 →
    (∀ fields, valid fields → constructor fields = subject → pt ∈ˢ proposition) →
    pt ∈ˢ proposition

open Kernel.SetTheory in
theorem semanticConstructorCover_iff {V : Type u} [Kernel.SetTheory V] {Fields : Type v}
    (valid : Fields → Prop) (constructor : Fields → V) (subject : V) :
    SemanticConstructorCover valid constructor subject ↔
      ∃ fields, valid fields ∧ constructor fields = subject := by
  constructor
  · intro cover
    let proposition : Prop := ∃ fields, valid fields ∧ constructor fields = subject
    have inUniverse : (truthVal proposition : V) ∈ˢ univ 0 := by
      rw [univ_zero]
      exact truthVal_mem_univZero proposition
    have inhabited := cover (truthVal proposition) inUniverse
      (fun fields typed equal => pt_mem_truthVal ⟨fields, typed, equal⟩)
    exact of_mem_truthVal inhabited
  · rintro ⟨fields, typed, equal⟩ proposition _ continuation
    exact continuation fields typed equal

open Kernel.SetTheory in
/-- Arbitrary-value projection correspondence, with its two substantive
premises visible: constructor coverage for every carrier member and the
checked equation's semantic interpretation on every typed field tuple.
Neither premise is inferred from the fixture census or from the generator. -/
theorem original_projection_extensional {source : Source} (site : SourceProjectionSite source)
    {V : Type u} [Kernel.SetTheory V] (values : Kernel.Name → (Kernel.Name → Nat) → V)
    (levels : Kernel.Name → Nat) (parameters : List V)
    (valid : SourceFieldValues site V → Prop) (carrier projection : V)
    (coverage : ∀ subject, subject ∈ˢ carrier → SemanticConstructorCover valid
      (originalConstructorValue site values levels parameters) subject)
    (computation : ∀ fields, valid fields →
      app projection (originalConstructorValue site values levels parameters fields) =
        originalSelectedField site fields) :
    ∀ subject, subject ∈ˢ carrier →
      OriginalProjectionValue site values levels parameters valid subject (app projection subject) ∧
      ∀ value, OriginalProjectionValue site values levels parameters valid subject value →
        value = app projection subject := by
  intro subject typed
  obtain ⟨fields, fieldsTyped, presents⟩ :=
    (semanticConstructorCover_iff _ _ _).mp (coverage subject typed)
  have computed : app projection subject = originalSelectedField site fields := by
    simpa only [presents] using computation fields fieldsTyped
  refine ⟨⟨fields, fieldsTyped, presents, computed.symm⟩, ?_⟩
  intro value reading
  obtain ⟨other, otherTyped, sameSubject, selected⟩ := reading
  have otherComputed : app projection subject = originalSelectedField site other := by
    simpa only [sameSubject] using computation other otherTyped
  exact selected.symm.trans otherComputed.symm

open Kernel.SetTheory in
/-- Function-value equality follows only with typed product membership.
The same proof covers graph functions and the proof-point regime. -/
theorem original_projection_function_extensional {source : Source} (site : SourceProjectionSite source)
    {V : Type u} [Kernel.SetTheory V] (values : Kernel.Name → (Kernel.Name → Nat) → V)
    (levels : Kernel.Name → Nat) (parameters : List V)
    (valid : SourceFieldValues site V → Prop) (carrier original lowered : V)
    {regime : Nat} {originalCodomain loweredCodomain : V → V}
    (originalTyped : original ∈ˢ Kernel.SetModel.piR regime carrier originalCodomain)
    (loweredTyped : lowered ∈ˢ Kernel.SetModel.piR regime carrier loweredCodomain)
    (originalReading : ∀ subject, subject ∈ˢ carrier →
      OriginalProjectionValue site values levels parameters valid subject (app original subject))
    (coverage : ∀ subject, subject ∈ˢ carrier → SemanticConstructorCover valid
      (originalConstructorValue site values levels parameters) subject)
    (computation : ∀ fields, valid fields →
      app lowered (originalConstructorValue site values levels parameters fields) =
        originalSelectedField site fields) : original = lowered := by
  apply Kernel.SetModel.eq_of_mem_piR_app_eq originalTyped loweredTyped
  intro subject typed
  exact (original_projection_extensional site values levels parameters valid carrier lowered
    coverage computation subject typed).2 _ (originalReading subject typed)

/-! A field tuple is typed against the actual annotated telescope, including
all dependencies on earlier fields. The residual expression and valuation are
outputs, so instantiation cannot silently switch to a different telescope. -/

open Kernel.SetTheory in
inductive InstalledTelescope {V : Type u} [Kernel.SetTheory V]
    (values : Kernel.Name → (Kernel.Name → Nat) → V) (env : Kernel.Env)
    (levels : Kernel.Name → Nat) :
    (Nat → V) → Kernel.Expr → List V → (Nat → V) → Kernel.Expr → Prop
  | nil {ρ expression} : InstalledTelescope values env levels ρ expression [] ρ expression
  | cons {ρ domain body binder argument A arguments finalρ result}
      (domainDenoted : Kernel.Denotes values env levels ρ domain A)
      (argumentTyped : argument ∈ˢ A)
      (rest : InstalledTelescope values env levels (Kernel.push argument ρ)
        body arguments finalρ result) :
      InstalledTelescope values env levels ρ (.forallE domain body binder)
        (argument :: arguments) finalρ result

open Kernel.SetTheory in
/-- Apply a member of the actual installed type to a dependent typed tuple.
No binder regime is guessed, and no unchecked source telescope is substituted. -/
theorem InstalledTelescope.apply {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V}
    {expression result : Kernel.Expr} {arguments : List V}
    (typed : InstalledTelescope values env levels ρ expression arguments finalρ result)
    {type function : V} (denoted : Kernel.Denotes values env levels ρ expression type)
    (member : function ∈ˢ type) :
    ∃ residual, Kernel.Denotes values env levels finalρ result residual ∧
      arguments.foldl app function ∈ˢ residual := by
  induction typed generalizing type function with
  | nil => exact ⟨type, denoted, member⟩
  | cons domainDenoted argumentTyped rest ih =>
    obtain ⟨next, readNext, memberNext⟩ :=
      installed_forall_elim denoted member domainDenoted argumentTyped
    exact ih readNext memberNext

open Kernel.SetTheory in
theorem InstalledTelescope.model_apply {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (model : Kernel.Model V env)
    {constant : Kernel.ConstantInfo} (installed : constant ∈ env.consts)
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V}
    {result : Kernel.Expr} {arguments : List V}
    (typed : InstalledTelescope model.cval env levels ρ constant.toConstantVal.type
      arguments finalρ result) :
    ∃ residual, Kernel.Denotes model.cval env levels finalρ result residual ∧
      arguments.foldl app (model.cval constant.name levels) ∈ˢ residual := by
  obtain ⟨type, denoted, member⟩ := model.mem constant installed levels ρ
  exact typed.apply denoted member

/-- Valuations related by insertion of `amount` slots below `cutoff`.
The inserted values are arbitrary and cannot affect the lifted expression. -/
def ValuationLift {V : Type u} (amount cutoff : Nat) (ρ target : Nat → V) : Prop :=
  ∀ index, target (if index ≥ cutoff then index + amount else index) = ρ index

theorem ValuationLift.push {V : Type u} {amount cutoff : Nat} {ρ target : Nat → V}
    (related : ValuationLift amount cutoff ρ target) (value : V) :
    ValuationLift amount (cutoff + 1) (Kernel.push value ρ) (Kernel.push value target) := by
  intro index
  cases index with
  | zero => simp [Kernel.push]
  | succ index =>
    have old := related index
    by_cases below : index ≥ cutoff
    · simp only [if_pos below] at old
      simpa [show index + 1 ≥ cutoff + 1 by omega, Kernel.push,
        Nat.add_right_comm index 1 amount] using old
    · simp only [if_neg below] at old
      simpa [show ¬ index + 1 ≥ cutoff + 1 by omega, Kernel.push] using old

/-- Public installed denotation is preserved by capture-avoiding weakening.
This transports dependent field domains across the extra subject/Prop binders
of the independently checked coverage certificate. -/
theorem denotes_lift {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V} {expression : Kernel.Expr} {value : V}
    (denoted : Kernel.Denotes values env levels ρ expression value)
    {amount cutoff : Nat} {target : Nat → V}
    (related : ValuationLift amount cutoff ρ target) :
    Kernel.Denotes values env levels target (expression.liftLooseBVars amount cutoff) value := by
  induction denoted generalizing cutoff target with
  | bvar =>
    rename_i old index
    simp only [Kernel.Expr.liftLooseBVars]
    split <;> rename_i h
    · have same := related index
      rw [if_pos h] at same
      rw [← same]
      exact .bvar
    · have same := related index
      rw [if_neg h] at same
      rw [← same]
      exact .bvar
  | sort => exact .sort
  | const hf hlen => exact .const hf hlen
  | app hf ha ihf iha => exact .app (ihf related) (iha related)
  | lam hA hF hP ihA ihF =>
    exact .lam (ihA related) (fun x hx => ihF x hx (related.push x)) hP
  | pi hA hB hP ihA ihB =>
    exact .pi (ihA related) (fun x hx => ihB x hx (related.push x)) hP
  | proj_table lookup he ih => exact .proj_table lookup (ih related)
  | proj_fst lookup he ih => exact .proj_fst lookup (ih related)
  | proj_snd lookup he ih => exact .proj_snd lookup (ih related)
  | natLit h ih =>
    apply Kernel.Denotes.natLit
    have lifted := ih related
    simpa only [Kernel.Expr.liftLooseBVars_eq_self
      (Kernel.natLitToConstructor_looseBVars _)] using lifted
  | strLit h ih =>
    apply Kernel.Denotes.strLit
    have lifted := ih related
    simpa only [Kernel.Expr.liftLooseBVars_eq_self
      (Kernel.strLitToConstructor_looseBVars _ _)] using lifted

def pushArguments {V : Type u} (ρ : Nat → V) : List V → Nat → V
  | [] => ρ
  | argument :: rest => pushArguments (Kernel.push argument ρ) rest

/-- The same dependent tuple remains typed after inserting arbitrary slots.
Both the residual expression's cutoff and its valuation track every consumed
binder. This is stronger than equality of field counts or isolated domains. -/
theorem InstalledTelescope.lift {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V}
    {expression result : Kernel.Expr} {arguments : List V}
    (typed : InstalledTelescope values env levels ρ expression arguments finalρ result)
    {amount cutoff : Nat} {target : Nat → V}
    (related : ValuationLift amount cutoff ρ target) :
    ValuationLift amount (cutoff + arguments.length) finalρ (pushArguments target arguments) ∧
      InstalledTelescope values env levels target (expression.liftLooseBVars amount cutoff)
        arguments (pushArguments target arguments)
        (result.liftLooseBVars amount (cutoff + arguments.length)) := by
  induction typed generalizing cutoff target with
  | nil => exact ⟨related, .nil⟩
  | cons domainDenoted argumentTyped rest ih =>
    obtain ⟨finalRelated, lifted⟩ := ih (related.push _)
    constructor
    · simpa only [pushArguments, List.length_cons, Nat.add_assoc,
        Nat.add_comm 1] using finalRelated
    · simp only [Kernel.Expr.liftLooseBVars, pushArguments, List.length_cons]
      apply InstalledTelescope.cons (denotes_lift domainDenoted related) argumentTyped
      simpa only [Nat.add_assoc, Nat.add_comm 1] using lifted

/-- Exactly the binder prefix consumed when reading the checked statement. -/
inductive InstalledBinderPrefix : Nat → Kernel.Expr → Prop
  | zero (expression) : InstalledBinderPrefix 0 expression
  | succ {count domain body binder} (rest : InstalledBinderPrefix count body) :
      InstalledBinderPrefix (count + 1) (.forallE domain body binder)

open Kernel.SetTheory in
/-- Introduce a continuation over an actual annotated dependent telescope.
Every possible typed tuple must leave an inhabited residual statement.
The constructed member respects the checker's regime, including Prop. -/
theorem InstalledBinderPrefix.inhabited {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {count : Nat} {expression : Kernel.Expr}
    (binders : InstalledBinderPrefix count expression)
    {ρ : Nat → V} {type : V}
    (denoted : Kernel.Denotes values env levels ρ expression type)
    (leaves : ∀ (arguments : List V) (finalρ : Nat → V) (result : Kernel.Expr),
      arguments.length = count →
      InstalledTelescope values env levels ρ expression arguments finalρ result →
      ∃ residual, Kernel.Denotes values env levels finalρ result residual ∧
        ∃ member, member ∈ˢ residual) :
    ∃ member, member ∈ˢ type := by
  classical
  induction binders generalizing ρ type with
  | zero expression =>
    obtain ⟨residual, readResidual, member, typed⟩ := leaves [] ρ expression rfl .nil
    obtain rfl := Kernel.Denotes_functional readResidual denoted
    exact ⟨member, typed⟩
  | @succ count domain body binder rest ih =>
    cases denoted with
    | @pi _ _ _ _ A B hA hB hP =>
      have inhabited : ∀ x, x ∈ˢ A → ∃ member, member ∈ˢ B x := by
        intro x hx
        apply ih (hB x hx)
        intro arguments finalρ result length typed
        exact leaves (x :: arguments) finalρ result (by simp [length])
          (.cons hA hx typed)
      let witness (x : V) : V := if hx : x ∈ˢ A then
        Classical.choose (inhabited x hx) else empty
      refine ⟨Kernel.SetModel.lamR (Kernel.regime levels binder.pw) A witness,
        Kernel.SetModel.lamR_mem ?_⟩
      intro x hx
      dsimp [witness]
      rw [dif_pos hx]
      exact Classical.choose_spec (inhabited x hx)

open Kernel.SetTheory in
/-- Interpret the final two binders of the checked Church statement.
The continuation is read under the actual proposition binder; no raw binder
annotation is asserted to have the same semantics as its installed image. -/
theorem installed_church_elim {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V}
    {continuation : Kernel.Expr} {outer inner : Kernel.BinderMeta} {type proof : V}
    (denoted : Kernel.Denotes values env levels ρ
      (.forallE (.sort .zero) (.forallE continuation (.bvar 1) inner) outer) type)
    (member : proof ∈ˢ type)
    (proposition : V) (isProp : proposition ∈ˢ univ 0)
    (continuationInhabited : ∃ continuationType,
      Kernel.Denotes values env levels (Kernel.push proposition ρ) continuation continuationType ∧
      ∃ witness, witness ∈ˢ continuationType) :
    pt ∈ˢ proposition := by
  obtain ⟨middle, readMiddle, memberMiddle⟩ := installed_forall_elim denoted member
    (Kernel.Denotes.sort (u := .zero)) isProp
  obtain ⟨continuationType, readContinuation, witness, witnessTyped⟩ := continuationInhabited
  obtain ⟨result, readResult, memberResult⟩ :=
    installed_forall_elim readMiddle memberMiddle readContinuation witnessTyped
  have same : result = proposition := by
    cases readResult
    rfl
  subst result
  have point := Kernel.SetTheory.eq_pt_of_mem_univZero
    (by simpa only [univ_zero] using isProp) memberResult
  rwa [point] at memberResult

end Ix.CompileCert
