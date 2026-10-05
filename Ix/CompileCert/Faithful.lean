import Ix.CompileCert.Translate
import Ix.Kernel.Ixon.ReaderSpec
import Ix.Kernel.Denotes
import Ix.Kernel.Verify.Subst
import Ix.Kernel.Verify.Close
import Ix.Kernel.Verify.InferLeaves
import Ix.Kernel.Verify.PropWhen

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

/-- Structural weakening of an installed semantic image. Projection table
positions and selected universe instances remain exactly the supplied ones. -/
theorem InstalledExprImage.lift {V : Type u} [Kernel.SetTheory V]
    {sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels source target}
    (image : InstalledExprImage (V := V) sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels source target)
    (amount cutoff : Nat) :
    InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels
      (source.liftLooseBVars amount cutoff) (target.liftLooseBVars amount cutoff) := by
  induction image generalizing cutoff with
  | bvar index =>
    simp only [Kernel.Expr.liftLooseBVars]
    split <;> exact .bvar _
  | sort levels => exact .sort levels
  | constant sl tl sa ta values => exact .constant sl tl sa ta values
  | app _ _ ihf iha => exact .app (ihf cutoff) (iha cutoff)
  | lam _ _ regimes ihA ihB => exact .lam (ihA cutoff) (ihB (cutoff + 1)) regimes
  | forallE _ _ regimes ihA ihB => exact .forallE (ihA cutoff) (ihB (cutoff + 1)) regimes
  | projTable sl tl position _ ih => exact .projTable sl tl position (ih cutoff)
  | projFst sl tl _ ih => exact .projFst sl tl (ih cutoff)
  | projSnd sl tl _ ih => exact .projSnd sl tl (ih cutoff)
  | natLit constructors _ => exact .natLit constructors
  | strLit constructors _ => exact .strLit constructors

/-- Exact capture-avoiding substitution on both sides of an installed image.
The replacements themselves must be related under the same environments and
universe assignments; equal hashes or target-only typing cannot supply it. -/
theorem InstalledExprImage.instantiate1Lift {V : Type u} [Kernel.SetTheory V]
    {sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels source target sourceArgument targetArgument}
    (image : InstalledExprImage (V := V) sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels source target)
    (argumentImage : InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels
      sourceArgument targetArgument) (depth : Nat) :
    InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels
      (source.instantiate1Lift sourceArgument depth) (target.instantiate1Lift targetArgument depth) := by
  induction image generalizing depth with
  | bvar index =>
    simp only [Kernel.Expr.instantiate1Lift]
    split
    · exact argumentImage.lift depth 0
    · split <;> exact .bvar _
  | sort levels => exact .sort levels
  | constant sl tl sa ta values => exact .constant sl tl sa ta values
  | app _ _ ihf iha => exact .app (ihf depth) (iha depth)
  | lam _ _ regimes ihA ihB => exact .lam (ihA depth) (ihB (depth + 1)) regimes
  | forallE _ _ regimes ihA ihB => exact .forallE (ihA depth) (ihB (depth + 1)) regimes
  | projTable sl tl position _ ih => exact .projTable sl tl position (ih depth)
  | projFst sl tl _ ih => exact .projFst sl tl (ih depth)
  | projSnd sl tl _ ih => exact .projSnd sl tl (ih depth)
  | natLit constructors _ => exact .natLit constructors
  | strLit constructors _ => exact .strLit constructors

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

/-- A checked semantic level comparison may replace the target constant's
universe syntax. This uses equality of the actual substitution assignments,
not canonical syntax or equal serialized hashes. -/
theorem InstalledExprImage.constant_equivalent_levels {V : Type u} [Kernel.SetTheory V]
    {sv tv se te sl tl sourceName targetName sourceUs targetUs equivalentUs}
    (image : InstalledExprImage (V := V) sv tv se te sl tl
      (.const sourceName sourceUs) (.const targetName targetUs))
    (equivalent : Kernel.Level.isEquivList targetUs equivalentUs = some true) :
    InstalledExprImage sv tv se te sl tl (.const sourceName sourceUs) (.const targetName equivalentUs) := by
  cases image with
  | constant sourceLookup targetLookup sourceArity targetArity values =>
    refine .constant sourceLookup targetLookup sourceArity ?_ ?_
    · exact (Kernel.Level.isEquivList_length equivalent).symm.trans targetArity
    · rw [← Kernel.Level.substFn_congr (Kernel.Level.isEquivList_sound equivalent tl)]
      exact values

/-- Literal correspondence needs the actual pinned constant images. The
proof works for every natural value without unfolding its numeral in an
executable image checker. -/
theorem InstalledExprImage.natural {V : Type u} [Kernel.SetTheory V]
    {sv tv se te sl tl}
    (zero : InstalledExprImage (V := V) sv tv se te sl tl
      (.const Kernel.natZeroName []) (.const Kernel.natZeroName []))
    (succ : InstalledExprImage sv tv se te sl tl
      (.const Kernel.natSuccName []) (.const Kernel.natSuccName [])) (value : Nat) :
    InstalledExprImage sv tv se te sl tl (.lit (.natVal value)) (.lit (.natVal value)) := by
  induction value with
  | zero => exact .natLit zero
  | succ value ih => exact .natLit (.app succ ih)

/-- String correspondence follows the actual constructor encoding and its
fixed universe instance. All supporting constant images are explicit. -/
theorem InstalledExprImage.string {V : Type u} [Kernel.SetTheory V]
    {sv tv se te sl tl}
    (zero : InstalledExprImage (V := V) sv tv se te sl tl (.const Kernel.natZeroName []) (.const Kernel.natZeroName []))
    (succ : InstalledExprImage sv tv se te sl tl (.const Kernel.natSuccName []) (.const Kernel.natSuccName []))
    (char : InstalledExprImage sv tv se te sl tl (.const Kernel.charName []) (.const Kernel.charName []))
    (ofNat : InstalledExprImage sv tv se te sl tl (.const Kernel.charOfNatName []) (.const Kernel.charOfNatName []))
    (nil : InstalledExprImage sv tv se te sl tl (.const Kernel.listNilName [.zero]) (.const Kernel.listNilName [.zero]))
    (cons : InstalledExprImage sv tv se te sl tl (.const Kernel.listConsName [.zero]) (.const Kernel.listConsName [.zero]))
    (ofList : InstalledExprImage sv tv se te sl tl (.const Kernel.stringOfListName []) (.const Kernel.stringOfListName []))
    (value : String) :
    InstalledExprImage sv tv se te sl tl (.lit (.strVal value)) (.lit (.strVal value)) := by
  apply InstalledExprImage.strLit
  unfold Kernel.strLitToConstructor
  apply InstalledExprImage.app ofList
  induction value.toList with
  | nil => exact .app nil char
  | cons character rest ih =>
    exact .app (.app (.app cons char) (.app ofNat (natural zero succ character.toNat))) ih

theorem naturalConstructor_parameters (parameters : List Kernel.Name) (value : Nat) :
    (Kernel.natLitToConstructor value).allLevelParamsDefined parameters = true := by
  cases value <;> rfl

theorem stringConstructor_parameters (parameters : List Kernel.Name) (value : String) :
    (Kernel.strLitToConstructor value).allLevelParamsDefined parameters = true := by
  unfold Kernel.strLitToConstructor
  simp only [Kernel.Expr.allLevelParamsDefined, List.all_nil, Bool.true_and]
  induction value.toList with
  | nil => rfl
  | cons character rest ih => simpa [Kernel.Expr.allLevelParamsDefined, Kernel.Level.allParamsDefined] using ih

/-- Change the source universe assignment only on parameters absent from
the actual expression. Constant values must obey their actual declaration's
parameter-locality law; binder semantic annotations are covered explicitly. -/
theorem InstalledExprImage.source_levels {V : Type u} [Kernel.SetTheory V]
    {sv tv se te sl tl source target}
    (image : InstalledExprImage (V := V) sv tv se te sl tl source target)
    (locality : ∀ name info, se.find? name = some info → ∀ first second,
      (∀ parameter ∈ info.toConstantVal.levelParams, first parameter = second parameter) →
      sv name first = sv name second)
    {parameters : List Kernel.Name} {levels : Kernel.Name → Nat}
    (bounded : source.allLevelParamsDefined parameters = true)
    (agree : ∀ parameter ∈ parameters, levels parameter = sl parameter) :
    InstalledExprImage sv tv se te levels tl source target := by
  induction image with
  | bvar index => exact .bvar index
  | sort equality => exact .sort ((Kernel.Level.eval_ext bounded agree).trans equality)
  | constant sourceLookup targetLookup sourceArity targetArity values =>
    refine .constant sourceLookup targetLookup sourceArity targetArity (Eq.trans ?_ values)
    apply locality _ _ sourceLookup
    apply Kernel.Level.substFn_ext agree
    · simpa only [Kernel.Expr.allLevelParamsDefined, List.all_eq_true] using bounded
    · exact sourceArity
  | app _ _ ihf iha =>
    simp only [Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at bounded
    exact .app (ihf bounded.1) (iha bounded.2)
  | lam _ _ regimes ihd ihb =>
    simp only [Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at bounded
    apply InstalledExprImage.lam (ihd bounded.1.1) (ihb bounded.1.2)
    rw [Kernel.regime, Kernel.PropWhen.holds_ext bounded.2 agree]
    exact regimes
  | forallE _ _ regimes ihd ihb =>
    simp only [Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at bounded
    apply InstalledExprImage.forallE (ihd bounded.1.1) (ihb bounded.1.2)
    rw [Kernel.regime, Kernel.PropWhen.holds_ext bounded.2 agree]
    exact regimes
  | projTable hs ht position _ ih => exact .projTable hs ht position (ih bounded)
  | projFst hs ht _ ih => exact .projFst hs ht (ih bounded)
  | projSnd hs ht _ ih => exact .projSnd hs ht (ih bounded)
  | natLit _ ih => exact .natLit (ih (naturalConstructor_parameters parameters _))
  | strLit _ ih => exact .strLit (ih (stringConstructor_parameters parameters _))

/-- Position-preserving argument images. Every slot has its own expression
correspondence even when several constant identities belong to one fiber. -/
inductive InstalledSpineImage {V : Type u} [Kernel.SetTheory V]
    (sourceValues targetValues : Kernel.Name → (Kernel.Name → Nat) → V)
    (sourceEnv targetEnv : Kernel.Env) (sourceLevels targetLevels : Kernel.Name → Nat) :
    List Kernel.Expr → List Kernel.Expr → Prop
  | nil : InstalledSpineImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels [] []
  | cons {source target sources targets}
      (head : InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels source target)
      (tail : InstalledSpineImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels sources targets) :
      InstalledSpineImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels
        (source :: sources) (target :: targets)

theorem InstalledSpineImage.sorts {V : Type u} [Kernel.SetTheory V]
    {sv tv se te sl tl} {sources targets : List Kernel.Level}
    (image : InstalledSpineImage (V := V) sv tv se te sl tl
      (sources.map Kernel.Expr.sort) (targets.map Kernel.Expr.sort)) :
    sources.map (Kernel.Level.eval sl) = targets.map (Kernel.Level.eval tl) := by
  induction sources generalizing targets with
  | nil => cases targets <;> cases image; rfl
  | cons source sources ih =>
    cases targets with
    | nil => cases image
    | cons target targets =>
      cases image with
      | cons head tail =>
        cases head with
        | sort equality => simp only [List.map_cons, equality, ih tail]

theorem InstalledSpineImage.append {V : Type u} [Kernel.SetTheory V]
    {sv tv se te sl tl source target sources targets}
    (first : InstalledSpineImage (V := V) sv tv se te sl tl source target)
    (second : InstalledSpineImage sv tv se te sl tl sources targets) :
    InstalledSpineImage sv tv se te sl tl (source ++ sources) (target ++ targets) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

theorem InstalledSpineImage.take {V : Type u} [Kernel.SetTheory V]
    {sv tv se te sl tl sources targets}
    (image : InstalledSpineImage (V := V) sv tv se te sl tl sources targets) (count : Nat) :
    InstalledSpineImage sv tv se te sl tl (sources.take count) (targets.take count) := by
  induction image generalizing count with
  | nil => simp only [List.take_nil]; exact .nil
  | cons head tail ih =>
    cases count with
    | zero => exact .nil
    | succ count => exact .cons head (ih count)

theorem InstalledSpineImage.drop {V : Type u} [Kernel.SetTheory V]
    {sv tv se te sl tl sources targets}
    (image : InstalledSpineImage (V := V) sv tv se te sl tl sources targets) (count : Nat) :
    InstalledSpineImage sv tv se te sl tl (sources.drop count) (targets.drop count) := by
  induction image generalizing count with
  | nil => simp only [List.drop_nil]; exact .nil
  | cons head tail ih =>
    cases count with
    | zero => exact .cons head tail
    | succ count => exact ih count

theorem InstalledSpineImage.mkAppN {V : Type u} [Kernel.SetTheory V]
    {sv tv se te sl tl sources targets source target}
    (image : InstalledSpineImage (V := V) sv tv se te sl tl sources targets)
    (head : InstalledExprImage sv tv se te sl tl source target) :
    InstalledExprImage sv tv se te sl tl (Kernel.Expr.mkAppN source sources) (Kernel.Expr.mkAppN target targets) := by
  induction image generalizing source target with
  | nil => exact head
  | cons argument tail ih => exact ih (.app head argument)

/-- A structural map of installed expressions. Constant universe arguments
are selected per source identity, independently of ambient sort/binder level
translation. Neither source names nor universe telescopes must be injective.
This does not purport to be the output of the annotation checker. -/
structure InstalledRenaming where
  name : Kernel.Name → Kernel.Name
  universes : Kernel.Name → List Kernel.Level → List Kernel.Level
  level : Kernel.Level → Kernel.Level
  binder : Kernel.BinderMeta → Kernel.BinderMeta
  projection : Kernel.Name → Nat → Kernel.Name × Nat

/-- Independent symbolic universe selection. Each source parameter may map
to a complete target level, including a selected/constant level; no parameter
injectivity or equal telescope lengths is assumed by these evaluation laws. -/
structure UniverseImage where
  parameter : Kernel.Name → Kernel.Level

def UniverseImage.level (image : UniverseImage) : Kernel.Level → Kernel.Level
  | .zero => .zero
  | .succ u => .succ (image.level u)
  | .max u v => .max (image.level u) (image.level v)
  | .imax u v => .imax (image.level u) (image.level v)
  | .param name => image.parameter name

def UniverseImage.identity : UniverseImage := ⟨Kernel.Level.param⟩

theorem UniverseImage.identity_level (level : Kernel.Level) : UniverseImage.identity.level level = level := by
  induction level <;> simp_all [UniverseImage.identity, UniverseImage.level]

def UniverseImage.valuation (image : UniverseImage) (target : Kernel.Name → Nat) : Kernel.Name → Nat :=
  fun name => Kernel.Level.eval target (image.parameter name)

theorem UniverseImage.identity_valuation (levels : Kernel.Name → Nat) :
    UniverseImage.identity.valuation levels = levels := rfl

def UniverseImage.datum (image : UniverseImage) (datum : Kernel.PropWhen) : Kernel.PropWhen :=
  datum.bindZ fun name => Kernel.Level.zeronessOf (image.parameter name)

def UniverseImage.binder (image : UniverseImage) (metadata : Kernel.BinderMeta) : Kernel.BinderMeta :=
  ⟨image.datum metadata.pw⟩

theorem UniverseImage.eval (image : UniverseImage) (target : Kernel.Name → Nat) (level : Kernel.Level) :
    Kernel.Level.eval target (image.level level) = Kernel.Level.eval (image.valuation target) level := by
  induction level <;> simp_all [UniverseImage.level, UniverseImage.valuation, Kernel.Level.eval]

/-- PropWhen is transported by zero-ness of the selected levels, not by
erasing the datum or retaining its old parameter names. -/
theorem UniverseImage.holds (image : UniverseImage) (target : Kernel.Name → Nat) (datum : Kernel.PropWhen) :
    (image.datum datum).holds target = datum.holds (image.valuation target) := by
  cases datum with
  | never => simp [UniverseImage.datum]
  | ifAllZero names =>
    simp only [UniverseImage.datum, Kernel.PropWhen.bindZ_ifAllZero,
      Kernel.PropWhen.holds_bindZ_go, Kernel.PropWhen.holds_ifAllZero]
    simp only [Kernel.PropWhen.zeronessOf_sound, UniverseImage.valuation]

theorem UniverseImage.regime (image : UniverseImage) (target : Kernel.Name → Nat) (metadata : Kernel.BinderMeta) :
    Kernel.regime target (image.binder metadata).pw =
      Kernel.regime (image.valuation target) metadata.pw := by
  simp only [UniverseImage.binder, Kernel.regime, image.holds]

/-- Actual output datum agreement with the symbolic selector establishes
regime agreement at every target assignment. Establishing this output
agreement from the two real annotation/checking traces is still D11. -/
theorem UniverseImage.output_regime (image : UniverseImage) (target : Kernel.Name → Nat)
    (sourceMetadata targetMetadata : Kernel.BinderMeta)
    (output : targetMetadata = image.binder sourceMetadata) :
    Kernel.regime target targetMetadata.pw =
      Kernel.regime (image.valuation target) sourceMetadata.pw := by
  rw [output]
  exact image.regime target sourceMetadata

/-- The exact kernel telescope selector, including its specified fallback
for unlisted parameters. Source-domain completeness and valid telescope
arity remain separately checked; this function invents no replacement. -/
def UniverseImage.select (parameters : List Kernel.Name) (arguments : List Kernel.Level) : UniverseImage :=
  ⟨Kernel.Level.subst.go parameters arguments⟩

theorem UniverseImage.select_level (parameters : List Kernel.Name) (arguments : List Kernel.Level)
    (level : Kernel.Level) :
    (UniverseImage.select parameters arguments).level level = Kernel.Level.subst parameters arguments level := by
  induction level <;> simp_all [UniverseImage.select, UniverseImage.level, Kernel.Level.subst]

theorem UniverseImage.select_datum (parameters : List Kernel.Name) (arguments : List Kernel.Level)
    (datum : Kernel.PropWhen) :
    (UniverseImage.select parameters arguments).datum datum = Kernel.Level.substPW parameters arguments datum := rfl

theorem UniverseImage.select_valuation (parameters : List Kernel.Name) (arguments : List Kernel.Level)
    (target : Kernel.Name → Nat) :
    (UniverseImage.select parameters arguments).valuation target = Kernel.Level.substFn target parameters arguments := by
  funext name
  exact Kernel.Level.eval_subst_go target parameters arguments name

/-- An actual formal telescope selects the corresponding actual argument.
Distinct formal names are required explicitly; arity alone is insufficient. -/
theorem levelSubst_get (valuation : Kernel.Name → Nat) {parameters : List Kernel.Name}
    {arguments : List Kernel.Level} (unique : parameters.Nodup)
    (arity : arguments.length = parameters.length) (index : Nat) (inside : index < parameters.length) :
    Kernel.Level.substFn valuation parameters arguments parameters[index] =
      Kernel.Level.eval valuation (arguments[index]'(by omega)) := by
  induction parameters generalizing arguments index with
  | nil => simp at inside
  | cons parameter parameters ih =>
    cases arguments with
    | nil => simp at arity
    | cons argument arguments =>
      have distinct := List.nodup_cons.mp unique
      cases index with
      | zero => simp [Kernel.Level.substFn]
      | succ index =>
        have bound : index < parameters.length := by simpa using inside
        have different : parameter ≠ parameters[index] := by
          intro equal
          exact distinct.1 (equal ▸ List.getElem_mem bound)
        simpa only [List.getElem_cons_succ, Kernel.Level.substFn, if_neg different] using
          ih distinct.2 (by simpa using arity) index bound

/-- Positional telescope renaming commutes with the actual universe instance
at every target formal. Assignments outside that telescope are irrelevant
only after the installed model's proved parameter-locality law is applied. -/
theorem UniverseImage.telescope_instance (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    {sourceParameters targetParameters : List Kernel.Name} {arguments : List Kernel.Level}
    (sourceUnique : sourceParameters.Nodup) (targetUnique : targetParameters.Nodup)
    (sameArity : sourceParameters.length = targetParameters.length)
    (argumentArity : arguments.length = sourceParameters.length)
    (parameter : Kernel.Name) (present : parameter ∈ targetParameters) :
    Kernel.Level.substFn
      (Kernel.Level.substFn (image.valuation targetLevels) sourceParameters arguments)
      targetParameters (sourceParameters.map Kernel.Level.param) parameter =
    Kernel.Level.substFn targetLevels targetParameters (arguments.map image.level) parameter := by
  obtain ⟨index, inside, rfl⟩ := List.mem_iff_getElem.mp present
  rw [levelSubst_get _ targetUnique (by simp [sameArity]) index inside,
    levelSubst_get _ targetUnique (by simp [argumentArity, sameArity]) index inside]
  simp only [List.getElem_map, Kernel.Level.eval]
  rw [levelSubst_get _ sourceUnique argumentArity index (by omega)]
  exact (image.eval targetLevels _).symm

/-- Selecting the target formal telescope and pulling its valuation from
the source recovers the original assignment on every source formal. No
claim is made about unrelated ambient parameter names. -/
theorem UniverseImage.telescope_recovery (sourceLevels : Kernel.Name → Nat)
    {sourceParameters targetParameters : List Kernel.Name}
    (sourceUnique : sourceParameters.Nodup) (targetUnique : targetParameters.Nodup)
    (sameArity : sourceParameters.length = targetParameters.length)
    (parameter : Kernel.Name) (present : parameter ∈ sourceParameters) :
    (UniverseImage.select sourceParameters (targetParameters.map Kernel.Level.param)).valuation
      (Kernel.Level.substFn sourceLevels targetParameters (sourceParameters.map Kernel.Level.param)) parameter =
      sourceLevels parameter := by
  rw [UniverseImage.select_valuation]
  obtain ⟨index, inside, rfl⟩ := List.mem_iff_getElem.mp present
  rw [levelSubst_get _ sourceUnique (by simp [sameArity]) index inside]
  simp only [List.getElem_map, Kernel.Level.eval]
  rw [levelSubst_get _ targetUnique (by simp [sameArity]) index (by omega)]
  simp only [List.getElem_map, Kernel.Level.eval]

def UniverseImage.asRenaming (image : UniverseImage) : InstalledRenaming where
  name := id
  universes := fun _ levels => levels.map image.level
  level := image.level
  binder := image.binder
  projection := fun name field => (name, field)

def InstalledRenaming.expr (rename : InstalledRenaming) : Kernel.Expr → Kernel.Expr
  | .bvar i => .bvar i
  | .fvar i type => .fvar i (rename.expr type)
  | .sort u => .sort (rename.level u)
  | .const name levels => .const (rename.name name) (rename.universes name levels)
  | .app f a => .app (rename.expr f) (rename.expr a)
  | .lam type body metadata => .lam (rename.expr type) (rename.expr body) (rename.binder metadata)
  | .forallE type body metadata => .forallE (rename.expr type) (rename.expr body) (rename.binder metadata)
  | .letE type value body => .letE (rename.expr type) (rename.expr value) (rename.expr body)
  | .proj name field value =>
      .proj (rename.projection name field).1 (rename.projection name field).2 (rename.expr value)
  | .lit literal => .lit literal

/-- Connection to the actual kernel expression operation, including every
binder's PropWhen and free-variable annotation. -/
theorem UniverseImage.select_expr (parameters : List Kernel.Name) (arguments : List Kernel.Level)
    (expression : Kernel.Expr) :
    (UniverseImage.select parameters arguments).asRenaming.expr expression =
      expression.instantiateLevelParams parameters arguments := by
  induction expression <;> simp_all [InstalledRenaming.expr, UniverseImage.asRenaming,
    UniverseImage.select_level, UniverseImage.binder, UniverseImage.select_datum,
    Kernel.Expr.instantiateLevelParams]

theorem InstalledRenaming.lift (rename : InstalledRenaming) (expression : Kernel.Expr)
    (amount cutoff : Nat) :
    rename.expr (Kernel.Expr.liftLooseBVars amount cutoff expression) =
      Kernel.Expr.liftLooseBVars amount cutoff (rename.expr expression) := by
  induction expression generalizing cutoff <;>
    simp_all [InstalledRenaming.expr, Kernel.Expr.liftLooseBVars]
  split <;> rfl

/-- Open-variable instantiation: exactly the kernel operation, which leaves
free-variable annotations intact and does not shift its replacement. -/
theorem InstalledRenaming.instantiate1 (rename : InstalledRenaming)
    (expression replacement : Kernel.Expr) (depth : Nat) :
    rename.expr (expression.instantiate1 replacement depth) =
      (rename.expr expression).instantiate1 (rename.expr replacement) depth := by
  induction expression generalizing depth <;>
    simp_all [InstalledRenaming.expr, Kernel.Expr.instantiate1]
  split
  · rfl
  · split <;> rfl

/-- Capture-avoiding substitution also commutes, with the replacement lift
proved explicitly rather than borrowing the open-variable operation's law. -/
theorem InstalledRenaming.instantiate1Lift (rename : InstalledRenaming)
    (expression replacement : Kernel.Expr) (depth : Nat) :
    rename.expr (expression.instantiate1Lift replacement depth) =
      (rename.expr expression).instantiate1Lift (rename.expr replacement) depth := by
  induction expression generalizing depth <;>
    simp_all [InstalledRenaming.expr, Kernel.Expr.instantiate1Lift]
  split
  · exact rename.lift replacement depth 0
  · split <;> rfl

theorem InstalledRenaming.abstract1 (rename : InstalledRenaming)
    (expression : Kernel.Expr) (depth cutoff : Nat) :
    rename.expr (expression.abstract1 depth cutoff) =
      (rename.expr expression).abstract1 depth cutoff := by
  induction expression generalizing cutoff <;>
    simp_all [InstalledRenaming.expr, Kernel.Expr.abstract1]
  split <;> rfl

/-- Cross-environment obligations for one actual installed-expression map.
Every source lookup is checked, including every member of a many-to-one
fiber; a shared target address alone cannot satisfy the value equation.
Projection entries use semantic positions, not just matching owner names.
The primitive literal squares concern their complete constructor syntax.
The two successful installation runs alone do not establish these laws. -/
structure InstalledRenaming.ShapeLaws
    (rename : InstalledRenaming)
    (sourceEnv targetEnv : Kernel.Env) (sourceLevels targetLevels : Kernel.Name → Nat) : Prop where
  sort : ∀ level, Kernel.Level.eval sourceLevels level = Kernel.Level.eval targetLevels (rename.level level)
  regime : ∀ metadata, Kernel.regime sourceLevels metadata.pw = Kernel.regime targetLevels (rename.binder metadata).pw
  projectionTable : ∀ name field entry, sourceEnv.findProj? name field = some entry →
    ∃ targetEntry,
      targetEnv.findProj? (rename.projection name field).1 (rename.projection name field).2 = some targetEntry ∧
      field + entry.off = (rename.projection name field).2 + targetEntry.off
  projectionFirst : ∀ name, sourceEnv.findProj? name 0 = none →
    (rename.projection name 0).2 = 0 ∧ targetEnv.findProj? (rename.projection name 0).1 0 = none
  projectionSecond : ∀ name, sourceEnv.findProj? name 1 = none →
    (rename.projection name 1).2 = 1 ∧ targetEnv.findProj? (rename.projection name 1).1 1 = none
  natLiteral : ∀ n, rename.expr (Kernel.natLitToConstructor n) = Kernel.natLitToConstructor n
  stringLiteral : ∀ s, rename.expr (Kernel.strLitToConstructor s) = Kernel.strLitToConstructor s

structure InstalledRenaming.Laws {V : Type u} [Kernel.SetTheory V]
    (rename : InstalledRenaming)
    (sourceValues targetValues : Kernel.Name → (Kernel.Name → Nat) → V)
    (sourceEnv targetEnv : Kernel.Env) (sourceLevels targetLevels : Kernel.Name → Nat) : Prop
    extends rename.ShapeLaws sourceEnv targetEnv sourceLevels targetLevels where
  constant : ∀ name levels sourceInfo,
    sourceEnv.find? name = some sourceInfo →
    levels.length = sourceInfo.toConstantVal.levelParams.length →
    ∃ targetInfo, targetEnv.find? (rename.name name) = some targetInfo ∧
      (rename.universes name levels).length = targetInfo.toConstantVal.levelParams.length ∧
      sourceValues name (Kernel.Level.substFn sourceLevels sourceInfo.toConstantVal.levelParams levels) =
        targetValues (rename.name name)
          (Kernel.Level.substFn targetLevels targetInfo.toConstantVal.levelParams (rename.universes name levels))

/-- Syntactic dependency evidence for semantic transport. Literals expose
their complete constructor dependency trees; projections retain their source
owner. This predicate does not assert source typing or semantic correctness. -/
inductive ConstantSupport (allowed : Kernel.Name → Prop) : Kernel.Expr → Prop
  | bvar (index) : ConstantSupport allowed (.bvar index)
  | sort (level) : ConstantSupport allowed (.sort level)
  | constant (name levels) (present : allowed name) : ConstantSupport allowed (.const name levels)
  | fvar (index) {type} (annotation : ConstantSupport allowed type) : ConstantSupport allowed (.fvar index type)
  | app {function argument} (left : ConstantSupport allowed function) (right : ConstantSupport allowed argument) :
      ConstantSupport allowed (.app function argument)
  | lam {type body} (metadata) (domain : ConstantSupport allowed type) (value : ConstantSupport allowed body) :
      ConstantSupport allowed (.lam type body metadata)
  | forallE {type body} (metadata) (domain : ConstantSupport allowed type) (value : ConstantSupport allowed body) :
      ConstantSupport allowed (.forallE type body metadata)
  | letE {type value body} (domain : ConstantSupport allowed type)
      (valueSupport : ConstantSupport allowed value) (bodySupport : ConstantSupport allowed body) :
      ConstantSupport allowed (.letE type value body)
  | proj (name field) {value} (owner : allowed name) (operand : ConstantSupport allowed value) :
      ConstantSupport allowed (.proj name field value)
  | natLiteral (n) (constructors : ConstantSupport allowed (Kernel.natLitToConstructor n)) :
      ConstantSupport allowed (.lit (.natVal n))
  | stringLiteral (s) (constructors : ConstantSupport allowed (Kernel.strLitToConstructor s)) :
      ConstantSupport allowed (.lit (.strVal s))

theorem ConstantSupport.mono {allowed larger : Kernel.Name → Prop}
    (extend : ∀ name, allowed name → larger name) {expression : Kernel.Expr}
    (supported : ConstantSupport allowed expression) : ConstantSupport larger expression := by
  induction supported with
  | bvar index => exact .bvar index
  | sort level => exact .sort level
  | constant name levels present => exact .constant name levels (extend name present)
  | fvar index _ ih => exact .fvar index ih
  | app _ _ ihf iha => exact .app ihf iha
  | lam metadata _ _ iht ihb => exact .lam metadata iht ihb
  | forallE metadata _ _ iht ihb => exact .forallE metadata iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | proj name field owner _ ih => exact .proj name field (extend name owner) ih
  | natLiteral n _ ih => exact .natLiteral n ih
  | stringLiteral s _ ih => exact .stringLiteral s ih

theorem ConstantSupport.lift {allowed : Kernel.Name → Prop} {expression : Kernel.Expr}
    (supported : ConstantSupport allowed expression) (amount cutoff : Nat) :
    ConstantSupport allowed (Kernel.Expr.liftLooseBVars amount cutoff expression) := by
  induction supported generalizing cutoff with
  | bvar index =>
    simp only [Kernel.Expr.liftLooseBVars]
    split <;> exact .bvar _
  | sort level => exact .sort level
  | constant name levels present => exact .constant name levels present
  | fvar index annotation _ => exact .fvar index annotation
  | app _ _ ihf iha => exact .app (ihf cutoff) (iha cutoff)
  | lam metadata _ _ iht ihb => exact .lam metadata (iht cutoff) (ihb (cutoff + 1))
  | forallE metadata _ _ iht ihb => exact .forallE metadata (iht cutoff) (ihb (cutoff + 1))
  | letE _ _ _ iht ihv ihb => exact .letE (iht cutoff) (ihv cutoff) (ihb (cutoff + 1))
  | proj name field owner _ ih => exact .proj name field owner (ih cutoff)
  | natLiteral n constructors _ => exact .natLiteral n constructors
  | stringLiteral s constructors _ => exact .stringLiteral s constructors

theorem ConstantSupport.instantiate1 {allowed : Kernel.Name → Prop}
    {expression replacement : Kernel.Expr}
    (supported : ConstantSupport allowed expression)
    (replacementSupport : ConstantSupport allowed replacement) (depth : Nat) :
    ConstantSupport allowed (expression.instantiate1 replacement depth) := by
  induction supported generalizing depth with
  | bvar index =>
    simp only [Kernel.Expr.instantiate1]
    split
    · exact replacementSupport
    · split <;> exact .bvar _
  | sort level => exact .sort level
  | constant name levels present => exact .constant name levels present
  | fvar index annotation _ => exact .fvar index annotation
  | app _ _ ihf iha => exact .app (ihf depth) (iha depth)
  | lam metadata _ _ iht ihb => exact .lam metadata (iht depth) (ihb (depth + 1))
  | forallE metadata _ _ iht ihb => exact .forallE metadata (iht depth) (ihb (depth + 1))
  | letE _ _ _ iht ihv ihb => exact .letE (iht depth) (ihv depth) (ihb (depth + 1))
  | proj name field owner _ ih => exact .proj name field owner (ih depth)
  | natLiteral n constructors _ => exact .natLiteral n constructors
  | stringLiteral s constructors _ => exact .stringLiteral s constructors

theorem ConstantSupport.instantiate1Lift {allowed : Kernel.Name → Prop}
    {expression replacement : Kernel.Expr}
    (supported : ConstantSupport allowed expression)
    (replacementSupport : ConstantSupport allowed replacement) (depth : Nat) :
    ConstantSupport allowed (expression.instantiate1Lift replacement depth) := by
  induction supported generalizing depth with
  | bvar index =>
    simp only [Kernel.Expr.instantiate1Lift]
    split
    · exact replacementSupport.lift depth 0
    · split <;> exact .bvar _
  | sort level => exact .sort level
  | constant name levels present => exact .constant name levels present
  | fvar index annotation _ => exact .fvar index annotation
  | app _ _ ihf iha => exact .app (ihf depth) (iha depth)
  | lam metadata _ _ iht ihb => exact .lam metadata (iht depth) (ihb (depth + 1))
  | forallE metadata _ _ iht ihb => exact .forallE metadata (iht depth) (ihb (depth + 1))
  | letE _ _ _ iht ihv ihb => exact .letE (iht depth) (ihv depth) (ihb (depth + 1))
  | proj name field owner _ ih => exact .proj name field owner (ih depth)
  | natLiteral n constructors _ => exact .natLiteral n constructors
  | stringLiteral s constructors _ => exact .stringLiteral s constructors

/-- Prefix-local compatibility. In particular, a definition whose value
only refers to earlier names does not need its own constant-value equation
as a hypothesis of semantic body transport. -/
structure InstalledRenaming.ScopedLaws {V : Type u} [Kernel.SetTheory V]
    (rename : InstalledRenaming) (allowed : Kernel.Name → Prop)
    (sourceValues targetValues : Kernel.Name → (Kernel.Name → Nat) → V)
    (sourceEnv targetEnv : Kernel.Env) (sourceLevels targetLevels : Kernel.Name → Nat) : Prop
    extends rename.ShapeLaws sourceEnv targetEnv sourceLevels targetLevels where
  constant : ∀ name, allowed name → ∀ levels sourceInfo,
    sourceEnv.find? name = some sourceInfo →
    levels.length = sourceInfo.toConstantVal.levelParams.length →
    ∃ targetInfo, targetEnv.find? (rename.name name) = some targetInfo ∧
      (rename.universes name levels).length = targetInfo.toConstantVal.levelParams.length ∧
      sourceValues name (Kernel.Level.substFn sourceLevels sourceInfo.toConstantVal.levelParams levels) =
        targetValues (rename.name name)
          (Kernel.Level.substFn targetLevels targetInfo.toConstantVal.levelParams (rename.universes name levels))

theorem InstalledRenaming.denotes_on {V : Type u} [Kernel.SetTheory V]
    {rename : InstalledRenaming} {allowed : Kernel.Name → Prop}
    {sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels}
    (laws : rename.ScopedLaws (V := V) allowed sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels)
    {ρ : Nat → V} {expression : Kernel.Expr} {value : V}
    (supported : ConstantSupport allowed expression)
    (denoted : Kernel.Denotes sourceValues sourceEnv sourceLevels ρ expression value) :
    Kernel.Denotes targetValues targetEnv targetLevels ρ (rename.expr expression) value := by
  induction denoted with
  | bvar => exact .bvar
  | sort => rw [laws.sort]; exact .sort
  | const lookup arity =>
    cases supported with
    | constant _ _ present =>
      obtain ⟨info, lookup', arity', values⟩ := laws.constant _ present _ _ lookup arity
      rw [values]
      exact .const lookup' arity'
  | app _ _ ihf iha =>
    cases supported with
    | app sf sa => exact .app (ihf sf) (iha sa)
  | lam _ _ proof ihA ihF =>
    cases supported with
    | lam metadata st sb =>
      rw [laws.regime]
      exact .lam (ihA st) (fun x hx => ihF x hx sb) (fun h => proof ((laws.regime _).trans h))
  | pi _ _ proof ihA ihB =>
    cases supported with
    | forallE metadata st sb =>
      rw [laws.regime]
      exact .pi (ihA st) (fun x hx => ihB x hx sb) (fun h => proof ((laws.regime _).trans h))
  | proj_table lookup _ ih =>
    cases supported with
    | proj _ _ _ operand =>
      obtain ⟨entry, lookup', position⟩ := laws.projectionTable _ _ _ lookup
      rw [position]
      exact .proj_table lookup' (ih operand)
  | proj_fst lookup _ ih =>
    cases supported with
    | proj _ _ _ operand =>
      obtain ⟨position, lookup'⟩ := laws.projectionFirst _ lookup
      simp only [InstalledRenaming.expr, position]
      exact .proj_fst lookup' (ih operand)
  | proj_snd lookup _ ih =>
    cases supported with
    | proj _ _ _ operand =>
      obtain ⟨position, lookup'⟩ := laws.projectionSecond _ lookup
      simp only [InstalledRenaming.expr, position]
      exact .proj_snd lookup' (ih operand)
  | natLit _ ih =>
    cases supported with
    | natLiteral _ constructors => exact .natLit (laws.natLiteral _ ▸ ih constructors)
  | strLit _ ih =>
    cases supported with
    | stringLiteral _ constructors => exact .strLit (laws.stringLiteral _ ▸ ih constructors)

/-- Compatible fibers identify values only at the same selected target
instance. This does not assume source-key injectivity or search for a reverse
alias; both original source identities and lookups remain in the statement. -/
theorem InstalledRenaming.Laws.fiber {V : Type u} [Kernel.SetTheory V]
    {rename : InstalledRenaming} {sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels}
    (laws : rename.Laws (V := V) sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels)
    {left right : Kernel.Name} {leftLevels rightLevels : List Kernel.Level}
    {leftInfo rightInfo : Kernel.ConstantInfo}
    (leftLookup : sourceEnv.find? left = some leftInfo)
    (rightLookup : sourceEnv.find? right = some rightInfo)
    (leftArity : leftLevels.length = leftInfo.toConstantVal.levelParams.length)
    (rightArity : rightLevels.length = rightInfo.toConstantVal.levelParams.length)
    (sameName : rename.name left = rename.name right)
    (sameSelection : rename.universes left leftLevels = rename.universes right rightLevels) :
    sourceValues left (Kernel.Level.substFn sourceLevels leftInfo.toConstantVal.levelParams leftLevels) =
      sourceValues right (Kernel.Level.substFn sourceLevels rightInfo.toConstantVal.levelParams rightLevels) := by
  obtain ⟨leftTarget, leftTargetLookup, _, leftValue⟩ := laws.constant _ _ _ leftLookup leftArity
  obtain ⟨rightTarget, rightTargetLookup, _, rightValue⟩ := laws.constant _ _ _ rightLookup rightArity
  rw [sameName, rightTargetLookup] at leftTargetLookup
  obtain rfl := Option.some.inj leftTargetLookup
  rw [leftValue, rightValue, sameName, sameSelection]

/-- Many-to-one, level-selecting semantic renaming of the actual expression.
This is a forward law under explicit installation compatibility, not a proof
that independent annotation runs establish that compatibility. In particular
no equation between arbitrary independently chosen models is inferred. -/
theorem InstalledRenaming.denotes {V : Type u} [Kernel.SetTheory V]
    {rename : InstalledRenaming} {sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels}
    (laws : rename.Laws (V := V) sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels)
    {ρ : Nat → V} {expression : Kernel.Expr} {value : V}
    (denoted : Kernel.Denotes sourceValues sourceEnv sourceLevels ρ expression value) :
    Kernel.Denotes targetValues targetEnv targetLevels ρ (rename.expr expression) value := by
  induction denoted with
  | bvar => exact .bvar
  | sort => rw [laws.sort]; exact .sort
  | const lookup arity =>
    obtain ⟨info, lookup', arity', values⟩ := laws.constant _ _ _ lookup arity
    rw [values]
    exact .const lookup' arity'
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ proof ihA ihF =>
    rw [laws.regime]
    exact .lam ihA ihF (fun h => proof ((laws.regime _).trans h))
  | pi _ _ proof ihA ihB =>
    rw [laws.regime]
    exact .pi ihA ihB (fun h => proof ((laws.regime _).trans h))
  | proj_table lookup _ ih =>
    obtain ⟨entry, lookup', position⟩ := laws.projectionTable _ _ _ lookup
    rw [position]
    exact .proj_table lookup' ih
  | proj_fst lookup _ ih =>
    obtain ⟨position, lookup'⟩ := laws.projectionFirst _ lookup
    simp only [InstalledRenaming.expr, position]
    exact .proj_fst lookup' ih
  | proj_snd lookup _ ih =>
    obtain ⟨position, lookup'⟩ := laws.projectionSecond _ lookup
    simp only [InstalledRenaming.expr, position]
    exact .proj_snd lookup' ih
  | natLit _ ih => exact .natLit (laws.natLiteral _ ▸ ih)
  | strLit _ ih => exact .strLit (laws.stringLiteral _ ▸ ih)

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

/-- A semantic selector defined entirely by the original constructor/field
relation. It does not inspect or apply a lowered projection. The off-carrier
fallback is irrelevant to the typed abstraction and is never an export rule. -/
noncomputable def originalProjectionSelection {source : Source} (site : SourceProjectionSite source)
    {V : Type u} [Kernel.SetTheory V] (values : Kernel.Name → (Kernel.Name → Nat) → V)
    (levels : Kernel.Name → Nat) (parameters : List V)
    (valid : SourceFieldValues site V → Prop) (subject : V) : V := by
  classical
  exact if present : ∃ fields, valid fields ∧
      originalConstructorValue site values levels parameters fields = subject then
    originalSelectedField site (Classical.choose present)
  else Kernel.SetTheory.pt

theorem originalProjectionSelection_reading {source : Source} (site : SourceProjectionSite source)
    {V : Type u} [Kernel.SetTheory V] (values : Kernel.Name → (Kernel.Name → Nat) → V)
    (levels : Kernel.Name → Nat) (parameters : List V)
    (valid : SourceFieldValues site V → Prop) (subject : V)
    (present : ∃ fields, valid fields ∧
      originalConstructorValue site values levels parameters fields = subject) :
    OriginalProjectionValue site values levels parameters valid subject
      (originalProjectionSelection site values levels parameters valid subject) := by
  classical
  unfold originalProjectionSelection
  rw [dif_pos present]
  exact ⟨Classical.choose present, (Classical.choose_spec present).1,
    (Classical.choose_spec present).2, rfl⟩

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

theorem InstalledTelescope.append {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ middleρ finalρ : Nat → V}
    {expression middle result : Kernel.Expr} {first second : List V}
    (firstTuple : InstalledTelescope values env levels ρ expression first middleρ middle)
    (suffix : InstalledTelescope values env levels middleρ middle second finalρ result) :
    InstalledTelescope values env levels ρ expression (first ++ second) finalρ result := by
  induction firstTuple with
  | nil => exact suffix
  | cons domain typed rest ih => exact .cons domain typed (ih suffix)

/-- Transport the full dependent tuple between the two installed models.
The target residual is accompanied by its source image; successful isolated
domain checks or matching telescope lengths would not establish this result. -/
theorem InstalledTelescope.image {V : Type u} [Kernel.SetTheory V]
    {sourceValues targetValues : Kernel.Name → (Kernel.Name → Nat) → V}
    {sourceEnv targetEnv : Kernel.Env} {sourceLevels targetLevels : Kernel.Name → Nat}
    {ρ finalρ : Nat → V} {source result target : Kernel.Expr} {arguments : List V}
    (typed : InstalledTelescope sourceValues sourceEnv sourceLevels ρ source arguments finalρ result)
    (image : InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels source target) :
    ∃ targetResult,
      InstalledTelescope targetValues targetEnv targetLevels ρ target arguments finalρ targetResult ∧
      InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels result targetResult := by
  induction typed generalizing target with
  | nil => exact ⟨target, .nil, image⟩
  | cons domainRead argumentTyped rest ih =>
    cases image with
    | forallE domainImage bodyImage regimes =>
      obtain ⟨targetResult, transported, residualImage⟩ := ih bodyImage
      exact ⟨targetResult, .cons (domainImage.denotes domainRead) argumentTyped transported, residualImage⟩

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

/-- Insert a semantic argument below the indicated number of inner binders.
Unlike a syntactic substitution this carries no expression annotation. -/
def insertValuation {V : Type u} : Nat → V → (Nat → V) → Nat → V
  | 0, value, valuation => Kernel.push value valuation
  | depth + 1, value, valuation =>
      Kernel.push (valuation 0) (insertValuation depth value (fun index => valuation (index + 1)))

theorem insertValuation_at {V : Type u} (depth : Nat) (value : V) (valuation : Nat → V) :
    insertValuation depth value valuation depth = value := by
  induction depth generalizing valuation with
  | zero => rfl
  | succ depth ih => exact ih _

theorem insertValuation_below {V : Type u} {depth index : Nat} (value : V) (valuation : Nat → V)
    (below : index < depth) : insertValuation depth value valuation index = valuation index := by
  induction depth generalizing index valuation with
  | zero => omega
  | succ depth ih =>
    cases index with
    | zero => rfl
    | succ index => exact ih _ (by omega)

theorem insertValuation_above {V : Type u} {depth index : Nat} (value : V) (valuation : Nat → V)
    (above : depth < index) : insertValuation depth value valuation index = valuation (index - 1) := by
  induction depth generalizing index valuation with
  | zero =>
    cases index with
    | zero => omega
    | succ index => rfl
  | succ depth ih =>
    cases index with
    | zero => omega
    | succ index =>
      have read := ih (fun index => valuation (index + 1)) (index := index) (by omega)
      have cancel : index - 1 + 1 = index := by omega
      simpa only [insertValuation, Kernel.push, Nat.add_sub_cancel, cancel] using read

/-- Public denotation under capture-avoiding substitution. The replacement
is read in the outer valuation, with the inner `depth` binders removed;
its occurrence is lifted over those binders by the actual kernel operation.
All lambda/Pi regime side conditions are preserved by the derivation. -/
theorem denotes_instantiate1Lift {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V} {expression : Kernel.Expr} {value : V}
    (denoted : Kernel.Denotes values env levels ρ expression value)
    {replacement : Kernel.Expr} {argument : V} {depth : Nat} {target : Nat → V}
    (related : ρ = insertValuation depth argument target)
    (replacementRead : Kernel.Denotes values env levels (fun index => target (index + depth)) replacement argument) :
    Kernel.Denotes values env levels target (expression.instantiate1Lift replacement depth) value := by
  induction denoted generalizing depth target with
  | bvar =>
    rename_i old index
    rw [related]
    simp only [Kernel.Expr.instantiate1Lift]
    split
    · rename_i equal
      subst index
      rw [insertValuation_at]
      exact denotes_lift replacementRead (by intro index; rw [if_pos (Nat.zero_le index)])
    · rename_i unequal
      split
      · rename_i above
        rw [insertValuation_above argument target above]
        exact .bvar
      · rename_i notAbove
        rw [insertValuation_below argument target (by omega)]
        exact .bvar
  | sort => exact .sort
  | const lookup arity => exact .const lookup arity
  | app _ _ ihf iha => exact .app (ihf related replacementRead) (iha related replacementRead)
  | lam _ _ proof ihA ihF =>
    refine .lam (ihA related replacementRead) (fun x hx => ihF x hx ?_ ?_) proof
    · rw [related]; rfl
    · exact replacementRead
  | pi _ _ proof ihA ihB =>
    refine .pi (ihA related replacementRead) (fun x hx => ihB x hx ?_ ?_) proof
    · rw [related]; rfl
    · exact replacementRead
  | proj_table lookup _ ih => exact .proj_table lookup (ih related replacementRead)
  | proj_fst lookup _ ih => exact .proj_fst lookup (ih related replacementRead)
  | proj_snd lookup _ ih => exact .proj_snd lookup (ih related replacementRead)
  | natLit _ ih =>
    apply Kernel.Denotes.natLit
    have substituted := ih related replacementRead
    simpa only [Kernel.Expr.instantiate1Lift_eq_self
      (Kernel.natLitToConstructor_looseBVars _)] using substituted
  | strLit _ ih =>
    apply Kernel.Denotes.strLit
    have substituted := ih related replacementRead
    simpa only [Kernel.Expr.instantiate1Lift_eq_self
      (Kernel.strLitToConstructor_looseBVars _ _)] using substituted

def pushArguments {V : Type u} (ρ : Nat → V) : List V → Nat → V
  | [] => ρ
  | argument :: rest => pushArguments (Kernel.push argument ρ) rest

def ValuationAgreement {V : Type u} (bound : Nat) (ρ target : Nat → V) : Prop :=
  ∀ index, index < bound → target index = ρ index

theorem ValuationAgreement.push {V : Type u} {bound : Nat} {ρ target : Nat → V}
    (agreement : ValuationAgreement bound ρ target) (value : V) :
    ValuationAgreement (bound + 1) (Kernel.push value ρ) (Kernel.push value target) := by
  intro index inside
  cases index with
  | zero => rfl
  | succ index => exact agreement index (by omega)

/-- Public denotation depends only on the bound variables that can occur.
This allows independently typed tuples to share one caller valuation without
equating arbitrary ambient valuations or changing their semantic arguments. -/
theorem denotes_valuation {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V} {expression : Kernel.Expr} {value : V}
    (denoted : Kernel.Denotes values env levels ρ expression value)
    {bound : Nat} (bounded : expression.looseBVarsBounded bound = true)
    {target : Nat → V} (agreement : ValuationAgreement bound ρ target) :
    Kernel.Denotes values env levels target expression value := by
  induction denoted generalizing bound target with
  | bvar =>
    rename_i old index
    have inside : index < bound := by simpa only [Kernel.Expr.looseBVarsBounded, decide_eq_true_eq] using bounded
    rw [← agreement index inside]
    exact .bvar
  | sort => exact .sort
  | const lookup arity => exact .const lookup arity
  | app _ _ ihf iha =>
    simp only [Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at bounded
    exact .app (ihf bounded.1 agreement) (iha bounded.2 agreement)
  | lam _ _ proof ihA ihF =>
    simp only [Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at bounded
    exact .lam (ihA bounded.1 agreement) (fun x hx => ihF x hx bounded.2 (agreement.push x)) proof
  | pi _ _ proof ihA ihB =>
    simp only [Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at bounded
    exact .pi (ihA bounded.1 agreement) (fun x hx => ihB x hx bounded.2 (agreement.push x)) proof
  | proj_table lookup _ ih => exact .proj_table lookup (ih bounded agreement)
  | proj_fst lookup _ ih => exact .proj_fst lookup (ih bounded agreement)
  | proj_snd lookup _ ih => exact .proj_snd lookup (ih bounded agreement)
  | natLit _ ih =>
    exact .natLit (ih (Kernel.Expr.looseBVarsBounded_mono (Nat.zero_le bound)
      (Kernel.natLitToConstructor_looseBVars _)) agreement)
  | strLit _ ih =>
    exact .strLit (ih (Kernel.Expr.looseBVarsBounded_mono (Nat.zero_le bound)
      (Kernel.strLitToConstructor_looseBVars _ _)) agreement)

/-- Rebase the entire dependent tuple into an agreeing ambient valuation.
At bound zero the ambient valuation is unrestricted; every consumed argument
is pushed unchanged, so later dependent domains retain their original values. -/
theorem InstalledTelescope.rebase {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V}
    {expression result : Kernel.Expr} {arguments : List V}
    (typed : InstalledTelescope values env levels ρ expression arguments finalρ result)
    {bound : Nat} (bounded : expression.looseBVarsBounded bound = true)
    {target : Nat → V} (agreement : ValuationAgreement bound ρ target) :
    ValuationAgreement (bound + arguments.length) finalρ (pushArguments target arguments) ∧
      InstalledTelescope values env levels target expression arguments (pushArguments target arguments) result := by
  induction typed generalizing bound target with
  | nil => exact ⟨agreement, .nil⟩
  | cons domainRead argumentTyped rest ih =>
    simp only [Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at bounded
    obtain ⟨finalAgreement, rebased⟩ := ih bounded.2 (agreement.push _)
    constructor
    · simpa only [pushArguments, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using finalAgreement
    · exact .cons (denotes_valuation domainRead bounded.1 agreement) argumentTyped rebased

/-- Closing a locally closed open term under additional binders is the
actual capture-avoiding lift of its original closure. Free-variable type
metadata is erased by both sides of `closeN`, not semantically interpreted. -/
theorem closeN_under_binders (expression : Kernel.Expr) (depth amount : Nat) :
    ∀ cutoff, expression.looseBVarsBounded cutoff = true →
      expression.closeN depth (amount + cutoff) =
        (expression.closeN depth cutoff).liftLooseBVars amount cutoff := by
  induction expression <;> intro cutoff bounded <;>
    simp_all [Kernel.Expr.closeN, Kernel.Expr.looseBVarsBounded,
      Kernel.Expr.liftLooseBVars, Nat.add_assoc]
  case bvar index => omega
  case fvar index type ih => omega

/-- Close the exact checker substitution as a public capture-avoiding
substitution. Both the body and replacement bounds are explicit; no source
normalization or annotation-image premise is inferred by this structural law. -/
theorem closeN_substitution (expression replacement : Kernel.Expr) (depth : Nat)
    (replacementBounded : replacement.looseBVarsBounded 0 = true) :
    ∀ cutoff, expression.looseBVarsBounded (cutoff + 1) = true →
      (expression.instantiate1 replacement cutoff).closeN depth cutoff =
        (expression.closeN depth (cutoff + 1)).instantiate1Lift
          (replacement.closeN depth) cutoff := by
  induction expression <;> intro cutoff bounded <;>
    simp_all [Kernel.Expr.closeN, Kernel.Expr.instantiate1,
      Kernel.Expr.instantiate1Lift, Kernel.Expr.looseBVarsBounded]
  case bvar index =>
    by_cases same : index = cutoff
    · subst index
      simpa using closeN_under_binders replacement depth cutoff 0 replacementBounded
    · have below : ¬index > cutoff := by omega
      simp [same, below, Kernel.Expr.closeN]
  case fvar index type ih =>
    have unequal : cutoff + 1 + (depth - 1 - index) ≠ cutoff := by omega
    have above : cutoff + 1 + (depth - 1 - index) > cutoff := by omega
    simp [unequal, above]

/-- Substitute an outer argument through the entire dependent telescope.
The final valuation and residual expression record every consumed binder;
later domains therefore retain their dependencies on earlier arguments. -/
theorem InstalledTelescope.instantiate1Lift {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V}
    {expression result : Kernel.Expr} {arguments : List V}
    (typed : InstalledTelescope values env levels ρ expression arguments finalρ result)
    {replacement : Kernel.Expr} {argument : V} {depth : Nat} {target : Nat → V}
    (related : ρ = insertValuation depth argument target)
    (replacementRead : Kernel.Denotes values env levels
      (fun index => target (index + depth)) replacement argument) :
    finalρ = insertValuation (depth + arguments.length) argument
        (pushArguments target arguments) ∧
      InstalledTelescope values env levels target
        (expression.instantiate1Lift replacement depth) arguments
        (pushArguments target arguments)
        (result.instantiate1Lift replacement (depth + arguments.length)) := by
  induction typed generalizing depth target with
  | nil => exact ⟨related, .nil⟩
  | @cons old domain body binder next A arguments finalρ result domainRead argumentTyped rest ih =>
    have pushed : Kernel.push next old = insertValuation (depth + 1) argument
        (Kernel.push next target) := by rw [related]; rfl
    obtain ⟨finalRelated, substituted⟩ := ih pushed replacementRead
    constructor
    · simpa only [pushArguments, List.length_cons, Nat.add_assoc,
        Nat.add_comm 1] using finalRelated
    · simp only [Kernel.Expr.instantiate1Lift, pushArguments, List.length_cons]
      apply InstalledTelescope.cons (denotes_instantiate1Lift domainRead related replacementRead)
        argumentTyped
      simpa only [Nat.add_assoc, Nat.add_comm 1] using substituted

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

open Kernel.SetTheory in
/-- Interpret the equality-to-P leaf of a checked coverage continuation.
Equality is used only at a typed carrier and typed endpoints, exactly where
the installed model supplies its law. The conclusion respects the actual
implication binder's regime. -/
theorem installed_eq_implication_inhabited {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (model : Kernel.Model V env)
    {levels : Kernel.Name → Nat} {ρ : Nat → V} {level : Kernel.Level}
    {equality : Kernel.Expr} {binder : Kernel.BinderMeta} {index : Nat}
    {E carrier left right proposition type : V}
    (eqConstant : Kernel.Denotes model.cval env levels ρ (.const Kernel.eqName [level]) E)
    (carrierTyped : carrier ∈ˢ univ (Kernel.Level.eval levels level))
    (leftTyped : left ∈ˢ carrier) (rightTyped : right ∈ˢ carrier)
    (equalityRead : Kernel.Denotes model.cval env levels ρ equality
      (app (app (app E carrier) left) right))
    (denoted : Kernel.Denotes model.cval env levels ρ
      (.forallE equality (.bvar (index + 1)) binder) type)
    (propositionSlot : ρ index = proposition)
    (continuation : left = right → pt ∈ˢ proposition) :
    ∃ member, member ∈ˢ type := by
  cases denoted with
  | pi hA hB hP =>
    obtain rfl := Kernel.Denotes_functional equalityRead hA
    refine ⟨Kernel.SetModel.lamR (Kernel.regime levels binder.pw) _ (fun _ => pt),
      Kernel.SetModel.lamR_mem ?_⟩
    intro witness witnessTyped
    have read := hB witness witnessTyped
    have equalLaw := model.eq_equality level levels ρ E carrier left right
      eqConstant carrierTyped leftTyped rightTyped
    rw [equalLaw] at witnessTyped
    have equal : left = right := Kernel.SetTheory.mem_eqv witnessTyped
    have resultEq := Kernel.Denotes_functional read
      (Kernel.Denotes.bvar (ρ := Kernel.push witness ρ) (i := index + 1))
    rw [resultEq]
    simpa only [Kernel.push, propositionSlot] using continuation equal

theorem InstalledTelescope.final_valuation {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V}
    {expression result : Kernel.Expr} {arguments : List V}
    (typed : InstalledTelescope values env levels ρ expression arguments finalρ result) :
    finalρ = pushArguments ρ arguments := by
  induction typed with
  | nil => rfl
  | cons _ _ _ ih => exact ih

theorem pushArguments_above {V : Type u} (arguments : List V) (ρ : Nat → V) (index : Nat) :
    pushArguments ρ arguments (arguments.length + index) = ρ index := by
  induction arguments generalizing ρ index with
  | nil => simp [pushArguments]
  | cons argument rest ih =>
    simpa only [pushArguments, List.length_cons, Nat.add_assoc, Nat.add_comm 1,
      Kernel.push] using ih (Kernel.push argument ρ) (index + 1)

theorem pushArguments_append {V : Type u} (ρ : Nat → V) (first second : List V) :
    pushArguments ρ (first ++ second) = pushArguments (pushArguments ρ first) second := by
  induction first generalizing ρ with
  | nil => rfl
  | cons argument rest ih => exact ih (Kernel.push argument ρ)

theorem pushArguments_get {V : Type u} (arguments : List V) (ρ : Nat → V)
    (index : Nat) (inside : index < arguments.length) :
    pushArguments ρ arguments (arguments.length - 1 - index) = arguments[index] := by
  induction arguments generalizing ρ index with
  | nil => simp at inside
  | cons argument rest ih =>
    cases index with
    | zero =>
      simpa only [pushArguments, List.length_cons, Nat.add_sub_cancel,
        Nat.sub_zero, List.getElem_cons_zero, Nat.add_zero, Kernel.push]
        using pushArguments_above rest (Kernel.push argument ρ) 0
    | succ index =>
      have inRest : index < rest.length := by simpa using inside
      have position : (argument :: rest).length - 1 - (index + 1) = rest.length - 1 - index := by
        simp only [List.length_cons]
        omega
      simpa only [position, pushArguments, List.getElem_cons_succ] using
        ih (Kernel.push argument ρ) index inRest

inductive DenotesSpine {V : Type u} [Kernel.SetTheory V]
    (values : Kernel.Name → (Kernel.Name → Nat) → V) (env : Kernel.Env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V) : List Kernel.Expr → List V → Prop
  | nil : DenotesSpine values env levels ρ [] []
  | cons {expression value expressions arguments}
      (head : Kernel.Denotes values env levels ρ expression value)
      (tail : DenotesSpine values env levels ρ expressions arguments) :
      DenotesSpine values env levels ρ (expression :: expressions) (value :: arguments)

theorem DenotesSpine.of_get {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V}
    {expressions : List Kernel.Expr} {arguments : List V}
    (length : expressions.length = arguments.length)
    (elements : ∀ index (inside : index < expressions.length),
      Kernel.Denotes values env levels ρ expressions[index]
        (arguments[index]'(by omega))) :
    DenotesSpine values env levels ρ expressions arguments := by
  induction expressions generalizing arguments with
  | nil =>
    have empty : arguments = [] := by simpa using length.symm
    subst arguments
    exact .nil
  | cons expression rest ih =>
    cases arguments with
    | nil => simp at length
    | cons argument arguments =>
      refine .cons (elements 0 (by simp)) (ih (by simpa using length) ?_)
      intro index inside
      exact elements (index + 1) (by simpa using inside)

theorem DenotesSpine.append {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V}
    {left right : List Kernel.Expr} {leftValues rightValues : List V}
    (first : DenotesSpine values env levels ρ left leftValues)
    (second : DenotesSpine values env levels ρ right rightValues) :
    DenotesSpine values env levels ρ (left ++ right) (leftValues ++ rightValues) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

theorem DenotesSpine.take {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V}
    {expressions : List Kernel.Expr} {arguments : List V}
    (spine : DenotesSpine values env levels ρ expressions arguments) (count : Nat) :
    DenotesSpine values env levels ρ (expressions.take count) (arguments.take count) := by
  induction spine generalizing count with
  | nil => simp only [List.take_nil]; exact .nil
  | cons head tail ih =>
    cases count with
    | zero => exact .nil
    | succ count => exact .cons head (ih count)

theorem DenotesSpine.drop {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V}
    {expressions : List Kernel.Expr} {arguments : List V}
    (spine : DenotesSpine values env levels ρ expressions arguments) (count : Nat) :
    DenotesSpine values env levels ρ (expressions.drop count) (arguments.drop count) := by
  induction spine generalizing count with
  | nil => simp only [List.drop_nil]; exact .nil
  | cons head tail ih =>
    cases count with
    | zero => exact .cons head tail
    | succ count => exact ih count

open Kernel.SetTheory in
/-- A typed application in a fixed public valuation. Each residual is the
actual capture-avoiding substitution, rather than a type chosen solely by
semantic equality. This does not assert an internal annotation reading. -/
inductive DenotedApplication {V : Type u} [Kernel.SetTheory V]
    (values : Kernel.Name → (Kernel.Name → Nat) → V) (env : Kernel.Env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V) :
    Kernel.Expr → List Kernel.Expr → List V → Kernel.Expr → Prop
  | nil {type} : DenotedApplication values env levels ρ type [] [] type
  | cons {domain body binder expression argument A expressions arguments residual}
      (domainRead : Kernel.Denotes values env levels ρ domain A)
      (argumentRead : Kernel.Denotes values env levels ρ expression argument)
      (argumentTyped : argument ∈ˢ A)
      (rest : DenotedApplication values env levels ρ (body.instantiate1Lift expression)
        expressions arguments residual) :
      DenotedApplication values env levels ρ (.forallE domain body binder)
        (expression :: expressions) (argument :: arguments) residual

/-- Arbitrary typed semantic arguments may be represented by any expression
spine with the stated public readings. Domain membership for the substituted
suffix is derived from the original dependent telescope. -/
theorem DenotedApplication.of_telescope {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V}
    {type result : Kernel.Expr} {expressions : List Kernel.Expr} {arguments : List V}
    (typed : InstalledTelescope values env levels ρ type arguments finalρ result)
    (readings : DenotesSpine values env levels ρ expressions arguments) :
    ∃ residual, DenotedApplication values env levels ρ type expressions arguments residual := by
  induction readings generalizing type finalρ result with
  | nil => exact ⟨type, .nil⟩
  | cons argumentRead restRead ih =>
    cases typed with
    | cons domainRead argumentTyped rest =>
      obtain ⟨_, substituted⟩ := rest.instantiate1Lift (depth := 0) rfl argumentRead
      obtain ⟨residual, applied⟩ := ih substituted
      exact ⟨residual, .cons domainRead argumentRead argumentTyped applied⟩

/-- Transport a dependent application through exact type and argument images.
Each substituted suffix remains related, and the resulting target residual
has an explicit image of the actual source residual. -/
theorem DenotedApplication.image {V : Type u} [Kernel.SetTheory V]
    {sourceValues targetValues : Kernel.Name → (Kernel.Name → Nat) → V}
    {sourceEnv targetEnv : Kernel.Env} {sourceLevels targetLevels : Kernel.Name → Nat}
    {ρ : Nat → V} {sourceType sourceResidual targetType : Kernel.Expr}
    {sources targets : List Kernel.Expr} {arguments : List V}
    (application : DenotedApplication sourceValues sourceEnv sourceLevels ρ sourceType sources arguments sourceResidual)
    (typeImage : InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels sourceType targetType)
    (argumentsImage : InstalledSpineImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels sources targets) :
    ∃ targetResidual,
      DenotedApplication targetValues targetEnv targetLevels ρ targetType targets arguments targetResidual ∧
      InstalledExprImage sourceValues targetValues sourceEnv targetEnv sourceLevels targetLevels sourceResidual targetResidual := by
  induction application generalizing targetType targets with
  | nil =>
    cases argumentsImage
    exact ⟨targetType, .nil, typeImage⟩
  | cons domainRead argumentRead argumentTyped rest ih =>
    cases typeImage with
    | forallE domainImage bodyImage regimes =>
      cases argumentsImage with
      | cons argumentImage tailImage =>
        obtain ⟨targetResidual, transported, residualImage⟩ :=
          ih (bodyImage.instantiate1Lift argumentImage 0) tailImage
        exact ⟨targetResidual, .cons (domainImage.denotes domainRead)
          (argumentImage.denotes argumentRead) argumentTyped transported, residualImage⟩

/-- Fresh de Bruijn variables represent every semantic tuple in the valuation
extended by exactly that tuple, in its original telescope order. -/
def argumentVariables (count : Nat) : List Kernel.Expr :=
  (List.range count).map fun index => .bvar (count - 1 - index)

theorem DenotesSpine.argumentVariables {V : Type u} [Kernel.SetTheory V]
    (values : Kernel.Name → (Kernel.Name → Nat) → V) (env : Kernel.Env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V) (arguments : List V) :
    DenotesSpine values env levels (pushArguments ρ arguments)
      (argumentVariables arguments.length) arguments := by
  apply DenotesSpine.of_get (by simp [CompileCert.argumentVariables])
  intro index inside
  have bound : index < arguments.length := by simpa [CompileCert.argumentVariables] using inside
  simp only [CompileCert.argumentVariables, List.getElem_map, List.getElem_range]
  rw [← pushArguments_get arguments ρ index bound]
  exact .bvar

/-- No semantic argument is assumed to have a closed syntactic name.
For a closed installed type, fresh variables in an extended caller valuation
give the full typed application and its exact substituted residual. -/
theorem DenotedApplication.arbitrary_arguments {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V}
    {type result : Kernel.Expr} {arguments : List V}
    (typed : InstalledTelescope values env levels ρ type arguments finalρ result)
    (closed : type.looseBVarsBounded 0 = true) :
    ∃ residual, DenotedApplication values env levels (pushArguments ρ arguments)
      type (argumentVariables arguments.length) arguments residual := by
  have related : ValuationLift arguments.length 0 ρ (pushArguments ρ arguments) := by
    intro index
    simpa [Nat.add_comm] using pushArguments_above arguments ρ index
  obtain ⟨_, lifted⟩ := typed.lift related
  rw [Kernel.Expr.liftLooseBVars_eq_self closed] at lifted
  exact of_telescope lifted (DenotesSpine.argumentVariables values env levels ρ arguments)

open Kernel.SetTheory in
/-- The application result inhabits the exact substituted residual under
the original caller valuation, including for dependent later domains. -/
theorem DenotedApplication.apply {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V}
    {type residual : Kernel.Expr} {expressions : List Kernel.Expr} {arguments : List V}
    (application : DenotedApplication values env levels ρ type expressions arguments residual)
    {typeValue function : V} (typeRead : Kernel.Denotes values env levels ρ type typeValue)
    (member : function ∈ˢ typeValue) :
    ∃ residualValue, Kernel.Denotes values env levels ρ residual residualValue ∧
      arguments.foldl app function ∈ˢ residualValue := by
  induction application generalizing typeValue function with
  | nil => exact ⟨typeValue, typeRead, member⟩
  | cons domainRead argumentRead argumentTyped rest ih =>
    obtain ⟨next, bodyRead, nextMember⟩ :=
      installed_forall_elim typeRead member domainRead argumentTyped
    have substituted := denotes_instantiate1Lift bodyRead (depth := 0) rfl argumentRead
    exact ih substituted nextMember

open Kernel.SetTheory in
theorem denotes_mkAppN {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V}
    {function : Kernel.Expr} {value : V} {expressions : List Kernel.Expr} {arguments : List V}
    (head : Kernel.Denotes values env levels ρ function value)
    (spine : DenotesSpine values env levels ρ expressions arguments) :
    Kernel.Denotes values env levels ρ (Kernel.Expr.mkAppN function expressions)
      (arguments.foldl app value) := by
  induction spine generalizing function value with
  | nil => exact head
  | cons argument _ ih => exact ih (.app head argument)

/-- A constant at its own parameter instance denotes its value under the
unchanged level assignment, including the values of other universe names. -/
theorem denotes_self_instance {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V}
    {name : Kernel.Name} {constant : Kernel.ConstantInfo}
    (lookup : env.find? name = some constant) :
    Kernel.Denotes values env levels ρ
      (.const name (constant.toConstantVal.levelParams.map Kernel.Level.param)) (values name levels) := by
  have denoted := Kernel.Denotes.const (cval := values) (φ := levels) (ρ := ρ)
    (us := constant.toConstantVal.levelParams.map Kernel.Level.param) lookup (by simp)
  simpa only [Kernel.Level.substFn_param_self] using denoted

theorem denotes_mkAppN_head {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V}
    (arguments : List Kernel.Expr) {function : Kernel.Expr} {value : V}
    (read : Kernel.Denotes values env levels ρ (Kernel.Expr.mkAppN function arguments) value) :
    ∃ headValue, Kernel.Denotes values env levels ρ function headValue := by
  induction arguments generalizing function value with
  | nil => exact ⟨value, read⟩
  | cons argument rest ih =>
    obtain ⟨_, readHead⟩ := ih read
    cases readHead with
    | app head _ => exact ⟨_, head⟩

theorem InstalledTelescope.read {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V}
    {expression result : Kernel.Expr} {arguments : List V}
    (typed : InstalledTelescope values env levels ρ expression arguments finalρ result)
    {type : V} (denoted : Kernel.Denotes values env levels ρ expression type) :
    ∃ residual, Kernel.Denotes values env levels finalρ result residual := by
  induction typed generalizing type with
  | nil => exact ⟨type, denoted⟩
  | cons domainDenoted argumentTyped rest ih =>
    cases denoted with
    | pi hA hB hP =>
      obtain rfl := Kernel.Denotes_functional domainDenoted hA
      exact ih (hB _ argumentTyped)

theorem valuationLift_two {V : Type u} (ρ : Nat → V) (subject proposition : V) :
    ValuationLift 2 0 ρ (Kernel.push proposition (Kernel.push subject ρ)) := by
  intro index
  simp [Kernel.push]

theorem denotes_forall_domain {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V}
    {domain body : Kernel.Expr} {binder : Kernel.BinderMeta} {type : V}
    (read : Kernel.Denotes values env levels ρ (.forallE domain body binder) type) :
    ∃ value, Kernel.Denotes values env levels ρ domain value := by
  cases read with
  | pi domainRead _ _ => exact ⟨_, domainRead⟩

open Kernel.SetTheory in
theorem denotes_church_continuation {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V}
    {continuation : Kernel.Expr} {outer inner : Kernel.BinderMeta} {type proposition : V}
    (read : Kernel.Denotes values env levels ρ
      (.forallE (.sort .zero) (.forallE continuation (.bvar 1) inner) outer) type)
    (typed : proposition ∈ˢ univ 0) :
    ∃ continuationType, Kernel.Denotes values env levels (Kernel.push proposition ρ)
      continuation continuationType := by
  cases read with
  | pi sortRead bodyRead _ =>
    cases sortRead
    exact denotes_forall_domain (bodyRead proposition typed)

end Ix.CompileCert
