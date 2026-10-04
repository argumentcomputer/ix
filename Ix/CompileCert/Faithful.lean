import Ix.CompileCert.Translate

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

end Ix.CompileCert
