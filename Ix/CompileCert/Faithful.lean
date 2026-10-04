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

/-- A source declaration agrees with an actual reader entry, including its
kind, complete type/value, universe telescope and every recursor-rule field.
This strict first mode intentionally has no auxiliary/hint exemption. -/
def DirectMatch (cx : ExportContext) (entries : List DirectEntry)
    (ci : Lean.ConstantInfo) : Prop :=
  match directExport cx ci with
  | .error _ => False
  | .ok e => e ∈ entries

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
    ∃ e ∈ streamEntries decls, directExport cx ci = .ok e := by
  have hm := h ci hc
  cases he : directExport cx ci with
  | error e => simp [DirectMatch, he] at hm
  | ok e => exact ⟨e, by simpa [DirectMatch, he] using hm, rfl⟩

end Ix.CompileCert
