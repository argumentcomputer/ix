import Ix.CompileCert.Installed
import Ix.CompileCert.SourceExportFast

/-! # Source installation

Installation of the original source through the independent fold
(`installSource`, `SourceInstallation`) and of generated source models
(`proposeSourceModels`, `installSourceModels`, `SourceModelInstallation`)
with their basis support.
-/

namespace Ix.CompileCert

open Kernel.Reader
open Kernel.Admission

/-- Every original source entry is compared against the full declaration
entries actually submitted to the independent source checker. Exact equality
retains bodies, hints, constructor arities and ordered recursor rules. -/
def SourceEntryMatches (ci : Lean.ConstantInfo) (declarations : Array Kernel.Declaration) : Prop :=
  match exportSourceEntry ci with
  | .error _ => False
  | .ok expected => expected ∈ streamEntries declarations

instance (ci : Lean.ConstantInfo) (declarations : Array Kernel.Declaration) :
    Decidable (SourceEntryMatches ci declarations) :=
  match h : exportSourceEntry ci with
  | .error _ => by simp only [SourceEntryMatches, h]; infer_instance
  | .ok _ => by simp only [SourceEntryMatches, h]; infer_instance

def SourceEntryCorrespondence (source : Source) (declarations : Array Kernel.Declaration) : Prop :=
  ∀ ci ∈ source.declarations, SourceEntryMatches ci declarations

instance (source : Source) (declarations : Array Kernel.Declaration) :
    Decidable (SourceEntryCorrespondence source declarations) :=
  inferInstanceAs (Decidable (∀ ci ∈ source.declarations, SourceEntryMatches ci declarations))

/-- An independent source installation attempt has no target map, reader,
bytes, hint oracle or target normalization state. Empty accelerator pins
request ordinary verified checking of the actual source definitions. -/
structure SourceInstallation (source : Source) (roots : List Lean.Name) where
  complete : CompleteSource source roots
  declarations : Array Kernel.Declaration
  exported : exportSourceDeclarations source = .ok declarations
  members : SourceEntryCorrespondence source declarations
  env : Kernel.Env
  checked : Kernel.Cached.checkDecls .verified [] declarations = .ok env

inductive SourceInstallError where
  | incomplete
  | exportFailure (reason : String)
  | correspondence
  | checking (error : Kernel.CheckError) (position : Nat)

/-- Success is evidence of this run, not a definition of the intended Dom.
Establishing success over that domain and the source/target annotation
simulation remain separate obligations. -/
def installSource (source : Source) (roots : List Lean.Name) :
    Except SourceInstallError (SourceInstallation source roots) :=
  if hc : CompleteSource source roots then
    match he : exportSourceDeclarations source with
    | .error reason => .error (.exportFailure reason)
    | .ok declarations =>
      if hm : SourceEntryCorrespondence source declarations then
        match hk : Kernel.Cached.checkDecls .verified [] declarations with
        | .error (error, position) => .error (.checking error position)
        | .ok env => .ok ⟨hc, declarations, he, hm, env, hk⟩
      else .error .correspondence
  else .error .incomplete

theorem SourceInstallation.has_model (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceInstallation source roots) :
    Nonempty (Kernel.Model V installed.env) :=
  Kernel.model_exists V [] installed.declarations installed.env installed.checked

/-- The source witness retains the checker's actual installed skeletons;
it does not identify raw binder annotations with installed annotations. -/
theorem SourceInstallation.skels {source : Source} {roots : List Lean.Name}
    (installed : SourceInstallation source roots) :
    Kernel.Cached.envSkels installed.env =
      Kernel.Cached.streamSkels installed.declarations.toList :=
  Kernel.Cached.checkDecls_skels installed.checked

theorem SourceInstallation.groups {source : Source} {roots : List Lean.Name}
    (installed : SourceInstallation source roots) :
    ∃ groups, exportSourceGroups source = .ok groups ∧ SourceGroupsCover source groups ∧
      orderSourceGroups (groups.length + 1) groups [] [] = .ok installed.declarations.toList :=
  exportSourceDeclarations_groups installed.exported

/-- The checked stream is a permutation of the independently exported
complete declaration groups: scheduling cannot discard or alter a body,
type, constructor, recursor rule, or any other declaration field. -/
theorem SourceInstallation.declarations_perm {source : Source} {roots : List Lean.Name}
    (installed : SourceInstallation source roots) :
    ∃ groups, SourceGroupsCover source groups ∧
      installed.declarations.toList.Perm (groups.map SourceDeclGroup.declaration) := by
  obtain ⟨groups, _, covered, ordered⟩ := installed.groups
  exact ⟨groups, covered, by simpa using orderSourceGroups_perm ordered⟩

/-- Each original source member has an exact entry in an actual declaration
of the accepted source fold. This retains full fields, not just membership
of an installation skeleton. Annotation pull-back remains a separate proof. -/
theorem SourceInstallation.member {source : Source} {roots : List Lean.Name}
    (installed : SourceInstallation source roots) {ci : Lean.ConstantInfo}
    (present : ci ∈ source.declarations) :
    ∃ entry declaration, exportSourceEntry ci = .ok entry ∧
      declaration ∈ installed.declarations.toList ∧ entry ∈ readerEntries declaration ∧
      Kernel.Cached.checkDecls .verified [] installed.declarations = .ok installed.env := by
  have matched := installed.members ci present
  cases he : exportSourceEntry ci with
  | error reason => simp [SourceEntryMatches, he] at matched
  | ok entry =>
    have hm : entry ∈ installed.declarations.toList.flatMap readerEntries := by
      simpa only [SourceEntryMatches, he, streamEntries] using matched
    obtain ⟨declaration, hd, hm⟩ := List.mem_flatMap.mp hm
    exact ⟨entry, declaration, rfl, hd, hm, installed.checked⟩

/-- For declarations with the existing kernel's singleton install receipt,
the source-entry provenance reaches an actual environment constant. Block
members still use the full-stream skeleton theorem; this statement does not
invent a singleton receipt for inductive or quotient declarations. -/
theorem SourceInstallation.member_installed {source : Source} {roots : List Lean.Name}
    (installed : SourceInstallation source roots) {ci : Lean.ConstantInfo}
    (present : ci ∈ source.declarations) :
    ∃ entry declaration, exportSourceEntry ci = .ok entry ∧
      declaration ∈ installed.declarations.toList ∧ entry ∈ readerEntries declaration ∧
      ∀ skeleton, Kernel.Cached.declSkel declaration = some skeleton →
        ∃ actual ∈ installed.env.consts, Kernel.Cached.ciSkel actual = skeleton := by
  obtain ⟨entry, declaration, exported, presentDecl, entryMem, checked⟩ := installed.member present
  exact ⟨entry, declaration, exported, presentDecl, entryMem,
    fun _ hs => Kernel.Cached.checkDecls_installs checked (by simpa using presentDecl) hs⟩

/-- Source-only proposal context. It starts empty and is populated solely
from original source declarations and this bundle's proposed model records. -/
structure SourceModelState where
  types : Std.HashMap Kernel.Name (List Kernel.Name × Kernel.Expr) := {}
  heights : Std.HashMap Kernel.Name Nat := {}
  blocks : Std.HashMap Kernel.Name Kernel.Frontend.InModel.BlockRec := {}

def SourceModelState.note (state : SourceModelState) (declaration : Kernel.Declaration) :
    SourceModelState :=
  let values : List (Kernel.ConstantVal × Option Nat) := match declaration with
    | .axiomDecl cv | .thmDecl cv _ | .opaqueDecl cv _ | .quotDecl _ cv => [(cv, none)]
    | .defnDecl cv _ hint => [(cv, some (Kernel.Frontend.InModel.hintHeight hint))]
    | .indDecl block _ => block.map (fun ci => (ci.toConstantVal, none))
    | .basisDecl kind => kind.decls.map (fun ci => (ci.toConstantVal, none))
  values.foldl (fun state (cv, height) =>
    let heights := match height with
      | none => state.heights
      | some h => state.heights.insert cv.name h
    { state with types := state.types.insert cv.name (cv.levelParams, cv.type), heights }) state

structure SourceModelProposal (source : Source) where
  declarations : Array Kernel.Declaration
  blocks : List (SourceBlockEvidence source)
  basisSupport : List Kernel.BasisKind

/-- Fixed source-model support identities, defined by the kernel's own raw
Eq/PUnit basis (Basis/Eq.lean and Basis/PUnit.lean). Both are finite closed
blocks. They are submitted as explicit declarations, never imported from
target pin bytes or used to overwrite a source-owned declaration. -/
def sourceModelBasisSupport : List (Kernel.Name × Kernel.BasisKind) :=
  [(Kernel.eqName, .eqK), (Kernel.punitName, .punitK)]

/-- Fixed source-owned ground required by the public semantic interface even
when the selected original cone does not mention False or Eq. Unlike modeller
dependencies, these can be appended after the original stream. A present
source identity is never replaced; all records still pass the same fold. -/
def sourceSemanticBasisSupport : List (Kernel.Name × Kernel.BasisKind) :=
  [(Kernel.falseName, .falseK), (Kernel.eqName, .eqK)]

/-- Reference closure of the finite raw basis terms. Literals and non-basis
record forms are refused here, so no implicit literal dependency is hidden. -/
def sourceSupportExprClosed (names : List Kernel.Name) : Kernel.Expr → Bool
  | .bvar _ | .sort _ => true
  | .const name _ => names.contains name
  | .fvar _ type => sourceSupportExprClosed names type
  | .app f a => sourceSupportExprClosed names f && sourceSupportExprClosed names a
  | .lam type body _ | .forallE type body _ =>
    sourceSupportExprClosed names type && sourceSupportExprClosed names body
  | .letE type value body => sourceSupportExprClosed names type &&
    sourceSupportExprClosed names value && sourceSupportExprClosed names body
  | .proj owner _ value => names.contains owner && sourceSupportExprClosed names value
  | .lit _ => false

def sourceBasisSupportClosed (kind : Kernel.BasisKind) : Bool :=
  let records := kind.decls
  let names := records.map Kernel.ConstantInfo.name
  records.all fun
    | .indInfo cv _ | .ctorInfo cv _ _ => sourceSupportExprClosed names cv.type
    | .recInfo cv _ _ rules => sourceSupportExprClosed names cv.type &&
        rules.all (fun rule => names.contains rule.ctor && sourceSupportExprClosed names rule.rhs)
    | _ => false

theorem sourceModelBasisSupport_closed :
    ∀ row ∈ sourceModelBasisSupport, sourceBasisSupportClosed row.2 = true := by decide

theorem sourceSemanticBasisSupport_closed :
    ∀ row ∈ sourceSemanticBasisSupport, sourceBasisSupportClosed row.2 = true := by decide

/-- Untrusted coverage proposal. The existing modeller has partial helpers;
this use does not prove termination or correspondence. Original declarations
are appended unchanged; independent checks below validate preservation and
submit every proposed record to the verified fold. No projection rewriting
or target data participates. -/
def proposeSourceModels (source : Source) (original : Array Kernel.Declaration) :
    ExportM (SourceModelProposal source) := do
  let groups ← exportSourceGroups source
  let mut state : SourceModelState := {}
  let mut declarations := #[]
  let mut evidence := []
  let mut basisSupport := []
  for declaration in original do
    if let .indDecl _ _ := declaration then
      let some group := groups.find? (fun group => decide (group.declaration = declaration))
        | throw "source model preparation could not associate an original group"
      let some owner := group.members.head? | throw "source model group has no owner"
      let block ← exportSourceBlockEvidence source owner
      unless decide (block.group.declaration = declaration) do
        throw "source model block evidence differs from the original declaration"
      evidence := evidence ++ [block]
      for type in block.shape.types do
        state := { state with blocks := state.blocks.insert type.cv.name block.shape }
      if Kernel.Frontend.InModel.wants block.shape then
        for (name, kind) in sourceModelBasisSupport do
          if (state.types[name]?).isNone then
            if original.any (fun d => d.names.contains name) then
              throw s!"source-owned support {repr name} is scheduled after a model that requires it"
            let support := Kernel.Declaration.basisDecl kind
            declarations := declarations.push support
            basisSupport := basisSupport ++ [kind]
            state := state.note support
        let context : Kernel.Frontend.InModel.Ctx :=
          ⟨fun n => state.types[n]?, fun n => state.heights.getD n 0, fun n => state.blocks[n]?⟩
        let proposed ← Kernel.Frontend.InModel.generate context block.shape
        for auxiliary in proposed do
          declarations := declarations.push auxiliary
          state := state.note auxiliary
    declarations := declarations.push declaration
    state := state.note declaration
  return ⟨declarations, evidence, basisSupport⟩

structure SourceModelInstallation (source : Source) (roots : List Lean.Name) where
  complete : CompleteSource source roots
  original : Array Kernel.Declaration
  exported : exportSourceDeclarations source = .ok original
  proposal : SourceModelProposal source
  proposed : proposeSourceModels source original = .ok proposal
  original_preserved : original.toList.Sublist proposal.declarations.toList
  members : SourceEntryCorrespondence source proposal.declarations
  support_checked : ∀ kind ∈ proposal.basisSupport,
    Kernel.Declaration.basisDecl kind ∈ proposal.declarations.toList ∧
      sourceBasisSupportClosed kind = true
  env : Kernel.Env
  checked : Kernel.Cached.checkDecls .verified [] proposal.declarations = .ok env

inductive SourceModelError where
  | incomplete
  | exportFailure (reason : String)
  | proposalFailure (reason : String)
  | changedOriginal
  | correspondence
  | supportMismatch
  | checking (error : Kernel.CheckError) (position : Nat)

def installSourceModels (source : Source) (roots : List Lean.Name) :
    Except SourceModelError (SourceModelInstallation source roots) :=
  if hc : CompleteSource source roots then
    match he : exportSourceDeclarations source with
    | .error reason => .error (.exportFailure reason)
    | .ok original =>
      match hp : proposeSourceModels source original with
      | .error reason => .error (.proposalFailure reason)
      | .ok proposal =>
        if hs : original.toList.Sublist proposal.declarations.toList then
          if hm : SourceEntryCorrespondence source proposal.declarations then
            if hb : ∀ kind ∈ proposal.basisSupport,
                Kernel.Declaration.basisDecl kind ∈ proposal.declarations.toList ∧
                  sourceBasisSupportClosed kind = true then
              match hk : Kernel.Cached.checkDecls .verified [] proposal.declarations with
              | .error (error, position) => .error (.checking error position)
              | .ok env => .ok ⟨hc, original, he, proposal, hp, hs, hm, hb, env, hk⟩
            else .error .supportMismatch
          else .error .correspondence
        else .error .changedOriginal
  else .error .incomplete

theorem SourceModelInstallation.has_model (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceModelInstallation source roots) :
    Nonempty (Kernel.Model V installed.env) :=
  Kernel.model_exists V [] installed.proposal.declarations installed.env installed.checked

/-- This is about actual installed definitions, including checked auxiliary
models. Pulling it back to original source expressions remains strong S. -/
theorem SourceModelInstallation.has_model_values (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceModelInstallation source roots) :
    ∃ model : Kernel.Model V installed.env, ∀ header value hint,
      Kernel.ConstantInfo.defnInfo header value hint ∈ installed.env.consts →
        ∀ φ ρ, Kernel.Denotes model.cval installed.env φ ρ value (model.cval header.name φ) :=
  Kernel.Cached.checkDecls_model_defn_values V [] installed.proposal.declarations
    installed.env installed.checked

theorem SourceModelInstallation.member {source : Source} {roots : List Lean.Name}
    (installed : SourceModelInstallation source roots) {ci : Lean.ConstantInfo}
    (present : ci ∈ source.declarations) :
    ∃ entry declaration, exportSourceEntry ci = .ok entry ∧
      declaration ∈ installed.proposal.declarations.toList ∧ entry ∈ readerEntries declaration ∧
      Kernel.Cached.checkDecls .verified [] installed.proposal.declarations = .ok installed.env := by
  have matched := installed.members ci present
  cases he : exportSourceEntry ci with
  | error reason => simp [SourceEntryMatches, he] at matched
  | ok entry =>
    have hm : entry ∈ installed.proposal.declarations.toList.flatMap readerEntries := by
      simpa only [SourceEntryMatches, he, streamEntries] using matched
    obtain ⟨declaration, hd, hm⟩ := List.mem_flatMap.mp hm
    exact ⟨entry, declaration, rfl, hd, hm, installed.checked⟩

theorem SourceModelInstallation.original_decl {source : Source} {roots : List Lean.Name}
    (installed : SourceModelInstallation source roots) {declaration : Kernel.Declaration}
    (present : declaration ∈ installed.original.toList) :
    declaration ∈ installed.proposal.declarations.toList :=
  installed.original_preserved.subset present

end Ix.CompileCert
