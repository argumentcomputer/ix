import Ix.CompileCert.Domain
import Ix.Kernel.Admission.Theorems

/-! # Admission-connected direct-cone certification

The executable reads and admits the exact bytes before comparing an
independent source export against the reader stream. Its result carries
proofs of the checks actually performed. No producer-supplied proposition,
Boolean verdict, or `Named.original` field is accepted as correspondence.

This is a conservative foundation of C1, not completed W. Singleton definitions
may use the proved raw reader-normalization relation; its semantic pull-back
and complete source/export refinement remain separate obligations.
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

/-- A checked equation proposal uses the original constructor telescope.
Every argument is symbolic. In particular the selected field's type is
lifted from its original prefix into the complete constructor telescope.
The universe is only a proposal: the independent fold checks this theorem. -/
def sourceProjectionEquation {source : Source} (site : SourceProjectionSite source)
    (projection : Kernel.ConstantVal) (level : Kernel.Level) : ExportM Kernel.Declaration := do
  let .ctor constructor _ _ ← exportSourceEntry (.ctorInfo site.ctor)
    | throw "source projection equation has no original constructor export"
  unless decide (constructor.levelParams = projection.levelParams) do
    throw "source projection and constructor universe telescopes differ"
  let (binders, _) := Kernel.Frontend.stripPisAll constructor.type
  let count := site.owner.numParams + site.ctor.numFields
  unless binders.length == count do
    throw "source constructor telescope disagrees with original field counts"
  let some (fieldType, _) := binders[site.owner.numParams + site.field]?
    | throw "source projection equation field is absent"
  let arguments := (List.range count).map (fun i => Kernel.Expr.bvar (count - 1 - i))
  let parameters := arguments.take site.owner.numParams
  let levels := projection.levelParams.map Kernel.Level.param
  let constructorValue := Kernel.Expr.mkAppN (.const constructor.name levels) arguments
  let lhs := Kernel.Expr.mkAppN (.const projection.name levels) (parameters ++ [constructorValue])
  let rhs := Kernel.Expr.bvar (site.ctor.numFields - 1 - site.field)
  let type := fieldType.liftLooseBVars (site.ctor.numFields - site.field) 0
  let equation := Kernel.Expr.mkAppN (.const Kernel.eqName [level]) [type, lhs, rhs]
  let proof := Kernel.Expr.mkAppN (.const Kernel.eqReflName [level]) [type, rhs]
  let header : Kernel.ConstantVal :=
    ⟨projection.name.str "_source_constructor_equation", projection.levelParams,
      binders.foldr (fun (type, binder) body => .forallE type body binder) equation⟩
  return .thmDecl header (Kernel.Frontend.mkLams binders proof)

/-- Source-owned lowering proposal. Original source syntax, constructor and
recursor metadata are authoritative. The generated source model supplies
only a proposed field universe. Neither target data nor reader projRewrite
is consulted. Acceptance below must check both the replacement and its
universal constructor equation; generation itself proves no semantics. -/
def proposeSourceProjection (source : Source) (state : SourceModelState)
    (declaration : Kernel.Declaration) : ExportM (Option (Kernel.Declaration × Kernel.Declaration)) := do
  let .defnDecl header body hint := declaration | return none
  let some ci := source.declarations.find? (fun ci => decide (sourceName ci.name = header.name))
    | return none
  let .defnInfo definition := ci | return none
  let some (owner, field, binders) := sourceProjectionBody definition.value | return none
  let site ← sourceProjectionSite source owner field
  unless binders == site.owner.numParams + 1 do
    throw "source projection binder count differs from original owner parameters"
  let original ← exportSourceEntry ci
  unless decide (original = .defn header body hint) do
    throw "source projection declaration differs from its immutable original export"
  let T := sourceName owner
  let some (_, iotaType) := state.types[Kernel.Frontend.projIotaName T field]?
    | return none
  let some level := Kernel.Frontend.projIotaLevel iotaType
    | throw "source-generated projection equation has no field universe"
  let some (.recInfo recursor) := source.find (owner.str "rec")
    | throw "source projection owner has no original recursor"
  unless recursor.numParams == site.owner.numParams && recursor.numIndices == 0 do
    throw "source projection recursor parameters or indices differ from original owner"
  let .recursor recHeader _ _ _ ← exportSourceEntry (.recInfo recursor)
    | throw "source projection recursor export has the wrong kind"
  let ownerRecipe : Kernel.Frontend.ProjRecOwner := {
    T, lps := site.owner.levelParams.map sourceName, nP := site.owner.numParams,
    ctor := sourceName site.ctorName, nF := site.ctor.numFields,
    recName := recHeader.name, recLps := recHeader.levelParams, recType := recHeader.type,
    numMotives := recursor.numMotives, numMinors := recursor.numMinors }
  let some lowered := Kernel.Frontend.projRecValue ownerRecipe level header.type body field
    | throw "source projection recursor proposal cannot represent the original projection"
  let equation ← sourceProjectionEquation site header level
  return some (.defnDecl header lowered hint, equation)

/-- Independent correspondence check for a proposed source projection.
The replacement may be generated by any algorithm: this receipt binds its
full header and hint to the exact original export and its checked equation
to the exact original constructor/field. It makes no extensional claim. -/
structure SourceProjectionReceipt (source : Source)
    (original replacement equation : Kernel.Declaration) where
  definition : Lean.DefinitionVal
  original_lookup : source.find definition.name = some (.defnInfo definition)
  header : Kernel.ConstantVal
  body : Kernel.Expr
  hint : Kernel.ReducibilityHint
  exported : exportSourceEntry (.defnInfo definition) = .ok (.defn header body hint)
  original_decl : original = .defnDecl header body hint
  ownerName : Lean.Name
  field : Nat
  site : SourceProjectionSite source
  site_checked : sourceProjectionSite source ownerName field = .ok site
  raw_shape : sourceProjectionBody definition.value =
    some (ownerName, field, site.owner.numParams + 1)
  value : Kernel.Expr
  replacement_decl : replacement = .defnDecl header value hint
  level : Kernel.Level
  equation_image : sourceProjectionEquation site header level = .ok equation

def checkSourceProjectionReceipt (source : Source)
    (original replacement equation : Kernel.Declaration) :
    ExportM (SourceProjectionReceipt source original replacement equation) := do
  let .defnDecl originalHeader _ _ := original
    | throw "source projection receipt original is not a definition"
  let some ci := source.declarations.find?
      (fun ci => decide (sourceName ci.name = originalHeader.name))
    | throw "source projection receipt original definition is absent"
  match ho : source.find ci.name with
  | some (.defnInfo definition) =>
    if hn : definition.name = ci.name then
      have originalLookup : source.find definition.name = some (.defnInfo definition) := by
        simpa only [hn] using ho
      match he : exportSourceEntry (.defnInfo definition) with
      | .ok (.defn header body hint) =>
        if hd : original = .defnDecl header body hint then
          let some (owner, field, _) := sourceProjectionBody definition.value
            | throw "source projection receipt original body is not a projection"
          match hm : sourceProjectionSite source owner field with
          | .error why => throw why
          | .ok site =>
            if hs : sourceProjectionBody definition.value =
                some (owner, field, site.owner.numParams + 1) then
              let .defnDecl _ value _ := replacement
                | throw "source projection replacement is not a definition"
              if hr : replacement = .defnDecl header value hint then
                let .thmDecl equationHeader _ := equation
                  | throw "source projection equation is not a theorem"
                let some level := Kernel.Frontend.projIotaLevel equationHeader.type
                  | throw "source projection equation is not a universally quantified equality"
                match hq : sourceProjectionEquation site header level with
                | .error why => throw why
                | .ok expected =>
                  if hsame : expected = equation then
                    return ⟨definition, originalLookup, header, body, hint, he, hd,
                      owner, field, site, hm, hs, value, hr, level,
                      by simpa only [hsame] using hq⟩
                  else throw "source projection equation differs from the original constructor field equation"
              else throw "source projection replacement changed the original header or hint"
            else throw "source projection receipt shape disagrees with original owner metadata"
        else throw "source projection receipt original differs from its exact source export"
      | _ => throw "source projection receipt source definition could not be exported"
    else throw "source projection receipt original identity is inconsistent"
  | _ => throw "source projection receipt does not identify the exact original definition"

theorem SourceProjectionReceipt.constructor_computes {source : Source} {original replacement equation}
    (receipt : SourceProjectionReceipt source original replacement equation)
    (levels : List Lean.Level) (params fields : List Lean.Expr)
    (parameterCount : params.length = receipt.site.owner.numParams)
    (fieldCount : fields.length = receipt.site.ctor.numFields) {value : Lean.Expr}
    (selected : fields[receipt.site.field]? = some value) :
    sourceProjectionCompute source (.proj receipt.ownerName receipt.field
      (sourceApps (.const receipt.site.ctorName levels) (params ++ fields))) = .ok value :=
  sourceProjectionCompute_constructor receipt.site_checked levels params fields
    parameterCount fieldCount selected

theorem SourceProjectionReceipt.original_fields {source : Source} {original replacement equation}
    (receipt : SourceProjectionReceipt source original replacement equation) :
    SourceValImage receipt.definition.toConstantVal receipt.header ∧
      exportSourceExpr receipt.definition.levelParams receipt.definition.value = .ok receipt.body ∧
      receipt.hint = exportHint receipt.definition.hints :=
  exportSourceEntry_defn receipt.exported

/-- A structural receipt, deliberately distinct from Sublist preservation.
Each changed declaration is exactly the source-owned proposal and its
constructor equation occurs immediately afterwards in the checked stream.
This relation records normalization, not semantic equality by definition. -/
inductive SourceProjectionNormalization (source : Source) :
    SourceModelState → List Kernel.Declaration → List Kernel.Declaration → Prop
  | nil (state) : SourceProjectionNormalization source state [] []
  | unchanged {state original rest output}
      (proposal : proposeSourceProjection source state original = .ok none)
      (tail : SourceProjectionNormalization source (state.note original) rest output) :
      SourceProjectionNormalization source state (original :: rest) (original :: output)
  | lowered {state original rest replacement equation output}
      (proposal : proposeSourceProjection source state original = .ok (some (replacement, equation)))
      (association : SourceProjectionReceipt source original replacement equation)
      (fresh : ∀ name ∈ equation.names, state.types[name]? = none ∧
        ∀ declaration ∈ original :: rest, name ∉ declaration.names)
      (tail : SourceProjectionNormalization source
        ((state.note replacement).note equation) rest output) :
      SourceProjectionNormalization source state (original :: rest)
        (replacement :: equation :: output)

def normalizeSourceProjections (source : Source) (state : SourceModelState)
    (input : List Kernel.Declaration) :
    ExportM { output : List Kernel.Declaration // SourceProjectionNormalization source state input output } :=
  match input with
  | [] => .ok ⟨[], .nil state⟩
  | original :: rest =>
    match hp : proposeSourceProjection source state original with
    | .error why => .error why
    | .ok none => do
      let output ← normalizeSourceProjections source (state.note original) rest
      return ⟨original :: output.val, .unchanged hp output.property⟩
    | .ok (some (replacement, equation)) =>
      if hf : ∀ name ∈ equation.names, state.types[name]? = none ∧
          ∀ declaration ∈ original :: rest, name ∉ declaration.names then do
        let association ← checkSourceProjectionReceipt source original replacement equation
        let output ← normalizeSourceProjections source
          ((state.note replacement).note equation) rest
        return ⟨replacement :: equation :: output.val, .lowered hp association hf output.property⟩
      else .error "source projection equation name conflicts with an existing declaration"

structure SourceNormalizedInstallation (source : Source) (roots : List Lean.Name) where
  complete : CompleteSource source roots
  original : Array Kernel.Declaration
  exported : exportSourceDeclarations source = .ok original
  modelProposal : SourceModelProposal source
  proposed : proposeSourceModels source original = .ok modelProposal
  original_preserved : original.toList.Sublist modelProposal.declarations.toList
  original_members : SourceEntryCorrespondence source modelProposal.declarations
  support_checked : ∀ kind ∈ modelProposal.basisSupport,
    Kernel.Declaration.basisDecl kind ∈ modelProposal.declarations.toList ∧
      sourceBasisSupportClosed kind = true
  declarations : List Kernel.Declaration
  normalization : SourceProjectionNormalization source {} modelProposal.declarations.toList declarations
  env : Kernel.Env
  checked : Kernel.Cached.checkDecls .verified [] declarations.toArray = .ok env

def installSourceNormalized (source : Source) (roots : List Lean.Name) :
    Except SourceModelError (SourceNormalizedInstallation source roots) :=
  if hc : CompleteSource source roots then
    match he : exportSourceDeclarations source with
    | .error why => .error (.exportFailure why)
    | .ok original =>
      match hp : proposeSourceModels source original with
      | .error why => .error (.proposalFailure why)
      | .ok proposal =>
        if hs : original.toList.Sublist proposal.declarations.toList then
          if hm : SourceEntryCorrespondence source proposal.declarations then
            if hb : ∀ kind ∈ proposal.basisSupport,
                Kernel.Declaration.basisDecl kind ∈ proposal.declarations.toList ∧
                  sourceBasisSupportClosed kind = true then
              match normalizeSourceProjections source {} proposal.declarations.toList with
              | .error why => .error (.proposalFailure why)
              | .ok output =>
                match hk : Kernel.Cached.checkDecls .verified [] output.val.toArray with
                | .error (error, position) => .error (.checking error position)
                | .ok env => .ok ⟨hc, original, he, proposal, hp, hs, hm, hb,
                    output.val, output.property, env, hk⟩
            else .error .supportMismatch
          else .error .correspondence
        else .error .changedOriginal
  else .error .incomplete

theorem SourceNormalizedInstallation.has_model (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceNormalizedInstallation source roots) :
    Nonempty (Kernel.Model V installed.env) :=
  Kernel.model_exists V [] installed.declarations.toArray installed.env installed.checked

/-- Value denotation for the actually installed normalized definitions.
Original-source value correspondence is a separate semantic pull-back. -/
theorem SourceNormalizedInstallation.has_model_values (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceNormalizedInstallation source roots) :
    ∃ model : Kernel.Model V installed.env, ∀ header value hint,
      Kernel.ConstantInfo.defnInfo header value hint ∈ installed.env.consts →
        ∀ φ ρ, Kernel.Denotes model.cval installed.env φ ρ value (model.cval header.name φ) :=
  Kernel.Cached.checkDecls_model_defn_values V [] installed.declarations.toArray
    installed.env installed.checked

theorem SourceProjectionNormalization.member {source : Source} {state input output}
    (receipt : SourceProjectionNormalization source state input output)
    {declaration : Kernel.Declaration} (present : declaration ∈ input) :
    declaration ∈ output ∨ ∃ prior replacement equation,
      proposeSourceProjection source prior declaration = .ok (some (replacement, equation)) ∧
      Nonempty (SourceProjectionReceipt source declaration replacement equation) ∧
      replacement ∈ output ∧ equation ∈ output := by
  induction receipt with
  | nil => simp at present
  | @unchanged state original rest output hp tail ih =>
    rcases List.mem_cons.mp present with rfl | present
    · exact .inl (by simp)
    · rcases ih present with same | ⟨prior, replacement, equation, hp, association, hr, he⟩
      · exact .inl (List.mem_cons_of_mem _ same)
      · exact .inr ⟨prior, replacement, equation, hp, association,
          List.mem_cons_of_mem _ hr, List.mem_cons_of_mem _ he⟩
  | @lowered state original rest replacement equation output hp association fresh tail ih =>
    rcases List.mem_cons.mp present with rfl | present
    · exact .inr ⟨state, replacement, equation, hp, ⟨association⟩, by simp, by simp⟩
    · rcases ih present with same | ⟨prior, next, law, hp, association, hr, he⟩
      · exact .inl (by simp only [List.mem_cons]; exact .inr (.inr same))
      · exact .inr ⟨prior, next, law, hp, association, by simp only [List.mem_cons]; exact .inr (.inr hr),
          by simp only [List.mem_cons]; exact .inr (.inr he)⟩

/-- Every original source entry is retained with its exact raw export,
then associated with either an unchanged checked declaration or the exact
source-owned replacement and checked equation. This does not substitute
the replacement for the original source expression in a semantic theorem. -/
theorem SourceNormalizedInstallation.member {source : Source} {roots : List Lean.Name}
    (installed : SourceNormalizedInstallation source roots) {ci : Lean.ConstantInfo}
    (present : ci ∈ source.declarations) :
    ∃ entry declaration, exportSourceEntry ci = .ok entry ∧ entry ∈ readerEntries declaration ∧
      (declaration ∈ installed.declarations ∨ ∃ prior replacement equation,
        proposeSourceProjection source prior declaration = .ok (some (replacement, equation)) ∧
        Nonempty (SourceProjectionReceipt source declaration replacement equation) ∧
        replacement ∈ installed.declarations ∧ equation ∈ installed.declarations) := by
  have matched := installed.original_members ci present
  cases he : exportSourceEntry ci with
  | error reason => simp [SourceEntryMatches, he] at matched
  | ok entry =>
    have hm : entry ∈ installed.modelProposal.declarations.toList.flatMap readerEntries := by
      simpa only [SourceEntryMatches, he, streamEntries] using matched
    obtain ⟨declaration, hd, hm⟩ := List.mem_flatMap.mp hm
    exact ⟨entry, declaration, rfl, hm, installed.normalization.member hd⟩

structure ArtifactInput where
  limits : Limits
  records : Records
  blobs : Kernel.Ingress.Blobs
  hint : Kernel.ConstRef Address → Option Kernel.ReducibilityHint := fun _ => none

structure Input extends ArtifactInput where
  source : Source
  roots : List Lean.Name
  map : SourceMap

/-- Validate host-supplied key widths before admission's hash-table lookups.
This does not assert that a key hashes its payload; admission treats keys as
opaque identities. Wire-embedded references are checked by the decoder. -/
def ArtifactKeysValid (input : ArtifactInput) : Prop :=
  (∀ row ∈ input.records, row.1.hash.size = 32) ∧
  (∀ row ∈ input.blobs, row.1.hash.size = 32)

instance (input : ArtifactInput) : Decidable (ArtifactKeysValid input) :=
  inferInstanceAs (Decidable (
    (∀ row ∈ input.records, row.1.hash.size = 32) ∧
    (∀ row ∈ input.blobs, row.1.hash.size = 32)))

/-- Resolve actual record references and names, rather than comparing a
producer's display label or allowing a fabricated member address. -/
def NameAgrees (cx : ExportContext) (n : Lean.Name) (target : Kernel.Name) : Prop :=
  match cx.name n with
  | .error _ => False
  | .ok actual => actual = target

instance (cx : ExportContext) (n : Lean.Name) (target : Kernel.Name) :
    Decidable (NameAgrees cx n target) :=
  match h : cx.name n with
  | .error _ => by simp only [NameAgrees, h]; infer_instance
  | .ok _ => by simp only [NameAgrees, h]; infer_instance

/-- Recursor K/safety flags are not retained in the reader's installed-rule
placeholder. Check them against the actual source-associated wire member. -/
def sourceRecordFlags (cx : ExportContext) (reader : Ctx) (e : MapEntry) : Bool :=
  match cx.source.find e.source with
  | some (.recInfo rv) =>
    match e.target with
    | .ctor .. => false
    | .member owner index =>
      match reader.store owner with
      | none => false
      | some record =>
        match (recursorMembers record).find? (fun entry => entry.1 == index) with
        | none => false
        | some (_, r) => r.k == rv.k && r.isUnsafe == rv.isUnsafe &&
            r.lvls.toNat == rv.levelParams.length
  | some _ => true
  | none => false

def MapAgrees (cx : ExportContext) (reader : Ctx) : Prop :=
  ∀ e ∈ cx.map,
    resolve reader.store e.record = some e.target ∧
    NameAgrees cx e.source (reader.nameOf e.target) ∧ sourceRecordFlags cx reader e = true

instance (cx : ExportContext) (reader : Ctx) : Decidable (MapAgrees cx reader) :=
  inferInstanceAs (Decidable (∀ e ∈ cx.map,
    resolve reader.store e.record = some e.target ∧
    NameAgrees cx e.source (reader.nameOf e.target) ∧ sourceRecordFlags cx reader e = true))

/-- Precise direct-cone relation. Reader declarations are deliberately kept
separate from the installed `env`: binder annotations/lets may change there. -/
structure AdmittedArtifact (input : ArtifactInput) where
  keys_valid : ArtifactKeysValid input
  env : Kernel.Env
  admitted : checkBytes input.limits input.records input.blobs input.hint = .ok env
  pins : Pins
  pins_valid : defaultPins = .ok pins
  prelude : Prelude
  prelude_valid : builtinPrelude = .ok prelude
  constants : List (Address × Ixon.Constant)
  decoded : decodeRecords input.limits input.records = .ok constants
  declarations : Array Kernel.Declaration
  readerState : State
  detailed_reading : readRecords (streamContext pins prelude constants input.blobs input.hint)
    prelude.state constants.toArray = .ok (readerState, declarations)
  reading : readStream pins prelude constants input.blobs input.hint = .ok declarations

/-- Source correspondence extends one reusable admitted artifact. -/
structure AcceptedAssociation (input : Input) extends AdmittedArtifact input.toArtifactInput where
  domain : DirectDomain input.source input.roots input.map
  map_agrees : MapAgrees ⟨input.source, input.map, pins⟩
    (streamContext pins prelude constants input.blobs input.hint)
  correspondence : SourceCorrespondence ⟨input.source, input.map, pins⟩
    (streamContext pins prelude constants input.blobs input.hint) constants declarations
  block_correspondence : BlockCorrespondence ⟨input.source, input.map, pins⟩ readerState
  definition_groups : DefinitionGroupsCovered ⟨input.source, input.map, pins⟩ constants

inductive Decline where
  | admission (error : Kernel.Admission.Error)
  | unsupported (source : Lean.Name) (feature : String)
  | malformedInput (reason : String)
  | sourceDomain
  | setup (reason : String)
  | decoding (error : ByteError)
  | reading (error : Kernel.Admission.Error)
  | mapMismatch
  | correspondence
  | blockCorrespondence
  | definitionGroupCorrespondence

/-- The runtime checks are the constructors' proof premises, not assumptions
supplied by the caller. Structural equality decisions are kernel-checked. -/
def prepareArtifact (input : ArtifactInput) : Except Decline (AdmittedArtifact input) :=
  if hk : ArtifactKeysValid input then
  match ha : checkBytes input.limits input.records input.blobs input.hint with
  | .error e => .error (.admission e)
  | .ok env =>
      match hp : defaultPins with
      | .error e => .error (.setup e)
      | .ok pins =>
        match hq : builtinPrelude with
        | .error e => .error (.setup e)
        | .ok pre =>
          match hc : decodeRecords input.limits input.records with
          | .error e => .error (.decoding e)
          | .ok constants =>
            match hr : readRecords (streamContext pins pre constants input.blobs input.hint)
                pre.state constants.toArray with
            | .error (e, position) => .error (.reading (.read position e))
            | .ok (state, decls) =>
              have hs : readStream pins pre constants input.blobs input.hint = .ok decls := by
                unfold readStream
                change (match readRecords
                  (streamContext pins pre constants input.blobs input.hint)
                  pre.state constants.toArray with
                  | .ok (_, ds) => Except.ok ds
                  | .error (e, i) => Except.error (Kernel.Admission.Error.read i e)) = .ok decls
                rw [hr]
              .ok ⟨hk, env, ha, pins, hp, pre, hq, constants, hc, decls, state, hr, hs⟩
  else .error (.malformedInput "record and blob keys must be exactly 32 bytes")

def checkAssociation (input : Input) (artifact : AdmittedArtifact input.toArtifactInput) :
    Except Decline (AcceptedAssociation input) :=
  if hd : DirectDomain input.source input.roots input.map then
    match input.source.declarations.findSome? (fun ci =>
        (unsupportedSource ci).map (ci.name, ·)) with
    | some (source, feature) => .error (.unsupported source feature)
    | none =>
    let cx : ExportContext := ⟨input.source, input.map, artifact.pins⟩
    let reader := streamContext artifact.pins artifact.prelude artifact.constants input.blobs input.hint
    if hm : MapAgrees cx reader then
      if hf : SourceCorrespondence cx reader artifact.constants artifact.declarations then
        if hb : BlockCorrespondence cx artifact.readerState then
          if hg : DefinitionGroupsCovered cx artifact.constants then
            .ok ⟨artifact, hd, hm, hf, hb, hg⟩
          else .error .definitionGroupCorrespondence
        else .error .blockCorrespondence
      else .error .correspondence
    else .error .mapMismatch
  else .error .sourceDomain

def checkCompiled (input : Input) : Except Decline (AcceptedAssociation input) := do
  checkAssociation input (← prepareArtifact input.toArtifactInput)

/-- Executable success entails actual admission and every finite source
declaration's independent direct correspondence in the exact reader stream. -/
theorem faithful_sound {input : Input} {accepted : AcceptedAssociation input}
    (_h : checkCompiled input = .ok accepted) :
    checkBytes input.limits input.records input.blobs input.hint = .ok accepted.env ∧
    DirectDomain input.source input.roots input.map ∧
    SourceCorrespondence ⟨input.source, input.map, accepted.pins⟩
      (streamContext accepted.pins accepted.prelude accepted.constants input.blobs input.hint)
      accepted.constants accepted.declarations ∧
    BlockCorrespondence ⟨input.source, input.map, accepted.pins⟩ accepted.readerState ∧
    DefinitionGroupsCovered ⟨input.source, input.map, accepted.pins⟩ accepted.constants :=
  ⟨accepted.admitted, accepted.domain, accepted.correspondence,
    accepted.block_correspondence, accepted.definition_groups⟩

/-- The existing target model theorem applies to these exact accepted bytes.
This is not yet source semantic pull-back (S). -/
theorem AcceptedAssociation.has_model (V : Type u) [Kernel.SetTheory V]
    {input : Input} (accepted : AcceptedAssociation input) :
    Nonempty (Kernel.Model V accepted.env) :=
  checkBytes_has_model V accepted.admitted

/-- Admission provides installation, independently of source correspondence.
No equality of raw reader types and installed annotated types is asserted. -/
theorem AcceptedAssociation.installed {input : Input} (accepted : AcceptedAssociation input) :
    ∃ pins pre natPins, defaultPins = .ok pins ∧ builtinPrelude = .ok pre ∧
      builtinNatOpPins = .ok natPins ∧
      WithinBatch input.limits input.records input.blobs ∧ UniqueKeys input.records input.blobs ∧
      ∃ constants, RecordsRead input.limits input.records constants ∧
        Installed pins pre natPins constants input.blobs input.hint accepted.env :=
  checkBytes_reading accepted.admitted

/-- The installation witness uses these exact decoded constants, pins and
prelude, rather than merely some existentially admitted reading. -/
theorem AdmittedArtifact.installed_exact {input : ArtifactInput} (artifact : AdmittedArtifact input) :
    ∃ natPins, builtinNatOpPins = .ok natPins ∧
      Installed artifact.pins artifact.prelude natPins artifact.constants
        input.blobs input.hint artifact.env := by
  obtain ⟨pins, pre, natPins, hp, hq, hn, hc⟩ := checkBytes_with artifact.admitted
  have hp' : pins = artifact.pins := Except.ok.inj (hp.symm.trans artifact.pins_valid)
  have hq' : pre = artifact.prelude := Except.ok.inj (hq.symm.trans artifact.prelude_valid)
  subst pins
  subst pre
  rw [checkBytesWith_eq] at hc
  cases hf : preflight input.limits input.records input.blobs with
  | error e => simp [hf, bind, Except.bind, Except.mapError] at hc
  | ok u =>
    cases hk : uniqueKeys input.records input.blobs with
    | error e => simp [hf, hk, bind, Except.bind, Except.mapError] at hc
    | ok v =>
      simp only [hf, hk, artifact.decoded, bind, Except.bind, Except.mapError] at hc
      exact ⟨natPins, hn, checkConstantsWith_installed hc⟩

/-- The exact declaration array used by correspondence, behind the actual
prelude, is the array accepted by the certified fold. This binds member-level
reader evidence to admission without replacing it by installation skeletons. -/
theorem AdmittedArtifact.checked_declarations {input : ArtifactInput}
    (artifact : AdmittedArtifact input) :
    ∃ natPins, builtinNatOpPins = .ok natPins ∧
      Kernel.Cached.checkDecls .verified natPins
        (Kernel.Frontend.preparePrelude artifact.prelude.ix artifact.declarations) = .ok artifact.env := by
  obtain ⟨pins, pre, natPins, hp, hq, hn, hc⟩ := checkBytes_with artifact.admitted
  have hp' : pins = artifact.pins := Except.ok.inj (hp.symm.trans artifact.pins_valid)
  have hq' : pre = artifact.prelude := Except.ok.inj (hq.symm.trans artifact.prelude_valid)
  subst pins
  subst pre
  rw [checkBytesWith_eq] at hc
  cases hf : preflight input.limits input.records input.blobs with
  | error e => simp [hf, bind, Except.bind, Except.mapError] at hc
  | ok u =>
    cases hk : uniqueKeys input.records input.blobs with
    | error e => simp [hf, hk, bind, Except.bind, Except.mapError] at hc
    | ok v =>
      simp only [hf, hk, artifact.decoded, bind, Except.bind, Except.mapError] at hc
      refine ⟨natPins, hn, ?_⟩
      simp only [checkConstantsWith, artifact.reading, bind, Except.bind] at hc
      cases hcheck : Kernel.Cached.checkDecls .verified natPins
          (Kernel.Frontend.preparePrelude artifact.prelude.ix artifact.declarations) with
      | error e => simp [hcheck, Except.mapError] at hc
      | ok result => simpa [hcheck, Except.mapError] using hc

/-- Direct correspondence identifies a full member of an actual declaration
in the accepted fold. Inductive members retain every rule field via
`readerEntries`; flattened definition-block declarations use the same route.
This is reader membership, not equality to installed annotated fields. -/
theorem AcceptedAssociation.direct_member_reading {input : Input}
    (accepted : AcceptedAssociation input) {ci : Lean.ConstantInfo}
    (direct : DirectMatch ⟨input.source, input.map, accepted.pins⟩
      (streamEntries accepted.declarations) ci) :
    ∃ expected actual decl natPins,
      directExport ⟨input.source, input.map, accepted.pins⟩ ci = .ok expected ∧
      EntryCompatible actual expected ∧ actual ∈ readerEntries decl ∧
      decl ∈ Kernel.Frontend.preparePrelude accepted.prelude.ix accepted.declarations ∧
      builtinNatOpPins = .ok natPins ∧
      Kernel.Cached.checkDecls .verified natPins
        (Kernel.Frontend.preparePrelude accepted.prelude.ix accepted.declarations) = .ok accepted.env := by
  cases he : directExport ⟨input.source, input.map, accepted.pins⟩ ci with
  | error e => simp [DirectMatch, he] at direct
  | ok expected =>
    have hm : expected.withoutHint ∈ compatibleEntries (streamEntries accepted.declarations) := by
      simpa [DirectMatch, he] using direct
    obtain ⟨actual, ha, same⟩ := List.mem_map.mp hm
    obtain ⟨decl, hd, hm⟩ := List.mem_flatMap.mp ha
    obtain ⟨natPins, hn, hc⟩ := accepted.toAdmittedArtifact.checked_declarations
    exact ⟨expected, actual, decl, natPins, rfl, same, hm,
      Kernel.Frontend.mem_preparePrelude (by simpa using hd), hn, hc⟩

/-- A raw-source definition is related to an actual declaration in the
admitted fold by the reader's proved normalization specification. Its raw
body remains explicit; no projection denotation theorem is smuggled into W. -/
theorem AcceptedAssociation.raw_definition_reading {input : Input}
    (accepted : AcceptedAssociation input) {ci : Lean.ConstantInfo}
    {owner : Address} {record : Ixon.Constant} {cv : Kernel.ConstantVal}
    {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (record_found : rawSourceRecord ⟨input.source, input.map, accepted.pins⟩
      accepted.constants ci = some (owner, record))
    (exported : directExport ⟨input.source, input.map, accepted.pins⟩ ci = .ok (.defn cv value hint))
    (raw : RawSourceMatch ⟨input.source, input.map, accepted.pins⟩
      (streamContext accepted.pins accepted.prelude accepted.constants input.blobs input.hint)
      accepted.constants ci) :
    ∃ natPins state decl ds, builtinNatOpPins = .ok natPins ∧
      DefinitionDecl cv value (projRewrite state cv value) .defn decl ∧
      decl ∈ ds ∧ Kernel.Cached.checkDecls .verified natPins ds = .ok accepted.env := by
  have hm : RawEntryMatch
      (streamContext accepted.pins accepted.prelude accepted.constants input.blobs input.hint)
      owner record (.defn cv value hint) := by
    simpa only [RawSourceMatch, exported, record_found] using raw
  cases hi : record.info <;> simp only [RawEntryMatch, hi] at hm
  all_goals try contradiction
  case defn definition =>
    obtain ⟨natPins, hn, installed⟩ := accepted.toAdmittedArtifact.installed_exact
    obtain ⟨state, decl, ds, reading, member, checked, _⟩ :=
      installed.singleton (rawSourceRecord_mem record_found) (by simp [hi, isSingleton])
    exact ⟨natPins, state, decl, ds, hn,
      RawDefinitionAgrees.reader_decl hi hm reading, member, checked⟩

/-- Restrict only source associations. Target bytes remain exact, including
their support/prelude; selecting a source root does not forge a new artifact. -/
def selectedInput (input : Input) (root : Lean.Name)
    (selected : SelectedSource input.source [root]) : Input :=
  { input with
    source := selected.source
    roots := [root]
    map := input.map.filter (fun e => selected.source.names.contains e.source) }

structure RootAssociation (input : Input) (root : Lean.Name) where
  selected : SelectedSource input.source [root]
  association : AcceptedAssociation (selectedInput input root selected)

inductive RootDecline where
  | selection (reason : String)
  | certification (reason : Decline)

/-- One supported cone can certify despite unrelated unsupported ambient
source declarations. Each requested root receives its own explicit outcome. -/
def checkRootWithArtifact (input : Input) (artifact : AdmittedArtifact input.toArtifactInput)
    (root : Lean.Name) :
    Except RootDecline (RootAssociation input root) := do
  let selected ← (selectSource input.source [root]).mapError RootDecline.selection
  let association ← (checkAssociation (selectedInput input root selected) artifact).mapError
    RootDecline.certification
  return ⟨selected, association⟩

def checkRoot (input : Input) (root : Lean.Name) :
    Except RootDecline (RootAssociation input root) := do
  let artifact ← (prepareArtifact input.toArtifactInput).mapError RootDecline.certification
  checkRootWithArtifact input artifact root

structure RootOutcome (input : Input) where
  root : Lean.Name
  result : Except RootDecline (RootAssociation input root)

inductive OutcomeClass where
  | certified | unsupported | blocked | rejected
  deriving BEq, Repr

/-- Classification never turns a decline into an acceptance. Original
diagnostics remain in `RootOutcome.result`. Internal/resource failures are
blocked; only completed malformed/correspondence decisions are rejected. -/
def admissionClass : Kernel.Admission.Error → OutcomeClass
  | .limit _ | .prelude _ | .kernel (.internal _) _ => .blocked
  | .read _ (.declined reason) | .kernel (.notImplemented reason) _ =>
    if (reason.splitOn "fuel").length > 1 then .blocked else .unsupported
  | _ => .rejected

def RootOutcome.classification {input : Input} (outcome : RootOutcome input) : OutcomeClass :=
  match outcome.result with
  | .ok _ => .certified
  | .error (.selection _) => .blocked
  | .error (.certification reason) =>
    match reason with
    | .unsupported .. => .unsupported
    | .admission e | .reading e => admissionClass e
    | .decoding (.limit _) | .setup _ => .blocked
    | _ => .rejected

def checkRoots (input : Input) : List (RootOutcome input) :=
  match prepareArtifact input.toArtifactInput with
  | .error e => input.roots.map (fun root => ⟨root, .error (.certification e)⟩)
  | .ok artifact => input.roots.map (fun root => ⟨root, checkRootWithArtifact input artifact root⟩)

theorem checkRoots_coverage (input : Input) :
    (checkRoots input).map RootOutcome.root = input.roots := by
  unfold checkRoots
  split <;> simp [List.map_map, Function.comp_def]

end Ix.CompileCert
