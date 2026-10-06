import Ix.CompileCert.AnnotationTrace
import Ix.CompileCert.SourceProjectionLowering

/-! # Source projection normalization

Projection equations and constructor-cover proposals for source projections,
the projection receipt (`SourceProjectionReceipt`), the normalization
(`normalizeSourceProjections`), semantic basis completion, and the normalized
installation (`SourceNormalizedInstallation`,
`SourceConstructorCoverChecked`) with its strong model.
-/

namespace Ix.CompileCert

open Kernel.Reader
open Kernel.Admission

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

/-- Parameters in an open frame containing `extra` more recent binders. -/
def sourceParameterVars (count extra : Nat) : List Kernel.Expr :=
  (List.range count).map (fun i => .bvar (extra + count - 1 - i))

theorem sourceParameterVars_denotes {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V} (arguments : List V) (extra : Nat)
    (frame : ∀ index (inside : index < arguments.length),
      ρ (extra + arguments.length - 1 - index) = arguments[index]) :
    DenotesSpine values env levels ρ (sourceParameterVars arguments.length extra) arguments := by
  apply DenotesSpine.of_get (by simp [sourceParameterVars])
  intro index inside
  have inArgs : index < arguments.length := by simpa [sourceParameterVars] using inside
  simp only [sourceParameterVars, List.getElem_map, List.getElem_range]
  rw [← frame index inArgs]
  exact .bvar

/-- Read parameters below an arbitrary list of more recent binders. This
matches the exact source-owned de Bruijn spine, not a guessed display order. -/
theorem sourceParameterVars_pushed {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} (ρ : Nat → V) (parameters extras : List V) :
    DenotesSpine values env levels (pushArguments (pushArguments ρ parameters) extras)
      (sourceParameterVars parameters.length extras.length) parameters := by
  apply sourceParameterVars_denotes
  intro index inside
  have position : extras.length + parameters.length - 1 - index =
      extras.length + (parameters.length - 1 - index) := by omega
  rw [position, pushArguments_above, pushArguments_get parameters ρ index inside]

/-- Church-encoded constructor presentation at an arbitrary subject:
`∀ P : Prop, (∀ fields, subject = C params fields → P) → P`.
The field domains are the original constructor's dependent telescope.
This avoids importing an unchecked existential-support declaration. -/
def sourceConstructorCoverBody {source : Source} (site : SourceProjectionSite source)
    (owner constructor : Kernel.ConstantVal) (level : Kernel.Level)
    (extra : Nat) (subject : Kernel.Expr) : ExportM Kernel.Expr := do
  let binder : Kernel.BinderMeta := ⟨.never⟩
  let parameters := sourceParameterVars site.owner.numParams (extra + 1)
  let some remaining := Kernel.Frontend.instPisOpen constructor.type parameters
    | throw "source constructor coverage cannot instantiate original parameters"
  let some (fields, _) := remaining.stripPis site.ctor.numFields
    | throw "source constructor coverage cannot read the original field telescope"
  let levels := owner.levelParams.map Kernel.Level.param
  let liftedParams := parameters.map (fun p => p.liftLooseBVars site.ctor.numFields 0)
  let fieldVars := sourceParameterVars site.ctor.numFields 0
  let carrier := Kernel.Expr.mkAppN (.const owner.name levels) liftedParams
  let constructed := Kernel.Expr.mkAppN (.const constructor.name levels) (liftedParams ++ fieldVars)
  let equality := Kernel.Expr.mkAppN (.const Kernel.eqName [level])
    [carrier, subject.liftLooseBVars (site.ctor.numFields + 1) 0, constructed]
  let continuation := fields.foldr
    (fun (type, binder) body => Kernel.Expr.forallE type body binder)
    (.forallE equality (.bvar (site.ctor.numFields + 1)) binder)
  return .forallE (.sort .zero) (.forallE continuation (.bvar 1) binder) binder

/-- Untrusted proposal of a theorem covering arbitrary source carrier
values, not merely constructor applications. The proof eliminates through
the original recursor. Every other motive is the closed true proposition
`∀ P : Prop, P → P`; recursive hypotheses are not assumed as coverage.
Admission plus a semantic reading of this statement is still required. -/
def proposeSourceConstructorCover {source : Source} (site : SourceProjectionSite source) :
    ExportM Kernel.Declaration := do
  let binder : Kernel.BinderMeta := ⟨.never⟩
  let .induct owner _ ← exportSourceEntry (.inductInfo site.owner)
    | throw "source coverage owner export has the wrong kind"
  let .ctor constructor _ _ ← exportSourceEntry (.ctorInfo site.ctor)
    | throw "source coverage constructor export has the wrong kind"
  unless decide (owner.levelParams = constructor.levelParams) do
    throw "source coverage constructor universe telescope differs from its owner"
  let some (parameterBinders, .sort level) := owner.type.stripPis site.owner.numParams
    | throw "source coverage owner is not a zero-index parameter telescope"
  let levels := owner.levelParams.map Kernel.Level.param
  let carrier := Kernel.Expr.mkAppN (.const owner.name levels) (sourceParameterVars site.owner.numParams 0)
  let statementBody ← sourceConstructorCoverBody site owner constructor level 1 (.bvar 0)
  let type := parameterBinders.foldr
    (fun (type, binder) body => Kernel.Expr.forallE type body binder)
    (.forallE carrier statementBody binder)
  let some (.recInfo recursor) := source.find (site.ownerName.str "rec")
    | throw "source coverage has no original recursor"
  unless recursor.numParams == site.owner.numParams && recursor.numIndices == 0 do
    throw "source coverage recursor owner parameters or indices disagree"
  let .recursor recHeader _ _ _ ← exportSourceEntry (.recInfo recursor)
    | throw "source coverage recursor export has the wrong kind"
  unless owner.levelParams.all (fun p => recHeader.levelParams.contains p) &&
      (recHeader.levelParams.filter (fun p => !owner.levelParams.contains p)).length ≤ 1 do
    throw "source coverage recursor universe selection is unsupported"
  let recLevels := recHeader.levelParams.map fun p =>
    if owner.levelParams.contains p then Kernel.Level.param p else .zero
  let recType := recHeader.type.instantiateLevelParams recHeader.levelParams recLevels
  let parameters := sourceParameterVars site.owner.numParams 1
  let some recType := Kernel.Frontend.instPisOpen recType parameters
    | throw "source coverage recursor parameters cannot be instantiated"
  let truth : Kernel.Expr := .forallE (.sort .zero)
    (.forallE (.bvar 0) (.bvar 1) binder) binder
  let truthProof : Kernel.Expr := .lam (.sort .zero)
    (.lam (.bvar 0) (.bvar 0) binder) binder
  let makeMotive := fun domain => do
    let (binders, _) := Kernel.Frontend.stripPisAll domain
    match binders with
    | [(major, _)] =>
      if Kernel.Frontend.headIs owner.name major then
        let body ← (sourceConstructorCoverBody site owner constructor level 2 (.bvar 0)).toOption
        return Kernel.Frontend.mkLams binders body
      else return Kernel.Frontend.mkLams binders truth
    | _ => return Kernel.Frontend.mkLams binders truth
  let some (motives, recType) := Kernel.Frontend.buildBinders makeMotive recursor.numMotives recType
    | throw "source coverage motive construction failed"
  let makeMinor := fun domain => do
    let (binders, result) := Kernel.Frontend.stripPisAll domain
    let some major := result.getAppArgs.getLast? | none
    if Kernel.Frontend.headIs constructor.name major then
      if site.ctor.numFields > binders.length then none else do
        let expected := Kernel.Expr.mkAppN (.const constructor.name levels)
          (sourceParameterVars site.owner.numParams (1 + binders.length) ++
            (List.range site.ctor.numFields).map (fun i => .bvar (binders.length - 1 - i)))
        if !decide (major = expected) then none else do
          let coverage ← (sourceConstructorCoverBody site owner constructor level
            (1 + binders.length) major).toOption
          let some (arguments, _) := coverage.stripPis 2 | none
          let carrier := Kernel.Expr.mkAppN (.const owner.name levels)
            (sourceParameterVars site.owner.numParams (3 + binders.length))
          let reflexive := Kernel.Expr.mkAppN (.const Kernel.eqReflName [level])
            [carrier, major.liftLooseBVars 2 0]
          let fields := (List.range site.ctor.numFields).map
            (fun i => Kernel.Expr.bvar (binders.length + 1 - i))
          return Kernel.Frontend.mkLams binders (Kernel.Frontend.mkLams arguments
            (Kernel.Expr.mkAppN (.bvar 0) (fields ++ [reflexive])))
    else return Kernel.Frontend.mkLams binders truthProof
  let some (minors, recType) := Kernel.Frontend.buildBinders makeMinor recursor.numMinors recType
    | throw "source coverage minor construction failed"
  let .forallE majorDomain _ _ := recType | throw "source coverage recursor has no major premise"
  unless Kernel.Frontend.headIs owner.name majorDomain do
    throw "source coverage recursor major premise has another owner"
  let application := Kernel.Expr.mkAppN (.const recHeader.name recLevels)
    (parameters ++ motives ++ minors ++ [.bvar 0])
  let value := Kernel.Frontend.mkLams parameterBinders (.lam carrier application binder)
  return .thmDecl ⟨owner.name.str "_source_constructor_cover", owner.levelParams, type⟩ value

/-- Source-owned lowering proposal. Original source syntax and constructor
metadata are authoritative; the replacement value is read from the Lean
lowering equation that the certifier had Lean's kernel check
(`loweringEquationName`). Neither target data, the reader's `projRewrite`
nor the source modeller's `proj_i.iota` artifact is consulted. Without such an
equation the declaration is left unchanged. Acceptance below checks the
replacement against the original (`SourceProjectionLowering`) and its
constructor equation (`SourceProjectionReceipt`); generation proves nothing. -/
def proposeSourceProjection (source : Source) (witnesses : LoweringWitnesses)
    (declaration : Kernel.Declaration) : ExportM (Option (Kernel.Declaration × Kernel.Declaration)) := do
  let .defnDecl header body hint := declaration | return none
  let some ci := source.declarations.find? (fun ci => decide (sourceName ci.name = header.name))
    | return none
  let .defnInfo definition := ci | return none
  let some (owner, field, binders) := sourceProjectionBody definition.value | return none
  let some witness := witnesses.find? (fun w => decide (w.name = loweringEquationName definition.name))
    | return none
  let site ← sourceProjectionSite source owner field
  unless binders == site.owner.numParams + 1 do
    throw "source projection binder count differs from original owner parameters"
  let original ← exportSourceEntry ci
  unless decide (original = .defn header body hint) do
    throw "source projection declaration differs from its immutable original export"
  let statement ← exportSourceExpr definition.levelParams witness.type
  let some value := loweringValueOf (site.owner.numParams + 1) statement
    | throw "source projection lowering equation has no right-hand side"
  let some level := loweredLevel (site.owner.numParams + 1) value
    | throw "source projection lowering equation's right-hand side has no recursor level"
  let equation ← sourceProjectionEquation site header level
  return some (.defnDecl header value hint, equation)

/-- The same proposal for a projection onto a proof field, which Lean makes a
theorem: the replacement is the theorem with the lowered proof (same header).
No constructor equation is added: a proof's value is irrelevant to the
statement, which is all the fold and the S endpoint compare for a theorem. -/
def proposeSourceProof (source : Source) (witnesses : LoweringWitnesses)
    (declaration : Kernel.Declaration) : ExportM (Option Kernel.Declaration) := do
  let .thmDecl header body := declaration | return none
  let some ci := source.declarations.find? (fun ci => decide (sourceName ci.name = header.name))
    | return none
  let .thmInfo proof := ci | return none
  let some (owner, field, binders) := sourceProjectionBody proof.value | return none
  let some witness := witnesses.find? (fun w => decide (w.name = loweringEquationName proof.name))
    | return none
  let site ← sourceProjectionSite source owner field
  unless binders == site.owner.numParams + 1 do
    throw "source proof projection binder count differs from original owner parameters"
  let original ← exportSourceEntry ci
  unless decide (original = .thm header body) do
    throw "source proof projection differs from its immutable original export"
  let statement ← exportSourceExpr proof.levelParams witness.type
  let some value := loweringValueOf (site.owner.numParams + 1) statement
    | throw "source proof projection lowering equation has no right-hand side"
  return some (.thmDecl header value)

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
inductive SourceProjectionNormalization (source : Source) (witnesses : LoweringWitnesses) :
    SourceModelState → List Kernel.Declaration → List Kernel.Declaration → Prop
  | nil (state) : SourceProjectionNormalization source witnesses state [] []
  | unchanged {state original rest output}
      (proposal : proposeSourceProjection source witnesses original = .ok none)
      (proofProposal : proposeSourceProof source witnesses original = .ok none)
      (tail : SourceProjectionNormalization source witnesses (state.note original) rest output) :
      SourceProjectionNormalization source witnesses state (original :: rest) (original :: output)
  | lowered {state original rest replacement equation output}
      (proposal : proposeSourceProjection source witnesses original = .ok (some (replacement, equation)))
      (association : SourceProjectionReceipt source original replacement equation)
      (lowering : SourceProjectionLowering source witnesses original replacement)
      (fresh : ∀ name ∈ equation.names, state.types[name]? = none ∧
        ∀ declaration ∈ original :: rest, name ∉ declaration.names)
      (tail : SourceProjectionNormalization source witnesses
        ((state.note replacement).note equation) rest output) :
      SourceProjectionNormalization source witnesses state (original :: rest)
        (replacement :: equation :: output)
  | loweredProof {state original rest replacement output}
      (proposal : proposeSourceProjection source witnesses original = .ok none)
      (proofProposal : proposeSourceProof source witnesses original = .ok (some replacement))
      (lowering : SourceProjectionLowering source witnesses original replacement)
      (tail : SourceProjectionNormalization source witnesses (state.note replacement) rest output) :
      SourceProjectionNormalization source witnesses state (original :: rest) (replacement :: output)

def normalizeSourceProjections (source : Source) (witnesses : LoweringWitnesses) (state : SourceModelState)
    (input : List Kernel.Declaration) :
    ExportM { output : List Kernel.Declaration //
      SourceProjectionNormalization source witnesses state input output } :=
  match input with
  | [] => .ok ⟨[], .nil state⟩
  | original :: rest =>
    match hp : proposeSourceProjection source witnesses original with
    | .error why => .error why
    | .ok none =>
      match hq : proposeSourceProof source witnesses original with
      | .error why => .error why
      | .ok none => do
        let output ← normalizeSourceProjections source witnesses (state.note original) rest
        return ⟨original :: output.val, .unchanged hp hq output.property⟩
      | .ok (some replacement) => do
        let lowering ← checkSourceProjectionLowering source witnesses original replacement
        let output ← normalizeSourceProjections source witnesses (state.note replacement) rest
        return ⟨replacement :: output.val, .loweredProof hp hq lowering output.property⟩
    | .ok (some (replacement, equation)) =>
      if hf : ∀ name ∈ equation.names, state.types[name]? = none ∧
          ∀ declaration ∈ original :: rest, name ∉ declaration.names then do
        let association ← checkSourceProjectionReceipt source original replacement equation
        let lowering ← checkSourceProjectionLowering source witnesses original replacement
        let output ← normalizeSourceProjections source witnesses
          ((state.note replacement).note equation) rest
        return ⟨replacement :: equation :: output.val,
          .lowered hp association lowering hf output.property⟩
      else .error "source projection equation name conflicts with an existing declaration"

/-- The finite source-owned basis suffix is selected from the normalized
stream itself. A present source identity is left intact, even if it will be
refused by the subsequent verified fold. No target names or data participate. -/
def sourceDeclaredNames : Kernel.Declaration → List Kernel.Name
  | .basisDecl kind => kind.decls.map Kernel.ConstantInfo.name
  | declaration => declaration.names

def missingSourceSemanticBasis (original : List Kernel.Declaration) : List Kernel.BasisKind :=
  (sourceSemanticBasisSupport.filter fun pair =>
    !(original.any fun declaration => (sourceDeclaredNames declaration).contains pair.1)).map (·.2)

structure SourceSemanticBasisCompletion (original : List Kernel.Declaration) where
  basisSupport : List Kernel.BasisKind
  selected : basisSupport = missingSourceSemanticBasis original

def SourceSemanticBasisCompletion.declarations {original : List Kernel.Declaration}
    (completion : SourceSemanticBasisCompletion original) : List Kernel.Declaration :=
  original ++ completion.basisSupport.map Kernel.Declaration.basisDecl

/-- Explicit identity bindings for every added reserved basis member, including
members hidden by `Declaration.names` on compact basis records. These remain
subject to original-name priority and the full actual installed checks. -/
def SourceSemanticBasisCompletion.nameBindings {original : List Kernel.Declaration}
    (completion : SourceSemanticBasisCompletion original) : List (Kernel.Name × Kernel.Name) :=
  completion.basisSupport.flatMap fun kind => kind.decls.map fun entry => (entry.name, entry.name)

def completeSourceSemanticBasis (original : List Kernel.Declaration) :
    SourceSemanticBasisCompletion original := ⟨missingSourceSemanticBasis original, rfl⟩

/-- Exact prefix preservation includes complete records, names and order;
support never rewrites a normalized declaration. -/
theorem SourceSemanticBasisCompletion.original_prefix {original : List Kernel.Declaration}
    (completion : SourceSemanticBasisCompletion original) :
    original.IsPrefix completion.declarations :=
  ⟨completion.basisSupport.map Kernel.Declaration.basisDecl, rfl⟩

theorem SourceSemanticBasisCompletion.support_closed {original : List Kernel.Declaration}
    (completion : SourceSemanticBasisCompletion original) :
    ∀ kind ∈ completion.basisSupport, sourceBasisSupportClosed kind = true := by
  intro kind present
  rw [completion.selected] at present
  simp only [missingSourceSemanticBasis, List.mem_map, List.mem_filter] at present
  obtain ⟨pair, ⟨inside, _⟩, rfl⟩ := present
  exact sourceSemanticBasisSupport_closed pair inside

theorem SourceSemanticBasisCompletion.only_missing {original : List Kernel.Declaration}
    (completion : SourceSemanticBasisCompletion original) {kind : Kernel.BasisKind}
    (present : kind ∈ completion.basisSupport) :
    ∃ name, (name, kind) ∈ sourceSemanticBasisSupport ∧
      ∀ declaration ∈ original, name ∉ sourceDeclaredNames declaration := by
  rw [completion.selected] at present
  simp only [missingSourceSemanticBasis, List.mem_map, List.mem_filter] at present
  obtain ⟨pair, ⟨inside, absent⟩, rfl⟩ := present
  refine ⟨pair.1, inside, ?_⟩
  intro declaration member contradiction
  simp at absent
  exact absent declaration member contradiction

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
  witnesses : LoweringWitnesses
  normalizedDeclarations : List Kernel.Declaration
  normalization : SourceProjectionNormalization source witnesses {} modelProposal.declarations.toList
    normalizedDeclarations
  semanticSupport : SourceSemanticBasisCompletion normalizedDeclarations
  declarations : List Kernel.Declaration
  semantic_append : declarations = semanticSupport.declarations
  /-- The Nat-operation pin sets the source fold runs with. The fold is sound for
  every pin list (its certificates are checked by the fold), so the pins are an
  untrusted proposal: the certifier passes the builtin pins with their constants
  renamed into the source's names, so that Lean's own `Nat.div`/`Nat.mod` spellings
  are accepted (with no pins the fold declines them). -/
  pins : List Kernel.NatOpPinSet
  env : Kernel.Env
  checked : Kernel.Cached.checkDecls .verified pins declarations.toArray = .ok env

/-- The normalized stream is preserved literally, before the separate source
semantic support suffix. This does not identify normalization with the
immutable original source expression. -/
theorem SourceNormalizedInstallation.normalized_prefix {source : Source} {roots : List Lean.Name}
    (installed : SourceNormalizedInstallation source roots) :
    installed.normalizedDeclarations.IsPrefix installed.declarations := by
  rw [installed.semantic_append]
  exact installed.semanticSupport.original_prefix

/-- The installation given the source's completeness (e.g. from an accepted W
association's `DirectDomain`, decided there with hash sets), so it is not decided
again by list membership. -/
def installSourceNormalizedComplete {source : Source} {roots : List Lean.Name}
    (hc : CompleteSource source roots) (pins : List Kernel.NatOpPinSet)
    (witnesses : LoweringWitnesses) : Except SourceModelError (SourceNormalizedInstallation source roots) :=
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
              match normalizeSourceProjections source witnesses {} proposal.declarations.toList with
              | .error why => .error (.proposalFailure why)
              | .ok output =>
                let completion := completeSourceSemanticBasis output.val
                match hk : Kernel.Cached.checkDecls .verified pins completion.declarations.toArray with
                | .error (error, position) => .error (.checking error position)
                | .ok env => .ok ⟨hc, original, he, proposal, hp, hs, hm, hb,
                    witnesses, output.val, output.property, completion, completion.declarations, rfl,
                    pins, env, hk⟩
            else .error .supportMismatch
          else .error .correspondence
        else .error .changedOriginal

def installSourceNormalizedWith (pins : List Kernel.NatOpPinSet) (source : Source) (roots : List Lean.Name)
    (witnesses : LoweringWitnesses) : Except SourceModelError (SourceNormalizedInstallation source roots) :=
  if hc : CompleteSource source roots then installSourceNormalizedComplete hc pins witnesses
  else .error .incomplete

/-- The installation with no Nat-operation pins (the route's original form). -/
def installSourceNormalized (source : Source) (roots : List Lean.Name) (witnesses : LoweringWitnesses) :
    Except SourceModelError (SourceNormalizedInstallation source roots) :=
  installSourceNormalizedWith [] source roots witnesses

theorem SourceNormalizedInstallation.has_model (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceNormalizedInstallation source roots) :
    Nonempty (Kernel.Model V installed.env) :=
  Kernel.model_exists V installed.pins installed.declarations.toArray installed.env installed.checked

theorem SourceNormalizedInstallation.strong_model (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceNormalizedInstallation source roots) :
    Nonempty (StrongInstalledModel V installed.env) :=
  strongInstalledModel_exists V installed.pins installed.declarations.toArray installed.env installed.checked

/-- In particular, every generated constructor equation is connected to
the actual full annotated statement of its independently installed theorem. -/
theorem SourceNormalizedInstallation.theorem_annotation
    {source : Source} {roots : List Lean.Name} (installed : SourceNormalizedInstallation source roots)
    {header : Kernel.ConstantVal} {value : Kernel.Expr}
    (present : Kernel.Declaration.thmDecl header value ∈ installed.declarations) :
    AnnotationTrace.TheoremInstalled .verified header value installed.env :=
  AnnotationTrace.theorem_checked (by simpa using present) installed.checked

/-- A separate certifier-owned extension of an independently installed
source bundle. The new theorem quantifies every carrier member. This
receipt records its exact proposal and admission, not yet its semantic
constructor-surjectivity interpretation. The original routes are unchanged. -/
structure SourceConstructorCoverChecked {source : Source} {roots : List Lean.Name}
    (installed : SourceNormalizedInstallation source roots) (site : SourceProjectionSite source) where
  header : Kernel.ConstantVal
  value : Kernel.Expr
  proposed : proposeSourceConstructorCover site = .ok (.thmDecl header value)
  fresh : ∀ declaration ∈ installed.declarations, header.name ∉ declaration.names
  env : Kernel.Env
  checked : Kernel.Cached.checkDecls .verified installed.pins
    (installed.declarations ++ [Kernel.Declaration.thmDecl header value]).toArray = .ok env

def checkSourceConstructorCover {source : Source} {roots : List Lean.Name}
    (installed : SourceNormalizedInstallation source roots) (site : SourceProjectionSite source) :
    Except SourceModelError (SourceConstructorCoverChecked installed site) :=
  match hp : proposeSourceConstructorCover site with
  | .error why => .error (.proposalFailure why)
  | .ok (.thmDecl header value) =>
    if hf : ∀ declaration ∈ installed.declarations, header.name ∉ declaration.names then
      match hk : Kernel.Cached.checkDecls .verified installed.pins
          (installed.declarations ++ [Kernel.Declaration.thmDecl header value]).toArray with
      | .error (error, position) => .error (.checking error position)
      | .ok env => .ok ⟨header, value, hp, hf, env, hk⟩
    else .error (.proposalFailure "source constructor coverage name is not fresh")
  | .ok _ => .error (.proposalFailure "source constructor coverage proposal is not a theorem")

theorem SourceConstructorCoverChecked.annotation {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    (coverage : SourceConstructorCoverChecked installed site) :
    AnnotationTrace.TheoremInstalled .verified coverage.header coverage.value coverage.env :=
  AnnotationTrace.theorem_checked (by simp) coverage.checked

theorem SourceConstructorCoverChecked.strong_model (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    (coverage : SourceConstructorCoverChecked installed site) :
    Nonempty (StrongInstalledModel V coverage.env) :=
  strongInstalledModel_exists V installed.pins _ coverage.env coverage.checked

theorem SourceInstallation.strong_model (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceInstallation source roots) :
    Nonempty (StrongInstalledModel V installed.env) :=
  strongInstalledModel_exists V [] installed.declarations installed.env installed.checked

/-- Pull-back on the independently installed direct source. The exact source
fold remains visible and the semantic image premises are not inferred from
it. This result supplies types/definition values, not the remaining strong
recursor laws or the end-to-end S association. -/
theorem SourceInstallation.target_value_pullback {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceInstallation source roots)
    {targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv) (map : PullbackMap)
    (types : PullbackTypeEvidence target.public installed.env map)
    (values : PullbackDefinitionEvidence target installed.env map)
    (locality : map.LevelLocality installed.env targetEnv) :
    Kernel.Cached.checkDecls .verified [] installed.declarations = .ok installed.env ∧
      ∃ pulled : PublicValueModel V installed.env,
        pulled.model.cval = map.values target.public.cval :=
  ⟨installed.checked, values.valueModel types locality, rfl⟩

/-- The normalized source route remains a distinct input receipt, retaining
its immutable original stream and checked normalization evidence. This does
not identify that receipt with the direct/Sublist installation route. -/
theorem SourceNormalizedInstallation.target_value_pullback {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceNormalizedInstallation source roots)
    {targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv) (map : PullbackMap)
    (types : PullbackTypeEvidence target.public installed.env map)
    (values : PullbackDefinitionEvidence target installed.env map)
    (locality : map.LevelLocality installed.env targetEnv) :
    Kernel.Cached.checkDecls .verified installed.pins installed.declarations.toArray = .ok installed.env ∧
      ∃ pulled : PublicValueModel V installed.env,
        pulled.model.cval = map.values target.public.cval :=
  ⟨installed.checked, values.valueModel types locality, rfl⟩

end Ix.CompileCert
