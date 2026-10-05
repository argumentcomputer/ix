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
