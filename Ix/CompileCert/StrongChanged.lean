import Ix.CompileCert.StrongCone
import Ix.CompileCert.Changed

/-! # S for cones that reach changed constants, at the value level (M7 S+a)

`StrongCone.sound` (`StrongCone.lean`) is S for a cone whose W association is the old one
(`AcceptedAssociation`: every source declaration matched directly or through its raw
record). A constant W+ certifies (`Changed.lean`: a theorem by its statement, a definition
by a theorem row stating its Lean value) has a target row that is not its Lean declaration's
export, and the strong check compares installed rows syntactically, so such a cone is
refused there. Worse, the strong *conclusion* cannot hold for the up-cone of a changed
definition: `EnvModelM.defn_reads` is an `AnnotTerm` equality and `denoteMeta` inlines
constant leaves, so the annotation pull-back fails at the changed definition and at every
constant whose value mentions it (`docs/compiler-certification.md` §1.5).

This module is S for such cones **at the value level**, the level the certification's Theorem S
is stated at (membership, `False` empty and `Eq` equality, definitions denote their values,
recursor rules hold), beside the unchanged `StrongCone.sound`:

* the cone's W association is W+'s (`AcceptedAssociation' input images support`), its support
  the W+ rows of the cone (and any source-owned support), folded once by the certified checker;
  the target of S is that fold, `accepted.folded.env`;
* the check (`checkChangedAssociation`) is the installed association's value-level part
  (telescopes, types, definitions, the `False`/`Eq` pins, capabilities, eta, recursors,
  constructors, rule level links), with one alternative: an installed source definition
  `c := v` whose target row's value is not the image of `v` passes when the target has a
  **theorem row** (named by an untrusted proposal) whose installed statement is
  `@Eq T (names c).{params} r` with `r` the image of `v` (`definitionRowF`). W+'s `rfl` rows and
  package V's value rows have this shape; Lean's `c.eq_def` does not (an unfolding equation does
  not determine a value in an existence-only model);
* `StrongCone'.sound`: W+'s conclusion for the input, and for **every** strong model of the
  target a `PublicValueModel` of the installed source whose values are the pull-back of the
  target's, with `PublicCapabilityLaws` and `UniversalRuleSimulation`, every original
  declaration installed as its export or through a lowering receipt;
* `StrongCone'.row_equations`: W+'s `model_equations` for the cone, in the same target
  environment: the rows the conclusion rests on hold in every strong model of it.

**What is weaker than `StrongCone.sound`, and why.** The source model is a public value model
with the capability and rule laws, not a `StrongInstalledModel` (`EnvModelM`): the annotations
(`acval`), graded readings, the `AnnotTerm` forms of the definition and rule laws, towers and the
native Nat operations are not pulled back. That is the level Theorem S is stated at
(`M_S(n) := M.cval (keyName (N n)) (φ ∘ σ_n)`), and the only level at which the pull-back can hold
above a changed definition. The target models quantified over are the same as
`StrongCone.sound`'s (`StrongInstalledModel` of the target fold).

No cone with a changed inductive block, an image recursor or a type row is decided here: their
rows fail the types, capability or recursor checks, which are the existing ones (S+b). -/

namespace Ix.CompileCert

open Kernel.Reader
open Kernel.Admission

/-! ## A definition's value through a theorem row of the target -/

/-- The row alternative for one installed source definition `name := value`, with the
lookups given: the target row named `rows name` is a theorem whose installed statement is
`@Eq.{ℓ} T c r`, `c` the target constant `names name` at its own universe parameters and `r`
the image of `value` (`checkInstalledMemberExprF`, the comparison the definitions check
uses). The row's name is an untrusted proposal; nothing else about it is assumed. -/
def definitionRowF (fS fT : Lookup) (names rows : Kernel.Name → Kernel.Name)
    (name : Kernel.Name) (value : Kernel.Expr) : Bool :=
  match fT (names name), fT (rows name) with
  | some targetEntry, some (.thmInfo row _) =>
    match eqParts row.type with
    | some (_, _, .const left us, right) =>
      decide (left = names name) &&
        decide (us = targetEntry.toConstantVal.levelParams.map Kernel.Level.param) &&
        decide (checkInstalledMemberExprF fS fT names name value right = some true)
    | _ => false
  | _, _ => false

theorem definitionRowF_spec {fS fT : Lookup} {names rows : Kernel.Name → Kernel.Name}
    {name : Kernel.Name} {value : Kernel.Expr} (h : definitionRowF fS fT names rows name value = true) :
    ∃ targetEntry row proof level carrier right,
      fT (names name) = some targetEntry ∧ fT (rows name) = some (.thmInfo row proof) ∧
      row.type = kernelEq level carrier
        (.const (names name) (targetEntry.toConstantVal.levelParams.map Kernel.Level.param)) right ∧
      checkInstalledMemberExprF fS fT names name value right = some true := by
  unfold definitionRowF at h
  cases hT : fT (names name) with
  | none => simp [hT] at h
  | some targetEntry =>
    cases hR : fT (rows name) with
    | none => simp [hT, hR] at h
    | some rowInfo =>
      cases rowInfo with
      | thmInfo row proof =>
        simp only [hT, hR] at h
        cases hp : eqParts row.type with
        | none => simp [hp] at h
        | some parts =>
          obtain ⟨level, carrier, left, right⟩ := parts
          cases left with
          | const leftName us =>
            simp only [hp, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨hl, hu⟩, hc⟩ := h
            subst hl
            subst hu
            exact ⟨targetEntry, row, proof, level, carrier, right, rfl, rfl, eqParts_sound hp, hc⟩
          | bvar _ | fvar _ _ | sort _ | app _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _ | lit _
          | proj _ _ _ => simp [hp] at h
      | axiomInfo _ | defnInfo _ _ _ | recInfo _ _ _ _ | indInfo _ _ | ctorInfo _ _ _ | projInfo _ =>
        simp [hT, hR] at h

/-! ## The definitions check with the row alternative -/

/-- Every installed source definition: the target row of its name is a definition whose value
is the image of the source value (`checkInstalledDefinitions`' comparison), **or** the row
alternative (`definitionRowF`). With the lookups given; `checkInstalledDefinitionsRows` is its
instance at the environments' own lookups. -/
def checkInstalledDefinitionsRowsF (source : Kernel.Env) (fS fT : Lookup)
    (names rows : Kernel.Name → Kernel.Name) : Bool :=
  source.consts.all fun entry =>
    match entry with
    | .defnInfo header value _ =>
      decide (fS header.name = some entry) &&
      ((match fT (names header.name) with
        | some (.defnInfo _ targetValue _) =>
          decide (checkInstalledMemberExprF fS fT names header.name value targetValue = some true)
        | _ => false) ||
        definitionRowF fS fT names rows header.name value)
    | _ => true

/-- The definitions check of the value-level S: `checkInstalledDefinitions` with the row
alternative. -/
def checkInstalledDefinitionsRows (source target : Kernel.Env) (names rows : Kernel.Name → Kernel.Name) : Bool :=
  checkInstalledDefinitionsRowsF source source.find? target.find? names rows

theorem checkInstalledDefinitionsRows_member {source target : Kernel.Env}
    {names rows : Kernel.Name → Kernel.Name}
    (checked : checkInstalledDefinitionsRows source target names rows = true)
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (present : Kernel.ConstantInfo.defnInfo header value hint ∈ source.consts) :
    source.find? header.name = some (.defnInfo header value hint) ∧
    ((∃ targetHeader targetValue targetHint,
        target.find? (names header.name) = some (.defnInfo targetHeader targetValue targetHint) ∧
        checkInstalledMemberExpr source target names header.name value targetValue = some true) ∨
      definitionRowF source.find? target.find? names rows header.name value = true) := by
  unfold checkInstalledDefinitionsRows checkInstalledDefinitionsRowsF at checked
  have row := List.all_eq_true.mp checked (.defnInfo header value hint) present
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at row
  refine ⟨row.1, ?_⟩
  rcases row.2 with direct | viaRow
  · left
    cases lookup : target.find? (names header.name) with
    | none => simp [lookup] at direct
    | some targetEntry =>
      cases targetEntry with
      | defnInfo targetHeader targetValue targetHint =>
        simp only [lookup, decide_eq_true_eq, checkInstalledMemberExprF_env] at direct
        exact ⟨targetHeader, targetValue, targetHint, rfl, direct⟩
      | axiomInfo _ | thmInfo _ _ | recInfo _ _ _ _ | indInfo _ _ | ctorInfo _ _ _ | projInfo _ =>
        simp [lookup] at direct
  · exact .inr viaRow

/-- **Definitions denote their values in the pull-back, through the rows.** For every installed
source definition `c := v` the check accepts, in **every** strong model of the target, `v`
denotes the pulled-back value of `c`: directly (the target definition's value is the image of
`v`, `StrongInstalledModel.definition_values`), or through the row: the target model satisfies
the row's statement `names c = r` (`StrongInstalledModel.theorem_eq`, the certified checker's
soundness for the installed theorem), and `r` is the image of `v`. -/
theorem checkInstalledDefinitionsRows_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names rows : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (checked : checkInstalledDefinitionsRows sourceEnv targetEnv names rows = true)
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (present : Kernel.ConstantInfo.defnInfo header value hint ∈ sourceEnv.consts)
    (levels : Kernel.Name → Nat) (valuation : Nat → V) :
    Kernel.Denotes ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv levels valuation value
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval header.name levels) := by
  obtain ⟨sourceLookup, direct | viaRow⟩ := checkInstalledDefinitionsRows_member checked present
  · obtain ⟨targetHeader, targetValue, targetHint, targetLookup, comparison⟩ := direct
    have image := checkInstalledMemberExpr_sound target association sourceLookup comparison levels
    have targetName : targetHeader.name = names header.name := Kernel.Semantics.Env.find?_name targetLookup
    have read := image.symm.denotes
      (target.definition_values targetHeader targetValue targetHint
        (Kernel.Semantics.Env.find?_mem targetLookup)
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels header.name levels) valuation)
    rw [targetName] at read
    exact read
  · obtain ⟨targetEntry, row, proof, level, carrier, right, targetLookup, rowLookup, rowType, comparison⟩ :=
      definitionRowF_spec viaRow
    rw [checkInstalledMemberExprF_env] at comparison
    have image := checkInstalledMemberExpr_sound target association sourceLookup comparison levels
    have rowPresent := Kernel.Semantics.Env.find?_mem rowLookup
    obtain ⟨type, typeRead, _⟩ := target.public.mem _ rowPresent
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels header.name levels) valuation
    change Kernel.Denotes _ _ _ _ row.type _ at typeRead
    rw [rowType] at typeRead
    unfold kernelEq at typeRead
    cases typeRead with
    | app prefixRead rightRead =>
      cases prefixRead with
      | app headRead leftRead =>
        have equal := target.theorem_eq row proof rowPresent
          (by rw [rowType]; exact InstalledTelescope.nil) leftRead rightRead
        have self := denotes_self_instance (values := target.public.cval) (ρ := valuation)
          (levels := (PullbackMap.fromEnvs sourceEnv targetEnv names).levels header.name levels) targetLookup
        have leftValue := Kernel.Denotes_functional leftRead self
        have read := image.symm.denotes rightRead
        rw [← equal, leftValue] at read
        exact read

/-! ## The value-level association -/

/-- The value-level installed association with the row alternative for definitions: the
Boolean part of `checkInstalledAssociation` (telescopes, types, definitions, the `False`/`Eq`
pins, capabilities, recursors, constructors), its eta associations and rule level links, with
`checkInstalledDefinitionsRows` in place of `checkInstalledDefinitions`. The availability pass
(which tells an unavailable comparison from a refusal and is discarded by every proof) is not
part of it. -/
def checkChangedAssociation (source target : Kernel.Env) (names rows : Kernel.Name → Kernel.Name) : Bool :=
  checkTelescopes source target names && checkInstalledTypes source target names &&
    checkInstalledDefinitionsRows source target names rows &&
    checkInstalledPin source names Kernel.falseName 0 && checkInstalledPin source names Kernel.eqName 1 &&
    checkInstalledCapabilities source target names && checkInstalledRecursors source target names &&
    checkInstalledConstructors source target names &&
    decide (checkInstalledEtaAssociations source target names = some true) &&
    decide (checkInstalledRuleLevelLinks source target names = some true)

/-- `checkChangedAssociation` on the index and the DAG (WP-F's lookup-parameterised checks at
IxC's name index, one index per environment). -/
def checkChangedAssociationF (source target : Kernel.Env) (names rows : Kernel.Name → Kernel.Name) : Bool :=
  let fS := envFind source
  let fT := envFind target
  checkTelescopesF source fT names && checkInstalledTypesF source fS fT names &&
    checkInstalledDefinitionsRowsF source fS fT names rows &&
    checkInstalledPin source names Kernel.falseName 0 && checkInstalledPin source names Kernel.eqName 1 &&
    checkInstalledCapabilitiesF source fS fT names && checkInstalledRecursorsF source fS fT names &&
    checkInstalledConstructorsF source fS fT names &&
    decide (checkInstalledEtaAssociationsF source fS fT names = some true) &&
    decide (checkInstalledRuleLevelLinksF source fS fT names = some true)

theorem checkChangedAssociationF_eq (source target : Kernel.Env) (names rows : Kernel.Name → Kernel.Name) :
    checkChangedAssociationF source target names rows = checkChangedAssociation source target names rows := by
  simp only [checkChangedAssociationF, checkChangedAssociation, envFind_eq, checkTelescopesF_env,
    checkInstalledTypesF_env, checkInstalledCapabilitiesF_env, checkInstalledRecursorsF_env,
    checkInstalledConstructorsF_env, checkInstalledEtaAssociationsF_env, checkInstalledRuleLevelLinksF_env]
  rfl

/-- **The value-level pull-back.** An accepted `checkChangedAssociation` between an installed
source (with a well-formed environment, e.g. from its own verified fold) and a target gives,
for **every** strong model of the target, a public value model of the source whose values are
the pull-back of the target's under the name map, with the public capability laws and the
universal rule simulation. -/
theorem checkedChangedAssociation_values {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceWf : Kernel.EnvWF sourceEnv)
    {names rows : Kernel.Name → Kernel.Name}
    (checked : checkChangedAssociation sourceEnv targetEnv names rows = true)
    (target : StrongInstalledModel V targetEnv) :
    ∃ source : PublicValueModel V sourceEnv,
      source.model.cval = (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval ∧
      PublicCapabilityLaws source.model.cval sourceEnv ∧ UniversalRuleSimulation target sourceEnv names := by
  simp only [checkChangedAssociation, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨telescopes, types⟩, definitions⟩, falsePin⟩, eqPin⟩, capabilities⟩, recursors⟩,
    constructors⟩, eta⟩, links⟩ := checked
  have association := checkTelescopes_sound telescopes
  have typeEvidence := checkedPullbackTypes target telescopes types falsePin eqPin
  let source : PublicValueModel V sourceEnv :=
    { model := typeEvidence.model
      parameters := fun _ _ lookup first second agree =>
        (PullbackMap.fromEnvs sourceEnv targetEnv names).values_params target
          (PullbackMap.fromEnvs_locality association) lookup first second agree
      definitions := fun _ _ _ present levels valuation =>
        checkInstalledDefinitionsRows_sound target association definitions present levels valuation }
  exact ⟨source, rfl, checkedCapabilities_publicLaws sourceWf target association types capabilities eta,
    checked_universal_rules sourceWf target association types recursors constructors links⟩

/-! ## The name map against W+'s association -/

/-- `SemanticNamesAgree` for W+'s association: the semantic name map agrees, for every source
declaration, with the accepted export map (image claims included). -/
def SemanticNamesAgree' {input : Input} {images : Lean.Name → Bool} {support : Array Kernel.Declaration}
    (accepted : AcceptedAssociation' input images support) (names : Kernel.Name → Kernel.Name) : Prop :=
  ∀ entry ∈ input.source.declarations,
    NameAgrees ⟨input.source, input.map, accepted.pins, images⟩ entry.name (names (sourceName entry.name))

/-- `SemanticNamesAgree'` decided with the source and the map indexed (as `semanticNamesFast`). -/
def semanticNamesFast' {input : Input} {images : Lean.Name → Bool} {support : Array Kernel.Declaration}
    (accepted : AcceptedAssociation' input images support) (names : Kernel.Name → Kernel.Name) : Bool :=
  let sIdx := sourceIndex input.source
  let mIdx := mapIndex input.map
  input.source.declarations.all fun entry =>
    match contextNameL (fun n => sIdx[n]?) (fun n => mIdx[n]?) accepted.pins images entry.name with
    | .error _ => false
    | .ok actual => decide (actual = names (sourceName entry.name))

theorem semanticNamesFast'_iff {input : Input} {images : Lean.Name → Bool} {support : Array Kernel.Declaration}
    (accepted : AcceptedAssociation' input images support) (names : Kernel.Name → Kernel.Name) :
    semanticNamesFast' accepted names = true ↔ SemanticNamesAgree' accepted names := by
  have hs : (fun n => (sourceIndex input.source)[n]?) = input.source.find := sourceIndex_find input.source
  have hm : (fun n => (mapIndex input.map)[n]?) = input.map.find := funext (mapIndex_get input.map)
  simp only [semanticNamesFast', hs, hm, List.all_eq_true]
  rw [show contextNameL input.source.find input.map.find accepted.pins images =
    (⟨input.source, input.map, accepted.pins, images⟩ : ExportContext).name from rfl]
  unfold SemanticNamesAgree' NameAgrees
  constructor
  · intro h entry hentry
    have row := h entry hentry
    split at row
    · contradiction
    · rename_i actual hact
      rw [hact]
      exact of_decide_eq_true row
  · intro h entry hentry
    have row := h entry hentry
    split
    · rename_i e he
      rw [he] at row
      exact row.elim
    · rename_i actual hact
      rw [hact] at row
      exact decide_eq_true row

/-! ## The cone, its decision and what an S-Certified verdict means -/

/-- Everything value-level S takes for one input whose W association is W+'s: the association
(the artifact admitted, the support folded on top of it, W+'s correspondences), the normalised
source installation, the name map and the row names (untrusted proposals), and the two accepted
checks. -/
structure StrongCone' (input : Input) (images : Lean.Name → Bool) (support : Array Kernel.Declaration) where
  accepted : AcceptedAssociation' input images support
  installed : SourceNormalizedInstallation input.source input.roots
  names : Kernel.Name → Kernel.Name
  rows : Kernel.Name → Kernel.Name
  names_agree : SemanticNamesAgree' accepted names
  checked : checkChangedAssociation installed.env accepted.folded.env names rows = true

/-- The untrusted part of a value-level cone: the name map and, per source definition, the name
of the target theorem row proposed for it. -/
structure StrongProposal' where
  names : Kernel.Name → Kernel.Name
  rows : Kernel.Name → Kernel.Name

inductive StrongDecline' where
  /-- The name map disagrees with W+'s export map. -/
  | names
  /-- The value-level association refused. -/
  | check

/-- The decision: the two checks, decided through the indices; success is exactly the premises
of `StrongCone'.sound`. -/
def decideStrongCone' {input : Input} {images : Lean.Name → Bool} {support : Array Kernel.Declaration}
    (accepted : AcceptedAssociation' input images support)
    (installed : SourceNormalizedInstallation input.source input.roots) (proposal : StrongProposal') :
    Except StrongDecline' (StrongCone' input images support) :=
  if hn : semanticNamesFast' accepted proposal.names = true then
    if hc : checkChangedAssociationF installed.env accepted.folded.env proposal.names proposal.rows = true then
      .ok { accepted, installed, names := proposal.names, rows := proposal.rows
            names_agree := (semanticNamesFast'_iff accepted proposal.names).mp hn
            checked := (checkChangedAssociationF_eq _ _ _ _).symm.trans hc }
    else .error .check
  else .error .names

/-- **What a value-level S-Certified verdict implies** (M7 S+a). For a cone the certifier
accepted with `decideStrongCone'`: W+'s conclusion for its input (`checkIndexed'_sound`'s: the
exact bytes admitted, the support folded by the certified checker on top of them, the closed
domain, the map with its image claims, every source declaration matched directly, through its
raw record, as a theorem by statement or by its equations, every block whole or changed, the
definition groups covered); the name map agrees with W+'s; the installed source's own fold; and
for **every** strong model of the target (the fold of the admitted artifact and the support) a
public value model of the installed source whose values are the target's pulled back under the
name map (Theorem S's `M_S`: membership, `False` empty, `Eq` equality, definitions denote
their values, here through the rows for the changed ones), with the public capability laws and
the universal rule simulation; and every original declaration installed as its export or through
a lowering receipt. The changed definitions' rows are W+'s: `StrongCone'.row_equations` states
that they hold in every strong model of this same target. -/
theorem StrongCone'.sound (V : Type u) [Kernel.SetTheory V] {input : Input} {images : Lean.Name → Bool}
    {support : Array Kernel.Declaration} (cone : StrongCone' input images support) :
    (checkBytes input.limits input.records input.blobs input.hint = .ok cone.accepted.env ∧
      Kernel.Cached.checkDecls .verified cone.accepted.folded.pins
        (Kernel.Frontend.preparePrelude cone.accepted.prelude.ix cone.accepted.declarations ++ support) =
          .ok cone.accepted.folded.env ∧
      DirectDomain input.source input.roots input.map ∧
      MapAgrees ⟨input.source, input.map, cone.accepted.pins, images⟩
        (streamContext cone.accepted.pins cone.accepted.prelude cone.accepted.constants input.blobs input.hint) ∧
      SourceCorrespondence' ⟨input.source, input.map, cone.accepted.pins, images⟩
        (streamContext cone.accepted.pins cone.accepted.prelude cone.accepted.constants input.blobs input.hint)
        cone.accepted.constants cone.accepted.declarations
        (streamEntries (cone.accepted.declarations ++ support)) ∧
      BlockCorrespondence' ⟨input.source, input.map, cone.accepted.pins, images⟩ cone.accepted.readerState ∧
      DefinitionGroupsCovered ⟨input.source, input.map, cone.accepted.pins, images⟩ cone.accepted.constants) ∧
    SemanticNamesAgree' cone.accepted cone.names ∧
      Kernel.Cached.checkDecls .verified cone.installed.pins cone.installed.declarations.toArray =
        .ok cone.installed.env ∧
      Nonempty (StrongInstalledModel V cone.installed.env) ∧
      Nonempty (StrongInstalledModel V cone.accepted.folded.env) ∧
      (∀ target : StrongInstalledModel V cone.accepted.folded.env,
       ∃ source : PublicValueModel V cone.installed.env,
        source.model.cval =
          (PullbackMap.fromEnvs cone.installed.env cone.accepted.folded.env cone.names).values
            target.public.cval ∧
        PublicCapabilityLaws source.model.cval cone.installed.env ∧
        UniversalRuleSimulation target cone.installed.env cone.names) ∧
      ∀ ci ∈ input.source.declarations, ∃ entry declaration,
        exportSourceEntry ci = .ok entry ∧ entry ∈ readerEntries declaration ∧
        (declaration ∈ cone.installed.declarations ∨ ∃ replacement,
          Nonempty (SourceProjectionLowering input.source cone.installed.witnesses declaration replacement) ∧
          replacement ∈ cone.installed.declarations) := by
  obtain ⟨sourceStrong⟩ := cone.installed.strong_model V
  refine ⟨⟨cone.accepted.admitted, cone.accepted.folded.checked, cone.accepted.domain,
      cone.accepted.map_agrees, cone.accepted.correspondence, cone.accepted.block_correspondence,
      cone.accepted.definition_groups⟩,
    cone.names_agree, cone.installed.checked, ⟨sourceStrong⟩,
    strongInstalledModel_exists V cone.accepted.folded.pins _ _ cone.accepted.folded.checked,
    fun target => checkedChangedAssociation_values sourceStrong.internal.base2.wf cone.checked target, ?_⟩
  intro ci present
  obtain ⟨entry, declaration, exported, member, rest⟩ := cone.installed.member present
  refine ⟨entry, declaration, exported, member, ?_⟩
  rcases rest with same | ⟨replacement, _, _, _, lowering, hr, _⟩ | ⟨replacement, _, lowering, hr⟩
  · exact .inl same
  · exact .inr ⟨replacement, lowering, hr⟩
  · exact .inr ⟨replacement, lowering, hr⟩

/-- **The rows of a value-level cone hold in its target.** W+'s `model_equations` for the cone:
a source declaration matched by its equations has a reader definition entry whose type denotes
Lean's, and each of its defining equations (a definition's `c = value`, from the `rfl` or value
row the definitions check read) is installed by the certified fold of the artifact and the
support and holds in every strong model of it, the environment `StrongCone'.sound` quantifies
over. -/
theorem StrongCone'.row_equations.{v} {input : Input} {images : Lean.Name → Bool}
    {support : Array Kernel.Declaration} (cone : StrongCone' input images support) {ci : Lean.ConstantInfo}
    (equations : EquationMatch ⟨input.source, input.map, cone.accepted.pins, images⟩
      (streamEntries cone.accepted.declarations) (streamEntries (cone.accepted.declarations ++ support)) ci) :
    ∃ header, directHeader ⟨input.source, input.map, cone.accepted.pins, images⟩ ci = .ok header ∧
      (∃ type value hint,
        DirectEntry.defn ⟨header.name, header.levelParams, type⟩ value hint ∈
          streamEntries cone.accepted.declarations ∧
        TypeHolds.{v} cone.accepted.folded.env header.levelParams type header.type) ∧
      match ci with
      | .recInfo r =>
        ∃ statements, ruleStatements ⟨input.source, input.map, cone.accepted.pins, images⟩ r = .ok statements ∧
          statements.length = r.rules.length ∧
          ∀ s ∈ statements, EquationHolds.{v} cone.accepted.folded.env header.levelParams s
      | .defnInfo d =>
        (∃ left right level,
          definitionSides ⟨input.source, input.map, cone.accepted.pins, images⟩ d header.levelParams =
            .ok (left, right) ∧
          EquationHolds.{v} cone.accepted.folded.env header.levelParams (kernelEq level header.type left right)) ∨
        (∃ t eqHeader, input.source.find (d.name.str "eq_def") = some (.thmInfo t) ∧
          directHeader ⟨input.source, input.map, cone.accepted.pins, images⟩ (.thmInfo t) = .ok eqHeader ∧
          eqLeftHead eqHeader.type = some header.name ∧
          EquationHolds.{v} cone.accepted.folded.env eqHeader.levelParams eqHeader.type)
      | _ => False := by
  have holds := AcceptedAssociation'.model_equations.{v} cone.accepted equations
  cases ci <;> exact holds

/-- The decision's success gives the value-level conclusion for the cone it returns, built from
the given association and installation. -/
theorem decideStrongCone'_sound (V : Type u) [Kernel.SetTheory V] {input : Input}
    {images : Lean.Name → Bool} {support : Array Kernel.Declaration}
    {accepted : AcceptedAssociation' input images support}
    {installed : SourceNormalizedInstallation input.source input.roots} {proposal : StrongProposal'}
    {cone : StrongCone' input images support} (h : decideStrongCone' accepted installed proposal = .ok cone) :
    cone.accepted = accepted ∧ cone.installed = installed ∧
      Nonempty (StrongInstalledModel V cone.accepted.folded.env) ∧
      ∀ target : StrongInstalledModel V cone.accepted.folded.env,
       ∃ source : PublicValueModel V cone.installed.env,
        source.model.cval =
          (PullbackMap.fromEnvs cone.installed.env cone.accepted.folded.env cone.names).values
            target.public.cval ∧
        PublicCapabilityLaws source.model.cval cone.installed.env ∧
        UniversalRuleSimulation target cone.installed.env cone.names := by
  obtain ⟨_, _, _, _, model, all, _⟩ := StrongCone'.sound V cone
  refine ⟨?_, ?_, model, all⟩
  all_goals
    unfold decideStrongCone' at h
    split at h
    · split at h
      · cases h; rfl
      · contradiction
    · contradiction

end Ix.CompileCert
