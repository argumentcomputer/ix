import Ix.CompileCert.StrongEntry
import Ix.CompileCert.StrongFast

/-! # S per cone: the strong-model endpoint as the certifier decides it

The certifier (`compile-certify --strong`, `Ix/CompileCert/StrongCertifier.lean`)
decides the strong-model endpoint S on one *cone* at a time: an `Input` whose
source is a root's closed dependency cone and whose records are the records
that cone's names reach. For such an input it builds, itself, everything
`SourceNormalizedInstallation.artifact_strong_model` takes: the W association
(`AcceptedAssociation`), the normalised source installation with its
Lean-kernel-checked projection-lowering witnesses, the name map with the helper
and basis bindings, the support declarations and the Nat/DivMod/reduce receipt
names. A `StrongCone input` packages them with the accepted strong check.

This module holds what is *proved*:

* `SourceNormalizedInstallation.artifact_strong_model_all`: S restated for
  **every** strong target model (KB's endpoint states `∃ targetModel`; the
  universal form follows from `checkedStrongAssociation`, which already
  quantifies every source and target model).
* `StrongCone.sound`: what an S-Certified verdict means. Every S-Certified
  constant is a member of `input.source` for some `cone : StrongCone input`, and
  then W's conclusion holds for the input (exact admitted bytes, closed source,
  direct correspondence, blocks, definition groups) and S's conclusion holds:
  for every strong target model of the admitted artifact plus its checked
  support there is a strong model of the installed (normalised) source whose
  annotations and values are the pull-back of the target's under the name map,
  and every original Lean declaration is installed as its exact export or
  through a lowering receipt.
* `decideStrongCone`: the decision that builds a `StrongCone` from an accepted
  association, an installation and an untrusted proposal (names, support,
  receipt names). Nothing in the proposal is trusted: names are checked by
  `SemanticNamesAgree` and the installed association, support by the verified
  fold (`checkAdmittedSupport`), receipts by the receipt checks.
-/

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics
open Kernel.Reader
open Kernel.Admission

/-- **S for every strong target model.** The conclusion of
`SourceNormalizedInstallation.artifact_strong_model` with the target model
universally quantified: whatever strong model the admitted artifact and its
checked support are given, the installed source has a strong model that is its
pull-back. The target environment has a strong model (`AdmittedSupport.strong_model`),
so the universal statement is not vacuous. -/
theorem SourceNormalizedInstallation.artifact_strong_model_all (V : Type u) [Kernel.SetTheory V]
    {input : Input} (installed : SourceNormalizedInstallation input.source input.roots)
    (accepted : AcceptedAssociation input) {support : Array Kernel.Declaration}
    (bundle : AdmittedSupport accepted.toAdmittedArtifact support)
    (names certificates operationCertificates elementCertificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level)
    (checked : checkNormalizedArtifactStrongAssociation accepted bundle installed names certificates
      operationCertificates elementCertificates levels = some true) :
    SemanticNamesAgree accepted names ∧
      Kernel.Cached.checkDecls .verified installed.pins installed.declarations.toArray = .ok installed.env ∧
      Nonempty (StrongInstalledModel V bundle.env) ∧
      (∀ targetModel : StrongInstalledModel V bundle.env,
       ∃ sourceModel : StrongInstalledModel V installed.env,
        sourceModel.internal.base2.acval = (PullbackMap.fromEnvs installed.env bundle.env names).annotations
          targetModel.internal.base2.acval ∧
        sourceModel.public.cval = (PullbackMap.fromEnvs installed.env bundle.env names).values
          targetModel.public.cval) ∧
      ∀ ci ∈ input.source.declarations, ∃ entry declaration,
        exportSourceEntry ci = .ok entry ∧ entry ∈ readerEntries declaration ∧
        (declaration ∈ installed.declarations ∨ ∃ replacement,
          Nonempty (SourceProjectionLowering input.source installed.witnesses declaration replacement) ∧
          replacement ∈ installed.declarations) := by
  obtain ⟨names_agree, folded, _, members⟩ :=
    installed.artifact_strong_model V accepted bundle names certificates operationCertificates
      elementCertificates levels checked
  obtain ⟨_, strongCheck⟩ := bothChecks_true checked
  obtain ⟨sourceModel⟩ := installed.strong_model V
  refine ⟨names_agree, folded, bundle.strong_model V, ?_, members⟩
  intro targetModel
  exact checkedStrongAssociation sourceModel targetModel strongCheck

/-- Support for a cone that needs none: the admitted artifact's own verified
fold is reused (`AdmittedArtifact.checked_declarations`), so no second fold
of the target runs. Only row preservation (trivial for the same environment
up to name uniqueness) is decided. -/
def admittedSupportEmpty {input : ArtifactInput} (artifact : AdmittedArtifact input) :
    Except SupportError (AdmittedSupport artifact #[]) :=
  match hp : builtinNatOpPins with
  | .error reason => .error (.setup reason)
  | .ok pins =>
    if rows : InstalledRowsPreserved artifact.env artifact.env then
      .ok { fresh := by simp [SupportFresh]
            pins
            pins_checked := hp
            env := artifact.env
            checked := by
              obtain ⟨natPins, hn, hc⟩ := artifact.checked_declarations
              have same : natPins = pins := Except.ok.inj (hn.symm.trans hp)
              subst same
              simpa using hc
            original_rows := rows }
    else .error .changedOriginal

/-- Admit the proposed support: the empty support reuses the artifact's fold,
any other runs `checkAdmittedSupport` (freshness, the verified fold over the
artifact's declarations and the support, row preservation). -/
def admitSupport {input : ArtifactInput} (artifact : AdmittedArtifact input)
    (support : Array Kernel.Declaration) : Except SupportError (AdmittedSupport artifact support) :=
  if h : support = #[] then by subst h; exact admittedSupportEmpty artifact
  else checkAdmittedSupport artifact support

/-- Everything the S endpoint takes, for one input, with the accepted check. -/
structure StrongCone (input : Input) where
  accepted : AcceptedAssociation input
  installed : SourceNormalizedInstallation input.source input.roots
  support : Array Kernel.Declaration
  bundle : AdmittedSupport accepted.toAdmittedArtifact support
  names : Kernel.Name → Kernel.Name
  certificates : Kernel.Name → Kernel.Name
  operationCertificates : Kernel.Name → Kernel.Name
  elementCertificates : Kernel.Name → Kernel.Name
  levels : Kernel.Name → Kernel.Level
  checked : checkNormalizedArtifactStrongAssociation accepted bundle installed names certificates
    operationCertificates elementCertificates levels = some true

/-- The untrusted part of a cone: what the certifier proposes. -/
structure StrongProposal where
  names : Kernel.Name → Kernel.Name
  support : Array Kernel.Declaration
  certificates : Kernel.Name → Kernel.Name
  operationCertificates : Kernel.Name → Kernel.Name
  elementCertificates : Kernel.Name → Kernel.Name
  levels : Kernel.Name → Kernel.Level

inductive StrongDecline where
  /-- The proposed support was refused (not fresh, the fold refused it, rows changed). -/
  | support (error : SupportError)
  /-- The strong association check refused (`some false`) or could not compare (`none`). -/
  | strong (result : Option Bool)

/-- The decision. Success is exactly the premises of
`SourceNormalizedInstallation.artifact_strong_model`; the proposal only
supplies the arguments the checks quantify. -/
def decideStrongCone {input : Input} (accepted : AcceptedAssociation input)
    (installed : SourceNormalizedInstallation input.source input.roots) (proposal : StrongProposal) :
    Except StrongDecline (StrongCone input) :=
  match admitSupport accepted.toAdmittedArtifact proposal.support with
  | .error e => .error (.support e)
  | .ok bundle =>
    match hc : checkNormalizedArtifactStrongAssociation accepted bundle installed proposal.names
        proposal.certificates proposal.operationCertificates proposal.elementCertificates proposal.levels with
    | some true => .ok ⟨accepted, installed, proposal.support, bundle, proposal.names, proposal.certificates,
        proposal.operationCertificates, proposal.elementCertificates, proposal.levels, hc⟩
    | result => .error (.strong result)

/-- **What an S-Certified verdict implies.** For a cone the certifier accepted:
W's conclusion for its input (the fields of `AcceptedAssociation`, i.e. the
conclusion of `faithful_sound`/`checkIndexed_sound`) and S's conclusion
(`artifact_strong_model_all`) for every strong target model. -/
theorem StrongCone.sound (V : Type u) [Kernel.SetTheory V] {input : Input} (cone : StrongCone input) :
    (checkBytes input.limits input.records input.blobs input.hint = .ok cone.accepted.env ∧
      DirectDomain input.source input.roots input.map ∧
      SourceCorrespondence ⟨input.source, input.map, cone.accepted.pins, noImages⟩
        (Kernel.Admission.streamContext cone.accepted.pins cone.accepted.prelude cone.accepted.constants
          input.blobs input.hint) cone.accepted.constants cone.accepted.declarations ∧
      BlockCorrespondence ⟨input.source, input.map, cone.accepted.pins, noImages⟩ cone.accepted.readerState ∧
      DefinitionGroupsCovered ⟨input.source, input.map, cone.accepted.pins, noImages⟩ cone.accepted.constants) ∧
    SemanticNamesAgree cone.accepted cone.names ∧
      Kernel.Cached.checkDecls .verified cone.installed.pins cone.installed.declarations.toArray = .ok cone.installed.env ∧
      Nonempty (StrongInstalledModel V cone.bundle.env) ∧
      (∀ targetModel : StrongInstalledModel V cone.bundle.env,
       ∃ sourceModel : StrongInstalledModel V cone.installed.env,
        sourceModel.internal.base2.acval =
          (PullbackMap.fromEnvs cone.installed.env cone.bundle.env cone.names).annotations
            targetModel.internal.base2.acval ∧
        sourceModel.public.cval =
          (PullbackMap.fromEnvs cone.installed.env cone.bundle.env cone.names).values
            targetModel.public.cval) ∧
      ∀ ci ∈ input.source.declarations, ∃ entry declaration,
        exportSourceEntry ci = .ok entry ∧ entry ∈ readerEntries declaration ∧
        (declaration ∈ cone.installed.declarations ∨ ∃ replacement,
          Nonempty (SourceProjectionLowering input.source cone.installed.witnesses declaration replacement) ∧
          replacement ∈ cone.installed.declarations) :=
  ⟨⟨cone.accepted.admitted, cone.accepted.domain, cone.accepted.correspondence,
    cone.accepted.block_correspondence, cone.accepted.definition_groups⟩,
   cone.installed.artifact_strong_model_all V cone.accepted cone.bundle cone.names cone.certificates
    cone.operationCertificates cone.elementCertificates cone.levels cone.checked⟩

/-- The decision's success gives `StrongCone.sound` for the cone it returns. -/
theorem decideStrongCone_sound (V : Type u) [Kernel.SetTheory V] {input : Input}
    {accepted : AcceptedAssociation input}
    {installed : SourceNormalizedInstallation input.source input.roots} {proposal : StrongProposal}
    {cone : StrongCone input} (_h : decideStrongCone accepted installed proposal = .ok cone) :
    cone.accepted = accepted ∧ cone.installed = installed ∧
      Nonempty (StrongInstalledModel V cone.bundle.env) ∧
      ∀ targetModel : StrongInstalledModel V cone.bundle.env,
       ∃ sourceModel : StrongInstalledModel V cone.installed.env,
        sourceModel.internal.base2.acval =
          (PullbackMap.fromEnvs cone.installed.env cone.bundle.env cone.names).annotations
            targetModel.internal.base2.acval ∧
        sourceModel.public.cval =
          (PullbackMap.fromEnvs cone.installed.env cone.bundle.env cone.names).values
            targetModel.public.cval := by
  obtain ⟨_, _, model, all, _⟩ := (StrongCone.sound V cone).2
  refine ⟨?_, ?_, model, all⟩
  all_goals
    unfold decideStrongCone at _h
    split at _h
    · contradiction
    · split at _h
      · cases _h; rfl
      · contradiction

end Ix.CompileCert
