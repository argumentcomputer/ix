import Ix.CompileCert.Domain
import Ix.Kernel.Admission.Theorems

/-! # Admission-connected direct-cone certification

The executable reads and admits the exact bytes before comparing an
independent source export against the reader stream. Its result carries
proofs of the checks actually performed. No producer-supplied proposition,
Boolean verdict, or `Named.original` field is accepted as correspondence.

This is the strict direct-syntax foundation of C1, not completed W: projection
normalization, compatible hint merging, source-block shape/order fidelity,
and complete source/export refinement still require their stated extensions.
-/

namespace Ix.CompileCert

open Kernel.Reader
open Kernel.Admission

structure Input where
  source : Source
  roots : List Lean.Name
  map : SourceMap
  limits : Limits
  records : Records
  blobs : Kernel.Ingress.Blobs
  hint : Kernel.ConstRef Address → Option Kernel.ReducibilityHint := fun _ => none

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

def MapAgrees (cx : ExportContext) (reader : Ctx) : Prop :=
  ∀ e ∈ cx.map,
    resolve reader.store e.record = some e.target ∧
    NameAgrees cx e.source (reader.nameOf e.target)

instance (cx : ExportContext) (reader : Ctx) : Decidable (MapAgrees cx reader) :=
  inferInstanceAs (Decidable (∀ e ∈ cx.map,
    resolve reader.store e.record = some e.target ∧
    NameAgrees cx e.source (reader.nameOf e.target)))

/-- Precise direct-cone relation. Reader declarations are deliberately kept
separate from the installed `env`: binder annotations/lets may change there. -/
structure AcceptedAssociation (input : Input) where
  env : Kernel.Env
  admitted : checkBytes input.limits input.records input.blobs input.hint = .ok env
  domain : DirectDomain input.source input.roots input.map
  pins : Pins
  pins_valid : defaultPins = .ok pins
  prelude : Prelude
  prelude_valid : builtinPrelude = .ok prelude
  constants : List (Address × Ixon.Constant)
  decoded : decodeRecords input.limits input.records = .ok constants
  declarations : Array Kernel.Declaration
  reading : readStream pins prelude constants input.blobs input.hint = .ok declarations
  map_agrees : MapAgrees ⟨input.source, input.map, pins⟩
    (streamContext pins prelude constants input.blobs input.hint)
  correspondence : DirectCorrespondence ⟨input.source, input.map, pins⟩ declarations

inductive Decline where
  | admission (error : Kernel.Admission.Error)
  | sourceDomain
  | setup (reason : String)
  | decoding (error : ByteError)
  | reading (error : Kernel.Admission.Error)
  | mapMismatch
  | correspondence

/-- The runtime checks are the constructors' proof premises, not assumptions
supplied by the caller. Structural equality decisions are kernel-checked. -/
def checkCompiled (input : Input) : Except Decline (AcceptedAssociation input) :=
  match ha : checkBytes input.limits input.records input.blobs input.hint with
  | .error e => .error (.admission e)
  | .ok env =>
    if hd : DirectDomain input.source input.roots input.map then
      match hp : defaultPins with
      | .error e => .error (.setup e)
      | .ok pins =>
        match hq : builtinPrelude with
        | .error e => .error (.setup e)
        | .ok pre =>
          match hc : decodeRecords input.limits input.records with
          | .error e => .error (.decoding e)
          | .ok constants =>
            match hr : readStream pins pre constants input.blobs input.hint with
            | .error e => .error (.reading e)
            | .ok decls =>
              let cx : ExportContext := ⟨input.source, input.map, pins⟩
              if hm : MapAgrees cx (streamContext pins pre constants input.blobs input.hint) then
                if hf : DirectCorrespondence cx decls then
                  .ok ⟨env, ha, hd, pins, hp, pre, hq, constants, hc, decls, hr, hm, hf⟩
                else .error .correspondence
              else .error .mapMismatch
    else .error .sourceDomain

/-- Executable success entails actual admission and every finite source
declaration's independent direct correspondence in the exact reader stream. -/
theorem faithful_sound {input : Input} {accepted : AcceptedAssociation input}
    (_h : checkCompiled input = .ok accepted) :
    checkBytes input.limits input.records input.blobs input.hint = .ok accepted.env ∧
    DirectDomain input.source input.roots input.map ∧
    DirectCorrespondence ⟨input.source, input.map, accepted.pins⟩ accepted.declarations :=
  ⟨accepted.admitted, accepted.domain, accepted.correspondence⟩

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

end Ix.CompileCert
