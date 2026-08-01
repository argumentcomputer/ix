import Ix.Tc.Verify.Driver.Enumeration
import Ix.Tc.Verify.Driver.Serial
import Ix.Tc.Verify.Whnf.Runtime.LazyIngress

/-!
# Serialized Ixon representation correspondence

This module states the representation boundary between Ixon bytes and the
anonymous kernel model.  `Ixon.deEnv` is the pure Lean reference decoder: a
successful run has already traversed the wire format and checked constant
hashes, blob hashes, the canonical constant Merkle root, sorted table keys,
the optional main pointer, and trailing-byte exhaustion.  The predicates
below retain the resulting facts in the exact form consumed by ingress.

The mmap-backed Rust decoder `Ixon.deEnvAnon` is intentionally not equated to
the pure decoder here.  That implementation/refinement result belongs to the
later Rust transport phase; T0 reasons from the pure decoder and the actual
Lean eager/lazy ingress functions.
-/

namespace Ix.Tc

namespace IxonEnv

/-- Anonymous checking erases source names, reverse-name indices, named
metadata, and commitments.  Constants, literal blobs, anonymous reducibility
hints, the bundle root, and explicit assumptions are semantic input and are
preserved. -/
def eraseAnonMetadata (env : Ixon.Env) : Ixon.Env :=
  { env with named := {}, names := {}, comms := {}, addrToName := {} }

@[simp] theorem eraseAnonMetadata_consts (env : Ixon.Env) :
    (eraseAnonMetadata env).consts = env.consts := rfl

@[simp] theorem eraseAnonMetadata_blobs (env : Ixon.Env) :
    (eraseAnonMetadata env).blobs = env.blobs := rfl

@[simp] theorem eraseAnonMetadata_hints (env : Ixon.Env) :
    (eraseAnonMetadata env).anonHints = env.anonHints := rfl

@[simp] theorem eraseAnonMetadata_main (env : Ixon.Env) :
    (eraseAnonMetadata env).main = env.main := rfl

@[simp] theorem eraseAnonMetadata_assumptions (env : Ixon.Env) :
    (eraseAnonMetadata env).assumptions = env.assumptions := rfl

@[simp] theorem eraseAnonMetadata_named (env : Ixon.Env) :
    (eraseAnonMetadata env).named = {} := rfl

@[simp] theorem eraseAnonMetadata_names (env : Ixon.Env) :
    (eraseAnonMetadata env).names = {} := rfl

@[simp] theorem eraseAnonMetadata_comms (env : Ixon.Env) :
    (eraseAnonMetadata env).comms = {} := rfl

@[simp] theorem eraseAnonMetadata_addrToName (env : Ixon.Env) :
    (eraseAnonMetadata env).addrToName = {} := rfl

/-- Every stored constant body commits to the map key under which ingress
will request it.  This is byte equality at the Ixon layer, before conversion
to a `KConst`; it does not assert hash injectivity. -/
def ConstAddressIntegrity (env : Ixon.Env) : Prop :=
  ∀ {addr lazy}, env.consts.get? addr = some lazy →
    Address.blake3 lazy.rawBytes = addr

/-- Every constant entry materializes successfully.  The pure decoder
provides cached parsed constants; mmap-backed environments establish the
same property only for entries reached by a successful lazy parse. -/
def ConstMaterializationIntegrity (env : Ixon.Env) : Prop :=
  ∀ {addr lazy}, env.consts.get? addr = some lazy →
    ∃ constant, lazy.get = .ok constant

/-- Literal data is separately content-addressed because the constants
Merkle root does not cover blob bytes. -/
def BlobAddressIntegrity (env : Ixon.Env) : Prop :=
  ∀ {addr bytes}, env.blobs.get? addr = some bytes →
    Address.blake3 bytes = addr

/-- Representation facts consumed by anonymous work enumeration and ingress.
Projection-address completeness is carried by `source`: every generated
IPrj/CPrj/RPrj/DPrj address must exist and point back to its owning Muts
block. -/
structure RepresentationWF (env : Ixon.Env) : Prop where
  constAddresses : ConstAddressIntegrity env
  constMaterialization : ConstMaterializationIntegrity env
  blobAddresses : BlobAddressIntegrity env
  source : AnonWorkEnvWF env
  blockOfIdempotent : BlockOfIdempotent env

namespace RepresentationWF

theorem projectionComplete {env : Ixon.Env} (h : RepresentationWF env)
    {block constant members target}
    (hentry : ExactAnonEntry env block constant)
    (hinfo : constant.info = .muts members)
    (htarget : target ∈ anonBlockTargets block members) :
    ∃ projectionConstant,
      ExactAnonEntry env target projectionConstant ∧
      projectionOwner? projectionConstant.info = some block :=
  h.source.projectionComplete hentry hinfo htarget

theorem projectionOwned {env : Ixon.Env} (h : RepresentationWF env)
    {addr constant owner}
    (hentry : ExactAnonEntry env addr constant)
    (howner : projectionOwner? constant.info = some owner) :
    ∃ blockConstant members,
      ExactAnonEntry env owner blockConstant ∧
      blockConstant.info = .muts members ∧
      addr ∈ anonBlockTargets owner members :=
  h.source.projectionOwned hentry howner

/-- Hash verification and materialization make the production verified
loader return the exact stored constant. -/
theorem getConstVerified_true {env : Ixon.Env} (h : RepresentationWF env)
    {addr : Address} {lazy : Ixon.LazyConstant}
    (hlookup : env.consts.get? addr = some lazy) :
    ∃ constant, getConstVerified env addr true = .ok (some constant) := by
  obtain ⟨constant, hget⟩ := h.constMaterialization hlookup
  refine ⟨constant, ?_⟩
  have hhash := h.constAddresses hlookup
  unfold getConstVerified
  change env.consts[addr]? = some lazy at hlookup
  rw [hlookup]
  simp only [Bool.true_or, if_true]
  rw [hhash]
  simp [hget]
  change Except.ok (some constant) = Except.ok (some constant)
  rfl

end RepresentationWF

/-- A successful pure decode followed by explicit anonymous metadata erasure
and a proof that the resulting ingress source is representation-safe. -/
structure SerializedAnonInput (bytes : ByteArray) (env : Ixon.Env) where
  source : Ixon.Env
  encode : Ixon.serEnv source = .ok bytes
  decoded : Ixon.Env
  decode : Ixon.deEnv bytes = .ok decoded
  erased : eraseAnonMetadata decoded = env
  representation : RepresentationWF env

/-- A source environment can be serialized, but its emitted bytes are
rejected by the reference decoder.  This is the useful negative contract for
malformed content-addressed maps: the writer is intentionally mechanical,
while the reader enforces representation integrity. -/
def SerializedDecodeRejected (source : Ixon.Env) : Prop :=
  ∃ bytes error,
    Ixon.serEnv source = .ok bytes ∧ Ixon.deEnv bytes = .error error

/-- Executable discriminator used only to establish finite rejection
fixtures. -/
def serializationRejected (source : Ixon.Env) : Bool :=
  match Ixon.serEnv source with
  | .error _ => false
  | .ok bytes =>
      match Ixon.deEnv bytes with
      | .error _ => true
      | .ok _ => false

theorem serializedDecodeRejected_of_true {source : Ixon.Env}
    (h : serializationRejected source = true) :
    SerializedDecodeRejected source := by
  unfold serializationRejected at h
  generalize hencode : Ixon.serEnv source = encoded at h
  cases encoded with
  | error error => simp at h
  | ok bytes =>
      generalize hdecode : Ixon.deEnv bytes = decoded at h
      cases decoded with
      | error error => exact ⟨bytes, error, hencode, hdecode⟩
      | ok env => simp [hdecode] at h

end IxonEnv

/-! ## Catalog load correspondence -/

/-- Exact successful eager ingress of the work enumerated from a serialized
environment, with both constant and block tables agreeing with the immutable
semantic world. -/
structure EagerCatalogAgreement (env : Ixon.Env) (world : VerifyWorld)
    (work : Array AnonWorkItem) where
  after : AnonEnv
  run : (ingressAll env true).run ({} : AnonEnv) = .ok work after
  constants : LoadedAgrees world.catalog after
  blocks : LoadedBlocksAgrees world.blocks after

/-- One successful production lazy-fault step and its immutable-catalog
postcondition.  The step may report `false` for an absent address; in that
case catalog agreement still has to hold. -/
structure LazyCatalogStep (env : Ixon.Env) (world : VerifyWorld)
    (before : AnonEnv) (addr : Address) where
  after : AnonEnv
  found : Bool
  run : ingressAnonAddrShallow env addr true before = .ok found after
  constants : LoadedAgrees world.catalog after
  blocks : LoadedBlocksAgrees world.blocks after

/-- A concrete sequence of successful production lazy faults.  This is the
finite, run-scoped load oracle used by serialized fixtures; it makes neither
an arbitrary-callback assumption nor an all-address totality claim. -/
inductive LazyCatalogTrace (env : Ixon.Env) (world : VerifyWorld) :
    AnonEnv → List Address → AnonEnv → Prop
  | nil (current : AnonEnv) : LazyCatalogTrace env world current [] current
  | cons {before after : AnonEnv} {addr : Address}
      {rest : List Address} :
      (step : LazyCatalogStep env world before addr) →
      LazyCatalogTrace env world step.after rest after →
      LazyCatalogTrace env world before (addr :: rest) after

/-! ## Serialized dependency binding -/

/-- Every abstract declaration edge is witnessed by the exact serialized
constant at its source and by membership in that constant's `refs` table.
The table is an intern table, so this is intentionally one-way: unused refs
and Nat/String blob slots do not become declaration dependencies. -/
def SerializedDependencyBound (env : Ixon.Env)
    (dependencies : DependencyCatalog) : Prop :=
  ∀ {source target}, dependencies.dependsOn source target →
    ∃ constant, env.getConst? source = some constant ∧
      target ∈ constant.refs

theorem IxonEnv.dependencyCatalog_bound (env : Ixon.Env)
    (hblock : IxonEnv.BlockOfIdempotent env) :
    SerializedDependencyBound env
      (IxonEnv.dependencyCatalog env hblock) := by
  intro source target hdependency
  obtain ⟨constant, hget, hsemantic⟩ := hdependency
  exact ⟨constant, hget, hsemantic.target_mem_refs⟩

/-! ## Byte-level acceptance package -/

/-- A complete finite serialized-input acceptance certificate.

The semantic conclusion remains the existing `SubjectWF`; the additional
fields prove that its source work, dependency edges, eager catalog, lazy
catalog, and production driver execution all originate in one successfully
decoded, hash-verified byte array. -/
structure SerializedSubjectCertificate (bytes : ByteArray) (world : VerifyWorld)
    (dependencies : DependencyCatalog) (assumptions : FiniteAddressSet)
    (lazyRequests : List Address) where
  env : Ixon.Env
  input : IxonEnv.SerializedAnonInput bytes env
  eager : EagerCatalogAgreement env world (expectedAnonWork env)
  lazyAfter : AnonEnv
  lazy : LazyCatalogTrace env world ({} : AnonEnv) lazyRequests lazyAfter
  lazyConstants : LoadedAgrees world.catalog lazyAfter
  lazyBlocks : LoadedBlocksAgrees world.blocks lazyAfter
  dependencyBound : SerializedDependencyBound env dependencies
  cfg : CheckCfg
  results : Array CheckResult
  driver : checkEnvAnon env cfg = .ok results
  resultsSucceeded : AllCheckResultsSucceeded results
  semantic : SubjectWF world dependencies (expectedAnonWork env)
    input.representation.source.subjects assumptions

/-- Proposition-level public statement: a byte array has a complete finite
serialized-input certificate. -/
def SerializedSubjectWF (bytes : ByteArray) (world : VerifyWorld)
    (dependencies : DependencyCatalog) (assumptions : FiniteAddressSet)
    (lazyRequests : List Address) : Prop :=
  Nonempty (SerializedSubjectCertificate bytes world dependencies assumptions
    lazyRequests)

end Ix.Tc
