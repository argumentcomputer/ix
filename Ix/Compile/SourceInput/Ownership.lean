module
public import Ix.Compile.SourceInput.Metadata
public import Ix.CompileM
public import Ix.RoleBinding.Artifact

@[expose] public section
namespace Ix.Compile.SourceInput.Ownership
open Ix.Kernel Ix.Kernel.Reader

/-- One actual decoded batch and its reader store. The erased equation
prevents observations from silently consulting a different owner store. -/
structure PhysicalIndex where
  input : Ix.RoleBinding.Artifact.PreparedRecords
  store : Ixon.CheckOrder.RecordStore
  built : store = recordMap input.constants.toArray

def PhysicalIndex.ofPrepared (input : Ix.RoleBinding.Artifact.PreparedRecords) : PhysicalIndex :=
  ⟨input,recordMap input.constants.toArray,rfl⟩

inductive Resolution where
  | aggregate (members : Nat)
  | resolved (reference : ConstRef Address)
  | unresolvedProjection

structure Physical where
  owner : Address
  ownerRecord : Option Ixon.Constant
  resolution : Resolution

/-- Aggregate blocks do not denote one member. A projection's unresolved
member and any absent owner stay explicit; neither triggers a fallback. -/
def observeRecord (index : PhysicalIndex) (address : Address) (constant : Ixon.Constant) : Physical :=
  let owner := Ixon.CheckOrder.owner address constant
  { owner, ownerRecord := index.store[owner]?, resolution := match constant.info with
    | .muts members => .aggregate members.size
    | _ => match resolveSource (index.store[·]?) address constant with
      | some reference => .resolved reference
      | none => .unresolvedProjection }

structure Row where
  position : Nat
  address : Address
  physical : Physical

def observeRows (index : PhysicalIndex) : List Row :=
  index.input.constants.zipIdx.map fun ((address,constant),position) =>
    ⟨position,address,observeRecord index address constant⟩

inductive AddressObservation where
  | absent (address : Address)
  | present (address : Address) (physical : Physical)

def probeAddress (index : PhysicalIndex) (address : Address) : AddressObservation :=
  match index.store[address]? with
  | none => .absent address
  | some constant => .present address (observeRecord index address constant)

inductive Publication where
  | unpublished
  | published (address : Address) (observation : AddressObservation)

def probePublication (index : PhysicalIndex) : Option Address → Publication
  | none => .unpublished
  | some address => .published address (probeAddress index address)

inductive NamedPublication where
  | absent
  | found (representative : Option Ix.Name) (entry : Ixon.Named)
      (current : AddressObservation) (original : Option AddressObservation)

/-- Keep the actual raw-map representative and full Named value. An absent
entry is distinct from a present entry with no original metadata address. -/
def probeNamed (index : PhysicalIndex) (entries : Ix.Map Ix.Name Ixon.Named) (query : Ix.Name) :
    NamedPublication :=
  match entries.get? query with
  | none => .absent
  | some entry => .found (entries.getKey? query) entry (probeAddress index entry.addr)
      (entry.original.map fun original => probeAddress index original.1)

structure NameObservation where
  primary : Publication
  compilerNamed : NamedPublication
  artifactNamed : NamedPublication

/-- These are three CURRENT lookup channels. The final named registries may
differ from primary resolution; no historical block-local lookup is inferred. -/
def probeName (cenv : Ix.CompileM.CompileEnv) (artifact : Ixon.Env) (index : PhysicalIndex)
    (query : Ix.Name) : NameObservation :=
  ⟨probePublication index (cenv.nameToAddr.get? query),
   probeNamed index cenv.nameToNamed query,probeNamed index artifact.named query⟩

structure Observation where
  query : Ix.Name
  sourceRepresentative : Option Ix.Name
  self : NameObservation
  metadata : Except Error (List (Metadata.Ref × NameObservation))

/-- Reports all metadata occurrences and all publication/owner failures as
data. A returned observation is not an admission or a Source-value claim. -/
def observeAt (carrier : Carrier) (cenv : Ix.CompileM.CompileEnv) (artifact : Ixon.Env)
    (index : PhysicalIndex) (query : Ix.Name) : Observation :=
  { query, sourceRepresentative := carrier.representative? query
    self := probeName cenv artifact index query
    metadata := (fun refs => refs.map fun ref => (ref,probeName cenv artifact index ref.name)) <$>
      carrier.captureMetadataAt query }

end Ix.Compile.SourceInput.Ownership
end
