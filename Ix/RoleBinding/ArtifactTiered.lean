module

public import Ix.RoleBinding.Artifact

/-! The artifact's exact binding/prelude and complete raw batch at the existing
tiered entry. Its logical part has a model; tier declarations are typed with
tier constants opaque. There is no retry of a failed logical check here. -/

@[expose] public section

namespace Ix.RoleBinding.Artifact

inductive TierError where
  | preparation (error : Error)
  | admission (error : Ix.Kernel.Admission.TierError)

instance : ToString TierError where
  toString
    | .preparation e => toString e
    | .admission e => s!"artifact tier: {e}"

/-- The admitted table must be exactly the prepared canonical binding, not
merely have an equal claimed hash. The prelude is the guarded actual input. -/
def Prepared.preludeFor (p : Prepared) (table : Ix.Kernel.RoleTable) :
    Except String (Ix.Kernel.Reader.Prelude .anon) := do
  unless table.toBytes == p.binding.bytes do
    throw "artifact tier: admitted table differs from prepared binding"
  return p.pre

def PreparedRecords.hasTier (input : PreparedRecords) : Bool :=
  input.constants.any fun (_, c) => Ix.Kernel.Admission.isTierInfo c.info

def prepareTiered (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) :
    Except TierError Prepared := do
  let input ← (prepareRecords artifact limits).mapError .preparation
  let p := input.prepared
  -- partitionTier preserves each input record in one arm, in input order;
  -- tier positions are positions in this same complete ordered batch.
  let (logical, tier) := Ix.Kernel.Admission.partitionTier input.constants
  unless logical.length + tier.size == input.constants.length do
    throw (.preparation (.coverage "tier partition does not cover every input record"))
  if let some (address, dependency) := Ix.Kernel.Admission.fenceOf logical tier then
    throw (.admission (.fence address dependency))
  let (evidence, declarations) ← (Ix.Kernel.Admission.readStream Address.admissionHash p.table p.pre
    logical p.blobs p.hints.lookup).mapError (.preparation ∘ .admission)
  (checkEvidence p.table evidence
    (Ix.Kernel.Frontend.preparePrelude p.pre.ix declarations)).mapError .preparation
  return p

/-- A receipt of preparation and the actual tiered check on every original
raw record. It makes no Source-value or host assumption-root claim. -/
structure TierReceipt (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) where
  prepared : Prepared
  logical : Ix.Kernel.Env .anon
  tier : List (Ix.Kernel.Tier.TierConst .anon)
  preparedFrom : prepareTiered artifact limits = .ok prepared
  checked : Ix.Kernel.Admission.checkBytesTieredUsing prepared.preludeFor Address.admissionHash
    prepared.binding limits prepared.records prepared.blobs prepared.hints.lookup = .ok (logical, tier)

def checkTiered (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) :
    Except TierError (TierReceipt artifact limits) :=
  match fromArtifact : prepareTiered artifact limits with
  | .error e => .error e
  | .ok prepared =>
    match checked : Ix.Kernel.Admission.checkBytesTieredUsing prepared.preludeFor Address.admissionHash
        prepared.binding limits prepared.records prepared.blobs prepared.hints.lookup with
    | .error e => .error (.admission e)
    | .ok (logical, tier) => .ok ⟨prepared, logical, tier, fromArtifact, checked⟩

end Ix.RoleBinding.Artifact
