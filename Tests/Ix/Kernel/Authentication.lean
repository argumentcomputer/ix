import Tests.Ix.Kernel.CertifiedEntry
import Ix.Address

/-! # Authentication at Ixon admission

The certified entries at BLAKE3 (`Ixon.Authenticated`) refuse every record
and every blob whose address is not the BLAKE3 hash of its bytes, exactly as
supplied, and derive omitted projection records under the same hash. The
checks run each entry on the reader fixtures re-keyed to their BLAKE3
addresses (`Tests.Ix.Kernel.Reader`):

- a record, and a blob, under a key that is not its hash is refused, as a
  reject, at its position, by all three entries;
- an omitted projection is reconstructed under its BLAKE3 address (the pure
  implementation's and the Rust backend's alike), and the entry accepts the
  batch; a supplied projection under another key is refused;
- the accept path is unchanged: the compiler's own records (the frozen
  `lTreeRecords` and `levelRecords`) are authentic as compiled;
- the committed prelude records (`PinData.prelude`) are keyed by the pure
  BLAKE3 hashes of their committed bytes. -/

open Ix.Kernel.Reader
open Tests.Ix.Kernel.Reader
open Tests.Ix.Kernel.CertifiedEntry (omitted twoKey litRecords)

namespace Tests.Ix.Kernel.Authentication

/-- The records a fixture's stand-in key holds under its BLAKE3 key. -/
def records (cs : List (Address × Ixon.Constant)) : Ix.Kernel.Admission.Records := (rekeyed cs).encoded

/-- `records` with the payload at `position` stored under `key` instead. -/
def rekeyAt (rs : Ix.Kernel.Admission.Records) (position : Nat) (key : Address) : Ix.Kernel.Admission.Records :=
  rs.zipIdx.map fun ((a, b), i) => if i == position then (key, b) else (a, b)

def litBlobs : List (Address × ByteArray) := (rekeyed [(address 42, litEq)] [(address 41, ⟨#[2]⟩)]).blobs

/-! ## Unauthentic records and blobs are refused -/

-- the controls: the re-keyed fixtures are accepted by all three entries
#guard (Ixon.Authenticated.checkBytes limits (records definitions) []).isOk
#guard (Ixon.Authenticated.checkBytesProjection 16 limits (records definitions) []).isOk
#guard (Ixon.Authenticated.checkBytesBlockOrder 16 limits {} (records definitions) []).isOk
#guard (Ixon.Authenticated.checkBytes limits litRecords litBlobs).isOk

-- a record under another record's key, under a stand-in key, or with its
-- payload changed under its own key
#guard match Ixon.Authenticated.checkBytes limits
    (rekeyAt (records definitions) 1 ((records definitions)[2]!.1)) [] with
  | .error (.duplicate .records 2 _) => true
  | _ => false
#guard match Ixon.Authenticated.checkBytes limits
    ((rekeyAt (records definitions) 1 ((records definitions)[2]!.1)).take 2) [] with
  | .error e@(.mismatch .records 1 a) => a == (records definitions)[2]!.1 && e.outcome == .rejected
  | _ => false
#guard match Ixon.Authenticated.checkBytes limits (rekeyAt (records definitions) 1 (address 11)) [] with
  | .error e@(.mismatch .records 1 a) => a == address 11 && e.outcome == .rejected
  | _ => false
#guard match Ixon.Authenticated.checkBytes limits
    ((records definitions).map fun (a, b) => if a == (rekeyed definitions).rename (address 12) then (a, b.push 0) else (a, b)) [] with
  | .error e@(.mismatch .records 2 a) => a == (rekeyed definitions).rename (address 12) && e.outcome == .rejected
  | _ => false
#guard match Ixon.Authenticated.checkBytesProjection 16 limits (rekeyAt (records definitions) 0 (address 10)) [] with
  | .error e@(.reconstruction (.admission (.mismatch .records 0 a))) => a == address 10 && e.outcome == .rejected
  | _ => false
#guard match Ixon.Authenticated.checkBytesBlockOrder 16 limits {} (rekeyAt (records definitions) 0 (address 10)) [] with
  | .error e@(.order (.admission (.mismatch .records 0 a))) => a == address 10 && e.outcome == .rejected
  | _ => false

-- a blob under a key that is not its hash, and a blob's bytes changed under
-- its key (the literal's value would change)
#guard match Ixon.Authenticated.checkBytes limits litRecords [(address 41, ⟨#[2]⟩)] with
  | .error e@(.mismatch .blobs 0 a) => a == address 41 && e.outcome == .rejected
  | _ => false
#guard match Ixon.Authenticated.checkBytes limits litRecords (litBlobs.map fun (a, _) => (a, ⟨#[3]⟩)) with
  | .error e@(.mismatch .blobs 0 _) => e.outcome == .rejected
  | _ => false
#guard match Ixon.Authenticated.checkBytesProjection 16 limits litRecords (litBlobs.map fun (a, _) => (a, ⟨#[3]⟩)) with
  | .error e@(.reconstruction (.admission (.mismatch .blobs 0 _))) => e.outcome == .rejected
  | _ => false
#guard match Ixon.Authenticated.checkBytesBlockOrder 16 limits {} litRecords (litBlobs.map fun (a, _) => (a, ⟨#[3]⟩)) with
  | .error e@(.order (.admission (.mismatch .blobs 0 _))) => e.outcome == .rejected
  | _ => false

/-! ## Omitted projections are reconstructed and authenticated -/

def reconstructed : List (Address × Ixon.Constant) :=
  match Ixon.Authenticated.reconstruct 16 (rekeyed twoFixture).records |>.toOption with
  | some cs => cs
  | none => []

def omittedConstants : List (Address × Ixon.Constant) :=
  (rekeyed twoFixture).records.filter fun (_, c) => !Ix.Kernel.Ingress.isProjection c.info

def derived : List (Address × Ixon.Constant) :=
  match Ixon.Authenticated.reconstruct 16 omittedConstants |>.toOption with
  | some cs => cs.filter fun (_, c) => Ix.Kernel.Ingress.isProjection c.info
  | none => []

-- the three projection records of `Two` are derived, each under the pure
-- BLAKE3 hash of its serialization and the Rust backend's alike, and they are
-- the fixture's own records under the keys its recursor and theorem name
#guard derived.length == 3
#guard derived.all fun (a, c) =>
  a == Address.blake3Pure (Ixon.serConstant c) && a == Address.blake3 (Ixon.serConstant c)
#guard derived.all fun pair => (rekeyed twoFixture).records.contains pair
#guard derived.all fun (_, c) => match c.info with
  | .iPrj p => p.block == twoKey
  | .cPrj p => p.block == twoKey
  | _ => false
-- reconstruction reuses the supplied projection records unchanged
#guard reconstructed.length == (rekeyed twoFixture).records.length
-- the entry accepts the batch without them, and refuses a projection record
-- supplied under another key
#guard (Ixon.Authenticated.checkBytesProjection 16 limits omitted []).isOk
#guard (Ixon.Authenticated.checkBytesProjection 16 limits (records twoFixture) []).isOk
#guard match Ixon.Authenticated.checkBytesProjection 16 limits (rekeyAt (records twoFixture) 1 (address 21)) [] with
  | .error e@(.reconstruction (.admission (.mismatch .records 1 a))) => a == address 21 && e.outcome == .rejected
  | _ => false

/-! ## The compiler's records are authentic as compiled -/

#guard (Ix.Kernel.Admission.authenticate Address.blake3Pure lTreeStream []).isOk
#guard (Ix.Kernel.Admission.authenticate Address.blake3Pure levelStream []).isOk
#guard lTreeStream.all fun (a, b) => a == Address.blake3 b
#guard (Ixon.Authenticated.checkBytes limits lTreeStream []).isOk

/-! ## The committed prelude is keyed by its records' hashes -/

def preludeEntries : List (Option Address × Option ByteArray) :=
  PinData.prelude.toList.map fun (a, b) => (addressOfHex a, bytesOfHex b)

#guard preludeEntries.length == PinData.prelude.size && preludeEntries.length > 0
#guard preludeEntries.all fun
  | (some a, some b) => a == Address.blake3Pure b && a == Address.blake3 b
  | _ => false
-- the prelude the entry loads holds exactly those records, decoded canonically
#guard match builtinPrelude with
  | .ok pre => pre.records.size == PinData.prelude.size && pre.records.all fun (a, c) =>
      a == Address.blake3Pure (Ixon.serConstant c)
  | .error _ => false

/-! ## The theorems, applied -/

example {records : Ix.Kernel.Admission.Records} {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : Ixon.Authenticated.checkBytesProjection 16 limits records blobs = .ok env) :
    ∃ output, (∀ entry ∈ output, entry.1 = Address.blake3Pure (Ixon.serConstant entry.2)) ∧
      Ix.Kernel.Admission.checkConstants output blobs = .ok env :=
  (Ixon.Authenticated.checkBytesProjection_authentic h).2

example {records : Ix.Kernel.Admission.Records} {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : Ixon.Authenticated.checkBytesBlockOrder 16 limits {} records blobs = .ok env) :
    ∀ entry ∈ blobs, entry.1 = Address.blake3Pure entry.2 :=
  (Ixon.Authenticated.checkBytesBlockOrder_authentic h).1.2

end Tests.Ix.Kernel.Authentication
