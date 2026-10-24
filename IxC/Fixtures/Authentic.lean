import IxC.Ixon.Codec

/-! # Authentic fixtures

The certified entries refuse a record or blob whose address is not the
content hash of its bytes, so a fixture written with readable stand-in keys
(`IxonFixtures.address 3`) is re-keyed before it is admitted: `rekey` stores
every blob under the hash of its bytes and every record, after the keys it
names are renamed, under the hash of its serialization, and keeps the
renaming so that tests can state their expectations in the stand-in keys.

`fixtureHash` is the kernel-side fixtures' hash: the kernel's fence admits no
hasher, and the entries' theorems hold at every hash. The root package's
tests re-key the same fixtures at BLAKE3 (`Address.blake3Pure`). -/

namespace Tests.Ix.Kernel.Authentic

/-- A hasher-free 32-byte digest: four 64-bit FNV-1a lanes with distinct
offsets. Deterministic and spread enough to give the fixtures distinct keys;
not collision-resistant. -/
def fixtureHash (bytes : ByteArray) : Address :=
  let lane (offset : UInt64) : UInt64 :=
    bytes.data.foldl (fun h b => (h ^^^ b.toUInt64) * 0x100000001b3) offset
  let word (w : UInt64) : Array UInt8 := (Array.range 8).map fun i => (w >>> (8 * i).toUInt64).toUInt8
  ⟨⟨#[0xcbf29ce484222325, 0x84222325cbf29ce4, 0x9ce484222325cbf2, 0x2325cbf29ce48422].flatMap
    fun offset => word (lane offset)⟩⟩

/-- A fixture under authentic keys, and the renaming of its stand-in keys. -/
structure Rekeyed where
  records : List (Address × Ixon.Constant)
  blobs : List (Address × ByteArray)
  renamed : List (Address × Address)

/-- The authentic key of a stand-in key; any other key is kept. -/
def Rekeyed.rename (s : Rekeyed) (address : Address) : Address :=
  (s.renamed.lookup address).getD address

/-- The stand-in key an authentic key renames, if any. -/
def Rekeyed.original (s : Rekeyed) (address : Address) : Address :=
  ((s.renamed.find? (·.2 == address)).map (·.1)).getD address

/-- The records' payloads, as the entries take them. -/
def Rekeyed.encoded (s : Rekeyed) : List (Address × ByteArray) :=
  s.records.map fun (address, constant) => (address, Ixon.serConstant constant)

def renameInfo (rename : Address → Address) : Ixon.ConstantInfo → Ixon.ConstantInfo
  | .iPrj p => .iPrj { p with block := rename p.block }
  | .cPrj p => .cPrj { p with block := rename p.block }
  | .rPrj p => .rPrj { p with block := rename p.block }
  | .dPrj p => .dPrj { p with block := rename p.block }
  | info => info

/-- A record with its references and its projection owner renamed. -/
def renameConstant (rename : Address → Address) (c : Ixon.Constant) : Ixon.Constant :=
  { c with info := renameInfo rename c.info, refs := c.refs.map rename }

/-- The keys a record names: its references and its projection owner. -/
def named (c : Ixon.Constant) : List Address :=
  c.refs.toList ++ match c.info with
    | .iPrj p => [p.block]
    | .cPrj p => [p.block]
    | .rPrj p => [p.block]
    | .dPrj p => [p.block]
    | _ => []

/-- Re-key a fixture under `hash`: every blob under `hash` of its bytes, and
every record, once the fixture keys it names are renamed, under `hash` of its
serialization. Records are renamed in rounds, dependencies first (a record
that names its own key, or a cycle, is renamed last with what is known). A
stand-in key used twice is renamed as its first record; a key that no record
or blob of the fixture holds (a prelude record, a missing reference) is
kept. -/
def rekey (hash : ByteArray → Address) (records : List (Address × Ixon.Constant))
    (blobs : List (Address × ByteArray) := []) : Rekeyed := Id.run do
  let keys := records.map (·.1)
  let blobRenaming := blobs.map fun (key, bytes) => (key, hash bytes)
  let rename (map : List (Address × Address)) (address : Address) : Address :=
    match map.lookup address with
    | some key => key
    | none => (blobRenaming.lookup address).getD address
  let mut renamed : List (Address × Address) := []
  let mut rekeyed : Array (Option (Address × Ixon.Constant)) := Array.replicate records.length none
  for round in [0:records.length + 1] do
    for ((key, c), i) in records.zipIdx do
      if rekeyed[i]!.isSome then continue
      let ready := (named c).all fun a => a == key || !keys.contains a || (renamed.lookup a).isSome
      if ready || round == records.length then
        let c' := renameConstant (rename renamed) c
        let key' := hash (Ixon.serConstant c')
        rekeyed := rekeyed.set! i (some (key', c'))
        if (renamed.lookup key).isNone then renamed := renamed ++ [(key, key')]
  return {
    records := (records.zip rekeyed.toList).map fun ((key, c), s) => s.getD (key, c)
    blobs := blobs.map fun (_, bytes) => (hash bytes, bytes)
    renamed := renamed ++ blobRenaming.filter fun (key, _) => (renamed.lookup key).isNone }

end Tests.Ix.Kernel.Authentic
