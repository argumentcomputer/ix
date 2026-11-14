/-
  The shard-proof index: `~/.ix/cache/formal-shard-proofs/<claim-digest-hex>`
  holds the store address of an `Ixon.Proof` wrapper whose bundled `CheckEnv`
  claim has that digest. It is what lets a partially proved partition resume
  after a refinement: a leaf's identity is its claim digest, never its manifest
  index. An index entry is an untrusted hint — readers decode the wrapper,
  compare the bundled claim with the one they expect and verify the proof
  natively before reusing it, the aggregate cache's discipline.
-/
module
public import Ix.Address
public import Ix.Store

public section

namespace Ix.Cli.ShardProofIndex

/-- The index directory: the global `~/.ix/cache/formal-shard-proofs`, or a
    hermetic root for tests. The retired backend's `shard-proofs` index held
    proofs in another format and is not read. -/
def indexDir (cacheRoot? : Option System.FilePath := none) : IO System.FilePath := do
  match cacheRoot? with
  | some root =>
    let dir := root / "formal-shard-proofs"
    IO.FS.createDirAll dir
    pure dir
  | none => StoreIO.toIO (Store.cacheDir "formal-shard-proofs")

/-- Read an index entry. A missing or malformed entry is a miss, never an
    error: store loading and verification happen separately. -/
def readAddress (dir : System.FilePath) (digest : Address) : IO (Option Address) := do
  let path := dir / toString digest
  if !(← path.pathExists) then return none
  try
    let raw ← IO.FS.readFile path
    pure (Address.fromString raw.trimAscii.toString)
  catch _ => pure none

/-- Atomically replace one index entry. The temporary name carries the pid
    so concurrent writers of one digest never share it. -/
def writeAddress (dir : System.FilePath) (digest addr : Address) : IO Unit := do
  let pid ← IO.Process.getPID
  let tmp := dir / s!"{digest}.tmp.{pid}"
  IO.FS.writeFile tmp s!"{addr}\n"
  IO.FS.rename tmp (dir / toString digest)

end Ix.Cli.ShardProofIndex
end
