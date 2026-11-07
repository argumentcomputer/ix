module
public import Aiur.Ixon
public import Ix.Address
public import IxC.Ixon.Codec
meta import IxC.Ixon.Codec
meta import Aiur.Ixon

/-! Content addressing of compiled Aiur artifacts (review item F3).

Lean's exporters write packages in Ixon serialization (`Aiur.Artifact`); an
artifact's identity is the BLAKE3 digest of its file. `ix` prints the digest of
every artifact it uses, checks it against a pinned digest when one is given
(`--aiur-artifact-digest`, `IX_AIUR_ARTIFACT_DIGEST` and their aggregation
counterparts), and caches exported artifacts by it:
`.lake/aiur/{target}-{digest}.ixa`, with `{target}-{key}.ref` recording the
digest exported for a source key. Rust hosts verify content-addressed names
on load (`aiur::artifact::read`), so a cached artifact that no longer matches
its digest fails closed on both sides. -/

public section
namespace Ix.AiurArtifact

/-- The Aiur package carries its own copy of Ixon's TagN integer code; it must
write exactly the bytes `Ixon.putTagN 0 0` writes. -/
private def tagNSamples : List UInt64 :=
  [0, 1, 127, 128, 129, 16511, 16512, 16513, 82047, 82048, 82049, 16859263,
   16859264, 16859265, 4311826559, 4311826560, 4311826561, 0xFFFFFFFFFFFFFFFE,
   0xFFFFFFFFFFFFFFFF]

#guard tagNSamples.all fun v =>
  (Aiur.Ixon.tagN0 .empty v).data == (Ixon.runPut (Ixon.putTagN 0 0 v)).data

def packageMagic : ByteArray := "IXAIURP\x00".toUTF8
def extension : String := "ixa"

/-- The digest pinned for an artifact: the `--{flag}-digest` flag, else the
`{env}_DIGEST` variable. -/
def expected (flagDigest : Option String) (env : String) : IO (Option String) := do
  if let some digest := flagDigest then return some digest
  IO.getEnv s!"{env}_DIGEST"

/-- Admit the compiled package at `path` for use: check that it is one, print
its digest, and refuse it when it differs from the `expected` digest. -/
def admit (target : String) (path : String) (expected : Option String := none) :
    IO Address := do
  let bytes ← IO.FS.readBinFile path
  unless (bytes.extract 0 packageMagic.size).data == packageMagic.data do
    throw (IO.userError s!"{path} is not a compiled Aiur package")
  let digest := Address.blake3 bytes
  IO.eprintln s!"[aiur] {target} artifact {path}: blake3 {digest}"
  if let some expected := expected then
    unless toString digest == expected do
      throw (IO.userError s!"{target} artifact {path} has digest {digest}, but {expected} is pinned")
  return digest

private def writeAtomically (path : System.FilePath) (text : String) : IO Unit := do
  let tmp := System.FilePath.mk s!"{path}.tmp.{← IO.Process.getPID}.{← IO.monoNanosNow}"
  try
    IO.FS.writeFile tmp text
    IO.FS.rename tmp path
  finally
    if ← tmp.pathExists then IO.FS.removeFile tmp

/-- The artifact cached in `directory` for `target` under the source `key`,
exported with `exportTo` (which writes the path it is given) when none is cached.
A cached artifact must still hash to the digest it is filed under, or this
fails closed; delete it to export again. The result is admitted against
`expected`. -/
def cached (directory : System.FilePath) (target : String) (key : Address)
    (expected : Option String) (exportTo : System.FilePath → IO Unit) : IO String := do
  IO.FS.createDirAll directory
  let ref := directory / s!"{target}-{key}.ref"
  let file := fun (digest : String) => directory / s!"{target}-{digest}.{extension}"
  if ← ref.pathExists then
    let digest := (← IO.FS.readFile ref).trimAscii.toString
    let path := file digest
    if ← path.pathExists then
      let actual := Address.blake3 (← IO.FS.readBinFile path)
      unless toString actual == digest do
        throw (IO.userError s!"cached artifact {path} hashes to {actual}, not its digest; delete it to export again")
      let _ ← admit target path.toString expected
      return path.toString
  IO.eprintln s!"[aiur] exporting the certified {target} artifact to {directory}; this runs once \
    per source revision and takes several minutes (`ix prepare` does it ahead of time)"
  let tmp := directory / s!"{target}-{key}.tmp.{← IO.Process.getPID}.{← IO.monoNanosNow}"
  try
    exportTo tmp
    let digest := Address.blake3 (← IO.FS.readBinFile tmp)
    let path := file (toString digest)
    IO.FS.rename tmp path
    writeAtomically ref s!"{digest}\n"
    let _ ← admit target path.toString expected
    return path.toString
  finally
    if ← tmp.pathExists then IO.FS.removeFile tmp

end Ix.AiurArtifact
end
