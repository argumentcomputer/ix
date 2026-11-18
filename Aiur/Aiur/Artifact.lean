import Aiur.Execution.Encode

/-! Compiled Aiur artifacts in Ixon serialization, as Lean's exporters write
them for the Rust hosts (`aiur::artifact`, which documents the grammar):

* a package is a compiled program and, when circuits were exported, its trace
  section (`Trace.exportPlan`);
* an execution package adds one invocation's arguments and data hints, for the
  development drivers;
* a grouping holds checked function groups alone (`Trace.exportGroups`), to
  replace a package's.

The writers emit `formatVersion` 2, which stores structure once: a program's
distinct table rows precede its tables, which name rows by index
(`Execution.rowPool`), and the distinct polynomial nodes of a trace section or
grouping precede it, which names each polynomial by its root node
(`Trace.withNodes`). Both pools list entries in first-reference order, so an
artifact has one encoding. The Rust reader also accepts version 1, which
writes rows and polynomial trees inline. `packageWide` explicitly selects
version 3: the same pooled structure, with up to four UInt64 limbs for the
modulus and field constants. Invocation and hint encodings remain narrow.

An artifact's identity is the BLAKE3 digest of its file. The Aiur package has
no BLAKE3, so the hosts compute it: Rust on every load, and `ix` when it
caches or admits an artifact (`Ix.AiurArtifact`). -/

namespace Aiur.Artifact
open Aiur.Ixon Execution

def packageMagic : ByteArray := "IXAIURP\x00".toUTF8
def executionMagic : ByteArray := "IXAIURX\x00".toUTF8
def groupsMagic : ByteArray := "IXAIURG\x00".toUTF8
/-- The default grammar version for the existing artifact writers. -/
def formatVersion : Nat := 2
/-- Opt-in package grammar with canonical field integers of at most 256 bits. -/
def wideFormatVersion : Nat := 3
/-- The conventional file extension. -/
def extension : String := "ixa"

def putPackageWithEncoding (encoding : FieldEncoding) (exported : Export F)
    (modulus : Nat) (encode : F → Nat)
    (trace : Option ByteArray) : PutM Unit := do
  raw packageMagic
  nat (match encoding with | .narrow => formatVersion | .wide => wideFormatVersion)
  exported.putProgramWithEncoding encoding modulus encode
  option trace raw

def putPackage (exported : Export F) (modulus : Nat) (encode : F → Nat)
    (trace : Option ByteArray) : PutM Unit :=
  putPackageWithEncoding .narrow exported modulus encode trace

/-- A compiled package. `trace` is a trace section from `Trace.exportPlan`. -/
def package (exported : Export F) (modulus : Nat) (encode : F → Nat)
    (trace : Option ByteArray := none) : Except String ByteArray :=
  Ixon.run (putPackage exported modulus encode trace)

/-- A wide-field transport package. `trace`, when present, must come from
`Trace.exportPlanWide` or `Trace.exportPlanParallelWide`. This format does not
provide wide invocation, hint or interpreter support. -/
def packageWide (exported : Export F) (modulus : Nat) (encode : F → Nat)
    (trace : Option ByteArray := none) : Except String ByteArray :=
  Ixon.run (putPackageWithEncoding .wide exported modulus encode trace)

/-- A package with one invocation: its arguments, an input the program must
reject (or none), and prepared data hints. -/
def execution (exported : Export F) (modulus : Nat) (encode : F → Nat)
    (trace : Option ByteArray) (args invalidArgs : List Nat)
    (hints : Array (FlatHintEntry F)) : Except String ByteArray :=
  Ixon.run do
    raw executionMagic
    nat formatVersion
    putPackage exported modulus encode trace
    nats args
    nats invalidArgs
    putHints encode hints

/-- Prepared data hints alone, as the in-process FFI takes them. -/
def hints (encode : F → Nat) (entries : Array (FlatHintEntry F)) : Except String ByteArray :=
  Ixon.run (putHints encode entries)

/-- Write an artifact through a temporary file, so that no reader sees a
partial one. -/
def write (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let tmp := System.FilePath.mk s!"{path}.tmp.{← IO.Process.getPID}"
  try
    IO.FS.writeBinFile tmp bytes
    IO.FS.rename tmp path
  finally
    if ← tmp.pathExists then IO.FS.removeFile tmp

end Aiur.Artifact
