module
public import Ix.Store
public import Aiur.SourceBundle
public import Ix.FormalProver

/-! The certified Aiur programs `ix` runs and generates code for: where
their sources and the compiled-program cache are, how a command obtains
them (from the cache, or by compiling misses concurrently with the linked
compiler), the check of the linked native executors, and the generated
sources `lake build ix` compiles into `ix` (`writeGenerated`). -/
public section
namespace Ix.Cli.FormalAiur

/-- Run `act`; with `IX_PHASE_TIMES` set, report its wall time on stderr. The
work is a thunk so that pure computations run inside the measured interval. -/
def phase {α : Type} (label : String) (act : Unit → IO α) : IO α := do
  if (← IO.getEnv "IX_PHASE_TIMES").isNone then return ← act ()
  let start ← IO.monoNanosNow
  let result ← act ()
  let finish ← IO.monoNanosNow
  IO.eprintln s!"[phase] {label}: {(finish - start) / 1000000} ms (ended at {finish / 1000000} ms)"
  return result

/-- The checkout this `ix` belongs to. The default backend's sources and the
frontend's build live there, so commands work from any directory.
`IX_ROOT` overrides it; otherwise an executable at `<root>/.lake/build/bin`
identifies it, falling back to the working directory. -/
def repoRoot : IO System.FilePath := do
  if let some root ← IO.getEnv "IX_ROOT" then return root
  let app ← IO.appPath
  let root := do
    let bin ← app.parent
    let build ← bin.parent
    let lake ← build.parent
    lake.parent
  if let some root := root then
    if ← (root / "IxVM" / "lakefile.lean").pathExists then return root
  return "."

/-- A program a command selected, in the registry that prepares its system. -/
structure Selected where
  registry : FormalProver.Registry
  program : FormalProver.Program
  /-- The artifact file it was loaded from or persisted to. -/
  path : String

/-- Load the trusted binary artifact at `path` into `registry`. -/
def Selected.load (registry : FormalProver.Registry) (path : String) : IO Selected := do
  return { registry, program := ← registry.loadBinary path, path }

/-- The program's system under the default STARK parameters, prepared once
per registry. -/
def Selected.system (s : Selected) : IO FormalProver.System :=
  s.registry.system s.program {}

/-- A certified program the linked compiler builds: the trusted artifact
flag and variable that select a file instead, its name, target and source
bundle relative to the checkout. -/
structure Certified where
  flag : String
  env : String
  name : String
  target : FormalProver.Target
  sourcePath : String

/-- IxVM's claim verifier (`IxVM::verify_claim`). -/
def ixvmProgram : Certified :=
  ⟨"aiur-artifact", "IX_AIUR_ARTIFACT", "ixvm", .ixvm, "IxVM/IxVM/Program.sources"⟩

/-- The recursive verifier (`MultiStark::verify_multi_stark_proof`). -/
def verifierProgram : Certified :=
  ⟨"verifier-artifact", "IX_VERIFIER_ARTIFACT", "verifier", .verifier,
    "MultiStark/MultiStark/Program.sources"⟩

/-- The aggregation program (`MultiStark::ix_aggr`). -/
def aggregationProgram : Certified :=
  ⟨"aggr-artifact", "IX_AGGR_ARTIFACT", "aggregation", .aggregation,
    "MultiStark/MultiStark/Aggregate.sources"⟩

/-- The compiled-program cache: `IX_AIUR_CACHE`, or `~/.ix/cache/aiur`.
Checkouts on one machine share it; see `compiledArtifacts`. -/
def programCache : IO System.FilePath := do
  if let some directory ← IO.getEnv "IX_AIUR_CACHE" then
    IO.FS.createDirAll directory
    return directory
  StoreIO.toIO (Store.cacheDir "aiur")

/-- The source bundle text of `c` in the checkout `root`, and its digest. -/
def Certified.source (c : Certified) (root : System.FilePath) : IO (String × Address) := do
  let path := root / c.sourcePath
  let text ← if path.extension == some "sources" then Aiur.SourceBundle.read path
    else IO.FS.readFile path
  return (text, Address.blake3 text.toUTF8)

/-- Under `IX_FORMAL_NATIVE=1`, require that the linked native executor of
`c` was generated from exactly the selected program; otherwise report a
stale executor once. A stale executor is never used: the program runs on
the interpreter, which produces identical records and proofs. -/
def checkExecutor (c : Certified) (s : Selected) : IO Unit := do
  if (← IO.getEnv "IX_PROVER_EXECUTOR") == some "interpreter" then return
  let (executor, fingerprint) ← s.program.executor
  if executor == s!"native-{c.name}" then return
  let message := s!"the linked native {c.name} executor was generated from a different \
    program than {s.path} (native fingerprint {fingerprint}), so it runs on the interpreter. \
    Rebuild `ix` (`lake build ix`) to generate it for the current programs."
  if (← IO.getEnv "IX_FORMAL_NATIVE") == some "1" then
    throw (IO.userError s!"IX_FORMAL_NATIVE=1: {message}")
  IO.eprintln s!"[aiur] {message}"

/-- Certified programs, in order: each is the trusted artifact `explicit`
names, or otherwise the linked
compiler's output for the checkout's source bundle. That output is cached
in `programCache` as one binary artifact per program, named by a lookup key
derived from the artifact format version, the compiler's identity, the
program and the source digest, so checkouts with the same compiler and
sources share a file, and others, and files of another format version, are
never looked up. Misses compile in process, concurrently, hand their images
to the prover directly and persist each program atomically. A cached
artifact that does not load is an error, never a silent recompile: the
checksum a load verifies detects corruption, and trust in a cached artifact
rests on its key naming this compiler and source. With `checkExecutors`,
each program's linked native executor is checked (`checkExecutor`). -/
def compiledPrograms (registry : FormalProver.Registry) (programs : Array Certified)
    (explicit : Certified → IO (Option String) := fun _ => pure none)
    (checkExecutors := true) : IO (Array Selected) := do
  let root ← repoRoot
  let mut found : Array (Option Selected) := #[]
  let mut misses : Array (Nat × Certified × System.FilePath × Address × FormalProver.CompileJob) := #[]
  let mut compiler : Option FormalProver.Compiler := none
  let format ← FormalProver.artifactVersion
  for c in programs do
    if let some path ← explicit c then
      found := found.push (some (← Selected.load registry path))
      continue
    let linked ← match compiler with
      | some linked => pure linked
      | none => FormalProver.compiler
    compiler := some linked
    let (text, source) ← c.source root
    let key := Address.blake3
      (s!"ix-formal-artifact/2\x00{format}\x00{linked.identity}\x00{c.name}\x00".toUTF8 ++
        source.hash)
    let path := (← programCache) / s!"{c.name}-{key}.aiur"
    if ← path.pathExists then
      let selected ← try Selected.load registry path.toString
        catch e => throw (IO.userError s!"the cached {c.name} program {path} cannot be \
          loaded: {e}. Delete it to compile the program again.")
      found := found.push (some selected)
    else
      misses := misses.push (found.size, c, path, source, { target := c.target, source := text, key := key.hash })
      found := found.push none
  if let some linked := compiler then
    unless misses.isEmpty do
      let names := ", ".intercalate (misses.map (·.2.1.name)).toList
      IO.eprintln s!"[aiur] compiling the certified {names} program{if misses.size == 1 then "" else "s"} \
        in process{if misses.size == 1 then "" else ", concurrently"}; this takes several minutes \
        once per source revision and compiler, and later commands load the result from \
        {← programCache}"
      let compiled ← phase s!"compile {names}" fun _ =>
        linked.compile registry root.toString (misses.map (·.2.2.2.2))
      for (i, c, path, source, _) in misses, program in compiled do
        program.save path.toString c.name linked.identity source.hash
        found := found.set! i (some { registry, program, path := path.toString })
  let selected ← found.mapM fun s => match s with
    | some s => pure s
    | none => throw (IO.userError "missing compiled program")
  if checkExecutors then
    for c in programs, s in selected do checkExecutor c s
  return selected

/-- Write the generated sources of `programs` under `directory`: each
program's native executor, and with `cuda` its trace writers. A file is
rewritten only when its contents change, so Cargo recompiles only what
changed; files that are no longer generated, CUDA output in a CPU build
included, are removed. -/
def writeGenerated (programs : Array Certified) (selected : Array Selected)
    (directory : System.FilePath) (cuda : Bool) : IO Unit := do
  let root ← repoRoot
  let mut expected : Array System.FilePath := #[]
  for c in programs, s in selected do
    let (_, source) ← c.source root
    let files ← s.program.codegen c.name source.hash cuda
    let (executor, fingerprint) ← s.program.executor
    let bytes := files.foldl (fun n (_, contents) => n + contents.utf8ByteSize) 0
    IO.println s!"{c.name} artifact {s.path}"
    IO.println s!"{c.name} native fingerprint {fingerprint}; linked executor {executor}"
    IO.println s!"{c.name} generated {files.size} files, {bytes} bytes"
    for (relative, contents) in files do
      let path := directory / relative
      expected := expected.push path
      let existing ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
      unless existing == some contents do
        if let some parent := path.parent then IO.FS.createDirAll parent
        let temporary := path.addExtension "tmp"
        IO.FS.writeFile temporary contents
        IO.FS.rename temporary path
  for sub in #["native", "cuda"] do
    let dir := directory / sub
    if ← dir.isDir then
      for entry in ← dir.walkDir do
        unless (← entry.isDir) || expected.contains entry do IO.FS.removeFile entry
  let cudaDir := directory / "cuda"
  if !cuda && (← cudaDir.isDir) then IO.FS.removeDirAll cudaDir

end Ix.Cli.FormalAiur
