import Compilatrix.Tools.Check

/-! Fresh compiler and upstream-machine processes, exact reviewed artifacts,
strict malformed-byte rejection, and the complete vendored source inventory. -/

open Lean System Compilatrix.Tools.Check

private def inventory (root : FilePath) : IO (List String) := do
  let root ← IO.FS.realPath root
  return ((← files root).map fun path =>
    (path.toString.drop (root.toString.length + 1)).toString).mergeSort (· ≤ ·)

private def same (first second : FilePath) : IO Unit := do
  need ((← IO.FS.readBinFile first) == (← IO.FS.readBinFile second)) s!"Ixby artifact drift: {first}"

private def u32 (bytes : ByteArray) (offset : Nat) : Nat :=
  (List.range 4).foldr (fun i n => n * 256 + bytes[offset + i]!.toNat) 0

private def leb (bytes : ByteArray) : Nat → Nat → IO (Nat × Nat)
  | 0, _ => throw (IO.userError "unterminated source natural")
  | fuel + 1, offset => do
    need (offset < bytes.size) "truncated source natural"
    let byte := bytes[offset]!.toNat
    if byte < 128 then return (byte, offset + 1)
    let (high, next) ← leb bytes fuel (offset + 1)
    return (byte % 128 + high * 128, next)

/-- Independently inspect the current header and constructor ABI. Addresses
remain fixed-width; table counts, members, tags and arities use LEB128. -/
private def constructorABI (directory : FilePath) : IO Unit := do
  let image ← IO.FS.readBinFile (directory / "program.ixby")
  let source ← readJson (directory / "source.json")
  let domain := "compilatrix/ixir0/decl/1".toUTF8.push 0
  let mut constructors := []
  for decl in ← arrField source "declarations" do
    let bytes ← checked (unhex (← strField decl "bytes"))
    need (bytes.extract 0 domain.size == domain) "source declaration domain differs"
    if bytes[domain.size]? == some 1 then
      let address ← checked (unhex (← strField decl "address"))
      let (tag, next) ← leb bytes bytes.size (domain.size + 1)
      let (arity, finish) ← leb bytes bytes.size next
      need (finish == bytes.size) "constructor source payload has trailing bytes"
      constructors := constructors ++ [(address, tag, arity)]
  need (image.extract 0 4 == "IXBF".toUTF8 && u32 image 4 == 1 && u32 image 8 == 2)
    "Ixby current header differs"
  let mut offset := 12
  for _ in [:12] do
    let (_, next) ← leb image image.size offset
    offset := next
  let (count, next) ← leb image image.size offset
  offset := next
  need (count == constructors.length + 4) "Ixby constructor table count differs"
  for i in [:4] do
    let block := image.extract offset (offset + 32)
    let (member, next) ← leb image image.size (offset + 32)
    let (tag, next) ← leb image image.size next
    let (arity, next) ← leb image image.size next
    offset := next
    need (block == ⟨Array.replicate 32 0⟩ && member == 1 && tag == i &&
      arity == (if i == 0 then 0 else 1)) "Ixby private box ABI differs"
  for (address, tag, arity) in constructors do
    let block := image.extract offset (offset + 32)
    let (actualMember, next) ← leb image image.size (offset + 32)
    let (actualTag, next) ← leb image image.size next
    let (actualArity, next) ← leb image image.size next
    offset := next
    need (block == address && actualMember == 0 && actualTag == tag && actualArity == arity)
      "Ixby source constructor address/tag/arity changed at byte export"

private def vendor (root : FilePath) : IO Unit := do
  let directory := root / "vendor/ixby"
  let pin ← readJson (directory / "upstream.json")
  need ((← strField pin "revision") == "6836a77c3f432c83c42428490e56811f4a69808d") "Ixby revision drifted"
  need (match pin.getObjVal? "file_revisions" with | .error _ => true | .ok _ => false)
    "Ixby files must all use the pinned runtime revision"
  need ((← strField pin "repository") == "https://github.com/argumentcomputer/ix" &&
    (← strField pin "branch") == "jcb/ixby") "Ixby upstream identity drifted"
  let hashes ← pairs (← field pin "unchanged_files_sha256")
  need (hashes.length == 15) "Ixby upstream file count changed"
  for (path, digest) in hashes do
    let actual := (words (← run "sha256sum" #[(directory / path).toString])).headD ""
    need (actual == (← string digest)) s!"vendored Ixby source differs: {path}"
  let locals ← (← arrField pin "local_files").toList.mapM string
  need ((← inventory directory) == ((hashes.map (·.1)) ++ locals).mergeSort (· ≤ ·))
    "Ixby vendored inventory differs"

private def runImage (runner : String) (directory output : FilePath) (fuel : String := "100000") : IO Unit := do
  let _ ← run runner #[(directory / "profile.ixfp").toString, (directory / "program.ixby").toString,
    (directory / "input.ixbi").toString, output.toString, fuel]
  same (directory / "output.ixbo") output

private def mutate (runner : String) (directory output : FilePath) (name : String)
    (change : ByteArray → ByteArray) : IO Unit := do
  let file := directory / name
  let original ← IO.FS.readBinFile file
  try
    IO.FS.writeBinFile file (change original)
    let result ← IO.Process.output { cmd := runner, args := #[
      (directory / "profile.ixfp").toString, (directory / "program.ixby").toString,
      (directory / "input.ixbi").toString, output.toString, "100000"] }
    need (result.exitCode == 1 && result.stderr.contains "ixby-run:" && !(← output.pathExists))
      s!"Ixby corrupted artifact was not rejected: {name}"
  finally IO.FS.writeBinFile file original

def main (args : List String) : IO UInt32 := cli "Ixby check failed" do
  let args ← checked (parseArgs ["--fixture", "--runner", "--compiler", "--root", "--expected", "--upstream"] args)
  let fixture ← present (optional args "--fixture") "--fixture required"
  let runner ← present (optional args "--runner") "--runner required"
  let compiler ← present (optional args "--compiler") "--compiler required"
  let root : FilePath := option args "--root" "."
  let upstream : FilePath := option args "--upstream" "fixtures/ixon-upstream"
  vendor root
  let expected ← readJson (option args "--expected" "fixtures/ixby/expected.json")
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      requireAll (← run fixture #[output.toString, upstream.toString])
        ["source-ixby ok: 33 cases, 270 generated, 29 rejections"] "Ixby source matrix"
      need ((← readJson (output / "report.json")) == expected) "reviewed Ixby report drifted"
    let paths ← inventory first
    need (paths == (← inventory second)) "Ixby artifact inventory differs across processes"
    for path in paths do same (first / path) (second / path)
    let mut wireCases := 0
    let mut mutations := 0
    for row in ← arrField expected "cases" do
      if (← field row "wire") != Json.null then
        let name ← strField row "name"
        let program := first / name
        constructorABI program
        runImage runner program (directory / s!"{name}.ixbo")
        for (file, change) in [
            ("program.ixby", fun bytes : ByteArray => bytes.push 0),
            ("program.ixby", fun bytes : ByteArray => bytes.extract 0 (bytes.size - 1)),
            ("program.ixby", fun bytes : ByteArray => bytes.set! 4 0),
            ("program.ixby", fun bytes : ByteArray => bytes.set! 8 255),
            ("input.ixbi", fun bytes : ByteArray => bytes.push 0),
            ("input.ixbi", fun bytes : ByteArray => bytes.extract 0 (bytes.size - 1)),
            ("profile.ixfp", fun bytes : ByteArray => bytes.set! 12 1)] do
          mutate runner program (directory / s!"bad-{mutations}.ixbo") file change
          mutations := mutations + 1
        wireCases := wireCases + 1
    for (name, main) in [
        ("applyClosed", "b81b754f02c1b63279a609ab4b55b609fd6f87fab7b14879f4021c3327c2eb40"),
        ("captureClosed", "5628cfe1b4f959fb116661fc50ae8e9e4bfa470ac5d0e639a75b9d23aed12953"),
        ("letClosed", "6c737171f1a3c482ba96cbe4998ea660fda824c578fe668ab9fdc4aae1b9754f")] do
      let catalog := directory / s!"{name}.ixc"
      IO.FS.createDirAll catalog
      IO.FS.writeBinFile (catalog / "manifest") (← checked (unhex (← IO.FS.readFile (upstream / s!"{name}.manifest.hex"))))
      IO.FS.writeBinFile (catalog / s!"CompilatrixUpstream.{name}.ixe")
        (← checked (unhex (← IO.FS.readFile (upstream / s!"{name}.ixe.hex"))))
      let output := directory / s!"compiled-{name}"
      let _ ← run compiler #[catalog.toString, main, output.toString]
      for file in ["program.ixby", "profile.ixfp", "source.json", "program.txt"] do
        same (first / s!"upstream-{name}" / file) (output / file)
    IO.println s!"Ixby check ok: 33 cases, 270 generated, 29 rejections, {wireCases} canonical runs, {mutations} byte mutations, 3 catalog compilations"
