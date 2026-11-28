import IxCC.Compile
import IxCC.Cli
import IxCC.Exe.Cert
import IxCCTests.Corpus.Manifest

/-! # `tests-pure-compile`: `Compile.compile` is a function of its three arguments

`IxCC.Compile.compile envBytes target opts` is a Lean function, so in the logic it
has one value. This suite is the evidence that the compiled function behaves so,
and that it is the compiler the command line already runs:

* **Twice in one process.** Every case is compiled twice (two separate
  evaluations, `compileRun 0` and `compileRun 1`) and the two outputs compared:
  the executable's bytes, the certificate's text, every field of the claim; or the
  refusal.
* **Again in another process, in another environment.** The executable runs itself
  (`--child`) with a different working directory, with `IX_KERNEL_*`, `IX_BIGNAT_LIB`,
  `IX_BIN`, `LEAN_NUM_THREADS`, `TZ`, `LANG` and `HOME` set to values that would
  change or break a compile that read them, and at other addresses (the loader's
  randomization), and what it writes is compared with the output of this process.
* **Against the command line**, where the comparison is like for like:
  `ixcc compile CLOSURE --root <address> --rc MODE --exe F -o O --emit-cert C`
  (in process, `IxCC.Cli.main`) writes the same executable, an object with the
  claim's digest, and the same certificate text; and
  `ixcc compile … --exe F --embed-cert` writes exactly the returned executable
  with the `.ix.cert` v1 trailer made from what `compile` and `check` return
  (`package`), which `Exe.Cert.verifyExeBytes` accepts for the claim's six-field
  projection (`Claim.legacy`). So the developer path loses nothing. `compile` runs the
  verifier's seed-closure check itself, so the verifier accepts every packaged file; were it
  to refuse one, `--embed-cert` (which runs it before writing) would exit 3 and write nothing.
* **Not like for like, reported and not required equal**: the command line with the
  fixture's `--equations` sidecar and its root's name. The hints then come from the
  sidecar instead of the environment, and the root has another name.
* **Options.** `workers` changes nothing but the claim's record of it; a layout
  changes the executable as the command line's `--stack` and `--region` do; a
  target that is no constant of the environment is refused the same way twice.

The cases: every root of the K1 benchmark closures (`fixtures/ixon-v4/bench-k1`)
under `off`, `on` and `auto`, and every `step`-th root of the other registered
corpus families under `off` and `auto` (the machines family as machines).

`tests-pure-compile [--step N] [--only LABEL-PREFIX]`. -/

set_option autoImplicit false

namespace IxCCTests.Compile

open IxCC IxCC.Recheck System

def fail (r : IO.Ref Nat) (msg : String) : IO Unit := do
  r.modify (· + 1)
  IO.eprintln s!"FAIL {msg}"

def expect (r : IO.Ref Nat) (ok : Bool) (msg : String) : IO Unit := unless ok do fail r msg

/-- One evaluation of `Compile.compile`. Two calls with different `run` are two
applications the compiler cannot share. -/
@[noinline] def compileRun (run : Nat) (bytes : ByteArray) (target : Ixon.Address)
    (opts : Compile.Options) : Nat × Except Err Compile.Output :=
  (run, Compile.compile bytes target opts)

/-- An output or a refusal, as what is compared. -/
structure Result where
  exe : ByteArray := .empty
  cert : String := ""
  claim : String := ""
  error : String := ""
  deriving BEq

def Result.of : Except Err Compile.Output → Result
  | .ok out => { exe := out.exe, cert := out.cert, claim := reprStr out.claim }
  | .error e => { error := e.render }

def Result.describe (x : Result) : String :=
  if x.error.isEmpty then
    s!"executable {x.exe.size} bytes (blake3 {Ixon.Address.blake3Pure x.exe}), certificate {x.cert.utf8ByteSize} bytes"
  else s!"refused: {x.error}"

def modeName : Compile.Rc → String
  | .off => "off" | .on => "on" | .auto => "auto"

def modeOf : String → Option Compile.Rc
  | "off" => some .off | "on" => some .on | "auto" => some .auto | _ => none

def kindName : X86.Exe.Cert.ExeKind → String
  | .plain => "plain" | .machine => "machine"

def kindOf : String → Option X86.Exe.Cert.ExeKind
  | "plain" => some .plain | "machine" => some .machine | _ => none

/-- One case: a closure, a target in it, and the executable's kind. -/
structure Case where
  label : String
  closure : FilePath
  target : Ixon.Address
  kind : X86.Exe.Cert.ExeKind := .plain
  /-- The fixture's sidecar and the root's name there (for the comparison that is
  not like for like). -/
  equations : Option FilePath := none
  root : String := ""

/-- The roots of a manifest, every `step`-th from `start`. -/
def familyCases (path : FilePath) (start step : Nat) (kind : X86.Exe.Cert.ExeKind := .plain) :
    IO (Array Case) := do
  let m ← IxCCTests.Corpus.Family.read path
  let dir : FilePath := m.directory
  let mut out := #[]
  let mut i := 0
  for f in m.fixtures do
    for r in f.roots do
      if i ≥ start && (i - start) % step == 0 then
        match Ixon.Address.fromString r.address with
        | some target =>
          out := out.push { label := s!"{m.family}/{f.name}/{r.name}", closure := dir / f.closure.path
                            target, kind, equations := some (dir / f.equations.path), root := r.name }
        | none => throw (IO.userError s!"{path}: root {r.name} has no address")
      i := i + 1
  return out

def k1Manifest : FilePath := "fixtures/ixon-v4/bench-k1/corpus.json"

def machinesManifest : FilePath := "fixtures/corpus/phase1-machines/corpus.json"

/-! ## The other process -/

/-- The environment of the other process: every variable a compile on the command
line reads, and some a careless one might, set to values that would change or break
a compile that read them. -/
def childEnv : Array (String × Option String) :=
  #[("IX_KERNEL_MAX_RECORDS", some "1"), ("IX_KERNEL_MAX_BLOBS", some "1"),
    ("IX_KERNEL_MAX_TOTAL_BYTES", some "1"), ("IX_KERNEL_MAX_RECORD_BYTES", some "1"),
    ("IX_KERNEL_MAX_RECORD_UNIV_NODES", some "1"), ("IX_KERNEL_MAX_DEPTH", some "1"),
    ("IX_KERNEL_WORKERS", some "3"), ("IX_KERNEL_LEVEL_BUDGET", some "1"),
    ("IX_BIGNAT_LIB", some "/nonexistent/bignat.json"), ("IX_BIGNAT_ENTRY", some "/nonexistent/Entry.lean"),
    ("IX_BIN", some "/nonexistent/ix"), ("IXCC_REEXEC", some "0"), ("LEAN_NUM_THREADS", some "3"),
    ("TZ", some "Pacific/Kiritimati"), ("LANG", some "tr_TR.UTF-8"), ("LC_ALL", some "tr_TR.UTF-8"),
    ("HOME", some "/nonexistent"), ("PATH", some "/nonexistent")]

/-- `--child CLOSURE TARGET MODE KIND STACK REGION DIR`: compile and write the output
(`exe`, `cert`, `claim`) or the refusal (`error`) into `DIR`. -/
def child (closure target mode kind stack region dir : String) : IO UInt32 := do
  let some target := Ixon.Address.fromString target | throw (IO.userError "child: target")
  let some rc := modeOf mode | throw (IO.userError "child: mode")
  let some kind := kindOf kind | throw (IO.userError "child: kind")
  let some stack := stack.toNat? | throw (IO.userError "child: stack")
  let some region := region.toNat? | throw (IO.userError "child: region")
  let bytes ← IO.FS.readBinFile closure
  let dir : FilePath := dir
  match Compile.compile bytes target { rc, kind, layout := { stack, region } } with
  | .ok out =>
    IO.FS.writeBinFile (dir / "exe") out.exe
    IO.FS.writeFile (dir / "cert") out.cert
    IO.FS.writeFile (dir / "claim") (reprStr out.claim)
  | .error e => IO.FS.writeFile (dir / "error") e.render
  return 0

/-- The other process's result for a case. -/
def inChild (work : FilePath) (c : Case) (opts : Compile.Options) : IO Result := do
  let dir := work / "child"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll dir
  let closure ← IO.FS.realPath c.closure
  let out ← IO.Process.output {
    cmd := (← IO.appPath).toString
    args := #["--child", closure.toString, toString c.target, modeName opts.rc, kindName opts.kind,
              toString opts.layout.stack, toString opts.layout.region, (← IO.FS.realPath dir).toString]
    cwd := some dir, env := childEnv }
  if out.exitCode != 0 then
    return { error := s!"the other process exited {out.exitCode}: {out.stderr}" }
  if ← (dir / "error").pathExists then
    return { error := ← IO.FS.readFile (dir / "error") }
  return { exe := ← IO.FS.readBinFile (dir / "exe"), cert := ← IO.FS.readFile (dir / "cert")
           claim := ← IO.FS.readFile (dir / "claim") }

/-! ## The command line -/

/-- `ixcc` in process: the exit code. -/
def ixcc (args : List String) : IO UInt32 := IxCC.Cli.main args

def layoutArgs (opts : Compile.Options) : List String :=
  let d : X86.Exe.Layout := {}
  if opts.layout.stack == d.stack && opts.layout.region == d.region then []
  else ["--stack", toString opts.layout.stack, "--region", toString opts.layout.region]

def kindArgs (opts : Compile.Options) : List String :=
  match opts.kind with
  | .plain => []
  | .machine => ["--machine"]

/-- **The developer path's file from what `compile` returns**: the returned
executable with the `.ix.cert` v1 trailer whose payload is the claim's six-field
projection, the returned certificate text, the environment's bytes and the derived
hints as a sidecar (`Exe.Cert.buildCertifiedExe`'s payload, without rebuilding the
executable). -/
def package (envBytes : ByteArray) (target : Ixon.Address) (opts : Compile.Options) :
    Except Err (Compile.Output × ByteArray × ByteArray) := do
  let c ← Compile.check envBytes target opts
  let out ← Compile.build target opts c
  let payload : X86.Exe.Cert.Payload := {
    exeKind := opts.kind
    stack := opts.layout.stack
    region := opts.layout.region
    rootNames := c.inp.names
    claimBytes := out.claim.legacy.toClaimBytes
    certBytes := out.cert.toUTF8
    envBytes
    eqBytes := (Src.Hints.toK1Json c.inp.hints).compress.toUTF8 }
  let file ← (X86.Exe.Cert.attachTrailer out.exe payload.encode).mapError fun e =>
    Exe.err "exe.cert.attach" e.render
  pure (out, payload.encode, file)

/-- The first offset at which two byte arrays differ (`none` if one is a prefix of the other). -/
def firstDiff (a b : ByteArray) : Option Nat := Id.run do
  for i in [0:min a.size b.size] do
    if a.get! i != b.get! i then return some i
  return none

/-- The number of offsets at which two byte arrays of one size differ. -/
def diffCount (a b : ByteArray) : Nat := Id.run do
  let mut n := 0
  for i in [0:min a.size b.size] do
    if a.get! i != b.get! i then n := n + 1
  return n

/-- What the suite counted. -/
structure Counts where
  cases : Nat := 0
  compiled : Nat := 0
  refused : Nat := 0
  twice : Nat := 0
  children : Nat := 0
  cli : Nat := 0
  embedded : Nat := 0
  verified : Nat := 0
  /-- `compile` refused at the seed-closure check (`ingress: kf4`). -/
  seedClosureRefused : Nat := 0
  /-- Of those, the command line (which runs that check only under `--embed-cert`) compiled. -/
  cliWithoutSeedClosure : Nat := 0
  sidecarSame : Nat := 0
  sidecarDiffers : Nat := 0
  sidecarOnlyOne : Nat := 0

/-- One case under one option set: twice here, once in the other process, and
against the command line. -/
def runCase (r : IO.Ref Nat) (n : IO.Ref Counts) (work : FilePath) (c : Case) (opts : Compile.Options)
    (withChild withEmbed withSidecar : Bool) : IO Result := do
  let tag := s!"{c.label} [{kindName opts.kind}, rc {modeName opts.rc}]"
  let bytes ← IO.FS.readBinFile c.closure
  n.modify fun k => { k with cases := k.cases + 1 }
  -- twice in this process
  let t0 ← IO.monoMsNow
  let (_, first) ← IO.lazyPure fun _ => compileRun 0 bytes c.target opts
  let t1 ← IO.monoMsNow
  let (_, second) ← IO.lazyPure fun _ => compileRun 1 bytes c.target opts
  let t2 ← IO.monoMsNow
  let a := Result.of first
  let b := Result.of second
  expect r (a == b) s!"{tag}: two evaluations differ: {a.describe} / {b.describe}"
  n.modify fun k => { k with twice := k.twice + 1 }
  if a.error.isEmpty then n.modify fun k => { k with compiled := k.compiled + 1 }
  else n.modify fun k => { k with refused := k.refused + 1 }
  IO.println s!"  {tag}: {a.describe} ({t1 - t0} ms, again {t2 - t1} ms)"
  -- the claim's digest is the file's
  if let .ok out := first then
    expect r (Ixon.Address.blake3Pure out.exe == out.claim.exe) s!"{tag}: the claim's digest is not the executable's"
    expect r (out.claim.target == c.target) s!"{tag}: the claim's target is not the target"
  -- in the other process
  if withChild then
    let other ← inChild work c opts
    expect r (other == a) s!"{tag}: the other process differs: {other.describe}"
    n.modify fun k => { k with children := k.children + 1 }
  -- the command line, like for like: the root by address, no sidecar
  let exe := work / "cli.exe"
  let obj := work / "cli.o"
  let cert := work / "cli.cert"
  for f in [exe, obj, cert] do
    if ← f.pathExists then IO.FS.removeFile f
  let base := ["compile", c.closure.toString, "--root", toString c.target, "--rc", modeName opts.rc]
  let code ← ixcc (base ++ ["--exe", exe.toString, "-o", obj.toString, "--emit-cert", cert.toString] ++
    kindArgs opts ++ layoutArgs opts)
  n.modify fun k => { k with cli := k.cli + 1 }
  match first with
  | .error e =>
    if e.code == "kf4" then
      n.modify fun k => { k with seedClosureRefused := k.seedClosureRefused + 1 }
      IO.println s!"    compile refuses at the seed-closure check: {e.message}"
      if code == 0 then
        n.modify fun k => { k with cliWithoutSeedClosure := k.cliWithoutSeedClosure + 1 }
        IO.println s!"    the command line, which runs that check only under --embed-cert, compiles"
    else
      expect r (code != 0) s!"{tag}: compile refuses ({e.render}) and the command line exits 0"
  | .ok out =>
    expect r (code == 0) s!"{tag}: compile succeeds and the command line exits {code}"
    if code == 0 then
      let cliExe ← IO.FS.readBinFile exe
      expect r (cliExe == out.exe)
        s!"{tag}: the command line's executable differs ({cliExe.size} bytes, first difference at \
          {firstDiff cliExe out.exe})"
      expect r (Ixon.Address.blake3Pure (← IO.FS.readBinFile obj) == out.claim.object)
        s!"{tag}: the command line's object does not have the claim's object digest"
      expect r ((← IO.FS.readFile cert) == out.cert) s!"{tag}: the command line's certificate text differs"
  -- the developer path: the trailer made from what compile returns
  if withEmbed then
    if let .ok out := first then
      let emb := work / "cli.embedded"
      if ← emb.pathExists then IO.FS.removeFile emb
      let code ← ixcc (base ++ ["--exe", emb.toString, "--embed-cert"] ++ kindArgs opts ++ layoutArgs opts)
      match package bytes c.target opts with
      | .error e => fail r s!"{tag}: package: {e.render}"
      | .ok (out', payload, file) =>
        expect r (out'.exe == out.exe && out'.cert == out.cert) s!"{tag}: check then build is not compile"
        -- `--embed-cert` runs verify-exe's verifier on the bytes before it writes them and rejects
        -- (exit 3, nothing written) when it refuses; so it writes this suite's packaged file
        -- exactly when the verifier below accepts it
        let verdict := Exe.Cert.verifyExeBytes file none none opts.kernelLimits
        if verdict.isOk then
          expect r (code == 0) s!"{tag}: verify-exe accepts the packaged file and the command line's --embed-cert exits {code}"
        else
          expect r (code == 3 && !(← emb.pathExists))
            s!"{tag}: verify-exe refuses the packaged file and the command line's --embed-cert exits {code} \
              (expected 3, with nothing written)"
        if code == 0 then
          let cliFile ← IO.FS.readBinFile emb
          expect r (cliFile == file)
            s!"{tag}: the command line's --embed-cert file differs from the packaged output ({cliFile.size} \
              and {file.size} bytes, first difference at {firstDiff cliFile file})"
        -- what `IxCCCorrect.binds_packaged` asks of a packaging
        expect r (X86.Exe.Cert.checkTrailer out.exe payload file) s!"{tag}: checkTrailer refuses the packaged file"
        match X86.Exe.Cert.extractTrailer file with
        | .ok (coreSize, payload') =>
          expect r (coreSize == out.exe.size && payload' == payload)
            s!"{tag}: the strict parser reads another core size or payload"
          expect r (X86.Exe.Cert.zeroShdr (file.extract 0 coreSize) == out.exe)
            s!"{tag}: the core under the trailer is not the returned executable"
        | .error e => fail r s!"{tag}: extractTrailer: {e.render}"
        -- `verify-exe` on the packaged file (the command line's own, byte for byte, when it wrote
        -- one): it must accept every file `compile` returns, the seed-closure check
        -- (`exe.cert.kf4`) included, which `compile` runs too.
        match verdict with
        | .ok v =>
          expect r (v.claim == out.claim.legacy) s!"{tag}: verify-exe reads another claim"
          expect r (v.exeKind == opts.kind && v.layout == opts.layout) s!"{tag}: verify-exe reads another kind or layout"
          n.modify fun k => { k with verified := k.verified + 1 }
        | .error e => fail r s!"{tag}: verify-exe refuses the packaged output: {e.render}"
        n.modify fun k => { k with embedded := k.embedded + 1 }
  -- not like for like: the sidecar's hints and the root's name
  if withSidecar then
    if let some eqs := c.equations then
      let side := work / "cli.sidecar"
      if ← side.pathExists then IO.FS.removeFile side
      let code ← ixcc (["compile", c.closure.toString, "--equations", eqs.toString, "--root", c.root,
        "--rc", modeName opts.rc, "--exe", side.toString] ++ kindArgs opts ++ layoutArgs opts)
      match first, code == 0 with
      | .ok out, true =>
        let sideExe ← IO.FS.readBinFile side
        if sideExe == out.exe then n.modify fun k => { k with sidecarSame := k.sidecarSame + 1 }
        else
          n.modify fun k => { k with sidecarDiffers := k.sidecarDiffers + 1 }
          let same := sideExe.size == out.exe.size
          IO.println s!"    with the sidecar: another executable ({sideExe.size} bytes against {out.exe.size}\
            {if same then s!", {diffCount sideExe out.exe} bytes differ" else ""}, first difference at \
            {firstDiff sideExe out.exe})"
      | .error _, false => pure ()
      | .ok _, false =>
        n.modify fun k => { k with sidecarOnlyOne := k.sidecarOnlyOne + 1 }
        IO.println s!"    with the sidecar: the command line declines (exit {code}); compile succeeds"
      | .error e, true =>
        n.modify fun k => { k with sidecarOnlyOne := k.sidecarOnlyOne + 1 }
        IO.println s!"    with the sidecar: the command line compiles; compile refuses ({e.render})"
  return a

/-- **Options**: `workers`, a layout, and a target outside the environment. -/
def optionControls (r : IO.Ref Nat) (work : FilePath) (c : Case) : IO Unit := do
  let bytes ← IO.FS.readBinFile c.closure
  let opts : Compile.Options := {}
  let base := Result.of (compileRun 0 bytes c.target opts).2
  expect r base.error.isEmpty s!"{c.label}: the control case does not compile: {base.error}"
  -- workers: the kernel's second phase on the calling thread, or on at most two tasks
  for w in [some 0, some 2] do
    let o : Compile.Options := { opts with kernelLimits := { opts.kernelLimits with workers := w } }
    let x := Result.of (compileRun 2 bytes c.target o).2
    expect r (x.exe == base.exe && x.cert == base.cert && x.error.isEmpty)
      s!"{c.label}: workers {w} changes the executable or the certificate"
    expect r (x.claim != base.claim) s!"{c.label}: workers {w} is not in the claim"
  IO.println s!"  {c.label}: workers 0 and 2 give the executable and the certificate of the default (the claim records them)"
  -- a layout: another file, the command line's --stack and --region
  let small : Compile.Options := { opts with layout := { stack := 1 <<< 20, region := 4 <<< 20 } }
  let n ← IO.mkRef ({} : Counts)
  let x ← runCase r n work c small true true false
  expect r (x.exe != base.exe && x.cert == base.cert)
    s!"{c.label}: a smaller layout does not change the executable, or changes the certificate"
  -- a kernel limit below the environment: declined, the same way twice
  let tight : Compile.Options := { opts with kernelLimits := { opts.kernelLimits with maxRecords := 1 } }
  let t1 := Result.of (compileRun 3 bytes c.target tight).2
  let t2 := Result.of (compileRun 4 bytes c.target tight).2
  expect r (t1 == t2 && !t1.error.isEmpty) s!"{c.label}: maxRecords 1 is not declined the same way twice: {t1.describe}"
  IO.println s!"  {c.label}: maxRecords 1: {t1.describe}"
  -- a target that is no constant of the environment
  let absent := Ixon.Address.blake3Pure "tests-pure-compile: no such constant".toUTF8
  let a1 := Result.of (compileRun 5 bytes absent opts).2
  let a2 := Result.of (compileRun 6 bytes absent opts).2
  expect r (a1 == a2 && !a1.error.isEmpty) s!"{c.label}: an absent target is not refused the same way twice"
  IO.println s!"  {c.label}: a target outside the environment: {a1.describe}"

def run (args : List String) : IO UInt32 := do
  let (step, only) ← match args with
    | [] => pure (4, none)
    | ["--step", n] => pure (n.toNat?.getD 4, none)
    | ["--only", p] => pure (1, some p)
    | ["--step", n, "--only", p] => pure (n.toNat?.getD 4, some p)
    | _ => throw (IO.userError "usage: tests-pure-compile [--step N] [--only LABEL-PREFIX]")
  let r ← IO.mkRef 0
  let n ← IO.mkRef ({} : Counts)
  let keep := fun (c : Case) => match only with
    | some p => c.label.startsWith p
    | none => true
  IO.println "tests-pure-compile"
  IO.FS.withTempDir fun work => do
    -- every K1 root, under every mode: twice, the other process, the command line, the trailer
    IO.println "K1 (fixtures/ixon-v4/bench-k1): every root, rc off, on and auto"
    let k1 := (← familyCases k1Manifest 0 1).filter keep
    for c in k1 do
      for rc in [Compile.Rc.off, .on, .auto] do
        let _ ← runCase r n work c { rc } true true true
    -- options, on the first K1 root
    if only.isNone then
      if let some c := k1[0]? then
        IO.println "options"
        optionControls r work c
    -- a sample of the corpus
    IO.println s!"corpus: every {step}th root of the other registered families, rc off and auto"
    for path in IxCCTests.Corpus.families do
      if path == k1Manifest then continue
      let kind : X86.Exe.Cert.ExeKind := if path == machinesManifest then .machine else .plain
      for c in (← familyCases path 0 step kind).filter keep do
        for rc in [Compile.Rc.off, .auto] do
          let _ ← runCase r n work c { rc, kind } (rc == .off) (rc == .auto) true
  let k ← n.get
  IO.println s!"  {k.cases} compiles ({k.compiled} compiled, {k.refused} refused): {k.twice} evaluated twice, \
    {k.children} repeated in another process and environment, {k.cli} compared with the command line \
    (executable, object digest, certificate text), {k.embedded} packaged and compared with --embed-cert"
  IO.println s!"  verify-exe on the {k.embedded} packaged files: {k.verified} accepted with the claim's projection"
  IO.println s!"  the seed-closure check: {k.seedClosureRefused} compiles refused there \
    ({k.cliWithoutSeedClosure} of which the command line compiles without --embed-cert)"
  IO.println s!"  not like for like (sidecar hints, the root's name): {k.sidecarSame} executables equal, \
    {k.sidecarDiffers} differ, {k.sidecarOnlyOne} compile on one side only"
  let failures ← r.get
  if failures == 0 then
    IO.println "tests-pure-compile: ok"
    return 0
  else
    IO.println s!"tests-pure-compile: {failures} failures"
    return 1

end IxCCTests.Compile
