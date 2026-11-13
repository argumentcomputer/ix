import IxCC.Recheck
import IxCC.Recheck.Rc.Produce
import IxCC.Anf.Print
import IxCC.Fir.Print
import IxCC.Cfg.Print
import IxCC.Lir.Print
import IxCC.Xv.Print
import IxCC.Exe
import IxCK.Host.Limits

/-! # The `ixcc` command line

```text
ixcc compile CLOSURE.ixe --equations EQ.json [--root NAME]... -o OUT.o
    [--rc off|on|auto] [--cert FILE] [--emit-cert FILE] [--signatures FILE]
    [--dump-ir LEVEL]... [--stats]
    [--exe FILE [--machine] [--stack BYTES] [--region BYTES]]
ixcc check-cert CLOSURE.ixe --equations EQ.json [--root NAME]... --cert FILE
    [-o OUT.o] [--signatures FILE] [--stats]
```

`compile` runs ingress, `produce` and `Recheck.run` and writes the ELF
object: `cx_<root>` for each root (the sidecar's names; every sidecar root
when no `--root` is given) and `cx_init` (`IxCC.X86.Driver` models how they are
called; `--exe` writes an executable that calls them). With `--cert`, the
given certificate replaces `produce`'s (so the recheck needs nothing from the
producer). `check-cert` runs its verifier (`checkText`: the text read with every
text and decode limit, Stage A, `Recheck.run` or `RcReplay.run`) on a certificate's
text and reports acceptance or the rejection. `compile` runs the same verifier on
the text it writes: the producer's certificate file text, which the producer has
already read back through the same reader (`Cert.readBack`), or the given file's
text; the object comes from that verdict, and `--emit-cert` writes exactly that
text, so a certificate `compile` writes is one `check-cert` accepts. A
certificate past a text or decode limit declines the compile with the limit's
reason (`cert: cert.parse: …`); under `--rc auto` a plain-RC one falls back to
the immortal policy, as any plain-RC refusal does. A certificate's format fixes its RC policy, so `--rc` with `--cert` (and so with
`check-cert`) is a usage error.

`--exe FILE` also writes a standalone static Linux x86-64 executable that runs
the first root (`Exe.build`): `FILE N1 … Nk` prints the root's result on
standard output, with no C compiler, linker or C driver involved. `-o` may then
be omitted. `--stack` and `--region` set its program stack and region (8 MiB
and 64 MiB otherwise). A root outside the fragment
executables run is refused (`exe.params`, `exe.result`; `IxCC/Exe.lean`).
With `--machine` the first root is a numeric state machine
(`Exe.buildMachine`): a step `Nat → Nat → Nat` run by a generic shell that
parses and renders nothing; `FILE ARG…` runs the session the program's own
Lean code parses and renders (`exe.machine` refuses another shape).

`compile` refuses, right after ingress, a root with a relevant parameter of
function type (`rt.fnparam`, `Recheck.checkFnParams`; the parameters refused
are listed in `Recheck/Declared.lean`): a closure cannot cross a program
boundary, so no caller can pass one.

`--rc off` (the default) compiles a zero-RC-format certificate on the immortal
backend, `--rc on` under plain RC (which may refuse the program). `--rc auto`
follows `RcReplay.produceAuto`: zero RC when `Own.Plain.selectRcPolicyForSrc`
selects it; plain RC when it selects that and the plain-RC certificate is
produced and replayed; otherwise the immortal policy. It prints
`rc policy: …` naming the policy it compiled under, and for the immortal fallback the reason plain
RC was refused (stage, code and message: for example `cert: own.plain: own.cert.budget: …` with
the measured captured work and the limit when the ownership certificate is past
`Anf.maxCapturedWork`).

`--signatures FILE` writes, per root, its symbol, parameter count and the text
forms of its result type and signature (`type`, `sig`; JSON; `null` when bounded ground
first-order signature discovery does not support the result type).
`--dump-ir LEVEL` prints a level (`lam`, `anf`, `fir`,
`cfg`, `lir`, `xv`, `xl`, or `all`) to standard output; `--stats` prints
the closure's envelope, constant root and role table address, the certified
kernel's acceptance (records and tier constants), timings, sizes and the
allocation outcomes, then each of the producer's word hints in full.

When the program reaches a pinned primitive word operation at run time without a word entry
(`Src.Table.wordHints`; it then runs the operation's reference body), `compile` prints one line
on standard error (`Src.Table.wordHintLine`: how many, the first names, and how to get the
equations that make them primitives, `Src.Table.wordEquationsAdvice`). It
changes no object, certificate or exit status; nothing is printed when there is none, or when the
certificate is read.

Ingress runs the certified kernel's acceptance of the whole closure
(`Src.KernelFront.accept`, the kernel's tiered entry; not optional): the
closure must be role-bound (`0xE5`, as `ix compile` writes it; an unbound
`0xE4` closure is refused), and a closure with any record the kernel does not
accept is refused whole, reached or not, as `ixcc: ingress: kernel: …` with the
kernel's stage and classification (an ill-typed record and any axiom but the
three standard ones, `sorryAx` among them, are declined).

A decline or rejection prints `ixcc: stage: code: message` on
standard error and exits 1; a usage error exits 2. The kernel's acceptance runs under the
kernel's limits, IxCC's decoder caps (`Src.KernelFront.defaultLimits`) unless a flag
(`--max-records`, `--max-blobs`, `--max-total-bytes`, `--max-record-bytes`,
`--max-record-univ-nodes`, `--max-depth`, `--workers`) or its variable (`IX_KERNEL_MAX_DEPTH`
and so on; the flag wins) sets one (`Ix.Kernel.Host.resolve`): a malformed value is a usage
error, the settings not at their defaults are printed first, and a decline by one exits 6,
naming it, its value and source and how to raise it. A limit only turns an acceptance into a
decline: an object and certificate made under raised limits are the ones the defaults would
give, and a verifier under lower ones declines (exit 6), it does not reject. IxCC's own limits
(its decoder's caps, its consumer budget) are not settings yet. -/

namespace IxCC.Cli

open System IxCC.Recheck

/-- Reference-counting compilation mode (`--rc off|on|auto`). -/
inductive RcMode where
  | off
  | on
  | auto
  deriving DecidableEq, Repr, Inhabited

namespace RcMode

def parse : String → Option RcMode
  | "off" => some .off
  | "on" => some .on
  | "auto" => some .auto
  | _ => none

end RcMode

structure Options where
  command : String := ""
  closure : Option FilePath := none
  equations : Option FilePath := none
  roots : List String := []
  out : Option FilePath := none
  cert : Option FilePath := none
  emitCert : Option FilePath := none
  signatures : Option FilePath := none
  dumps : List String := []
  stats : Bool := false
  rc : RcMode := .off
  rcExplicit : Bool := false
  /-- `--exe FILE`: also write a standalone executable of the first root. -/
  exe : Option FilePath := none
  /-- The executable's stack and region (`--stack`, `--region`, in bytes). -/
  layout : X86.Exe.Layout := {}
  layoutGiven : Bool := false
  /-- `--machine`: the executable runs a numeric state machine (`Exe.buildMachine`). -/
  machine : Bool := false
  /-- The kernel-limit flags as given, in order (`settingsOf`). -/
  kernel : List (Ix.Kernel.Host.Setting × String) := []
  deriving Inhabited

def usage : String :=
  "\n".intercalate [
    "usage:",
    "  ixcc compile CLOSURE.ixe --equations EQ.json [--root NAME]... -o OUT.o",
    "      [--rc off|on|auto] [--cert FILE] [--emit-cert FILE] [--signatures FILE] [--dump-ir LEVEL]... [--stats]",
    "      [--exe FILE [--machine] [--stack BYTES] [--region BYTES]]",
    "  ixcc check-cert CLOSURE.ixe --equations EQ.json [--root NAME]... --cert FILE",
    "      [-o OUT.o] [--signatures FILE] [--stats]",
    "dump levels: lam anf fir cfg lir xv xl all",
    "kernel limits (compile, check-cert): --max-records N --max-blobs N --max-total-bytes N",
    "      --max-record-bytes N --max-record-univ-nodes N --max-depth N --workers N",
    "      (else IX_KERNEL_MAX_RECORDS, ..., IX_KERNEL_WORKERS); a decline by one exits 6",
    "IXCC_REEXEC=0: do not re-run on a larger stack (the caller sets LEAN_STACK_SIZE_KB)"]

def dumpLevels : List String := ["lam", "anf", "fir", "cfg", "lir", "xv", "xl"]

def parseRest (o : Options) : List String → Except String Options
  | [] => pure o
  | "--equations" :: f :: rest => parseRest { o with equations := some f } rest
  | "--root" :: n :: rest => parseRest { o with roots := o.roots ++ [n] } rest
  | "-o" :: f :: rest => parseRest { o with out := some f } rest
  | "--rc" :: m :: rest =>
    match RcMode.parse m with
    | some mode => parseRest { o with rc := mode, rcExplicit := true } rest
    | none => throw s!"unknown --rc mode {m}"
  | "--cert" :: f :: rest => parseRest { o with cert := some f } rest
  | "--emit-cert" :: f :: rest => parseRest { o with emitCert := some f } rest
  | "--signatures" :: f :: rest => parseRest { o with signatures := some f } rest
  | "--dump-ir" :: l :: rest =>
    if l == "all" then parseRest { o with dumps := o.dumps ++ dumpLevels } rest
    else if dumpLevels.contains l then parseRest { o with dumps := o.dumps ++ [l] } rest
    else throw s!"unknown IR level {l}"
  | "--stats" :: rest => parseRest { o with stats := true } rest
  | "--max-records" :: v :: rest => parseRest { o with kernel := o.kernel ++ [(.maxRecords, v)] } rest
  | "--max-blobs" :: v :: rest => parseRest { o with kernel := o.kernel ++ [(.maxBlobs, v)] } rest
  | "--max-total-bytes" :: v :: rest => parseRest { o with kernel := o.kernel ++ [(.maxTotalBytes, v)] } rest
  | "--max-record-bytes" :: v :: rest => parseRest { o with kernel := o.kernel ++ [(.maxRecordBytes, v)] } rest
  | "--max-record-univ-nodes" :: v :: rest =>
    parseRest { o with kernel := o.kernel ++ [(.maxRecordUnivNodes, v)] } rest
  | "--max-depth" :: v :: rest => parseRest { o with kernel := o.kernel ++ [(.maxDepth, v)] } rest
  | "--workers" :: v :: rest => parseRest { o with kernel := o.kernel ++ [(.workers, v)] } rest
  | "--exe" :: f :: rest => parseRest { o with exe := some f } rest
  | "--machine" :: rest => parseRest { o with machine := true } rest
  | "--stack" :: n :: rest =>
    match n.toNat? with
    | some b => parseRest { o with layout := { o.layout with stack := b }, layoutGiven := true } rest
    | none => throw s!"--stack takes a number of bytes, not {n}"
  | "--region" :: n :: rest =>
    match n.toNat? with
    | some b => parseRest { o with layout := { o.layout with region := b }, layoutGiven := true } rest
    | none => throw s!"--region takes a number of bytes, not {n}"
  | arg :: rest =>
    if arg.startsWith "-" then throw s!"unknown option {arg}"
    else if o.closure.isSome then throw s!"unexpected argument {arg}"
    else parseRest { o with closure := some arg } rest

def parse : List String → Except String Options
  | cmd :: rest =>
    if cmd == "compile" || cmd == "check-cert" then do
      let o ← parseRest { command := cmd } rest
      if o.closure.isNone then throw "no closure given"
      if o.equations.isNone then throw "no --equations sidecar given"
      if cmd == "compile" && o.out.isNone && o.exe.isNone then throw "no -o or --exe output given"
      if o.layoutGiven && o.exe.isNone then throw "--stack and --region apply to --exe"
      if o.machine && o.exe.isNone then throw "--machine applies to --exe"
      -- a certificate fixes the RC policy (its format), so `--rc` with one is a usage error
      if o.cert.isSome && o.rcExplicit then throw "cannot combine --rc with --cert"
      if cmd == "check-cert" && o.cert.isNone then throw "check-cert needs --cert"
      pure o
    else throw s!"unknown command {cmd}"
  | [] => throw "no command"

/-! ## Reports -/

def lamNodes (P : Lam.Program) : Nat := P.globalList.foldl (fun n (_, g) => n + g.body.nodes) 0
def anfNodes (A : Anf.Program) : Nat := A.globalList.foldl (fun n (_, g) => n + g.body.nodes) 0

/-- A level as text. -/
def dump (a : Artifact) : String → String
  | "lam" => "\n".intercalate (a.lam.globalList.map fun (g, gl) =>
      s!"g{g} [{gl.key.render}] := {reprStr gl.body}")
  | "anf" => a.anf.render
  | "fir" => a.fir.render
  | "cfg" => a.cfg.render
  | "lir" => a.lowered.program.text
  | "xv" => a.xv.text
  | "xl" => a.xl.text
  | l => s!"(no level {l})"

def driverArgs (r : Root) : String :=
  match r.driverType with
  | some (t, s) => s!"--type {t} --sig '{s}'"
  | none => "(no readback type)"

/-- The roots' signatures for the driver (and the runner). -/
def signaturesJson (a : Artifact) : Lean.Json :=
  Lean.Json.mkObj [("roots", Lean.Json.arr (a.roots.toArray.map fun r =>
    Lean.Json.mkObj [("name", r.name), ("symbol", r.symbol), ("params", Lean.toJson r.params),
      ("type", match r.driverType with | some (t, _) => Lean.Json.str t | none => .null),
      ("sig", match r.driverType with | some (_, s) => Lean.Json.str s | none => .null)]))]

def statsLines (a : Artifact) (outcomes : Option (List Xv.Alloc.Outcome)) : List String :=
  let lir := a.lowered.program
  let lirBlocks := lir.funcs.foldl (fun n f => n + f.blocks.size) 0
  let alloc := match outcomes with
    | some os =>
      let scan := os.countP (· matches .scan)
      s!"allocation: linear scan accepted for {scan} of {os.length} functions, all slots for the rest"
    | none => "allocation: from the given certificate"
  let edits := a.backend.stacked.program.blocks.size
  [s!"src: {a.src.size} constants, {a.src.roots.length} roots, {a.checked.reached.length} reached",
   s!"lam: {a.lam.size} globals, {lamNodes a.lam} nodes",
   s!"anf: {a.anf.size} globals, {anfNodes a.anf} nodes",
   s!"cfg: {a.cfg.size} functions, {a.cfg.blocks} blocks, {a.cfg.instrs} instructions and terminators",
   s!"lir: {lir.funcs.size} functions, {lirBlocks} blocks, {lir.size} statements and terminators",
   alloc,
   s!"x86: {edits} blocks after stacking, text {a.backend.encoded.text.size} bytes, object {a.object.size} bytes"] ++
  a.roots.map fun r => s!"root {r.name}: {r.symbol}, parameters {r.params}, driver {driverArgs r}"

/-- What the closure is, by its identity: the envelope, the constant root and,
for a role-bound envelope, the binding hash (the role table's address) and the
table the kernel admitted. -/
def envelopeLine (inp : Recheck.Input) : String :=
  let env := inp.env
  let t := inp.kernel.acc.table
  match env.binding with
  | some b =>
    s!"environment: role-bound (0xE5), root {env.root}, role table {b.address} \
      ({t.bound.size} roles bound, specification version {t.version})"
  | none => s!"environment: unbound (0xE4), root {env.root}"

/-! ## Commands -/

def cliErr (code message : String) : Err := { stage := .cli, code, message }

def readInputs (o : Options) : ExceptT Err IO (ByteArray × Lean.Json) := do
  let some closure := o.closure | throw (cliErr "cli.args" "no closure")
  let some eqs := o.equations | throw (cliErr "cli.args" "no equations")
  let bytes ← (IO.FS.readBinFile closure).toBaseIO >>= fun
    | .ok b => pure b
    | .error e => throw (cliErr "cli.read" s!"{closure}: {e}")
  let text ← (IO.FS.readFile eqs).toBaseIO >>= fun
    | .ok t => pure t
    | .error e => throw (cliErr "cli.read" s!"{eqs}: {e}")
  let json ← match (Src.Hints.checkJsonText text >>= fun () => Lean.Json.parse text) with
    | .ok j => pure j
    | .error e => throw { stage := .ingress, code := "hints", message := s!"{eqs}: {e}" }
  pure (bytes, json)

/-- Either a zero-RC (`ixcc/cert/1`) or plain-RC (`ixcc/rc-cert/2`) certificate. -/
inductive CliCert where
  | zeroRc (cert : Cert)
  | plainRc (cert : RcReplay.Cert)

def CliCert.base : CliCert → Cert
  | .zeroRc c => c
  | .plainRc c => c.base

/-- The certificate a text is, by the format its envelope names: `RcReplay.Cert.parse` for a
plain-RC envelope (`["ixcc/rc-cert/2", …]`), `Cert.ofText` otherwise. The reader of `check-cert`
and `compile --cert`, with every text and decode limit. -/
def CliCert.ofText (text : String) : Except Err CliCert :=
  if text.trimAscii.toString.startsWith "[\"ixcc/rc-cert/2\"" then .plainRc <$> RcReplay.Cert.parse text
  else .zeroRc <$> Cert.ofText text

/-- **`check-cert`'s verifier**, on a certificate's text: the text read (`CliCert.ofText`), its
relevance annotation checked to be the annotator's (Stage A, `checkCanonicalRelevance`), and the
certificate replayed (`run`, or `RcReplay.run` for a plain-RC certificate). `compile` runs it on
the text it is about to write, so a successful compile is one whose written certificate this
accepts. -/
def checkText (cfg : Config) (inp : Input) (text : String) : Except Err (CliCert × Artifact) := do
  let cc ← CliCert.ofText text
  unless checkCanonicalRelevance cfg inp cc.base.table cc.base.relevance do
    throw { stage := .relevance, code := "relevance-canonical",
            message := "certificate relevance annotation does not match canonical annotator output" }
  match cc with
  | .zeroRc cert => return (cc, ← run cfg inp.program cert)
  | .plainRc cert =>
    let rcArt ← RcReplay.run cfg inp.program cert
    return (cc, ← rcArt.toRecheckArtifact cert)

/-- The certificate text `compile` writes under `--rc` mode `rc` (the producer's file text, read
back through the verifier's reader inside the producer), with the allocation outcomes and, for
`--rc auto`, the policy it compiled under, and the word hints after admission (stage W1). `--rc auto` follows `RcReplay.produceAuto`: plain RC when
it is selected and its certificate is produced and replayed, else the immortal policy. -/
def produceText (rc : RcMode) (cfg : Config) (inp : Input) :
    Except Err (String × List Xv.Alloc.Outcome × Option String × Array Src.Diag) := do
  match rc with
  | .off =>
    let p ← produceWith cfg inp
    pure (p.text, p.alloc, none, p.wordHints)
  | .on =>
    let p ← RcReplay.produceWith cfg inp
    pure (p.text, p.alloc, none, p.front.wordHints)
  | .auto =>
    let front ← RcReplay.produceFir cfg inp
    match Own.Plain.selectRcPolicyForSrc front.src front.fir with
    | .zeroRc =>
      let p ← RcReplay.finishZeroRcCert cfg front
      pure (p.text, p.alloc, some "zero-rc", front.wordHints)
    | .plainRc =>
      match RcReplay.producePlain cfg inp front with
      | .ok (p, _) => pure (p.text, p.alloc, some "plain-rc", front.wordHints)
      | .error reason =>
        let p ← RcReplay.finishZeroRcCert cfg front
        pure (p.text, p.alloc,
          some s!"immortal (plain RC refused: {reason.stage.name}: {reason.code}: {reason.message})",
          front.wordHints)

/-- An attempt at a configuration with the middle end's inline-round retry and, if that fails at
any stage, again without it (each run is the proved composition at its own configuration). -/
def withRetry {m : Type → Type} [Monad m] [MonadExcept Err m] {α : Type} (cfg : Config)
    (attempt : Config → m α) : m α :=
  if cfg.budgets.retryInline then tryCatch (attempt cfg) fun _ => attempt cfg.noRetry
  else attempt cfg

/-- What `compile` computes without a given certificate, as a pure function: the certificate text
it writes (`produceText`) and `check-cert`'s verdict on that text (`checkText`), with the retry. -/
def compileText (rc : RcMode) (cfg : Config) (inp : Input) : Except Err (String × CliCert × Artifact) :=
  withRetry cfg fun cfg => do
    let (text, _, _, _) ← produceText rc cfg inp
    let (cc, a) ← checkText cfg inp text
    pure (text, cc, a)

def readText (f : FilePath) : ExceptT Err IO String := do
  (IO.FS.readFile f).toBaseIO >>= fun
    | .ok t => pure t
    | .error e => throw (cliErr "cli.read" s!"{f}: {e}")

def write (f : FilePath) (write : IO Unit) : ExceptT Err IO Unit := do
  match ← write.toBaseIO with
  | .ok () => pure ()
  | .error e => throw (cliErr "cli.write" s!"{f}: {e}")

def timed {α : Type} (action : ExceptT Err IO α) : ExceptT Err IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let r ← action
  return (r, (← IO.monoMsNow) - t0)

/-- A pure stage, evaluated when the action runs (so `timed` measures it). -/
def lift {α : Type} (x : Unit → Except Err α) : ExceptT Err IO α := ExceptT.mk (IO.lazyPure x)

/-- `compile` and `check-cert`, the kernel under `limits`. -/
def execute (o : Options) (limits : Ix.Kernel.Admission.Limits := Src.KernelFront.defaultLimits) :
    ExceptT Err IO Unit := do
  let ((bytes, json), tRead) ← timed (readInputs o)
  let (inp, tIngress) ← timed (lift fun _ => ingress bytes json o.roots limits)
  let cfg := Config.forInput {} inp
  -- a root whose caller would pass a closure has no meaningful caller: refused
  -- before anything is produced (every producer refuses it too, `produceClosures`)
  if o.command == "compile" then lift fun _ => checkFnParams cfg.names inp.program
  -- `policy`: the policy `--rc auto` compiled under, reported on standard output.
  -- The certificate text (the producer's, read back inside the producer, or the given file's),
  -- then `check-cert`'s verifier on that text (`checkText`): the object and everything written
  -- come from its verdict on the text that is written. Without a given certificate, with the
  -- middle end's inline-round retry first and, if that fails at any stage, without it
  -- (`withRetry`; each run is the proved composition at its own configuration).
  let produceRun := fun (cfg : Config) => show ExceptT Err IO _ from do
    let ((text, outcomes, policy, hints), tProduce) ← timed do
      match o.cert with
      | some f => pure (← readText f, none, none, #[])
      | none =>
        let (text, outcomes, policy, hints) ← lift fun _ => produceText o.rc cfg inp
        pure (text, some outcomes, policy, hints)
    let ((cliCert, a), tRun) ← timed (lift fun _ => checkText cfg inp text)
    pure (text, cliCert, outcomes, policy, tProduce, a, tRun, hints)
  let (text, cliCert, outcomes, policy, tProduce, a, tRun, hints) ←
    if o.cert.isNone then withRetry cfg produceRun else produceRun cfg
  if let some l := Src.Table.wordHintLine hints then IO.eprintln l
  if let some f := o.out then
    write f do
      let tmp : FilePath := s!"{f}.tmp.{← IO.monoNanosNow}"
      IO.FS.writeBinFile tmp a.object
      IO.FS.rename tmp f
  if let some f := o.exe then
    -- the bytes and the placement of the executable `--exe` or `--machine` writes
    let (bytes, p) ← if o.machine then do
        let L : X86.Exe.Machine.Layout := { stack := o.layout.stack, region := o.layout.region }
        let ⟨_, exe⟩ ← lift fun _ => Exe.buildMachine a L
        pure (exe.checked.bytes, exe.checked.plan.placement)
      else do
        let ⟨_, exe⟩ ← lift fun _ => Exe.build a o.layout
        pure (exe.bytes, exe.plan.placement)
    write f do
      let tmp : FilePath := s!"{f}.tmp.{← IO.monoNanosNow}"
      IO.FS.writeBinFile tmp bytes
      IO.setAccessRights tmp { user := { read := true, write := true, execution := true }
                               group := { read := true, execution := true }
                               other := { read := true, execution := true } }
      IO.FS.rename tmp f
    if o.stats then
      IO.println s!"executable: {bytes.size} bytes (object text {p.textSize}, shell {p.shellSize}), \
        stack {o.layout.stack} bytes, region {o.layout.region} bytes"
  -- exactly the text that was verified
  if let some f := o.emitCert then write f (IO.FS.writeFile f text)
  if let some f := o.signatures then write f (IO.FS.writeFile f ((signaturesJson a).pretty ++ "\n"))
  for l in o.dumps do
    IO.println s!"== {l} =="
    IO.println (dump a l)
  if o.command == "check-cert" then
    IO.println s!"certificate accepted: object {a.object.size} bytes, text {a.backend.encoded.text.size} bytes, \
      exports {a.roots.map (·.symbol)}"
  if let some p := policy then IO.println s!"rc policy: {p}"
  if o.stats then
    let cert := cliCert.base
    let certBytes := if text.endsWith "\n" then text.utf8ByteSize - 1 else text.utf8ByteSize
    let producer := if o.cert.isSome then "certificate read" else "produce"
    IO.println (envelopeLine inp)
    IO.println s!"kernel: accepted {inp.kernel.acc.records.length} records, \
      {inp.kernel.acc.decls.size} logical declarations and {inp.kernel.acc.tier.length} tier constants, \
      within ingress"
    IO.println s!"time: read {tRead} ms, ingress {tIngress} ms (the kernel's acceptance included), \
      {producer} {tProduce} ms, run {tRun} ms"
    IO.println s!"certificate: {certBytes} bytes of JSON; {cert.table.resolve.length} table entries, \
      {cert.relevance.nodes.length} annotated terms, {cert.mid.steps.length} middle-end steps, \
      {cert.alloc.length} allocations, {cert.frames.length} frame layouts"
    for l in statsLines a outcomes do IO.println l
    for d in hints do IO.println s!"hint: {d.message}"

/-- The kernel's limits: the flags (the last of each), else the `IX_KERNEL_*` variables, else
IxCC's decoder caps (`Src.KernelFront.defaultLimits`, depth 16,384). -/
def settingsOf (o : Options) : IO (Except String Ix.Kernel.Host.Resolved) :=
  Ix.Kernel.Host.resolveIO Src.KernelFront.defaultLimits fun s => (o.kernel.reverse.find? (·.1 == s)).map (·.2)

/-- The limit an error is a decline by (`Recheck.kernelLimitCode`). -/
def limitOfCode (code : String) : Option Ix.Kernel.Admission.Resource :=
  [Ix.Kernel.Admission.Resource.records, Ix.Kernel.Admission.Resource.blobs,
    Ix.Kernel.Admission.Resource.totalBytes, Ix.Kernel.Admission.Resource.recordBytes,
    Ix.Kernel.Admission.Resource.recordUnivNodes, Ix.Kernel.Admission.Resource.depth].find?
    (kernelLimitCode · == code)

/-- The command line; the exit code: 0, 1 a decline or rejection, 2 a usage error, 6 a decline
by a kernel limit (with one more line naming the setting). -/
def main (args : List String) : IO UInt32 := do
  if args == ["--help"] || args == ["-h"] || args.isEmpty then
    IO.println usage
    return (if args.isEmpty then 2 else 0)
  match parse args with
  | .error e =>
    IO.eprintln s!"ixcc: {e}\n{usage}"
    return 2
  | .ok o =>
    let settings ← match ← settingsOf o with
      | .ok s => pure s
      | .error e => IO.eprintln s!"ixcc: {e}\n{usage}"; return 2
    if let some h := Ix.Kernel.Host.header settings then IO.eprintln s!"ixcc: {h}"
    match ← (execute o settings.limits).run with
    | .ok () => return 0
    | .error e =>
      IO.eprintln s!"ixcc: {e.render}"
      match limitOfCode e.code with
      | some r =>
        IO.eprintln s!"ixcc: {Ix.Kernel.Host.declineMessage settings r}"
        return Ix.Kernel.Host.exitDeclined
      | none => return 1

end IxCC.Cli
