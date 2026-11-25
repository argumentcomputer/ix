import IxCC.Recheck
import IxCC.Compile
import IxCC.Recheck.Rc.Produce
import IxCC.Src.AutoHints
import IxCC.Anf.Print
import IxCC.Fir.Print
import IxCC.Cfg.Print
import IxCC.Lir.Print
import IxCC.Xv.Print
import IxCC.Exe
import IxCC.Exe.Cert
import IxCC.Rt.BigNat.Link
import IxCC.Rt.BigNat.LowerBig
import IxCK.Host.Limits

/-! # The `ixcc` command line

```text
ixcc compile CLOSURE.ixe [--equations EQ.json] [--root NAME|ADDR|NAME=ADDR]... -o OUT.o
    [--rc off|on|auto] [--cert FILE] [--emit-cert FILE] [--signatures FILE]
    [--dump-ir LEVEL]... [--stats]
    [--exe FILE [--embed-cert] [--machine] [--stack BYTES] [--region BYTES]]
    [--uncertified --opt | --uncertified --bignat [--bignat-lib FILE] [--opt]]
ixcc check-cert CLOSURE.ixe [--equations EQ.json] [--root NAME|ADDR|NAME=ADDR]... --cert FILE
    [-o OUT.o] [--signatures FILE] [--stats]
ixcc verify-exe FILE [--closure CLOSURE.ixe] [--equations EQ.json]
    [--expect-target ADDR] [--expect-env ADDR] [--stats]
```

**The default path is the pure compiler.** `ixcc compile CLOSURE.ixe [--root R]` with no
`--equations` sidecar, no `--cert` and no `--uncertified` mode, naming one root, is an IO
wrapper around `IxCC.Compile.compile` (`defaultPlan?`): it reads the closure, resolves `--root`
(`NAME`, `<64-hex>`, `NAME=<64-hex>`, or the default `entry`/`main`) to an address and a name, and
calls `Compile.check` then, when `--exe` is given, `Compile.build`, with the options `--rc`,
`--machine`, `--stack`/`--region`, the kernel's limits and the root's name. Everything it writes
is what they return (`-o` the checked artifact's object, `--exe` the executable, `--emit-cert` the
certificate text, `--embed-cert` that executable with the trailer made from the returned claim),
so the command line and `compile` agree byte for byte by construction (`tests-pure-compile`).
The hints are derived inside `compile`, the seed-closure check runs on every compile, and a
program that selects zero RC and whose contract recheck refuses is rejected (exit 3), never
compiled as immortal. Without `--exe` only `check` runs. Several `--root`s, a sidecar, a given
certificate or an uncertified mode take the paths below, which are not `compile`.

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
certificate the producer makes past a text or decode limit declines the compile with the limit's
reason (`cert: cert.parse: …`; a given one past it is rejected); under `--rc auto` a plain-RC one
falls back to the immortal policy, as any plain-RC refusal does. A certificate's format fixes its RC policy, so `--rc` with `--cert` (and so with
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

**Exit statuses** (`Outcome`). A failure prints `ixcc: stage: code: message` on standard error
and exits with what kind of failure it is:

| Status | Outcome | When |
| --- | --- | --- |
| 0 | success | everything computed and written |
| 1 | declined | the program is outside what the compiler accepts: ingress (the kernel's acceptance included), the producer, a root outside the executables' fragment, a definition assertion that does not hold (`assert.*`) |
| 2 | usage error | the command line is malformed, or a file or root it names cannot be read, written or found (`cli.*`) |
| 3 | rejected | a certificate or an artifact failed a check: `check-cert`'s verifier on any certificate text (the producer's or a given one), the policy recheck and executable verifier of `--embed-cert`, `verify-exe` and its `--expect-*` |
| 4 | internal error | the compiler failed in a way that is its own fault (`rt.internal`, an uncaught exception) |
| 6 | declined by a kernel limit | below |

A step's errors take its outcome, except where the code decides (`classify`: `cli.*` usage,
`rt.internal` internal, `assert.*` declined). On the default path a refusal of `compile` is a
decline (1), except the policy recheck (`exe.cert.policy`), the seed-closure check (`kf4`) and
the certificate's relevance annotation (`relevance-canonical`), which are rejections (3)
(`compileOutcome`); `compile` checks its own producer's certificate, so a replay failure there is
a decline of the program, not a rejected input.

The kernel's acceptance runs under the
kernel's limits, IxCC's decoder caps (`Src.KernelFront.defaultLimits`) unless a flag
(`--max-records`, `--max-blobs`, `--max-total-bytes`, `--max-record-bytes`,
`--max-record-univ-nodes`, `--max-depth`, `--workers`, `--level-budget`) or its variable
(`IX_KERNEL_MAX_DEPTH` and so on; the flag wins) sets one (`Ix.Kernel.Host.resolve`): a malformed value is a usage
error, the settings not at their defaults are printed first, and a decline by one exits 6,
naming it, its value and source and how to raise it. A limit only turns an acceptance into a
decline: an object and certificate made under raised limits are the ones the defaults would
give, and a verifier under lower ones declines (exit 6), it does not reject. IxCC's own limits
(its decoder's caps, its consumer budget) are not settings yet.

**All or nothing.** A run computes everything first (the object, the executable, the
certificate text, the signatures, what it prints), then writes each file to a temporary file
beside it and renames them all into place (`commit`). A run that fails at any point after its
command line parsed writes none of its files and removes the ones it would have replaced (`-o`,
`--exe`, `--emit-cert`, `--signatures`; `removeOutputs`: regular files and symbolic links only),
so no stale or partial output survives a failure; so does a run whose second process
(`IxCC.Cli.Main`) dies by a signal. A malformed command line or kernel-limit setting (exit 2
before anything runs) touches no file. No two outputs may name the same file, and no output may
name an input (a usage error).

**Modes no certificate replay covers** (`--uncertified`). `--opt` replays the certificate and
then rebuilds the object from the replayed Lir with `Backend.compileOpt` (the Lir SSA optimizer,
then selection, allocation, stacking and encoding afresh), so the object written is not the one
the certificate verified. `--bignat` produces and checks no certificate at all: it lowers through
`Rt.BigNat.lowerRepBig` by hand, with a BigNat runtime library loaded from `--bignat-lib FILE`,
`IX_BIGNAT_LIB`, or frozen by running an external `ix` (`IX_BIN`, `../.lake/build/bin/ix`,
`.lake/build/bin/ix`, or `ix` on `PATH`) into `/tmp`. Each requires `--uncertified` as well
(without it a usage error naming what is not covered), and `--uncertified` requires one of them.
With it the run prints one line on standard error saying that what it writes is not covered by
certificate replay (`uncertifiedLine`), and the object's provenance note says so: the top bit of
its pass-policy word is set (`Recheck.uncertifiedProvenance`; `--opt` pass policy 2 on the
replay's lowering 1 or 3, `--bignat` lowering 4, pass policy 1 or, with `--opt`, 2), which the
executable `--exe` writes carries too. Neither mode checks definition assertions (`@[no_alloc]`,
`@[no_rc]`, `@[bounded_stack]`) on the object it writes, so each declines a program any of whose
constants carries one (`assert.uncertified`). Neither combines with `--cert`, `--emit-cert` or
`--embed-cert`.

**`--embed-cert`** writes the executable only once the executable verifier (`verify-exe`'s,
`Exe.Cert.verifyExeBytes`, under the same kernel limits) has accepted the bytes about to be
written and returned the claim built; the policy the claim binds comes from
`Exe.Cert.policyOfArtifact`, whose contract recheck refusing is a rejection, not a weaker label.
It prints the claim (`executable certificate verified: …`).

**`verify-exe FILE`** runs that verifier on the file and prints the claim's target, policy,
arity and sizes, then its environment root and role table; `--expect-target ADDR` and
`--expect-env ADDR` (64 hexadecimal digits) reject (exit 3) an executable whose claim names
another target or environment root, so "verified" can mean "a correct compile of this target in
this environment". -/

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
  /-- `--rc`: reference-counting mode (`off`, `on`, `auto`). -/
  rc : RcMode := .off
  rcExplicit : Bool := false
  /-- `--opt`: rebuild the replayed object with the Lir SSA optimizer (`Backend.compileOpt`,
  default OFF; not covered by certificate replay, so it needs `--uncertified`). -/
  opt : Bool := false
  /-- `--bignat`: compile via DR3/DR4 + Phase 4 arbitrary-precision `Nat` (`Rt.BigNat.lowerRepBig`,
  default OFF; no certificate at all, so it needs `--uncertified`). -/
  bignat : Bool := false
  /-- `--bignat-lib FILE`: pre-frozen `ixcc/bignat-bootstrap/1` JSON for `--bignat`. -/
  bignatLib : Option FilePath := none
  /-- `--uncertified`: accept `--opt` or `--bignat`, whose objects no certificate replay covers
  (they are marked so in their provenance note, `Recheck.uncertifiedProvenance`). -/
  uncertified : Bool := false
  /-- `verify-exe --expect-target ADDR`: the target the claim must name. -/
  expectTarget : Option Ixon.Address := none
  /-- `verify-exe --expect-env ADDR`: the environment root the claim must name. -/
  expectEnv : Option Ixon.Address := none
  /-- `--exe FILE`: also write a standalone executable of the first root. -/
  exe : Option FilePath := none
  /-- `--embed-cert`: package a hardened `.ix.cert` v1 trailer into `--exe`. -/
  embedCert : Bool := false
  /-- Executable path for `ixcc verify-exe FILE`. -/
  verifyExe : Option FilePath := none
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
    "  ixcc compile CLOSURE.ixe [--equations EQ.json] [--root NAME|ADDR|NAME=ADDR]... -o OUT.o",
    "      [--rc off|on|auto] [--cert FILE] [--emit-cert FILE]",
    "      [--signatures FILE] [--dump-ir LEVEL]... [--stats]",
    "      [--exe FILE [--embed-cert] [--machine] [--stack BYTES] [--region BYTES]]",
    "      [--uncertified --opt | --uncertified --bignat [--bignat-lib FILE] [--opt]]",
    "  ixcc check-cert CLOSURE.ixe [--equations EQ.json] [--root NAME|ADDR|NAME=ADDR]... --cert FILE",
    "      [-o OUT.o] [--signatures FILE] [--stats]",
    "  ixcc verify-exe FILE [--closure CLOSURE.ixe] [--equations EQ.json]",
    "      [--expect-target ADDR] [--expect-env ADDR] [--stats]",
    "dump levels: lam anf fir cfg lir xv xl all",
    "--opt and --bignat write objects no certificate replay covers (--opt rebuilds the replayed object",
    "      with Backend.compileOpt; --bignat checks no certificate at all): each needs --uncertified,",
    "      which marks the object's provenance note and prints a line on standard error",
    "--embed-cert writes the executable only once verify-exe's verifier accepts its bytes;",
    "      verify-exe prints the claim's target and environment, --expect-target/--expect-env",
    "      ADDR (64 hex digits) reject another",
    "outputs (-o, --exe, --emit-cert, --signatures) are written together once everything is computed;",
    "      a failed run writes none and removes the files they name",
    "kernel limits (compile, check-cert, verify-exe): --max-records N --max-blobs N --max-total-bytes N",
    "      --max-record-bytes N --max-record-univ-nodes N --max-depth N --workers N --level-budget N",
    "      (else IX_KERNEL_MAX_RECORDS, ..., IX_KERNEL_LEVEL_BUDGET); a decline by one exits 6",
    "exit status: 0 success, 1 declined (the program is outside what the compiler accepts),",
    "      2 usage error (a malformed command line, or a file or root it names that cannot be used),",
    "      3 rejected (a certificate or an artifact failed a check), 4 internal error,",
    "      6 declined by a kernel limit",
    "IXCC_REEXEC=0: do not re-run on a larger stack (the caller sets LEAN_STACK_SIZE_KB)"]

def dumpLevels : List String := ["lam", "anf", "fir", "cfg", "lir", "xv", "xl"]

def parseRest (o : Options) : List String → Except String Options
  | [] => pure o
  | "--closure" :: f :: rest => parseRest { o with closure := some f } rest
  | "--equations" :: f :: rest => parseRest { o with equations := some f } rest
  | "--root" :: n :: rest => parseRest { o with roots := o.roots ++ [n] } rest
  | "-o" :: f :: rest => parseRest { o with out := some f } rest
  | "--rc" :: m :: rest =>
    match RcMode.parse m with
    | some mode => parseRest { o with rc := mode, rcExplicit := true } rest
    | none => throw s!"unknown --rc mode {m}"
  | "--opt" :: rest => parseRest { o with opt := true } rest
  | "--bignat" :: rest => parseRest { o with bignat := true } rest
  | "--bignat-lib" :: f :: rest => parseRest { o with bignatLib := some f } rest
  | "--uncertified" :: rest => parseRest { o with uncertified := true } rest
  | "--expect-target" :: a :: rest =>
    match Ixon.Address.fromString a with
    | some t => parseRest { o with expectTarget := some t } rest
    | none => throw s!"--expect-target takes an address of 64 hexadecimal digits, not {a}"
  | "--expect-env" :: a :: rest =>
    match Ixon.Address.fromString a with
    | some e => parseRest { o with expectEnv := some e } rest
    | none => throw s!"--expect-env takes an address of 64 hexadecimal digits, not {a}"
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
  | "--level-budget" :: v :: rest => parseRest { o with kernel := o.kernel ++ [(.levelBudget, v)] } rest
  | "--exe" :: f :: rest => parseRest { o with exe := some f } rest
  | "--embed-cert" :: rest => parseRest { o with embedCert := true } rest
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
    else if o.command == "verify-exe" then
      if o.verifyExe.isSome then throw s!"unexpected argument {arg}"
      else parseRest { o with verifyExe := some arg } rest
    else if o.closure.isSome then throw s!"unexpected argument {arg}"
    else parseRest { o with closure := some arg } rest

/-- The files a run writes (`-o`, `--exe`, `--emit-cert`, `--signatures`), as given. -/
def Options.outputs (o : Options) : List FilePath := [o.out, o.exe, o.emitCert, o.signatures].filterMap id

/-- The files a run reads, as given. -/
def Options.inputs (o : Options) : List FilePath :=
  [o.closure, o.equations, o.cert, o.bignatLib].filterMap id

/-- The uncertified mode a run is in (`--opt`, `--bignat` or both), as its flags spell it. -/
def Options.uncertifiedMode (o : Options) : Option String :=
  if o.bignat && o.opt then some "--bignat --opt"
  else if o.bignat then some "--bignat"
  else if o.opt then some "--opt"
  else none

/-- Why `--opt` or `--bignat` needs `--uncertified`: what certificate replay does not cover. -/
def uncoveredWhy (o : Options) : Option String :=
  if o.bignat then some "--bignat writes an object no certificate covers: it produces and checks \
    no certificate, builds the object through Rt.BigNat.lowerRepBig and a fresh back end, loads \
    its BigNat library from --bignat-lib FILE or IX_BIGNAT_LIB or freezes one by running an \
    external ix (IX_BIN, ../.lake/build/bin/ix, .lake/build/bin/ix, or ix on PATH) into /tmp, \
    and checks no definition assertion; pass --uncertified as well to write it, marked \
    uncertified in its provenance note"
  else if o.opt then some "--opt writes an object no certificate covers: it replays the \
    certificate and then rebuilds the object from the replayed Lir with Backend.compileOpt \
    (the Lir SSA optimizer, then selection, allocation, stacking and encoding afresh), which \
    no certificate or replay checks; pass --uncertified as well to write it, marked uncertified \
    in its provenance note"
  else none

/-- A path as written, without its `.` components and repeated separators: two outputs, or an
output and an input, that name the same file this way are refused. -/
def pathKey (f : FilePath) : String :=
  let parts := (f.toString.splitOn "/").filter fun c => c != "." && c != ""
  (if f.toString.startsWith "/" then "/" else "") ++ "/".intercalate parts

/-- Two outputs naming one file, or an output naming an input. -/
def outputClash (o : Options) : Option String :=
  let outs := o.outputs
  match outs.find? fun f => (outs.filter (pathKey · == pathKey f)).length > 1 with
  | some f => some s!"{f} is named by two outputs"
  | none =>
    match outs.find? fun f => o.inputs.any (pathKey · == pathKey f) with
    | some f => some s!"{f} is both an input and an output"
    | none => none

def parse : List String → Except String Options
  | cmd :: rest =>
    if cmd == "compile" || cmd == "check-cert" then do
      let o ← parseRest { command := cmd } rest
      if o.closure.isNone then throw "no closure given"
      if cmd == "compile" && o.out.isNone && o.exe.isNone then throw "no -o or --exe output given"
      if o.layoutGiven && o.exe.isNone then throw "--stack and --region apply to --exe"
      if o.machine && o.exe.isNone then throw "--machine applies to --exe"
      if o.embedCert && o.exe.isNone then throw "--embed-cert applies to --exe"
      if o.opt && cmd == "check-cert" then throw "--opt applies only to compile"
      if o.opt && o.cert.isSome then throw "cannot combine --opt with --cert"
      if o.opt && o.emitCert.isSome then throw "cannot combine --opt with --emit-cert"
      if o.opt && o.embedCert then throw "cannot combine --opt with --embed-cert"
      if o.bignat && cmd == "check-cert" then throw "--bignat applies only to compile"
      if o.bignat && o.cert.isSome then throw "cannot combine --bignat with --cert"
      if o.bignat && o.emitCert.isSome then throw "cannot combine --bignat with --emit-cert"
      if o.bignat && o.embedCert then throw "cannot combine --bignat with --embed-cert"
      if o.bignat && o.machine then throw "cannot combine --bignat with --machine"
      if o.bignat && o.rc != .off then throw "--bignat requires --rc off"
      if o.bignatLib.isSome && !o.bignat then throw "--bignat-lib applies to --bignat"
      if o.uncertified && !(o.opt || o.bignat) then
        throw "--uncertified applies to --opt and --bignat"
      if let some why := uncoveredWhy o then
        unless o.uncertified do throw why
      if o.expectTarget.isSome || o.expectEnv.isSome then
        throw "--expect-target and --expect-env apply to verify-exe"
      -- a certificate fixes the RC policy (its format), so `--rc` with one is a usage error
      if o.cert.isSome && o.rcExplicit then throw "cannot combine --rc with --cert"
      if cmd == "check-cert" && o.cert.isNone then throw "check-cert needs --cert"
      if let some why := outputClash o then throw why
      pure o
    else if cmd == "verify-exe" then do
      let o ← parseRest { command := cmd } rest
      if o.verifyExe.isNone then throw "no executable given"
      if o.out.isSome || o.exe.isSome || o.cert.isSome || o.emitCert.isSome ||
          o.signatures.isSome || !o.dumps.isEmpty || o.rcExplicit || o.opt ||
          o.bignat || o.bignatLib.isSome || o.uncertified || o.layoutGiven ||
          o.machine || o.embedCert || !o.roots.isEmpty then
        throw "verify-exe accepts only FILE [--closure FILE] [--equations FILE] \
          [--expect-target ADDR] [--expect-env ADDR] [--stats] and kernel limits"
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

def readBin (f : FilePath) : ExceptT Err IO ByteArray := do
  (IO.FS.readBinFile f).toBaseIO >>= fun
    | .ok b => pure b
    | .error e => throw (cliErr "cli.read" s!"{f}: {e}")

def readInputs (o : Options) : ExceptT Err IO (ByteArray × Lean.Json × ByteArray) := do
  let some closure := o.closure | throw (cliErr "cli.args" "no closure")
  let some eqs := o.equations | throw (cliErr "cli.args" "no equations")
  let bytes ← readBin closure
  let text ← (IO.FS.readFile eqs).toBaseIO >>= fun
    | .ok t => pure t
    | .error e => throw (cliErr "cli.read" s!"{eqs}: {e}")
  let json ← match (Src.Hints.checkJsonText text >>= fun () => Lean.Json.parse text) with
    | .ok j => pure j
    | .error e => throw { stage := .ingress, code := "hints", message := s!"{eqs}: {e}" }
  pure (bytes, json, text.toUTF8)

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

/-- **`check-cert`'s verifier**, on a certificate's text, and with `opt` (`compile --uncertified
--opt`) the replayed object rebuilt by `Backend.compileOpt` (the Lir SSA optimizer and a fresh back
end), which no certificate covers: its provenance is `uncertifiedProvenance` (pass policy
`optPassPolicy`, on the replay's lowering, 1 or 3). -/
def checkTextWith (opt : Bool) (cfg : Config) (inp : Input) (text : String) :
    Except Err (CliCert × Artifact) := do
  let cc ← CliCert.ofText text
  unless checkCanonicalRelevance cfg inp cc.base.table cc.base.relevance do
    throw { stage := .relevance, code := "relevance-canonical",
            message := "certificate relevance annotation does not match canonical annotator output" }
  match cc with
  | .zeroRc cert =>
    let a ← DefAsserts.runWithReading cfg inp.program inp.kernel.rd cert
    if !opt then
      return (cc, a)
    else
      let root := (a.src.roots.head?.map (·.1)).getD default
      let bcfg : Backend.Config :=
        { a.lowered.config (uncertifiedProvenance root 1 optPassPolicy) with env := cfg.env }
      let backend ← (Backend.compileOpt a.lowered.program bcfg).mapError Err.ofBackend
      return (cc, { a with backend })
  | .plainRc cert =>
    let rcArt ← DefAsserts.runRcWithReading cfg inp.program inp.kernel.rd cert
    let a ← rcArt.toRecheckArtifact cert
    if !opt then
      return (cc, a)
    else
      let root := (rcArt.front.src.roots.head?.map (·.1)).getD default
      let provenance := uncertifiedProvenance root 3 optPassPolicy
      let bcfg : Backend.Config :=
        { rcArt.front.lowered.config provenance with
          reps := rcArt.front.reps, env := rcArt.front.env cfg.env }
      let backend ← (Backend.compileOpt rcArt.front.lowered.program bcfg).mapError Err.ofBackend
      return (cc, { a with backend })

/-- **`check-cert`'s verifier**, on a certificate's text: the text read (`CliCert.ofText`), its
relevance annotation checked to be the annotator's (Stage A, `checkCanonicalRelevance`), the
certificate replayed (`run`, or `RcReplay.run` for a plain-RC certificate), and decoded Ixon v5
`Definition.asserts` enforced (`DefAsserts.checkWithReading` / `checkRcWithReading`). `compile`
runs it on the text it is about to write, so a successful compile is one whose written certificate
this accepts. -/
def checkText (cfg : Config) (inp : Input) (text : String) : Except Err (CliCert × Artifact) :=
  checkTextWith false cfg inp text

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
def withRetry {m : Type → Type} {ε : Type} [Monad m] [MonadExcept ε m] {α : Type} (cfg : Config)
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

def timed {ε α : Type} (action : ExceptT ε IO α) : ExceptT ε IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let r ← action
  return (r, (← IO.monoMsNow) - t0)

/-- A pure stage, evaluated when the action runs (so `timed` measures it). -/
def lift {α : Type} (x : Unit → Except Err α) : ExceptT Err IO α := ExceptT.mk (IO.lazyPure x)

/-- Resolve the `ix` executable path for on-demand `--bignat` bootstrap freezing. -/
private def resolveIxBin : IO String := do
  if let some envBin ← IO.getEnv "IX_BIN" then
    if !envBin.isEmpty then return envBin
  for p in [FilePath.mk "../.lake/build/bin/ix", FilePath.mk ".lake/build/bin/ix"] do
    if ← p.pathExists then return p.toString
  return "ix"

/-- Load (from `--bignat-lib` / `IX_BIGNAT_LIB`) or bootstrap-freeze `IxCC.BigNat.Entry`
and compile the zero-C, zero-GMP Phase 4 BigNat runtime library. -/
def loadBigNatLib (o : Options) : ExceptT Err IO Rt.BigNat.CompiledBigNatLib := do
  let libFile? : Option FilePath ← match o.bignatLib with
    | some f => pure (some f)
    | none =>
      match ← IO.getEnv "IX_BIGNAT_LIB" with
      | some s => pure (if s.isEmpty then none else some (FilePath.mk s))
      | none => pure none
  let frozen ← match libFile? with
    | some f =>
      let text ← readText f
      let j ← match Lean.Json.parse text with
        | .ok j => pure j
        | .error e => throw (cliErr "cli.bignat" s!"{f}: {e}")
      match BigNat.Bootstrap.FrozenLibrary.ofJson j with
      | .ok fl => pure fl
      | .error e => throw (cliErr "cli.bignat" s!"{f}: {e}")
    | none =>
      let (cwd, sourceFile) ← match ← IO.getEnv "IX_BIGNAT_ENTRY" with
        | some s =>
          if !s.isEmpty then pure (none, FilePath.mk s)
          else if ← (FilePath.mk "IxCC/BigNat/Entry.lean").pathExists then
            pure (none, FilePath.mk "IxCC/BigNat/Entry.lean")
          else if ← (FilePath.mk "IxCC/IxCC/BigNat/Entry.lean").pathExists then
            pure (some (FilePath.mk "IxCC"), FilePath.mk "IxCC/BigNat/Entry.lean")
          else
            throw (cliErr "cli.bignat" "cannot locate IxCC/BigNat/Entry.lean; pass --bignat-lib FILE or set IX_BIGNAT_ENTRY")
        | none =>
          if ← (FilePath.mk "IxCC/BigNat/Entry.lean").pathExists then
            pure (none, FilePath.mk "IxCC/BigNat/Entry.lean")
          else if ← (FilePath.mk "IxCC/IxCC/BigNat/Entry.lean").pathExists then
            pure (some (FilePath.mk "IxCC"), FilePath.mk "IxCC/BigNat/Entry.lean")
          else
            throw (cliErr "cli.bignat" "cannot locate IxCC/BigNat/Entry.lean; pass --bignat-lib FILE or set IX_BIGNAT_ENTRY")
      let ixBin ← resolveIxBin
      let stamp ← IO.monoNanosNow
      let fcfg : BigNat.Bootstrap.FreezeConfig :=
        { ix := ixBin
        , sourceFile
        , outDir := FilePath.mk s!"/tmp/ixcc-bignat-cli-{stamp}"
        , cwd
        , includeLimbEqns := false
        , ops := BigNat.Bootstrap.SlowPathOp.numericOps }
      match ← (BigNat.Bootstrap.freezeClosure fcfg).toBaseIO with
      | .ok fl => pure fl
      | .error e => throw (cliErr "cli.bignat" s!"{e}")
  match Rt.BigNat.compileLibrary frozen with
  | .ok lib => pure lib
  | .error e =>
    -- the BigNat runtime library is the compiler's own: its failing to compile (an array
    -- analysis past its bound among the reasons) is an internal error, not a usage error
    throw { stage := .rt, code := "rt.internal", message := s!"the BigNat runtime library does not compile: {e}" }

/-- Compile `inp` via the DR1/DR2/DR3/DR4 + Phase 4 arbitrary-precision `Nat` pipeline
(`Lam.Erase.Array → Anf → Fir → Fir.Rep → Own → Cfg → Rt.BigNat.lowerRepBig → Backend`),
optionally running the validated `Lir.Opt` SSA optimizer when `opt = true`. No certificate covers
the object (`compile --uncertified --bignat`): its provenance is `uncertifiedProvenance` (lowering
`bigNatLowering`, pass policy 1, or `optPassPolicy` with `opt`). The array analyses run to their
fixpoints first (`Rt.LowerRep.checkArrayAnalyses`), or the program is refused (`rt.internal`). -/
def compileBigNat (opt : Bool) (lib : Rt.BigNat.CompiledBigNatLib) (cfg : Config) (inp : Input) :
    Except Err (Artifact × List Xv.Alloc.Outcome × Array Src.Diag) := do
  let ps ← produceSource cfg inp
  let (lam, _, info) ← (Lam.Erase.Array.eraseWithArrays ps.src ps.checked .fixed [] none).mapError Err.ofErase
  let budgets : Anf.Pipeline.Budgets :=
    { cfg.budgets with inline := { cfg.budgets.inline with noInline := info.noInline } }
  let trace ← produceAnf budgets lam
  let (anf, _) ← produceClosures ps.src trace
  let fir ← (Fir.lower anf).mapError Err.ofFir
  let repCert := Fir.Rep.inferWithArrays fir info
  unless Fir.Rep.checkWithArrays fir repCert do
    throw { stage := .fir, code := "fir.rep", message := "Fir.Rep.checkWithArrays failed" }
  let own := Own.immortal fir
  let C := Cfg.lower own
  checkParams cfg C (List.zipIdx C.exports |>.map fun (f, i) => (i, f))
  (Rt.LowerRep.checkArrayAnalyses repCert C).mapError Err.ofRt
  let lowered0 ← (Rt.BigNat.lowerRepBig { names := cfg.names } lib repCert C).mapError Err.ofRt
  let prog0 := lowered0.program.splitCriticalEdges
  match prog0.check with
  | .ok () => pure ()
  | .error e => throw { stage := .rt, code := "rt.lir", message := toString e }
  let lirProg := if opt then Lir.Opt.run prog0 else prog0
  let lowered : Rt.Lowered := { lowered0 with program := lirProg }
  let (xv, _) ← (Xv.Select.run lirProg).mapError fun e =>
    { stage := .select, code := e.form, message := e.reason }
  let allocRes ← (Xv.Alloc.run cfg.env xv).mapError fun msg =>
    { stage := .alloc, code := "alloc", message := msg }
  let root := (ps.src.roots.head?.map (·.1)).getD default
  let provenance := uncertifiedProvenance root bigNatLowering (if opt then optPassPolicy else 1)
  let bcfg : Backend.Config := { lowered.config provenance with env := cfg.env }
  let backend ← (Backend.emit allocRes.program bcfg).mapError Err.ofBackend
  let rows := (List.range ps.src.roots.length).zip (ps.src.roots.zip (C.exports.zip lowered.roots))
  let roots := rootsOf cfg ps.src C lowered rows
  let art : Artifact :=
    { src := ps.src, checked := ps.checked, lam, anf, fir, own, cfg := C, lowered
    , xv, xl := allocRes.program, backend, roots }
  pure (art, allocRes.outcomes, ps.wordHints)

/-- Auto-discovered ingress when `--equations` is omitted: decodes the envelope, resolves
`--root` specs (`NAME`, `<64-hex>`, `NAME=<64-hex>`, or default `entry`/`main`), runs the
certified kernel's acceptance and N5 mode check, discovers `.eqn`/`.word` proposals from
theorem statements alone (`Src.AutoHints.discover`), and finishes Src ingress + faithful
reading. Returns `(input, proposalCount, autoHintsMs, eqBytes)`. -/
def ingressAuto (bytes : ByteArray) (roots : List String)
    (limits : Ix.Kernel.Admission.Limits) (needEqBytes : Bool) :
    ExceptT Err IO (Input × Nat × Nat × ByteArray) := do
  let env ← lift fun _ =>
    (Ixon.V3.decodeAnonymousEnv bytes).mapError fun m =>
      { stage := .ingress, code := "decode", message := m }
  let chosen ← lift fun _ =>
    (Src.AutoHints.resolveRoots env roots).mapError fun m =>
      { stage := .cli, code := "cli.root", message := m }
  let acc ← lift fun _ =>
    (Src.KernelFront.accept env limits).mapError fun r =>
      { stage := .ingress, code := (r.limit.map kernelLimitCode).getD "kernel", message := r.report }
  lift fun _ =>
    (Src.KernelFront.defaultModeCheck acc).mapError fun r =>
      { stage := .ingress, code := "mode-check", message := r.report }
  let pins := Src.KernelFront.pinsOfTable acc.table
  let (proposals, tAutoMs) ← timed (lift fun _ => .ok (Src.AutoHints.discover env pins))
  let names := chosen.toList.zipIdx.map fun ((_, n), i) => n.getD s!"root{i}"
  let namedRoots := chosen.zipIdx.map fun ((a, n), i) => (a, some (n.getD s!"root{i}"))
  let hints : Src.Hints := { roots := namedRoots, proposals }
  let records ← lift fun _ =>
    (Src.Ingress.reach env (Src.Ingress.Seeds.of hints pins)).mapError fun m =>
      { stage := .ingress, code := "decode", message := m }
  let p ← lift fun _ =>
    (Src.Ingress.readConsts env records (namedRoots.map (·.1))).mapError fun m =>
      { stage := .ingress, code := "ingress", message := m }
  let p := { p with known := { pins } }
  let p := { p with known := Src.Pinned.known p }
  let rd ← lift fun _ =>
    (Src.KernelFront.Reading.build acc p).mapError fun m =>
      { stage := .ingress, code := "faithful", message := m }
  let inp : Input := { env, hints, program := p, names, kernel := { acc, rd, fe := Ix.Kernel.mkFEnv acc.env } }
  let eqBytes := if needEqBytes then (Src.Hints.toK1Json hints).compress.toUTF8 else ByteArray.empty
  pure (inp, proposals.size, tAutoMs, eqBytes)

/-! ## Outcomes and exit statuses -/

/-- How a run of `ixcc` failed, as its exit status reports it (`Outcome.exitCode`; the module's
table). -/
inductive Outcome where
  /-- The program is outside what the compiler accepts (exit 1). -/
  | declined
  /-- The command line is malformed, or a file or root it names cannot be used (exit 2). -/
  | usage
  /-- A certificate or an artifact failed a check (exit 3). -/
  | rejected
  /-- The compiler failed in a way that is its own fault (exit 4). -/
  | internal
  deriving DecidableEq, Repr, Inhabited

def Outcome.exitCode : Outcome → UInt32
  | .declined => 1
  | .usage => 2
  | .rejected => 3
  | .internal => 4

/-- A failed run: its outcome and its error. -/
structure Failure where
  outcome : Outcome
  err : Err
  deriving Inhabited

/-- The outcome of `e`, raised in a step whose failures are `k`: `cli.*` codes are usage errors,
`rt.internal` the compiler's own failure and `assert.*` a declined program wherever they arise;
any other code takes the step's outcome. -/
def classify (k : Outcome) (e : Err) : Outcome :=
  if e.code.startsWith "cli." then .usage
  else if e.code == "rt.internal" then .internal
  else if e.code.startsWith "assert." then .declined
  else k

/-- A step whose failures are `k` (`classify`). -/
def phase {α : Type} (k : Outcome) (x : ExceptT Err IO α) : ExceptT Failure IO α :=
  ExceptT.adapt (fun e => { outcome := classify k e, err := e }) x

/-- A failure of outcome `k` with error `e`. -/
def failure {α : Type} (k : Outcome) (e : Err) : ExceptT Failure IO α := throw { outcome := k, err := e }

/-! ## Outputs, all or nothing -/

/-- A file a run writes, whole. -/
structure Output where
  path : FilePath
  bytes : ByteArray
  /-- Mode 0755 (an executable), else as created. -/
  executable : Bool := false

/-- Remove `f` if it is a regular file or a symbolic link (never a directory or a device);
errors are ignored. -/
def removeFileIfAny (f : FilePath) : IO Unit := do
  match ← f.symlinkMetadata.toBaseIO with
  | .ok m =>
    if m.type == .file || m.type == .symlink then
      try IO.FS.removeFile f catch _ => pure ()
  | .error _ => pure ()

/-- Remove the files a run of `o` would have written (`Options.outputs`): a failed run leaves none
of them, stale or partial. -/
def removeOutputs (o : Options) : IO Unit := do
  for f in o.outputs do removeFileIfAny f

def writeOutput (f : FilePath) (out : Output) : IO Unit := do
  IO.FS.writeBinFile f out.bytes
  if out.executable then
    IO.setAccessRights f { user := { read := true, write := true, execution := true }
                           group := { read := true, execution := true }
                           other := { read := true, execution := true } }

/-- Write `outs` all or nothing: each to a temporary file beside it, then each renamed into
place; if any write or rename fails, every temporary file and every one of `outs` is removed
(`cli.write`, a usage error). -/
def commit (outs : List Output) : ExceptT Failure IO Unit := do
  if outs.isEmpty then return
  let pid ← IO.Process.getPID
  let stamp ← IO.monoNanosNow
  let tmp := fun (out : Output) => FilePath.mk s!"{out.path}.tmp.{pid}.{stamp}"
  let fail : FilePath → IO.Error → ExceptT Failure IO Unit := fun f e => do
    for out in outs do removeFileIfAny (tmp out)
    for out in outs do removeFileIfAny out.path
    failure .usage (cliErr "cli.write" s!"{f}: {e}")
  for out in outs do
    match ← (writeOutput (tmp out) out).toBaseIO with
    | .ok () => pure ()
    | .error e => fail out.path e
  for out in outs do
    match ← (IO.FS.rename (tmp out) out.path).toBaseIO with
    | .ok () => pure ()
    | .error e => fail out.path e

/-- What a run writes and prints on standard output, computed before anything is written. -/
structure Plan where
  outputs : Array Output := #[]
  stdout : Array String := #[]

/-! ## Running a command -/

/-- The line `ixcc compile --uncertified` prints on standard error at every run. -/
def uncertifiedLine (o : Options) : Option String :=
  if !o.uncertified then none
  else if o.bignat then
    some s!"ixcc: uncertified ({(o.uncertifiedMode).getD "--bignat"}): what this run writes is not \
      covered by certificate replay (no certificate is produced or checked); its provenance note \
      says so (lowering {bigNatLowering}, pass policy 0x8000000{if o.opt then optPassPolicy else 1})"
  else
    some s!"ixcc: uncertified (--opt): what this run writes is not covered by certificate replay \
      (Backend.compileOpt rebuilds the object after the replay); its provenance note says so \
      (pass policy 0x8000000{optPassPolicy})"

/-- Under `--opt` or `--bignat` (`mode`), a program any of whose constants carries a definition
assertion (`@[no_alloc]`, `@[no_rc]`, `@[bounded_stack]`) is declined: neither mode checks them on
the object it writes (`--opt` would check the replayed object, not the one rebuilt; `--bignat`
nothing). -/
def refuseAsserts (mode : String) (inp : Input) : Except Err Unit :=
  match (inp.kernel.rd.assertsMap inp.program).toList with
  | [] => .ok ()
  | as@((c, _) :: _) =>
    .error { stage := .rt, code := "assert.uncertified"
             message := s!"{as.length} constant(s) carry definition assertions (@[no_alloc], \
               @[no_rc], @[bounded_stack]), the first at {inp.program.addr c}, and {mode} does not \
               check them on the object it writes; compile without {mode} to have them checked" }

/-- The claim `--embed-cert` binds, as it prints it. -/
def claimLine (c : CompileClaim) : String :=
  s!"executable certificate verified: target {c.target}, policy {repr c.policy}, \
    environment root {c.env}"

/-- `--embed-cert`: the certified executable of `a` (`Exe.Cert.buildCertifiedExe`), its claim
binding the policy `Exe.Cert.policyOfArtifact` gives (a refusal by its recheck is a rejection,
never a weaker label), once `verify` (the executable verifier, `Exe.Cert.verifyExeBytes`, what
`verify-exe` runs, under the run's kernel limits) has accepted the very bytes to be written and
returned the claim built (else rejected, and nothing is written). -/
def embedCertified (cfg : Config) (inp : Input) (rootSelection : List String) (cc : CliCert)
    (text : String) (a : Artifact) (kind : X86.Exe.Cert.ExeKind) (layout : X86.Exe.Layout)
    (envBytes eqBytes : ByteArray) (limits : Ix.Kernel.Admission.Limits)
    (verify : ByteArray → Except Err Exe.Cert.VerifiedExe :=
      fun b => Exe.Cert.verifyExeBytes b none none limits) :
    ExceptT Failure IO Exe.Cert.BuiltCertifiedExe := do
  let isPlainRc := match cc with | .plainRc _ => true | .zeroRc _ => false
  let policy ← phase .rejected (lift fun _ => Exe.Cert.policyOfArtifact cfg inp a isPlainRc text)
  let built ← phase .declined (lift fun _ =>
    Exe.Cert.buildCertifiedExe inp rootSelection policy text a kind layout envBytes eqBytes)
  let v ← phase .rejected (lift fun _ => verify built.bytes)
  unless v.claim == built.claim do
    failure .rejected (Exe.err "exe.cert.claim"
      "the executable verifier returned another claim than the one built")
  pure built

/-! ## The default path: the pure compiler -/

/-- Whether a run takes the default path (`compile` with no `--equations` sidecar, no
given certificate and no uncertified mode): its one root is compiled by
`IxCC.Compile.compile`. -/
def Options.defaultPath (o : Options) : Bool :=
  o.command == "compile" && o.equations.isNone && o.cert.isNone && !o.uncertified && !o.opt &&
    !o.bignat

/-- The pure compiler's policy request for `--rc`. -/
def RcMode.toCompile : RcMode → Compile.Rc
  | .off => .off
  | .on => .on
  | .auto => .auto

/-- The outcome of a refusal of `Compile.check` or `Compile.build`: the policy recheck
(`exe.cert.policy`), the seed-closure check (`kf4`) and the certificate checker's Stage A
(`relevance-canonical`) are rejections (an artifact failed a check); anything else is a
decline (`classify`: `cli.*` usage, `rt.internal` internal, `assert.*` declined; a kernel
limit exits 6, `main`). -/
def compileOutcome (e : Err) : Outcome :=
  if e.code == "exe.cert.policy" || e.code == "kf4" || e.code == "relevance-canonical" then .rejected
  else classify .declined e

/-- A pure step of the compiler, its refusal classified by `compileOutcome`. -/
def compileStep {α : Type} (x : Unit → Except Err α) : ExceptT Failure IO α :=
  ExceptT.adapt (fun e => { outcome := compileOutcome e, err := e }) (lift x)

/-- The policy line `--rc auto` prints: the reason plain RC was refused (`Checked.note`), or the
policy compiled under. -/
def policyLine (c : Compile.Checked) : String :=
  match c.note with
  | some n => n
  | none =>
    match c.policy with
    | .zeroRc => "zero-rc"
    | .plainRc => "plain-rc"
    | .immortal => "immortal"

/-- The certificate `check` accepted, in the zero-RC format's shape (its base). -/
def checkedCert (c : Compile.Checked) : Cert :=
  match c.replay with
  | .zero cert _ => cert
  | .plain cert _ _ => cert.base

/-- **`--embed-cert` on the default path**: the returned executable with the `.ix.cert` v1
trailer made from what `compile` returned (the claim's six-field projection
`Compile.Claim.legacy`, the certificate text, the environment's bytes, the derived hints as a
sidecar, the root's name), once the executable verifier (`Exe.Cert.verifyExeBytes`, what
`verify-exe` runs, under the run's kernel limits) has accepted these very bytes and returned
that claim (else rejected, and nothing is written). The core under the trailer is the returned
executable, byte for byte. -/
def embedOutput (envBytes : ByteArray) (opts : Compile.Options) (c : Compile.Checked)
    (out : Compile.Output) (limits : Ix.Kernel.Admission.Limits)
    (verify : ByteArray → Except Err Exe.Cert.VerifiedExe :=
      fun b => Exe.Cert.verifyExeBytes b none none limits) :
    ExceptT Failure IO (ByteArray × Nat × CompileClaim) := do
  let payload : X86.Exe.Cert.Payload := {
    exeKind := opts.kind
    stack := opts.layout.stack
    region := opts.layout.region
    rootNames := c.inp.names
    claimBytes := out.claim.legacy.toClaimBytes
    certBytes := out.cert.toUTF8
    envBytes
    eqBytes := (Src.Hints.toK1Json c.inp.hints).compress.toUTF8 }
  let encoded := payload.encode
  let file ← phase .declined (lift fun _ => (X86.Exe.Cert.attachTrailer out.exe encoded).mapError fun e =>
    Exe.err "exe.cert.attach" e.render)
  let v ← phase .rejected (lift fun _ => verify file)
  unless v.claim == out.claim.legacy do
    failure .rejected (Exe.err "exe.cert.claim"
      "the executable verifier returned another claim than the one compiled")
  pure (file, encoded.size, out.claim.legacy)

/-- **The default path** (`Options.defaultPath`): read the closure, resolve `--root` to one
address and name (`Src.AutoHints.resolveRoots`, a pure step; the name is an option of
`compile`), then `Compile.check` and, when an executable is asked for, `Compile.build`:
`compile` exactly. Everything written comes from what they return: `-o` the object `check`'s
artifact holds, `--exe` the executable `build` returned (with `--embed-cert` its trailer),
`--emit-cert` the certificate text `check` accepted, `--signatures` and `--dump-ir` the
artifact. Without `--exe` only `check` runs (the object needs no executable). `none` when
`--root` names several roots: that run takes the sidecar-free multi-root path below. -/
def defaultPlan? (o : Options) (limits : Ix.Kernel.Admission.Limits) :
    ExceptT Failure IO (Option Plan) := do
  let some closure := o.closure | failure .usage (cliErr "cli.args" "no closure")
  let (bytes, tRead) ← phase .usage (timed (readBin closure))
  let env ← phase .declined (lift fun _ =>
    (Ixon.V3.decodeAnonymousEnv bytes).mapError fun m => { stage := .ingress, code := "decode", message := m })
  let chosen ← phase .usage (lift fun _ =>
    (Src.AutoHints.resolveRoots env o.roots).mapError fun m => cliErr "cli.root" m)
  let #[(target, name)] := chosen | return none
  let opts : Compile.Options :=
    { rc := o.rc.toCompile, kind := if o.machine then .machine else .plain, layout := o.layout
      kernelLimits := limits, name }
  let t0 ← IO.monoMsNow
  let c ← compileStep fun _ => Compile.check bytes target opts
  let tCheck := (← IO.monoMsNow) - t0
  if let some l := Src.Table.wordHintLine c.wordHints then IO.eprintln l
  let a := c.replay.artifact
  let mut outputs : Array Output := #[]
  let mut stdout : Array String := #[]
  if let some f := o.out then outputs := outputs.push { path := f, bytes := a.object }
  if let some f := o.exe then
    let out ← compileStep fun _ => Compile.build target opts c
    let (exeBytes, certInfo?) ← if o.embedCert then do
        let (file, paySz, claim) ← embedOutput bytes opts c out limits
        pure (file, some (paySz, claim))
      else pure (out.exe, none)
    outputs := outputs.push { path := f, bytes := exeBytes, executable := true }
    if let some (_, claim) := certInfo? then stdout := stdout.push (claimLine claim)
    if o.stats then
      let sizes := match certInfo? with
        | some (paySz, _) => s!"core {out.exe.size}, .ix.cert {paySz}, "
        | none => ""
      stdout := stdout.push s!"executable: {exeBytes.size} bytes ({sizes}object text \
        {a.backend.encoded.text.size}), stack {o.layout.stack} bytes, region {o.layout.region} bytes"
  if let some f := o.emitCert then outputs := outputs.push { path := f, bytes := c.cert.toUTF8 }
  if let some f := o.signatures then
    outputs := outputs.push { path := f, bytes := ((signaturesJson a).pretty ++ "\n").toUTF8 }
  for l in o.dumps do
    stdout := stdout.push s!"== {l} =="
    stdout := stdout.push (dump a l)
  if o.rc == .auto then stdout := stdout.push s!"rc policy: {policyLine c}"
  if o.stats then
    stdout := stdout.push (envelopeLine c.inp)
    stdout := stdout.push s!"kernel: accepted {c.inp.kernel.acc.records.length} records, \
      {c.inp.kernel.acc.decls.size} logical declarations and {c.inp.kernel.acc.tier.length} tier constants, \
      within ingress"
    stdout := stdout.push s!"auto-hints: {c.inp.hints.proposals.size} proposals (derived by compile)"
    let cert := checkedCert c
    let certBytes := if c.cert.endsWith "\n" then c.cert.utf8ByteSize - 1 else c.cert.utf8ByteSize
    stdout := stdout.push s!"time: read {tRead} ms, compile {tCheck} ms (ingress with the kernel's \
      acceptance, the producer, the certificate checker and the seed-closure check)"
    stdout := stdout.push s!"certificate: {certBytes} bytes of JSON; {cert.table.resolve.length} table entries, \
      {cert.relevance.nodes.length} annotated terms, {cert.mid.steps.length} middle-end steps, \
      {cert.alloc.length} allocations, {cert.frames.length} frame layouts"
    stdout := stdout.push s!"claim: policy {repr c.policy}, role table {c.roleTable}, target {target}"
    for l in statsLines a (some c.alloc) do stdout := stdout.push l
    for d in c.wordHints do stdout := stdout.push s!"hint: {d.message}"
  pure (some { outputs, stdout })

/-- `verify-exe`, the kernel under `limits`. -/
def verifyPlan (o : Options) (limits : Ix.Kernel.Admission.Limits) : ExceptT Failure IO Plan := do
  let some f := o.verifyExe | failure .usage (cliErr "cli.args" "no executable given")
  let (exeBytes, tRead) ← phase .usage (timed (readBin f))
  let extEnv? ← phase .usage (match o.closure with
    | some cf => some <$> readBin cf
    | none => pure none)
  let extEq? ← phase .usage (match o.equations with
    | some ef => some <$> readBin ef
    | none => pure none)
  let (v, tVerify) ← phase .rejected (timed (lift fun _ =>
    Exe.Cert.verifyExeBytes exeBytes extEnv? extEq? limits))
  if let some t := o.expectTarget then
    unless v.claim.target == t do
      failure .rejected (Exe.err "exe.cert.expect"
        s!"the executable's claim names target {v.claim.target}, not {t} (--expect-target)")
  if let some e := o.expectEnv then
    unless v.claim.env == e do
      failure .rejected (Exe.err "exe.cert.expect"
        s!"the executable's claim names environment root {v.claim.env}, not {e} (--expect-env)")
  let kindStr := match v.exeKind with | .plain => "plain" | .machine => "machine"
  let roleTable := match v.claim.roleTable with
    | some r => toString r
    | none => "none (an unbound environment)"
  let mut out := #[s!"executable verified: kind {kindStr}, target {v.claim.target}, policy {repr v.claim.policy}, \
      arity {v.claim.abiArity}, core {v.coreSize} bytes, .ix.cert {v.payloadSize} bytes, \
      object {v.objectSize} bytes (blake3 {v.claim.elfHash})",
    s!"environment: root {v.claim.env}, role table {roleTable}"]
  if o.stats then
    out := out.push s!"layout: stack {v.layout.stack} bytes, region {v.layout.region} bytes, roots {v.rootNames}"
    out := out.push s!"time: read {tRead} ms, verify {tVerify} ms"
  pure { stdout := out }

/-- `compile` and `check-cert`, the kernel under `limits`: everything they write and print. -/
def compilePlan (o : Options) (limits : Ix.Kernel.Admission.Limits) : ExceptT Failure IO Plan := do
  -- the default path: `Compile.check` and `Compile.build`, exactly (`defaultPlan?`)
  if o.defaultPath then
    if let some plan ← defaultPlan? o limits then return plan
  let (bytes, eqBytes, inp, tRead, tIngress, autoStats?, certRoots) ← phase .declined do
    match o.equations with
    | some _ =>
      let ((bytes, json, eqBytes), tRead) ← timed (readInputs o)
      let (inp, tIngress) ← timed (lift fun _ => ingress bytes json o.roots limits)
      pure (bytes, eqBytes, inp, tRead, tIngress, (none : Option (Nat × Nat)), o.roots)
    | none =>
      let some closure := o.closure | throw (cliErr "cli.args" "no closure")
      let (bytes, tRead) ← timed (readBin closure)
      let ((inp, nProps, tAutoMs, eqBytes), tIngress) ← timed (ingressAuto bytes o.roots limits o.embedCert)
      pure (bytes, eqBytes, inp, tRead, tIngress, some (nProps, tAutoMs), inp.names)
  let cfg := Config.forInput {} inp
  -- a root whose caller would pass a closure has no meaningful caller: refused
  -- before anything is produced (every producer refuses it too, `produceClosures`)
  if o.command == "compile" then phase .declined (lift fun _ => checkFnParams cfg.names inp.program)
  -- the uncertified modes check no definition assertion on what they write
  if let some mode := o.uncertifiedMode then phase .declined (lift fun _ => refuseAsserts mode inp)
  -- `policy`: the policy `--rc auto` compiled under, reported on standard output.
  -- The certificate text (the producer's, read back inside the producer, or the given file's),
  -- then `check-cert`'s verifier on that text (`checkText`): the object and everything written
  -- come from its verdict on the text that is written. Without a given certificate, with the
  -- middle end's inline-round retry first and, if that fails at any stage, without it
  -- (`withRetry`; each run is the proved composition at its own configuration).
  let (text?, cliCert?, outcomes, policy, tProduce, a, tRun, hints) ←
    if o.bignat then
      let (lib, tLib) ← phase .declined (timed (loadBigNatLib o))
      let ((a, outcomes, hints), tComp) ← timed (withRetry cfg fun cfg =>
        phase .declined (lift fun _ => compileBigNat o.opt lib cfg inp))
      pure (none, none, some outcomes, none, tLib, a, tComp, hints)
    else
      let produceRun := fun (cfg : Config) => show ExceptT Failure IO _ from do
        let ((text, outcomes, policy, hints), tProduce) ← timed do
          match o.cert with
          | some f => pure (← phase .usage (readText f), none, none, #[])
          | none =>
            let (text, outcomes, policy, hints) ← phase .declined (lift fun _ => produceText o.rc cfg inp)
            pure (text, some outcomes, policy, hints)
        let ((cliCert, a), tRun) ← timed (phase .rejected (lift fun _ => checkTextWith o.opt cfg inp text))
        pure (some text, some cliCert, outcomes, policy, tProduce, a, tRun, hints)
      if o.cert.isNone then withRetry cfg produceRun else produceRun cfg
  if let some l := Src.Table.wordHintLine hints then IO.eprintln l
  let mut outputs : Array Output := #[]
  let mut stdout : Array String := #[]
  if let some f := o.out then outputs := outputs.push { path := f, bytes := a.object }
  if let some f := o.exe then
    -- the bytes and the placement of the executable `--exe` or `--machine` writes
    let (exeBytes, p, certInfo?) ← if o.embedCert then do
        let some cliCert := cliCert? | failure .usage (cliErr "cli.args" "cannot combine --embed-cert with --bignat")
        let some text := text? | failure .usage (cliErr "cli.args" "cannot combine --embed-cert with --bignat")
        let exeKind : X86.Exe.Cert.ExeKind := if o.machine then .machine else .plain
        let built ← embedCertified cfg inp certRoots cliCert text a exeKind o.layout bytes eqBytes limits
        pure (built.bytes, built.placement, some (built.coreSize, built.payloadSize, built.claim))
      else if o.machine then do
        let L : X86.Exe.Machine.Layout := { stack := o.layout.stack, region := o.layout.region }
        let ⟨_, exe⟩ ← phase .declined (lift fun _ => Exe.buildMachine a L)
        pure (exe.checked.bytes, exe.checked.plan.placement, none)
      else do
        let ⟨_, exe⟩ ← phase .declined (lift fun _ => Exe.build a o.layout)
        pure (exe.bytes, exe.plan.placement, none)
    outputs := outputs.push { path := f, bytes := exeBytes, executable := true }
    if let some (_, _, claim) := certInfo? then stdout := stdout.push (claimLine claim)
    if o.stats then
      match certInfo? with
      | some (coreSz, certSz, _) =>
        stdout := stdout.push s!"executable: {exeBytes.size} bytes (core {coreSz}, .ix.cert {certSz}, \
          object text {p.textSize}, shell {p.shellSize}), \
          stack {o.layout.stack} bytes, region {o.layout.region} bytes"
      | none =>
        stdout := stdout.push s!"executable: {exeBytes.size} bytes (object text {p.textSize}, shell {p.shellSize}), \
          stack {o.layout.stack} bytes, region {o.layout.region} bytes"
  -- exactly the text that was verified
  if let (some f, some text) := (o.emitCert, text?) then outputs := outputs.push { path := f, bytes := text.toUTF8 }
  if let some f := o.signatures then
    outputs := outputs.push { path := f, bytes := ((signaturesJson a).pretty ++ "\n").toUTF8 }
  for l in o.dumps do
    stdout := stdout.push s!"== {l} =="
    stdout := stdout.push (dump a l)
  if o.command == "check-cert" then
    stdout := stdout.push s!"certificate accepted: object {a.object.size} bytes, text {a.backend.encoded.text.size} bytes, \
      exports {a.roots.map (·.symbol)}"
  if let some p := policy then stdout := stdout.push s!"rc policy: {p}"
  if o.stats then
    stdout := stdout.push (envelopeLine inp)
    stdout := stdout.push s!"kernel: accepted {inp.kernel.acc.records.length} records, \
      {inp.kernel.acc.decls.size} logical declarations and {inp.kernel.acc.tier.length} tier constants, \
      within ingress"
    if let some (nProps, tAuto) := autoStats? then
      stdout := stdout.push s!"auto-hints: {nProps} proposals in {tAuto} ms"
    match cliCert?, text? with
    | some cliCert, some text =>
      let cert := cliCert.base
      let certBytes := if text.endsWith "\n" then text.utf8ByteSize - 1 else text.utf8ByteSize
      let producer := if o.cert.isSome then "certificate read" else "produce"
      stdout := stdout.push s!"time: read {tRead} ms, ingress {tIngress} ms (the kernel's acceptance included), \
        {producer} {tProduce} ms, run {tRun} ms"
      stdout := stdout.push s!"certificate: {certBytes} bytes of JSON; {cert.table.resolve.length} table entries, \
        {cert.relevance.nodes.length} annotated terms, {cert.mid.steps.length} middle-end steps, \
        {cert.alloc.length} allocations, {cert.frames.length} frame layouts"
    | _, _ =>
      stdout := stdout.push s!"time: read {tRead} ms, ingress {tIngress} ms (the kernel's acceptance included), \
        bignat-lib {tProduce} ms, compile {tRun} ms"
      stdout := stdout.push "bignat: enabled (DR1/DR2/DR3/DR4 + Phase 4 arbitrary-precision Nat, zero C/GMP)"
    if o.opt then stdout := stdout.push "lir.opt: enabled (Backend.compileOpt; not covered by certificate replay)"
    for l in statsLines a outcomes do stdout := stdout.push l
    for d in hints do stdout := stdout.push s!"hint: {d.message}"
  pure { outputs, stdout }

/-- `compile`, `check-cert`, and `verify-exe`, the kernel under `limits`: everything computed
(`compilePlan`, `verifyPlan`), then written all or nothing (`commit`) and printed. A failure
writes nothing and removes the files the run would have written (`removeOutputs`). -/
def executeWith (o : Options) (limits : Ix.Kernel.Admission.Limits := Src.KernelFront.defaultLimits) :
    ExceptT Failure IO Unit := do
  if let some l := uncertifiedLine o then IO.eprintln l
  let plan ← tryCatch (if o.command == "verify-exe" then verifyPlan o limits else compilePlan o limits)
    fun f => do removeOutputs o; throw f
  commit plan.outputs.toList
  for l in plan.stdout do IO.println l

/-- `executeWith`, its failure as its error alone. -/
def execute (o : Options) (limits : Ix.Kernel.Admission.Limits := Src.KernelFront.defaultLimits) :
    ExceptT Err IO Unit :=
  ExceptT.adapt Failure.err (executeWith o limits)

/-- The kernel's limits: the flags (the last of each), else the `IX_KERNEL_*` variables, else
IxCC's decoder caps (`Src.KernelFront.defaultLimits`, depth 16,384). -/
def settingsOf (o : Options) : IO (Except String Ix.Kernel.Host.Resolved) :=
  Ix.Kernel.Host.resolveIO Src.KernelFront.defaultLimits fun s => (o.kernel.reverse.find? (·.1 == s)).map (·.2)

/-- The limit an error is a decline by (`Recheck.kernelLimitCode`). -/
def limitOfCode (code : String) : Option Ix.Kernel.Admission.Resource :=
  [Ix.Kernel.Admission.Resource.records, Ix.Kernel.Admission.Resource.blobs,
    Ix.Kernel.Admission.Resource.totalBytes, Ix.Kernel.Admission.Resource.recordBytes,
    Ix.Kernel.Admission.Resource.recordUnivNodes, Ix.Kernel.Admission.Resource.depth,
    Ix.Kernel.Admission.Resource.levelBudget].find?
    (kernelLimitCode · == code)

/-- The command line; the exit code (the module's table): 0, 1 declined, 2 a usage error, 3
rejected, 4 an internal error, 6 a decline by a kernel limit (with one more line naming the
setting). -/
def main (args : List String) : IO UInt32 := do
  if args == ["--help"] || args == ["-h"] || args.isEmpty then
    IO.println usage
    return (if args.isEmpty then Outcome.usage.exitCode else 0)
  match parse args with
  | .error e =>
    IO.eprintln s!"ixcc: {e}\n{usage}"
    return Outcome.usage.exitCode
  | .ok o =>
    try
      let settings ← match ← settingsOf o with
        | .ok s => pure s
        | .error e => IO.eprintln s!"ixcc: {e}\n{usage}"; return Outcome.usage.exitCode
      if let some h := Ix.Kernel.Host.header settings then IO.eprintln s!"ixcc: {h}"
      match ← (executeWith o settings.limits).run with
      | .ok () => return 0
      | .error f =>
        IO.eprintln s!"ixcc: {f.err.render}"
        match limitOfCode f.err.code with
        | some r =>
          IO.eprintln s!"ixcc: {Ix.Kernel.Host.declineMessage settings r}"
          return Ix.Kernel.Host.exitDeclined
        | none => return f.outcome.exitCode
    catch e =>
      try IO.eprintln s!"ixcc: internal error: {e}" catch _ => pure ()
      removeOutputs o
      return Outcome.internal.exitCode

end IxCC.Cli
