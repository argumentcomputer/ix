import IxCC.Recheck
import IxCC.Recheck.Rc.Produce
import IxCC.Anf.Print
import IxCC.Fir.Print
import IxCC.Cfg.Print
import IxCC.Lir.Print
import IxCC.Xv.Print
import IxCC.Exe

/-! # The `ixcc` command line

```text
ixcc compile CLOSURE.ixe --equations EQ.json [--root NAME]... -o OUT.o
    [--rc off|on|auto] [--cert FILE] [--emit-cert FILE] [--signatures FILE]
    [--dump-ir LEVEL]... [--stats] [--no-typecheck]
    [--exe FILE [--machine] [--stack BYTES] [--region BYTES]]
ixcc check-cert CLOSURE.ixe --equations EQ.json [--root NAME]... --cert FILE
    [-o OUT.o] [--signatures FILE] [--stats] [--no-typecheck]
```

`compile` runs ingress, `produce` and `Recheck.run` and writes the ELF
object: `cx_<root>` for each root (the sidecar's names; every sidecar root
when no `--root` is given) and `cx_init` (`IxCC.X86.Driver` models how they are
called; `--exe` writes an executable that calls them). With `--cert`, the
given certificate replaces `produce`'s (so the recheck needs nothing from the
producer); `--emit-cert` writes the certificate used. `check-cert` runs
`Recheck.run` on a certificate and reports acceptance or the rejection. A
certificate's format fixes its RC policy, so `--rc` with `--cert` (and so with
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

`--rc off` (the default) compiles a zero-RC-format certificate on the immortal
backend, `--rc on` under plain RC (which may refuse the program). `--rc auto`
follows `RcReplay.produceAuto`: zero RC when `Own.Plain.selectRcPolicyForSrc`
selects it; plain RC when it selects that and the plain-RC certificate is
produced and replayed; otherwise the immortal policy. It prints
`rc policy: …` naming the policy it compiled under.

`--signatures FILE` writes, per root, its symbol, parameter count and the text
forms of its result type and signature (`type`, `sig`; JSON; `null` when bounded ground
first-order signature discovery does not support the result type).
`--dump-ir LEVEL` prints a level (`lam`, `anf`, `fir`,
`cfg`, `lir`, `xv`, `xl`, or `all`) to standard output; `--stats` prints
the closure's envelope, constant root and role table address, timings, sizes
and the allocation outcomes. The closure is either envelope: role-bound
(`0xE5`, as `ix compile` writes it) or unbound (`0xE4`). `--no-typecheck` skips erased
typing at ingress (the fixtures' typing is gated by `tests-ixon-v3`).

A decline or rejection prints `ixcc: stage: code: message` on
standard error and exits 1; a usage error exits 2. -/

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
  typecheck : Bool := true
  rc : RcMode := .off
  rcExplicit : Bool := false
  /-- `--exe FILE`: also write a standalone executable of the first root. -/
  exe : Option FilePath := none
  /-- The executable's stack and region (`--stack`, `--region`, in bytes). -/
  layout : X86.Exe.Layout := {}
  layoutGiven : Bool := false
  /-- `--machine`: the executable runs a numeric state machine (`Exe.buildMachine`). -/
  machine : Bool := false
  deriving Inhabited

def usage : String :=
  "\n".intercalate [
    "usage:",
    "  ixcc compile CLOSURE.ixe --equations EQ.json [--root NAME]... -o OUT.o",
    "      [--rc off|on|auto] [--cert FILE] [--emit-cert FILE] [--signatures FILE] [--dump-ir LEVEL]... [--stats] [--no-typecheck]",
    "      [--exe FILE [--machine] [--stack BYTES] [--region BYTES]]",
    "  ixcc check-cert CLOSURE.ixe --equations EQ.json [--root NAME]... --cert FILE",
    "      [-o OUT.o] [--signatures FILE] [--stats] [--no-typecheck]",
    "dump levels: lam anf fir cfg lir xv xl all"]

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
  | "--no-typecheck" :: rest => parseRest { o with typecheck := false } rest
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
for a role-bound envelope, the binding hash (the role table's address). -/
def envelopeLine (env : Ixon.V3.Env) : String :=
  match env.binding with
  | some b =>
    s!"environment: role-bound (0xE5), root {env.root}, role table {b.address} \
      ({b.table.bound.length} roles bound, specification version {b.table.version})"
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

def CliCert.toText : CliCert → String
  | .zeroRc c => c.toText
  | .plainRc c => c.toText

def CliCert.base : CliCert → Cert
  | .zeroRc c => c
  | .plainRc c => c.base

def readCert (f : FilePath) : ExceptT Err IO Cert := do
  let text ← (IO.FS.readFile f).toBaseIO >>= fun
    | .ok t => pure t
    | .error e => throw (cliErr "cli.read" s!"{f}: {e}")
  ExceptT.mk (pure (Cert.ofText text))

def readCliCert (f : FilePath) : ExceptT Err IO CliCert := do
  let text ← (IO.FS.readFile f).toBaseIO >>= fun
    | .ok t => pure t
    | .error e => throw (cliErr "cli.read" s!"{f}: {e}")
  if text.trimAscii.toString.startsWith "[\"ixcc/rc-cert/2\"" then
    match RcReplay.Cert.ofText text with
    | .ok c => pure (.plainRc c)
    | .error m => throw { stage := .cert, code := "cert.parse", message := m }
  else
    ExceptT.mk (pure ((Cert.ofText text).map .zeroRc))

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

/-- `compile` and `check-cert`. -/
def execute (o : Options) : ExceptT Err IO Unit := do
  let ((bytes, json), tRead) ← timed (readInputs o)
  let (inp, tIngress) ← timed (lift fun _ => ingress bytes json o.roots o.typecheck)
  let cfg := Config.forInput {} inp
  -- `policy`: the policy `--rc auto` compiled under, reported on standard output
  let ((cliCert, outcomes, policy), tProduce) ← timed do
    match o.cert with
    | some f =>
      let cc ← readCliCert f
      unless checkCanonicalRelevance cfg inp cc.base.table cc.base.relevance do
        throw { stage := .relevance, code := "relevance-canonical",
                message := "certificate relevance annotation does not match canonical annotator output" }
      pure (cc, none, none)
    | none =>
      match o.rc with
      | .off =>
        let p ← lift fun _ => produceWith cfg inp
        pure (.zeroRc p.cert, some p.alloc, none)
      | .on =>
        let p ← lift fun _ => RcReplay.produceWith cfg inp
        pure (.plainRc p.cert, some p.alloc, none)
      | .auto =>
        -- `RcReplay.produceAuto`'s choice: plain RC when it is selected and its
        -- certificate is produced and replayed, else the immortal policy
        let front ← lift fun _ => RcReplay.produceFir cfg inp
        match Own.Plain.selectRcPolicyForSrc front.src front.fir with
        | .zeroRc =>
          let p ← lift fun _ => RcReplay.finishZeroRcCert cfg front
          pure (.zeroRc p.cert, some p.alloc, some "zero-rc")
        | .plainRc =>
          match ← lift fun _ => .ok (RcReplay.producePlain cfg inp front) with
          | .ok (p, _) => pure (.plainRc p.cert, some p.alloc, some "plain-rc")
          | .error reason =>
            let p ← lift fun _ => RcReplay.finishZeroRcCert cfg front
            pure (.zeroRc p.cert, some p.alloc,
              some s!"immortal (plain RC refused: {reason.stage.name}: {reason.code})")
  let (a, tRun) ← timed do
    match cliCert with
    | .zeroRc cert => lift fun _ => run cfg inp.program cert
    | .plainRc rcCert =>
      let rcArt ← lift fun _ => RcReplay.run cfg inp.program rcCert
      lift fun _ => rcArt.toRecheckArtifact rcCert
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
  if let some f := o.emitCert then write f (IO.FS.writeFile f (cliCert.toText ++ "\n"))
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
    let certBytes := cliCert.toText.utf8ByteSize
    let producer := if o.cert.isSome then "certificate read" else "produce"
    IO.println (envelopeLine inp.env)
    IO.println s!"time: read {tRead} ms, ingress {tIngress} ms, {producer} {tProduce} ms, run {tRun} ms"
    IO.println s!"certificate: {certBytes} bytes of JSON; {cert.table.resolve.length} table entries, \
      {cert.relevance.nodes.length} annotated terms, {cert.mid.steps.length} middle-end steps, \
      {cert.alloc.length} allocations, {cert.frames.length} frame layouts"
    for l in statsLines a outcomes do IO.println l

/-- The command line; the exit code. -/
def main (args : List String) : IO UInt32 := do
  if args == ["--help"] || args == ["-h"] || args.isEmpty then
    IO.println usage
    return (if args.isEmpty then 2 else 0)
  match parse args with
  | .error e =>
    IO.eprintln s!"ixcc: {e}\n{usage}"
    return 2
  | .ok o =>
    match ← (execute o).run with
    | .ok () => return 0
    | .error e =>
      IO.eprintln s!"ixcc: {e.render}"
      return 1

end IxCC.Cli
