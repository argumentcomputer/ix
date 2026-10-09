import Compilatrix.Recheck
import Compilatrix.Anf.Print
import Compilatrix.Fir.Print
import Compilatrix.Cfg.Print
import Compilatrix.Lir.Print
import Compilatrix.Xv.Print

/-! # The `compilatrix` command line (M1.I1)

```text
compilatrix compile CLOSURE.ixe --equations EQ.json [--root NAME]... -o OUT.o
    [--cert FILE] [--emit-cert FILE] [--signatures FILE] [--dump-ir LEVEL]...
    [--stats] [--no-typecheck]
compilatrix check-cert CLOSURE.ixe --equations EQ.json [--root NAME]... --cert FILE
    [-o OUT.o] [--signatures FILE] [--stats] [--no-typecheck]
```

`compile` runs ingress, `produce` and `Recheck.run` and writes the ELF
object: `cx_<root>` for each root (the sidecar's names; every sidecar root
when no `--root` is given) and `cx_init`, for `fixtures/x86/runtime_driver.c`
(`cc -no-pie -DENTRY=cx_<root> runtime_driver.c OUT.o`). With `--cert`, the
given certificate replaces `produce`'s (so the recheck needs nothing from the
producer); `--emit-cert` writes the certificate used. `check-cert` runs
`Recheck.run` on a certificate and reports acceptance or the rejection.

`--signatures FILE` writes, per root, its symbol, parameter count and the
driver's `--type`/`--sig` arguments (JSON; `null` when bounded ground
first-order signature discovery does not support the result type).
`--dump-ir LEVEL` prints a level (`lam`, `anf`, `fir`,
`cfg`, `lir`, `xv`, `xl`, or `all`) to standard output; `--stats` prints
timings, sizes and the allocation outcomes. `--no-typecheck` skips erased
typing at ingress (the fixtures' typing is gated by `tests-ixon-v3`).

A decline or rejection prints `compilatrix: stage: code: message` on
standard error and exits 1; a usage error exits 2. -/

namespace Compilatrix.Cli

open System Compilatrix.Recheck

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
  deriving Inhabited

def usage : String :=
  "\n".intercalate [
    "usage:",
    "  compilatrix compile CLOSURE.ixe --equations EQ.json [--root NAME]... -o OUT.o",
    "      [--cert FILE] [--emit-cert FILE] [--signatures FILE] [--dump-ir LEVEL]... [--stats] [--no-typecheck]",
    "  compilatrix check-cert CLOSURE.ixe --equations EQ.json [--root NAME]... --cert FILE",
    "      [-o OUT.o] [--signatures FILE] [--stats] [--no-typecheck]",
    "dump levels: lam anf fir cfg lir xv xl all"]

def dumpLevels : List String := ["lam", "anf", "fir", "cfg", "lir", "xv", "xl"]

def parseRest (o : Options) : List String → Except String Options
  | [] => pure o
  | "--equations" :: f :: rest => parseRest { o with equations := some f } rest
  | "--root" :: n :: rest => parseRest { o with roots := o.roots ++ [n] } rest
  | "-o" :: f :: rest => parseRest { o with out := some f } rest
  | "--cert" :: f :: rest => parseRest { o with cert := some f } rest
  | "--emit-cert" :: f :: rest => parseRest { o with emitCert := some f } rest
  | "--signatures" :: f :: rest => parseRest { o with signatures := some f } rest
  | "--dump-ir" :: l :: rest =>
    if l == "all" then parseRest { o with dumps := o.dumps ++ dumpLevels } rest
    else if dumpLevels.contains l then parseRest { o with dumps := o.dumps ++ [l] } rest
    else throw s!"unknown IR level {l}"
  | "--stats" :: rest => parseRest { o with stats := true } rest
  | "--no-typecheck" :: rest => parseRest { o with typecheck := false } rest
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
      if cmd == "compile" && o.out.isNone then throw "no -o output given"
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
  let json ← match Lean.Json.parse text with
    | .ok j => pure j
    | .error e => throw { stage := .ingress, code := "hints", message := s!"{eqs}: {e}" }
  pure (bytes, json)

def readCert (f : FilePath) : ExceptT Err IO Cert := do
  let text ← (IO.FS.readFile f).toBaseIO >>= fun
    | .ok t => pure t
    | .error e => throw (cliErr "cli.read" s!"{f}: {e}")
  ExceptT.mk (pure (Cert.ofText text))

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
  let ((cert, outcomes), tProduce) ← timed do
    match o.cert with
    | some f => pure (← readCert f, none)
    | none =>
      let p ← lift fun _ => produceWith cfg inp
      pure (p.cert, some p.alloc)
  let (a, tRun) ← timed (lift fun _ => run cfg inp.program cert)
  if let some f := o.out then write f (IO.FS.writeBinFile f a.object)
  if let some f := o.emitCert then write f (IO.FS.writeFile f (cert.toText ++ "\n"))
  if let some f := o.signatures then write f (IO.FS.writeFile f ((signaturesJson a).pretty ++ "\n"))
  for l in o.dumps do
    IO.println s!"== {l} =="
    IO.println (dump a l)
  if o.command == "check-cert" then
    IO.println s!"certificate accepted: object {a.object.size} bytes, text {a.backend.encoded.text.size} bytes, \
      exports {a.roots.map (·.symbol)}"
  if o.stats then
    let certBytes := cert.toText.utf8ByteSize
    let producer := if o.cert.isSome then "certificate read" else "produce"
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
    IO.eprintln s!"compilatrix: {e}\n{usage}"
    return 2
  | .ok o =>
    match ← (execute o).run with
    | .ok () => return 0
    | .error e =>
      IO.eprintln s!"compilatrix: {e.render}"
      return 1

end Compilatrix.Cli
