import Lean.Parser
import Lean.Util.Path

/-!
# Proof submissions: a term for a fixed target, nothing else

An agent supplies only the proof of a target the harness fixes. Before anything is elaborated, the
text must parse, in an environment of `Init` alone, as exactly one term (a `by` block is a term)
with nothing after it: no commands (`#eval`, `run_cmd`, `initialize`, `macro`, `syntax`,
attributes, further declarations), since those are not terms. The term itself must not use the
escape hatches that run code during elaboration or step outside the kernel: `run_tac`,
`native_decide` and `decide +native`, `set_option`, `open … in`, `dbg_trace`, `unsafe`, and
identifiers of `IO`, `ST`, `Lean`, `System` or `unsafe*` constants.

This is a first line only: elaboration of what passes still runs isolated
(`IxAIVerify.Sandbox`), and the compiled goal's type is checked against the target's address
afterwards (`IxAIVerify.Ixon.checkGoalType`).

The check must parse with the grammar of the toolchain that compiles the submission. This file
imports nothing outside Lean, so the harness runs it as a script under that toolchain
(`lean --run`, with `main` calling `checkerMain`), whatever toolchain the harness itself was built
with.
-/

namespace IxAIVerify

open Lean

/-- Atoms (keywords and symbols) a submission may not contain. -/
def deniedAtoms : List String :=
  ["native_decide", "run_tac", "set_option", "open", "dbg_trace", "dbgTrace", "unsafe", "#", "@[",
   "macro", "syntax", "elab", "initialize", "builtin_initialize", "attribute", "eval%", "by_elab",
   "run_cmd", "run_elab", "run_meta", "#eval", "#print", "#exit", "implemented_by", "extern"]

/-- Identifier components a submission may not mention. -/
def deniedNames : List String :=
  ["IO", "EIO", "BaseIO", "ST", "Lean", "System", "native", "ofReduceBool", "ofReduceNat",
   "implemented_by", "extern", "sorryAx", "dbgTrace", "panic", "panicCore"]

def deniedIdent (n : Name) : Bool :=
  n.components.any fun c =>
    let s := c.toString
    deniedNames.contains s || s.startsWith "unsafe" || s.startsWith "native"

/-- The first denied piece of a parsed submission, if any. -/
partial def deniedIn : Syntax → Option String
  | .atom _ v => if deniedAtoms.contains v || v.startsWith "#" then some s!"`{v}`" else none
  | .ident _ _ n _ => if deniedIdent n then some s!"identifier `{n}`" else none
  | .node _ kind args =>
    if (kind.components.any fun c => c.toString == "Command") then some s!"command syntax `{kind}`"
    else args.findSome? deniedIn
  | .missing => some "incomplete syntax"

/-- `syntax` declarations of `Init` register their parsers when imported, which runs their
initializers; enabling that is `unsafe`. -/
unsafe def submissionEnvImpl (sysroot : System.FilePath) : IO Environment := do
  initSearchPath sysroot
  enableInitializersExecution
  importModules #[{ module := `Init }] {} (loadExts := true)

/-- The environment submissions are parsed in: `Init` from the toolchain at `sysroot`. -/
@[implemented_by submissionEnvImpl]
opaque submissionEnv (sysroot : System.FilePath) : IO Environment

/-- Accept `proof` only if it is exactly one term without denied syntax. -/
def checkSubmission (env : Environment) (proof : String) : Except String Unit := do
  if proof.trimAscii.toString.isEmpty then throw "empty submission"
  let stx ← match Parser.runParserCategory env `term proof "<submission>" with
    | .ok s => pure s
    | .error e => throw s!"not exactly one term (commands, declarations and trailing text are refused): {e}"
  if let some why := deniedIn stx then throw s!"denied in a submission: {why}"

/-- `checker PROOF_FILE`: parse the submission in the `Init` of the running toolchain. Prints
`accepted`, or `refused: REASON` and exits 1. -/
def checkerMain (args : List String) : IO UInt32 := do
  let [file] := args | IO.eprintln "usage: checker PROOF_FILE"; return 2
  let env ← submissionEnv (← findSysroot)
  match checkSubmission env (← IO.FS.readFile file) with
  | .ok () => IO.println s!"accepted (Lean {Lean.versionString})"; return 0
  | .error why => IO.println s!"refused: {why}"; return 1

end IxAIVerify
