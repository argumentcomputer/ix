import Aiur.Generic.Derive.Lookup
import Aiur.Generic.Derive.Mirrors
import Aiur.Generic.Derive.Obs
import Lean

/-! # Deriving a program's semantic helpers at elaboration time

`deriveLookup`, `deriveMirrors`, `deriveObsShared` and `deriveObs` render the helpers of a
prepared program (`Derive.Lookup`, `Derive.Mirrors`, `Derive.Obs`) and elaborate them where
they are called: the declarations exist once the calling command has run, and Lean has
checked each of them. A program gets its helpers from commands of its own that call these
with its `Target` and its source, as it gets its definitions from `Modules.emitProgram`.

The declarations refer to the lemma libraries by name, so the module that elaborates them
imports the library they need: `Aiur.Generic.LookupFacts` for the lookup facts,
`Aiur.Generic.Refinement.Mirror` for the mirrors, `Aiur.Generic.Refinement.Obs` for the
path lemmas.

`set_option trace.Aiur.derive true` shows what each call derived, and the text it
elaborated. -/

namespace Aiur.Generic.Derive
open Lean Elab Command

initialize registerTraceClass `Aiur.derive

/-- The first line of a declaration, for a message about it. -/
private def firstLine (stx : Syntax) : String :=
  match stx.reprint with
  | some s => ((s.trimAscii.toString.splitOn "\n").headD "").take 120 |>.toString
  | none => ""

/-- The syntax with every position replaced by `ref`'s: the positions of derived text mean
nothing in the file that elaborates it. -/
private partial def relocate (ref : Syntax) : Syntax → Syntax
  | .node _ kind args => .node (.fromRef ref) kind (args.map (relocate ref))
  | .atom _ val => .atom (.fromRef ref) val
  | .ident _ raw val pre => .ident (.fromRef ref) raw val pre
  | .missing => .missing

/-- **Elaborate derived text**: parse it as a sequence of commands and elaborate each one.
Every message is reported at the calling command (`relocate`), with the declaration it is
about. -/
def elabText (what : String) (text : String) : CommandElabM Unit := do
  trace[Aiur.derive] "{what}:\n{text}"
  let ref ← getRef
  let ictx := Parser.mkInputContext text s!"<derived {what}>"
  let mut st : Parser.ModuleParserState := {}
  -- no message is left to a task, so that each can be told which declaration it is about;
  -- the text opens and closes its own scopes, which inherit this option, and ends in the
  -- scope it started in
  let async := Elab.async.get (← getOptions)
  modifyScope fun scope => { scope with opts := Elab.async.set scope.opts false }
  try repeat
    let scope := (← get).scopes.head!
    let pmctx : Parser.ParserModuleContext :=
      { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace,
        openDecls := scope.openDecls }
    let (cmd, st', msgs) := Parser.parseCommand ictx pmctx st {}
    st := st'
    if msgs.hasErrors then
      let errors ← msgs.toList.mapM (·.data.toString)
      throwError "{what}: the derived text does not parse: {errors}"
    if Parser.isTerminalCommand cmd then break
    let saved := (← get).messages
    modify fun s => { s with messages := {} }
    try
      elabCommand (relocate ref cmd)
    finally
      let named := (← get).messages.toList.foldl (init := saved) fun log m =>
        log.add { m with data := m!"{what}, at `{firstLine cmd}`:\n{m.data}" }
      modify fun s => { s with messages := named }
  finally
    modifyScope fun scope => { scope with opts := Elab.async.set scope.opts async }

variable {F : Type} [Field F] [DecidableEq F] [Target F]

/-- A part `(i, n)` is the `i`-th of `n`, from 1. -/
private def checkPart : Option (Nat × Nat) → CommandElabM Unit
  | some (i, n) => unless 1 ≤ i ∧ i ≤ n do throwError "there is no part {i} of {n}"
  | none => pure ()

/-- Declare the lookup facts of a program (`Derive.lookup`): all of them, or one part of
them, each part in a module of its own, the others importing the first. -/
def deriveLookup (prog : Program F) (part : Option (Nat × Nat) := none) : CommandElabM Unit := do
  checkPart part
  elabText "lookup facts" (lookup prog (prog.functions.map (·.name)) part)

/-- Declare the mirrors of the functions reachable from `roots`, and their lemmas
(`Derive.mirrors`). `priorRoots` are the roots whose mirrors were derived before. -/
def deriveMirrors (src : Aiur.Generic.Source F) (priorRoots roots : List String) :
    CommandElabM Unit := do
  let (text, report) := mirrors src priorRoots roots
  trace[Aiur.derive] "mirrors:\n{"\n".intercalate report}"
  elabText "mirrors" text

private def obsRun (src : Aiur.Generic.Source F) (select : String → Bool) :
    CommandElabM Obs.Run := do
  let table ← match Obs.nameTable F with
    | .ok table => pure table
    | .error e => throwError "path lemmas: {e}"
  let run := Obs.run table src select
  unless run.failures.isEmpty do
    throwError "path lemmas: a name could not be assigned, and nothing is declared:\n{
      "\n".intercalate run.failures.toList}"
  trace[Aiur.derive] "path lemmas:\n{"\n".intercalate run.report}"
  return run

/-- Declare what the path lemmas of a program share: its world `W` and the instance names
they normalize (`Obs.Run.sharedText`), before any `deriveObs`: all of it, or one part of it,
each part in a module of its own, the others importing the first. -/
def deriveObsShared (src : Aiur.Generic.Source F) (part : Option (Nat × Nat) := none) :
    CommandElabM Unit := do
  checkPart part
  elabText "path lemmas (shared names)" ((← obsRun src fun _ => true).sharedText F part)

/-- Declare the path inductive `«f».Path` and the inversion theorem `«f».obs` of each selected
function (`Derive.Obs`): of all of them, or of one part of them (`Obs.Run.part`), each part
in a module of its own. A function the deriver does not handle is left out: the trace says
which, and why. -/
def deriveObs (src : Aiur.Generic.Source F) (select : String → Bool)
    (part : Option (Nat × Nat) := none) : CommandElabM Unit := do
  checkPart part
  let run ← obsRun src select
  if run.derived.isEmpty then
    throwError "path lemmas: no function is selected and derived"
  let run := match part with
    | some (i, n) => run.part i n
    | none => run
  elabText "path lemmas" (run.text F)

end Aiur.Generic.Derive
