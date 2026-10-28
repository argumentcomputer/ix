module
public import Ix.CompileDriver
public import Ix.Compile.SourceGraph.Accounting
public import Ix.Resource.Validate
public import Ix.Cert.Compile
public section

/-!
# The Lean pipeline's validated post-steps

`Ix.CompileM.compileLeanInput` compiles and serializes; it does not validate
resources, so the compiler does not import `Ix.Resource.Validate` (and with it
the validator's typing half, `Ix.Resource.typeCheck`). An input that carries semantic contracts, or
a compile against a resource profile, is emitted only after this post-step:
the requested closure must be complete (no recorded failure), and the
compiled environment must validate (`Ix.Resource.validate`, against the given
profile or the environment's standard one). Every result then checks original
input publication/failure accounting from the compiler's retained facts, and
the compile's report as the pure compiler checks its own (`reportPostStep`).
`ix compile-lean`, `ix validate-lean` and the Lean backend of artifact support
use the validated wrappers before emission. Bare compileLeanInput/compileLeanConsts
remain unvalidated.
This post-step does not authenticate caller-supplied Node maps.
-/

namespace Ix.CompileM

/-- Validate resources when required, then original-input accounting for
every result. Existing resource errors retain precedence. -/
def resourcePostStep (out : LeanPipelineOut)
    (resourceProfile : Option Ix.Resource.Profile := none) : Except String Unit := do
  if out.annotated || resourceProfile.isSome then
    if !out.cenv.ungrounded.isEmpty then
      throw "resource compilation requires the complete requested closure"
    let _ ← Ix.Resource.validate out.env
      (resourceProfile.getD (Ix.Resource.standardProfile out.env))
  let some nodes := out.sourceNodes?
    | throw "source accounting: original input facts are unavailable"
  (Ix.Compile.SourceGraph.Accounting.check nodes out.env.named out.cenv.ungrounded).mapError
    Ix.Compile.SourceGraph.Accounting.Issue.message

/-- An input constant's header: a theorem's or opaque's value replaced by
`Sort 0`, any other constant as it is. -/
def headerRaw : Ix.Compile.SourceInput.Raw → Ix.Compile.SourceInput.Raw
  | (n, .thmInfo v) => (n, .thmInfo { v with value := .sort .zero })
  | (n, .opaqueInfo v) => (n, .opaqueInfo { v with value := .sort .zero })
  | p => p

/-- **The input the report checks read**: every original input constant (the
retained source facts' names), canonical, as the pure compiler reads its input,
except that a theorem or opaque is read as its header (`headerRaw`): its value
is not canonicalized. A code constant is the materialized one, read through the
compile's lazy lookup; so is every constant when the output retains no original
input (`LeanPipelineOut.originalSource?`).

The headers leave the verdict unchanged: `Ix.Cert.checkReport` reads its input
environment only through its keys (`uncovered`, `nameHashCollision`,
`unresolvedPublished`, `strayFailure`, `unreadablePublished`), a constant's kind
and own name (`unseenInductive`, `misnamedInput`), an inductive's constructors
and a constructor's inductive (`strayConstructor`), and an inductive family's
shape: the names it lists, constructor indices, level-parameter names, `all` lists,
nested counts and recursor rules' constructor names (`unstoredFamilyName`,
`misplacedConstructor`, `strayLevelParams`,
`strayFamilyMember`, `recursorShapeError`), and never a type or a value. Reading the
values would hold every proof body of the input at once. The family check reads the
condensation the driver compiled (`LeanPipelineOut.blocks`), not one recomputed from
the headers. -/
def reportInput (out : LeanPipelineOut) : Except String Ix.Environment := do
  let some nodes := out.sourceNodes?
    | throw "report check: original input facts are unavailable"
  let read (n : Ix.Name) : Option Ix.ConstantInfo :=
    match out.originalSource?.bind (·.byName.get? n) with
    | some raw =>
      match raw.2 with
      | .thmInfo _ | .opaqueInfo _ => Ix.Compile.SourceInput.canonical? (headerRaw raw)
      | _ => out.cenv.env.get? n
    | none => out.cenv.env.get? n
  let consts ← nodes.foldM (init := ({} : Std.HashMap Ix.Name Ix.ConstantInfo)) fun m n _ =>
    match read n with
    | some ci => pure (m.insert n ci)
    | none => throw s!"report check: the input constant {n.pretty} could not be read"
  pure { consts }

/-- Up to three recorded failures, root causes first: a failure that only names a
missing constant is a dependent's, listed after the ones that name a cause. -/
def recordedFailures (failures : Std.HashMap Ix.Name String) : String :=
  let cascade (e : String) := e.startsWith "missingConstant" || e.startsWith "missing constant"
  let all := failures.toList
  let ordered := all.filter (!cascade ·.2) ++ all.filter (cascade ·.2)
  "; ".intercalate (ordered.take 3 |>.map fun (n, e) => s!"{n.pretty}: {(e.replace "\n" " ").take 200}")

/-- **The compile's report, checked as the pure compiler checks its own**
(`Ix.Cert.checkReport`, the checks behind `Ix.Cert.compileReport`): on the
whole input (`reportInput`), the driver's final environment and the artifact with
every recorded failure (the ground filter's refusals are among the driver's). A
refusal names the compile's recorded failures too, root causes first: a check can
fail because of a block that failed to compile.
Coverage, authentic storage, an acyclic reference order, distinct name hashes,
blocks that agree with their `Muts` entries, published input names at readable
records (`Ix.Cert.unreadablePublished`), and the resolution and naming invariants
hold of the emitted artifact, and the input's inductives have Lean's shapes over the
condensation the driver compiled (`out.blocks`), or the compile is refused. -/
def reportPostStep (out : LeanPipelineOut) : Except String Unit := do
  let env ← reportInput out
  (Ix.Cert.checkReport env out.cenv (out.env, { blocks := out.cenv.ungrounded })
    out.blocks).mapError fun e =>
    match recordedFailures out.cenv.ungrounded with
    | "" => e
    | causes => s!"{e}; the compile recorded {out.cenv.ungrounded.size} failure(s), first {causes}"

/-- `compileLeanInput` followed by the post-steps: an output that fails one is
an error, never a result to emit. -/
def compileLeanInputValidated (input : Ix.Compile.CompileInput)
    (rustRef : Option (Std.HashMap Name Address) := none)
    (numWorkers : Nat := 32) (opts : DriverOptions := {})
    (resourceProfile : Option Ix.Resource.Profile := none) :
    IO (Except String LeanPipelineOut) := do
  match ← compileLeanInput input rustRef numWorkers opts with
  | .error e => return .error e
  | .ok out =>
    let t0 ← IO.monoMsNow
    let checked ← IO.lazyPure fun _ =>
      resourcePostStep out resourceProfile >>= fun _ => reportPostStep out
    if opts.dbg then
      IO.println s!"  [compile-lean] post-steps (resources, accounting, report checks): \
{(← IO.monoMsNow) - t0}ms"
      if let some read := opts.memory then
        IO.println s!"  [compile-lean] rss after the post-steps: {← read}"
    return checked.map fun _ => out

/-- `compileLeanConsts` followed by the post-steps. -/
def compileLeanConstsValidated (consts : List (Lean.Name × Lean.ConstantInfo))
    (rustRef : Option (Std.HashMap Name Address) := none)
    (numWorkers : Nat := 32) (opts : DriverOptions := {})
    (resourceProfile : Option Ix.Resource.Profile := none) :
    IO (Except String LeanPipelineOut) := do
  match ← compileLeanConsts consts rustRef numWorkers opts with
  | .error e => return .error e
  | .ok out =>
    return (resourcePostStep out resourceProfile >>= fun _ => reportPostStep out).map fun _ => out

end Ix.CompileM

end
