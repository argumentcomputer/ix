module
public import Ix.CompileDriver
public import Ix.Compile.SourceGraph.Accounting
public import Ix.Resource.Validate
public section

/-!
# The Lean pipeline's validated post-step

`Ix.CompileM.compileLeanInput` compiles and serializes; it does not validate
resources, so the compiler does not import `Ix.Resource.Validate` (and with it
the validator's typing half, `Ix.Resource.typeCheck`). An input that carries semantic contracts, or
a compile against a resource profile, is emitted only after this post-step:
the requested closure must be complete (no recorded failure), and the
compiled environment must validate (`Ix.Resource.validate`, against the given
profile or the environment's standard one). Every result then checks original
input publication/failure accounting from the compiler's retained facts.
`ix compile-lean` and `ix validate-lean` use the validated wrappers before
emission. Bare compileLeanInput/compileLeanConsts remain unvalidated.
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

/-- `compileLeanInput` followed by the resource post-step: an output that
    fails the post-step is an error, never a result to emit. -/
def compileLeanInputValidated (input : Ix.Compile.CompileInput)
    (rustRef : Option (Std.HashMap Name Address) := none)
    (numWorkers : Nat := 32) (opts : DriverOptions := {})
    (resourceProfile : Option Ix.Resource.Profile := none) :
    IO (Except String LeanPipelineOut) := do
  match ← compileLeanInput input rustRef numWorkers opts with
  | .error e => return .error e
  | .ok out => return (resourcePostStep out resourceProfile).map fun _ => out

/-- `compileLeanConsts` followed by the resource post-step. -/
def compileLeanConstsValidated (consts : List (Lean.Name × Lean.ConstantInfo))
    (rustRef : Option (Std.HashMap Name Address) := none)
    (numWorkers : Nat := 32) (opts : DriverOptions := {})
    (resourceProfile : Option Ix.Resource.Profile := none) :
    IO (Except String LeanPipelineOut) := do
  match ← compileLeanConsts consts rustRef numWorkers opts with
  | .error e => return .error e
  | .ok out => return (resourcePostStep out resourceProfile).map fun _ => out

end Ix.CompileM

end
