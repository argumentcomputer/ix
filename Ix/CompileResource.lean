module
public import Ix.CompileDriver
public import Ix.Resource.Validate
public section

/-!
# The Lean pipeline's resource post-step

`Ix.CompileM.compileLeanInput` compiles and serializes; it does not validate
resources, so the compiler does not import `Ix.Resource.Validate` (and with it
the `Ix.Tc` environment checker). An input that carries semantic contracts, or
a compile against a resource profile, is emitted only after this post-step:
the requested closure must be complete (no recorded failure), and the
compiled environment must validate (`Ix.Resource.validate`, against the given
profile or the environment's standard one). `ix compile-lean` and
`ix validate-lean` run it before writing.
-/

namespace Ix.CompileM

/-- The resource post-step of a Lean pipeline result: required for an input
    with semantic contracts (`LeanPipelineOut.annotated`) or a resource
    profile, and a no-op otherwise. -/
def resourcePostStep (out : LeanPipelineOut)
    (resourceProfile : Option Ix.Resource.Profile := none) : Except String Unit := do
  if out.annotated || resourceProfile.isSome then
    if !out.cenv.ungrounded.isEmpty then
      throw "resource compilation requires the complete requested closure"
    let _ ← Ix.Resource.validate out.env
      (resourceProfile.getD (Ix.Resource.standardProfile out.env))

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
