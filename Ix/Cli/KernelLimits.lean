module

public import Cli
public import IxCK.Host.Limits
public import Ix.Ixon
public import Ix.HostAdmission
public import Ix.RoleBinding.ArtifactTiered
public import Ix.Runtime.Thread

/-! # The kernel's limits at the root's command line

What `ix check-lean`, `ix verify-host` and `ix compile` share of the settings
mechanism (`IxCK.Host.Limits`): the flags read from a parsed command line, the
limit a host's error is a decline by, and the threads the kernel runs on, sized
from the limits before any task starts (`prepareThreads`) and checked against
the process's address-space limit. -/

@[expose] public section

namespace Ix.Cli.KernelLimits

open Ix.Kernel.Host
open Ix.Kernel.Admission (Resource Limits)

/-- The limit flags as the `Cli` declarations give them (every one a `String`,
so that a malformed value gets the mechanism's message). -/
def flagText (p : Cli.Parsed) (s : Setting) : Option String :=
  (p.flag? s.flag).map (·.as! String)

/-- The settings of a parsed command line over a host's defaults. -/
def resolveCli (defaults : Limits) (p : Cli.Parsed) : IO (Except String Resolved) :=
  resolveIO defaults (flagText p)

/-- The limit a loader's error is a decline by (`Ixon.depthLimitError`). -/
def loaderLimitOf (e : String) : Option Resource :=
  if Ixon.isDepthLimitError e then some .depth else none

def artifactLimitOf : Ix.RoleBinding.Artifact.Error → Option Resource
  | .bytes e => limitOfBytes e
  | .admission e => limitOfError e
  | _ => none

def artifactTierLimitOf : Ix.RoleBinding.Artifact.TierError → Option Resource
  | .preparation e => artifactLimitOf e
  | .admission e => limitOfTier e

def hostLimitOf : Ix.HostAdmission.Error → Option Resource
  | .preparation e => artifactLimitOf e
  | .tiered e => artifactTierLimitOf e
  | _ => none

/-- **Size the kernel's threads, before any task starts**: first the
address-space check (`Ix.Kernel.Host.spaceCheck`), before the resize, since the
check itself starts threads (`poolSize` runs `nproc`), which a resized stack
over the limit would abort: `some` is a refusal the host prints as a usage
error (exit 2), given only when the run certainly cannot fit; a run that may
not fit gets a warning line on standard error and proceeds. Then every thread
started afterwards (the run's own, the pool's workers) gets `Limits.stackFor`
bytes of stack. -/
def prepareThreads (r : Resolved) : IO (Option String) := do
  let stack := r.limits.stackFor
  let certain := s!"--workers or {Setting.workers.var}, or --max-depth or {Setting.maxDepth.var} \
(the stack is 16 KiB per level, at least 256 MiB)"
  let reduce := s!"--workers or {Setting.workers.var}, or --max-depth or {Setting.maxDepth.var}"
  match ← spaceCheck stack r.limits.workers (← poolSize) certain reduce with
  | .refuse why => return some why
  | .warn line => IO.eprintln line
  | .fits => pure ()
  Ix.Runtime.setLeanThreadStackSize (USize.ofNat stack)
  return none

/-- Run `act` on a dedicated thread (sized by `prepareThreads`). -/
def onKernelThread {α : Type} (act : IO α) : IO α := do
  IO.ofExcept (← IO.wait (← IO.asTask (prio := .dedicated) act))

/-- The usage text of the limit flags, for a command's help. -/
def flagsHelp : String :=
  "Kernel limits (each also IX_KERNEL_<LIMIT>, the flag winning; a positive whole number): \
--max-records, --max-blobs, --max-total-bytes, --max-record-bytes, --max-record-univ-nodes, \
--max-depth; a decline by one exits 6 and names it (docs/kernel.md, \"Limits\")"

end Ix.Cli.KernelLimits
