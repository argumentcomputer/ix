/-
  The compiler suites' unit harness (R11-08), names: the conversions between
  Lean and Ix names, dotted names with numeric components, and what an
  output's named entries are.

  The harness modules (`Tests/Ix/Compile/Harness/{Names,Units,Check,Kernels}`)
  hold what the donor's `Tests/Ix/Compile/Pass3.lean` (a9cf3607) gave the 22
  modules that imported the `pass3` suite to reach it. They build on the
  closure suites' harness (`Tests.Ix.Compile.ClosureHarness`: the compile of
  a closure, decompile fidelity, the certified checker) instead of copying
  it; `ixN` and `toLeanName` are its own, exported here.
-/
import Ix.Ixon
import Ix.Compile.Pass.Names
import Tests.Ix.Compile.ClosureHarness

open Lean

namespace Tests.Ix.Compile.Harness

export Tests.Ix.Compile.ClosureHarness (ixN toLeanName)

/-- A dotted name with numeric components (`_private.M.0.f`). -/
def parseName (s : String) : Name :=
  (s.splitOn ".").foldl (init := .anonymous) fun n c =>
    match c.toNat? with
    | some k => .num n k
    | none => .str n c

/-- Substring test (independent of the `String` pattern API). -/
def hasSub (s pat : String) : Bool := (s.splitOn pat).length > 1

/-- A block's synthetic `Muts` entry (its container label): its metadata is
the block's classes, which no input constant's is. -/
def isMutsEntry (nd : Ixon.Named) : Bool :=
  match nd.constMeta.info with
  | .muts .. => true
  | _ => false

/-- The Lean name an `_ix` display name stands for, as text (`x._ix.S ↦
x.S`), to match the names in failure messages. -/
def leanOf (s : String) : String :=
  String.intercalate "." ((s.splitOn ".").filter (· != _root_.Ix.Compile.Pass.ixComponent))

end Tests.Ix.Compile.Harness
