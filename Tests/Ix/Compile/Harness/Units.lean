/-
  The compiler suites' unit harness (R11-08), units: a compile unit (a
  fixture's constants and their closure), the fixture families, and the
  compile of a unit by the Lean pipeline.

  Families: the aux-cert reproducers (`Tests.Ix.Compile.AuxCert.fixtures`,
  loaded from their files), image-gen's cases (`Tests/Ix/Compile/Image/C*`),
  the twin families (`Tests.Ix.Compile.Twins.allFamilies`, in the
  `TwinsFixtures` environment) and the aux corpus (`validateAuxClosure`).
  `twinsUnit`/`corpusUnit` are lane G's (`2010ad27`), shared by every runner
  that compiles those units.
-/
import Ix.Meta
import Ix.EnvScope
import Ix.CompileM
import Ix.CompileDriver
import Tests.Ix.Compile.Harness.Names
import Tests.Ix.Compile.AuxCert
import Tests.Ix.Compile.Twins
import Tests.Ix.Compile.ValidateAux

open Lean

namespace Tests.Ix.Compile.Harness

/-- A compile unit: its fixture constants (`seeds`) and their closure. -/
structure CUnit where
  name : String
  env : Environment
  seeds : Array Name
  closure : List (Name × ConstantInfo)

/-- The constants images are built from (`PProd`, `And`, `True`, and `Eq` for
the rule statements): a closure compile must contain them, as a whole-library
compile does. -/
def packing : List Name :=
  [``PProd, ``PProd.mk, ``And, ``And.intro, ``True, ``True.intro, ``Eq, ``Eq.refl]

/-- The closure of `seeds` with `packing`, every inductive's recursors
included (`Twins.closeWithRecursors`: the certified checker's reader needs
an inductive block's recursor). -/
def closureOf (env : Environment) (seeds : List Name) : List (Name × ConstantInfo) :=
  Tests.Ix.Compile.Twins.closeWithRecursors env
    (Ix.EnvScope.collectDeps env (seeds ++ packing.filter env.contains))

/-- `n` is a constant of `env`: of its elaborator view, or only of its kernel
view (the nested auxiliary recursors of a raw `addDecl`, `T.rec_1`). -/
def inputHas (env : Environment) (n : Name) : Bool :=
  env.contains n || (env.toKernelEnv.find? n).isSome

/-- A file's stem, the unit's name. -/
def stemOf (path : String) : String := (System.FilePath.mk path).fileStem.getD path

/-- The unit of a fixture file: the constants the file itself declares
(elaborated in this process, `getFileEnv`). -/
def unitOfFile (path : String) : IO CUnit := do
  let env ← getFileEnv path
  let seeds := (Tests.Ix.Compile.ClosureHarness.ownConstants env).toArray
  return { name := stemOf path, env, seeds, closure := closureOf env seeds.toList }

/-- The Lean pipeline's compile of a unit (`ClosureHarness.compileClosure`:
`compileInputFromEnv`, then `compileLeanInput`, under the compiler's
sharing limits). Per-block failures are in `cenv.ungrounded`. -/
def compileUnit (u : CUnit) (workers : Nat := 32) : IO _root_.Ix.CompileM.LeanPipelineOut := do
  try Tests.Ix.Compile.ClosureHarness.compileClosure u.env u.closure workers
  catch e => throw (IO.userError s!"{u.name}: {e}")

/-- Fixtures Lean itself rejects (the aux-cert record's `.xfail` rows that
Lean refuses). -/
def leanRejects : List String := ["PropEvap", "SortU", "SortURec", "SortUOpt"]

/-- The aux-cert reproducers' files. -/
def auxCertFiles : List String :=
  Tests.Ix.Compile.AuxCert.fixtures.map fun f =>
    f.src.getD s!"Tests/Ix/Compile/AuxCert/{f.stem}.lean"

/-- image-gen's cases. -/
def protoFiles : List String :=
  ["C1Perm", "C2Split", "C3PropSplit", "C4Evap", "C5Collapse", "C6NestedCollapse", "C7IndPred",
   "C8Collapse3", "C9Params"].map fun s => s!"Tests/Ix/Compile/Image/{s}.lean"

/-- The definitional passes' fixtures (CQ5.1, TT-07). -/
def passFiles : List String :=
  ["O1Perm", "O2Split", "O3Cases", "O4BRecOn", "O5PropSplit"].map fun s => s!"Tests/Ix/Compile/Pass/{s}.lean"

/-- Every fixture file of the families loaded from files. -/
def fixtureFiles : List String := auxCertFiles ++ protoFiles ++ passFiles

/-- The twins unit: every twin family's fixture constants and their closure,
in the `TwinsFixtures` environment. -/
def twinsUnit : IO CUnit := do
  let env ← Tests.Ix.Compile.Twins.fixturesEnv
  let (seeds, _) := Tests.Ix.Compile.Twins.familyClosure env Tests.Ix.Compile.Twins.allFamilies
  -- with the clique rows' prerequisites, so the well-founded clique twins are
  -- transported and their rows and `_ix.src` copies published (CQ5.2 (b)): the
  -- kernels then check every row (row admission in the wired compile)
  pure { name := "twins", env, seeds,
         closure := closureOf env (seeds.toList ++ Tests.Ix.Compile.Twins.rowPrereqNames env) }

/-- The aux corpus unit: the closure of `validateAuxClosure`. -/
def corpusUnit (env : Environment) : IO CUnit := do
  let closure := closureOf env ((validateAuxClosure env).map (·.1))
  pure { name := "corpus", env, seeds := (closure.map (·.1)).toArray, closure }

/-- A unit of named constants of `env` (comma-separated dotted names; a name
`env` lacks is left out), for diagnostics. -/
def namesUnit (env : Environment) (spec : String) : CUnit :=
  let seeds := (spec.splitOn ",").toArray.filterMap fun s =>
    let n := parseName s.trimAscii.toString
    if env.contains n then some n else none
  { name := "names", env, seeds, closure := closureOf env seeds.toList }

end Tests.Ix.Compile.Harness
