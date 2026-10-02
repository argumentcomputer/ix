/-
  aux-gen-closure: auxiliary regeneration on closure-only environments.

  `ix compile --consts` (and any claim built from a dependency closure)
  hands the compiler only the seeds' transitive dependencies. Such a closure
  can hold a nested auxiliary `<all0>.brecOn_N`/`.below_N`, or one class's
  `.brecOn`, without the `.brecOn`/`.below` of the block's canonical first
  class. Each case below compiles exactly that closure and type-checks the
  seed with the Rust kernel (`rsCheckConstsFFI`: Lean closure → Ixon
  compile → kernel), and expects it to pass. Before the fix:

  - `T.brecOn_1`, `T.below_1`, `A.brecOn_1`, `A.below_1`: `ix compile`
    (`rsCompileEnvBytesFFI`, fail-closed) failed the block,
    `aux_gen alias target missing: … maps to canonical aux #0 but no
    generated brecOn (below) patch exists`;
  - `A.brecOn` (`B` sorts first): compiled in its source form against the
    canonical `.rec`/`.below` and rejected, `AppTypeMismatch`.

  Run with: `lake test -- --ignored aux-gen-closure`.
-/
import Ix.Meta
import Ix.EnvScope
import Ix.KernelCheck
import Ix.CompileM
import LSpec

open LSpec
open Ix.KernelCheck (CheckError rsCheckConstsFFI)

namespace Tests.Ix.Compile.AuxGenClosure

/-- Nested through `List`: one class, one auxiliary (`T.rec_1` and so on). -/
inductive T where
  | mk : List T → T

-- Mutual and nested; `B` sorts before `A` canonically.
mutual
inductive A where
  | mk : List B → A
inductive B where
  | mk : A → B
end

/-- Seeds whose closure lacks the canonical first class's `.brecOn`/`.below`. -/
def seeds : List Lean.Name := [
  ``T.brecOn_1, ``T.below_1, ``A.brecOn_1, ``A.below_1, ``A.brecOn
]

def suite : List TestSeq := [
  .individualIO "aux_gen on closure-only environments" none (do
    let env ← get_env!
    let mut failed := 0
    let dir ← IO.FS.createTempDir
    for seed in seeds do
      let mut errs : Array String := #[]
      let closure := Ix.EnvScope.collectDeps env [seed]
      -- The `ix compile --consts` path: fail-closed, no source-form fallback.
      let prepared ← IO.ofExcept <|
        Ix.Compile.prepareRegisteredConstants env closure
      let status ← Ix.CompileM.rsCompileEnvBytesFFI prepared
        (dir / s!"{seed}.ixe").toString false
      if let some (n, r) := status.ungrounded[0]? then
        errs := errs.push s!"compile ({status.ungrounded.size} ungrounded): {n}: {r}"
      let results ← rsCheckConstsFFI closure #[seed] #[true] false
      match results[0]? with
      | some none => pure ()
      | some (some (CheckError.kernelException m)) => errs := errs.push s!"kernel: {m}"
      | some (some (CheckError.compileError m)) => errs := errs.push s!"check-compile: {m}"
      | none => errs := errs.push "no kernel result"
      if errs.isEmpty then
        IO.println s!"[aux-gen-closure] {seed}: ok"
      else
        failed := failed + 1
        for e in errs do IO.println s!"[aux-gen-closure] FAIL {seed}: {e}"
    let n := seeds.length
    return (failed == 0, n - failed, n,
      if failed == 0 then none else some s!"{failed} closure(s) failed"))
    .done
]

end Tests.Ix.Compile.AuxGenClosure
