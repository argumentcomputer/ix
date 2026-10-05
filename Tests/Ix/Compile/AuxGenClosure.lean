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
    canonical `.rec`/`.below` and rejected, `AppTypeMismatch`;
  - `PV.brecOn`, `PV.brecOn_1` (a Prop inductive nested through a Prop
    inductive): `.brecOn` generation indexed the classes' `.below` names
    by motive number and panicked (index out of bounds), aborting the
    process; `PV.below_1`: no `.below_N` was generated for a Prop-level
    block, `aux_gen alias target missing`.

  A second case, `mutual` definitions on closure-only environments: a
  structural, well-founded or `partial` `mutual` member's value goes
  through auxiliaries and never mentions its siblings, but its compiled
  metadata carries Lean's `all` (the siblings' names), which meta kernel
  ingress resolves through the env's Named entries. Before the fix,
  `collectDeps` did not follow a definition's `all`, so the closure of
  `oddN` (or of a theorem about it) lacked `evenN`, and `ix check-rs`
  rejected the written `.ixe`: `resolve_all: Named entry for 'evenN'
  missing`. That case compiles the closure to a file, as `ix compile
  --consts` does, and checks the file with the meta Rust kernel, as
  `ix check-rs` does.

  A third case, `ix pack` on regenerated auxiliaries: a regenerated
  `.rec`/`.below`/`.brecOn` records in `Named.original` the address of
  Lean's source form, which the compiler never stores. Before the fix,
  `Env::prune_to_closure` followed that address as a constant edge, so
  `ix pack` failed on any constant whose closure carried such an entry:
  `prune_to_closure: <addr> reachable from main but not in consts/blobs
  and not assumed`. That case compiles a closure to a file, checks that
  it holds an unstored original, packs the seed with `rsPackEnv` (the
  `ix pack` path) and checks the bundle with the meta Rust kernel.

  Run with: `lake test -- --ignored aux-gen-closure`.
-/
import Ix.Meta
import Ix.EnvScope
import Ix.KernelCheck
import Ix.CompileM
import Ix.Ixon
import LSpec

open LSpec
open Ix.KernelCheck (CheckError rsCheckConstsFFI rsCheckIxonFFI)

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

/-- Prop nested through a Prop-valued family: one class, one auxiliary
    (`PV.below_1` is an inductive, `PV.brecOn_1` a theorem). -/
inductive Pw (R : Nat → Nat → Prop) : List Nat → List Nat → Prop where
  | nil : Pw R [] []
  | cons : R a b → Pw R as bs → Pw R (a :: as) (b :: bs)

inductive PV : Nat → Nat → Prop where
  | base : PV 0 0
  | node : Pw PV xs ys → PV xs.length ys.length

/-- Seeds whose closure lacks the canonical first class's `.brecOn`/`.below`,
    and the auxiliaries of a nested Prop block. -/
def seeds : List Lean.Name := [
  ``T.brecOn_1, ``T.below_1, ``A.brecOn_1, ``A.below_1, ``A.brecOn,
  ``PV.brecOn, ``PV.brecOn_1, ``PV.below_1
]

-- `mutual` definitions whose values do not mention their siblings.
mutual
/-- Structural: the value goes through `evenN._f`/`oddN._f`. -/
def evenN : Nat → Bool
  | 0 => true
  | n + 1 => oddN n
def oddN : Nat → Bool
  | 0 => false
  | n + 1 => evenN n
end

mutual
/-- Well-founded: the value goes through `wfEven._mutual`. -/
def wfEven : Nat → Bool
  | 0 => true
  | n + 1 => wfOdd n
termination_by n => n
def wfOdd : Nat → Bool
  | 0 => false
  | n + 1 => wfEven n
termination_by n => n
end

mutual
/-- `partial`: an opaque with a default value. -/
partial def pEven : Nat → Bool
  | 0 => true
  | n + 1 => pOdd n
partial def pOdd : Nat → Bool
  | 0 => false
  | n + 1 => pEven n
end

theorem oddN_one : oddN 1 = true := rfl

/-- Seeds whose closure must hold the named sibling. -/
def mutualSeeds : List (Lean.Name × Lean.Name) := [
  (``oddN, ``evenN), (``wfOdd, ``wfEven), (``pOdd, ``pEven), (``oddN_one, ``evenN)
]

/-- Regenerated auxiliaries whose `Named.original` is not stored. -/
def packSeeds : List Lean.Name := [``A.rec, ``A.below, ``A.brecOn, ``B.rec]

/-- Named entries of the file at `path` whose `original` differs from
    their address and is absent from its constants and blobs. -/
def unstoredOriginals (path : String) : IO Nat := do
  let env ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))
  return env.named.fold (init := 0) fun n _ e =>
    match e.original with
    | some (a, _) =>
      if a != e.addr && !env.consts.contains a && !env.blobs.contains a then n + 1 else n
    | none => n

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
    (.individualIO "mutual definitions on closure-only environments" none (do
    let env ← get_env!
    let mut failed := 0
    let dir ← IO.FS.createTempDir
    for (seed, sibling) in mutualSeeds do
      let mut errs : Array String := #[]
      let closure := Ix.EnvScope.collectDeps env [seed]
      if !closure.any (·.1 == sibling) then
        errs := errs.push s!"closure lacks {sibling}"
      -- The `ix compile --consts` path, written to a file …
      let path := (dir / s!"{seed}.ixe").toString
      let prepared ← IO.ofExcept <|
        Ix.Compile.prepareRegisteredConstants env closure
      let status ← Ix.CompileM.rsCompileEnvBytesFFI prepared path false
      if let some (n, r) := status.ungrounded[0]? then
        errs := errs.push s!"compile ({status.ungrounded.size} ungrounded): {n}: {r}"
      else
        -- … and the `ix check-rs` path (meta mode) on that file.
        let results ← rsCheckIxonFFI path #[seed] #[true] true ""
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
    let n := mutualSeeds.length
    return (failed == 0, n - failed, n,
      if failed == 0 then none else some s!"{failed} closure(s) failed"))
    (.individualIO "ix pack on regenerated auxiliaries" none (do
    let env ← get_env!
    let mut failed := 0
    let dir ← IO.FS.createTempDir
    for seed in packSeeds do
      let mut errs : Array String := #[]
      let closure := Ix.EnvScope.collectDeps env [seed]
      let path := (dir / s!"{seed}.ixe").toString
      let prepared ← IO.ofExcept <|
        Ix.Compile.prepareRegisteredConstants env closure
      let status ← Ix.CompileM.rsCompileEnvBytesFFI prepared path false
      if let some (n, r) := status.ungrounded[0]? then
        errs := errs.push s!"compile ({status.ungrounded.size} ungrounded): {n}: {r}"
      else
        -- The fixture must exercise an unstored original.
        if (← unstoredOriginals path) == 0 then
          errs := errs.push "fixture: no unstored Named.original in the closure"
        -- The `ix pack` path, then `ix check-rs` (meta) on the bundle.
        let bundle := (dir / s!"pack-{seed}.ixe").toString
        match ← (Ixon.rsPackEnv path (toString seed) #[] bundle false false).toBaseIO with
        | .error e => errs := errs.push s!"pack: {e}"
        | .ok () =>
          let results ← rsCheckIxonFFI bundle #[seed] #[true] true ""
          match results[0]? with
          | some none => pure ()
          | some (some (CheckError.kernelException m)) => errs := errs.push s!"kernel: {m}"
          | some (some (CheckError.compileError m)) => errs := errs.push s!"check-compile: {m}"
          | none => errs := errs.push "no kernel result"
      if errs.isEmpty then
        IO.println s!"[aux-gen-closure] pack {seed}: ok"
      else
        failed := failed + 1
        for e in errs do IO.println s!"[aux-gen-closure] FAIL pack {seed}: {e}"
    let n := packSeeds.length
    return (failed == 0, n - failed, n,
      if failed == 0 then none else some s!"{failed} pack(s) failed"))
    .done))
]

end Tests.Ix.Compile.AuxGenClosure
