import LSpec
import Ix.EnvScope
import Tests.Ix.Compile.AuxGenClosure
import Tests.Ix.Compile.Twins.Cliques
import Tests.Ix.Compile.Pass3

open LSpec Lean

namespace Tests.Ix.Compile.SelectedClosure

def matcher (n : Nat) : Nat := n
theorem matcher._arg_pusher : matcher 0 = 0 := rfl
theorem carriedProof : matcher 0 = 0 := matcher._arg_pusher

private def names (cs : List (Name × ConstantInfo)) : Std.HashSet Name :=
  cs.foldl (fun acc c => acc.insert c.1) {}

private def sameNames (xs ys : List (Name × ConstantInfo)) : Bool :=
  let ys' := names ys
  xs.length == ys.length && xs.all (ys'.contains ·.1)

def suite : List TestSeq := [
  .individualIO "selected sizeOf support closes singleton roots and subsets" none (do
    let env ← getFileEnv "Tests/Ix/Compile/Pass/O2Split.lean"
    let roots := [`PassO2.SA._sizeOf_1, `PassO2.SA._sizeOf_2]
    let required := [`PassO2.SA._sizeOf_inst, `PassO2.SB._sizeOf_inst, `SizeOf.sizeOf]
    let mut errors : Array String := #[]
    for n in roots ++ required do
      unless env.contains n do errors := errors.push s!"fixture missing {n}"
    for seeds in roots.map (fun n => [n]) ++ [roots, roots.reverse] do
      let closed := Ix.EnvScope.collectSelectedDeps env seeds
      let ns := names closed
      -- the selected scope also seeds the compiler's introduced references
      let support := Ix.EnvScope.introducedSupport env
      let ordinary := Lean.collectDependenciesMany (seeds ++ support).toArray env.constants
        (withCompilerSupport := true) (withCheckerSupport := true)
      unless sameNames closed ordinary do
        errors := errors.push s!"{seeds}: ordinary and scoped selected collectors disagree"
      unless sameNames ordinary (Lean.collectDependenciesMany (ordinary.map (·.1)).toArray
          env.constants (withCompilerSupport := true) (withCheckerSupport := true)) do
        errors := errors.push s!"{seeds}: ordinary selected closure is not a fixed point"
      if let [seed] := seeds then
        unless sameNames closed (Lean.collectDependenciesMany (seed :: support).toArray env.constants
            (withCompilerSupport := true) (withCheckerSupport := true)) do
          errors := errors.push s!"{seed}: ordinary singleton collector disagrees"
      for n in required do
        unless ns.contains n do errors := errors.push s!"{seeds}: missing support {n}"
      unless sameNames closed (Ix.EnvScope.collectSelectedDeps env (closed.map (·.1))) do
        errors := errors.push s!"{seeds}: closure is not a fixed point"
    unless sameNames (Ix.EnvScope.collectSelectedDeps env roots)
        (Ix.EnvScope.collectSelectedDeps env roots.reverse) do
      errors := errors.push "subset order changed closure"
    -- Raw dependencies intentionally do not supply rewrite-only instances.
    let raw := names (Ix.EnvScope.collectDeps env [`PassO2.SA._sizeOf_1])
    if required.all raw.contains then errors := errors.push "raw negative control unexpectedly complete"
    let ordinaryRaw := names (Lean.collectDependencies `PassO2.SA._sizeOf_1 env.constants)
    if required.all ordinaryRaw.contains then errors := errors.push "ordinary raw negative control unexpectedly complete"
    for e in errors do IO.println s!"[selected-closure] {e}"
    return (errors.isEmpty, if errors.isEmpty then 1 else 0, 1,
      if errors.isEmpty then none else some s!"{errors.size} closure failures"))
    (.individualIO "selected clique members retain all source-owned siblings" none (do
    let env ← get_env!
    let mut checked := 0
    let mut errors : Array String := #[]
    let bare := names (Ix.EnvScope.collectSelectedDeps env [``matcher])
    let carried := names (Ix.EnvScope.collectSelectedDeps env [``carriedProof])
    unless carried.contains ``matcher._arg_pusher do
      errors := errors.push "carried proof lost its explicit pusher dependency"
    -- M1-d (design document §6.3, owner rule of 2026-10-05): an on-demand
    -- auxiliary belongs to its declaration's logical unit and a closure
    -- producer carries it with the block. Before M1-d this asserted the
    -- opposite (an "unrelated ambient pusher" must not be pulled).
    unless bare.contains ``matcher._arg_pusher do
      errors := errors.push "bare matcher lost the pusher of its logical unit"
    -- negative control: a constant outside the unit is not pulled
    if bare.contains ``carriedProof then
      errors := errors.push "bare matcher pulled its caller carriedProof"
    for (root, sibling) in Tests.Ix.Compile.AuxGenClosure.mutualSeeds do
      let closed := Ix.EnvScope.collectSelectedDeps env [root]
      checked := checked + 1
      unless (names closed).contains sibling do errors := errors.push s!"{root}: missing {sibling}"
    -- Exercise every partial_fixpoint, structural, and WF family in the
    -- existing clique fixture as individual roots, not their union.
    let fixturePrefix := `Tests.Ix.Compile.Twins.Cliques
    for (root, ci) in env.constants.toList do
      unless fixturePrefix.isPrefixOf root do continue
      let all := match ci with
        | .defnInfo d => d.all
        | .thmInfo d => d.all
        | .opaqueInfo d => d.all
        | _ => []
      if all.length < 2 then continue
      let ns := names (Ix.EnvScope.collectSelectedDeps env [root])
      checked := checked + 1
      for sibling in all do
        unless ns.contains sibling do errors := errors.push s!"{root}: missing {sibling}"
    if checked <= 4 then errors := errors.push "no encoded clique members were exercised"
    for e in errors do IO.println s!"[selected-closure] {e}"
    IO.println s!"[selected-closure] checked {checked} individual clique roots"
    return (errors.isEmpty, if errors.isEmpty then checked else 0, checked,
      if errors.isEmpty then none else some s!"{errors.size} clique closure failures")) .done)
]

/-- End-to-end selected versus whole-environment compilation, retaining complete Named
metadata, refusal coverage, decompile fidelity and strict kernel evidence. -/
def run : IO UInt32 := do
  let env ← getFileEnv "Tests/Ix/Compile/Pass/O2Split.lean"
  let roots := [`PassO2.SA._sizeOf_1, `PassO2.SA._sizeOf_2]
  let dir : System.FilePath := "out/codex-a7/selected-closure/e2e"
  IO.FS.createDirAll dir
  let mut errors : Array String := #[]
  for mode in [false, true] do
    let wholeUnit : Pass3.CUnit :=
      { name := "O2Split-whole", env := env,
        seeds := Pass3.ownConstants env,
        closure := env.constants.toList }
    IO.println s!"[selected-closure-e2e] whole environment: {wholeUnit.closure.length} declarations, mode={mode}"
    let whole ← Pass3.compileUnit wholeUnit mode
    unless whole.cenv.ungrounded.isEmpty do
      errors := errors.push s!"whole mode={mode}: {whole.cenv.ungrounded.size} refusals"
    let mut subsetBytes : Option ByteArray := none
    for (seeds, i) in (roots.map (fun n => [n]) ++ [roots, roots.reverse]).zipIdx do
      let unit : Pass3.CUnit :=
        { name := s!"O2Split-selected-{i}", env := env,
          seeds := seeds.toArray, closure := Ix.EnvScope.collectSelectedDeps env seeds }
      let out ← Pass3.compileUnit unit mode
      let legDir := dir / s!"mode-{mode}-{i}"
      IO.FS.createDirAll legDir
      let path := legDir / "output.ixe"
      IO.FS.writeBinFile path out.bytes
      unless out.cenv.ungrounded.isEmpty do
        errors := errors.push s!"{unit.name} mode={mode}: {out.cenv.ungrounded.size} refusals"
      for (name, named) in out.env.named do
        match whole.env.named[name]? with
        | none => errors := errors.push s!"{unit.name}: full output lacks {name.pretty}"
        | some reference => unless named == reference do
          errors := errors.push s!"{unit.name} mode={mode}: address/metadata differs for {name.pretty}"
      if i == 2 then subsetBytes := some out.bytes
      if i == 3 && subsetBytes != some out.bytes then
        errors := errors.push s!"mode={mode}: reversed subset changed exact bytes"
      let (decompileErrors, summary) ← Pass3.decompileCheck unit out
      errors := errors ++ decompileErrors
      let failed ← Pass3.kernelFailures legDir path (seeds.toArray.map toString) (anon := true)
      for (kernel, name, why) in failed do
        errors := errors.push s!"{kernel}: {name}: {why}"
      -- Certification means accept, not a documented decline.
      let report ← IO.ofExcept (KernelReport.parse (← IO.FS.readFile (legDir / "cert.jsonl")))
      for seed in seeds do
        let some named := out.env.named[Pass3.ixN seed]?
          | throw (IO.userError s!"missing selected root {seed}")
        let record := AuxCert.recordOf out.env named.addr
        unless (report[toString record]?).any (·.outcome == "accept") do
          errors := errors.push s!"{seed} mode={mode}: selected owning record not accepted"
      IO.println s!"[selected-closure-e2e] mode={mode} seeds={seeds}: {out.bytes.size}B; {summary}"
  for e in errors do IO.println s!"[selected-closure-e2e] FAIL {e}"
  IO.println s!"[selected-closure-e2e] {errors.size} failure(s)"
  return if errors.isEmpty then 0 else 1

end Tests.Ix.Compile.SelectedClosure
