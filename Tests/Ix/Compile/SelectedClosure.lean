import LSpec
import Ix.EnvScope
import Tests.Ix.Compile.AuxGenClosure
import Tests.Ix.Compile.Twins.Cliques

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
    if bare.contains ``matcher._arg_pusher then
      errors := errors.push "bare matcher pulled an unrelated ambient pusher"
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

end Tests.Ix.Compile.SelectedClosure
