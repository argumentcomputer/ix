/-
  canon-pass1: Pass 1 (`Ix.Compile.Canon`) under `Rules.today` against the
  compiler, on the fixture closure of `validateAuxClosure`
  (`Tests.Ix.Compile.{Mutual,Canonicity,LevelSpellings}`, `IxVMInd`,
  `Test.Ix.Fixtures` and their dependencies).

  The compiler side is the Lean compiler's own functions, called directly in
  a `CompileEnv` seeded with the Rust compile of the same closure (the
  `aux-gen-diff` harness's setup): `CondenseM` (components), `sortConsts`
  (classes and order), and `expandNestedBlock` →
  `sortAuxByPartitionRefinement` → `computeAuxPerm` (nested auxiliaries).
  Checked:

  1. the components of the reference graph equal `CondenseM`'s, as a
     partition of the closure;
  2. for every component with two or more members or an inductive, the
     classes of `sortClasses Rules.today` equal `sortConsts`'s, member by
     member and in order;
  3. for every inductive component with nested auxiliaries, the canonical
     auxiliary count and the source permutation equal the compiler's;
  4. for every Lean block with nested auxiliaries, the discovery order
     (`Nested.expand`, Lean's deduplication) equals the occurrences of the
     environment's `all₀.rec_1 …` in order;
  5. `canonBlock` succeeds under both rule sets on every Lean block, and the
     comparator is a total preorder (`preorderViolations`) on every
     component under both;
  6. small pure checks of `tarjan`.

  Invoked as `lake test -- --ignored canon-pass1`.
-/
import Ix.CompileM
import Ix.Commit
import Ix.CondenseM
import Ix.AuxGen.Nested
import Ix.Compile.Canon
import Ix.CanonM
import Ix.Meta
import Tests.Ix.Compile.ValidateAux
import Tests.Ix.Compile.AuxGenDiff

open _root_.Ix.Compile.Canon

namespace Tests.Ix.Compile.Canon
open Ix.CompileM (CompilePhases CompileEnv)

structure Tally where
  checked : Nat := 0
  failures : Array String := #[]

def Tally.check (t : Tally) (ok : Bool) (msg : String) : Tally :=
  { t with checked := t.checked + 1, failures := if ok then t.failures else t.failures.push msg }

def pretty (xs : Array (Array Ix.Name)) : String :=
  toString (xs.map (·.map namePretty))

/-- Pure checks of the total Tarjan. -/
def tarjanChecks (t : Tally) : Tally :=
  let norm := fun (cs : Array (Array Nat)) => (cs.map (·.qsort (· < ·))).qsort
    (fun a b => a[0]! < b[0]!)
  let cases : List (Array (Array Nat) × Array (Array Nat)) := [
    (#[#[]], #[#[0]]),
    (#[#[1], #[0]], #[#[0, 1]]),
    (#[#[1], #[2], #[]], #[#[0], #[1], #[2]]),
    (#[#[1], #[0, 2], #[3], #[2]], #[#[0, 1], #[2, 3]]),
    (#[#[1], #[2], #[0, 3], #[4], #[5], #[3], #[7], #[6]],
      #[#[0, 1, 2], #[3, 4, 5], #[6, 7]]),
    (#[#[0]], #[#[0]])]
  cases.foldl (init := t) fun t (g, want) =>
    match tarjan g with
    | some cs => t.check (norm cs == norm want) s!"tarjan {g}: {cs}, want {want}"
    | none => t.check false s!"tarjan {g}: out of fuel"

def run (env : Lean.Environment) : IO UInt32 := do
  let mut t : Tally := tarjanChecks {}
  let filtered := validateAuxClosure env
  IO.println s!"[canon-pass1] {filtered.length} constants"
  let raw ← Ix.CompileM.rsCompilePhasesFFI filtered
  let rawEnv := raw.rawEnv.toEnvironment
  let condensed := raw.condensed.toCondensedBlocks
  let phases : CompilePhases := { rawEnv, condensed, compileEnv := raw.compileEnv.toEnv }
  let cenv : CompileEnv :=
    Tests.Compile.AuxGenDiff.seedBlockRegistry (Ix.Commit.mkCompileEnv phases) condensed
  let addr? : Ix.Name → Option Address := fun n =>
    match cenv.nameToAddr.get? n with
    | some a => some a
    | none => cenv.auxNameToAddr.get? n
  let cenvRef : Env := { const? := rawEnv.consts.get?, addr? }

  -- 1. components
  let names := rawEnv.consts.toArray.map (·.1)
  let refs := fun n => match rawEnv.consts.get? n with
    | some c => refsConst c
    | none => {}
  let key := fun (c : Array Ix.Name) =>
    (c.map (toString ·.getHash)).qsort (· < ·)
  match sccsOf names refs with
  | none => t := t.check false "sccsOf: out of fuel"
  | some comps =>
    let mine := (comps.map key).qsort (fun a b => a[0]! < b[0]!)
    let theirs := (condensed.blocks.toArray.map (fun (_, s) => key s.toArray)).qsort
      (fun a b => a[0]! < b[0]!)
    t := t.check (mine == theirs)
      s!"components: {mine.size} vs CondenseM {theirs.size}"

  -- 2, 3. classes and nested order per condensed component
  let mut nClasses := 0
  let mut nNested := 0
  let mut nCollapsed := 0
  let mut nMulti := 0
  let mut nPermMoved := 0
  let mut nPhaseADiffers := 0
  for (lo, members) in condensed.blocks do
    let ms := members.toArray
    let hasInd := ms.any fun n => match rawEnv.consts.get? n with
      | some (.inductInfo _) => true
      | _ => false
    if ms.size < 2 && !hasInd then continue
    let blockEnv : Ix.CompileM.BlockEnv :=
      { all := {}, current := lo, mutCtx := default, univCtx := [] }
    let ixRes := Ix.CompileM.CompileM.run cenv blockEnv {} do
      let mut cs : Array Ix.MutConst := #[]
      for n in ms do
        match (← Ix.AuxGen.lookupConst? n) with
        | some (.inductInfo v) => cs := cs.push (← Ix.CompileM.MutConst.mkIndc v)
        | some (.defnInfo v) => cs := cs.push (Ix.MutConst.fromDefinitionVal v)
        | some (.opaqueInfo v) => cs := cs.push (Ix.MutConst.fromOpaqueVal v)
        | some (.thmInfo v) => cs := cs.push (Ix.MutConst.fromTheoremVal v)
        | some (.recInfo v) => cs := cs.push (.recr v)
        | _ => pure ()
      let sorted ← Ix.CompileM.sortConsts cs.toList
      let classes := (sorted.map fun c => (c.map (·.name)).toArray).toArray
      -- nested, as generateAuxPatches computes it
      let originalAll : Array Ix.Name := Id.run do
        for c in cs do
          if let .indc i := c then return i.all
        return #[]
      let mut nestedOut : Option (Nat × Array Nat) := none
      if hasInd && !originalAll.isEmpty then
        let reps := classes.map (·[0]!)
        let mut aliasToRep : Std.HashMap Ix.Name Ix.Name := {}
        let mut o2c : Std.HashMap Ix.Name Ix.Name := {}
        for cls in classes do
          for n in cls do
            o2c := o2c.insert n cls[0]!
            if n != cls[0]! then aliasToRep := aliasToRep.insert n cls[0]!
        let mut metaNested := false
        for n in originalAll do
          if let some (.inductInfo v) ← Ix.AuxGen.lookupConst? n then
            if v.numNested > 0 then metaNested := true
        let probe ← Ix.AuxGen.expandNestedBlock reps aliasToRep
        let structNested := probe.types.size > probe.nOriginals
        if metaNested || structNested then
          let x ← if metaNested && structNested then
              (·.1) <$> Ix.AuxGen.sortAuxByPartitionRefinement probe
            else pure probe
          let perm ← Ix.AuxGen.computeAuxPerm x originalAll o2c addr?
          nestedOut := some (x.types.size - x.nOriginals, perm)
      pure (cs, classes, nestedOut)
    match ixRes with
    | .error e => t := t.check false s!"compiler side {namePretty lo}: {repr e}"
    | .ok ((cs, classes, nestedOut), _) =>
      match sortClasses Rules.today addr? cs.toList with
      | .error e => t := t.check false s!"sortClasses {namePretty lo}: {e}"
      | .ok (mine, _) =>
        nClasses := nClasses + 1
        if classes.any (·.size > 1) then nCollapsed := nCollapsed + 1
        if classes.size > 1 then nMulti := nMulti + 1
        if let .ok (a, _) := sortClasses Rules.phaseA addr? cs.toList then
          if classNames a != classes then nPhaseADiffers := nPhaseADiffers + 1
        t := t.check (classNames mine == classes)
          s!"classes {namePretty lo}: {pretty (classNames mine)} vs {pretty classes}"
        if let some (nCanon, perm) := nestedOut then
          let originalAll : Array Ix.Name := Id.run do
            for c in cs do
              if let .indc i := c then return i.all
            return #[]
          match componentNested Rules.today cenvRef originalAll classes with
          | .error e => t := t.check false s!"nested {namePretty lo}: {e}"
          | .ok none => t := t.check false s!"nested {namePretty lo}: none, compiler has {perm}"
          | .ok (some n) =>
            nNested := nNested + 1
            if perm.zipIdx.any (fun (p, j) => p != Ix.AuxGen.PERM_OUT_OF_SCC && p != j) then
              nPermMoved := nPermMoved + 1
            let permMine := n.perm.map fun
              | some i => i
              | none => Ix.AuxGen.PERM_OUT_OF_SCC
            t := t.check (permMine == perm && n.canonClasses.size == nCanon)
              s!"nested {namePretty lo}: perm {permMine} / {n.canonClasses.size} vs {perm} / {nCanon}"
  IO.println s!"[canon-pass1] compared {nClasses} components ({nMulti} with several classes, \
    {nCollapsed} with a collapse; phaseA differs on {nPhaseADiffers}), {nNested} nested \
    ({nPermMoved} with a moved auxiliary)"

  -- 4, 5. Lean blocks: discovery vs rec_N; canonBlock under both rule sets
  let mut seen : Std.HashSet Ix.Name := {}
  let mut nBlocks := 0
  let mut nDisc := 0
  for (_, c) in rawEnv.consts do
    let .inductInfo v := c | continue
    let some all0 := v.all[0]? | continue
    if seen.contains all0 then continue
    seen := seen.insert all0
    nBlocks := nBlocks + 1
    for rules in [Rules.today, Rules.phaseA] do
      match canonBlock rules cenvRef v.all with
      | .error e => t := t.check false s!"canonBlock {rules.name} {namePretty all0}: {e}"
      | .ok b =>
        t := t.check true ""
        for comp in b.components do
          let cs := comp.classes.toList.map fun cls =>
            cls.toList.filterMap fun n => (mutConstOf cenvRef n).toOption
          match preorderViolations rules addr? cs with
          | .error e => t := t.check false s!"preorder {rules.name} {namePretty all0}: {e}"
          | .ok vs => t := t.check vs.isEmpty s!"preorder {rules.name} {namePretty all0}: {vs}"
    if v.numNested > 0 then
      match expand cenvRef.ind? .lean v.all with
      | .error e => t := t.check false s!"discovery {namePretty all0}: {e}"
      | .ok x =>
        let sigs := x.sigs
        let recs := recMajorSignatures cenvRef.const? all0 v.numParams sigs.size
        let ok := sigs.size == v.numNested && (sigs.zip recs).all fun (s, r) =>
          match r with
          | some (h, ls, ps) => s.head == h && s.levels == ls && s.specs.size == ps.size &&
              (s.specs.zip ps).all fun (a, b) => auxSpecEq (fun _ => none) {} a b
          | none => false
        nDisc := nDisc + 1
        t := t.check ok s!"discovery {namePretty all0}: {sigs.size} auxiliaries \
          ({sigs.map (namePretty ·.head)}), numNested {v.numNested}, rec_N heads \
          {recs.map fun r => (r.map fun (h, _, _) => namePretty h)}"
  IO.println s!"[canon-pass1] {nBlocks} Lean blocks, {nDisc} nested blocks checked against rec_N"

  -- 7. seed sweep on every fixture component (today with the port fixes, phaseA)
  let mut nSwept := 0
  for (_, members) in condensed.blocks do
    let ms := members.toArray
    if ms.size < 2 then continue
    let cs := ms.toList.filterMap fun n => (mutConstOf cenvRef n).toOption
    if cs.length != ms.size then continue
    nSwept := nSwept + 1
    for rules in [Rules.today, Rules.phaseA] do
      match seedSweep rules addr? cs with
      | .ok r => t := t.check r.isNone s!"seed sweep {rules.name}: {r}"
      | .error e => t := t.check false s!"seed sweep {rules.name}: {e}"
  IO.println s!"[canon-pass1] seed sweep on {nSwept} components"

  -- 8. sibling occurrences of an external mutual group; isRec on a split block
  try
    let fe ← getFileEnvCore "Tests/Ix/Compile/Fixtures/CanonSiblingNest.lean"
    let lenv := fe.env
    let indLike := lenv.constants.toList.toArray.filter fun (_, c) =>
      match c with
      | .inductInfo _ | .ctorInfo _ | .recInfo _ => true
      | _ => false
    let consts := (Ix.CanonM.canonChunk indLike).foldl (init := ({} : Std.HashMap Ix.Name Ix.ConstantInfo))
      fun m (n, c) => m.insert n c
    let fenv : Env := { const? := consts.get?, addr? := fun _ => none }
    for nm in [`CanonSiblingNest.T, `CanonSiblingNest.F, `CanonSiblingNest.B] do
      let n := Ix.Name.fromLeanName nm
      let some (.inductInfo v) := consts.get? n | t := t.check false s!"sibling {nm}: missing"; continue
      let leanX := expand fenv.ind? .lean v.all
      let compX := expand fenv.ind? .compiler v.all
      match leanX, compX with
      | .ok x, .ok y =>
        let sigs := x.sigs
        let recs := recMajorSignatures fenv.const? n v.numParams (max sigs.size v.numNested)
        let ok := sigs.size == v.numNested && (sigs.zip recs).all fun (s, r) =>
          match r with
          | some (h, ls, ps) => s.head == h && s.levels == ls && s.specs.size == ps.size &&
              (s.specs.zip ps).all fun (a, b) => auxSpecEq (fun _ => none) {} a b
          | none => false
        t := t.check ok s!"sibling {nm}: Lean dedup {sigs.map (namePretty ·.head)} vs rec_N"
        let recHeads := recs.map fun r => (r.map fun (h, _, _) => namePretty h).getD "-"
        IO.println s!"[canon-pass1] sibling {nm}: numNested {v.numNested}, rec_N heads {recHeads}; \
          Lean-dedup expansion {sigs.map (namePretty ·.head)}; compiler-dedup expansion \
          {y.sigs.map (namePretty ·.head)}"
      | .error e, _ | _, .error e => t := t.check false s!"sibling {nm}: {e}"
    for nm in [`CanonSiblingNest.NR, `CanonSiblingNest.R] do
      if let some (.inductInfo v) := lenv.find? nm then
        IO.println s!"[canon-pass1] isRec {nm} = {v.isRec} (all {v.all})"
  catch e => t := t.check false s!"sibling fixture: {e}"

  IO.println s!"[canon-pass1] {t.checked} checks, {t.failures.size} failures"
  for f in t.failures.toList.take 50 do
    IO.println s!"[canon-pass1] FAIL {f}"
  return if t.failures.isEmpty then 0 else 1

end Tests.Ix.Compile.Canon
