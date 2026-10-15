/-
  canon-pass1: Pass 1 (`Ix.Compile.Canon`) against the compiler's Step 1, on
  the fixture closure of `validateAuxClosure`
  (`Tests.Ix.Compile.{Mutual,Canonicity,LevelSpellings}`, `IxVMInd`,
  `Test.Ix.Fixtures` and their dependencies).

  The compiler side is `Ix.CondenseM.run`, `Ix.CompileM.sortConsts` and
  `Ix.AuxGen.expandNestedBlock` → `sortAuxByPartitionRefinement` →
  `computeAuxPerm`, called in a `CompileEnv` seeded with the Rust compile of
  the same closure (the `aux-gen-diff` harness's setup). Checked:

  1. the condensation (`Ix.CondenseM.run` over the closure's reference
     graph) has the components of Rust's condensation and of `sccsOf`, as
     a partition, and every block's representative is one of its members;
  2. for every component with two or more members or an inductive, the
     compiler's `sortConsts` (addresses through the compile environment)
     gives the classes of the pure `sortClasses Rules.today`, member by
     member and in order;
  3. for every inductive component with nested auxiliaries, the compiler's
     path gives the canonical auxiliary count and the source permutation of
     Pass 1's own expansion (`componentNested Rules.today`);
  4. for every Lean block with nested auxiliaries, the discovery order
     (`Nested.expand`, Lean's deduplication) equals the occurrences of the
     environment's `all₀.rec_1 …` in order;
  5. `canonBlock` succeeds under `Rules.today` and `Rules.phaseA` on every
     Lean block, and the comparator is a total preorder
     (`preorderViolations`) on every component under both;
  6. small pure checks of `tarjan` and `condensation`;
  7. the seed sweep: the classes do not depend on the presentation;
  8. sibling occurrences of an external mutual group;
  9. **the port fixes change nothing on the fixtures**: on every component
     (and every nested block's auxiliary sort) the classes and their order
     are identical with `portFixes` off (`Rules.today`) and on
     (`Rules.compiler`), and the unfixed comparator reads no cached
     ordering back for the swapped pair inside a sort; and two synthetic
     pairs show what each fix does (a definition against an inductive: `lt`
     both ways unfixed, by kind tag fixed; a cached strong `lt` read back
     for the swapped pair: unflipped unfixed, flipped fixed).

  The comparator-study helpers (`compareFresh`, `preorderViolations`, the
  seed sweep) live here, not in the library.

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

def ruleName (r : Rules) : String :=
  if r == .today then "today" else if r == .phaseA then "phaseA"
  else if r == .compiler then "compiler" else reprStr r

/-! ## The comparator study -/

/-- Uncached comparison under `rules` at context `ctx`. -/
def compareFresh (rules : Rules) (addr? : Ix.Name → Option Address) (ctx : Ix.MutCtx)
    (x y : Ix.MutConst) : Except CmpError Ordering :=
  (·.1) <$> (compareConst rules addr? ctx x y).run {}

/-- Pairs that are not antisymmetric and triples that are not transitive at
the fixed-point context of `classes` (members flattened), each as a short
description. Exhaustive: cubic in the member count. -/
def preorderViolations (rules : Rules) (addr? : Ix.Name → Option Address)
    (classes : List (List Ix.MutConst)) : Except String (Array String) := do
  let ctx := Ix.MutConst.ctx classes
  let ms := classes.flatten.toArray
  let n := ms.size
  let mut tbl : Array (Array Ordering) := #[]
  for hi : i in [0:ms.size] do
    let mut row : Array Ordering := #[]
    for hj : j in [0:ms.size] do
      row := row.push (← (compareFresh rules addr? ctx ms[i] ms[j]).mapError toString)
    tbl := tbl.push row
  let mut out : Array String := #[]
  let nm := fun (i : Nat) => ((ms[i]?).map (namePretty ·.name)).getD s!"#{i}"
  let at2 := fun (a b : Nat) => match tbl[a]? >>= (·[b]?) with
    | some o => (pure o : Except String Ordering)
    | none => throw s!"preorderViolations: table entry ({a}, {b}) out of range"
  for i in [0:n] do
    if (← at2 i i) != .eq then out := out.push s!"irreflexive: {nm i}"
    for j in [0:n] do
      if (← at2 i j) != (← at2 j i).swap then
        out := out.push s!"not antisymmetric: {nm i} vs {nm j}"
      for k in [0:n] do
        let le := fun (a b : Nat) => do return (← at2 a b) != .gt
        if (← le i j) && (← le j k) && !(← le i k) then
          out := out.push s!"not transitive: {nm i} ≤ {nm j} ≤ {nm k}"
  return out

/-- A deterministic pseudo-random permutation (linear congruential draws,
Fisher-Yates). -/
def shuffle (seed : Nat) (xs : Array α) : Array α := Id.run do
  let mut a := xs
  let mut s := seed * 2654435761 + 12345
  for i' in [0:a.size] do
    let i := a.size - 1 - i'
    s := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
    let j := (s / 65536) % (i + 1)
    a := a.swapIfInBounds i j
  return a

/-- Classes as sets (names sorted by hash), in class order. -/
def classSets (classes : List (List Ix.MutConst)) : Array (Array Ix.Name) :=
  (classNames classes).map (·.qsort fun a b => compare a b == .lt)

/-- Run the refinement from the identity, reverse, name-hash and `random`
pseudo-random presentations of `sources` (seed `allOrder`, so the
presentation is the seed) and report the first presentation whose class
list differs, as sets in order, from the identity's. -/
def seedSweep (rules : Rules) (addr? : Ix.Name → Option Address) (sources : List Ix.MutConst)
    (random : Nat := 10) : Except CmpError (Option String) := do
  let r := { rules with seed := .allOrder, portFixes := true }
  let run := fun (xs : List Ix.MutConst) => do
    let (cls, _) ← sortClasses r addr? xs
    pure (classSets cls)
  let base ← run sources
  let arr := sources.toArray
  let mut presentations : List (String × List Ix.MutConst) :=
    [("reverse", sources.reverse), ("name-hash", sortByName sources)]
  for k in [0:random] do
    presentations := presentations ++ [(s!"random {k}", (shuffle k arr).toList)]
  for (label, xs) in presentations do
    let got ← run xs
    if got != base then
      return some s!"{label}: {got.map (·.map namePretty)} vs identity {base.map (·.map namePretty)}"
  return none

/-! ## Checks -/

/-- Pure checks of the total Tarjan and of `condensation`'s roots and
discovery order. -/
def tarjanChecks (t : Tally) : Tally :=
  let norm := fun (cs : Array (Array Nat)) => (cs.map (·.qsort (· < ·))).qsort
    (fun a b => a[0]?.getD 0 < b[0]?.getD 0)
  let cases : List (Array (Array Nat) × Array (Array Nat)) := [
    (#[#[]], #[#[0]]),
    (#[#[1], #[0]], #[#[0, 1]]),
    (#[#[1], #[2], #[]], #[#[0], #[1], #[2]]),
    (#[#[1], #[0, 2], #[3], #[2]], #[#[0, 1], #[2, 3]]),
    (#[#[1], #[2], #[0, 3], #[4], #[5], #[3], #[7], #[6]],
      #[#[0, 1, 2], #[3, 4, 5], #[6, 7]]),
    (#[#[0]], #[#[0]])]
  let t := cases.foldl (init := t) fun t (g, want) =>
    match tarjan g with
    | some cs => t.check (norm cs == norm want) s!"tarjan {g}: {cs}, want {want}"
    | none => t.check false s!"tarjan {g}: out of fuel"
  -- Roots are first-discovered members; discovery follows the presentation:
  -- 0 → 2 → 1 → 0 (one cycle) and 3 → 0: roots 0 and 3, order 0, 2, 1, 3.
  match condensation #[#[2], #[0], #[1], #[0]] with
  | some c =>
    t.check (c.order == #[0, 2, 1, 3] && c.roots == #[0, 3] &&
        c.comps == #[#[0, 1, 2], #[3]])
      s!"condensation: order {c.order}, roots {c.roots}, comps {c.comps}"
  | none => t.check false "condensation: out of fuel"

def showE {ε α : Type} [ToString ε] [Repr α] : Except ε α → String
  | .ok a => reprStr a
  | .error e => s!"error: {e}"

/-- What each port fix does, on synthetic members. C1: a definition and an
inductive compare `lt` in both orders unfixed, and by kind tag
(definition < inductive) fixed. C2: a strong `lt` cached for `(x, y)` is
read back for `(y, x)` unflipped unfixed, flipped fixed. -/
def portFixUnitChecks (t : Tally) : Tally :=
  let s0 := Ix.Expr.mkSort Ix.Level.mkZero
  let nm := fun (s : String) => Ix.Name.mkStr Ix.Name.mkAnon s
  let defn := fun (n : String) (lps : Array Ix.Name) =>
    Ix.MutConst.defn ⟨nm n, lps, s0, .defn, s0, .opaque, .safe, #[]⟩
  let d := defn "canonPortFixD" #[]
  let i := Ix.MutConst.indc ⟨nm "canonPortFixI", #[], s0, 0, 0, #[], #[], 0, false, false, false⟩
  let x := defn "canonPortFixX" #[]
  let y := defn "canonPortFixY" #[nm "u"]
  let none? : Ix.Name → Option Address := fun _ => none
  let fresh := fun (r : Rules) (a b : Ix.MutConst) => compareFresh r none? {} a b
  let t := match fresh .today d i, fresh .today i d, fresh .compiler d i, fresh .compiler i d with
    | .ok .lt, .ok .lt, .ok .lt, .ok .gt => t.check true ""
    | a, b, c, e => t.check false s!"C1: today {showE a}/{showE b}, fixed {showE c}/{showE e}"
  let seq := fun (r : Rules) =>
    (do
      let a ← compareConst r none? {} x y
      let b ← compareConst r none? {} y x
      pure (a, b) : CmpM (Ordering × Ordering)).run' {}
  match seq .today, seq .compiler, fresh .today y x with
  | .ok (.lt, .lt), .ok (.lt, .gt), .ok .gt => t.check true ""
  | a, b, c => t.check false s!"C2: today {showE a}, fixed {showE b}, uncached {showE c}"

def run (env : Lean.Environment) : IO UInt32 := do
  let mut t : Tally := portFixUnitChecks (tarjanChecks {})
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

  -- 1. components: the compiler's condensation against Rust's and `sccsOf`
  let names := rawEnv.consts.toArray.map (·.1)
  let refs := fun n => match rawEnv.consts.get? n with
    | some c => refsConst c
    | none => {}
  let refMap : Ix.Map Ix.Name (Ix.Set Ix.Name) :=
    names.foldl (init := {}) fun m n => m.insert n (refs n)
  let key := fun (c : Array Ix.Name) =>
    (c.map (toString ·.getHash)).qsort (· < ·)
  let partition := fun (cs : Array (Array Ix.Name)) =>
    (cs.map key).qsort (fun a b => a[0]?.getD "" < b[0]?.getD "")
  let rust := partition (condensed.blocks.toArray.map fun (_, s) => s.toArray)
  let wired := Ix.CondenseM.run refMap
  let w := partition (wired.blocks.toArray.map fun (_, s) => s.toArray)
  t := t.check (w == rust) s!"components: compiler {w.size} vs Rust {rust.size}"
  match sccsOf names refs with
  | some comps =>
    t := t.check (partition comps == w)
      s!"components: sccsOf {comps.size} vs compiler {w.size}"
  | none => t := t.check false "sccsOf: a component index out of range"
  let repsOk := wired.blocks.toList.all fun (lo, s) =>
    s.contains lo && s.toList.all fun n => wired.lowLinks.get? n == some lo
  t := t.check repsOk "components: a representative is not a member of its block"
  t := t.check (wired.blockRefs.size == wired.blocks.size)
    s!"components: {wired.blockRefs.size} blockRefs for {wired.blocks.size} blocks"

  -- 2, 3. classes and nested order per condensed component
  let mut nClasses := 0
  let mut nNested := 0
  let mut nCollapsed := 0
  let mut nMulti := 0
  let mut nPermMoved := 0
  let mut nPhaseADiffers := 0
  let mut nPortFix := 0
  let mut nPortFixAux := 0
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
      let mut auxX : Option Expanded := none
      if hasInd && !originalAll.isEmpty then
        let reps := classes.filterMap (·[0]?)
        let mut aliasToRep : Std.HashMap Ix.Name Ix.Name := {}
        let mut o2c : Std.HashMap Ix.Name Ix.Name := {}
        for cls in classes do
          let some rep := cls[0]? | continue
          for n in cls do
            o2c := o2c.insert n rep
            if n != rep then aliasToRep := aliasToRep.insert n rep
        let mut metaNested := false
        for n in originalAll do
          if let some (.inductInfo v) ← Ix.AuxGen.lookupConst? n then
            if v.numNested > 0 then metaNested := true
        let probe ← Ix.AuxGen.expandNestedBlock reps aliasToRep
        let structNested := probe.types.size > probe.nOriginals
        if metaNested || structNested then
          if metaNested && structNested then auxX := some probe.toCanon
          let x ← if metaNested && structNested then
              (·.1) <$> Ix.AuxGen.sortAuxByPartitionRefinement probe
            else pure probe
          let perm ← Ix.AuxGen.computeAuxPerm x originalAll o2c addr?
          nestedOut := some (x.types.size - x.nOriginals, perm)
      pure (cs, classes, nestedOut, auxX)
    match ixRes with
    | .error e => t := t.check false s!"compiler side {namePretty lo}: {repr e}"
    | .ok ((cs, classes, nestedOut, auxX), _) =>
      -- 9. the port fixes change nothing: classes and order with them off
      -- (`Rules.today`) and on (`Rules.compiler`), and no reversed
      -- non-equal cache hit inside the unfixed sort
      match sortClasses Rules.today addr? cs.toList, sortClasses Rules.compiler addr? cs.toList with
      | .ok (off, st), .ok (on, _) =>
        nPortFix := nPortFix + 1
        t := t.check (classNames off == classNames on)
          s!"port fixes {namePretty lo}: {pretty (classNames off)} off vs {pretty (classNames on)} on"
        t := t.check (st.hazards == 0)
          s!"port fixes {namePretty lo}: {st.hazards} reversed non-equal cache hits unfixed"
      | .error e, _ | _, .error e => t := t.check false s!"port fixes {namePretty lo}: {e}"
      if let some x := auxX then
        match structuralAuxClasses Rules.today addr? x, structuralAuxClasses Rules.compiler addr? x with
        | .ok off, .ok on =>
          nPortFixAux := nPortFixAux + 1
          t := t.check (classNames off == classNames on)
            s!"port fixes, auxiliaries of {namePretty lo}: {pretty (classNames off)} off vs \
              {pretty (classNames on)} on"
        | .error e, _ | _, .error e => t := t.check false s!"port fixes, auxiliaries of {namePretty lo}: {e}"
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
    ({nPermMoved} with a moved auxiliary); port fixes neutral on {nPortFix} components and \
    {nPortFixAux} auxiliary sorts"

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
      | .error e => t := t.check false s!"canonBlock {ruleName rules} {namePretty all0}: {e}"
      | .ok b =>
        t := t.check true ""
        for comp in b.components do
          let cs := comp.classes.toList.map fun cls =>
            cls.toList.filterMap fun n => (mutConstOf cenvRef n).toOption
          match preorderViolations rules addr? cs with
          | .error e => t := t.check false s!"preorder {ruleName rules} {namePretty all0}: {e}"
          | .ok vs => t := t.check vs.isEmpty s!"preorder {ruleName rules} {namePretty all0}: {vs}"
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

  -- 7. seed sweep on every fixture component (with the port fixes, and phaseA)
  let mut nSwept := 0
  for (_, members) in condensed.blocks do
    let ms := members.toArray
    if ms.size < 2 then continue
    let cs := ms.toList.filterMap fun n => (mutConstOf cenvRef n).toOption
    if cs.length != ms.size then continue
    nSwept := nSwept + 1
    for rules in [Rules.today, Rules.phaseA] do
      match seedSweep rules addr? cs with
      | .ok r => t := t.check r.isNone s!"seed sweep {ruleName rules}: {r}"
      | .error e => t := t.check false s!"seed sweep {ruleName rules}: {e}"
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
