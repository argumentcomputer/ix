/-
  canon-pass1: Pass 1 (`Ix.Compile.Canon`) as the compiler runs it, on the
  fixture closure of `validateAuxClosure`
  (`Tests.Ix.Compile.{Mutual,Canonicity,LevelSpellings}`, `IxVMInd`,
  `Test.Ix.Fixtures` and their dependencies).

  The compiler's Step 1 is wired into Pass 1 under `Rules.compiler`, which
  is `Rules.phaseA` since A2-order (levels after `canonUniv`, nested
  auxiliaries in discovery order, the port fixes): `Ix.CondenseM.run` is
  `condensation`, `Ix.CompileM.sortConsts` is `sortClasses`, and
  `Ix.AuxGen.sortAuxByPartitionRefinement`/`computeAuxPerm` take their
  order and permutation from `canonicalAuxOrder`/`computePerm`. The
  compiler side below is that wired path, called in a `CompileEnv` seeded
  with the Rust compile of the same closure (the `aux-gen-diff` harness's
  setup). Checked:

  1. the wired condensation (`Ix.CondenseM.run` over the closure's reference
     graph) has the components of Rust's condensation and of `sccsOf`, as
     a partition, and every block's representative is one of its members;
  2. for every component with two or more members or an inductive, the
     wired `sortConsts` (in `CompileM`, addresses through
     `constAddrLookup`) gives the classes of the pure
     `sortClasses Rules.compiler`, member by member and in order (and the
     components whose order today's rules would give differently, i.e.
     the order moves of comparing levels after `canonUniv`, are counted);
  3. for every inductive component with nested auxiliaries, the wired
     compiler path (`expandNestedBlock` → `sortAuxByPartitionRefinement` →
     `computeAuxPerm`) gives the canonical auxiliary count and the source
     permutation of Pass 1's own expansion (`componentNested
     Rules.compiler`, external groups from the compiled class registry).
     Under discovery order this is Lean's `rec_N` order wherever the
     member order is Lean's, so the oracle of today's structural order is
     replaced by Lean's own; the components with a moved auxiliary are
     counted under both orders;
  4. for every Lean block with nested auxiliaries, the discovery order
     (`Nested.expand`, Lean's deduplication) equals the occurrences of the
     environment's `all₀.rec_1 …` in order;
  5. `canonBlock` succeeds under both rule sets on every Lean block, and the
     comparator is a total preorder (`preorderViolations`) on every
     component under both;
  6. small pure checks of `tarjan` and `condensation`;
  7. the seed sweep;
  8. sibling occurrences of an external mutual group;
  9. **the port fixes change nothing on the fixtures**: on every component
     (and every nested block's auxiliary sort) the classes and their order
     are identical with `portFixes` off (`Rules.today`) and on
     (`todayFixed`), and today's comparator reads no cached ordering
     back for the swapped pair inside a sort; and two synthetic pairs show
     what each fix does (a definition against an inductive: `lt` both ways
     today, by kind tag fixed; a cached strong `lt` read back for the
     swapped pair: unflipped today, flipped fixed).
  10. **representatives**: under `Rules.today` and `Rules.phaseA` every class
     of every component lists its members in name-hash order, so the
     representative is the least-name-hash member; on a synthetic three-way
     collapse from four presentations likewise, and with the measurement
     switches `allOrder`/`firstInCanonicalOrder` the class keeps the
     presentation's order.

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
import Tests.Ix.Compile.Twins
import Tests.Ix.Compile.AuxNames
import Tests.Ix.Compile.AddressNames

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

/-- Pure checks of the total Tarjan and of `condensation`'s roots and
discovery order. -/
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

def showE {α : Type} [Repr α] : Except String α → String
  | .ok a => reprStr a
  | .error e => s!"error: {e}"

/-- Today's rules with only the two port fixes on (what `Rules.compiler` was
before A2-order). -/
def todayFixed : Rules := { Rules.today with portFixes := true }

/-- What each port fix does, on synthetic members (design document §3.4).
C1: a definition and an inductive compare `lt` in both orders today, and by
kind tag (definition < inductive) with the fix. C2: a strong `lt` cached
for `(x, y)` is read back for `(y, x)` unflipped today, flipped with the
fix. -/
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
  let t := match fresh .today d i, fresh .today i d, fresh todayFixed d i, fresh todayFixed i d with
    | .ok .lt, .ok .lt, .ok .lt, .ok .gt => t.check true ""
    | a, b, c, e => t.check false s!"C1: today {showE a}/{showE b}, fixed {showE c}/{showE e}"
  let seq := fun (r : Rules) =>
    (do
      let a ← compareConst r none? {} x y
      let b ← compareConst r none? {} y x
      pure (a, b) : CmpM (Ordering × Ordering)).run' {}
  match seq .today, seq todayFixed, fresh .today y x with
  | .ok (.lt, .lt), .ok (.lt, .gt), .ok .gt => t.check true ""
  | a, b, c => t.check false s!"C2: today {showE a}, fixed {showE b}, uncached {showE c}"

/-- Every class lists its members in name-hash order, so its first member
(the representative) has the least name hash. -/
def nameSorted (classes : Array (Array Ix.Name)) : Bool :=
  classes.all fun cls =>
    (List.range (cls.size - 1)).all fun k => compare cls[k]! cls[k + 1]! == .lt

/-- Representatives on a synthetic collapse: three alpha-equal definitions
form one class, listed in name-hash order (the representative is the
least-name-hash member) under `Rules.today` and `Rules.phaseA` from every
presentation; and with the measurement switches `allOrder` and
`firstInCanonicalOrder` the class keeps the presentation's order (the last
group of a refinement round used to come out reversed). -/
def representativeUnitChecks (t : Tally) : Tally :=
  let s0 := Ix.Expr.mkSort Ix.Level.mkZero
  let mk := fun (s : String) =>
    Ix.MutConst.defn ⟨Ix.Name.mkStr Ix.Name.mkAnon s, #[], s0, .defn, s0, .opaque, .safe, #[]⟩
  let ms := [mk "canonRepA", mk "canonRepB", mk "canonRepC"]
  let presentations := [ms, ms.reverse, [ms[1]!, ms[0]!, ms[2]!], [ms[2]!, ms[0]!, ms[1]!]]
  let none? : Ix.Name → Option Address := fun _ => none
  let stable : Rules :=
    { Rules.today with seed := .allOrder, representative := .firstInCanonicalOrder }
  presentations.foldl (init := t) fun t p =>
    let t := [Rules.today, Rules.phaseA].foldl (init := t) fun t r =>
      match sortClasses r none? p with
      | .ok (cls, _) =>
        let names := classNames cls
        t.check (names.size == 1 && names[0]!.size == 3 && nameSorted names)
          s!"representative {r.name}: {pretty names}"
      | .error e => t.check false s!"representative {r.name}: {e}"
    match sortClasses stable none? p with
    | .ok (cls, _) =>
      let names := classNames cls
      t.check (names == #[(p.map (·.name)).toArray])
        s!"stable class order: {pretty names} from {p.map (namePretty ·.name)}"
    | .error e => t.check false s!"stable class order: {e}"

/-- Compile the checked flag fixture through the ordinary class/member fold and
canonical sharing builder, returning the complete serialized anonymous block.
Reversing class members also exercises the choice of representative. -/
def nonDepPayload (env : Lean.Environment) (ns : Lean.Name) (reverseInput reverseReps : Bool) :
    Except String (List Nat × ByteArray) := do
  let inputs := ([`Left, `Right, `Left.mk, `Right.mk].filterMap fun n =>
    (env.find? (ns ++ n)).map (fun ci => (ns ++ n, ci))).toArray
  let consts := (Ix.CanonM.canonChunk inputs).foldl
    (fun m (n, ci) => m.insert n ci) ({} : Std.HashMap Ix.Name Ix.ConstantInfo)
  let cenv := Env.ofSource { source := { consts }, addr? := fun _ => none }
  let names := [`Left, `Right].map fun n => Ix.Name.fromLeanName (ns ++ n)
  let members ← names.mapM (mutConstOf cenv)
  let (classes, _) ← sortClasses Rules.compiler cenv.addr?
    (if reverseInput then members.reverse else members)
  let classes := if reverseReps then classes.map List.reverse else classes
  let benv : Ix.CompileM.BlockEnv := {
    all := names.foldl (fun s n => s.insert n) {}, current := names.head!,
    mutCtx := Ix.MutConst.ctx classes, univCtx := [] }
  let (bytes, _) ← (Ix.CompileM.CompileM.run default benv {} do
    let (payloads, _, _) ← Ix.CompileM.compileMutConsts classes
    let cache ← get
    let block ← Ix.CompileM.buildBlockConstant (.muts payloads) cache.refs cache.univs
    pure (Ixon.serConstant block)).mapError toString
  pure (classes.map List.length, bytes)

def nonDepUnitChecks (env : Lean.Environment) (t : Tally) : Tally := Id.run do
  let mut t := t
  let ns := `Tests.Ix.Compile.Fixtures.LetNonDep
  let values := [`letForm, `haveForm, `neighbour].mapM fun n => do
    let some (.defnInfo d) := env.find? (ns ++ n) | none
    pure ((Ix.CanonM.canonExpr d.value).run' {})
  match values with
  | some [a, b, neighbour] =>
    let ctx : CmpCtx := {
      levels := .afterCanonUniv, mode := .addr,
      addr? := fun _ => none, mutCtx := {} }
    let cmp := fun x y => (compareExpr ctx [] [] x y).toOption.map fun o => (o.strong, o.ord)
    t := t.check (cmp a b == some (true, .lt) && cmp b a == some (true, .gt))
      "checked let nonDep spellings must compare strongly false < true"
    t := t.check (cmp a neighbour == some (true, .eq))
      "checked same-flag binder-renamed neighbour must compare equal"
  | _ => t := t.check false "checked let nonDep declarations missing"
  for (family, sizes) in [(`Split, [1, 1]), (`Equal, [2])] do
    let ns := `Tests.Ix.Compile.Fixtures.LetNonDep ++ family
    match nonDepPayload env (ns ++ `A) false false with
    | .error e => t := t.check false s!"let nonDep {family}: {e}"
    | .ok (actual, reference) =>
      t := t.check (actual == sizes) s!"let nonDep {family}: classes {actual}, expected {sizes}"
      for pres in [`A, `B] do
        for input in [false, true] do
          for reps in [false, true] do
            match nonDepPayload env (ns ++ pres) input reps with
            | .error e => t := t.check false s!"let nonDep {family}.{pres}: {e}"
            | .ok (actual, bytes) =>
              t := t.check (actual == sizes && bytes == reference)
                s!"let nonDep {family}.{pres}: serialized payload changed (input={input}, reps={reps})"
  return t

/-- The key follows positional serialized universes, including nested sort
and constant levels. Malformed levels fail beside well-formed neighbours. -/
def nestedKeyUnitChecks (t : Tally) : Tally := Id.run do
  let nm := Ix.Name.fromLeanName
  let u := nm `u
  let v := nm `v
  let z := Ix.Level.mkZero
  let pu := Ix.Level.mkParam u
  let pv := Ix.Level.mkParam v
  let key := addrKey [u, v] (fun _ => none) (fun _ => false)
  let app := fun l => Ix.Expr.mkApp (Ix.Expr.mkConst (nm `List) #[l])
    (Ix.Expr.mkSort l)
  let mut t := t
  t := t.check ((key (app z)).isOk && (key (app (Ix.Level.mkMax z z))).isOk &&
      (key (app z)).toOption == (key (app (Ix.Level.mkMax z z))).toOption)
    "nested key: zero and max zero zero must agree in constant and sort levels"
  t := t.check ((key (app pu)).isOk && (key (app pv)).isOk &&
      (key (app pu)).toOption != (key (app pv)).toOption)
    "nested key: distinct positional universe parameters must remain distinct"
  t := t.check ((key (app (Ix.Level.mkMax pu pv))).isOk &&
      (key (app (Ix.Level.mkMax pv pu))).isOk &&
      (key (app (Ix.Level.mkMax pu pv))).toOption ==
      (key (app (Ix.Level.mkMax pv pu))).toOption)
    "nested key: commuted max must follow canonical serialized universes"
  t := t.check (!(key (app (Ix.Level.mkParam (nm `missing)))).isOk &&
      !(key (app (Ix.Level.mkMvar (nm `unknown)))).isOk)
    "nested key: unknown universe parameters and metavariables must fail"
  let cx : XCtx := {
    ind? := fun _ => none, dedup := .lean,
    all0 := nm `Empty, blockLevels := #[], nParams := 0, paramBinders := #[] }
  for fuel in [0, 1, 2] do
    t := t.check (match walkQueue cx fuel 0 { keyError := some "first key error" } with
      | .error e => e == "first key error"
      | .ok _ => false) s!"nested key: pending error bypassed at empty queue/fuel={fuel}"
    t := t.check ((walkQueue cx fuel 0 {}).isOk)
      s!"nested key: valid empty queue rejected at fuel={fuel}"
  return t

/-- Serialize all members of an expanded block using the ordinary canonical
sharing builder. This compares every primary payload byte, not Expr hashes
or source-order metadata. This helper is used only for the checked safe
fixture and safe external List. `numNested`, `isRec` and `isReflexive` are
not fields of the primary `Ixon.Inductive` emitted by
`finishInductiveDataCompilation`; `isUnsafe` is checked below. -/
def expandedPayload (cenv : CompileEnv) (x : Expanded) : Except String ByteArray := do
  let members := x.types.map fun mem =>
    let ctors := mem.ctors.zipIdx.map fun (c, ci) =>
      ({ cnst := { name := c.name, levelParams := x.levelParams, type := c.typ }
         induct := mem.name, cidx := ci, numParams := mem.nParams,
         numFields := c.nFields, isUnsafe := false } : Ix.ConstructorVal)
    Ix.MutConst.indc {
      name := mem.name, levelParams := x.levelParams, type := mem.typ,
      numParams := mem.nParams, numIndices := mem.nIndices, all := x.types.map (·.name),
      ctors, numNested := 0, isRec := false, isReflexive := false, isUnsafe := false }
  let classes := members.toList.map (fun m => [m])
  let benv : Ix.CompileM.BlockEnv := {
    all := members.foldl (fun s m => s.insert m.name) {},
    current := members[0]!.name, mutCtx := Ix.MutConst.ctx classes,
    univCtx := x.levelParams.toList }
  let (bytes, _) ← (Ix.CompileM.CompileM.run cenv benv {} do
    let (payloads, _, _) ← Ix.CompileM.compileMutConsts classes
    let cache ← get
    let block ← Ix.CompileM.buildBlockConstant (.muts payloads) cache.refs cache.univs
    pure (Ixon.serConstant block)).mapError toString
  pure bytes

/-- The kernel-checked level-spelling fixture through both the pure and
production expansion, with actual compiled dependency addresses/registry.
Either representative, either source member order, and either input order
has one auxiliary and identical complete canonical payload bytes. -/
def nestedLevelChecks (cenv : CompileEnv) (t : Tally) : Tally := Id.run do
  let addr? := fun n => cenv.nameToAddr.get? n <|> cenv.auxNameToAddr.get? n
  let sourceEnv : SourceEnv := { source := cenv.env, addr?, groupOf := sourceGroupsOfBlocks cenv.blocks }
  let env := Env.ofSource sourceEnv
  let mut t := t
  for family in [`Mixed, `Neighbour] do
    let mut reference : Option ByteArray := none
    for pres in [`A, `B] do
      let ns := `Tests.Ix.Compile.Fixtures.NestedLevels ++ family ++ pres
      let names := [`Left, `Right].map (fun n => Ix.Name.fromLeanName (ns ++ n))
      for reverse in [false, true] do
        let result : Except String (List Nat × Array (Nat × Nat × ByteArray × ByteArray)) := do
          let ms ← (if reverse then names.reverse else names).mapM (mutConstOf env)
          let (cls, _) ← sortClasses Rules.compiler addr? ms
          let mut results := #[]
          for rep in names do
            let aliases := names.foldl (fun m n => if n == rep then m else m.insert n rep)
              ({} : Std.HashMap Ix.Name Ix.Name)
            let x ← expandSource cenv.env .lean #[rep] aliases sourceEnv.groupOf (some addr?)
            let benv : Ix.CompileM.BlockEnv := {
              all := names.foldl (·.insert ·) {}, current := rep,
              mutCtx := Ix.MutConst.ctx cls, univCtx := [] }
            let (y, _) ← (Ix.CompileM.CompileM.run cenv benv {} do
              let y ← Ix.AuxGen.expandNestedBlock #[rep] aliases true
              pure (← Ix.AuxGen.sortAuxByPartitionRefinement y).1).mapError toString
            results := results.push (x.aux.size, y.types.size - y.nOriginals,
              ← expandedPayload cenv x, ← expandedPayload cenv y.toCanon)
          pure (cls.map List.length, results)
        match result with
        | .error e => t := t.check false s!"nested levels {family}.{pres}: {e}"
        | .ok (sizes, results) =>
          t := t.check (sizes == [2]) s!"nested levels {family}.{pres}: classes={sizes}"
          for (pureCount, productionCount, pureBytes, productionBytes) in results do
            if reference.isNone then reference := some pureBytes
            t := t.check (pureCount == 1 && productionCount == 1 &&
                some pureBytes == reference && productionBytes == pureBytes)
              s!"nested levels {family}.{pres}: pure={pureCount}, production={productionCount}, input-reversed={reverse}; full payload bytes must agree"
  return t

/-- Every declaration in the checked mixed-level source and its same-spelling
neighbour compiles, including all recursors. The actual stored projection and
owning-block payloads agree under member reordering. Canonical recursors agree
even when source-facing images retain different motive orders and numbering. -/
def nestedLevelPipelineChecks (env : Lean.Environment) (t : Tally) : IO Tally := do
  let fixturePrefix := `Tests.Ix.Compile.Fixtures.NestedLevels
  let seeds := env.constants.toList.filterMap fun (n, _) =>
    if fixturePrefix.isPrefixOf n then some n else none
  let closure := Tests.Ix.Compile.Twins.closeWithRecursors env <|
    Ix.EnvScope.collectDeps env (seeds ++ [`PProd, `PProd.mk, `And, `And.intro,
      `True, `True.intro, `Eq, `Eq.refl])
  let mut t := t.check (!seeds.isEmpty) "nested levels: checked fixture seeds missing"
  t := t.check (closure.all fun (_, ci) => match ci with
    | .inductInfo i => !i.isUnsafe
    | .ctorInfo c => !c.isUnsafe
    | _ => true) "nested levels: payload helper requires safe source and external inductives"
  let result ← Ix.CompileM.compileLeanConsts closure (numWorkers := 1)
  match result with
  | .error e => return t.check false s!"nested levels: complete pipeline failed: {e}"
  | .ok out =>
    t := t.check (out.ungroundedCount == 0 && out.cenv.ungrounded.isEmpty)
      s!"nested levels: unexpected pipeline failures: {out.cenv.ungrounded.toArray.map (fun (n,e) => (n.pretty,e))}"
    for n in seeds do
      let name := Ix.Name.fromLeanName n
      t := t.check ((out.env.getNamed? name).isSome &&
          (out.cenv.ungrounded.get? name).isNone)
        s!"nested levels: checked declaration has wrong emitted/refused coverage: {n}"
    let bytesOf := fun n => do
      let nd ← out.env.getNamed? (Ix.Name.fromLeanName n)
      let lc ← out.env.consts.get? nd.addr
      let c ← lc.get.toOption
      let block ← match c.info with
        | .iPrj p => some p.block
        | .cPrj p => some p.block
        | _ => none
      let owner ← out.env.consts.get? block
      pure (lc.rawBytes, owner.rawBytes)
    let recursorsOf := fun ns => (do
      let mut count := 0
      let mut payloads : Array (ByteArray × Option ByteArray) := #[]
      for (name, named) in out.env.named do
        if !ns.isPrefixOf (keyName name) || !Ix.Compile.Pass.hasReserved name then continue
        let .recr .. := named.constMeta.info | continue
        let loaded ← out.env.consts.get? named.addr
        let constant ← loaded.get.toOption
        match constant.info with
        | .rPrj _ | .recr _ => pure ()
        | _ => none
        let payload ← Tests.Ix.Compile.AddressNames.payload out name
        count := count + 1
        if !payloads.contains payload then payloads := payloads.push payload
      pure (count, payloads) : Option (Nat × Array (ByteArray × Option ByteArray)))
    let mut referenceRecs : Option (Array (ByteArray × Option ByteArray)) := none
    for family in [`Mixed, `Neighbour] do
      let ns := fixturePrefix ++ family
      for role in [`Left, `Right, `Left.mk, `Right.mk] do
        let a := bytesOf (ns ++ `A ++ role)
        let b := bytesOf (ns ++ `B ++ role)
        t := t.check (a.isSome && b.isSome && a == b)
          s!"nested levels {family}.{role}: actual full projection/owning-block bytes differ"
      for presentation in [`A, `B] do
        match recursorsOf (ns ++ presentation) with
        | none => t := t.check false s!"nested levels {family}.{presentation}: canonical recursor payload missing or malformed"
        | some (count, payloads) =>
          -- Left/Right share one canonical recursor; their one nested class
          -- has the other. The representative spelling can differ across
          -- presentations, so compare complete payload sets, not those names.
          t := t.check (count == 3 && payloads.size == 2)
            s!"nested levels {family}.{presentation}: canonical recursor coverage {count} names/{payloads.size} payloads, expected 3/2"
          if let some reference := referenceRecs then
            t := t.check (payloads.all reference.contains && reference.all payloads.contains)
              s!"nested levels {family}.{presentation}: canonical recursor/owning-block bytes differ"
          else referenceRecs := some payloads
    return t

/-- Generated-name tables ignore every cached prefix digest, while
retaining all structural components and ordinary overwrite semantics. -/
def nameTableChecks (t : Tally) : Tally := Id.run do
  let root := Ix.Name.fromLeanName `Root
  let changed := Ix.Name.str Ix.Name.mkAnon "Root" (Ix.Name.fromLeanName `Other).getHash
  let aux := fun r => Ix.Name.mkStr (Ix.Name.mkStr r "_nested") "List_1"
  let a := aux root
  let b := aux changed
  let collision := Ix.Name.str Ix.Name.mkAnon "Different" a.getHash
  let first := ({} : NameTable Nat).insert a 1
  let both := first.insert collision 2
  let updated := both.insert b 3
  let mut t := t.check (first.get? a == some 1 && first.getFast? a == first.get? a)
    "name table: ordinary generated-name hit"
  t := t.check (first.get? collision == none && first.getFast? collision == none)
    "name table: equal root digest cannot merge unequal structural names"
  t := t.check (both.getFast? a == some 1 && both.getFast? collision == some 2)
    "name table: cache overwrite retains both entries"
  t := t.check (first.get? b == some 1 && first.getFast? b == first.get? b)
    "name table: generated names over rehashed prefixes still match"
  t := t.check (updated.size == 2 && updated.getFast? a == some 3 &&
      updated.getFast? b == some 3 && updated.getFast? collision == some 2)
    "name table: structural overwrite replaces exactly one entry"
  let ctor := Ix.Name.mkStr a "mk"
  let target := Ix.Name.fromLeanName `Fresh
  t := t.check (keyName (nameReplacePrefix ctor b target) == `Fresh.mk &&
      keyName (Ix.AuxGen.nameReplacePrefix ctor b target) == `Fresh.mk)
    "name prefix: generated constructor matching ignores cached prefixes"
  t := t.check (keyName (nameReplacePrefix ctor collision target) == keyName ctor)
    "name prefix: unequal structural prefixes remain unchanged"
  let expr := Ix.Expr.mkProj b 0 (Ix.Expr.mkConst b #[])
  let table := ({} : NameTable Ix.Name).insert a target
  t := t.check (decide (occurrenceKey (table.replaceConstNames expr) =
      occurrenceKey (Ix.Expr.mkProj target 0 (Ix.Expr.mkConst target #[]))))
    "name table: generated constant and projection references both rename"
  return t

/-- Exercise confirmed hits, collisions and misses on the total structural
table. Forged cached fields here are cache controls, not Lean declarations. -/
def occurrenceTableChecks (t : Tally) : Tally := Id.run do
  let a := Ix.Expr.mkBVar 0
  let other := Ix.Expr.bvar 1 a.getHash
  let rehashed := Ix.Expr.bvar 0 (Ix.Expr.mkBVar 1).getHash
  let an := Ix.Name.fromLeanName `OccurrenceA
  let bn := Ix.Name.fromLeanName `OccurrenceB
  let first := ({} : OccurrenceTable).insert a an
  let both := first.insert other bn
  let again := both.insert rehashed bn
  let read := fun (table : OccurrenceTable) e =>
    (table.get? e).map keyName
  let fast := fun (table : OccurrenceTable) e =>
    (table.getFast? e).map keyName
  let mut t := t.check (read first a == some `OccurrenceA && fast first a == read first a)
    "occurrence table: ordinary hit"
  t := t.check (read first other == none && fast first other == none)
    "occurrence table: colliding unequal key must miss"
  t := t.check (read both a == some `OccurrenceA && fast both a == read both a &&
      read both other == some `OccurrenceB && fast both other == read both other)
    "occurrence table: overwritten cache candidate must preserve both structural entries"
  t := t.check (read both rehashed == some `OccurrenceA && fast both rehashed == read both rehashed)
    "occurrence table: different stored hash must find equal structural entry"
  t := t.check (again.entries.length == 2 && read again a == some `OccurrenceA &&
      fast again rehashed == some `OccurrenceA)
    "occurrence table: equal rehashed insertion must retain first discovery"
  let n := Ix.Name.fromLeanName `u
  let n' := Ix.Name.str Ix.Name.mkAnon "u" an.getHash
  let u := Ix.Level.mkParam n
  let u' := Ix.Level.param n' (Ix.Level.mkZero).getHash
  let x := Ix.Expr.mkConst n #[u]
  let y := Ix.Expr.mkConst n' #[u']
  t := t.check (decide (occurrenceKey x = occurrenceKey y))
    "occurrence key: nested name and level digests must not enter equality"
  let x := Ix.Expr.mkMData #[(n, .ofName n)] x
  let y := Ix.Expr.mkMData #[(n', .ofName n')] y
  t := t.check (decide (occurrenceKey x = occurrenceKey y))
    "occurrence key: metadata names must be structural"
  let z := Ix.Expr.mdata #[] y x.getHash
  t := t.check (!decide (occurrenceKey x = occurrenceKey z))
    "occurrence key: source metadata remains part of the key"
  return t

/-- Synthetic cache controls exercise the source resolver's actual Address
identity. The deliberately rehashed names are not claimed to be checked Lean
declarations. Every queried structural spelling must still be protected. -/
def sourceFastChecks (t : Tally) : Tally := Id.run do
  let a := Ix.Name.fromLeanName `SourceA
  let b := Ix.Name.str Ix.Name.mkAnon "SourceAlias" a.getHash
  let dep := Ix.Name.fromLeanName `SourceDependency
  let missing := Ix.Name.fromLeanName `MissingSource
  let missingAlias := Ix.Name.str Ix.Name.mkAnon "MissingAlias" missing.getHash
  let stored := Ix.Name.fromLeanName `StoredRecordName
  let storedDep := Ix.Name.fromLeanName `StoredDependencyName
  let ci : Ix.ConstantInfo := .axiomInfo {
    cnst := { name := stored, levelParams := #[], type := Ix.Expr.mkConst dep #[] }
    isUnsafe := false }
  let depCi : Ix.ConstantInfo := .axiomInfo {
    cnst := { name := storedDep, levelParams := #[], type := Ix.Expr.mkBVar 0 }
    isUnsafe := false }
  let source : Ix.Environment := { consts := ({} : Std.HashMap Ix.Name Ix.ConstantInfo).insert a ci |>.insert dep depCi }
  let names := #[a,b,missing,missingAlias,a]
  let result := sourceContextCached source names
  let expected := [keyName a,keyName missingAlias,keyName missing,keyName b,
    keyName storedDep,keyName dep,keyName stored,keyName dep,keyName a]
  let mut t := t.check (result.protectedNames == expected)
    "source cache: preserve all query spellings, missing aliases, order and duplicates"
  t := t.check (result.visitedKeys == [dep.getHash,a.getHash])
    "source cache: preserve exact finite visited-key order"
  let readShape := fun n => (result.declarations.get? n).map fun value =>
    (keyName value.getCnst.name,occurrenceKey value.getCnst.type)
  let expectedRecord := some (keyName stored,occurrenceKey (Ix.Expr.mkConst dep #[]))
  t := t.check (readShape a == expectedRecord && readShape b == expectedRecord &&
      (readShape missing).isNone && (readShape missingAlias).isNone)
    "source cache: actual lookup identity and record name remain distinct"
  let first := ({} : SourceFetchCache source).read a
  let aliasRead := first.cache.read b
  let absent := aliasRead.cache.read missing
  let absentAlias := absent.cache.read missingAlias
  t := t.check (first.cache.rows.size == 1 && aliasRead.cache.rows.size == 1 &&
      absent.cache.rows.size == 2 && absentAlias.cache.rows.size == 2 &&
      absent.value.isNone && absentAlias.value.isNone)
    "source cache: repeated present and missing lookup identities reuse exact fetch entries"
  let overrideName := Ix.Name.fromLeanName `OverlayRecord
  let override : Ix.ConstantInfo := .axiomInfo {
    cnst := { name := overrideName, levelParams := #[], type := Ix.Expr.mkBVar 1 }
    isUnsafe := false }
  let overlay := { source with overlay := ({} : Std.HashMap Ix.Name Ix.ConstantInfo).insert a override }
  let overlayResult := sourceContextCached overlay #[b,a]
  t := t.check (overlayResult.protectedNames == [keyName a,keyName overrideName,keyName b] &&
      overlayResult.visitedKeys == [a.getHash] &&
      (overlayResult.declarations.get? b).map (fun value => keyName value.getCnst.name) == some (keyName overrideName))
    "source cache: overlay precedence agrees with the actual resolver under alias queries"
  -- This is the actual finite-index fallback API used for canon-on-demand.
  -- The pinned payload and queried spelling deliberately differ from ci.name.
  let pinned : Lean.ConstantInfo := .axiomInfo {
    name := `PinnedSourceInput, levelParams := [], type := .sort .zero, isUnsafe := false }
  let lazySource : Ix.Environment := {
    consts := {}
    fallback? := some {
      index := ({} : Std.HashMap Ix.Name (Lean.Name × Lean.ConstantInfo))
        |>.insert a (`DecodeRoot,pinned)
        |>.insert dep (`DecodeDependency,pinned)
        |>.insert missing (`DecodeNone,pinned)
      fetch := fun payload =>
        if payload.1 == `DecodeRoot then some ci
        else if payload.1 == `DecodeDependency then some depCi
        else none } }
  let lazyResult := sourceContextCached lazySource names
  let lazyReadShape := fun n => (lazyResult.declarations.get? n).map fun value =>
    (keyName value.getCnst.name,occurrenceKey value.getCnst.type)
  t := t.check (lazyResult.protectedNames == expected &&
      lazyResult.visitedKeys == [dep.getHash,a.getHash])
    "source cache: lazy decoder retains exact query/record spellings and traversal lists"
  t := t.check (lazyResult.declarations.size == 2 &&
      lazyReadShape a == expectedRecord && lazyReadShape b == expectedRecord &&
      lazyReadShape dep == some (keyName storedDep,occurrenceKey (Ix.Expr.mkBVar 0)) &&
      (lazyReadShape missing).isNone && (lazyReadShape missingAlias).isNone)
    "source cache: lazy aliases and indexed decoder-none query retain complete declarations"
  let lazyFirst := ({} : SourceFetchCache lazySource).read a
  let lazyAlias := lazyFirst.cache.read b
  let lazyDependency := lazyAlias.cache.read dep
  let lazyAbsent := lazyDependency.cache.read missing
  let lazyAbsentAlias := lazyAbsent.cache.read missingAlias
  t := t.check (lazyFirst.cache.rows.size == 1 && lazyAlias.cache.rows.size == 1 &&
      lazyDependency.cache.rows.size == 2 && lazyAbsent.cache.rows.size == 3 &&
      lazyAbsentAlias.cache.rows.size == 3 && lazyAbsent.value.isNone &&
      lazyAbsentAlias.value.isNone)
    "source cache: lazy present and indexed decoder-none aliases reuse existing cache rows"
  let before : SourceContext := {
    declarations := ({} : Std.HashMap Ix.Name Ix.ConstantInfo).insert dep depCi
    protectedNames := [`Before]
    visitedKeys := [a.getHash,a.getHash] }
  let resumed := collectSourceCached lazySource sourceConstRefs sourceConstNames
    [b,missingAlias,a] before
  t := t.check (resumed.protectedNames == [keyName a,keyName missingAlias,keyName b,`Before] &&
      resumed.visitedKeys == [a.getHash,a.getHash])
    "source cache: arbitrary intermediate entry retains duplicate visited keys and exact protection order"
  t := t.check (resumed.declarations.size == 2 &&
      (resumed.declarations.get? a).map (fun value => keyName value.getCnst.name) == some (keyName stored) &&
      (resumed.declarations.get? dep).map (fun value => keyName value.getCnst.name) == some (keyName storedDep))
    "source cache: resumed known aliases still install their declaration and retain old declarations"
  return t

/-- Canonical reference categories stay distinct for all source spellings,
including the former literal address encoding. Cache hints are advisory. -/
def taggedOccurrenceChecks (t : Tally) : Tally := Id.run do
  let address := Address.blake3 "tagged occurrence control".toUTF8
  let encoded := Ix.Name.mkStr Ix.Name.mkAnon s!"#{address}"
  let sourceName := Ix.Name.fromLeanName `ExternalDependency
  let an := Ix.Name.fromLeanName `FirstAux
  let bn := Ix.Name.fromLeanName `SecondAux
  let named : OccurrenceRef := .named (keyName encoded)
  let external : OccurrenceRef := .external address
  let mut t := t.check (named != external)
    "occurrence key: an external address must not equal its literal source name"
  for (left,right) in [
      (OccurrenceKey.const named [], OccurrenceKey.const external []),
      (OccurrenceKey.proj named 0 (.bvar 0), OccurrenceKey.proj external 0 (.bvar 0))] do
    let a : OccurrenceInput := ⟨left, 37⟩
    let b : OccurrenceInput := ⟨right, 37⟩
    let rehashed : OccurrenceInput := ⟨left, 91⟩
    let first := ({} : OccurrenceTable).insert a an
    let both := first.insert b bn
    let again := both.insert rehashed bn
    t := t.check (first.get? b == none && first.getFast? b == none)
      "occurrence key: distinct reference categories sharing a cache bucket must miss"
    t := t.check ((both.getFast? a).map keyName == some `FirstAux &&
        (both.getFast? b).map keyName == some `SecondAux && both.entries.length == 2)
      "occurrence key: overwritten cache must retain both reference categories"
    t := t.check ((again.getFast? rehashed).map keyName == some `FirstAux &&
        again.entries.length == 2)
      "occurrence key: changed hint must recover the first structural insertion"
  let key := addrKey [] (fun n => if keyName n == keyName sourceName then some address else none)
    (fun n => keyName n == keyName encoded)
  for (retained,resolved) in [
      (Ix.Expr.mkConst encoded #[], Ix.Expr.mkConst sourceName #[]),
      (Ix.Expr.mkProj encoded 0 (Ix.Expr.mkBVar 0),
       Ix.Expr.mkProj sourceName 0 (Ix.Expr.mkBVar 0))] do
    t := t.check ((key retained).isOk && (key resolved).isOk &&
        (key retained).toOption != (key resolved).toOption)
      "canonical key: successful const/proj normalization must retain reference category"
  return t

def run (env : Lean.Environment) : IO UInt32 := do
  let mut t : Tally := occurrenceTableChecks (nameTableChecks (nestedKeyUnitChecks (nonDepUnitChecks env
    (representativeUnitChecks (portFixUnitChecks (tarjanChecks {}))))))
  t := taggedOccurrenceChecks (sourceFastChecks t)
  t ← nestedLevelPipelineChecks env t
  try
    Tests.Ix.Compile.AuxNames.run
    t := t.check true "auxiliary name capture regression"
  catch err =>
    t := t.check false s!"auxiliary name capture regression: {err}"
  try
    Tests.Ix.Compile.AddressNames.run
    t := t.check true "nested address identity regression"
  catch err =>
    t := t.check false s!"nested address identity regression: {err}"
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
  let sourceRef : SourceEnv := { source := rawEnv, addr? }
  let cenvRef := Env.ofSource sourceRef
  -- the canonical expansion as the compiler runs it: external groups from
  -- the compiled class registry
  let cenvRefC := Env.ofSource { sourceRef with groupOf := sourceGroupsOfBlocks cenv.blocks }
  t := nestedLevelChecks cenv t

  -- 1. components: the wired condensation against Rust's and `sccsOf`
  let names := rawEnv.consts.toArray.map (·.1)
  let refs := fun n => match rawEnv.consts.get? n with
    | some c => refsConst c
    | none => {}
  let refMap : Ix.Map Ix.Name (Ix.Set Ix.Name) :=
    names.foldl (init := {}) fun m n => m.insert n (refs n)
  let key := fun (c : Array Ix.Name) =>
    (c.map (toString ·.getHash)).qsort (· < ·)
  let partition := fun (cs : Array (Array Ix.Name)) =>
    (cs.map key).qsort (fun a b => a[0]! < b[0]!)
  let rust := partition (condensed.blocks.toArray.map fun (_, s) => s.toArray)
  match Ix.CondenseM.run refMap, sccsOf names refs with
  | .ok wired, some comps =>
    let w := partition (wired.blocks.toArray.map fun (_, s) => s.toArray)
    t := t.check (w == rust) s!"components: wired {w.size} vs Rust {rust.size}"
    t := t.check (partition comps == w)
      s!"components: sccsOf {comps.size} vs wired {w.size}"
    let repsOk := wired.blocks.toList.all fun (lo, s) =>
      s.contains lo && s.toList.all fun n => wired.lowLinks.get? n == some lo
    t := t.check repsOk "components: a representative is not a member of its block"
    t := t.check (wired.blockRefs.size == wired.blocks.size)
      s!"components: {wired.blockRefs.size} blockRefs for {wired.blocks.size} blocks"
  | .error e, _ => t := t.check false s!"wired condensation: {e}"
  | _, none => t := t.check false "sccsOf: out of fuel"

  -- 2, 3. classes and nested order per condensed component
  let mut nClasses := 0
  let mut nNested := 0
  let mut nCollapsed := 0
  let mut nMulti := 0
  let mut nPermMoved := 0
  let mut nTodayDiffers := 0
  let mut nPermMovedToday := 0
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
        let probe ← Ix.AuxGen.expandNestedBlock reps aliasToRep true
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
      -- non-equal cache hit inside today's sort
      match sortClasses Rules.today addr? cs.toList, sortClasses todayFixed addr? cs.toList with
      | .ok (off, st), .ok (on, _) =>
        nPortFix := nPortFix + 1
        t := t.check (classNames off == classNames on)
          s!"port fixes {namePretty lo}: {pretty (classNames off)} off vs {pretty (classNames on)} on"
        t := t.check (st.hazards == 0)
          s!"port fixes {namePretty lo}: {st.hazards} reversed non-equal cache hits today"
      | .error e, _ | _, .error e => t := t.check false s!"port fixes {namePretty lo}: {e}"
      if let some x := auxX then
        match structuralAuxClasses Rules.today addr? x, structuralAuxClasses todayFixed addr? x with
        | .ok off, .ok on =>
          nPortFixAux := nPortFixAux + 1
          t := t.check (classNames off == classNames on)
            s!"port fixes, auxiliaries of {namePretty lo}: {pretty (classNames off)} off vs \
              {pretty (classNames on)} on"
        | .error e, _ | _, .error e => t := t.check false s!"port fixes, auxiliaries of {namePretty lo}: {e}"
      match sortClasses Rules.compiler addr? cs.toList with
      | .error e => t := t.check false s!"sortClasses {namePretty lo}: {e}"
      | .ok (mine, _) =>
        nClasses := nClasses + 1
        if classes.any (·.size > 1) then nCollapsed := nCollapsed + 1
        if classes.size > 1 then nMulti := nMulti + 1
        -- the order moves of A2-order's level rule: today's classes against
        -- the wired ones (measured; the census predicts none)
        match sortClasses Rules.today addr? cs.toList with
        | .ok (a, _) =>
          if classNames a != classes then nTodayDiffers := nTodayDiffers + 1
          t := t.check (nameSorted (classNames a))
            s!"representative today {namePretty lo}: {pretty (classNames a)}"
        | .error e => t := t.check false s!"sortClasses today {namePretty lo}: {e}"
        t := t.check (nameSorted (classNames mine))
          s!"representative compiler {namePretty lo}: {pretty (classNames mine)}"
        t := t.check (classNames mine == classes)
          s!"classes {namePretty lo}: {pretty (classNames mine)} vs {pretty classes}"
        if let some (nCanon, perm) := nestedOut then
          let originalAll : Array Ix.Name := Id.run do
            for c in cs do
              if let .indc i := c then return i.all
            return #[]
          match componentNested Rules.compiler cenvRefC originalAll classes with
          | .error e => t := t.check false s!"nested {namePretty lo}: {e}"
          | .ok none => t := t.check false s!"nested {namePretty lo}: none, compiler has {perm}"
          | .ok (some n) =>
            nNested := nNested + 1
            if perm.zipIdx.any (fun (p, j) => p != Ix.AuxGen.PERM_OUT_OF_SCC && p != j) then
              nPermMoved := nPermMoved + 1
            -- today's structural order, for the count of blocks it moved
            if let .ok (some n0) := componentNested Rules.today cenvRef originalAll classes then
              if n0.perm.zipIdx.any (fun (p, j) => p.isSome && p != some j) then
                nPermMovedToday := nPermMovedToday + 1
            let permMine := n.perm.map fun
              | some i => i
              | none => Ix.AuxGen.PERM_OUT_OF_SCC
            t := t.check (permMine == perm && n.canonClasses.size == nCanon)
              s!"nested {namePretty lo}: perm {permMine} / {n.canonClasses.size} vs {perm} / {nCanon}"
  IO.println s!"[canon-pass1] compared {nClasses} components ({nMulti} with several classes, \
    {nCollapsed} with a collapse; today's rules differ on {nTodayDiffers}), {nNested} nested \
    ({nPermMoved} with a moved auxiliary under discovery order, {nPermMovedToday} under today's \
    structural order); port fixes neutral on {nPortFix} components and {nPortFixAux} auxiliary sorts"

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
      match expandSource rawEnv .lean v.all with
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
    let fenv := Env.ofSource { source := { consts }, addr? := fun _ => none }
    for nm in [`CanonSiblingNest.T, `CanonSiblingNest.F, `CanonSiblingNest.B] do
      let n := Ix.Name.fromLeanName nm
      let some (.inductInfo v) := consts.get? n | t := t.check false s!"sibling {nm}: missing"; continue
      let leanX := expandSource { consts } .lean v.all
      let compX := expandSource { consts } .compiler v.all
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
