import Ix.EnvScope
import Ix.LeanExport
import Ix.Cert.Compile

/-! Semantic controls for the source-unit and family-check caches. The small
runner constructs its own environments and needs no fixture imports or FFI
test library. `Scripts/Performance/CompilerChecks.lean` shares the builders
for native scale measurements.
-/

namespace Tests.Ix.Compile.Performance

private def need (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def sourceDef (name : Lean.Name) (value : Lean.Expr := .sort .zero)
    (all : Option (List Lean.Name) := none) : Lean.Name × Lean.ConstantInfo :=
  (name, .defnInfo {
    name, levelParams := [], type := .sort (.succ .zero), value
    hints := .opaque, safety := .safe, all := all.getD [name] })

private def sourceAxiom (name : Lean.Name) : Lean.Name × Lean.ConstantInfo :=
  (name, .axiomInfo { name, levelParams := [], type := .sort (.succ .zero), isUnsafe := false })

private def sourceInductive (name : Lean.Name) (all ctors : List Lean.Name) :
    Lean.Name × Lean.ConstantInfo :=
  (name, .inductInfo {
    name, levelParams := [], type := .sort (.succ .zero)
    numParams := 0, numIndices := 0, all, ctors, numNested := 0,
    isRec := false, isUnsafe := false, isReflexive := false })

private def sourceConstructor (name owner : Lean.Name) : Lean.Name × Lean.ConstantInfo :=
  (name, .ctorInfo {
    name, levelParams := [], type := .const owner [], induct := owner
    cidx := 0, numParams := 0, numFields := 0, isUnsafe := false })

structure UnitFixture where
  env : Lean.Environment
  root : Lean.Name
  auxiliaries : Array Lean.Name
  dependencies : Array Lean.Name
  expected : List Lean.Name

/-- Every auxiliary has a separate dependency outside its owner's unit. -/
def unitFixture (count : Nat) : IO UnitFixture := do
  let root := `CompilerPerformance.unit
  let auxiliaries := (Array.range count).map fun i => root.str s!"eq_{i}"
  let dependencies := (Array.range count).map fun i => (`CompilerPerformance).str s!"dependency{i}"
  let mut constants := #[sourceDef root, sourceDef `CompilerPerformance.unrelated]
  for i in [:count] do
    constants := constants.push (sourceDef dependencies[i]!)
    constants := constants.push (sourceDef auxiliaries[i]! (.const dependencies[i]! []))
  return { env := ← _root_.Ix.LeanExport.environment constants, root, auxiliaries, dependencies
           expected := root :: auxiliaries.toList ++ dependencies.toList }

private def selectedNames (env : Lean.Environment) (seeds : List Lean.Name) : List Lean.Name :=
  (_root_.Ix.EnvScope.collectSelectedDeps env seeds).map (·.1)

private def unitChecks : IO Unit := do
  let data ← unitFixture 64
  let reference := (_root_.Ix.EnvScope.collectDeps data.env data.expected).map (·.1)
  let actual := selectedNames data.env [data.root]
  need "wide unit lost an auxiliary's independent dependency" (actual == reference)
  need "wide unit included unrelated declarations" (!actual.contains `CompilerPerformance.unrelated)
  need "selected closure is not idempotent" (selectedNames data.env actual == actual)
  need "auxiliary seeds changed the selected closure"
    (selectedNames data.env data.auxiliaries.toList == actual)
  need "seed order changed the selected closure"
    (selectedNames data.env data.auxiliaries.toList.reverse == actual)
  let index := _root_.Ix.EnvScope.unitIndex data.env.constants
  let expectedOrder := data.env.constants.toList.filterMap fun (name, _) =>
    if data.auxiliaries.contains name then some name else none
  need "unit index changed auxiliary order or omitted entries"
    (index.size == 1 && index.getD data.root #[] == expectedOrder.toArray)
  -- Neither malformed owner's `all` lists the owner itself. Starting from
  -- an auxiliary therefore reaches the roots only through unit expansion.
  let left := `MalformedUnit.left
  let right := `MalformedUnit.right
  let first := `MalformedUnit.shared
  let leftRoot := `MalformedUnit.leftRoot
  let rightRoot := `MalformedUnit.rightRoot
  let leftDependency := `MalformedUnit.leftDependency
  let rightDependency := `MalformedUnit.rightDependency
  let leftAux := left.str "eq_1"
  let rightAux := right.str "eq_1"
  let malformed ← _root_.Ix.LeanExport.environment #[
    sourceDef left (.sort .zero) (some [first, leftRoot]),
    sourceDef right (.sort .zero) (some [first, rightRoot]),
    sourceDef leftAux, sourceDef rightAux, sourceAxiom first,
    sourceDef leftRoot (.const leftDependency []),
    sourceDef rightRoot (.const rightDependency []),
    sourceDef leftDependency, sourceDef rightDependency]
  let expected := (_root_.Ix.EnvScope.collectDeps malformed
    [first, leftRoot, rightRoot, leftDependency, rightDependency, leftAux, rightAux]).map (·.1)
  need "malformed owner control does not share a first unit key"
    (_root_.Ix.EnvScope.unitKey malformed.constants left ==
      _root_.Ix.EnvScope.unitKey malformed.constants right)
  for seeds in [[leftAux], [rightAux], [leftAux, rightAux], [rightAux, leftAux]] do
    let closed := selectedNames malformed seeds
    need "owners with one unit key lost distinct root dependencies" (closed == expected)
    need "malformed unit closure is not idempotent" (selectedNames malformed closed == closed)

private def unitKeyChecks : IO Unit := do
  let root := `UnitKeys.root
  let ctor := `UnitKeys.root.ctor
  let empty := `UnitKeys.empty
  let constants := #[
    sourceInductive root [root] [ctor], sourceConstructor ctor root,
    sourceInductive empty [] [], sourceConstructor `UnitKeys.emptyCtor empty,
    sourceInductive `UnitKeys.malformed [`UnitKeys.missing, root] [],
    sourceConstructor `UnitKeys.malformedCtor `UnitKeys.malformed,
    sourceConstructor `UnitKeys.missingOwnerCtor `UnitKeys.missing,
    sourceConstructor `UnitKeys.wrongOwnerCtor `UnitKeys.ordinary,
    sourceDef `UnitKeys.ordinary,
    sourceDef `UnitKeys.emptyDefinition (.sort .zero) (some []),
    sourceAxiom `UnitKeys.axiom,
    (`UnitKeys.theorem, Lean.ConstantInfo.thmInfo {
      name := `UnitKeys.theorem, levelParams := [], type := .sort .zero,
      value := .sort .zero, all := [] }),
    (`UnitKeys.opaque, Lean.ConstantInfo.opaqueInfo {
      name := `UnitKeys.opaque, levelParams := [], type := .sort .zero,
      value := .sort .zero, isUnsafe := false, all := [] })]
  let env ← _root_.Ix.LeanExport.environment constants
  for name in `UnitKeys.absent :: (constants.map (·.1)).toList do
    need s!"unitKey differs from the first root for {name}"
      (_root_.Ix.EnvScope.unitKey env.constants name ==
        (_root_.Ix.EnvScope.unitRoots env.constants name).head?.getD name)

structure FamilyFixture where
  env : _root_.Ix.Environment
  blocks : _root_.Ix.CondensedBlocks
  root : _root_.Ix.Name
  constructors : Array _root_.Ix.Name
  members : _root_.Ix.Set _root_.Ix.Name

def familyFixture (count : Nat) : FamilyFixture := Id.run do
  let root := _root_.Ix.Name.fromLeanName `CompilerPerformance.Enum
  let constructors := (Array.range count).map (_root_.Ix.Name.mkNat root ·)
  let family : _root_.Ix.ConstantInfo := .inductInfo {
    cnst := { name := root, levelParams := #[], type := .mkSort (.mkSucc .mkZero) }
    numParams := 0, numIndices := 0, all := #[root], ctors := constructors,
    numNested := 0, isRec := false, isUnsafe := false, isReflexive := false }
  let mut env : _root_.Ix.Environment := { consts := ({} : _root_.Ix.Map _ _).insert root family }
  let mut members : _root_.Ix.Set _root_.Ix.Name := ({} : _root_.Ix.Set _).insert root
  for i in [:count] do
    let name := constructors[i]!
    let ctor : _root_.Ix.ConstantInfo := .ctorInfo {
      cnst := { name, levelParams := #[], type := .mkConst root #[] }
      induct := root, cidx := i, numParams := 0, numFields := 0, isUnsafe := false }
    env := { env with consts := env.consts.insert name ctor }
    members := members.insert name
  return {
    env, root, constructors, members
    blocks := {
      lowLinks := members.fold (fun map name => map.insert name root) {}
      blocks := ({} : _root_.Ix.Map _ _).insert root members
      blockRefs := ({} : _root_.Ix.Map _ _).insert root {} } }

/-- Deliberately call the unchanged per-member helper. Calling
`strayFamilyMemberWith` here would compare its csimp replacement to itself. -/
def familyReference (env : _root_.Ix.Environment) (blocks : _root_.Ix.CondensedBlocks)
    (recs : Std.HashMap Address (Array _root_.Ix.Name)) : Option (_root_.Ix.Name × _root_.Ix.Name) :=
  blocks.blocks.toList.findSome? fun (rep, all) =>
    (all.toList.find? fun name => !_root_.Ix.Cert.familyBlockOk env recs all name).map (rep, ·)

private def checkFind (label : String) (env : _root_.Ix.Environment)
    (members : _root_.Ix.Set _root_.Ix.Name) (names : List _root_.Ix.Name)
    (expected : Option _root_.Ix.Name) : IO Unit := do
  let reference := names.find? fun name => !_root_.Ix.Cert.familyBlockOk env {} members name
  let cached := (_root_.Ix.Cert.familyBlockFindCached env {} members names {}).val
  -- Ix.Name's BEq uses stored hashes. These comparisons must also distinguish
  -- the spelling of a colliding original member from its owning cache key.
  need s!"{label}: reference fixture has the wrong first failure" (decide (reference = expected))
  need s!"{label}: cache changed the exact first failure" (decide (cached = reference))

private def familyChecks : IO Unit := do
  for count in [0, 1] do
    let small := familyFixture count
    need "singleton family fast path changed the reference result"
      (decide (_root_.Ix.Cert.strayFamilyMemberWithCached small.env small.blocks {} =
        familyReference small.env small.blocks {}))
  let data := familyFixture 64
  checkFind "wide enum" data.env data.members (data.root :: data.constructors.toList) none
  need "wide enum wrapper was rejected"
    ((_root_.Ix.Cert.strayFamilyMemberWithCached data.env data.blocks {}).isNone)
  let first := data.constructors[0]!
  let second := data.constructors[1]!
  let last := data.constructors.back!
  let ordinary := _root_.Ix.Name.fromLeanName `CompilerPerformance.ordinary
  let missing := _root_.Ix.Name.fromLeanName `CompilerPerformance.missing
  let ordinaryInfo : _root_.Ix.ConstantInfo := .axiomInfo {
    cnst := { name := ordinary, levelParams := #[], type := .mkSort .mkZero }, isUnsafe := false }
  let env := { data.env with consts := data.env.consts.insert ordinary ordinaryInfo }
  let changeOwner (env : _root_.Ix.Environment) (name owner : _root_.Ix.Name) :=
    match env.consts.get? name with
    | some (.ctorInfo ctor) => { env with consts := env.consts.insert name (.ctorInfo { ctor with induct := owner }) }
    | _ => env
  let broken := changeOwner (changeOwner env first missing) second ordinary
  checkFind "missing constructor owner after a warm family hit" broken data.members
    [data.root, first, second] (some first)
  checkFind "wrong-kind constructor owner is the first failure" broken data.members
    [data.root, second, first] (some second)
  let recursor := _root_.Ix.Name.mkStr data.root "rec"
  let recursorInfo : _root_.Ix.ConstantInfo := .recInfo {
    cnst := { name := recursor, levelParams := #[], type := .mkSort .mkZero }
    all := #[data.root], numParams := 0, numIndices := 0, numMotives := 1
    numMinors := data.constructors.size, rules := #[], k := false, isUnsafe := false }
  let withRecursor := { env with consts := env.consts.insert recursor recursorInfo }
  checkFind "a recursor must not reuse its inductive's family-block answer" withRecursor data.members
    [data.root, recursor] (some recursor)
  let missingMember := data.members.erase last
  checkFind "missing family member reports the original constructor" env missingMember
    [ordinary, first, data.root] (some first)
  checkFind "extra family member" env (data.members.insert ordinary)
    [ordinary, second, first] (some second)
  let tampered := match env.consts.get? data.root with
    | some (.inductInfo family) =>
      let changed := _root_.Ix.ConstantInfo.inductInfo { family with ctors := family.ctors.pop }
      { env with consts := env.consts.insert data.root changed }
    | _ => env
  checkFind "tampered source family list" tampered data.members [ordinary, first, data.root] (some first)
  let aliasName : _root_.Ix.Name := .str .mkAnon "colliding-constructor" first.getHash
  need "name-hash collision fixture is not structurally distinct"
    (aliasName == first && !decide (aliasName = first))
  checkFind "hash alias keeps its exact failing spelling" env missingMember
    [ordinary, aliasName, first, data.root] (some aliasName)
  checkFind "hash alias preserves the reference membership semantics" env
    ((data.members.erase first).insert aliasName) [aliasName, first, data.root] none
  for source in [env, broken, tampered] do
    let reference := familyReference source data.blocks {}
    let cached := _root_.Ix.Cert.strayFamilyMemberWithCached source data.blocks {}
    need "block wrapper changed its first failing member" (decide (cached = reference))

def run : IO Unit := do
  unitChecks
  unitKeyChecks
  familyChecks
  IO.println "Compiler unit and family cache regressions PASS"

end Tests.Ix.Compile.Performance
