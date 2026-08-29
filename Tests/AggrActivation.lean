module

public import Tests.Aggr

/-!
# `ix_aggr` activation audit

M1-e replaces the pre-convergence lift/flat/structural-entrypoint audit with
an audit of the one production `ix_aggr` entrypoint and all ten verified shape
arms. The deterministic matrix crosses:

* two controlled child trace heights;
* wrap shapes 0–1;
* pair shapes 2–9;
* optional assumptions independently on the left and right; and
* assumptions that are either discharged by the other subject tree or carried
  into the output.

That produces 4 wrap executions plus 128 pair executions. The runner executes
the complete 132-case matrix twice through the generated native path, compares
every per-circuit query count, and emits a Markdown report. It records
activation only; dummy-call policy remains deferred until a static terminal is
selected.
-/

public section

open Aiur

namespace Tests.Aggr
namespace ActivationAudit

inductive Height where
  | short
  | tall
  deriving BEq, Repr

private def Height.label : Height → String
  | .short => "short"
  | .tall => "tall"

inductive ChildKind where
  | ixvm
  | aggr
  deriving BEq, Repr

private def ChildKind.label : ChildKind → String
  | .ixvm => "ixvm"
  | .aggr => "aggr"

private def ChildKind.shapeCode : ChildKind → Nat
  | .ixvm => 0
  | .aggr => 1

inductive Disposition where
  | discharge
  | carry
  deriving BEq, Repr

private def Disposition.label : Disposition → String
  | .discharge => "discharge"
  | .carry => "carry"

/-- Cheap parameters are sufficient here: the audit studies which verifier
circuits execute, not production soundness calibration or proof size. -/
private def auditFri : Aiur.FriParameters :=
  { logFinalPolyLen := 0, maxLogArity := 1, numQueries := 1,
    commitProofOfWorkBits := 0, queryProofOfWorkBits := 0 }

/-- The two fake child entrypoints have the exact public-claim layouts accepted
by `ix_aggr`. Both vary their trace height from the output-claim digest, letting
one statement fixture drive the same height through either child kind. -/
private def childProgram : Source.Toplevel := ⟦
  fn activation_height_probe(n: G) {
    match n {
      0 => (),
      _ => activation_height_probe(n - 1),
    }
  }

  fn activation_vary_height(digest: [G; 8]) {
    match u32_less_than(digest[0], digest[1]) {
      1 => activation_height_probe(1),
      _ => activation_height_probe(4),
    }
  }

  pub fn fake_verify_claim(digest: [G; 8]) {
    activation_vary_height(digest)
  }

  pub fn fake_aggr(allowed_digest: [G; 8], out_claim_digest: [G; 8]) {
    activation_vary_height(out_claim_digest);
    assert_eq!(load(store(allowed_digest[0])), allowed_digest[0]);
    ()
  }
⟧

private def canonicalTree (leaves : Array Address) : Ix.AssumptionTree :=
  (Ix.AssumptionTree.canonical leaves).get!

private def digestSelectsShort (digest : Array Aiur.G) : Bool :=
  match digest[0]?, digest[1]? with
  | some a, some b => decide (a.n < b.n)
  | _, _ => false

private structure Indices where
  verify : Aiur.Bytecode.FunIdx
  aggr : Aiur.Bytecode.FunIdx

private structure Fixture where
  height : Height
  salt : Nat
  leftNone : Aggr.CheckEnvTrees
  leftDischarge : Aggr.CheckEnvTrees
  leftCarry : Aggr.CheckEnvTrees
  rightNone : Aggr.CheckEnvTrees
  rightDischarge : Aggr.CheckEnvTrees
  rightCarry : Aggr.CheckEnvTrees

private def fixtureAt (height : Height) (salt : Nat) : Fixture :=
  let address (side : String) :=
    Address.blake3 (s!"ix-aggr-activation-{salt}-{side}").toUTF8
  let a := address "subject-left"
  let b := address "subject-right"
  let c := address "carry-left"
  let d := address "carry-right"
  let leftSubjects := canonicalTree #[a]
  let rightSubjects := canonicalTree #[b]
  {
    height
    salt
    leftNone := { subjects := leftSubjects, assumptions := none }
    leftDischarge := {
      subjects := leftSubjects, assumptions := some (canonicalTree #[b]) }
    leftCarry := {
      subjects := leftSubjects, assumptions := some (canonicalTree #[c]) }
    rightNone := { subjects := rightSubjects, assumptions := none }
    rightDischarge := {
      subjects := rightSubjects, assumptions := some (canonicalTree #[a]) }
    rightCarry := {
      subjects := rightSubjects, assumptions := some (canonicalTree #[d]) }
  }

private def Fixture.statements (fixture : Fixture) : Array Aggr.CheckEnvTrees :=
  #[fixture.leftNone, fixture.leftDischarge, fixture.leftCarry,
    fixture.rightNone, fixture.rightDischarge, fixture.rightCarry]

/-- Find six related statements whose claim digests all select the requested
height branch. The expected search is 64 salts; the generous bound keeps the
fixture deterministic without baking opaque addresses into the source. -/
private def findFixture (height : Height) : Except String Fixture := do
  let wantShort := height == .short
  let some salt := (Array.range 65536).find? fun salt =>
      let fixture := fixtureAt height salt
      fixture.statements.all fun statement =>
        digestSelectsShort (Aggr.digestGs (Ix.Claim.ser statement.claim)) ==
          wantShort
    | throw s!"activation audit: no {height.label} statement fixture found"
  pure (fixtureAt height salt)

private structure HeightConfig where
  fixture : Fixture
  probeRows : Nat

private def prepareHeightConfig (compiled : Aiur.CompiledToplevel)
    (indices : Indices) (probeIdx : Aiur.Bytecode.FunIdx) (height : Height) :
    Except String HeightConfig := do
  let fixture ← findFixture height
  let input := Aggr.digestGs (Ix.Claim.ser fixture.leftNone.claim)
  let (_, _, counts) ← compiled.bytecode.execute indices.verify input default
  let some count := counts[probeIdx]?
    | throw s!"activation audit: missing height-probe query count {probeIdx}"
  pure { fixture, probeRows := count.uniqueRows }

private def selectStatement (withoutAsm discharge carry : Aggr.CheckEnvTrees)
    (present : Bool) (disposition : Disposition) : Aggr.CheckEnvTrees :=
  if !present then withoutAsm
  else match disposition with
    | .discharge => discharge
    | .carry => carry

private def assumptionLabel (present : Bool) : String :=
  if present then "some" else "none"

private structure PreparedChild where
  proofAdviceBytes : ByteArray
  claimsBytes : ByteArray

private def prepareChild (ixvmSystem selfSystem : Aiur.AiurSystem)
    (indices : Indices) (allowed : ByteArray) (kind : ChildKind)
    (statement : Aggr.CheckEnvTrees) : Except String PreparedChild := do
  let claimBytes := Ix.Claim.ser statement.claim
  let (system, idx, input) := match kind with
    | .ixvm => (ixvmSystem, indices.verify, Aggr.digestGs claimBytes)
    | .aggr => (selfSystem, indices.aggr, Aggr.pubInput allowed claimBytes)
  let (outer, proof, _) := system.prove idx input default
  let proofAdviceBytes ← system.proofToAdviceBytes outer proof
  pure {
    proofAdviceBytes
    claimsBytes := MultiStark.serializeClaims #[outer]
  }

private structure PairShape where
  shape : Nat
  structural : Bool
  leftKind : ChildKind
  rightKind : ChildKind

private def pairShapes : Array PairShape := #[
  { shape := 2, structural := false, leftKind := .ixvm, rightKind := .ixvm },
  { shape := 3, structural := false, leftKind := .ixvm, rightKind := .aggr },
  { shape := 4, structural := false, leftKind := .aggr, rightKind := .ixvm },
  { shape := 5, structural := false, leftKind := .aggr, rightKind := .aggr },
  { shape := 6, structural := true, leftKind := .ixvm, rightKind := .ixvm },
  { shape := 7, structural := true, leftKind := .ixvm, rightKind := .aggr },
  { shape := 8, structural := true, leftKind := .aggr, rightKind := .ixvm },
  { shape := 9, structural := true, leftKind := .aggr, rightKind := .aggr }
]

private structure WrapCase where
  label : String
  shape : Nat
  statement : Aggr.CheckEnvTrees
  child : PreparedChild

private structure PairCase where
  label : String
  pair : PairShape
  left : Aggr.CheckEnvTrees
  right : Aggr.CheckEnvTrees
  leftChild : PreparedChild
  rightChild : PreparedChild

private def prepareWrapCases (ixvmSystem selfSystem : Aiur.AiurSystem)
    (indices : Indices) (allowed : ByteArray)
    (configs : Array HeightConfig) : Except String (Array WrapCase) := do
  let mut cases : Array WrapCase := #[]
  for config in configs do
    for kind in #[ChildKind.ixvm, .aggr] do
      let child ← prepareChild ixvmSystem selfSystem indices allowed kind
        config.fixture.leftNone
      cases := cases.push {
        label := s!"shape={kind.shapeCode},height={config.fixture.height.label},\
          child={kind.label}"
        shape := kind.shapeCode
        statement := config.fixture.leftNone
        child
      }
  pure cases

private def preparePairCases (ixvmSystem selfSystem : Aiur.AiurSystem)
    (indices : Indices) (allowed : ByteArray)
    (configs : Array HeightConfig) : Except String (Array PairCase) := do
  let mut cases : Array PairCase := #[]
  for config in configs do
    let fixture := config.fixture
    for disposition in #[Disposition.discharge, .carry] do
      for leftAsm in #[false, true] do
        for rightAsm in #[false, true] do
          let left := selectStatement fixture.leftNone fixture.leftDischarge
            fixture.leftCarry leftAsm disposition
          let right := selectStatement fixture.rightNone fixture.rightDischarge
            fixture.rightCarry rightAsm disposition
          for pair in pairShapes do
            let leftChild ← prepareChild ixvmSystem selfSystem indices allowed
              pair.leftKind left
            let rightChild ← prepareChild ixvmSystem selfSystem indices allowed
              pair.rightKind right
            cases := cases.push {
              label := s!"shape={pair.shape},height={fixture.height.label},\
                left-asm={assumptionLabel leftAsm},\
                right-asm={assumptionLabel rightAsm},\
                disposition={disposition.label},\
                children={pair.leftKind.label}+{pair.rightKind.label}"
              pair
              left
              right
              leftChild
              rightChild
            }
  pure cases

private structure Sample where
  label : String
  shape : Nat
  queryCounts : Array Aiur.QueryCount

private def runWrap (compiled : Aiur.CompiledToplevel)
    (idx : Aiur.Bytecode.FunIdx) (ixvmVk selfVk allowed : ByteArray)
    (case : WrapCase) : Except String Sample := do
  let claimBytes := Ix.Claim.ser case.statement.claim
  let (_, queryCounts) ← match compiled.bytecode.executeIxAggr idx
      (Aggr.pubInput allowed claimBytes) case.shape
      case.child.proofAdviceBytes ByteArray.empty ixvmVk selfVk
      case.child.claimsBytes ByteArray.empty claimBytes allowed
      (Aggr.preimagesBlob #[]) (Aggr.treesBlob #[]) (Aggr.pathsBlob #[]) with
    | .ok result => pure result
    | .error e => throw s!"{case.label}: {e}"
  pure { label := case.label, shape := case.shape, queryCounts }

private def runPair (compiled : Aiur.CompiledToplevel)
    (idx : Aiur.Bytecode.FunIdx) (ixvmVk selfVk allowed : ByteArray)
    (case : PairCase) : Except String Sample := do
  let output := if case.pair.structural then
    case.left.joinStructural case.right
  else
    case.left.join case.right
  let trees := if case.pair.structural then
    Aggr.CheckEnvTrees.structuralAdviceTrees case.left case.right output
  else
    Aggr.CheckEnvTrees.adviceTrees case.left case.right output
  let paths := if case.pair.structural then
    Aggr.CheckEnvTrees.structuralPathAdvice case.left case.right output
  else #[]
  let leftBytes := Ix.Claim.ser case.left.claim
  let rightBytes := Ix.Claim.ser case.right.claim
  let outputBytes := Ix.Claim.ser output.claim
  let (_, queryCounts) ← match compiled.bytecode.executeIxAggr idx
      (Aggr.pubInput allowed outputBytes) case.pair.shape
      case.leftChild.proofAdviceBytes case.rightChild.proofAdviceBytes
      ixvmVk selfVk case.leftChild.claimsBytes case.rightChild.claimsBytes
      outputBytes allowed (Aggr.preimagesBlob #[leftBytes, rightBytes])
      (Aggr.treesBlob trees) (Aggr.pathsBlob paths) with
    | .ok result => pure result
    | .error e => throw s!"{case.label}: {e}"
  pure { label := case.label, shape := case.pair.shape, queryCounts }

private def collect (compiled : Aiur.CompiledToplevel)
    (idx : Aiur.Bytecode.FunIdx) (ixvmVk selfVk allowed : ByteArray)
    (wrapCases : Array WrapCase) (pairCases : Array PairCase) :
    Except String (Array Sample) := do
  let mut samples : Array Sample := #[]
  for case in wrapCases do
    samples := samples.push (← runWrap compiled idx ixvmVk selfVk allowed case)
  for case in pairCases do
    samples := samples.push (← runPair compiled idx ixvmVk selfVk allowed case)
  pure samples

private def queryCountsEq (left right : Array Aiur.QueryCount) : Bool :=
  left.size == right.size && (left.zip right).all fun (a, b) =>
    a.uniqueRows == b.uniqueRows && a.totalHits == b.totalHits

private def samplesEq (left right : Array Sample) : Bool :=
  left.size == right.size && (left.zip right).all fun (a, b) =>
    a.label == b.label && a.shape == b.shape &&
      queryCountsEq a.queryCounts b.queryCounts

private structure Circuit where
  name : String
  queryIdx : Nat

private def circuits (compiled : Aiur.CompiledToplevel) : Array Circuit := Id.run do
  let reverseNames := compiled.nameMap.fold
    (init := ({} : Std.HashMap Aiur.Bytecode.FunIdx String))
    fun names global idx =>
      let name := toString global
      match names[idx]? with
      | none => names.insert idx name
      | some old => if compare name old == .lt then names.insert idx name else names
  let mut result : Array Circuit := #[]
  for (function, idx) in compiled.bytecode.functions.mapIdx
      fun idx function => (function, idx) do
    if function.constrained then
      result := result.push {
        name := reverseNames[idx]?.getD s!"fn[{idx}]"
        queryIdx := idx
      }
  let functionCount := compiled.bytecode.functions.size
  for (width, idx) in compiled.bytecode.memorySizes.mapIdx fun idx width =>
      (width, idx) do
    result := result.push {
      name := s!"memory[{width}]"
      queryIdx := functionCount + idx
    }
  pure result

private structure Cell where
  active : Nat
  total : Nat
  minActiveRows : Nat
  maxActiveRows : Nat

private def rowsAt (sample : Sample) (queryIdx : Nat) : Nat :=
  match sample.queryCounts[queryIdx]? with
  | some count => count.uniqueRows
  | none => 0

private def cell (samples : Array Sample) (queryIdx : Nat) : Cell :=
  let activeRows := samples.map (rowsAt · queryIdx) |>.filter (· != 0)
  let minActiveRows := match activeRows[0]? with
    | none => 0
    | some first => activeRows.foldl Nat.min first
  {
    active := activeRows.size
    total := samples.size
    minActiveRows
    maxActiveRows := activeRows.foldl Nat.max 0
  }

private def Cell.render (summary : Cell) : String :=
  if summary.active == 0 then s!"0/{summary.total}"
  else s!"{summary.active}/{summary.total} \
    ({summary.minActiveRows}..{summary.maxActiveRows})"

private def shapeSamples (samples : Array Sample) (shape : Nat) : Array Sample :=
  samples.filter fun sample => sample.shape == shape

private def activationSignature (samples : Array Sample) : Address :=
  let lines := samples.map fun sample =>
    let counts := sample.queryCounts.map fun count =>
      s!"{count.uniqueRows}/{count.totalHits}"
    sample.label ++ ":" ++ String.intercalate "," counts.toList
  Address.blake3 (String.intercalate "\n" lines.toList).toUTF8

private def report (compiled : Aiur.CompiledToplevel)
    (configs : Array HeightConfig) (samples : Array Sample) : String :=
  let catalog := circuits compiled
  let affected := catalog.filter fun circuit =>
    let summary := cell samples circuit.queryIdx
    summary.active < summary.total
  let alwaysActive := catalog.countP fun circuit =>
    (cell samples circuit.queryIdx).active == samples.size
  let variableCount := catalog.countP fun circuit =>
    let summary := cell samples circuit.queryIdx
    summary.active != 0 && summary.active < summary.total
  let neverObserved := catalog.countP fun circuit =>
    (cell samples circuit.queryIdx).active == 0
  let shapeCounts := (Array.range 10).map fun shape =>
    s!"shape {shape}: {(shapeSamples samples shape).size}"
  let configRows := configs.map fun config =>
    s!"| {config.fixture.height.label} | {config.fixture.salt} | \
      {config.probeRows} |"
  let tableHeader := "| Circuit | " ++
    String.intercalate " | " ((Array.range 10).map fun shape =>
      s!"Shape {shape}").toList ++ " |"
  let tableDivider := "|---|" ++
    String.intercalate "" ((Array.range 10).map fun _ => "---:|").toList
  let circuitRows := affected.map fun circuit =>
    let cells := (Array.range 10).map fun shape =>
      (cell (shapeSamples samples shape) circuit.queryIdx).render
    s!"| `{circuit.name}` | {String.intercalate " | " cells.toList} |"
  let introduction := #[]
    |>.push "# `ix_aggr` activation audit"
    |>.push ""
    |>.push s!"- Matrix signature: `{activationSignature samples}`"
    |>.push s!"- Accepted executions: {samples.size} \
      ({String.intercalate ", " shapeCounts.toList})"
    |>.push "- Axes: two child trace heights; both wrap shapes; every flat and \
      structural child-kind shape; assumption root `{none,some}` independently \
      per side; and `{discharge,carry}`."
    |>.push "- Counts are `active cases / total cases (min..max unique rows when active)`."
    |>.push "- Catalog covers constrained function circuits and memory circuits. \
      `Bytes1`/`Bytes2` are fixed-height preprocessed circuits and are not \
      represented in the execute FFI's query-count array."
    |>.push s!"- Catalog summary: {catalog.size} circuits; {alwaysActive} active \
      in every case; {variableCount} input-dependent; {neverObserved} never observed."
    |>.push "- Dummy calls remain deferred until a static terminal circuit is selected."
    |>.push ""
    |>.push "## Trace-height control"
    |>.push ""
    |>.push "| Height | Fixture salt | `activation_height_probe` unique rows |"
    |>.push "|---|---:|---:|"
  let circuitHeader := (introduction ++ configRows)
    |>.push ""
    |>.push "## Circuits inactive in at least one audited shape"
    |>.push ""
    |>.push tableHeader
    |>.push tableDivider
  String.intercalate "\n" (circuitHeader ++ circuitRows).toList

def run : IO UInt32 := do
  IO.println "aggregate-activation (132-case ix_aggr matrix, two deterministic passes)…"
  let childCompiled ← match childProgram.compile with
    | .error e => IO.eprintln s!"activation child compilation failed: {e}"; return 1
    | .ok compiled => pure compiled
  let some verifyIdx := childCompiled.getFuncIdx `fake_verify_claim | do
    IO.eprintln "activation audit: fake_verify_claim entrypoint not found"; return 1
  let some fakeAggrIdx := childCompiled.getFuncIdx `fake_aggr | do
    IO.eprintln "activation audit: fake_aggr entrypoint not found"; return 1
  let some probeIdx := childCompiled.getFuncIdx `activation_height_probe | do
    IO.eprintln "activation audit: height probe not found"; return 1
  let indices : Indices := { verify := verifyIdx, aggr := fakeAggrIdx }
  let ixvmSystem := Aiur.AiurSystem.build childCompiled.bytecode
    Tests.MultiStark.recCommitParams auditFri
  let selfSystem := Aiur.AiurSystem.build childCompiled.bytecode
    Tests.MultiStark.recCommitParams { auditFri with numQueries := 2 }
  let ixvmVk := ixvmSystem.vkBytes
  let selfVk := selfSystem.vkBytes
  let allowed := Aggr.allowedBlob ixvmVk verifyIdx selfVk fakeAggrIdx

  let short ← match prepareHeightConfig childCompiled indices probeIdx .short with
    | .error e => IO.eprintln e; return 1
    | .ok config => pure config
  let tall ← match prepareHeightConfig childCompiled indices probeIdx .tall with
    | .error e => IO.eprintln e; return 1
    | .ok config => pure config
  if short.probeRows >= tall.probeRows then
    IO.eprintln s!"activation audit: height controls did not vary the trace \
      ({short.probeRows} vs {tall.probeRows} rows)"
    return 1
  let configs := #[short, tall]
  let wrapCases ← match prepareWrapCases ixvmSystem selfSystem indices allowed configs with
    | .error e => IO.eprintln s!"activation wrap preparation failed: {e}"; return 1
    | .ok cases => pure cases
  let pairCases ← match preparePairCases ixvmSystem selfSystem indices allowed configs with
    | .error e => IO.eprintln s!"activation pair preparation failed: {e}"; return 1
    | .ok cases => pure cases
  if wrapCases.size != 4 || pairCases.size != 128 then
    IO.eprintln s!"activation audit: expected 4 wraps + 128 pairs, built \
      {wrapCases.size} + {pairCases.size}"
    return 1

  let top ← match Aggr.ixAggr with
    | .error e => IO.eprintln s!"activation toplevel merge failed: {e}"; return 1
    | .ok top => pure top
  let compiled ← match top.compile with
    | .error e => IO.eprintln s!"activation toplevel compilation failed: {e}"; return 1
    | .ok compiled => pure compiled
  let some ixAggrIdx := compiled.getFuncIdx `ix_aggr | do
    IO.eprintln "activation audit: ix_aggr entrypoint not found"; return 1

  let first ← match collect compiled ixAggrIdx ixvmVk selfVk allowed
      wrapCases pairCases with
    | .error e => IO.eprintln s!"activation audit pass 1 failed: {e}"; return 1
    | .ok samples => pure samples
  let second ← match collect compiled ixAggrIdx ixvmVk selfVk allowed
      wrapCases pairCases with
    | .error e => IO.eprintln s!"activation audit pass 2 failed: {e}"; return 1
    | .ok samples => pure samples
  if first.size != 132 then
    IO.eprintln s!"activation audit: expected 132 samples, collected {first.size}"
    return 1
  let expectedQueryCounts := compiled.bytecode.functions.size +
    compiled.bytecode.memorySizes.size
  if first.any fun sample => sample.queryCounts.size != expectedQueryCounts then
    IO.eprintln s!"activation audit: a sample returned the wrong query-count \
      cardinality (expected {expectedQueryCounts})"
    return 1
  if !samplesEq first second then
    IO.eprintln "activation audit: query-count matrix changed between passes"
    return 1
  IO.println (report compiled configs first)
  IO.println ""
  IO.println "[activation-audit] stable across two passes"
  return 0

end ActivationAudit

def activationAudit : IO UInt32 := ActivationAudit.run

end Tests.Aggr

end
