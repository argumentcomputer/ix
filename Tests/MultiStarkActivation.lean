module

public import Tests.MultiStark

/-!
# Aggregate recursion activation audit

WP-D from `plans/aggregate-first-pipeline.md` asks for an input-shape audit of
the production lift, flat-join, and structural-join entrypoints before any
future static terminal circuit relies on an input-independent activation set.

This runner deliberately stays separate from the normal aggregate smoke suite.
It executes a deterministic 98-case matrix twice, compares every returned
per-circuit query count, and emits a Markdown report of circuits inactive in at
least one case. It does not add dummy calls; that policy remains deferred until
a static terminal is selected.
-/

public section

open Aiur

namespace Tests.MultiStark
namespace ActivationAudit

inductive Height where
  | short
  | tall
  deriving BEq, Repr

private def Height.label : Height → String
  | .short => "short"
  | .tall => "tall"

inductive ChildKind where
  | lift
  | flat
  | structural
  deriving BEq, Repr

private def ChildKind.label : ChildKind → String
  | .lift => "lift"
  | .flat => "flat"
  | .structural => "structural"

inductive Disposition where
  | discharge
  | carry
  deriving BEq, Repr

private def Disposition.label : Disposition → String
  | .discharge => "discharge"
  | .carry => "carry"

inductive Entrypoint where
  | lift
  | flat
  | structural
  deriving BEq, Repr

private def Entrypoint.label : Entrypoint → String
  | .lift => "lift"
  | .flat => "flat"
  | .structural => "structural"

private inductive JoinKind where
  | flat
  | structural

private def JoinKind.entrypoint : JoinKind → Entrypoint
  | .flat => .flat
  | .structural => .structural

private def JoinKind.label (kind : JoinKind) : String :=
  kind.entrypoint.label

/-- Cheap parameters are sufficient here: the audit studies which verifier
circuits execute, not soundness calibration or proof size. -/
private def auditFri : Aiur.FriParameters :=
  { logFinalPolyLen := 0, maxLogArity := 1, numQueries := 1,
    commitProofOfWorkBits := 0, queryProofOfWorkBits := 0 }

private def canonicalTree (leaves : Array Address) : Ix.AssumptionTree :=
  (Ix.AssumptionTree.canonical leaves).get!

private def digestSelectsShort (digest : Array Aiur.G) : Bool :=
  match digest[0]?, digest[1]? with
  | some a, some b => decide (a.n < b.n)
  | _, _ => false

private structure Indices where
  verify : Aiur.Bytecode.FunIdx
  lift : Aiur.Bytecode.FunIdx
  flat : Aiur.Bytecode.FunIdx
  structural : Aiur.Bytecode.FunIdx

private structure HeightConfig where
  height : Height
  fakeIxvmVk : ByteArray
  allowed : ByteArray
  probeRows : Nat

/-- Find a tiny fake IxVM key whose own digest and resulting allowed-blob
digest select the same branch of `activation_vary_height`. The search has
roughly 1/4 success probability per candidate for either requested branch. -/
private def findFakeIxvmVk (childVk : ByteArray) (indices : Indices)
    (height : Height) : Except String ByteArray :=
  let wantShort := height == .short
  let candidate? := (Array.range 4096).find? fun n =>
    let candidate : ByteArray := ⟨Tests.MultiStark.u64le n⟩
    let allowed := MultiStark.allowedBlob candidate indices.verify childVk
      indices.lift indices.flat indices.structural
    digestSelectsShort (MultiStark.digestGs candidate) == wantShort &&
      digestSelectsShort (MultiStark.digestGs allowed) == wantShort
  match candidate? with
  | some n => .ok ⟨Tests.MultiStark.u64le n⟩
  | none => .error s!"activation audit: no {height.label} digest selector found"

private def heightProbeRows (compiled : Aiur.CompiledToplevel)
    (verifyIdx probeIdx : Aiur.Bytecode.FunIdx) (fakeIxvmVk : ByteArray) :
    Except String Nat := do
  let (_, _, counts) ← compiled.bytecode.execute verifyIdx
    (MultiStark.digestGs fakeIxvmVk) default
  let some count := counts[probeIdx]?
    | throw s!"activation audit: missing height-probe query count {probeIdx}"
  pure count.uniqueRows

private def prepareHeightConfig (compiled : Aiur.CompiledToplevel)
    (childVk : ByteArray) (indices : Indices) (probeIdx : Aiur.Bytecode.FunIdx)
    (height : Height) : Except String HeightConfig := do
  let fakeIxvmVk ← findFakeIxvmVk childVk indices height
  let allowed := MultiStark.allowedBlob fakeIxvmVk indices.verify childVk
    indices.lift indices.flat indices.structural
  let probeRows ← heightProbeRows compiled indices.verify probeIdx fakeIxvmVk
  pure { height, fakeIxvmVk, allowed, probeRows }

private structure PreparedChild where
  proofBytes : ByteArray
  outerClaimsBytes : ByteArray
  preimages : Array ByteArray

private def prepareChild (system : Aiur.AiurSystem) (indices : Indices)
    (config : HeightConfig) (kind : ChildKind)
    (statement : MultiStark.CheckEnvTrees) : Except String PreparedChild := do
  let claimBytes := Ix.Claim.ser statement.claim
  match kind with
  | .lift =>
    let innerClaim := Aiur.buildClaim indices.verify
      (MultiStark.digestGs claimBytes) #[]
    let innerClaimsBytes := MultiStark.serializeClaims #[innerClaim]
    let input := MultiStark.verifierPubInput config.fakeIxvmVk innerClaimsBytes
    let (outer, proof, _) := system.prove indices.lift input default
    let adviceBytes ← system.proofToAdviceBytes outer proof
    pure ({
      proofBytes := adviceBytes
      outerClaimsBytes := MultiStark.serializeClaims #[outer]
      preimages := #[innerClaimsBytes, claimBytes]
    } : PreparedChild)
  | .flat | .structural =>
    let idx := match kind with
      | .flat => indices.flat
      | .structural => indices.structural
      | .lift => unreachable!
    let input := MultiStark.joinPubInput config.allowed claimBytes
    let (outer, proof, _) := system.prove idx input default
    let adviceBytes ← system.proofToAdviceBytes outer proof
    pure ({
      proofBytes := adviceBytes
      outerClaimsBytes := MultiStark.serializeClaims #[outer]
      preimages := #[claimBytes]
    } : PreparedChild)

private structure JoinCase where
  label : String
  allowed : ByteArray
  left : MultiStark.CheckEnvTrees
  right : MultiStark.CheckEnvTrees
  leftChild : PreparedChild
  rightChild : PreparedChild

private def assumptionLabel (present : Bool) : String :=
  if present then "some" else "none"

private def selectStatement (withoutAsm discharge carry :
    MultiStark.CheckEnvTrees) (present : Bool)
    (disposition : Disposition) : MultiStark.CheckEnvTrees :=
  if !present then withoutAsm
  else match disposition with
    | .discharge => discharge
    | .carry => carry

/-- Build the 48 join inputs shared by the flat and structural entrypoints:

`2 heights × 2 dispositions × 2 left-asm shapes × 2 right-asm shapes
 × 3 left-child kinds`.

The right child remains a lift. Both child positions call the same decoder, so
varying one side covers all three decoder arms while retaining a mixed-shape
case for the flat and structural child kinds. -/
private def prepareJoinCases (system : Aiur.AiurSystem) (indices : Indices)
    (configs : Array HeightConfig) : Except String (Array JoinCase) := do
  let a := Address.blake3 "activation-subject-left".toUTF8
  let b := Address.blake3 "activation-subject-right".toUTF8
  let c := Address.blake3 "activation-carry-left".toUTF8
  let d := Address.blake3 "activation-carry-right".toUTF8
  let leftSubjects := canonicalTree #[a]
  let rightSubjects := canonicalTree #[b]
  let leftNone : MultiStark.CheckEnvTrees :=
    { subjects := leftSubjects, assumptions := none }
  let leftDischarge : MultiStark.CheckEnvTrees :=
    { subjects := leftSubjects, assumptions := some (canonicalTree #[b]) }
  let leftCarry : MultiStark.CheckEnvTrees :=
    { subjects := leftSubjects, assumptions := some (canonicalTree #[c]) }
  let rightNone : MultiStark.CheckEnvTrees :=
    { subjects := rightSubjects, assumptions := none }
  let rightDischarge : MultiStark.CheckEnvTrees :=
    { subjects := rightSubjects, assumptions := some (canonicalTree #[a]) }
  let rightCarry : MultiStark.CheckEnvTrees :=
    { subjects := rightSubjects, assumptions := some (canonicalTree #[d]) }
  let mut cases : Array JoinCase := #[]
  for config in configs do
    for disposition in #[Disposition.discharge, .carry] do
      for leftAsm in #[false, true] do
        for rightAsm in #[false, true] do
          let left := selectStatement leftNone leftDischarge leftCarry
            leftAsm disposition
          let right := selectStatement rightNone rightDischarge rightCarry
            rightAsm disposition
          let rightChild ← prepareChild system indices config .lift right
          for childKind in #[ChildKind.lift, .flat, .structural] do
            let leftChild ← prepareChild system indices config childKind left
            cases := cases.push {
              label := s!"height={config.height.label},left-asm={assumptionLabel leftAsm},\
                right-asm={assumptionLabel rightAsm},disposition={disposition.label},\
                left-child={childKind.label},right-child=lift"
              allowed := config.allowed
              left
              right
              leftChild
              rightChild
            }
  return cases

private structure Sample where
  label : String
  entrypoint : Entrypoint
  queryCounts : Array Aiur.QueryCount

private def runLift (compiled : Aiur.CompiledToplevel)
    (childSystem : Aiur.AiurSystem) (childVk : ByteArray) (indices : Indices)
    (productionLiftIdx : Aiur.Bytecode.FunIdx) (config : HeightConfig) :
    Except String Sample := do
  let input := MultiStark.digestGs config.fakeIxvmVk
  let (innerClaim, proof, _) := childSystem.prove indices.verify input default
  let proofBytes ← childSystem.proofToAdviceBytes innerClaim proof
  let claimBytes := MultiStark.serializeClaims #[innerClaim]
  let pubInput := MultiStark.verifierPubInput childVk claimBytes
  let (_, queryCounts) ← compiled.bytecode.executeMultiStark productionLiftIdx
    pubInput proofBytes childVk claimBytes
  pure {
    label := s!"lift/height={config.height.label}"
    entrypoint := .lift
    queryCounts
  }

private def runJoinWithVk (compiled : Aiur.CompiledToplevel)
    (childVk : ByteArray) (flatIdx structuralIdx : Aiur.Bytecode.FunIdx)
    (kind : JoinKind) (case : JoinCase) : Except String Sample := do
  let output := match kind with
    | .flat => case.left.join case.right
    | .structural => case.left.joinStructural case.right
  let idx := match kind with
    | .flat => flatIdx
    | .structural => structuralIdx
  let trees := match kind with
    | .flat => MultiStark.CheckEnvTrees.adviceTrees case.left case.right output
    | .structural =>
      MultiStark.CheckEnvTrees.structuralAdviceTrees case.left case.right output
  let paths := match kind with
    | .flat => #[]
    | .structural =>
      MultiStark.CheckEnvTrees.structuralPathAdvice case.left case.right output
  let outputBytes := Ix.Claim.ser output.claim
  let pubInput := MultiStark.joinPubInput case.allowed outputBytes
  let preimagesBlob := MultiStark.joinPreimagesBlob
    (case.leftChild.preimages ++ case.rightChild.preimages)
  let (_, queryCounts) ← match compiled.bytecode.executeMultiStarkJoin idx
      pubInput case.leftChild.proofBytes case.rightChild.proofBytes childVk
      case.leftChild.outerClaimsBytes case.rightChild.outerClaimsBytes outputBytes
      case.allowed preimagesBlob (MultiStark.joinTreesBlob trees)
      (MultiStark.joinPathsBlob paths) with
    | .ok result => pure result
    | .error e => throw s!"{kind.label}/{case.label}: {e}"
  pure {
    label := s!"{kind.label}/{case.label}"
    entrypoint := kind.entrypoint
    queryCounts
  }

private def collect (compiled : Aiur.CompiledToplevel)
    (childSystem : Aiur.AiurSystem) (childVk : ByteArray) (indices : Indices)
    (productionLiftIdx flatIdx structuralIdx : Aiur.Bytecode.FunIdx)
    (configs : Array HeightConfig) (cases : Array JoinCase) :
    Except String (Array Sample) := do
  let mut samples : Array Sample := #[]
  for config in configs do
    samples := samples.push (← runLift compiled childSystem childVk indices
      productionLiftIdx config)
  for case in cases do
    samples := samples.push (← runJoinWithVk compiled childVk flatIdx
      structuralIdx .flat case)
  for case in cases do
    samples := samples.push (← runJoinWithVk compiled childVk flatIdx
      structuralIdx .structural case)
  pure samples

private def queryCountsEq (left right : Array Aiur.QueryCount) : Bool :=
  left.size == right.size && (left.zip right).all fun (a, b) =>
    a.uniqueRows == b.uniqueRows && a.totalHits == b.totalHits

private def samplesEq (left right : Array Sample) : Bool :=
  left.size == right.size && (left.zip right).all fun (a, b) =>
    a.label == b.label && a.entrypoint == b.entrypoint &&
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
  return result

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

private def entrySamples (samples : Array Sample) (entrypoint : Entrypoint) :
    Array Sample :=
  samples.filter fun sample => sample.entrypoint == entrypoint

private def Cell.render (c : Cell) : String :=
  if c.active == 0 then s!"0/{c.total}"
  else s!"{c.active}/{c.total} ({c.minActiveRows}..{c.maxActiveRows})"

private def activationSignature (samples : Array Sample) : Address :=
  let lines := samples.map fun sample =>
    let counts := sample.queryCounts.map fun count =>
      s!"{count.uniqueRows}/{count.totalHits}"
    sample.label ++ ":" ++ String.intercalate "," counts.toList
  Address.blake3 (String.intercalate "\n" lines.toList).toUTF8

private def report (compiled : Aiur.CompiledToplevel)
    (configs : Array HeightConfig) (samples : Array Sample) : String :=
  let catalog := circuits compiled
  let liftSamples := entrySamples samples .lift
  let flatSamples := entrySamples samples .flat
  let structuralSamples := entrySamples samples .structural
  let affected := catalog.filter fun circuit =>
    let summary := cell samples circuit.queryIdx
    summary.active < summary.total
  let alwaysActive := catalog.countP fun circuit =>
    let summary := cell samples circuit.queryIdx
    summary.active == summary.total
  let variableCount := catalog.countP fun circuit =>
    let summary := cell samples circuit.queryIdx
    summary.active != 0 && summary.active < summary.total
  let neverObserved := catalog.countP fun circuit =>
    (cell samples circuit.queryIdx).active == 0
  let configRows := configs.map fun config =>
    s!"| {config.height.label} | {config.probeRows} |"
  let circuitRows := affected.map fun circuit =>
    s!"| `{circuit.name}` | {(cell liftSamples circuit.queryIdx).render} | \
      {(cell flatSamples circuit.queryIdx).render} | \
      {(cell structuralSamples circuit.queryIdx).render} |"
  let introduction := #[]
    |>.push "# Aggregate recursion activation audit"
    |>.push ""
    |>.push s!"- Matrix signature: `{activationSignature samples}`"
    |>.push s!"- Accepted executions: {samples.size} \
      ({liftSamples.size} lift, {flatSamples.size} flat, \
      {structuralSamples.size} structural)"
    |>.push "- Join axes: assumption root `{none,some}` independently per side; \
      `{discharge,carry}`; left child `{lift,flat,structural}` with a lift on \
      the right; and two child trace heights."
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
    |>.push "| Height | `activation_height_probe` unique rows |"
    |>.push "|---|---:|"
  let circuitHeader := (introduction ++ configRows)
    |>.push ""
    |>.push "## Circuits inactive in at least one audited shape"
    |>.push ""
    |>.push "| Circuit | Lift | Flat join | Structural join |"
    |>.push "|---|---:|---:|---:|"
  String.intercalate "\n" (circuitHeader ++ circuitRows).toList

def run : IO UInt32 := do
  IO.println "aggregate-activation (98-case matrix, two deterministic passes)…"
  let childCompiled ← match Tests.MultiStark.joinChildProgram.compile with
    | .error e => IO.eprintln s!"activation child compilation failed: {e}"; return 1
    | .ok compiled => pure compiled
  let childSystem := Aiur.AiurSystem.build childCompiled.bytecode
    Tests.MultiStark.recCommitParams auditFri
  let childVk := childSystem.vkBytes
  let some verifyIdx := childCompiled.getFuncIdx `fake_verify_claim | do
    IO.eprintln "activation audit: fake_verify_claim entrypoint not found"; return 1
  let some childLiftIdx := childCompiled.getFuncIdx `fake_lift | do
    IO.eprintln "activation audit: fake_lift entrypoint not found"; return 1
  let some childFlatIdx := childCompiled.getFuncIdx `fake_join | do
    IO.eprintln "activation audit: fake_join entrypoint not found"; return 1
  let some childStructuralIdx := childCompiled.getFuncIdx `fake_struct_join | do
    IO.eprintln "activation audit: fake_struct_join entrypoint not found"; return 1
  let some probeIdx := childCompiled.getFuncIdx `activation_height_probe | do
    IO.eprintln "activation audit: height probe not found"; return 1
  let indices : Indices := {
    verify := verifyIdx
    lift := childLiftIdx
    flat := childFlatIdx
    structural := childStructuralIdx
  }
  let short ← match prepareHeightConfig childCompiled childVk indices probeIdx .short with
    | .error e => IO.eprintln e; return 1
    | .ok config => pure config
  let tall ← match prepareHeightConfig childCompiled childVk indices probeIdx .tall with
    | .error e => IO.eprintln e; return 1
    | .ok config => pure config
  if short.probeRows >= tall.probeRows then
    IO.eprintln s!"activation audit: height controls did not vary the trace \
      ({short.probeRows} vs {tall.probeRows} rows)"
    return 1
  let configs := #[short, tall]
  let cases ← match prepareJoinCases childSystem indices configs with
    | .error e => IO.eprintln s!"activation audit input preparation failed: {e}"; return 1
    | .ok cases => pure cases
  if cases.size != 48 then
    IO.eprintln s!"activation audit: expected 48 join cases, built {cases.size}"
    return 1

  let top ← match MultiStark.multiStark with
    | .error e => IO.eprintln s!"activation toplevel merge failed: {e}"; return 1
    | .ok top => pure top
  let compiled ← match top.compile with
    | .error e => IO.eprintln s!"activation toplevel compilation failed: {e}"; return 1
    | .ok compiled => pure compiled
  let some productionLiftIdx := compiled.getFuncIdx `verify_multi_stark_proof | do
    IO.eprintln "activation audit: production lift entrypoint not found"; return 1
  let some flatIdx := compiled.getFuncIdx `join_two | do
    IO.eprintln "activation audit: flat join entrypoint not found"; return 1
  let some structuralIdx := compiled.getFuncIdx `join_two_structural | do
    IO.eprintln "activation audit: structural join entrypoint not found"; return 1

  let first ← match collect compiled childSystem childVk indices
      productionLiftIdx flatIdx structuralIdx configs cases with
    | .error e => IO.eprintln s!"activation audit pass 1 failed: {e}"; return 1
    | .ok samples => pure samples
  let second ← match collect compiled childSystem childVk indices
      productionLiftIdx flatIdx structuralIdx configs cases with
    | .error e => IO.eprintln s!"activation audit pass 2 failed: {e}"; return 1
    | .ok samples => pure samples
  if first.size != 98 then
    IO.eprintln s!"activation audit: expected 98 samples, collected {first.size}"
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

end Tests.MultiStark

end
