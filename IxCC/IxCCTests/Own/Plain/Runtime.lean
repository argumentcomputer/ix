import IxCC.Own.Plain.Check
import IxCC.Own.Plain.Semantics

/-! Bounded compiled controls with independently written complete values,
cell counts, alias identities, source-clock thresholds and release oracles.
No compiler/corpus/fixture generator is imported by this executable suite. -/

namespace IxCCTests.Own.Plain.Runtime
open IxCC
open IxCC.Own.Plain

private def leafInfo : Fir.CtorInfo :=
  { key := .src 830, tag := 0, nobj := 1, fieldKinds := [.shared] }
private def pairInfo : Fir.CtorInfo :=
  { key := .src 831, tag := 1, nobj := 2, fieldKinds := [.shared, .shared] }

private def sharing : Fir.Code :=
  .bind 1 (.ctor leafInfo [.var 0])
    (.bind 2 (.ctor pairInfo [.var 1, .var 1])
      (.bind 3 (.call 1 [.var 2]) (.ret (.var 3))))

private def identityJoin : Fir.Code :=
  .jp 0 [1] false (.ret (.var 1)) (.jmp 0 [.var 0])

private def projected : Fir.Code :=
  .bind 1 (.call 0 [.var 0]) (.bind 2 (.proj 1 pairInfo.key 0) (.ret (.var 2)))

private def countdown : Fir.Code :=
  .jp 0 [1] true
    (.case 1 [
      .mk (.src 832) (.ret (.lit (.nat 0))),
      .mk (.src 833) (.bind 2 (.proj 1 (.src 833) 0) (.jmp 0 [.var 2]))] none)
    (.jmp 0 [.var 0])

private def source : Fir.Program :=
  { funs := Src.NatMap.ofDense [
      { key := .const 830 [], params := [(0, .tobj)], body := sharing },
      { key := .const 831 [], params := [(0, .tobj)], body := identityJoin },
      { key := .const 832 [], params := [(0, .tobj)], body := projected },
      { key := .const 833 [], params := [(0, .tobj)], body := countdown }]
    size := 4, exports := [0, 1, 2, 3]
    ctors := [
      { key := leafInfo.key, tag := 0, arity := 1 },
      { key := pairInfo.key, tag := 1, arity := 2 },
      { key := .src 832, tag := 0, arity := 0 },
      { key := .src 833, tag := 1, arity := 1 }]
    known := { natZero := some (.src 832), natSucc := some (.src 833) } }

private def expect (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def nilInfo : Fir.CtorInfo :=
  { key := .src 834, tag := 0, nobj := 0, fieldKinds := [] }
private def consInfo : Fir.CtorInfo :=
  { key := .src 835, tag := 1, nobj := 2, fieldKinds := [.shared, .shared] }

-- `buildList (1 n : Nat) (! acc : List Nat) : ! List Nat`
private def buildListFun : Fir.Fun :=
  { key := .const 840 [],
    params := [(0, .tobj), (1, .tobj)],
    result := .unique,
    contracts := [.linear, { value := .unique }],
    body := .case 0
      [ .mk (.src 832) (.ret (.var 1)),
        .mk (.src 833)
          (.bind 2 (.proj 0 (.src 833) 0)
            (.bind 3 (.ctor consInfo [.var 2, .var 1])
              (.tcall 0 [.var 2, .var 3]))) ]
      none }

-- `lenErased (0 α) (~ xs : List α) : Nat`
private def lenErasedFun : Fir.Fun :=
  { key := .const 841 [],
    params := [(0, .tobj), (1, .tobj)],
    contracts := [.erased, { value := .localShared }],
    body := .case 1
      [ .mk nilInfo.key (.ret (.lit (.nat 0))),
        .mk consInfo.key
          (.bind 2 (.proj 1 consInfo.key 1)
            (.bind 3 (.call 1 [.erased, .var 2])
              (.bind 4 (.prim .natAdd [.var 3, .lit (.nat 1)])
                (.ret (.var 4))))) ]
      none }

-- `linCons (1 xs : List Nat) : List Nat`
private def linConsFun : Fir.Fun :=
  { key := .const 842 [],
    params := [(0, .tobj)],
    contracts := [.linear],
    body := .bind 1 (.arg (.lit (.nat 42)))
      (.bind 2 (.ctor consInfo [.var 1, .var 0])
        (.ret (.var 2))) }

-- `affHead (& xs : List Nat) : Nat`
private def affHeadFun : Fir.Fun :=
  { key := .const 843 [],
    params := [(0, .tobj)],
    contracts := [.affine],
    body := .case 0
      [ .mk nilInfo.key (.ret (.lit (.nat 0))),
        .mk consInfo.key (.bind 1 (.proj 0 consInfo.key 0) (.ret (.var 1))) ]
      none }

-- `borrowLen (~ xs : List Nat) : ~ Nat` with `let borrow (~ v) := xs`
private def borrowLenFun : Fir.Fun :=
  { key := .const 844 [],
    params := [(0, .tobj)],
    result := .localShared,
    contracts := [{ value := .localShared }],
    letContracts := [(1, Ixon.V3.LetContract.borrow true)],
    body := .bind 1 (.arg (.var 0))
      (.jp 0 [2, 3] true
        (.case 2
          [ .mk nilInfo.key (.ret (.var 3)),
            .mk consInfo.key
              (.bind 4 (.proj 2 consInfo.key 1)
                (.bind 5 (.prim .natAdd [.var 3, .lit (.nat 1)])
                  (.jmp 0 [.var 4, .var 5]))) ]
          none)
        (.jmp 0 [.var 1, .lit (.nat 0)])) }

-- `revUnique (! xs : List Nat) (! acc : List Nat) : ! List Nat`
private def revUniqueFun : Fir.Fun :=
  { key := .const 845 [],
    params := [(0, .tobj), (1, .tobj)],
    result := .unique,
    contracts := [{ value := .unique }, { value := .unique }],
    body := .case 0
      [ .mk nilInfo.key (.ret (.var 1)),
        .mk consInfo.key
          (.bind 2 (.proj 0 consInfo.key 0)
            (.bind 3 (.proj 0 consInfo.key 1)
              (.bind 4 (.ctor consInfo [.var 2, .var 1])
                (.tcall 5 [.var 3, .var 4])))) ]
      none }

-- `entry (n : Nat) : Nat` exercising all 6 annotated list functions
private def contractEntryFun : Fir.Fun :=
  { key := .const 846 [],
    params := [(0, .tobj)],
    body := .bind 1 (.ctor nilInfo [])
      (.bind 2 (.call 0 [.var 0, .var 1])
        (.bind 3 (.call 5 [.var 2, .var 1])
          (.bind 4 (.call 2 [.var 3])
            (.bind 5 (.call 1 [.erased, .var 4])
              (.bind 6 (.call 3 [.var 4])
                (.bind 7 (.call 4 [.var 4])
                  (.bind 8 (.prim .natAdd [.var 5, .var 6])
                    (.bind 9 (.prim .natAdd [.var 8, .var 7])
                      (.ret (.var 9)))))))))) }

private def contractListSource : Fir.Program :=
  { funs := Src.NatMap.ofDense [
      buildListFun, lenErasedFun, linConsFun, affHeadFun,
      borrowLenFun, revUniqueFun, contractEntryFun],
    size := 7,
    exports := [6],
    ctors := [
      { key := .src 832, tag := 0, arity := 0 },
      { key := .src 833, tag := 1, arity := 1 },
      { key := nilInfo.key, tag := 0, arity := 0 },
      { key := consInfo.key, tag := 1, arity := 2 } ],
    known := { natZero := some (.src 832), natSucc := some (.src 833) } }

private def contractListManySource : Fir.Program :=
  { contractListSource with
    funs := contractListSource.funs.insert 5 { revUniqueFun with result := .shared, contracts := [.many, .many] } }

private def expectedLeaf (seed : Nat) : Fir.Val := .ctor leafInfo [.lit (.nat seed)]
private def expectedPair (seed : Nat) : Fir.Val :=
  .ctor pairInfo [expectedLeaf seed, expectedLeaf seed]

private def sameOutcome : Sem.Result Fir.Val → Sem.Result (Own.RVal × Own.Heap) → Bool
  | .ok expected, .ok (v, heap) => heap.value? v == some expected
  | .timeout, .timeout | .trap, .trap | .stuck, .stuck => true
  | .resource x, .resource y => decide (x = y)
  | _, _ => false

private def returned (P : Program) (f clock seed : Nat) (expected : Fir.Val) : IO (Own.RVal × Own.Heap) := do
  let sourceResult := Fir.evalCall source clock f [.lit (.nat seed)]
  expect (match sourceResult with | .ok value => value == expected | _ => false)
    s!"f{f}: independent source value at seed={seed}, clock={clock}"
  match evalCall P clock f [.lit (.nat seed)] {} with
  | .ok (v, heap) =>
    expect (heap.value? v == some expected) s!"f{f}: complete heap value at seed={seed}"
    return (v, heap)
  | outcome => throw (IO.userError s!"f{f}: unexpected target outcome {repr outcome}")

private def releaseOutput (label : String) (v : Own.RVal) (heap : Own.Heap) : IO Unit := do
  match Own.Rc.dropAll heap [v] with
  | none => throw (IO.userError s!"{label}: output release declined")
  | some released =>
    expect (released.size == heap.size) s!"{label}: release changed address-space size"
    expect (released.cells.all fun cell => cell == .dead) s!"{label}: a live cell leaked after output release"
    match v with
    | .loc _ => expect ((Own.Rc.dropAll released [v]).isNone) s!"{label}: double release was accepted"
    | _ => pure ()

def run : IO Unit := do
  let canonical := Program.canonical source
  let candidate := canonical.bodies
  expect (checkPlainMap source candidate) "complete canonical map rejected"
  expect (!checkPlainMap source (candidate.insert 1 .trap)) "changed callee accepted"
  -- Execute the checked candidate itself, keeping the source record fixed.
  let program : Program := { source, bodies := candidate }
  let mut clockCases := 0
  for seed in [0, 7, 101] do
    let (pair, heap) ← returned program 0 8 seed (expectedPair seed)
    expect (pair == .loc 1 && heap.size == 2) "shared output root/heap size changed"
    match heap.cell? 0, heap.cell? 1 with
    | some (.live 2 .dyn leaf), some (.live 1 .dyn parent) =>
      expect (leaf.fields == [.lit (.nat seed)]) "shared leaf payload changed"
      expect (parent.fields == [.loc 0, .loc 0]) "shared field identities were copied or lost"
    | _, _ => throw (IO.userError "shared output counts must be leaf=2,parent=1")
    releaseOutput "shared pair" pair heap
    let (leaf, projectedHeap) ← returned program 2 8 seed (expectedLeaf seed)
    expect (leaf == .loc 0 && projectedHeap.size == 2) "projected output root/heap size changed"
    match projectedHeap.cell? 0, projectedHeap.cell? 1 with
    | some (.live 1 .dyn _), some .dead => pure ()
    | _, _ => throw (IO.userError "projected alias must retain leaf=1 and release its parent")
    releaseOutput "projected leaf" leaf projectedHeap
    let (value, joinedHeap) ← returned program 1 1 seed (.lit (.nat seed))
    expect joinedHeap.cells.isEmpty "first join allocated unexpectedly"
    releaseOutput "free first join" value joinedHeap
    for f in [0, 1, 2] do
      for clock in List.range 6 do
        expect (sameOutcome (Fir.evalCall source clock f [.lit (.nat seed)])
          (evalCall program clock f [.lit (.nat seed)] {})) s!"f{f}: clock mismatch at {clock}"
        clockCases := clockCases + 1
  for n in [0, 1, 4, 12] do
    for clock in List.range (n + 3) do
      let actual := evalCall program clock 3 [.lit (.nat n)] {}
      expect (sameOutcome (Fir.evalCall source clock 3 [.lit (.nat n)]) actual)
        s!"recursive join: source-clock mismatch n={n},clock={clock}"
      if clock < n + 1 then
        expect (actual == .timeout) s!"recursive join failed to charge n={n},clock={clock}"
      else
        match actual with
        | .ok (value, heap) =>
          expect (heap.value? value == some (.lit (.nat 0)) && heap.cells.isEmpty)
            s!"recursive join: complete zero result n={n},clock={clock}"
          releaseOutput "recursive join" value heap
        | _ => throw (IO.userError s!"recursive join: expected success n={n},clock={clock}")
      clockCases := clockCases + 1
  -- Contract-annotated list suite (`0`, `1`, `&`, `~`, `let borrow`, `!` vs `.many`).
  let contractBodies := (Program.canonical contractListSource).bodies
  expect (!programDomain contractListSource) "annotated list suite unexpectedly passed narrow programDomain"
  expect (contractProgramDomain contractListSource) "contractProgramDomain rejected annotated list suite"
  expect (checkContractPlainMap contractListSource contractBodies) "checkContractPlainMap rejected canonical annotated list map"
  expect (!checkContractPlainMap contractListSource (contractBodies.insert 2 .trap)) "checkContractPlainMap accepted corrupted callee"
  expect (selectRcPolicy contractListSource == .zeroRc) "selectRcPolicy failed to select .zeroRc for fully annotated list suite"
  expect (contractProgramDomain contractListManySource) "contractProgramDomain rejected mixed list suite"
  expect (selectRcPolicy contractListManySource == .plainRc) "selectRcPolicy failed to select .plainRc when revMany is unannotated"
  let contractProg : Program := { source := contractListSource, bodies := contractBodies }
  let mut contractRuns := 0
  for n in [0, 1, 3, 6] do
    let expectedVal : Fir.Val := .lit (.nat (2 * n + 44))
    let srcOut := Fir.evalCall contractListSource 128 6 [.lit (.nat n)]
    let ownOut := evalCall contractProg 128 6 [.lit (.nat n)] {}
    expect (sameOutcome srcOut ownOut) s!"contract list entry({n}): Fir/Own.Plain mismatch"
    match ownOut with
    | .ok (v, heap) =>
      expect (heap.value? v == some expectedVal) s!"contract list entry({n}): unexpected value"
      expect (heap.size == 2 * n + 1) s!"contract list entry({n}): expected {2 * n + 1} allocated cons cells, got {heap.size}"
      expect (heap.cells.all (· == .dead)) s!"contract list entry({n}): live cell leaked after consuming entry"
    | _ => throw (IO.userError s!"contract list entry({n}): expected .ok")
    for clock in List.range (4 * n + 12) do
      expect (sameOutcome (Fir.evalCall contractListSource clock 6 [.lit (.nat n)])
        (evalCall contractProg clock 6 [.lit (.nat n)] {}))
        s!"contract list entry({n}): clock mismatch at {clock}"
      contractRuns := contractRuns + 1
  IO.println s!"plain ownership runtime: 9 complete-value cases, {clockCases} clock controls, {contractRuns} contract-annotated list controls, alias counts and final release passed"

end IxCCTests.Own.Plain.Runtime
