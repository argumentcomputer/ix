import Compilatrix.Own.Plain.Check
import Compilatrix.Own.Plain.Semantics

/-! Bounded compiled controls with independently written complete values,
cell counts, alias identities, source-clock thresholds and release oracles.
No compiler/corpus/fixture generator is imported by this executable suite. -/

namespace CompilatrixTests.Own.Plain.Runtime
open Compilatrix
open Compilatrix.Own.Plain

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
  IO.println s!"plain ownership runtime: 9 complete-value cases, {clockCases} clock controls, alias counts and final release passed"

end CompilatrixTests.Own.Plain.Runtime
