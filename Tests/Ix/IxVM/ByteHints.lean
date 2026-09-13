module

public import Ix.IxVM.Toplevel
public import Tests.Aiur.Common
public import Ix.Benchmark.Bench

/-!
The production u32 byte hint is constant-time, untrusted advice. Exercise
its real checking caller, including normalized zero, byte boundaries,
malformed in-range advice, rejected large inputs, and native proofs.
-/

public section

namespace Tests.Ix.IxVM.ByteHints

open Aiur LSpec

private def entries := ⟦
  pub fn u32_hint(x: G) -> (G, G, G, G) { #split_u32(x) }
  pub fn checked_u32(x: G) -> U64 {
    let n = klimbs_from_g(x);
    match x {
      0 =>
        assert_eq!(load(n), ListNode.Nil, "zero must stay normalized");
        [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
      _ =>
        let ListNode.Cons(limb, rest) = load(n);
        assert_eq!(load(rest), ListNode.Nil, "u32 must fit one limb");
        limb,
    }
  }
⟧

private def source : Except Global Source.Toplevel := do
  let vm ← IxVM.ixVMFull
  let vm ← vm.merge entries
  pure (vm.prune [`u32_hint, `checked_u32])

private def bytes (n width : Nat) : Array Aiur.G :=
  (Array.range width).map fun i => G.ofNat ((n / 256 ^ i) % 256)

private def boundaries : List AiurTestCase := Id.run do
  let mut cases := []
  for n in [0, 1, 255, 256, 65535, 65536, 16777215, 16777216, 4294967295] do
    cases := cases ++ [
      .interp `u32_hint #[G.ofNat n] (bytes n 4) s!"u32 hint {n}",
      .interp `checked_u32 #[G.ofNat n] (bytes n 8) s!"checked u32 {n}"]
  return cases

private def rejects (compiled : CompiledToplevel) (input : Array Aiur.G)
    (label : String) : TestSeq :=
  match compiled.getFuncIdx `checked_u32 with
  | none => test s!"{label}: entrypoint missing" false
  | some i => match compiled.bytecode.execute i input default with
    | .ok _ => test s!"{label}: must reject" false
    | .error _ => test label true

private def rejectionTests (src : Source.Toplevel)
    (compiled : CompiledToplevel) : TestSeq := Id.run do
  let mut seq := .done
  for n in [2 ^ 32, 2 ^ 32 + 1, gSize.toNat - 1] do
    seq := seq ++ rejects compiled #[G.ofNat n]
      s!"checked u32 rejects {n} instead of truncating"
  -- Change only the untrusted hint. Range-correct but value-incorrect
  -- advice must still fail the unchanged production reconstruction check.
  let altered : Except String CompiledToplevel := do
    if !(src.functions.any fun f => f.name.toName == `split_u32) then
      throw "missing split_u32 hint"
    let functions := src.functions.map fun f =>
      if f.name.toName == `split_u32 then
        { f with body := .tuple (#[0, 0, 0, 0].map Source.Term.field) }
      else f
    { src with functions }.compile
  seq := seq ++ withExceptOk "wrong-hint fixture compiles" altered fun wrong =>
    rejects wrong #[1] "u32 conversion rejects wrong in-range hint"
  return seq

private def constantTimeTests (compiled : CompiledToplevel) : TestSeq :=
  let direct := do
    let idx ← compiled.getFuncIdx `split_u32
    let function ← compiled.bytecode.functions[idx]?
    match function.body.ops.toList, function.body.ctrl with
    | [.unconstrainedGToBytes 0], .return _ _ => some (!function.constrained)
    | _, _ => some false
  test "no repeated-subtraction divider remains reachable"
    (compiled.getFuncIdx `divmod_256 == none) ++
  test "split_u32 lowers to one native hint without recursion or a circuit"
    (direct == some true)

def run : IO UInt32 := do
  let .ok src := source | IO.eprintln "byte-hint fixture merge failed"; return 1
  let .ok env := AiurTestEnv.build (.ok src)
    | IO.eprintln "byte-hint fixture compile failed"; return 1
  let tests := constantTimeTests env.compiled ++ rejectionTests src env.compiled
  let result ← lspecIO (.ofList [("ixvm-byte-hints", [tests])]) []
  let cases ← lspecEachIO boundaries fun tc => pure (env.runTestCase tc)
  let proofs ← lspecEachIO [
    AiurTestCase.prove `checked_u32 #[0] (bytes 0 8)
      "normalized zero conversion prove/verify",
    AiurTestCase.prove `checked_u32 #[4294967295] (bytes 4294967295 8)
      "max-u32 conversion prove/verify"] fun tc => pure (env.runTestCase tc)
  return if result == 0 && cases == 0 && proofs == 0 then 0 else 1

-- Pre-change advice retained only for the optional performance comparison.
-- These functions never enter the production toplevel or verification key.
private def oldHints := ⟦
  fn divmod_256(x: G, q: G) -> (G, G) {
    match u32_less_than(x, 256) {
      1 => (x, q),
      0 => divmod_256(x - 256, q + 1),
    }
  }
  fn split_u32(x: G) -> (G, G, G, G) {
    match divmod_256(x, 0) {
      (b0, q1) => match divmod_256(q1, 0) {
        (b1, q2) => match divmod_256(q2, 0) {
          (b2, q3) => match divmod_256(q3, 0) {
            (b3, _) => (b0, b1, b2, b3),
          },
        },
      },
    }
  }
⟧

/-- Compare the same hint call using the old and new helper. Setup is outside
the timer, `blackBoxIO` forces execution inside it, and outputs are checked.
No timing assertion. `IX_AIUR_QUERY_STATS=1` also reports advice-map sizes. -/
def timings : IO UInt32 := do
  let full ← IO.ofExcept ((do
    let vm ← IxVM.ixVMFull
    vm.merge entries).mapError toString)
  let current ← IO.ofExcept ((full.prune [`u32_hint]).compile)
  let oldFns := full.functions.filter fun f => f.name.toName != `split_u32
  let oldSource := { full with functions := oldFns ++ oldHints.functions }
  let legacy ← IO.ofExcept ((oldSource.prune [`u32_hint]).compile)
  for n in [256, 65536, 1048576] do
    for round in [:3] do
      let picks := if round % 2 == 0 then [("legacy", legacy), ("native", current)]
        else [("native", current), ("legacy", legacy)]
      for (name, compiled) in picks do
        let idx := compiled.getFuncIdx `u32_hint |>.get!
        IO.eprintln s!"CASE {name} n={n} round={round}"
        let start ← IO.monoNanosNow
        let result ← blackBoxIO (fun _ =>
          compiled.bytecode.execute idx #[G.ofNat n] default) ()
        let stop ← IO.monoNanosNow
        let (output, _, _) ← IO.ofExcept result
        unless output == bytes n 4 do
          throw (IO.userError "incorrect hint")
        IO.println s!"{name}\t{n}\t{round}\t{(stop - start).toFloat / 1000000}"
  let idx := current.getFuncIdx `u32_hint |>.get!
  IO.eprintln "CASE native n=4294967295"
  let result ← blackBoxIO (fun _ =>
    current.bytecode.execute idx #[4294967295] default) ()
  let (output, _, _) ← IO.ofExcept result
  unless output == #[255, 255, 255, 255] do
    throw (IO.userError "incorrect max-u32 hint")
  return 0

end Tests.Ix.IxVM.ByteHints

end
