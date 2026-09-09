module

public import Ix.IxVM.Toplevel
public import Tests.Aiur.Common

/-!
The production arithmetic byte hints must be constant-time, but remain
untrusted advice. Test the real helpers and their real checking callers:
boundary/reference arithmetic, malformed advice, out-of-range inputs, and
small prove/verify cases. No test-only entrypoint enters the production VK.
-/

public section

namespace Tests.Ix.IxVM.ByteHints

open Aiur LSpec

private def entries := ⟦
  pub fn carry_hint(x: G) -> (G, G, G) { #split_carry(x) }
  pub fn u32_hint(x: G) -> (G, G, G, G) { #split_u32(x) }
  pub fn checked_mul(a: U64, b: U64) -> (U64, U64) { u64_mul(a, b) }
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
  pure (vm.prune [`carry_hint, `u32_hint, `checked_mul, `checked_u32])

private def bytes (n width : Nat) : Array Aiur.G :=
  (Array.range width).map fun i => G.ofNat ((n / 256 ^ i) % 256)

private def boundaryCases : List AiurTestCase := Id.run do
  let mut cases := []
  for n in [0, 1, 255, 256, 257, 65535, 65536, 524287] do
    cases := cases ++ [.interp `carry_hint #[G.ofNat n] (bytes n 3) s!"carry {n}"]
  for n in [0, 1, 255, 256, 65535, 65536, 16777215, 16777216, 4294967295] do
    cases := cases ++ [
      .interp `u32_hint #[G.ofNat n] (bytes n 4) s!"u32 hint {n}",
      .interp `checked_u32 #[G.ofNat n] (bytes n 8) s!"checked u32 {n}"]
  let top := 2 ^ 64 - 1
  let pairs := [(0, top), (1, top), (255, 256), (65535, 65536),
    (2 ^ 32, 2 ^ 32), (2 ^ 63, 2), (top, top),
    (0x0123456789abcdef, 0xfedcba9876543210)]
  for (a, b) in pairs do
    cases := cases ++ [.interp `checked_mul (bytes a 8 ++ bytes b 8)
      (bytes (a * b) 16) s!"u64 multiply {a} * {b}"]
  -- Deterministic varied limbs exercise carry propagation without timing
  -- assertions or a dependency on a particular random-number generator.
  let mut seed := 0x243f6a8885a308d3
  for i in [:24] do
    seed := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    let a := seed
    seed := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    let b := seed
    cases := cases ++ [.interp `checked_mul (bytes a 8 ++ bytes b 8)
      (bytes (a * b) 16) s!"varied u64 multiply {i}"]
  return cases

/-- Replace only an untrusted helper body, leaving its production checking
caller intact. A missing target is a broken fixture, not a passing rejection. -/
private def withHint (src : Source.Toplevel) (name : Lean.Name)
    (values : Array Aiur.G) : Except String CompiledToplevel := do
  if !(src.functions.any fun f => f.name.toName == name) then
    throw s!"missing hint {name}"
  let functions := src.functions.map fun f =>
    if f.name.toName == name then
      { f with body := .tuple (values.map Source.Term.field) }
    else f
  { src with functions }.compile

private def rejects (compiled : CompiledToplevel) (name : Lean.Name)
    (input : Array Aiur.G) (label : String) : TestSeq :=
  match compiled.getFuncIdx name with
  | none => test s!"{label}: entrypoint missing" false
  | some i => match compiled.bytecode.execute i input default with
    | .ok _ => test s!"{label}: must reject" false
    | .error _ => test label true

private def rejectionTests (src : Source.Toplevel)
    (compiled : CompiledToplevel) : TestSeq := Id.run do
  let mut seq := .done
  for n in [2 ^ 32, 2 ^ 32 + 1, gSize.toNat - 1] do
    seq := seq ++ rejects compiled `checked_u32 #[G.ofNat n]
      s!"checked u32 rejects {n} instead of truncating"
  for (hint, advice, entry, input, label) in [
      (`split_carry, #[0, 0, 0], `checked_mul, bytes 1 8 ++ bytes 1 8,
        "multiplication rejects wrong in-range carry hint"),
      (`split_u32, #[0, 0, 0, 0], `checked_u32, #[1],
        "u32 conversion rejects wrong in-range hint")] do
    seq := seq ++ withExceptOk s!"{label}: fixture compiles"
      (withHint src hint advice) fun altered => rejects altered entry input label
  return seq

/-- Malformed hint bytes must produce a typed execution rejection, including
in release builds with `panic=abort`. Keep the subprocess so a regression to
an abort cannot masquerade as successful rejection or kill the whole suite. -/
def runOutOfRangeProbe (kind : String) : IO UInt32 := do
  let .ok src := source | return 2
  let (hint, advice, entry, input) ← match kind with
    | "carry" => pure (`split_carry, #[256, 0, 0], `checked_mul,
        bytes 16 8 ++ bytes 16 8)
    | "u32" => pure (`split_u32, #[256, 0, 0, 0], `checked_u32, #[256])
    | _ => return 2
  let .ok compiled := withHint src hint advice | return 2
  let some i := compiled.getFuncIdx entry | return 2
  match compiled.bytecode.execute i input default with
  | .ok _ => return 0
  | .error e =>
    IO.eprintln e
    return 1

private def outOfRangeTests : IO TestSeq := do
  let exe ← IO.appPath
  let mut seq := .done
  for kind in ["carry", "u32"] do
    let output ← IO.Process.output {
      cmd := "bash"
      args := #["-c", "ulimit -c 0; exec \"$@\"", "ixvm-byte-hints",
        exe.toString, s!"ixvm-byte-hints-probe={kind}"] }
    seq := seq ++ test s!"{kind}: value-correct out-of-range hint byte rejected"
      (output.exitCode == 1 && output.stderr.contains
        "value 256 out of u8 range [0, 256)")
  return seq

/-- Guard against accidentally putting a recursive Aiur divider back into
either hint. These helpers should each lower to just one native hint op. -/
private def constantTimeTests (compiled : CompiledToplevel) : TestSeq := Id.run do
  let mut seq := test "no repeated-subtraction divider remains reachable"
    (compiled.getFuncIdx `divmod_256 == none)
  for name in [`split_carry, `split_u32] do
    let direct := do
      let idx ← compiled.getFuncIdx name
      let function ← compiled.bytecode.functions[idx]?
      match function.body.ops.toList, function.body.ctrl with
      | [.unconstrainedGToBytes 0], .return _ _ => some (!function.constrained)
      | _, _ => some false
    seq := seq ++ test s!"{name}: one native hint op, no recursion or circuit"
      (direct == some true)
  return seq

def run : IO UInt32 := do
  let .ok src := source | IO.eprintln "byte-hint fixture merge failed"; return 1
  let .ok env := AiurTestEnv.build (.ok src)
    | IO.eprintln "byte-hint fixture compile failed"; return 1
  let tests := constantTimeTests env.compiled ++ rejectionTests src env.compiled
    ++ (← outOfRangeTests)
  let result ← lspecIO (.ofList [("ixvm-byte-hints", [tests])]) []
  let cases ← lspecEachIO boundaryCases fun tc => pure (env.runTestCase tc)
  -- Exercise the actual constraint/lookup pipeline as well as execution.
  let top := 2 ^ 64 - 1
  let proofs ← lspecEachIO [
    AiurTestCase.prove `checked_mul (bytes top 8 ++ bytes top 8)
      (bytes (top * top) 16) "max-u64 multiplication prove/verify",
    AiurTestCase.prove `checked_u32 #[4294967295] (bytes 4294967295 8)
      "max-u32 conversion prove/verify"] fun tc => pure (env.runTestCase tc)
  return if result == 0 && cases == 0 && proofs == 0 then 0 else 1

end Tests.Ix.IxVM.ByteHints

end
