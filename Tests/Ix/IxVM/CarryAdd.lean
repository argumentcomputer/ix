module

public import Ix.IxVM.Toplevel
public import Tests.Aiur.Common

public section

namespace Tests.Ix.IxVM.CarryAdd

open Aiur LSpec

/-! The byte-column invariant behind the fused carry. These Nat lemmas
establish the arithmetic identity and that the sum of the two overflow bits
is a bit. They are not a proof of the whole Aiur compiler or byte gadget. -/
private theorem carry_column (a b c : Nat)
    (ha : a < 256) (hb : b < 256) (hc : c ≤ 1) :
    ((a + b) % 256 + c) % 256 = (a + b + c) % 256 ∧
    (a + b) / 256 + ((a + b) % 256 + c) / 256 = (a + b + c) / 256 ∧
    (a + b) / 256 + ((a + b) % 256 + c) / 256 ≤ 1 := by
  omega

private theorem product_high_bound (a b : Nat)
    (ha : a < 2^64) (hb : b < 2^64) : a * b / 2^64 ≤ 2^64 - 2 := by
  have h : a * b ≤ (2^64 - 1) * (2^64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

private theorem high_carry_fits (hi c : Nat)
    (hhi : hi ≤ 2^64 - 2) (hc : c ≤ 1) : hi + c < 2^64 := by omega

private def fixtures := ⟦
  pub fn inc(a: U64) -> (U64, U8) { u64_succ_carry(a) }
  pub fn inc_legacy(a: U64) -> (U64, U8) {
    u64_add(a, [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8])
  }
  pub fn adc(a: U64, b: U64) -> (U64, U8) { u64_add_carry_one(a, b) }
  pub fn adc_legacy(a: U64, b: U64) -> (U64, U8) {
    let (sum, c1) = u64_add(a, b);
    let (out, c2) = u64_add(sum, [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
    (out, u8_from_field_unsafe(to_field(c1) + to_field(c2)))
  }
  -- Exercise the production carry dispatch, not a copy of its conditionals.
  pub fn limb_add(a: U64, b: U64, carry: G) -> (U64, U8) {
    let nil = store(ListNode.Nil);
    let out = klimbs_add_carry(store(ListNode.Cons(a, nil)),
      store(ListNode.Cons(b, nil)), carry);
    let ListNode.Cons(sum, rest) = load(out);
    match load(rest) {
      ListNode.Nil => (sum, 0u8),
      ListNode.Cons(top, tail) =>
        assert_eq!(top, [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
        assert_eq!(load(tail), ListNode.Nil);
        (sum, 1u8),
    }
  }
  pub fn empty_add(carry: G) -> G {
    let nil = store(ListNode.Nil);
    match load(klimbs_add_carry(nil, nil, carry)) {
      ListNode.Nil => 0,
      ListNode.Cons(limb, _) => to_field(limb[0]),
    }
  }
  pub fn right_empty_add(carry: G) -> G {
    let nil = store(ListNode.Nil);
    let one = store(ListNode.Cons([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], nil));
    match load(klimbs_add_carry(one, nil, carry)) {
      ListNode.Nil => 0,
      ListNode.Cons(limb, _) => to_field(limb[0]),
    }
  }
⟧

private def source : Except Global Source.Toplevel := do
  let vm ← IxVM.ixVMFull
  let vm ← vm.merge fixtures
  pure (vm.prune [`inc, `inc_legacy, `adc, `adc_legacy, `limb_add,
    `empty_add, `right_empty_add])

private def radix : Nat := 2^64
private def bytes (n : Nat) : Array Aiur.G :=
  (Array.range 8).map fun i => G.ofNat ((n / 256^i) % 256)
private def output (n : Nat) : Array Aiur.G := bytes n ++ #[G.ofNat (n / radix)]

private def cases : List AiurTestCase := Id.run do
  let top := radix - 1
  let mut result := []
  -- Carry stops at each possible byte, plus full-u64 overflow.
  for k in [:9] do
    let a := 256^k - 1
    for entry in [`inc, `inc_legacy] do
      result := result ++ [.interp entry (bytes a) (output (a + 1)) s!"{entry} carry chain {k}"]
  let mut pairs := [(0, 0), (0, top), (top, 0), (top, top), (255, 255),
    (255, 0), (256, 255), (2^32 - 1, 2^32 - 1), (2^63, 2^63 - 1)]
  for k in [1:8] do pairs := pairs ++ [(256^k - 1, 1), (256^k - 2, 1)]
  let mut seed := 0x243f6a8885a308d3
  for _ in [:24] do
    seed := (seed * 6364136223846793005 + 1442695040888963407) % radix
    let a := seed
    seed := (seed * 6364136223846793005 + 1442695040888963407) % radix
    pairs := pairs ++ [(a, seed)]
  for ((a, b), i) in pairs.zipIdx do
    for entry in [`adc, `adc_legacy] do
      result := result ++ [.interp entry (bytes a ++ bytes b) (output (a + b + 1))
        s!"{entry} pair {i}"]
    for carry in [0, 1] do
      result := result ++ [.interp `limb_add (bytes a ++ bytes b ++ #[G.ofNat carry])
        (output (a + b + carry)) s!"limb add pair {i}, carry {carry}"]
  for carry in [0, 1] do
    result := result ++ [
      .interp `empty_add #[G.ofNat carry] #[G.ofNat carry] s!"empty add carry {carry}",
      .interp `right_empty_add #[G.ofNat carry] #[G.ofNat (1 + carry)]
        s!"right-empty add carry {carry}"]
  return result

private def structuralTests (env : AiurTestEnv) : TestSeq := Id.run do
  let mut seq := .done
  for (name, inputs, adds) in [(`u64_succ_carry, 8, 8), (`u64_add_carry_one, 16, 16)] do
    let valid := do
      let idx ← env.compiled.getFuncIdx name
      let function ← env.compiled.bytecode.functions[idx]?
      let checkedAdds := function.body.ops.foldl (fun n op => match op with
        | .u8Add _ _ => n + 1 | _ => n) 0
      return function.layout.inputSize == inputs && checkedAdds == adds && function.constrained
    seq := seq ++ test s!"{name}: narrow key and {adds} constrained byte adds"
      (valid == some true)
  return seq

private def rejectBadCarry (env : AiurTestEnv) : TestSeq := Id.run do
  let mut seq := .done
  for carry in [2, 255, gSize.toNat - 1] do
    for (entry, inputPrefix) in [(`limb_add, bytes 0 ++ bytes 0),
        (`empty_add, #[]), (`right_empty_add, #[])] do
      match env.compiled.getFuncIdx entry with
      | none => seq := seq ++ test s!"{entry}: missing rejection fixture" false
      | some idx =>
        let result := env.compiled.bytecode.execute idx (inputPrefix ++ #[G.ofNat carry]) default
        seq := seq ++ test s!"{entry} rejects non-bit carry {carry}" (!result.isOk)
  return seq

def run : IO UInt32 := do
  let env ← IO.ofExcept <| (AiurTestEnv.build source).mapError
    (fun e => s!"carry-add fixture build failed: {e}")
  let basic ← lspecEachIO cases fun tc => pure (env.runTestCase tc)
  let checks ← lspecIO (.ofList [("ixvm-carry-add",
    [structuralTests env ++ rejectBadCarry env])]) []
  let top := radix - 1
  let proofs ← lspecEachIO [
    AiurTestCase.prove `inc (bytes top) (output radix) "checked increment overflow prove/verify",
    AiurTestCase.prove `adc (bytes top ++ bytes top) (output (2 * top + 1))
      "fused add maximal carry prove/verify",
    AiurTestCase.prove `limb_add (bytes top ++ bytes 0 ++ #[0]) (output top)
      "zero-carry dispatch prove/verify",
    AiurTestCase.prove `limb_add (bytes top ++ bytes top ++ #[1]) (output (2 * top + 1))
      "one-carry dispatch prove/verify"] fun tc => pure (env.runTestCase tc)
  return if basic == 0 && checks == 0 && proofs == 0 then 0 else 1

end Tests.Ix.IxVM.CarryAdd

end
