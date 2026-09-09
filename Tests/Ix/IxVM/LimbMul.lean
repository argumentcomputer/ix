module

public import Ix.IxVM.Toplevel
public import Tests.Aiur.Common

public section

namespace Tests.Ix.IxVM.LimbMul

open Aiur LSpec

/-! A list-level equivalence proof, parameterized by the unchanged arithmetic
step and final-carry rule. This proves the construction transformation, not
the whole Aiur compiler/executor or the arithmetic gadgets. -/

private def prefixRow (step : α → β → α × β) (finish : β → List α) :
    List α → β → List α → List α
  | [], carry, acc => acc ++ finish carry
  | x :: xs, carry, acc =>
    let (limb, next) := step x carry
    prefixRow step finish xs next (acc ++ [limb])

private def consRow (step : α → β → α × β) (finish : β → List α) :
    List α → β → List α
  | [], carry => finish carry
  | x :: xs, carry =>
    let (limb, next) := step x carry
    limb :: consRow step finish xs next

private theorem prefixRow_eq_append_consRow
    (step : α → β → α × β) (finish : β → List α)
    (xs : List α) (carry : β) (acc : List α) :
    prefixRow step finish xs carry acc = acc ++ consRow step finish xs carry := by
  induction xs generalizing carry acc with
  | nil => rfl
  | cons x xs ih => simp [prefixRow, consRow, ih, List.append_assoc]

private def fixtures := ⟦
  -- Frozen pre-optimization implementation, sharing the REAL arithmetic
  -- helpers. Keep this test-only; it must never enter the production VK.
  fn legacy_row(a: U64, b: KLimbs, carry: U64, acc: KLimbs) -> KLimbs {
    match load(b) {
      ListNode.Nil =>
        match u64_is_zero(carry) {
          1 => acc,
          0 => list_snoc(acc, carry),
        },
      ListNode.Cons(limb, rest) =>
        let (lo, hi) = u64_mul(a, limb);
        let (sum, carry_out) = u64_add(lo, carry);
        let (next, _) = u64_add(hi,
          [carry_out, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
        legacy_row(a, rest, next, list_snoc(acc, sum)),
    }
  }

  -- Isolate carry specialization from the earlier cons-vs-snoc change:
  -- this is the linear row builder immediately BEFORE carry specialization.
  fn before_carry_row(a: U64, b: KLimbs, carry: U64) -> KLimbs {
    match load(b) {
      ListNode.Nil => match u64_is_zero(carry) {
        1 => store(ListNode.Nil),
        0 => store(ListNode.Cons(carry, store(ListNode.Nil))),
      },
      ListNode.Cons(limb, rest) =>
        let (lo, hi) = u64_mul(a, limb);
        let (sum, carry_out) = u64_add(lo, carry);
        let (next, _) = u64_add(hi,
          [carry_out, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
        store(ListNode.Cons(sum, before_carry_row(a, rest, next))),
    }
  }

  fn read_limbs(n: G, offset: G) -> KLimbs {
    match n {
      0 => store(ListNode.Nil),
      _ =>
        let [b0, b1, b2, b3, b4, b5, b6, b7] = io_read(0, offset, 8);
        let (c0, c1) = u8_range_check(b0, b1);
        let (c2, c3) = u8_range_check(b2, b3);
        let (c4, c5) = u8_range_check(b4, b5);
        let (c6, c7) = u8_range_check(b6, b7);
        store(ListNode.Cons([c0, c1, c2, c3, c4, c5, c6, c7],
          read_limbs(n - 1, offset + 8))),
    }
  }

  fn write_limbs(xs: KLimbs) {
    match load(xs) {
      ListNode.Nil => (),
      ListNode.Cons(limb, rest) =>
        let [b0, b1, b2, b3, b4, b5, b6, b7] = limb;
        io_write(1, [to_field(b0), to_field(b1), to_field(b2), to_field(b3),
          to_field(b4), to_field(b5), to_field(b6), to_field(b7)]);
        write_limbs(rest),
    }
  }

  pub fn row_linear(a: U64, carry: U64, n: G) {
    write_limbs(klimbs_mul_single(a, read_limbs(n, 0), carry))
  }
  pub fn row_legacy(a: U64, carry: U64, n: G) {
    write_limbs(legacy_row(a, read_limbs(n, 0), carry, store(ListNode.Nil)))
  }
  pub fn row_before_carry(a: U64, carry: U64, n: G) {
    write_limbs(before_carry_row(a, read_limbs(n, 0), carry))
  }
  pub fn product(n: G, m: G) {
    let a = read_limbs(n, 0);
    let b = read_limbs(m, n * 8);
    write_limbs(klimbs_normalize(klimbs_mul(a, b)))
  }
⟧

private def source : Except Global Source.Toplevel := do
  let vm ← IxVM.ixVMFull
  let vm ← vm.merge fixtures
  pure (vm.prune [`row_linear, `row_legacy, `row_before_carry, `product])

private def radix : Nat := 2 ^ 64
private def limbBytes (n : Nat) : Array Aiur.G :=
  (Array.range 8).map fun i => G.ofNat ((n / 256 ^ i) % 256)
private def limbData (xs : List Nat) : Array Aiur.G :=
  xs.foldl (fun data x => data ++ limbBytes x) #[]
private def value (xs : List Nat) : Nat := xs.foldr (fun x v => x + radix * v) 0

private def rowRef (a : Nat) : List Nat → Nat → List Nat
  | [], carry => if carry == 0 then [] else [carry]
  | x :: xs, carry =>
    let p := a * x + carry
    (p % radix) :: rowRef a xs (p / radix)

private def varied (n : Nat) : List Nat := Id.run do
  let mut seed := 0x243f6a8885a308d3
  let mut xs := []
  for _ in [:n] do
    seed := (seed * 6364136223846793005 + 1442695040888963407) % radix
    xs := seed :: xs
  return xs

private def inputIo (xs : List Nat) : IOBuffer :=
  { data := ({} : Std.HashMap _ _).insert 0 (limbData xs), map := {} }

private def outputIo (input : IOBuffer) (xs : List Nat) : IOBuffer :=
  if xs.isEmpty then input else
    { input with data := input.data.insert 1 (limbData xs) }

private def rowCase (entry : Lean.Name) (a carry : Nat) (xs : List Nat)
    (label : String) : AiurTestCase :=
  let io := inputIo xs
  { functionName := entry, label
    input := limbBytes a ++ limbBytes carry ++ #[G.ofNat xs.length]
    inputIOBuffer := io, expectedIOBuffer := outputIo io (rowRef a xs carry)
    withProof := false }

private def productCase (a b : List Nat) (label : String) : AiurTestCase :=
  let io := inputIo (a ++ b)
  let p := value a * value b
  let output := (List.range (a.length + b.length)).map
    (fun i => (p / radix ^ i) % radix)
  let normalized := (output.reverse.dropWhile (· == 0)).reverse
  { functionName := `product, label
    input := #[G.ofNat a.length, G.ofNat b.length]
    inputIOBuffer := io, expectedIOBuffer := outputIo io normalized
    withProof := false }

private def rowCases : List AiurTestCase := Id.run do
  let top := radix - 1
  let cases := [(0, 0, []), (top, 0, []), (top, top, []),
    (0, 0, [0, 0, 0]), (0, top, [top, 0, 0]),
    (1, 0, [7, 0, 0]), (top, top, [top, top, top]),
    (2 ^ 32, 1, [2 ^ 32, 0, top]), (top - 2, 7, varied 12)]
  let mut result := []
  for ((a, carry, xs), i) in cases.zipIdx do
    for entry in [`row_linear, `row_legacy, `row_before_carry] do
      result := result ++ [rowCase entry a carry xs s!"{entry} boundary {i}"]
  return result

private def productCases : List AiurTestCase := Id.run do
  let top := radix - 1
  let mut result := []
  for ((a, b), i) in [([], [top]), ([top], []), ([0, 0], [top, 0]),
      ([1], [top, 0, 0]), ([0, 1], [0, 1]),
      ([top, top], [top, top]), (varied 4, varied 7)].zipIdx do
    result := result ++ [productCase a b s!"full product {i}"]
  return result

private def execute (env : AiurTestEnv) (tc : AiurTestCase) :
    Except String (Array QueryCount) := do
  let some idx := env.compiled.getFuncIdx tc.functionName
    | throw "missing row entry"
  let (out, io, qc) ← env.compiled.bytecode.execute idx tc.input tc.inputIOBuffer
  if out != tc.expectedOutput || io != tc.expectedIOBuffer then
    throw s!"wrong result for {tc.label}"
  return qc

private def limbRows (compiled : CompiledToplevel) (qc : Array QueryCount) :
    Except String Nat := do
  let some i := compiled.bytecode.memorySizes.findIdx? (· == 10)
    | throw "limb memory circuit missing"
  let some count := qc[compiled.bytecode.functions.size + i]?
    | throw "limb memory query count missing"
  return count.uniqueRows

private def scalingTests (env : AiurTestEnv) : IO TestSeq := do
  let mut seq := .done
  for n in [16, 32, 64, 128, 256, 512] do
    let a := radix - 3
    let xs := varied n
    let comparison := do
      let linear ← execute env (rowCase `row_linear a 7 xs s!"linear {n}")
      let legacy ← execute env (rowCase `row_legacy a 7 xs s!"legacy {n}")
      let l ← limbRows env.compiled linear
      let old ← limbRows env.compiled legacy
      return (l, old)
    match comparison with
    | .error e => seq := seq ++ test s!"row scaling {n}: {e}" false
    | .ok (linear, legacy) =>
      IO.println s!"[limb-row] n={n} memory rows: linear={linear} legacy={legacy}"
      seq := seq ++ test s!"{n} limbs: exact outputs agree with Nat model" true
        ++ test s!"{n} limbs: input + output use at most 2*n+2 memory rows"
          (linear <= 2 * n + 2)
        ++ test s!"{n} limbs: legacy fixture exposes quadratic prefix copying"
          (legacy >= n * (n + 1) / 2)
  return seq

/-- Uncompressed-equivalent argument/result storage for the hot addition helpers.
The increment has 8 input + 9 output fields; generic/fused addition has
16 + 9. This is a row-count model, not the byte-encoded retained payload;
it excludes table/multiplicity overhead and is NOT total RSS. -/
private def additionPayload (compiled : CompiledToplevel) (qc : Array QueryCount) :
    Except String (Nat × Nat) := do
  let some add := compiled.getFuncIdx `u64_add | throw "u64_add missing"
  let some addCount := qc[add]? | throw "u64_add count missing"
  let mut words := addCount.uniqueRows * 25
  for (name, width) in [(`u64_succ_carry, 17), (`u64_add_carry_one, 25)] do
    if let some idx := compiled.getFuncIdx name then
      let some count := qc[idx]? | throw s!"{name} count missing"
      words := words + count.uniqueRows * width
  return (addCount.uniqueRows, words * 8)

private def carrySavingsTests (env : AiurTestEnv) : IO TestSeq := do
  let mut seq := .done
  for n in [16, 64, 256, 512] do
    let comparison := do
      let xs := varied n
      let now ← execute env (rowCase `row_linear (radix - 3) 7 xs s!"carry optimized {n}")
      let old ← execute env (rowCase `row_before_carry (radix - 3) 7 xs s!"carry baseline {n}")
      let current ← additionPayload env.compiled now
      let previous ← additionPayload env.compiled old
      let currentFft := (computeStats env.compiled now env.shapes).totalFftCost
      let previousFft := (computeStats env.compiled old env.shapes).totalFftCost
      return (current, previous, currentFft, previousFft)
    match comparison with
    | .error e => seq := seq ++ test s!"carry savings {n}: {e}" false
    | .ok ((rows, payload), (oldRows, oldPayload), fft, oldFft) =>
      IO.println s!"[carry-row] n={n} u64_add rows={rows}/{oldRows}, uncompressed-equivalent addition payload={payload}/{oldPayload} bytes, FFT={fft}/{oldFft} (new/old)"
      seq := seq ++ test s!"{n} limbs: old/new exact outputs match Nat reference" true
        ++ test s!"{n} limbs: at least half the generic u64_add rows removed" (rows * 2 <= oldRows)
        ++ test s!"{n} limbs: uncompressed-equivalent hot addition payload shrank" (payload < oldPayload)
        ++ test s!"{n} limbs: row FFT cost improved" (fft < oldFft)
  return seq

def run : IO UInt32 := do
  let .ok env := AiurTestEnv.build source
    | IO.eprintln "limb-multiplication fixture build failed"; return 1
  let basic ← lspecEachIO (rowCases ++ productCases) fun tc =>
    pure (env.runTestCase tc)
  let scaling ← scalingTests env
  let carrySavings ← carrySavingsTests env
  let scaleResult ← lspecIO (.ofList [("ixvm-limb-mul", [scaling, carrySavings])]) []
  let top := radix - 1
  let proofs := [
    { rowCase `row_linear top top [top, top] "row carry prove/verify" with
      withProof := true },
    { productCase [top, top] [top, top] "multi-limb product prove/verify" with
      withProof := true }]
  let proofResult ← lspecEachIO proofs fun tc => pure (env.runTestCase tc)
  return if basic == 0 && scaleResult == 0 && proofResult == 0 then 0 else 1

end Tests.Ix.IxVM.LimbMul

end
