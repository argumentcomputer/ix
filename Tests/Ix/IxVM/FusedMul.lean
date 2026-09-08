module

public import Ix.IxVM.Toplevel
public import Tests.Aiur.Common

public section
namespace Tests.Ix.IxVM.FusedMul
open Aiur LSpec

/-! Producer/consumer fusion, parameterized by the unchanged arithmetic
steps. Equality is of exact lists, not only their numeric interpretation.
This is not a proof of the Aiur compiler or underlying arithmetic gadgets. -/
private def produce (step : α → μ → β × μ) (finish : μ → List β) :
    List α → μ → List β
  | [], carry => finish carry
  | x :: xs, carry => let (out, next) := step x carry
    out :: produce step finish xs next

private def consume (step : β → β → ν → β × ν) (finish : List β → ν → List β) :
    List β → List β → ν → List β
  | [], ys, carry => finish ys carry
  | xs, [], carry => finish xs carry
  | x :: xs, y :: ys, carry => let (out, next) := step x y carry
    out :: consume step finish xs ys next

private def fused (mul : α → μ → β × μ) (endMul : μ → List β)
    (add : β → β → ν → β × ν) (endAdd : List β → ν → List β) :
    List α → List β → μ → ν → List β
  | [], acc, mc, ac => consume add endAdd acc (endMul mc) ac
  | x :: xs, [], mc, ac => consume add endAdd [] (produce mul endMul (x :: xs) mc) ac
  | x :: xs, y :: ys, mc, ac =>
    let (digit, nextMc) := mul x mc
    let (out, nextAc) := add y digit ac
    out :: fused mul endMul add endAdd xs ys nextMc nextAc

private theorem fused_eq_produce_consume (mul : α → μ → β × μ) (endMul : μ → List β)
    (add : β → β → ν → β × ν) (endAdd : List β → ν → List β)
    (xs : List α) (acc : List β) (mc : μ) (ac : ν) :
    fused mul endMul add endAdd xs acc mc ac =
      consume add endAdd acc (produce mul endMul xs mc) ac := by
  induction xs generalizing acc mc ac with
  | nil => rfl
  | cons x xs ih => cases acc <;> simp [fused, produce, consume, ih]

private def fixtures := ⟦
  -- Frozen pre-fusion outer loop. This remains test-only after production
  -- adopts fusion; it still shares the unchanged arithmetic and row helpers.
  fn legacy_fma_outer(a: KLimbs, b: KLimbs, acc: KLimbs, shift: G) -> KLimbs {
    match load(a) {
      ListNode.Nil => acc,
      ListNode.Cons(a_limb, rest) =>
        let prod = klimbs_mul_single(a_limb, b, [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
        let shifted = klimbs_shl_limbs(prod, shift);
        let next = klimbs_add(acc, shifted);
        legacy_fma_outer(rest, b, next, shift + 1),
    }
  }
  fn fma_read(n: G, offset: G) -> KLimbs {
    match n {
      0 => store(ListNode.Nil),
      _ => let [b0, b1, b2, b3, b4, b5, b6, b7] = io_read(0, offset, 8);
        let (c0, c1) = u8_range_check(b0, b1);
        let (c2, c3) = u8_range_check(b2, b3);
        let (c4, c5) = u8_range_check(b4, b5);
        let (c6, c7) = u8_range_check(b6, b7);
        store(ListNode.Cons([c0, c1, c2, c3, c4, c5, c6, c7], fma_read(n - 1, offset + 8))),
    }
  }
  fn fma_write(xs: KLimbs) {
    match load(xs) {
      ListNode.Nil => (),
      ListNode.Cons(limb, rest) =>
        let [b0, b1, b2, b3, b4, b5, b6, b7] = limb;
        io_write(1, [to_field(b0), to_field(b1), to_field(b2), to_field(b3),
          to_field(b4), to_field(b5), to_field(b6), to_field(b7)]);
        fma_write(rest),
    }
  }
  pub fn fma_row(mode: G, a: U64, mc: U64, ac: G, n: G, m: G) {
    let b = fma_read(n, 0);
    let acc = fma_read(m, n * 8);
    let result = match mode {
      0 => klimbs_mul_acc_row(a, b, acc, mc, ac),
      1 => klimbs_add_carry(acc, klimbs_mul_single(a, b, mc), ac),
    };
    fma_write(result)
  }
  pub fn fma_shift(mode: G, a: U64, shift: G, n: G, m: G) {
    let b = fma_read(n, 0);
    let acc = fma_read(m, n * 8);
    let result = match mode {
      0 => klimbs_mul_acc_shift(a, b, acc, shift),
      1 => klimbs_add(acc, klimbs_shl_limbs(
        klimbs_mul_single(a, b, [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), shift)),
    };
    fma_write(result)
  }
  pub fn fma_product(mode: G, n: G, m: G) {
    let a = fma_read(n, 0);
    let b = fma_read(m, n * 8);
    let result = match mode {
      0 => klimbs_mul(a, b),
      1 => legacy_fma_outer(a, b, store(ListNode.Nil), 0),
    };
    fma_write(result)
  }
⟧

private def source : Except Global Source.Toplevel := do
  let vm ← IxVM.ixVMFull
  let vm ← vm.merge fixtures
  pure (vm.prune [`fma_row, `fma_shift, `fma_product])

private def radix : Nat := 2^64
private def bytes (n : Nat) : Array Aiur.G := (Array.range 8).map fun i => G.ofNat ((n / 256^i) % 256)
private def data (xs : List Nat) : Array Aiur.G := xs.foldl (fun acc x => acc ++ bytes x) #[]
private def rowRef (a : Nat) : List Nat → Nat → List Nat
  | [], carry => if carry == 0 then [] else [carry]
  | b :: bs, carry => let n := a * b + carry
    n % radix :: rowRef a bs (n / radix)
private def succRef : List Nat → List Nat
  | [] => [1]
  | x :: xs => if x + 1 < radix then (x + 1) :: xs else 0 :: succRef xs
private def addRef : List Nat → List Nat → Nat → List Nat
  | [], ys, c => if c == 0 then ys else succRef ys
  | xs, [], c => if c == 0 then xs else succRef xs
  | x :: xs, y :: ys, c => let n := x + y + c
    n % radix :: addRef xs ys (n / radix)
private def productRef (a b : List Nat) : List Nat :=
  ((a.foldl fun (acc, shift) x =>
    (addRef acc (List.replicate shift 0 ++ rowRef x b 0) 0, shift + 1)) ([], 0)).1
private def varied (n : Nat) : List Nat := Id.run do
  let mut seed := 0x243f6a8885a308d3
  let mut xs := []
  for _ in [:n] do
    seed := (seed * 6364136223846793005 + 1442695040888963407) % radix
    xs := seed :: xs
  return xs

private def fixture (name : Lean.Name) (mode : Nat) (args : Array Aiur.G)
    (input expected : List Nat) (label : String) : AiurTestCase :=
  let io : IOBuffer := { data := ({} : Std.HashMap _ _).insert 0 (data input), map := {} }
  { functionName := name, label := s!"{label} ({mode})", input := #[G.ofNat mode] ++ args,
    inputIOBuffer := io, expectedIOBuffer := if expected.isEmpty then io else
      { io with data := io.data.insert 1 (data expected) }, withProof := false }
private def rowCase (mode a mc ac : Nat) (b acc : List Nat) (label : String) : AiurTestCase :=
  fixture `fma_row mode (bytes a ++ bytes mc ++ #[G.ofNat ac, G.ofNat b.length, G.ofNat acc.length])
    (b ++ acc) (addRef acc (rowRef a b mc) ac) label
private def shiftCase (mode a shift : Nat) (b acc : List Nat) (label : String) : AiurTestCase :=
  fixture `fma_shift mode (bytes a ++ #[G.ofNat shift, G.ofNat b.length, G.ofNat acc.length])
    (b ++ acc) (addRef acc (List.replicate shift 0 ++ rowRef a b 0) 0) label
private def productCase (mode : Nat) (a b : List Nat) (label : String) : AiurTestCase :=
  fixture `fma_product mode #[G.ofNat a.length, G.ofNat b.length] (a ++ b) (productRef a b) label

private def cases : List AiurTestCase := Id.run do
  let top := radix - 1
  let mut cases := []
  let lists := [[], [0], [0, 0], [1], [top], [top, top], [top, 0, 0], varied 5]
  for (b, i) in lists.zipIdx do
    for (acc, j) in lists.zipIdx do
      for (a, mc) in [(0, 0), (1, top), (top, top)] do
        for ac in [0, 1] do
          for mode in [0, 1] do
            cases := cases ++ [rowCase mode a mc ac b acc s!"row {i}/{j}/{a}/{mc}/{ac}"]
      for shift in [0, 1, 3, 6] do
        for mode in [0, 1] do
          cases := cases ++ [shiftCase mode top shift b acc s!"shift {i}/{j}/{shift}"]
      for mode in [0, 1] do
        cases := cases ++ [productCase mode b acc s!"product {i}/{j}"]
  return cases

private def execute (env : AiurTestEnv) (tc : AiurTestCase) : Except String (Array QueryCount) := do
  let some idx := env.compiled.getFuncIdx tc.functionName | throw "fixture entry missing"
  let (out, io, qc) ← env.compiled.bytecode.execute idx tc.input tc.inputIOBuffer
  unless out == tc.expectedOutput && io == tc.expectedIOBuffer do throw s!"wrong result: {tc.label}"
  return qc

private def stats (env : AiurTestEnv) (qc : Array QueryCount) : Except String (Nat × Nat × Float) := do
  let some i := env.compiled.bytecode.memorySizes.findIdx? (· == 10) | throw "limb circuit missing"
  let some mem := qc[env.compiled.bytecode.functions.size + i]? | throw "limb count missing"
  let rows := qc.foldl (fun n q => n + q.uniqueRows) 0
  return (mem.uniqueRows, rows, (computeStats env.compiled qc env.shapes).totalFftCost)

private def scaling (env : AiurTestEnv) : IO TestSeq := do
  let mut seq := .done
  for (n, m) in [(1, 32), (4, 4), (8, 32), (32, 8), (16, 16), (32, 32)] do
    for repeated in [false, true] do
      let a := if repeated then List.replicate n (radix - 1) else varied n
      let b := varied m
      let result := do
        let now ← stats env (← execute env (productCase 0 a b "fused scaling"))
        let old ← stats env (← execute env (productCase 1 a b "legacy scaling"))
        return (now, old)
      match result with
      | .error e => seq := seq ++ test s!"scaling {n}/{m}: {e}" false
      | .ok ((mem, rows, fft), (oldMem, oldRows, oldFft)) =>
        IO.println s!"[fused-mul] {n}x{m} repeated={repeated} limbs={mem}/{oldMem} rows={rows}/{oldRows} FFT={fft}/{oldFft} (new/old)"
        seq := seq ++ test s!"{n}x{m}/{repeated}: exact output agrees with Nat model" true
          ++ test s!"{n}x{m}/{repeated}: no extra limb-list nodes" (mem <= oldMem)
          ++ test s!"{n}x{m}/{repeated}: fewer total query rows" (rows < oldRows)
        if repeated then
          -- The old pipeline shares whole repeated product rows. Fusion
          -- retains fewer records but can have slightly wider hot circuits.
          seq := seq ++ test s!"{n}x{m}: repeated-input FFT regression <= 0.5%" (fft <= oldFft * 1.005)
        else
          seq := seq ++ test s!"{n}x{m}: varied-input FFT improves" (fft < oldFft)
          if n > 1 then
            seq := seq ++ test s!"{n}x{m}: varied-input limb nodes shrink" (mem < oldMem)
  return seq

private def invalidCarryTests (env : AiurTestEnv) : TestSeq := Id.run do
  let mut seq := .done
  for ac in [2, 255, gSize.toNat - 1] do
    for (b, acc) in [([], []), ([1], []), ([], [1]), ([1], [1])] do
      for mode in [0, 1] do
        let tc := rowCase mode 1 0 ac b acc "invalid addition carry"
        let some idx := env.compiled.getFuncIdx tc.functionName
          | return test "carry fixture entry missing" false
        let result := env.compiled.bytecode.execute idx tc.input tc.inputIOBuffer
        seq := seq ++ test s!"{mode}: non-bit carry {ac}, lengths {b.length}/{acc.length} rejected"
          (!result.isOk)
  return seq

def run : IO UInt32 := do
  let env ← IO.ofExcept (AiurTestEnv.build source)
  let basic ← lspecEachIO cases fun tc => pure (env.runTestCase tc)
  let measured ← scaling env
  let cost ← lspecIO (.ofList [("ixvm-fused-mul", [measured, invalidCarryTests env])]) []
  let top := radix - 1
  let proofs := [
    { rowCase 0 top top 1 [top, top] [top, top, top] "fused carries proof" with withProof := true },
    { shiftCase 0 top 3 [top, top] [top] "fused shift proof" with withProof := true },
    { productCase 0 [top, top] [top, top] "fused product proof" with withProof := true }]
  let proved ← lspecEachIO proofs fun tc => pure (env.runTestCase tc)
  return if basic == 0 && cost == 0 && proved == 0 then 0 else 1

end Tests.Ix.IxVM.FusedMul
end
