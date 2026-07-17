module
public import Ix.Aiur.Meta
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
public import Ix.IxVM.Blake3
public import Ix.IxVM.RBTreeMap
public import Ix.IxVM.Ingress
public import Ix.IxVM.Ixon
public import Ix.IxVM.IxonSerialize
public import Ix.IxVM.IxonDeserialize
public import Ix.IxVM.Convert
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel.Levels
public import Ix.IxVM.Kernel.Primitive
public import Ix.IxVM.Kernel.Subst
public import Ix.IxVM.Kernel.Whnf
public import Ix.IxVM.Kernel.Infer
public import Ix.IxVM.Kernel.DefEq
public import Ix.IxVM.Kernel.Inductive
public import Ix.IxVM.Kernel.CanonicalCheck
public import Ix.IxVM.Kernel.Check
public import Ix.IxVM.Kernel.Claim
public import Ix.IxVM.ClaimHarness

public section

namespace IxVM

def testEntrypoints := ⟦
  /- # Test entrypoints -/

  pub fn ixon_serde_test(n: G) {
    match n {
      0 => (),
      _ =>
        let n_minus_1 = n - 1;
        let (idx, len) = io_get_info(0, [n_minus_1]);
        let bytes = #read_byte_stream(0, idx, len);
        let (const, rest) = get_constant(bytes);
        assert_eq!(load(rest), ListNode.Nil);
        let bytes2 = put_constant(const, store(ListNode.Nil));
        assert_eq!(bytes, bytes2);
        ixon_serde_test(n_minus_1),
    }
  }

  fn level_cmp_tests() {
    let zero = store(KLevelNode.Zero);
    let p0 = store(KLevelNode.Param(0));
    let p1 = store(KLevelNode.Param(1));
    let succ_p0 = store(KLevelNode.Succ(p0));
    let succ_zero = store(KLevelNode.Succ(zero));

    -- Zero ≤ anything
    assert_eq!(level_leq(zero, p0), 1);

    -- Param(u) ≤ Param(u) (reflexivity)
    assert_eq!(level_leq(p0, p0), 1);

    -- Param(u) ≤ Param(v) fails (u ≠ v, set u > v)
    assert_eq!(level_leq(p0, p1), 0);

    -- Succ(u) ≤ Succ(u) (peel both succs)
    assert_eq!(level_leq(succ_p0, succ_p0), 1);

    -- Succ(u) ≤ u fails (u+1 > u at any assignment)
    assert_eq!(level_leq(succ_p0, p0), 0);

    -- Param(u) ≤ Succ(Param(u)) (u ≤ u+1)
    assert_eq!(level_leq(p0, succ_p0), 1);

    -- max(u, v) ≤ max(u, v) (reflexivity via distribution)
    let max_uv = store(KLevelNode.Max(p0, p1));
    assert_eq!(level_leq(max_uv, max_uv), 1);

    -- u ≤ max(u, v)
    assert_eq!(level_leq(p0, max_uv), 1);

    -- max(u, v) ≤ u fails
    assert_eq!(level_leq(max_uv, p0), 0);

    -- imax(u, v) ≤ max(u, v)
    let imax_uv = store(KLevelNode.IMax(p0, p1));
    assert_eq!(level_leq(imax_uv, max_uv), 1);

    -- max(u, v) ≤ imax(u, v) fails
    assert_eq!(level_leq(max_uv, imax_uv), 0);

    -- u+1 = max(1, imax(u+1, u)): equal for all σ (case-split fix)
    let a = succ_p0;
    let b = store(KLevelNode.Max(
      succ_zero,
      store(KLevelNode.IMax(succ_p0, p0))));
    assert_eq!(level_equal(a, b), 1);

    -- imax(u, u) = u
    assert_eq!(level_equal(store(KLevelNode.IMax(p0, p0)), p0), 1);

    -- max(u, 0) = u
    assert_eq!(level_equal(store(KLevelNode.Max(p0, zero)), p0), 1);

    -- level_imax reduces imax(u, 1+v) to max(u, 1+v) and imax(u, 0) to 0
    let succ_v = store(KLevelNode.Succ(p1));
    assert_eq!(level_eq(
      level_imax(p0, succ_v),
      store(KLevelNode.Max(p0, succ_v))), 1);

    assert_eq!(level_eq(
      level_imax(p0, zero),
      zero), 1);
  }

  pub fn kernel_unit_tests() {
    level_cmp_tests()
  }

  /- # Benchmark entrypoints -/

  pub fn ixon_serde_blake3_bench(n: G) {
    match n {
      0 => (),
      _ =>
        let n_minus_1 = n - 1;
        let (idx, len) = io_get_info(0, [n_minus_1]);
        let bytes = #read_byte_stream(0, idx, len);
        let (const, rest) = get_constant(bytes);
        assert_eq!(load(rest), ListNode.Nil);
        let bytes2 = put_constant(const, store(ListNode.Nil));
        assert_eq!(blake3(bytes), blake3(bytes2));
        ixon_serde_blake3_bench(n_minus_1),
    }
  }
⟧

/-- Build the IxVM Aiur toplevel. The byte loaders inside `ingress`
    recompute blake3 over every IOBuffer read and assert the digest
    matches the address key — required for `verify_claim`'s soundness.
    `verify_const` (the arena-test subject-only entrypoint) goes
    through the same loaders since the IxVM kernel only has one
    storage convention. -/
def ixVM : Except Aiur.Global Aiur.Source.Toplevel := do
  let vm ← core.merge byteStream
  let vm ← vm.merge blake3
  let vm ← vm.merge rbTreeMap
  let vm ← vm.merge ixon
  let vm ← vm.merge ixonSerialize
  let vm ← vm.merge ixonDeserialize
  let vm ← vm.merge convert
  let vm ← vm.merge ingress
  let vm ← vm.merge kernelTypes
  let vm ← vm.merge levels
  let vm ← vm.merge primitive
  let vm ← vm.merge subst
  let vm ← vm.merge whnf
  let vm ← vm.merge infer
  let vm ← vm.merge defEq
  let vm ← vm.merge inductive_check
  let vm ← vm.merge canonicalCheck
  let vm ← vm.merge check
  vm.merge claim

/-- The IxVM toplevel extended with every test/benchmark entrypoint
    (`ixon_serde_test`, `kernel_unit_tests`, `ixon_serde_blake3_bench`,
    `blake3_test`/`blake3_bench`, `rbtree_map_test`, …). Test and bench
    harnesses build their systems from this; the production `ixVM` stays
    free of the extra entry circuits (and of whatever becomes reachable
    only through them). NOTE: the codegen'd Rust kernel (`ix codegen`)
    is generated from `ixVM`, so entrypoints that only exist here must
    be executed via the bytecode interpreter, never `executeIxVM`. -/
def ixVMTests : Except Aiur.Global Aiur.Source.Toplevel := do
  let vm ← ixVM
  let vm ← vm.merge blake3Tests
  let vm ← vm.merge rbTreeMapTests
  vm.merge testEntrypoints

end IxVM

end
