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

def entrypoints := ⟦
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

  -- Mutual-block member addresses, pinned against the Rust side
  -- (`Constant::new(ConstantInfo::XPrj{..}).commit()`; see the
  -- `proj_addr_dump` test in `crates/kernel/src/ingress.rs` for the
  -- fixture). Address-keyed constants resolve `Expr.Rec(i)` through these,
  -- so a drift in the projection encoding must fail loudly here rather than
  -- silently rebind a mutual-block reference.
  fn member_addr_tests() {
    let block = store([0x13u8, 0x66u8, 0x47u8, 0xa8u8, 0x96u8, 0x84u8, 0x89u8, 0xabu8, 0xf2u8, 0x00u8, 0xbau8, 0x35u8, 0xfeu8, 0xb6u8, 0x13u8, 0xd7u8, 0xb3u8, 0x5cu8, 0xe3u8, 0xbau8, 0x68u8, 0x21u8, 0x93u8, 0x06u8, 0xd5u8, 0x62u8, 0x40u8, 0x58u8, 0x9cu8, 0x4cu8, 0x55u8, 0x8bu8]);
    let idx3 = [0x03u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    assert_eq!(address_eq(dprj_content_addr(idx3, block),
      store([0xefu8, 0x80u8, 0x33u8, 0xc1u8, 0x89u8, 0x54u8, 0xf2u8, 0x2eu8, 0x1bu8, 0x88u8, 0xb3u8, 0x38u8, 0x94u8, 0xdbu8, 0xddu8, 0x06u8, 0x28u8, 0xe0u8, 0xc3u8, 0x33u8, 0xf2u8, 0x7cu8, 0xb5u8, 0x5du8, 0x07u8, 0x42u8, 0xe4u8, 0xa7u8, 0xa7u8, 0xb4u8, 0x75u8, 0x46u8])), 1);
    assert_eq!(address_eq(iprj_content_addr(idx3, block),
      store([0xf5u8, 0x9fu8, 0x2fu8, 0xaeu8, 0x42u8, 0x8du8, 0x9eu8, 0x4au8, 0x4eu8, 0x5fu8, 0xddu8, 0xeeu8, 0x4cu8, 0x58u8, 0xf8u8, 0xb8u8, 0x34u8, 0xf8u8, 0xfbu8, 0x6du8, 0x54u8, 0xcdu8, 0x9au8, 0x74u8, 0x34u8, 0xa4u8, 0x53u8, 0x3cu8, 0x95u8, 0x99u8, 0x57u8, 0x21u8])), 1);
    assert_eq!(address_eq(rprj_content_addr(idx3, block),
      store([0x5cu8, 0xb1u8, 0x45u8, 0x79u8, 0xd7u8, 0xc8u8, 0xceu8, 0xa9u8, 0x1du8, 0xb5u8, 0xacu8, 0xeau8, 0x36u8, 0xc0u8, 0x39u8, 0x20u8, 0xc9u8, 0x29u8, 0x46u8, 0xdeu8, 0x69u8, 0x84u8, 0xf6u8, 0xf0u8, 0x26u8, 0x60u8, 0x37u8, 0xb9u8, 0x61u8, 0x49u8, 0x10u8, 0x13u8])), 1);
  }

  pub fn kernel_unit_tests() {
    level_cmp_tests();
    member_addr_tests()
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

/-- Build the FULL IxVM Aiur toplevel: every merged module, every entry
    point — including the test/bench entries (`blake3_test`,
    `sha256_bench`, `rbtree_map_test`, `kernel_unit_tests`,
    `ixon_serde_blake3_bench`, …). Use this only for harnesses that run
    those entries; production systems build from `ixVM` (pruned), so
    test-only circuits never widen a committed kernel system. -/
def ixVMFull : Except Aiur.Global Aiur.Source.Toplevel := do
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
  let vm ← vm.merge claim
  vm.merge entrypoints

/-- The production IxVM kernel toplevel: `ixVMFull` pruned to the closure
    of the two kernel entry points. The byte loaders inside `ingress`
    recompute blake3 over every IOBuffer read and assert the digest
    matches the address key — required for `verify_claim`'s soundness.
    `verify_const` (the arena-test subject-only entrypoint) goes through
    the same loaders since the IxVM kernel only has one storage
    convention. Pruning drops the test/bench entries and their exclusive
    call closures — every compiled function is a committed circuit whose
    openings pad every proof, so dead entries cost real proof bytes. -/
def ixVM : Except Aiur.Global Aiur.Source.Toplevel := do
  let vm ← ixVMFull
  pure (vm.prune [`verify_claim, `verify_const])

end IxVM

end
