module
public import Ix.Aiur.Meta
public import Ix.IxVM.Templates
public import Ix.IxVM.ByteStream
public import Ix.IxVM.Blake3
public import Ix.IxVM.Ingress
public import Ix.IxVM.Ixon
public import Ix.IxVM.IxonSerialize
public import Ix.IxVM.IxonDeserialize
public import Ix.IxVM.Convert
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel

public section

namespace IxVM

def entrypoints := ⟦
  /- # Test entrypoints -/

  pub fn ixon_serde_test(n: G) {
    match n {
      0 => (),
      _ =>
        let n_minus_1 = n - 1;
        let (idx, len) = io_get_info([n_minus_1]);
        let bytes = #read_byte_stream(idx, len);
        let (const, rest) = get_constant(bytes);
        assert_eq!(rest, ByteStream.Nil);
        let bytes2 = put_constant(const, ByteStream.Nil);
        assert_eq!(bytes, bytes2);
        ixon_serde_test(n_minus_1),
    }
  }

  pub fn kernel_check_test(target_addr: [G; 32]) {
    let (k_consts, nat_idx, str_idx) = ingress_with_primitives(target_addr);
    k_check_all_go(k_consts, k_consts, nat_idx, str_idx, 0)
  }

  fn level_cmp_tests() {
    -- Zero ≤ anything
    assert_eq!(level_leq(KLevel.Zero, KLevel.Param(0)), 1);

    -- Param(u) ≤ Param(u) (reflexivity)
    assert_eq!(level_leq(KLevel.Param(0), KLevel.Param(0)), 1);

    -- Param(u) ≤ Param(v) fails (u ≠ v, set u > v)
    assert_eq!(level_leq(KLevel.Param(0), KLevel.Param(1)), 0);

    -- Succ(u) ≤ Succ(u) (peel both succs)
    assert_eq!(level_leq(
      KLevel.Succ(store(KLevel.Param(0))),
      KLevel.Succ(store(KLevel.Param(0)))), 1);

    -- Succ(u) ≤ u fails (u+1 > u at any assignment)
    assert_eq!(level_leq(
      KLevel.Succ(store(KLevel.Param(0))),
      KLevel.Param(0)), 0);

    -- === level_leq: Param ≤ Succ reduction ===

    -- Param(u) ≤ Succ(Param(u)) (u ≤ u+1, reduces to u ≤ u)
    assert_eq!(level_leq(
      KLevel.Param(0),
      KLevel.Succ(store(KLevel.Param(0)))), 1);

    -- === level_leq: Max distribution ===

    -- max(u, v) ≤ max(u, v) (reflexivity via distribution)
    let max_uv = KLevel.Max(store(KLevel.Param(0)), store(KLevel.Param(1)));
    assert_eq!(level_leq(max_uv, max_uv), 1);

    -- u ≤ max(u, v) (try-each-branch: first branch succeeds)
    assert_eq!(level_leq(KLevel.Param(0), max_uv), 1);

    -- max(u, v) ≤ u fails (set v > u)
    assert_eq!(level_leq(max_uv, KLevel.Param(0)), 0);

    -- === level_leq: IMax case-splitting ===

    -- imax(u, v) ≤ max(u, v) (case-split on v: v=0 gives 0 ≤ max(0,0)=0; v>0 gives max=max)
    let imax_uv = KLevel.IMax(store(KLevel.Param(0)), store(KLevel.Param(1)));
    assert_eq!(level_leq(imax_uv, max_uv), 1);

    -- max(u, v) ≤ imax(u, v) fails (set v=0: max(u,0) = u but imax(u,0) = 0; take u=1)
    assert_eq!(level_leq(max_uv, imax_uv), 0);

    -- === level_leq: Succ ≤ Max with IMax child (the case-split fix) ===

    -- u+1 = max(1, imax(u+1, u)): equal for all σ
    -- σ(u)=0: 1 = max(1, imax(1,0)) = max(1,0) = 1
    -- σ(u)=n>0: n+1 = max(1, max(n+1,n)) = n+1
    -- This is the case that requires case-splitting through Max when
    -- neither branch (Succ(Zero) or IMax) alone dominates Succ(Param(u)).
    let a = KLevel.Succ(store(KLevel.Param(0)));
    let b = KLevel.Max(
      store(KLevel.Succ(store(KLevel.Zero))),
      store(KLevel.IMax(
        store(KLevel.Succ(store(KLevel.Param(0)))),
        store(KLevel.Param(0)))));
    assert_eq!(level_equal(a, b), 1);

    -- === level_equal: semantic equality ===

    -- imax(u, u) = u (when u=0: imax(0,0)=0=u; when u>0: max(u,u)=u)
    assert_eq!(level_equal(
      KLevel.IMax(store(KLevel.Param(0)), store(KLevel.Param(0))),
      KLevel.Param(0)), 1);

    -- max(u, 0) = u
    assert_eq!(level_equal(
      KLevel.Max(store(KLevel.Param(0)), store(KLevel.Zero)),
      KLevel.Param(0)), 1);

    -- level_imax reduces imax(u, 1+v) to max(u, 1+v) and imax(u, 0) to 0
    let succ_v = KLevel.Succ(store(KLevel.Param(1)));
    assert_eq!(level_eq(
      level_imax(KLevel.Param(0), succ_v),
      KLevel.Max(store(KLevel.Param(0)), store(succ_v))), 1);

    assert_eq!(level_eq(
      level_imax(KLevel.Param(0), KLevel.Zero),
      KLevel.Zero), 1);
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
        let (idx, len) = io_get_info([n_minus_1]);
        let bytes = #read_byte_stream(idx, len);
        let (const, rest) = get_constant(bytes);
        assert_eq!(rest, ByteStream.Nil);
        let bytes2 = put_constant(const, ByteStream.Nil);
        assert_eq!(blake3(bytes), blake3(bytes2));
        ixon_serde_blake3_bench(n_minus_1),
    }
  }
⟧

def ixVM : Except Aiur.Global Aiur.Toplevel := do
  let vm ← templates.merge byteStream
  let vm ← vm.merge blake3
  let vm ← vm.merge ixon
  let vm ← vm.merge ixonSerialize
  let vm ← vm.merge ixonDeserialize
  let vm ← vm.merge convert
  let vm ← vm.merge ingress
  let vm ← vm.merge kernelTypes
  let vm ← vm.merge kernel
  vm.merge entrypoints

end IxVM

end
