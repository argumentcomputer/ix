module
public import Ix.Aiur.Meta
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
public import Ix.IxVM.Blake3
public import Ix.IxVM.RBTreeMap
public import Ix.IxVM.Ixon
public import Ix.IxVM.IxonSerialize
public import Ix.IxVM.IxonDeserialize
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel.Klimbs
public import Ix.IxVM.Kernel.NatPrim
public import Ix.IxVM.Convert
public import Ix.IxVM.Ingress
public import Ix.IxVM.Kernel.Levels
public import Ix.IxVM.Kernel.Subst
public import Ix.IxVM.Kernel.Whnf
public import Ix.IxVM.Kernel.InferOnly
public import Ix.IxVM.Kernel.DefEq
public import Ix.IxVM.Kernel.Infer
public import Ix.IxVM.Kernel.CanonicalCheck
public import Ix.IxVM.Kernel.Check
public import Ix.IxVM.Kernel.Claim

public section

namespace IxVM

def entrypoints := ⟦
  -- Check entrypoint. Loads the constant at `addr_bytes` and typechecks
  -- it via run_check. Refs discovered during the check fault lazily via
  -- get_ci rather than being walked up front.
  --
  -- Checks the constant AT `addr_bytes` and nothing else: its refs are
  -- ingressed and get_ci'd for their declared types, but are not
  -- themselves checked. For the transitive discipline use `verify_claim`
  -- with a Check or CheckEnv claim.
  pub fn verify_check(addr_bytes: [U8; 32]) {
    run_check(store(addr_bytes));
  }

  -- CheckEnv entrypoint. Parses the env tree at `root_bytes` (ch 1),
  -- checks every leaf via run_check. Faults constants lazily via
  -- get_ci; shared subterms across leaves ingressed once (memoized).
  pub fn verify_check_env(root_bytes: [U8; 32]) {
    run_check_env(store(root_bytes), Option.None);
  }

  /- # Test entrypoints. These exercise shared infrastructure — the Ixon
     serde round-trip and the level comparator — rather than the
     typechecker proper, and are pruned out of the production `ixVM`
     toplevel below. -/

  pub fn ixon_serde_test(n: G) {
    match n {
      0 => (),
      _ =>
        let n_minus_1 = n - 1;
        let (idx, len) = io_get_info(0, [n_minus_1]);
        let bytes = #read_byte_stream(0, idx, len);
        let (const, rest) = get_constant(bytes);
        assert_eq!(load(rest), ListNode.Nil,
          "ixon deserialization left trailing bytes");
        let bytes2 = put_constant(const, store(ListNode.Nil));
        assert_eq!(bytes, bytes2,
          "ixon round-trip: re-serialized bytes differ from the input");
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
    assert_eq!(level_leq(zero, p0), 1, "level_leq: 0 <= u must hold");

    -- Param(u) ≤ Param(u) (reflexivity)
    assert_eq!(level_leq(p0, p0), 1, "level_leq: u <= u must hold (reflexivity)");

    -- Param(u) ≤ Param(v) fails (u ≠ v, set u > v)
    assert_eq!(level_leq(p0, p1), 0,
      "level_leq: distinct params must not compare <=");

    -- Succ(u) ≤ Succ(u) (peel both succs)
    assert_eq!(level_leq(succ_p0, succ_p0), 1,
      "level_leq: u+1 <= u+1 must hold (peel both succs)");

    -- Succ(u) ≤ u fails (u+1 > u at any assignment)
    assert_eq!(level_leq(succ_p0, p0), 0,
      "level_leq: u+1 <= u must fail at every assignment");

    -- Param(u) ≤ Succ(Param(u)) (u ≤ u+1)
    assert_eq!(level_leq(p0, succ_p0), 1, "level_leq: u <= u+1 must hold");

    -- max(u, v) ≤ max(u, v) (reflexivity via distribution)
    let max_uv = store(KLevelNode.Max(p0, p1));
    assert_eq!(level_leq(max_uv, max_uv), 1,
      "level_leq: max(u,v) <= max(u,v) must hold (reflexivity via distribution)");

    -- u ≤ max(u, v)
    assert_eq!(level_leq(p0, max_uv), 1, "level_leq: u <= max(u,v) must hold");

    -- max(u, v) ≤ u fails
    assert_eq!(level_leq(max_uv, p0), 0, "level_leq: max(u,v) <= u must fail");

    -- imax(u, v) ≤ max(u, v)
    let imax_uv = store(KLevelNode.IMax(p0, p1));
    assert_eq!(level_leq(imax_uv, max_uv), 1,
      "level_leq: imax(u,v) <= max(u,v) must hold");

    -- max(u, v) ≤ imax(u, v) fails
    assert_eq!(level_leq(max_uv, imax_uv), 0,
      "level_leq: max(u,v) <= imax(u,v) must fail");

    -- u+1 = max(1, imax(u+1, u)): equal for all σ (case-split fix)
    let a = succ_p0;
    let b = store(KLevelNode.Max(
      succ_zero,
      store(KLevelNode.IMax(succ_p0, p0))));
    assert_eq!(level_equal(a, b), 1,
      "level_equal: u+1 = max(1, imax(u+1, u)) must hold at every assignment");

    -- imax(u, u) = u
    assert_eq!(level_equal(store(KLevelNode.IMax(p0, p0)), p0), 1,
      "level_equal: imax(u,u) = u must hold");

    -- max(u, 0) = u
    assert_eq!(level_equal(store(KLevelNode.Max(p0, zero)), p0), 1,
      "level_equal: max(u,0) = u must hold");

    -- level_imax reduces imax(u, 1+v) to max(u, 1+v) and imax(u, 0) to 0
    let succ_v = store(KLevelNode.Succ(p1));
    assert_eq!(level_eq(
      level_imax(p0, succ_v),
      store(KLevelNode.Max(p0, succ_v))), 1,
      "level_imax must reduce imax(u, 1+v) to max(u, 1+v)");

    assert_eq!(level_eq(
      level_imax(p0, zero),
      zero), 1,
      "level_imax must reduce imax(u, 0) to 0");
  }

  pub fn kernel_unit_tests() {
    level_cmp_tests()
  }

  -- Subject-only typecheck. DEBUG entrypoint, NOT a claim: checks
  -- `addr_bytes` alone and trusts its transitive deps (they are
  -- get_ci'd for their declared types but never checked). Used by the
  -- kernel-arena fixtures, where the
  -- per-fixture speed matters (shared deps would otherwise be
  -- revalidated once per fixture) and where a `bad_*` rejection must
  -- be attributable to the SUBJECT rather than to a dep.
  --
  -- Verifier policy must never accept this funcidx as a production
  -- claim — it carries no claim digest and no assumption discipline.
  -- Body is deliberately identical to `verify_check`: the two exist as
  -- separate funcidxs precisely so policy can accept one and reject the
  -- other.
  pub fn verify_const(addr_bytes: [U8; 32]) {
    run_check(store(addr_bytes));
  }

  -- Claim-discipline entrypoint — the coverage-bearing production
  -- entrypoint. Loads the claim bytes at ch 0 keyed by `claim_digest`,
  -- blake3-binds them against that key (so the public input pins which
  -- claim was proved), then dispatches on the claim variant: Check,
  -- CheckEnv, Reveal, and Contains. See `run_claim` for the
  -- per-variant discipline.
  -- The digest is public input as 8 field elements of 4 packed LE bytes
  -- (injective in Goldilocks; 8 input columns instead of 32) — the same
  -- representation the recursive verifier's entrypoint uses.
  pub fn verify_claim(claim_digest: [G; 8]) {
    run_claim(claim_digest);
  }

  -- Per-block warmup entrypoint for the shared-record executor: checks
  -- the constant at `addr_bytes` through the same shape-dispatched
  -- gauntlet a CheckEnv walk applies per node (`check_node`: the Muts
  -- member gauntlet for mutual blocks, `run_check` otherwise). Workers
  -- execute one of these per schedule block IN PARALLEL; the segment's
  -- single CheckEnv claim then walks the owned tree and memo-hits
  -- every node's work, so the ownership/assumption discipline executes
  -- once per segment instead of once per batch.
  --
  -- POLICY: like `verify_const`, a `verify_block` claim alone attests
  -- a per-node check that trusts dependency TYPES via `get_ci` — it
  -- carries no walk discipline. It exists in the production toplevel
  -- because every externally-invoked entry must be claimed for the
  -- witness to balance. Env coverage rests SOLELY on `verify_claim`
  -- CheckEnv claims; verifiers must treat `verify_block` claims as
  -- execution plumbing, never as coverage.
  pub fn verify_block(addr_bytes: [U8; 32]) {
    check_node(store(addr_bytes));
  }

⟧

open IxVM (core byteStream blake3 rbTreeMap ixon ixonSerialize ixonDeserialize)

/-- The full IxVM kernel toplevel: shared modules (core, ixon, blake3, …)
    merged with the kernel-specific `kernelTypes`, `convert`, `ingress`,
    and `entrypoints`. Carries the test and benchmark entrypoints too;
    `ixVM` below is the pruned production toplevel. -/
def ixVMFull : Except Aiur.Global Aiur.Source.Toplevel := do
  let vm ← core.merge byteStream
  let vm ← vm.merge blake3
  let vm ← vm.merge rbTreeMap
  let vm ← vm.merge ixon
  let vm ← vm.merge ixonSerialize
  let vm ← vm.merge ixonDeserialize
  let vm ← vm.merge kernelTypes
  let vm ← vm.merge klimbs
  let vm ← vm.merge natPrim
  let vm ← vm.merge convert
  let vm ← vm.merge ingress
  let vm ← vm.merge levels
  let vm ← vm.merge subst
  let vm ← vm.merge whnf
  let vm ← vm.merge inferOnly
  let vm ← vm.merge defEq
  let vm ← vm.merge infer
  let vm ← vm.merge canonicalCheck
  let vm ← vm.merge check
  let vm ← vm.merge claim
  vm.merge entrypoints

/-- Pruned production toplevel: `verify_claim` plus the executor's
    `verify_block` warmup entry, and nothing else.

    `verify_const` / `verify_check` / `verify_check_env` are DEBUG
    entrypoints that trust their dependencies instead of walking them, so
    a proof made with one attests far less than a claim does. Keeping
    them here put them in the same verifying key as `verify_claim`,
    leaving `ix verify`'s funcIdx check as the only thing standing
    between a debug proof and acceptance — a policy, enforced in one
    place, with no test asserting it, and no policy at all in the
    recursive verifier.

    Pruning them makes it structural: under the production VK such a
    proof cannot exist. Callers that genuinely want a subject-only check
    build `ixVMFull` and are thereby using a different VK, which is the
    honest signal.

    `verify_block` is the one deliberate exception: the shared-record
    executor invokes it per schedule block to warm the record, and every
    invoked entry must appear in the proof's claim list for the witness
    to balance — so it must live under the production VK. It shares
    `verify_const`'s weak trust shape, and the same policy discipline
    applies at the claim-list level instead of the VK level: coverage
    verdicts come from CheckEnv `verify_claim` claims ONLY, and a
    `verify_block` claim is accepted merely as execution plumbing
    alongside them. -/
def ixVM : Except Aiur.Global Aiur.Source.Toplevel := do
  let vm ← ixVMFull
  pure (vm.prune [`verify_claim, `verify_block])

end IxVM

end
