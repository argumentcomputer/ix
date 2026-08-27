module
public import Ix.Aiur.Meta
public import Ix.IxVM.Blake3
public import Ix.MultiStark.Verifier

/-!
# Binary recursive aggregation (aggregate-first)

The mode-1 join from `plans/aggregate-first-pipeline.md` §6: verify two proofs
of the recursion system, pin their entrypoints and transitive allowed-vk
identity, decode their `CheckEnv` statements, re-open the canonical address
sets behind their roots, and emit

`subjects = subjects_L ∪ subjects_R`

`assumptions = (assumptions_L ∪ assumptions_R) ∖ subjects`.

All address-list operations use bytewise address comparison. Pointer identity
is never used as set equality: Aiur memory constrains pointers to be unique,
not stored values to be globally deduplicated.
-/

public section

namespace MultiStark

def aggregate := ⟦
  enum JoinNextAssumption {
    Done,
    More(Addr, List‹Addr›, List‹Addr›)
  }

  /- ## Small strict byte readers

  The join only decodes fixed-width digests, u64 function indices, and the
  single-byte `CheckEnv` tag.  Keeping these readers local avoids pulling the
  full IxVM Ixon decoder (and all of its kernel-only types) into the recursion
  system.
  -/

  fn join_read_byte(stream: ByteStream) -> (U8, ByteStream) {
    let ListNode.Cons(byte, rest) = load(stream);
    (byte, rest)
  }

  fn join_read_address(stream: ByteStream) -> (Addr, ByteStream) {
    let ListNode.Cons(b0, s) = load(stream);
    let ListNode.Cons(b1, s) = load(s);
    let ListNode.Cons(b2, s) = load(s);
    let ListNode.Cons(b3, s) = load(s);
    let ListNode.Cons(b4, s) = load(s);
    let ListNode.Cons(b5, s) = load(s);
    let ListNode.Cons(b6, s) = load(s);
    let ListNode.Cons(b7, s) = load(s);
    let ListNode.Cons(b8, s) = load(s);
    let ListNode.Cons(b9, s) = load(s);
    let ListNode.Cons(b10, s) = load(s);
    let ListNode.Cons(b11, s) = load(s);
    let ListNode.Cons(b12, s) = load(s);
    let ListNode.Cons(b13, s) = load(s);
    let ListNode.Cons(b14, s) = load(s);
    let ListNode.Cons(b15, s) = load(s);
    let ListNode.Cons(b16, s) = load(s);
    let ListNode.Cons(b17, s) = load(s);
    let ListNode.Cons(b18, s) = load(s);
    let ListNode.Cons(b19, s) = load(s);
    let ListNode.Cons(b20, s) = load(s);
    let ListNode.Cons(b21, s) = load(s);
    let ListNode.Cons(b22, s) = load(s);
    let ListNode.Cons(b23, s) = load(s);
    let ListNode.Cons(b24, s) = load(s);
    let ListNode.Cons(b25, s) = load(s);
    let ListNode.Cons(b26, s) = load(s);
    let ListNode.Cons(b27, s) = load(s);
    let ListNode.Cons(b28, s) = load(s);
    let ListNode.Cons(b29, s) = load(s);
    let ListNode.Cons(b30, s) = load(s);
    let ListNode.Cons(b31, s) = load(s);
    (store([b0, b1, b2, b3, b4, b5, b6, b7,
            b8, b9, b10, b11, b12, b13, b14, b15,
            b16, b17, b18, b19, b20, b21, b22, b23,
            b24, b25, b26, b27, b28, b29, b30, b31]), s)
  }

  fn join_put_address(addr: Addr, rest: ByteStream) -> ByteStream {
    let a = load(addr);
    let s31 = store(ListNode.Cons(a[31], rest));
    let s30 = store(ListNode.Cons(a[30], s31));
    let s29 = store(ListNode.Cons(a[29], s30));
    let s28 = store(ListNode.Cons(a[28], s29));
    let s27 = store(ListNode.Cons(a[27], s28));
    let s26 = store(ListNode.Cons(a[26], s27));
    let s25 = store(ListNode.Cons(a[25], s26));
    let s24 = store(ListNode.Cons(a[24], s25));
    let s23 = store(ListNode.Cons(a[23], s24));
    let s22 = store(ListNode.Cons(a[22], s23));
    let s21 = store(ListNode.Cons(a[21], s22));
    let s20 = store(ListNode.Cons(a[20], s21));
    let s19 = store(ListNode.Cons(a[19], s20));
    let s18 = store(ListNode.Cons(a[18], s19));
    let s17 = store(ListNode.Cons(a[17], s18));
    let s16 = store(ListNode.Cons(a[16], s17));
    let s15 = store(ListNode.Cons(a[15], s16));
    let s14 = store(ListNode.Cons(a[14], s15));
    let s13 = store(ListNode.Cons(a[13], s14));
    let s12 = store(ListNode.Cons(a[12], s13));
    let s11 = store(ListNode.Cons(a[11], s12));
    let s10 = store(ListNode.Cons(a[10], s11));
    let s9 = store(ListNode.Cons(a[9], s10));
    let s8 = store(ListNode.Cons(a[8], s9));
    let s7 = store(ListNode.Cons(a[7], s8));
    let s6 = store(ListNode.Cons(a[6], s7));
    let s5 = store(ListNode.Cons(a[5], s6));
    let s4 = store(ListNode.Cons(a[4], s5));
    let s3 = store(ListNode.Cons(a[3], s4));
    let s2 = store(ListNode.Cons(a[2], s3));
    let s1 = store(ListNode.Cons(a[1], s2));
    store(ListNode.Cons(a[0], s1))
  }

  fn join_pack_address(addr: Addr) -> [G; 8] {
    let a = load(addr);
    [@b3_pack_w([a[0], a[1], a[2], a[3]]),
     @b3_pack_w([a[4], a[5], a[6], a[7]]),
     @b3_pack_w([a[8], a[9], a[10], a[11]]),
     @b3_pack_w([a[12], a[13], a[14], a[15]]),
     @b3_pack_w([a[16], a[17], a[18], a[19]]),
     @b3_pack_w([a[20], a[21], a[22], a[23]]),
     @b3_pack_w([a[24], a[25], a[26], a[27]]),
     @b3_pack_w([a[28], a[29], a[30], a[31]])]
  }

  -- `Ix.Merkle.nodeHash`: Blake3 of `0x01 ‖ left ‖ right`.
  fn join_node_hash(left: Addr, right: Addr) -> Addr {
    let tail = join_put_address(left,
      join_put_address(right, store(ListNode.Nil)));
    bytes_to_addr(store(ListNode.Cons(1u8, tail)))
  }

  -- `Ix.Merkle.leafHash`: Blake3 of `0x00 ‖ address`.
  fn join_leaf_hash(addr: Addr) -> Addr {
    let tail = join_put_address(addr, store(ListNode.Nil));
    bytes_to_addr(store(ListNode.Cons(0u8, tail)))
  }

  fn join_pack_be4(a: U8, b: U8, c: U8, d: U8) -> G {
    ((to_field(a) * 256 + to_field(b)) * 256 + to_field(c)) * 256
      + to_field(d)
  }

  -- Byte-lexicographic address order: 0 = less, 1 = equal, 2 = greater.
  -- Four-byte big-endian words stay below 2^32, so native field equality and
  -- `u32_less_than` are exact.
  fn join_address_order(a: Addr, b: Addr) -> G {
    let av = load(a);
    let bv = load(b);
    let aw0 = @join_pack_be4(av[0], av[1], av[2], av[3]);
    let bw0 = @join_pack_be4(bv[0], bv[1], bv[2], bv[3]);
    match aw0 - bw0 {
      0 =>
        let aw1 = @join_pack_be4(av[4], av[5], av[6], av[7]);
        let bw1 = @join_pack_be4(bv[4], bv[5], bv[6], bv[7]);
        match aw1 - bw1 {
          0 =>
            let aw2 = @join_pack_be4(av[8], av[9], av[10], av[11]);
            let bw2 = @join_pack_be4(bv[8], bv[9], bv[10], bv[11]);
            match aw2 - bw2 {
              0 =>
                let aw3 = @join_pack_be4(av[12], av[13], av[14], av[15]);
                let bw3 = @join_pack_be4(bv[12], bv[13], bv[14], bv[15]);
                match aw3 - bw3 {
                  0 =>
                    let aw4 = @join_pack_be4(av[16], av[17], av[18], av[19]);
                    let bw4 = @join_pack_be4(bv[16], bv[17], bv[18], bv[19]);
                    match aw4 - bw4 {
                      0 =>
                        let aw5 = @join_pack_be4(av[20], av[21], av[22], av[23]);
                        let bw5 = @join_pack_be4(bv[20], bv[21], bv[22], bv[23]);
                        match aw5 - bw5 {
                          0 =>
                            let aw6 = @join_pack_be4(av[24], av[25], av[26], av[27]);
                            let bw6 = @join_pack_be4(bv[24], bv[25], bv[26], bv[27]);
                            match aw6 - bw6 {
                              0 =>
                                let aw7 = @join_pack_be4(av[28], av[29], av[30], av[31]);
                                let bw7 = @join_pack_be4(bv[28], bv[29], bv[30], bv[31]);
                                match aw7 - bw7 {
                                  0 => 1,
                                  _ => match u32_less_than(aw7, bw7) { 1 => 0, _ => 2, },
                                },
                              _ => match u32_less_than(aw6, bw6) { 1 => 0, _ => 2, },
                            },
                          _ => match u32_less_than(aw5, bw5) { 1 => 0, _ => 2, },
                        },
                      _ => match u32_less_than(aw4, bw4) { 1 => 0, _ => 2, },
                    },
                  _ => match u32_less_than(aw3, bw3) { 1 => 0, _ => 2, },
                },
              _ => match u32_less_than(aw2, bw2) { 1 => 0, _ => 2, },
            },
          _ => match u32_less_than(aw1, bw1) { 1 => 0, _ => 2, },
        },
      _ => match u32_less_than(aw0, bw0) { 1 => 0, _ => 2, },
    }
  }

  fn join_assert_strict_sorted(leaves: List‹Addr›) {
    match load(leaves) {
      ListNode.Nil => (),
      ListNode.Cons(a, rest) =>
        match load(rest) {
          ListNode.Nil => (),
          ListNode.Cons(b, _) =>
            assert_eq!(join_address_order(a, b), 0,
              "join: tree leaves are not strictly sorted");
            join_assert_strict_sorted(rest),
        },
    }
  }

  -- Parse an `AssumptionTree` body into its in-order real leaves. Padding is
  -- omitted. The serialized shape is advice; canonical-root recomputation
  -- below binds the resulting sorted leaf set to the requested root.
  fn join_parse_tree_body(stream: ByteStream) -> (List‹Addr›, ByteStream) {
    let (tag, rest) = join_read_byte(stream);
    match tag {
      0 =>
        let (addr, stop) = join_read_address(rest);
        (store(ListNode.Cons(addr, store(ListNode.Nil))), stop),
      1 => (store(ListNode.Nil), rest),
      2 =>
        let (left, s2) = join_parse_tree_body(rest);
        let (right, stop) = join_parse_tree_body(s2);
        (list_concat(left, right), stop),
    }
  }

  fn join_leaf_hashes(leaves: List‹Addr›) -> List‹Addr› {
    match load(leaves) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(addr, rest) =>
        store(ListNode.Cons(join_leaf_hash(addr), join_leaf_hashes(rest))),
    }
  }

  -- One canonical Merkle reduction level. An odd last node is paired with
  -- the zero-address padding sentinel.
  fn join_pair_hashes(nodes: List‹Addr›) -> List‹Addr› {
    match load(nodes) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(left, rest) =>
        match load(rest) {
          ListNode.Nil =>
            let zero = store([0u8; 32]);
            store(ListNode.Cons(join_node_hash(left, zero), store(ListNode.Nil))),
          ListNode.Cons(right, tail) =>
            store(ListNode.Cons(join_node_hash(left, right), join_pair_hashes(tail))),
        },
    }
  }

  fn join_reduce_hashes(nodes: List‹Addr›) -> Addr {
    let ListNode.Cons(root, rest) = load(nodes);
    match load(rest) {
      ListNode.Nil => root,
      _ => join_reduce_hashes(join_pair_hashes(nodes)),
    }
  }

  fn join_canonical_root(leaves: List‹Addr›) -> Addr {
    join_reduce_hashes(join_leaf_hashes(leaves))
  }

  fn join_load_canonical_tree(root: Addr) -> List‹Addr› {
    let raw = load(root);
    let (idx, len) = io_get_info(5, raw);
    let bytes = #read_byte_stream(5, idx, len);
    let (tag, body) = join_read_byte(bytes);
    assert_eq!(tag, 0xE2u8, "join: tree has the wrong Ixon tag");
    let (leaves, stop) = join_parse_tree_body(body);
    assert_eq!(load(stop), ListNode.Nil,
      "join: trailing bytes after AssumptionTree");
    assert_eq!(list_is_empty(leaves), 0,
      "join: a present tree must contain at least one leaf");
    join_assert_strict_sorted(leaves);
    let expected = join_canonical_root(leaves);
    assert_eq!(address_eq(expected, root), 1,
      "join: tree leaves do not reproduce the canonical root");
    leaves
  }

  fn join_load_optional_tree(root: Option‹Addr›) -> List‹Addr› {
    match root {
      Option.None => store(ListNode.Nil),
      Option.Some(addr) => join_load_canonical_tree(addr),
    }
  }

  fn join_assert_same_list(left: List‹Addr›, right: List‹Addr›) {
    match (load(left), load(right)) {
      (ListNode.Nil, ListNode.Nil) => (),
      (ListNode.Cons(a, ar), ListNode.Cons(b, br)) =>
        assert_eq!(address_eq(a, b), 1, "join: set element mismatch");
        join_assert_same_list(ar, br),
    }
  }

  -- Assert `output` is the sorted, deduplicated union of two sorted unique
  -- inputs. The merge is linear in the number of leaves.
  fn join_assert_union(left: List‹Addr›, right: List‹Addr›,
      output: List‹Addr›) {
    match (load(left), load(right)) {
      (ListNode.Nil, _) => join_assert_same_list(right, output),
      (_, ListNode.Nil) => join_assert_same_list(left, output),
      (ListNode.Cons(a, ar), ListNode.Cons(b, br)) =>
        let ListNode.Cons(o, or) = load(output);
        match join_address_order(a, b) {
          0 =>
            assert_eq!(address_eq(a, o), 1, "join: subject union mismatch");
            join_assert_union(ar, right, or),
          1 =>
            assert_eq!(address_eq(a, o), 1, "join: subject union mismatch");
            join_assert_union(ar, br, or),
          _ =>
            assert_eq!(address_eq(b, o), 1, "join: subject union mismatch");
            join_assert_union(left, br, or),
        },
    }
  }

  -- Select the next unique value from the union of two sorted assumption
  -- lists, returning the unconsumed tails.
  fn join_next_assumption(left: List‹Addr›, right: List‹Addr›)
      -> JoinNextAssumption {
    match (load(left), load(right)) {
      (ListNode.Nil, ListNode.Nil) => JoinNextAssumption.Done,
      (ListNode.Cons(a, ar), ListNode.Nil) =>
        JoinNextAssumption.More(a, ar, right),
      (ListNode.Nil, ListNode.Cons(b, br)) =>
        JoinNextAssumption.More(b, left, br),
      (ListNode.Cons(a, ar), ListNode.Cons(b, br)) =>
        match join_address_order(a, b) {
          0 => JoinNextAssumption.More(a, ar, right),
          1 => JoinNextAssumption.More(a, ar, br),
          _ => JoinNextAssumption.More(b, left, br),
        },
    }
  }

  -- Find `target` in a sorted subject list, discarding subject values below it
  -- and returning the suffix useful for the next (strictly larger) target.
  fn join_seek_subject(target: Addr, subjects: List‹Addr›)
      -> (G, List‹Addr›) {
    match load(subjects) {
      ListNode.Nil => (0, subjects),
      ListNode.Cons(subject, rest) =>
        match join_address_order(subject, target) {
          0 => join_seek_subject(target, rest),
          1 => (1, rest),
          _ => (0, subjects),
        },
    }
  }

  -- Assert `output = (left ∪ right) ∖ subjects`, all lists sorted and
  -- duplicate-free. Subject scan state is threaded so the check is linear.
  fn join_assert_difference(left: List‹Addr›, right: List‹Addr›,
      subjects: List‹Addr›, output: List‹Addr›) {
    match join_next_assumption(left, right) {
      JoinNextAssumption.Done =>
        assert_eq!(load(output), ListNode.Nil,
          "join: output has an extra assumption");
        (),
      JoinNextAssumption.More(candidate, left_rest, right_rest) =>
        let (discharged, subject_rest) = join_seek_subject(candidate, subjects);
        match discharged {
          1 => join_assert_difference(left_rest, right_rest, subject_rest, output),
          _ =>
            let ListNode.Cons(actual, output_rest) = load(output);
            assert_eq!(address_eq(candidate, actual), 1,
              "join: outstanding assumption mismatch");
            join_assert_difference(left_rest, right_rest, subject_rest, output_rest),
        },
    }
  }

  fn join_get_opt_address(stream: ByteStream) -> (Option‹Addr›, ByteStream) {
    let (tag, rest) = join_read_byte(stream);
    match tag {
      0 => (Option.None, rest),
      1 =>
        let (addr, stop) = join_read_address(rest);
        (Option.Some(addr), stop),
    }
  }

  -- Strictly decode one complete `Claim::CheckEnv` byte string.
  fn join_parse_check_env(bytes: ByteStream) -> (Addr, Option‹Addr›) {
    let (tag, s) = join_read_byte(bytes);
    assert_eq!(tag, 0xE5u8, "join: child claim is not CheckEnv");
    let (root, s2) = join_read_address(s);
    let (assumptions, stop) = join_get_opt_address(s2);
    assert_eq!(load(stop), ListNode.Nil,
      "join: trailing bytes after CheckEnv claim");
    (root, assumptions)
  }

  /- ## Digest-bound advice and outer-claim decoding -/

  fn join_load_preimage(digest: [G; 8]) -> ByteStream {
    let (idx, len) = io_get_info(4, digest);
    let bytes = #read_byte_stream(4, idx, len);
    assert_eq!(@b3_pack(@blake3(bytes)), digest,
      "join: claim preimage digest mismatch");
    bytes
  }

  fn join_claim_field(claim: List‹U64›, index: G) -> G {
    @gl_val(list_lookup(claim, index))
  }

  fn join_claim_digest(claim: List‹U64›, start: G) -> [G; 8] {
    [join_claim_field(claim, start),
     join_claim_field(claim, start + 1),
     join_claim_field(claim, start + 2),
     join_claim_field(claim, start + 3),
     join_claim_field(claim, start + 4),
     join_claim_field(claim, start + 5),
     join_claim_field(claim, start + 6),
     join_claim_field(claim, start + 7)]
  }

  fn join_assert_digest(actual: [G; 8], expected: [G; 8]) {
    assert_eq!(actual[0], expected[0]);
    assert_eq!(actual[1], expected[1]);
    assert_eq!(actual[2], expected[2]);
    assert_eq!(actual[3], expected[3]);
    assert_eq!(actual[4], expected[4]);
    assert_eq!(actual[5], expected[5]);
    assert_eq!(actual[6], expected[6]);
    assert_eq!(actual[7], expected[7]);
    ()
  }

  fn join_only_claim(claims: List‹List‹U64››) -> List‹U64› {
    let ListNode.Cons(claim, rest) = load(claims);
    assert_eq!(load(rest), ListNode.Nil,
      "join: child proof must expose exactly one claim");
    claim
  }

  -- Verify one recursive child against the already-bound recursion system.
  -- Child claims need no standalone public digest: the verified proof's lookup
  -- accumulator and Fiat-Shamir transcript bind `cbytes` directly.
  fn join_verify_child(sys: Sys, key: G) -> List‹List‹U64›› {
    let (idx, len) = io_get_info(0, [key]);
    let (proof, stop) = @read_proof(idx);
    assert_eq!(stop, idx + len);
    let (cidx, clen) = io_get_info(2, [key]);
    let cbytes = #read_byte_stream(2, cidx, clen);
    let (claims, crest) = @read_claims(cbytes);
    assert_eq!(load(crest), ListNode.Nil);
    assert_eq!(@verify(proof), 1);
    assert_eq!(@ood_verify(sys, proof, claims, cbytes), 1);
    claims
  }

  -- Open the IxVM claim nested under a lift's claims digest.
  fn join_decode_lift_claim(outer: List‹U64›, verify_claim_idx: G)
      -> (Addr, Option‹Addr›) {
    let claims_digest = join_claim_digest(outer, 10);
    let claims_bytes = join_load_preimage(claims_digest);
    let (inner_claims, rest) = @read_claims(claims_bytes);
    assert_eq!(load(rest), ListNode.Nil);
    let inner = join_only_claim(inner_claims);
    assert_eq!(list_length(inner), 10,
      "join: IxVM lift must expose a 10-word verify_claim claim");
    assert_eq!(join_claim_field(inner, 0), 0,
      "join: IxVM child has the wrong claim channel");
    assert_eq!(join_claim_field(inner, 1), verify_claim_idx,
      "join: IxVM child has the wrong entrypoint");
    let check_env_digest = join_claim_digest(inner, 2);
    join_parse_check_env(join_load_preimage(check_env_digest))
  }

  -- Decode a verified child as either a lift or a transitive join. Function
  -- indices live in the digest-bound allowed blob because Source programs have
  -- no primitive for materializing their compiler-assigned numeric index.
  fn join_decode_child(outer_claims: List‹List‹U64››,
      ixvm_vk_digest: [G; 8], allowed_digest: [G; 8],
      verify_claim_idx: G, lift_idx: G, join_idx: G)
      -> (Addr, Option‹Addr›) {
    let outer = join_only_claim(outer_claims);
    assert_eq!(list_length(outer), 18,
      "join: recursive child claim must contain 16 public inputs");
    assert_eq!(join_claim_field(outer, 0), 0,
      "join: recursive child has the wrong claim channel");
    let child_idx = join_claim_field(outer, 1);
    match eq_zero(child_idx - lift_idx) {
      1 =>
        join_assert_digest(join_claim_digest(outer, 2), ixvm_vk_digest);
        join_decode_lift_claim(outer, verify_claim_idx),
      _ =>
        assert_eq!(child_idx, join_idx,
          "join: child is neither lift nor join");
        join_assert_digest(join_claim_digest(outer, 2), allowed_digest);
        let output_digest = join_claim_digest(outer, 10);
        join_parse_check_env(join_load_preimage(output_digest)),
    }
  }

  /- ## Canonical set-discharge join -/

  -- Verify two lift/join proofs and emit the canonical union/difference of their
  -- `CheckEnv` statements. Public input is
  -- `blake3(allowed_blob) ‖ blake3(output_claim_bytes)`, packed four bytes per
  -- Goldilocks element.
  pub fn join_two(allowed_digest: [G; 8], out_claim_digest: [G; 8]) {
    -- Allowed blob:
    --   ixvm_vk_digest(32) ‖ verify_claim_idx(u64 LE) ‖
    --   recursion_vk_digest(32) ‖ lift_idx(u64 LE) ‖ join_idx(u64 LE).
    let (aidx, alen) = io_get_info(3, [0]);
    let allowed_bytes = #read_byte_stream(3, aidx, alen);
    assert_eq!(@b3_pack(@blake3(allowed_bytes)), allowed_digest,
      "join: allowed blob digest mismatch");
    let (ixvm_digest_addr, as1) = join_read_address(allowed_bytes);
    let (verify_idx_limb, as2) = @read_u64(as1);
    let (rec_digest_addr, as3) = join_read_address(as2);
    let (lift_idx_limb, as4) = @read_u64(as3);
    let (join_idx_limb, astop) = @read_u64(as4);
    assert_eq!(load(astop), ListNode.Nil,
      "join: allowed blob must be exactly 88 bytes");
    let ixvm_vk_digest = join_pack_address(ixvm_digest_addr);
    let rec_vk_digest = join_pack_address(rec_digest_addr);
    let verify_claim_idx = flatten_u64(verify_idx_limb);
    let lift_idx = flatten_u64(lift_idx_limb);
    let join_idx = flatten_u64(join_idx_limb);

    -- Deserialize and bind this recursion system's vk once; both children
    -- verify against the same system.
    let (sidx, slen) = io_get_info(1, [0]);
    let sbytes = #read_byte_stream(1, sidx, slen);
    assert_eq!(@b3_pack(@blake3(sbytes)), rec_vk_digest,
      "join: recursion vk digest mismatch");
    let (sys, srest) = @read_system(sbytes);
    assert_eq!(load(srest), ListNode.Nil);

    let left_claims = join_verify_child(sys, 0);
    let right_claims = join_verify_child(sys, 1);
    let (left_root, left_asm) = join_decode_child(left_claims,
      ixvm_vk_digest, allowed_digest, verify_claim_idx, lift_idx, join_idx);
    let (right_root, right_asm) = join_decode_child(right_claims,
      ixvm_vk_digest, allowed_digest, verify_claim_idx, lift_idx, join_idx);

    -- Bind and decode the current join's output claim.
    let (oidx, olen) = io_get_info(2, [2]);
    let output_bytes = #read_byte_stream(2, oidx, olen);
    assert_eq!(@b3_pack(@blake3(output_bytes)), out_claim_digest,
      "join: output claim digest mismatch");
    let (output_root, output_asm) = join_parse_check_env(output_bytes);

    let left_subjects = join_load_canonical_tree(left_root);
    let right_subjects = join_load_canonical_tree(right_root);
    let left_assumptions = join_load_optional_tree(left_asm);
    let right_assumptions = join_load_optional_tree(right_asm);
    let output_subjects = join_load_canonical_tree(output_root);
    let output_assumptions = join_load_optional_tree(output_asm);

    join_assert_union(left_subjects, right_subjects, output_subjects);
    join_assert_difference(left_assumptions, right_assumptions,
      output_subjects, output_assumptions);
    ()
  }
⟧

end MultiStark

end
