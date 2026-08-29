module
public import Ix.Aiur.Meta
public import Ix.IxVM.Blake3
public import Ix.MultiStark.Verifier

/-!
# Heterogeneous recursive aggregation circuit

One entrypoint, `ix_aggr`, subsumes wrapping and joining. A non-deterministic
shape hint (IO channel 6) selects one of ten verified forms:

| shape | children                  | statement fold                          |
|-------|---------------------------|-----------------------------------------|
| 0     | one IxVM proof            | pass-through (wrap)                     |
| 1     | one `ix_aggr` proof       | pass-through (wrap)                     |
| 2     | IxVM, IxVM                | union / difference                      |
| 3     | IxVM, `ix_aggr`           | union / difference                      |
| 4     | `ix_aggr`, IxVM           | union / difference                      |
| 5     | `ix_aggr`, `ix_aggr`      | union / difference                      |
| 6     | IxVM, IxVM                | structural root / path discharge        |
| 7     | IxVM, `ix_aggr`           | structural root / path discharge        |
| 8     | `ix_aggr`, IxVM           | structural root / path discharge        |
| 9     | `ix_aggr`, `ix_aggr`      | structural root / path discharge        |

The hint is advice, not trust: every shape verifies its children against the
verifying key demanded by that shape (digest-bound to the allowed blob) and
then demands that shape's exact claim layout, so a wrong hint fails either the
proof verification or a digest/shape assertion.

The public statement is uniform across all shapes:

`blake3(allowed_blob) ‖ blake3(output CheckEnv claim bytes)`,

packed four bytes per Goldilocks element. The 80-byte allowed blob is

`blake3(ixvm vk) ‖ verify_claim idx (u64 LE) ‖ blake3(self vk) ‖ ix_aggr idx
(u64 LE)`

and is carried unchanged by every node of an aggregation tree: a parent
asserts its `ix_aggr` children bind the *same* allowed digest, which pins both
verifying keys and both entrypoint indices transitively. The indices must be
explicit because the Source DSL cannot materialize its compiler-assigned
function index inside a circuit.

Child claims normalize to one `CheckEnv` statement each:

* IxVM child — 10-word `verify_claim` claim `[0, verify_idx, digest(8)]`,
  where the digest packs `blake3` of the serialized `CheckEnv` claim.
* `ix_aggr` child — 18-word claim `[0, aggr_idx, allowed(8), digest(8)]`.

Wrap shapes bind the output digest to the child's `CheckEnv` digest directly
and open nothing. Flat pair shapes open both `CheckEnv` preimages (channel 4),
re-root the canonical subject/assumption trees (channel 5), and prove

`subjects = subjects_L ∪ subjects_R`

`assumptions = (assumptions_L ∪ assumptions_R) ∖ subjects`.

Structural pair shapes instead bind
`subjects = nodeHash(subjects_L.root, subjects_R.root)` and account for every
input assumption by either carrying it into the canonical output assumptions
or discharging it with a strict Merkle inclusion path on channel 6.

All address-list operations use bytewise address comparison. Pointer identity
is never used as set equality: Aiur memory constrains pointers to be unique,
not stored values to be globally deduplicated.

## IO channels

| channel | key                  | payload                                  |
|---------|----------------------|------------------------------------------|
| 0       | `[0]` / `[1]`        | child proof bytes                        |
| 1       | `[kind]`             | vk bytes (0 = IxVM, 1 = self)            |
| 2       | `[0]` / `[1]`, `[2]` | child claims; output claim bytes         |
| 3       | `[0]`                | 80-byte allowed blob                     |
| 4       | packed digest        | `CheckEnv` claim preimages               |
| 5       | raw 32-byte root     | serialized canonical `AssumptionTree`s   |
| 6       | `[0]` / address      | shape byte (0–9) / structural path choice |
-/

public section

namespace Aggr

def circuit := ⟦
  enum AggrNextAssumption {
    Done,
    More(Addr, List‹Addr›, List‹Addr›)
  }

  /- ## Small strict byte readers

  The aggregator only decodes fixed-width digests, u64 function indices, and
  single-byte tags.  Keeping these readers local avoids pulling the full IxVM
  Ixon decoder (and all of its kernel-only types) into the recursion system.
  -/

  fn aggr_read_byte(stream: ByteStream) -> (U8, ByteStream) {
    let ListNode.Cons(byte, rest) = load(stream);
    (byte, rest)
  }

  fn aggr_read_address(stream: ByteStream) -> (Addr, ByteStream) {
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

  fn aggr_put_address(addr: Addr, rest: ByteStream) -> ByteStream {
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

  fn aggr_pack_address(addr: Addr) -> [G; 8] {
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
  fn aggr_node_hash(left: Addr, right: Addr) -> Addr {
    let tail = aggr_put_address(left,
      aggr_put_address(right, store(ListNode.Nil)));
    bytes_to_addr(store(ListNode.Cons(1u8, tail)))
  }

  -- `Ix.Merkle.leafHash`: Blake3 of `0x00 ‖ address`.
  fn aggr_leaf_hash(addr: Addr) -> Addr {
    let tail = aggr_put_address(addr, store(ListNode.Nil));
    bytes_to_addr(store(ListNode.Cons(0u8, tail)))
  }

  fn aggr_pack_be4(a: U8, b: U8, c: U8, d: U8) -> G {
    ((to_field(a) * 256 + to_field(b)) * 256 + to_field(c)) * 256
      + to_field(d)
  }

  -- Byte-lexicographic address order: 0 = less, 1 = equal, 2 = greater.
  -- Four-byte big-endian words stay below 2^32, so native field equality and
  -- `u32_less_than` are exact.
  fn aggr_address_order(a: Addr, b: Addr) -> G {
    let av = load(a);
    let bv = load(b);
    let aw0 = @aggr_pack_be4(av[0], av[1], av[2], av[3]);
    let bw0 = @aggr_pack_be4(bv[0], bv[1], bv[2], bv[3]);
    match aw0 - bw0 {
      0 =>
        let aw1 = @aggr_pack_be4(av[4], av[5], av[6], av[7]);
        let bw1 = @aggr_pack_be4(bv[4], bv[5], bv[6], bv[7]);
        match aw1 - bw1 {
          0 =>
            let aw2 = @aggr_pack_be4(av[8], av[9], av[10], av[11]);
            let bw2 = @aggr_pack_be4(bv[8], bv[9], bv[10], bv[11]);
            match aw2 - bw2 {
              0 =>
                let aw3 = @aggr_pack_be4(av[12], av[13], av[14], av[15]);
                let bw3 = @aggr_pack_be4(bv[12], bv[13], bv[14], bv[15]);
                match aw3 - bw3 {
                  0 =>
                    let aw4 = @aggr_pack_be4(av[16], av[17], av[18], av[19]);
                    let bw4 = @aggr_pack_be4(bv[16], bv[17], bv[18], bv[19]);
                    match aw4 - bw4 {
                      0 =>
                        let aw5 = @aggr_pack_be4(av[20], av[21], av[22], av[23]);
                        let bw5 = @aggr_pack_be4(bv[20], bv[21], bv[22], bv[23]);
                        match aw5 - bw5 {
                          0 =>
                            let aw6 = @aggr_pack_be4(av[24], av[25], av[26], av[27]);
                            let bw6 = @aggr_pack_be4(bv[24], bv[25], bv[26], bv[27]);
                            match aw6 - bw6 {
                              0 =>
                                let aw7 = @aggr_pack_be4(av[28], av[29], av[30], av[31]);
                                let bw7 = @aggr_pack_be4(bv[28], bv[29], bv[30], bv[31]);
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

  fn aggr_assert_strict_sorted(leaves: List‹Addr›) {
    match load(leaves) {
      ListNode.Nil => (),
      ListNode.Cons(a, rest) =>
        match load(rest) {
          ListNode.Nil => (),
          ListNode.Cons(b, _) =>
            assert_eq!(aggr_address_order(a, b), 0,
              "aggr: tree leaves are not strictly sorted");
            aggr_assert_strict_sorted(rest),
        },
    }
  }

  -- Parse an `AssumptionTree` body into its in-order real leaves. Padding is
  -- omitted. The serialized shape is advice; canonical-root recomputation
  -- below binds the resulting sorted leaf set to the requested root.
  fn aggr_parse_tree_body(stream: ByteStream) -> (List‹Addr›, ByteStream) {
    let (tag, rest) = aggr_read_byte(stream);
    match tag {
      0 =>
        let (addr, stop) = aggr_read_address(rest);
        (store(ListNode.Cons(addr, store(ListNode.Nil))), stop),
      1 => (store(ListNode.Nil), rest),
      2 =>
        let (left, s2) = aggr_parse_tree_body(rest);
        let (right, stop) = aggr_parse_tree_body(s2);
        (list_concat(left, right), stop),
    }
  }

  fn aggr_leaf_hashes(leaves: List‹Addr›) -> List‹Addr› {
    match load(leaves) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(addr, rest) =>
        store(ListNode.Cons(aggr_leaf_hash(addr), aggr_leaf_hashes(rest))),
    }
  }

  -- One canonical Merkle reduction level. An odd last node is paired with
  -- the zero-address padding sentinel.
  fn aggr_pair_hashes(nodes: List‹Addr›) -> List‹Addr› {
    match load(nodes) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(left, rest) =>
        match load(rest) {
          ListNode.Nil =>
            let zero = store([0u8; 32]);
            store(ListNode.Cons(aggr_node_hash(left, zero), store(ListNode.Nil))),
          ListNode.Cons(right, tail) =>
            store(ListNode.Cons(aggr_node_hash(left, right), aggr_pair_hashes(tail))),
        },
    }
  }

  fn aggr_reduce_hashes(nodes: List‹Addr›) -> Addr {
    let ListNode.Cons(root, rest) = load(nodes);
    match load(rest) {
      ListNode.Nil => root,
      _ => aggr_reduce_hashes(aggr_pair_hashes(nodes)),
    }
  }

  fn aggr_canonical_root(leaves: List‹Addr›) -> Addr {
    aggr_reduce_hashes(aggr_leaf_hashes(leaves))
  }

  fn aggr_load_canonical_tree(root: Addr) -> List‹Addr› {
    let raw = load(root);
    let (idx, len) = io_get_info(5, raw);
    let bytes = #read_byte_stream(5, idx, len);
    let (tag, body) = aggr_read_byte(bytes);
    assert_eq!(tag, 0xE2u8, "aggr: tree has the wrong Ixon tag");
    let (leaves, stop) = aggr_parse_tree_body(body);
    assert_eq!(load(stop), ListNode.Nil,
      "aggr: trailing bytes after AssumptionTree");
    assert_eq!(list_is_empty(leaves), 0,
      "aggr: a present tree must contain at least one leaf");
    aggr_assert_strict_sorted(leaves);
    let expected = aggr_canonical_root(leaves);
    assert_eq!(address_eq(expected, root), 1,
      "aggr: tree leaves do not reproduce the canonical root");
    leaves
  }

  fn aggr_load_optional_tree(root: Option‹Addr›) -> List‹Addr› {
    match root {
      Option.None => store(ListNode.Nil),
      Option.Some(addr) => aggr_load_canonical_tree(addr),
    }
  }

  fn aggr_assert_same_list(left: List‹Addr›, right: List‹Addr›) {
    match (load(left), load(right)) {
      (ListNode.Nil, ListNode.Nil) => (),
      (ListNode.Cons(a, ar), ListNode.Cons(b, br)) =>
        assert_eq!(address_eq(a, b), 1, "aggr: set element mismatch");
        aggr_assert_same_list(ar, br),
    }
  }

  -- Assert `output` is the sorted, deduplicated union of two sorted unique
  -- inputs. The merge is linear in the number of leaves.
  fn aggr_assert_union(left: List‹Addr›, right: List‹Addr›,
      output: List‹Addr›) {
    match (load(left), load(right)) {
      (ListNode.Nil, _) => aggr_assert_same_list(right, output),
      (_, ListNode.Nil) => aggr_assert_same_list(left, output),
      (ListNode.Cons(a, ar), ListNode.Cons(b, br)) =>
        let ListNode.Cons(o, or) = load(output);
        match aggr_address_order(a, b) {
          0 =>
            assert_eq!(address_eq(a, o), 1, "aggr: subject union mismatch");
            aggr_assert_union(ar, right, or),
          1 =>
            assert_eq!(address_eq(a, o), 1, "aggr: subject union mismatch");
            aggr_assert_union(ar, br, or),
          _ =>
            assert_eq!(address_eq(b, o), 1, "aggr: subject union mismatch");
            aggr_assert_union(left, br, or),
        },
    }
  }

  -- Select the next unique value from the union of two sorted assumption
  -- lists, returning the unconsumed tails.
  fn aggr_next_assumption(left: List‹Addr›, right: List‹Addr›)
      -> AggrNextAssumption {
    match (load(left), load(right)) {
      (ListNode.Nil, ListNode.Nil) => AggrNextAssumption.Done,
      (ListNode.Cons(a, ar), ListNode.Nil) =>
        AggrNextAssumption.More(a, ar, right),
      (ListNode.Nil, ListNode.Cons(b, br)) =>
        AggrNextAssumption.More(b, left, br),
      (ListNode.Cons(a, ar), ListNode.Cons(b, br)) =>
        match aggr_address_order(a, b) {
          0 => AggrNextAssumption.More(a, ar, right),
          1 => AggrNextAssumption.More(a, ar, br),
          _ => AggrNextAssumption.More(b, left, br),
        },
    }
  }

  -- Find `target` in a sorted subject list, discarding subject values below it
  -- and returning the suffix useful for the next (strictly larger) target.
  fn aggr_seek_subject(target: Addr, subjects: List‹Addr›)
      -> (G, List‹Addr›) {
    match load(subjects) {
      ListNode.Nil => (0, subjects),
      ListNode.Cons(subject, rest) =>
        match aggr_address_order(subject, target) {
          0 => aggr_seek_subject(target, rest),
          1 => (1, rest),
          _ => (0, subjects),
        },
    }
  }

  -- Assert `output = (left ∪ right) ∖ subjects`, all lists sorted and
  -- duplicate-free. Subject scan state is threaded so the check is linear.
  fn aggr_assert_difference(left: List‹Addr›, right: List‹Addr›,
      subjects: List‹Addr›, output: List‹Addr›) {
    match aggr_next_assumption(left, right) {
      AggrNextAssumption.Done =>
        assert_eq!(load(output), ListNode.Nil,
          "aggr: output has an extra assumption");
        (),
      AggrNextAssumption.More(candidate, left_rest, right_rest) =>
        let (discharged, subject_rest) = aggr_seek_subject(candidate, subjects);
        match discharged {
          1 => aggr_assert_difference(left_rest, right_rest, subject_rest, output),
          _ =>
            let ListNode.Cons(actual, output_rest) = load(output);
            assert_eq!(address_eq(candidate, actual), 1,
              "aggr: outstanding assumption mismatch");
            aggr_assert_difference(left_rest, right_rest, subject_rest, output_rest),
        },
    }
  }

  /- ## Structural assumption discharge

  Structural pairs do not open their subject trees. Channel 6 carries one
  choice for every unique input-assumption candidate, keyed by the raw
  candidate address. A carried candidate must occur next in the canonical
  output-assumption list; a discharged candidate must supply a valid Merkle
  path into the one-hash structural output root.
  -/

  fn aggr_fold_path(hash: Addr, remaining: G, stream: ByteStream)
      -> (Addr, ByteStream) {
    match remaining {
      0 => (hash, stream),
      _ =>
        let (side, s1) = aggr_read_byte(stream);
        assert_eq!(u8_less_than(side, 2u8), 1,
          "aggr structural: path side must be 0 or 1");
        let (sibling, s2) = aggr_read_address(s1);
        let parent = match side {
          0 => aggr_node_hash(sibling, hash),
          _ => aggr_node_hash(hash, sibling),
        };
        aggr_fold_path(parent, remaining - 1, s2),
    }
  }

  -- Return 1 when `candidate` is discharged by a path into `root`, or 0
  -- when it is explicitly carried. The payload is strict:
  --   carried:     0
  --   discharged: 1 || count:u8 || (side:u8 || sibling:32)*
  fn aggr_discharge_choice(candidate: Addr, root: Addr) -> G {
    let (idx, len) = io_get_info(6, load(candidate));
    let bytes = #read_byte_stream(6, idx, len);
    let (choice, rest) = aggr_read_byte(bytes);
    assert_eq!(u8_less_than(choice, 2u8), 1,
      "aggr structural: discharge choice must be 0 or 1");
    match choice {
      0 =>
        assert_eq!(load(rest), ListNode.Nil,
          "aggr structural: carried choice has trailing bytes");
        0,
      _ =>
        let (count, path) = aggr_read_byte(rest);
        assert_eq!(u8_less_than(count, 65u8), 1,
          "aggr structural: Merkle path exceeds 64 steps");
        let (actual, stop) = aggr_fold_path(aggr_leaf_hash(candidate),
          to_field(count), path);
        assert_eq!(load(stop), ListNode.Nil,
          "aggr structural: trailing bytes after Merkle path");
        assert_eq!(address_eq(actual, root), 1,
          "aggr structural: assumption path does not reach subject root");
        1,
    }
  }

  -- Every unique candidate from `left ∪ right` is either discharged by a
  -- membership path or consumed from the strictly-sorted output list.
  fn aggr_assert_structural_difference(left: List‹Addr›, right: List‹Addr›,
      subject_root: Addr, output: List‹Addr›) {
    match aggr_next_assumption(left, right) {
      AggrNextAssumption.Done =>
        assert_eq!(load(output), ListNode.Nil,
          "aggr structural: output has an extra assumption");
        (),
      AggrNextAssumption.More(candidate, left_rest, right_rest) =>
        match aggr_discharge_choice(candidate, subject_root) {
          1 => aggr_assert_structural_difference(left_rest, right_rest,
            subject_root, output),
          _ =>
            let ListNode.Cons(actual, output_rest) = load(output);
            assert_eq!(address_eq(candidate, actual), 1,
              "aggr structural: outstanding assumption mismatch");
            aggr_assert_structural_difference(left_rest, right_rest,
              subject_root, output_rest),
        },
    }
  }

  fn aggr_get_opt_address(stream: ByteStream) -> (Option‹Addr›, ByteStream) {
    let (tag, rest) = aggr_read_byte(stream);
    match tag {
      0 => (Option.None, rest),
      1 =>
        let (addr, stop) = aggr_read_address(rest);
        (Option.Some(addr), stop),
    }
  }

  -- Strictly decode one complete `Claim::CheckEnv` byte string.
  fn aggr_parse_check_env(bytes: ByteStream) -> (Addr, Option‹Addr›) {
    let (tag, s) = aggr_read_byte(bytes);
    assert_eq!(tag, 0xE5u8, "aggr: claim is not CheckEnv");
    let (root, s2) = aggr_read_address(s);
    let (assumptions, stop) = aggr_get_opt_address(s2);
    assert_eq!(load(stop), ListNode.Nil,
      "aggr: trailing bytes after CheckEnv claim");
    (root, assumptions)
  }

  /- ## Digest-bound advice and claim decoding -/

  fn aggr_load_preimage(digest: [G; 8]) -> ByteStream {
    let (idx, len) = io_get_info(4, digest);
    let bytes = #read_byte_stream(4, idx, len);
    assert_eq!(@b3_pack(@blake3(bytes)), digest,
      "aggr: claim preimage digest mismatch");
    bytes
  }

  fn aggr_claim_field(claim: List‹U64›, index: G) -> G {
    @gl_val(list_lookup(claim, index))
  }

  fn aggr_claim_digest(claim: List‹U64›, start: G) -> [G; 8] {
    [aggr_claim_field(claim, start),
     aggr_claim_field(claim, start + 1),
     aggr_claim_field(claim, start + 2),
     aggr_claim_field(claim, start + 3),
     aggr_claim_field(claim, start + 4),
     aggr_claim_field(claim, start + 5),
     aggr_claim_field(claim, start + 6),
     aggr_claim_field(claim, start + 7)]
  }

  fn aggr_assert_digest(actual: [G; 8], expected: [G; 8]) {
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

  fn aggr_only_claim(claims: List‹List‹U64››) -> List‹U64› {
    let ListNode.Cons(claim, rest) = load(claims);
    assert_eq!(load(rest), ListNode.Nil,
      "aggr: child proof must expose exactly one claim");
    claim
  }

  /- ## Heterogeneous child verification

  Child kind 0 verifies against the IxVM system, kind 1 against this circuit's
  own system.  Which system a proof MUST verify against is fixed by the kind:
  the vk bytes on channel 1 are digest-checked against the corresponding half
  of the allowed blob before deserialization, so a hinted kind that does not
  match the child proof fails verification.
  -/

  fn aggr_load_sys(kind: G, ixvm_vk_digest: [G; 8], self_vk_digest: [G; 8])
      -> Sys {
    let (sidx, slen) = io_get_info(1, [kind]);
    let sbytes = #read_byte_stream(1, sidx, slen);
    let digest = @b3_pack(@blake3(sbytes));
    match kind {
      0 =>
        aggr_assert_digest(digest, ixvm_vk_digest),
      _ =>
        aggr_assert_digest(digest, self_vk_digest),
    };
    let (sys, srest) = @read_system(sbytes);
    assert_eq!(load(srest), ListNode.Nil);
    sys
  }

  -- Verify one child proof against `sys`. The verified proof's lookup
  -- accumulator and Fiat-Shamir transcript bind `cbytes` directly, so child
  -- claims need no standalone public digest.
  fn aggr_verify_child(sys: Sys, key: G) -> List‹List‹U64›› {
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

  -- Verify the child at `key` as the hinted `kind` and return the packed
  -- digest of its `CheckEnv` claim bytes.
  --
  -- * kind 0 (IxVM): the 10-word `verify_claim` claim carries the `CheckEnv`
  --   digest as its public input.
  -- * kind 1 (self): the 18-word `ix_aggr` claim must bind THIS aggregation
  --   identity (`allowed_digest`), pinning both vks and both entrypoint
  --   indices transitively; its output digest is the child's `CheckEnv`.
  fn aggr_child_check_env_digest(kind: G, key: G,
      ixvm_vk_digest: [G; 8], self_vk_digest: [G; 8],
      verify_idx: G, aggr_idx: G, allowed_digest: [G; 8]) -> [G; 8] {
    let sys = aggr_load_sys(kind, ixvm_vk_digest, self_vk_digest);
    let claim = aggr_only_claim(aggr_verify_child(sys, key));
    assert_eq!(aggr_claim_field(claim, 0), 0,
      "aggr: child has the wrong claim channel");
    match kind {
      0 =>
        assert_eq!(list_length(claim), 10,
          "aggr: IxVM child must expose a 10-word verify_claim claim");
        assert_eq!(aggr_claim_field(claim, 1), verify_idx,
          "aggr: IxVM child has the wrong entrypoint");
        aggr_claim_digest(claim, 2),
      _ =>
        assert_eq!(list_length(claim), 18,
          "aggr: recursive child must expose an 18-word ix_aggr claim");
        assert_eq!(aggr_claim_field(claim, 1), aggr_idx,
          "aggr: recursive child has the wrong entrypoint");
        aggr_assert_digest(aggr_claim_digest(claim, 2), allowed_digest);
        aggr_claim_digest(claim, 10),
    }
  }

  /- ## Shapes -/

  -- Wrap: one child, output statement identical to the child's. Digest
  -- equality is byte equality (Blake3), so nothing needs to be opened.
  fn aggr_wrap(kind: G, ixvm_vk_digest: [G; 8], self_vk_digest: [G; 8],
      verify_idx: G, aggr_idx: G, allowed_digest: [G; 8],
      out_claim_digest: [G; 8]) {
    let child = aggr_child_check_env_digest(kind, 0,
      ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
    aggr_assert_digest(child, out_claim_digest)
  }

  -- Pair: two children, canonical set-discharge fold.
  fn aggr_pair(left_kind: G, right_kind: G,
      ixvm_vk_digest: [G; 8], self_vk_digest: [G; 8],
      verify_idx: G, aggr_idx: G, allowed_digest: [G; 8],
      out_claim_digest: [G; 8]) {
    let left_digest = aggr_child_check_env_digest(left_kind, 0,
      ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
    let right_digest = aggr_child_check_env_digest(right_kind, 1,
      ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
    let (left_root, left_asm) =
      aggr_parse_check_env(aggr_load_preimage(left_digest));
    let (right_root, right_asm) =
      aggr_parse_check_env(aggr_load_preimage(right_digest));

    -- Bind and decode this fold's output claim.
    let (oidx, olen) = io_get_info(2, [2]);
    let output_bytes = #read_byte_stream(2, oidx, olen);
    assert_eq!(@b3_pack(@blake3(output_bytes)), out_claim_digest,
      "aggr: output claim digest mismatch");
    let (output_root, output_asm) = aggr_parse_check_env(output_bytes);

    let left_subjects = aggr_load_canonical_tree(left_root);
    let right_subjects = aggr_load_canonical_tree(right_root);
    let left_assumptions = aggr_load_optional_tree(left_asm);
    let right_assumptions = aggr_load_optional_tree(right_asm);
    let output_subjects = aggr_load_canonical_tree(output_root);
    let output_assumptions = aggr_load_optional_tree(output_asm);

    aggr_assert_union(left_subjects, right_subjects, output_subjects);
    aggr_assert_difference(left_assumptions, right_assumptions,
      output_subjects, output_assumptions);
    ()
  }

  -- Structural pair: verify the same heterogeneous child forms, commit to
  -- subjects with one free-form node hash, and discharge assumptions through
  -- channel-6 Merkle paths. Only canonical assumption trees are opened.
  fn aggr_pair_structural(left_kind: G, right_kind: G,
      ixvm_vk_digest: [G; 8], self_vk_digest: [G; 8],
      verify_idx: G, aggr_idx: G, allowed_digest: [G; 8],
      out_claim_digest: [G; 8]) {
    let left_digest = aggr_child_check_env_digest(left_kind, 0,
      ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
    let right_digest = aggr_child_check_env_digest(right_kind, 1,
      ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
    let (left_root, left_asm) =
      aggr_parse_check_env(aggr_load_preimage(left_digest));
    let (right_root, right_asm) =
      aggr_parse_check_env(aggr_load_preimage(right_digest));

    let (oidx, olen) = io_get_info(2, [2]);
    let output_bytes = #read_byte_stream(2, oidx, olen);
    assert_eq!(@b3_pack(@blake3(output_bytes)), out_claim_digest,
      "aggr structural: output claim digest mismatch");
    let (output_root, output_asm) = aggr_parse_check_env(output_bytes);

    let expected_root = aggr_node_hash(left_root, right_root);
    assert_eq!(address_eq(output_root, expected_root), 1,
      "aggr structural: output subject root is not nodeHash(left, right)");

    let left_assumptions = aggr_load_optional_tree(left_asm);
    let right_assumptions = aggr_load_optional_tree(right_asm);
    let output_assumptions = aggr_load_optional_tree(output_asm);
    aggr_assert_structural_difference(left_assumptions, right_assumptions,
      output_root, output_assumptions);
    ()
  }

  /- ## Entrypoint -/

  -- Public input is `blake3(allowed_blob) ‖ blake3(output_claim_bytes)`,
  -- packed four bytes per Goldilocks element.
  pub fn ix_aggr(allowed_digest: [G; 8], out_claim_digest: [G; 8]) {
    -- Allowed blob:
    --   ixvm_vk_digest(32) ‖ verify_idx(u64 LE) ‖
    --   self_vk_digest(32) ‖ aggr_idx(u64 LE).
    let (aidx, alen) = io_get_info(3, [0]);
    assert_eq!(alen, 80,
      "aggr: allowed blob must be exactly 80 bytes");
    let allowed_bytes = #read_byte_stream(3, aidx, alen);
    assert_eq!(@b3_pack(@blake3(allowed_bytes)), allowed_digest,
      "aggr: allowed blob digest mismatch");
    let (ixvm_digest_addr, as1) = aggr_read_address(allowed_bytes);
    let (verify_idx_limb, as2) = @read_u64(as1);
    let (self_digest_addr, as3) = aggr_read_address(as2);
    let (aggr_idx_limb, astop) = @read_u64(as3);
    assert_eq!(load(astop), ListNode.Nil,
      "aggr: allowed blob must be exactly 80 bytes");
    let ixvm_vk_digest = aggr_pack_address(ixvm_digest_addr);
    let self_vk_digest = aggr_pack_address(self_digest_addr);
    let verify_idx = flatten_u64(verify_idx_limb);
    let aggr_idx = flatten_u64(aggr_idx_limb);

    -- Shape hint: exactly one advice byte.
    --   0 = wrap IxVM        1 = wrap self
    --   2–5 = flat pairs:       2 + 2·left + right
    --   6–9 = structural pairs: 6 + 2·left + right
    let (hidx, hlen) = io_get_info(6, [0]);
    assert_eq!(hlen, 1, "aggr: shape hint must be exactly one byte");
    let hint = #read_byte_stream(6, hidx, hlen);
    let (shape, hstop) = aggr_read_byte(hint);
    assert_eq!(load(hstop), ListNode.Nil,
      "aggr: trailing bytes after shape hint");
    match shape {
      0 => aggr_wrap(0, ixvm_vk_digest, self_vk_digest,
        verify_idx, aggr_idx, allowed_digest, out_claim_digest),
      1 => aggr_wrap(1, ixvm_vk_digest, self_vk_digest,
        verify_idx, aggr_idx, allowed_digest, out_claim_digest),
      2 => aggr_pair(0, 0, ixvm_vk_digest, self_vk_digest,
        verify_idx, aggr_idx, allowed_digest, out_claim_digest),
      3 => aggr_pair(0, 1, ixvm_vk_digest, self_vk_digest,
        verify_idx, aggr_idx, allowed_digest, out_claim_digest),
      4 => aggr_pair(1, 0, ixvm_vk_digest, self_vk_digest,
        verify_idx, aggr_idx, allowed_digest, out_claim_digest),
      5 => aggr_pair(1, 1, ixvm_vk_digest, self_vk_digest,
        verify_idx, aggr_idx, allowed_digest, out_claim_digest),
      6 => aggr_pair_structural(0, 0, ixvm_vk_digest, self_vk_digest,
        verify_idx, aggr_idx, allowed_digest, out_claim_digest),
      7 => aggr_pair_structural(0, 1, ixvm_vk_digest, self_vk_digest,
        verify_idx, aggr_idx, allowed_digest, out_claim_digest),
      8 => aggr_pair_structural(1, 0, ixvm_vk_digest, self_vk_digest,
        verify_idx, aggr_idx, allowed_digest, out_claim_digest),
      9 => aggr_pair_structural(1, 1, ixvm_vk_digest, self_vk_digest,
        verify_idx, aggr_idx, allowed_digest, out_claim_digest),
    }
  }
⟧

end Aggr

end
