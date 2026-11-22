import Aiur.Modules.Frontend

/-! # MultiStark module `Aggregation`

Aggregation of Ix claims: assumption trees, claim catalogs and their hashes.

Formal Aiur source, written as Lean syntax (`aiur⟦ … ⟧`). `MultiStark.recursionSource`
and `MultiStark.aggregateSource` (`MultiStark/MultiStark/Program.lean`) compose the modules. -/

namespace MultiStark.Source

def aggregation : Aiur.Modules.Program Nat := aiur⟦
module Aggregation {
  enum AggrNextAssumption {
      Done,
      More(Bytes::AddressRef, Field, Lists::List<Bytes::AddressRef>, Lists::List<Bytes::AddressRef>)
    }

  enum AggrOptBridge {
      NoBridge,
      SomeBridge(Bytes::AddressRef, Bytes::AddressRef, Bytes::AddressRef, UInt64::U64, Bytes::AddressRef)
    }

  enum AggrOptCircuitRef {
      NoCircuitRef,
      SomeCircuitRef(Bytes::AddressRef, UInt64::U64)
    }

  fn aggr_read_byte(stream: Bytes::Stream) -> (UInt8::U8, Bytes::Stream) {
      let Lists::Node::Cons(byte, rest) = (*(stream));
      (byte, rest)
    }

  fn aggr_read_u32_le(stream: Bytes::Stream) -> (Field, Bytes::Stream) {
      let (b0, s1) = aggr_read_byte(stream);
      let (b1, s2) = aggr_read_byte(s1);
      let (b2, s3) = aggr_read_byte(s2);
      let (b3, s4) = aggr_read_byte(s3);
      (UInt8::to_field(b0) + 256 * UInt8::to_field(b1)
        + 65536 * UInt8::to_field(b2) + 16777216 * UInt8::to_field(b3), s4)
    }

  fn aggr_read_u64(stream: Bytes::Stream) -> (UInt64::U64, Bytes::Stream) {
      let (b0, s0) = aggr_read_byte(stream);
      let (b1, s1) = aggr_read_byte(s0);
      let (b2, s2) = aggr_read_byte(s1);
      let (b3, s3) = aggr_read_byte(s2);
      let (b4, s4) = aggr_read_byte(s3);
      let (b5, s5) = aggr_read_byte(s4);
      let (b6, s6) = aggr_read_byte(s5);
      let (b7, s7) = aggr_read_byte(s6);
      ([b0, b1, b2, b3, b4, b5, b6, b7], s7)
    }

  fn aggr_read_u64_list_n(stream: Bytes::Stream, n: Field) -> (Lists::List<UInt64::U64>, Bytes::Stream) {
      match n {
        0 => { ((&(Lists::Node::Nil)), stream) } ,
        _ => {
          let (w, s1) = aggr_read_u64(stream);
          let (rest, s2) = aggr_read_u64_list_n(s1, n - 1);
          ((&(Lists::Node::Cons(w, rest))), s2) } ,
      }
    }

  fn aggr_read_address(stream: Bytes::Stream) -> (Bytes::AddressRef, Bytes::Stream) {
      let Lists::Node::Cons(b0, s) = (*(stream));
      let Lists::Node::Cons(b1, s) = (*(s));
      let Lists::Node::Cons(b2, s) = (*(s));
      let Lists::Node::Cons(b3, s) = (*(s));
      let Lists::Node::Cons(b4, s) = (*(s));
      let Lists::Node::Cons(b5, s) = (*(s));
      let Lists::Node::Cons(b6, s) = (*(s));
      let Lists::Node::Cons(b7, s) = (*(s));
      let Lists::Node::Cons(b8, s) = (*(s));
      let Lists::Node::Cons(b9, s) = (*(s));
      let Lists::Node::Cons(b10, s) = (*(s));
      let Lists::Node::Cons(b11, s) = (*(s));
      let Lists::Node::Cons(b12, s) = (*(s));
      let Lists::Node::Cons(b13, s) = (*(s));
      let Lists::Node::Cons(b14, s) = (*(s));
      let Lists::Node::Cons(b15, s) = (*(s));
      let Lists::Node::Cons(b16, s) = (*(s));
      let Lists::Node::Cons(b17, s) = (*(s));
      let Lists::Node::Cons(b18, s) = (*(s));
      let Lists::Node::Cons(b19, s) = (*(s));
      let Lists::Node::Cons(b20, s) = (*(s));
      let Lists::Node::Cons(b21, s) = (*(s));
      let Lists::Node::Cons(b22, s) = (*(s));
      let Lists::Node::Cons(b23, s) = (*(s));
      let Lists::Node::Cons(b24, s) = (*(s));
      let Lists::Node::Cons(b25, s) = (*(s));
      let Lists::Node::Cons(b26, s) = (*(s));
      let Lists::Node::Cons(b27, s) = (*(s));
      let Lists::Node::Cons(b28, s) = (*(s));
      let Lists::Node::Cons(b29, s) = (*(s));
      let Lists::Node::Cons(b30, s) = (*(s));
      let Lists::Node::Cons(b31, s) = (*(s));
      ((&([b0, b1, b2, b3, b4, b5, b6, b7,
              b8, b9, b10, b11, b12, b13, b14, b15,
              b16, b17, b18, b19, b20, b21, b22, b23,
              b24, b25, b26, b27, b28, b29, b30, b31])), s)
    }

  fn aggr_put_address(addr: Bytes::AddressRef, rest: Bytes::Stream) -> Bytes::Stream {
      let a = (*(addr));
      let s31 = (&(Lists::Node::Cons(a[31], rest)));
      let s30 = (&(Lists::Node::Cons(a[30], s31)));
      let s29 = (&(Lists::Node::Cons(a[29], s30)));
      let s28 = (&(Lists::Node::Cons(a[28], s29)));
      let s27 = (&(Lists::Node::Cons(a[27], s28)));
      let s26 = (&(Lists::Node::Cons(a[26], s27)));
      let s25 = (&(Lists::Node::Cons(a[25], s26)));
      let s24 = (&(Lists::Node::Cons(a[24], s25)));
      let s23 = (&(Lists::Node::Cons(a[23], s24)));
      let s22 = (&(Lists::Node::Cons(a[22], s23)));
      let s21 = (&(Lists::Node::Cons(a[21], s22)));
      let s20 = (&(Lists::Node::Cons(a[20], s21)));
      let s19 = (&(Lists::Node::Cons(a[19], s20)));
      let s18 = (&(Lists::Node::Cons(a[18], s19)));
      let s17 = (&(Lists::Node::Cons(a[17], s18)));
      let s16 = (&(Lists::Node::Cons(a[16], s17)));
      let s15 = (&(Lists::Node::Cons(a[15], s16)));
      let s14 = (&(Lists::Node::Cons(a[14], s15)));
      let s13 = (&(Lists::Node::Cons(a[13], s14)));
      let s12 = (&(Lists::Node::Cons(a[12], s13)));
      let s11 = (&(Lists::Node::Cons(a[11], s12)));
      let s10 = (&(Lists::Node::Cons(a[10], s11)));
      let s9 = (&(Lists::Node::Cons(a[9], s10)));
      let s8 = (&(Lists::Node::Cons(a[8], s9)));
      let s7 = (&(Lists::Node::Cons(a[7], s8)));
      let s6 = (&(Lists::Node::Cons(a[6], s7)));
      let s5 = (&(Lists::Node::Cons(a[5], s6)));
      let s4 = (&(Lists::Node::Cons(a[4], s5)));
      let s3 = (&(Lists::Node::Cons(a[3], s4)));
      let s2 = (&(Lists::Node::Cons(a[2], s3)));
      let s1 = (&(Lists::Node::Cons(a[1], s2)));
      (&(Lists::Node::Cons(a[0], s1)))
    }

  fn aggr_pack_address(addr: Bytes::AddressRef) -> [Field; 8] {
      let a = (*(addr));
      [Blake3::pack_word(UInt32::from_bytes([a[0], a[1], a[2], a[3]])),
       Blake3::pack_word(UInt32::from_bytes([a[4], a[5], a[6], a[7]])),
       Blake3::pack_word(UInt32::from_bytes([a[8], a[9], a[10], a[11]])),
       Blake3::pack_word(UInt32::from_bytes([a[12], a[13], a[14], a[15]])),
       Blake3::pack_word(UInt32::from_bytes([a[16], a[17], a[18], a[19]])),
       Blake3::pack_word(UInt32::from_bytes([a[20], a[21], a[22], a[23]])),
       Blake3::pack_word(UInt32::from_bytes([a[24], a[25], a[26], a[27]])),
       Blake3::pack_word(UInt32::from_bytes([a[28], a[29], a[30], a[31]]))]
    }

  fn aggr_node_hash(left: Bytes::AddressRef, right: Bytes::AddressRef) -> Bytes::AddressRef {
      let tail = aggr_put_address(left,
        aggr_put_address(right, (&(Lists::Node::Nil))));
      Blake3::bytes_to_addr((&(Lists::Node::Cons(UInt8::BYTE_1, tail))))
    }

  fn aggr_leaf_hash(addr: Bytes::AddressRef) -> Bytes::AddressRef {
      let tail = aggr_put_address(addr, (&(Lists::Node::Nil)));
      Blake3::bytes_to_addr((&(Lists::Node::Cons(UInt8::BYTE_0, tail))))
    }

  inline fn aggr_pack_be4(a: UInt8::U8, b: UInt8::U8, c: UInt8::U8, d: UInt8::U8) -> Field {
      ((UInt8::to_field(a) * 256 + UInt8::to_field(b)) * 256 + UInt8::to_field(c)) * 256
        + UInt8::to_field(d)
    }

  fn aggr_address_order(a: Bytes::AddressRef, b: Bytes::AddressRef) -> Field {
      let av = (*(a));
      let bv = (*(b));
      let aw0 = aggr_pack_be4(av[0], av[1], av[2], av[3]);
      let bw0 = aggr_pack_be4(bv[0], bv[1], bv[2], bv[3]);
      match aw0 - bw0 {
        0 => {
          let aw1 = aggr_pack_be4(av[4], av[5], av[6], av[7]);
          let bw1 = aggr_pack_be4(bv[4], bv[5], bv[6], bv[7]);
          match aw1 - bw1 {
            0 => {
              let aw2 = aggr_pack_be4(av[8], av[9], av[10], av[11]);
              let bw2 = aggr_pack_be4(bv[8], bv[9], bv[10], bv[11]);
              match aw2 - bw2 {
                0 => {
                  let aw3 = aggr_pack_be4(av[12], av[13], av[14], av[15]);
                  let bw3 = aggr_pack_be4(bv[12], bv[13], bv[14], bv[15]);
                  match aw3 - bw3 {
                    0 => {
                      let aw4 = aggr_pack_be4(av[16], av[17], av[18], av[19]);
                      let bw4 = aggr_pack_be4(bv[16], bv[17], bv[18], bv[19]);
                      match aw4 - bw4 {
                        0 => {
                          let aw5 = aggr_pack_be4(av[20], av[21], av[22], av[23]);
                          let bw5 = aggr_pack_be4(bv[20], bv[21], bv[22], bv[23]);
                          match aw5 - bw5 {
                            0 => {
                              let aw6 = aggr_pack_be4(av[24], av[25], av[26], av[27]);
                              let bw6 = aggr_pack_be4(bv[24], bv[25], bv[26], bv[27]);
                              match aw6 - bw6 {
                                0 => {
                                  let aw7 = aggr_pack_be4(av[28], av[29], av[30], av[31]);
                                  let bw7 = aggr_pack_be4(bv[28], bv[29], bv[30], bv[31]);
                                  match aw7 - bw7 {
                                    0 => {  1 } ,
                                    _ => {  match UInt32::less_than_fields(aw7, bw7) { 1 => {  0 } , _ => {  2 } , } } ,
                                  } } ,
                                _ => {  match UInt32::less_than_fields(aw6, bw6) { 1 => {  0 } , _ => {  2 } , } } ,
                              } } ,
                            _ => {  match UInt32::less_than_fields(aw5, bw5) { 1 => {  0 } , _ => {  2 } , } } ,
                          } } ,
                        _ => {  match UInt32::less_than_fields(aw4, bw4) { 1 => {  0 } , _ => {  2 } , } } ,
                      } } ,
                    _ => {  match UInt32::less_than_fields(aw3, bw3) { 1 => {  0 } , _ => {  2 } , } } ,
                  } } ,
                _ => {  match UInt32::less_than_fields(aw2, bw2) { 1 => {  0 } , _ => {  2 } , } } ,
              } } ,
            _ => {  match UInt32::less_than_fields(aw1, bw1) { 1 => {  0 } , _ => {  2 } , } } ,
          } } ,
        _ => {  match UInt32::less_than_fields(aw0, bw0) { 1 => {  0 } , _ => {  2 } , } } ,
      }
    }

  fn aggr_assert_strict_sorted(leaves: Lists::List<Bytes::AddressRef>) -> () {
      match (*(leaves)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(a, rest) => {
          match (*(rest)) {
            Lists::Node::Nil => {  () } ,
            Lists::Node::Cons(b, _) => {
              assert_eq!(aggr_address_order(a, b), 0,
                "aggr: tree leaves are not strictly sorted");
              aggr_assert_strict_sorted(rest) } ,
          } } ,
      }
    }

  fn aggr_parse_tree_body(stream: Bytes::Stream) -> (Lists::List<Bytes::AddressRef>, Bytes::Stream) {
      let (tag, rest) = aggr_read_byte(stream);
      match UInt8::to_field(tag) {
        0 => {
          let (addr, stop) = aggr_read_address(rest);
          ((&(Lists::Node::Cons(addr, (&(Lists::Node::Nil))))), stop) } ,
        1 => {  ((&(Lists::Node::Nil)), rest) } ,
        2 => {
          let (left, s2) = aggr_parse_tree_body(rest);
          let (right, stop) = aggr_parse_tree_body(s2);
          (Lists::concat(left, right), stop) } ,
      }
    }

  fn aggr_leaf_hashes(leaves: Lists::List<Bytes::AddressRef>) -> Lists::List<Bytes::AddressRef> {
      match (*(leaves)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(addr, rest) => {
          (&(Lists::Node::Cons(aggr_leaf_hash(addr), aggr_leaf_hashes(rest)))) } ,
      }
    }

  fn aggr_pair_hashes(nodes: Lists::List<Bytes::AddressRef>) -> Lists::List<Bytes::AddressRef> {
      match (*(nodes)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(left, rest) => {
          match (*(rest)) {
            Lists::Node::Nil => {
              let zero = (&([UInt8::BYTE_0; 32]));
              (&(Lists::Node::Cons(aggr_node_hash(left, zero), (&(Lists::Node::Nil))))) } ,
            Lists::Node::Cons(right, tail) => {
              (&(Lists::Node::Cons(aggr_node_hash(left, right), aggr_pair_hashes(tail)))) } ,
          } } ,
      }
    }

  fn aggr_reduce_hashes(nodes: Lists::List<Bytes::AddressRef>) -> Bytes::AddressRef {
      let Lists::Node::Cons(root, rest) = (*(nodes));
      match (*(rest)) {
        Lists::Node::Nil => {  root } ,
        _ => {  aggr_reduce_hashes(aggr_pair_hashes(nodes)) } ,
      }
    }

  fn aggr_canonical_root(leaves: Lists::List<Bytes::AddressRef>) -> Bytes::AddressRef {
      aggr_reduce_hashes(aggr_leaf_hashes(leaves))
    }

  fn aggr_load_canonical_tree(root: Bytes::AddressRef) -> Lists::List<Bytes::AddressRef> {
      let raw = (*(root));
      let (idx, len) = hint::<(Field, Field)>("stark.io.address", (5, Blake3::address_to_fields(raw)));
      let bytes = StarkIO::read_byte_stream(5, idx, len);
      let (tag, body) = aggr_read_byte(bytes);
      assert_eq!(UInt8::to_field(tag), 226, "aggr: tree has the wrong Ixon tag");
      let (leaves, stop) = aggr_parse_tree_body(body);
      let Lists::Node::Nil = (*(stop));
      assert_eq!(Lists::is_empty(leaves), 0,
        "aggr: a present tree must contain at least one leaf");

      aggr_assert_strict_sorted(leaves);
      let expected = aggr_canonical_root(leaves);
      assert_eq!(Bytes::address_eq(expected, root), 1,
        "aggr: tree leaves do not reproduce the canonical root");
      leaves
    }

  fn aggr_load_optional_tree(root: Options::Option<Bytes::AddressRef>) -> Lists::List<Bytes::AddressRef> {
      match root {
        Options::Option::None => {  (&(Lists::Node::Nil)) } ,
        Options::Option::Some(addr) => {  aggr_load_canonical_tree(addr) } ,
      }
    }

  fn aggr_assert_same_list(left: Lists::List<Bytes::AddressRef>, right: Lists::List<Bytes::AddressRef>) -> () {
      match ((*(left)), (*(right))) {
        (Lists::Node::Nil, Lists::Node::Nil) => {  () } ,
        (Lists::Node::Cons(a, ar), Lists::Node::Cons(b, br)) => {
          assert_eq!(Bytes::address_eq(a, b), 1, "aggr: set element mismatch");
          aggr_assert_same_list(ar, br) } ,
      }
    }

  fn aggr_assert_union(left: Lists::List<Bytes::AddressRef>, right: Lists::List<Bytes::AddressRef>,
        output: Lists::List<Bytes::AddressRef>) -> () {
      match ((*(left)), (*(right))) {
        (Lists::Node::Nil, _) => {  aggr_assert_same_list(right, output) } ,
        (_, Lists::Node::Nil) => {  aggr_assert_same_list(left, output) } ,
        (Lists::Node::Cons(a, ar), Lists::Node::Cons(b, br)) => {
          let Lists::Node::Cons(o, or) = (*(output));
          match aggr_address_order(a, b) {
            0 => {
              assert_eq!(Bytes::address_eq(a, o), 1, "aggr: subject union mismatch");
              aggr_assert_union(ar, right, or) } ,
            1 => {
              assert_eq!(Bytes::address_eq(a, o), 1, "aggr: subject union mismatch");
              aggr_assert_union(ar, br, or) } ,
            _ => {
              assert_eq!(Bytes::address_eq(b, o), 1, "aggr: subject union mismatch");
              aggr_assert_union(left, br, or) } ,
          } } ,
      }
    }

  fn aggr_assert_disjoint_union(left: Lists::List<Bytes::AddressRef>, right: Lists::List<Bytes::AddressRef>,
        output: Lists::List<Bytes::AddressRef>) -> () {
      match ((*(left)), (*(right))) {
        (Lists::Node::Nil, _) => {  aggr_assert_same_list(right, output) } ,
        (_, Lists::Node::Nil) => {  aggr_assert_same_list(left, output) } ,
        (Lists::Node::Cons(a, ar), Lists::Node::Cons(b, br)) => {
          let Lists::Node::Cons(o, or) = (*(output));
          match aggr_address_order(a, b) {
            0 => {
              assert_eq!(Bytes::address_eq(a, o), 1, "aggr: subject union mismatch");
              aggr_assert_disjoint_union(ar, right, or) } ,
            1 => {
              assert_eq!(0, 1, "aggr: child subject sets overlap");
              () } ,
            _ => {
              assert_eq!(Bytes::address_eq(b, o), 1, "aggr: subject union mismatch");
              aggr_assert_disjoint_union(left, br, or) } ,
          } } ,
      }
    }

  fn aggr_assert_disjoint(left: Lists::List<Bytes::AddressRef>, right: Lists::List<Bytes::AddressRef>) -> () {
      match ((*(left)), (*(right))) {
        (Lists::Node::Nil, _) => {  () } ,
        (_, Lists::Node::Nil) => {  () } ,
        (Lists::Node::Cons(a, ar), Lists::Node::Cons(b, br)) => {
          match aggr_address_order(a, b) {
            0 => {  aggr_assert_disjoint(ar, right) } ,
            1 => {
              assert_eq!(0, 1, "aggr: subject set overlaps assumption set");
              () } ,
            _ => {  aggr_assert_disjoint(left, br) } ,
          } } ,
      }
    }

  fn aggr_next_assumption(left: Lists::List<Bytes::AddressRef>, right: Lists::List<Bytes::AddressRef>)
        -> AggrNextAssumption {
      match ((*(left)), (*(right))) {
        (Lists::Node::Nil, Lists::Node::Nil) => {  AggrNextAssumption::Done } ,
        (Lists::Node::Cons(a, ar), Lists::Node::Nil) => {
          AggrNextAssumption::More(a, 0, ar, right) } ,
        (Lists::Node::Nil, Lists::Node::Cons(b, br)) => {
          AggrNextAssumption::More(b, 2, left, br) } ,
        (Lists::Node::Cons(a, ar), Lists::Node::Cons(b, br)) => {
          match aggr_address_order(a, b) {
            0 => {  AggrNextAssumption::More(a, 0, ar, right) } ,
            1 => {  AggrNextAssumption::More(a, 1, ar, br) } ,
            _ => {  AggrNextAssumption::More(b, 2, left, br) } ,
          } } ,
      }
    }

  fn aggr_seek_subject(target: Bytes::AddressRef, subjects: Lists::List<Bytes::AddressRef>)
        -> (Field, Lists::List<Bytes::AddressRef>) {
      match (*(subjects)) {
        Lists::Node::Nil => {  (0, subjects) } ,
        Lists::Node::Cons(subject, rest) => {
          match aggr_address_order(subject, target) {
            0 => {  aggr_seek_subject(target, rest) } ,
            1 => {  (1, rest) } ,
            _ => {  (0, subjects) } ,
          } } ,
      }
    }

  fn aggr_assert_difference(left: Lists::List<Bytes::AddressRef>, right: Lists::List<Bytes::AddressRef>,
        subjects: Lists::List<Bytes::AddressRef>, output: Lists::List<Bytes::AddressRef>) -> () {
      match aggr_next_assumption(left, right) {
        AggrNextAssumption::Done => {
          let Lists::Node::Nil = (*(output));
          () } ,
        AggrNextAssumption::More(candidate, _source, left_rest, right_rest) => {
          let (discharged, subject_rest) = aggr_seek_subject(candidate, subjects);
          match discharged {
            1 => {  aggr_assert_difference(left_rest, right_rest, subject_rest, output) } ,
            _ => {
              let Lists::Node::Cons(actual, output_rest) = (*(output));
              assert_eq!(Bytes::address_eq(candidate, actual), 1,
                "aggr: outstanding assumption mismatch");
              aggr_assert_difference(left_rest, right_rest, subject_rest, output_rest) } ,
          } } ,
      }
    }

  fn aggr_fold_path(hash: Bytes::AddressRef, remaining: Field, stream: Bytes::Stream)
        -> (Bytes::AddressRef, Bytes::Stream) {
      match remaining {
        0 => {  (hash, stream) } ,
        _ => {
          let (side, s1) = aggr_read_byte(stream);
          assert_eq!(UInt8::less_than(side, UInt8::BYTE_2), 1,
            "aggr structural: path side must be 0 or 1");
          let (sibling, s2) = aggr_read_address(s1);
          let parent = match UInt8::to_field(side) {
            0 => {  aggr_node_hash(sibling, hash) } ,
            _ => {  aggr_node_hash(hash, sibling) } ,
          };
          aggr_fold_path(parent, remaining - 1, s2) } ,
      }
    }

  fn aggr_discharge_choice(candidate: Bytes::AddressRef, source: Field,
        left_root: Bytes::AddressRef, right_root: Bytes::AddressRef) -> Field {
      let (idx, len) = hint::<(Field, Field)>("stark.io.address", (6, Blake3::address_to_fields((*(candidate)))));
      let bytes = StarkIO::read_byte_stream(6, idx, len);
      let (choice, rest) = aggr_read_byte(bytes);
      assert_eq!(UInt8::less_than(choice, UInt8::BYTE_2), 1,
        "aggr structural: discharge choice must be 0 or 1");
      match UInt8::to_field(choice) {
        0 => {
          let Lists::Node::Nil = (*(rest));
          0 } ,
        _ => {
          let (count, path) = aggr_read_byte(rest);
          assert_eq!(UInt8::less_than(UInt8::BYTE_0, count), 1,
            "aggr structural: Merkle path must have at least 1 step");
          assert_eq!(UInt8::less_than(count, UInt8::BYTE_65), 1,
            "aggr structural: Merkle path exceeds 64 steps");
          let (child_actual, last_step) = aggr_fold_path(aggr_leaf_hash(candidate),
            UInt8::to_field(count) - 1, path);
          let (last_side, s1) = aggr_read_byte(last_step);
          let (last_sibling, stop) = aggr_read_address(s1);
          let Lists::Node::Nil = (*(stop));
          match source {
            0 => {
              assert_eq!(UInt8::to_field(last_side), 0,
                "aggr structural: left assumption must be discharged by right child");
              assert_eq!(Bytes::address_eq(last_sibling, left_root), 1,
                "aggr structural: final step sibling is not left subject root");
              assert_eq!(Bytes::address_eq(child_actual, right_root), 1,
                "aggr structural: assumption path does not reach right subject root");
              1 } ,
            2 => {
              assert_eq!(UInt8::to_field(last_side), 1,
                "aggr structural: right assumption must be discharged by left child");
              assert_eq!(Bytes::address_eq(last_sibling, right_root), 1,
                "aggr structural: final step sibling is not right subject root");
              assert_eq!(Bytes::address_eq(child_actual, left_root), 1,
                "aggr structural: assumption path does not reach left subject root");
              1 } ,
            _ => {
              assert_eq!(0, 1,
                "aggr structural: shared assumption cannot be discharged");
              0 } ,
          } } ,
      }
    }

  fn aggr_assert_structural_difference(left: Lists::List<Bytes::AddressRef>, right: Lists::List<Bytes::AddressRef>,
        left_root: Bytes::AddressRef, right_root: Bytes::AddressRef, output: Lists::List<Bytes::AddressRef>) -> () {
      match aggr_next_assumption(left, right) {
        AggrNextAssumption::Done => {
          let Lists::Node::Nil = (*(output));
          () } ,
        AggrNextAssumption::More(candidate, source, left_rest, right_rest) => {
          match aggr_discharge_choice(candidate, source, left_root, right_root) {
            1 => {  aggr_assert_structural_difference(left_rest, right_rest,
              left_root, right_root, output) } ,
            _ => {
              let Lists::Node::Cons(actual, output_rest) = (*(output));
              assert_eq!(Bytes::address_eq(candidate, actual), 1,
                "aggr structural: outstanding assumption mismatch");
              aggr_assert_structural_difference(left_rest, right_rest,
                left_root, right_root, output_rest) } ,
          } } ,
      }
    }

  fn aggr_get_opt_address(stream: Bytes::Stream) -> (Options::Option<Bytes::AddressRef>, Bytes::Stream) {
      let (tag, rest) = aggr_read_byte(stream);
      match UInt8::to_field(tag) {
        0 => {  (Options::Option::None, rest) } ,
        1 => {
          let (addr, stop) = aggr_read_address(rest);
          (Options::Option::Some(addr), stop) } ,
      }
    }

  fn aggr_parse_check_env(bytes: Bytes::Stream)
        -> ((Bytes::AddressRef, Bytes::AddressRef, Options::Option<Bytes::AddressRef>, Field), Bytes::AddressRef, Options::Option<Bytes::AddressRef>) {

      let (tag, s) = aggr_read_byte(bytes);
      assert_eq!(UInt8::to_field(tag), 229, "aggr: claim is not CheckEnv");
      let (format, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(format), 4, "aggr: unsupported object format");
      let (validator_byte, s) = aggr_read_byte(s);
      let validator = UInt8::to_field(validator_byte);
      assert_eq!((validator - 3) * (validator - 4) * (validator - 5), 0,
        "aggr: wrong validator identity");
      let (spec, s) = aggr_read_address(s);
      let (binding, s) = aggr_read_address(s);
      let (axioms, s) = aggr_get_opt_address(s);
      let (root, s2) = aggr_read_address(s);
      let (assumptions, stop) = aggr_get_opt_address(s2);
      let Lists::Node::Nil = (*(stop));
      ((spec, binding, axioms, validator), root, assumptions)
    }

  fn aggr_parse_binding(bytes: Bytes::Stream) -> (Bytes::AddressRef, Bytes::AddressRef) {

      let (tag0, s) = aggr_read_byte(bytes);
      assert_eq!(UInt8::to_field(tag0), 232, "aggr: claim is not Binding");
      let (tag1, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(tag1), 2, "aggr: claim is not Binding");
      let (format, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(format), 4, "aggr: unsupported object format");
      let (validator, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(validator), 3, "aggr: wrong validator identity");
      let (spec, s) = aggr_read_address(s);
      let (binding, stop) = aggr_read_address(s);
      let Lists::Node::Nil = (*(stop));
      (spec, binding)
    }

  fn aggr_parse_catalog(bytes: Bytes::Stream) -> Bytes::AddressRef {

      let (tag0, s) = aggr_read_byte(bytes);
      assert_eq!(UInt8::to_field(tag0), 232, "aggr: claim is not Catalog");
      let (tag1, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(tag1), 0, "aggr: claim is not Catalog");
      let (format, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(format), 4, "aggr: unsupported object format");
      let (validator, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(validator), 3, "aggr: wrong validator identity");
      let (members, stop) = aggr_read_address(s);
      let Lists::Node::Nil = (*(stop));
      members
    }

  fn aggr_opt_address_eq(a: Options::Option<Bytes::AddressRef>, b: Options::Option<Bytes::AddressRef>) -> Field {
      match a {
        Options::Option::None => {
          match b {
            Options::Option::None => {  1 } ,
            Options::Option::Some(_) => {  0 } ,
          } } ,
        Options::Option::Some(x) => {
          match b {
            Options::Option::None => {  0 } ,
            Options::Option::Some(y) => {  Bytes::address_eq(x, y) } ,
          } } ,
      }
    }

  fn aggr_assert_same_context_base(a: (Bytes::AddressRef, Bytes::AddressRef, Options::Option<Bytes::AddressRef>, Field),
        b: (Bytes::AddressRef, Bytes::AddressRef, Options::Option<Bytes::AddressRef>, Field)) -> () {
      let (spec_a, binding_a, _axioms_a, validator_a) = a;
      let (spec_b, binding_b, _axioms_b, validator_b) = b;
      assert_eq!(Bytes::address_eq(spec_a, spec_b), 1,
        "aggr: claims differ in specification digest");
      assert_eq!(Bytes::address_eq(binding_a, binding_b), 1,
        "aggr: claims differ in binding hash");
      assert_eq!(validator_a, validator_b,
        "aggr: claims differ in whether they assume their binding");
      ()
    }

  fn aggr_assert_axioms_merge(left: Options::Option<Bytes::AddressRef>,
        right: Options::Option<Bytes::AddressRef>,
        output: Options::Option<Bytes::AddressRef>) -> () {
      match left {
        Options::Option::None => {
          assert_eq!(aggr_opt_address_eq(right, output), 1,
            "aggr: claims differ in axioms");
          () } ,
        Options::Option::Some(la) => {
          match right {
            Options::Option::None => {
              assert_eq!(aggr_opt_address_eq(left, output), 1,
                "aggr: claims differ in axioms");
              () } ,
            Options::Option::Some(ra) => {
              match Bytes::address_eq(la, ra) {
                1 => {
                  assert_eq!(aggr_opt_address_eq(left, output), 1,
                    "aggr: claims differ in axioms");
                  () } ,
                _ => {
                  let Options::Option::Some(oa) = output;
                  let left_leaves = aggr_load_canonical_tree(la);
                  let right_leaves = aggr_load_canonical_tree(ra);
                  let out_leaves = aggr_load_canonical_tree(oa);
                  aggr_assert_union(left_leaves, right_leaves, out_leaves) } ,
              } } ,
          } } ,
      }
    }

  fn aggr_assert_same_context(a: (Bytes::AddressRef, Bytes::AddressRef, Options::Option<Bytes::AddressRef>, Field),
        b: (Bytes::AddressRef, Bytes::AddressRef, Options::Option<Bytes::AddressRef>, Field)) -> () {
      let (spec_a, binding_a, axioms_a, validator_a) = a;
      let (spec_b, binding_b, axioms_b, validator_b) = b;
      assert_eq!(Bytes::address_eq(spec_a, spec_b), 1,
        "aggr: claims differ in specification digest");
      assert_eq!(Bytes::address_eq(binding_a, binding_b), 1,
        "aggr: claims differ in binding hash");
      assert_eq!(aggr_opt_address_eq(axioms_a, axioms_b), 1,
        "aggr: claims differ in axioms");
      assert_eq!(validator_a, validator_b,
        "aggr: claims differ in whether they assume their binding");
      ()
    }

  fn aggr_load_preimage(digest: [Field; 8]) -> Bytes::Stream {
      let (idx, len) = hint::<(Field, Field)>("stark.io.digest", digest);
      let bytes = StarkIO::read_byte_stream(4, idx, len);
      assert_eq!(Blake3::pack_digest(Blake3::hash(bytes)), digest,
        "aggr: claim preimage digest mismatch");
      bytes
    }

  fn aggr_claim_field(claim: Lists::List<UInt64::U64>, index: Field) -> Field {
      Goldilocks::gl_val(Lists::lookup(claim, index))
    }

  fn aggr_claim_digest(claim: Lists::List<UInt64::U64>, start: Field) -> [Field; 8] {
      [aggr_claim_field(claim, start),
       aggr_claim_field(claim, start + 1),
       aggr_claim_field(claim, start + 2),
       aggr_claim_field(claim, start + 3),
       aggr_claim_field(claim, start + 4),
       aggr_claim_field(claim, start + 5),
       aggr_claim_field(claim, start + 6),
       aggr_claim_field(claim, start + 7)]
    }

  fn aggr_assert_digest(actual: [Field; 8], expected: [Field; 8]) -> () {
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

  fn aggr_only_claim(claims: Lists::List<Lists::List<UInt64::U64>>) -> Lists::List<UInt64::U64> {
      let Lists::Node::Cons(claim, rest) = (*(claims));
      let Lists::Node::Nil = (*(rest));
      claim
    }

  fn aggr_load_sys(kind: Field, ixvm_vk_digest: [Field; 8], self_vk_digest: [Field; 8])
        -> SystemDeserialize::Sys {

      let (sidx, slen) = hint::<(Field, Field)>("stark.io.info", (1, kind));
      let sbytes = StarkIO::read_byte_stream(1, sidx, slen);
      let digest = Blake3::pack_digest(Blake3::hash(sbytes));
      match kind {
        0 => {
          aggr_assert_digest(digest, ixvm_vk_digest) } ,
        _ => {
          aggr_assert_digest(digest, self_vk_digest) } ,
      };
      let (sys, srest) = SystemDeserialize::read_system(sbytes);
      let Lists::Node::Nil = (*(srest));
      sys
    }

  fn aggr_verify_child(sys: SystemDeserialize::Sys, key: Field) -> Lists::List<Lists::List<UInt64::U64>> {
      let (idx, len) = hint::<(Field, Field)>("stark.io.info", (0, key));
      let (cidx, clen) = hint::<(Field, Field)>("stark.io.info", (2, key));
      let cbytes = StarkIO::read_byte_stream(2, cidx, clen);
      let (claims, crest) = StarkVerifier::read_claims(cbytes);
      let Lists::Node::Nil = (*(crest));
      assert_eq!(StarkVerifier::verify_batch_at(sys, idx, len, claims), 1);
      claims
    }

  fn aggr_child_check_env_digest(kind: Field, key: Field,
        ixvm_vk_digest: [Field; 8], self_vk_digest: [Field; 8],
        verify_idx: Field, aggr_idx: Field, allowed_digest: [Field; 8]) -> [Field; 8] {
      let sys = aggr_load_sys(kind, ixvm_vk_digest, self_vk_digest);
      let claim = aggr_only_claim(aggr_verify_child(sys, key));
      assert_eq!(aggr_claim_field(claim, 0), 1,
        "aggr: child has the wrong claim channel");
      match kind {
        0 => {
          assert_eq!(Lists::length(claim), 10,
            "aggr: IxVM child must expose a 10-word verify_claim claim");
          assert_eq!(aggr_claim_field(claim, 1), verify_idx,
            "aggr: IxVM child has the wrong entrypoint");
          aggr_claim_digest(claim, 2) } ,
        _ => {
          assert_eq!(Lists::length(claim), 18,
            "aggr: recursive child must expose an 18-word ix_aggr claim");
          assert_eq!(aggr_claim_field(claim, 1), aggr_idx,
            "aggr: recursive child has the wrong entrypoint");
          aggr_assert_digest(aggr_claim_digest(claim, 2), allowed_digest);
          aggr_claim_digest(claim, 10) } ,
      }
    }

  fn aggr_wrap(kind: Field, ixvm_vk_digest: [Field; 8], self_vk_digest: [Field; 8],
        verify_idx: Field, aggr_idx: Field, allowed_digest: [Field; 8],
        out_claim_digest: [Field; 8]) -> () {
      let child = aggr_child_check_env_digest(kind, 0,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      aggr_assert_digest(child, out_claim_digest)
    }

  fn aggr_pair(left_kind: Field, right_kind: Field,
        ixvm_vk_digest: [Field; 8], self_vk_digest: [Field; 8],
        verify_idx: Field, aggr_idx: Field, allowed_digest: [Field; 8],
        out_claim_digest: [Field; 8]) -> () {
      let left_digest = aggr_child_check_env_digest(left_kind, 0,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      let right_digest = aggr_child_check_env_digest(right_kind, 1,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      let (left_ctx, left_root, left_asm) =
        aggr_parse_check_env(aggr_load_preimage(left_digest));
      let (right_ctx, right_root, right_asm) =
        aggr_parse_check_env(aggr_load_preimage(right_digest));

      let (oidx, olen) = hint::<(Field, Field)>("stark.io.info", (2, 2));
      let output_bytes = StarkIO::read_byte_stream(2, oidx, olen);
      assert_eq!(Blake3::pack_digest(Blake3::hash(output_bytes)), out_claim_digest,
        "aggr: output claim digest mismatch");
      let (output_ctx, output_root, output_asm) = aggr_parse_check_env(output_bytes);
      aggr_assert_same_context_base(left_ctx, right_ctx);
      aggr_assert_same_context_base(left_ctx, output_ctx);
      let (_ls, _lb, left_axioms, _lv) = left_ctx;
      let (_rs, _rb, right_axioms, _rv) = right_ctx;
      let (_os, _ob, output_axioms, _ov) = output_ctx;
      aggr_assert_axioms_merge(left_axioms, right_axioms, output_axioms);

      let left_subjects = aggr_load_canonical_tree(left_root);
      let right_subjects = aggr_load_canonical_tree(right_root);
      let left_assumptions = aggr_load_optional_tree(left_asm);
      let right_assumptions = aggr_load_optional_tree(right_asm);
      let output_subjects = aggr_load_canonical_tree(output_root);
      let output_assumptions = aggr_load_optional_tree(output_asm);

      aggr_assert_disjoint(left_subjects, left_assumptions);
      aggr_assert_disjoint(right_subjects, right_assumptions);
      aggr_assert_disjoint_union(left_subjects, right_subjects, output_subjects);
      aggr_assert_difference(left_assumptions, right_assumptions,
        output_subjects, output_assumptions);
      ()
    }

  fn aggr_pair_structural(left_kind: Field, right_kind: Field,
        ixvm_vk_digest: [Field; 8], self_vk_digest: [Field; 8],
        verify_idx: Field, aggr_idx: Field, allowed_digest: [Field; 8],
        out_claim_digest: [Field; 8]) -> () {
      let left_digest = aggr_child_check_env_digest(left_kind, 0,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      let right_digest = aggr_child_check_env_digest(right_kind, 1,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      let (left_ctx, left_root, left_asm) =
        aggr_parse_check_env(aggr_load_preimage(left_digest));
      let (right_ctx, right_root, right_asm) =
        aggr_parse_check_env(aggr_load_preimage(right_digest));

      let (oidx, olen) = hint::<(Field, Field)>("stark.io.info", (2, 2));
      let output_bytes = StarkIO::read_byte_stream(2, oidx, olen);
      assert_eq!(Blake3::pack_digest(Blake3::hash(output_bytes)), out_claim_digest,
        "aggr structural: output claim digest mismatch");
      let (output_ctx, output_root, output_asm) = aggr_parse_check_env(output_bytes);
      aggr_assert_same_context_base(left_ctx, right_ctx);
      aggr_assert_same_context_base(left_ctx, output_ctx);
      let (_ls, _lb, left_axioms, _lv) = left_ctx;
      let (_rs, _rb, right_axioms, _rv) = right_ctx;
      let (_os, _ob, output_axioms, _ov) = output_ctx;
      aggr_assert_axioms_merge(left_axioms, right_axioms, output_axioms);

      assert_eq!(Bytes::address_eq(left_root, right_root), 0,
        "aggr structural: child subject roots must be distinct");
      let expected_root = aggr_node_hash(left_root, right_root);
      assert_eq!(Bytes::address_eq(output_root, expected_root), 1,
        "aggr structural: output subject root is not nodeHash(left, right)");

      let left_assumptions = aggr_load_optional_tree(left_asm);
      let right_assumptions = aggr_load_optional_tree(right_asm);
      let output_assumptions = aggr_load_optional_tree(output_asm);
      aggr_assert_structural_difference(left_assumptions, right_assumptions,
        left_root, right_root, output_assumptions);
      ()
    }

  fn aggr_discharge_binding(kind: Field,
        ixvm_vk_digest: [Field; 8], self_vk_digest: [Field; 8],
        verify_idx: Field, aggr_idx: Field, allowed_digest: [Field; 8],
        out_claim_digest: [Field; 8]) -> () {
      let child_digest = aggr_child_check_env_digest(kind, 0,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      let binding_digest = aggr_child_check_env_digest(0, 1,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      let (child_ctx, child_root, child_asm) =
        aggr_parse_check_env(aggr_load_preimage(child_digest));
      let (spec, binding, axioms, validator) = child_ctx;
      assert_eq!(validator, 4,
        "aggr discharge: the claim does not assume its binding");
      let (bound_spec, bound_binding) =
        aggr_parse_binding(aggr_load_preimage(binding_digest));
      assert_eq!(Bytes::address_eq(spec, bound_spec), 1,
        "aggr discharge: the binding claim is for another specification digest");
      assert_eq!(Bytes::address_eq(binding, bound_binding), 1,
        "aggr discharge: the binding claim is for another binding");

      let (oidx, olen) = hint::<(Field, Field)>("stark.io.info", (2, 2));
      let output_bytes = StarkIO::read_byte_stream(2, oidx, olen);
      assert_eq!(Blake3::pack_digest(Blake3::hash(output_bytes)), out_claim_digest,
        "aggr discharge: output claim digest mismatch");
      let (output_ctx, output_root, output_asm) = aggr_parse_check_env(output_bytes);
      aggr_assert_same_context((spec, binding, axioms, 3), output_ctx);
      assert_eq!(Bytes::address_eq(child_root, output_root), 1,
        "aggr discharge: output subject root differs from the child's");
      assert_eq!(aggr_opt_address_eq(child_asm, output_asm), 1,
        "aggr discharge: output assumptions differ from the child's");
      ()
    }

  fn aggr_is_class_role(i: Field) -> Field {
      match i {
        0 => {  1 } ,
        1 => {  1 } ,
        2 => {  1 } ,
        29 => {  1 } ,
        30 => {  1 } ,
        31 => {  1 } ,
        36 => {  1 } ,
        37 => {  1 } ,
        38 => {  1 } ,
        39 => {  1 } ,
        40 => {  1 } ,
        56 => {  1 } ,
        57 => {  1 } ,
        _ => {  0 } ,
      }
    }

  fn aggr_class_walk(stream: Bytes::Stream, i: Field, remaining: Field) -> Lists::List<Bytes::AddressRef> {
      match remaining {
        0 => {  (&(Lists::Node::Nil)) } ,
        _ => {
          let (role, s) = aggr_read_byte(stream);
          assert_eq!(UInt8::to_field(role), i,
            "aggr cross-binding: the binding does not bind every role in order");
          let (addr, s2) = aggr_read_address(s);
          let rest = aggr_class_walk(s2, i + 1, remaining - 1);
          match aggr_is_class_role(i) {
            1 => {  (&(Lists::Node::Cons(addr, rest))) } ,
            _ => {  rest } ,
          } } ,
      }
    }

  fn aggr_put_addresses(addrs: Lists::List<Bytes::AddressRef>, tail: Bytes::Stream) -> Bytes::Stream {
      match (*(addrs)) {
        Lists::Node::Nil => {  tail } ,
        Lists::Node::Cons(a, rest) => {  aggr_put_address(a, aggr_put_addresses(rest, tail)) } ,
      }
    }

  -- A complete role table binds every role of the specification, in role order: the 103
  -- kernel roles and the five inert compiler-trust roles (103-107), 108 in all (`Ix.Kernel.Role.all`,
  -- IxVM `KernelRoleSpec::role_count`). The literal class reads the class roles among them.

  fn aggr_binding_class(binding: Bytes::AddressRef) -> Bytes::AddressRef {
      let bytes = aggr_load_preimage(aggr_pack_address(binding));
      let (tag0, s) = aggr_read_byte(bytes);
      assert_eq!(UInt8::to_field(tag0), 232, "aggr cross-binding: not a role binding section");
      let (tag1, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(tag1), 3, "aggr cross-binding: not a role binding section");
      let (_version, s) = aggr_read_byte(s);
      let (count, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(count), 108,
        "aggr cross-binding: the binding does not bind every role");
      let addrs = aggr_class_walk(s, 0, 108);
      let body = aggr_put_addresses(addrs, (&(Lists::Node::Nil)));
      Blake3::bytes_to_addr((&(Lists::Node::Cons(UInt8::BYTE_232, (&(Lists::Node::Cons(UInt8::BYTE_4, body)))))))
    }

  fn aggr_context_class(ctx: (Bytes::AddressRef, Bytes::AddressRef, Options::Option<Bytes::AddressRef>, Field)) -> Bytes::AddressRef {
      let (_spec, binding, _axioms, validator) = ctx;
      assert_eq!((validator - 3) * (validator - 5), 0,
        "aggr cross-binding: the claim assumes its binding");
      match validator {
        5 => {  binding } ,
        _ => {  aggr_binding_class(binding) } ,
      }
    }

  fn aggr_cross_binding(ixvm_vk_digest: [Field; 8], self_vk_digest: [Field; 8],
        verify_idx: Field, aggr_idx: Field, allowed_digest: [Field; 8],
        out_claim_digest: [Field; 8]) -> () {
      let left_digest = aggr_child_check_env_digest(1, 0,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      let right_digest = aggr_child_check_env_digest(1, 1,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      let (left_ctx, left_root, left_asm) =
        aggr_parse_check_env(aggr_load_preimage(left_digest));
      let (right_ctx, right_root, right_asm) =
        aggr_parse_check_env(aggr_load_preimage(right_digest));
      let left_class = aggr_context_class(left_ctx);
      let right_class = aggr_context_class(right_ctx);
      assert_eq!(Bytes::address_eq(left_class, right_class), 1,
        "aggr cross-binding: the bindings' literal classes differ");
      let (left_spec, _lb, left_axioms, _lv) = left_ctx;
      let (right_spec, _rb, right_axioms, _rv) = right_ctx;

      let (oidx, olen) = hint::<(Field, Field)>("stark.io.info", (2, 2));
      let output_bytes = StarkIO::read_byte_stream(2, oidx, olen);
      assert_eq!(Blake3::pack_digest(Blake3::hash(output_bytes)), out_claim_digest,
        "aggr cross-binding: output claim digest mismatch");
      let (output_ctx, output_root, output_asm) = aggr_parse_check_env(output_bytes);
      let (_os, _ob, output_axioms, _ov) = output_ctx;
      aggr_assert_same_context_base((left_spec, left_class, left_axioms, 5), output_ctx);
      aggr_assert_same_context_base((right_spec, right_class, right_axioms, 5), output_ctx);
      aggr_assert_axioms_merge(left_axioms, right_axioms, output_axioms);

      assert_eq!(Bytes::address_eq(left_root, right_root), 0,
        "aggr cross-binding: child subject roots must be distinct");
      let expected_root = aggr_node_hash(left_root, right_root);
      assert_eq!(Bytes::address_eq(output_root, expected_root), 1,
        "aggr cross-binding: output subject root is not nodeHash(left, right)");
      let left_assumptions = aggr_load_optional_tree(left_asm);
      let right_assumptions = aggr_load_optional_tree(right_asm);
      let output_assumptions = aggr_load_optional_tree(output_asm);
      aggr_assert_structural_difference(left_assumptions, right_assumptions,
        left_root, right_root, output_assumptions);
      ()
    }

  fn aggr_catalog_part(digest: [Field; 8]) -> Lists::List<Bytes::AddressRef> {
      let bytes = aggr_load_preimage(digest);
      let (tag, _rest) = aggr_read_byte(bytes);
      match UInt8::to_field(tag) {
        229 => {
          let (ctx, _root, asm) = aggr_parse_check_env(bytes);
          let (_spec, _binding, _axioms, validator) = ctx;
          assert_eq!((validator - 3) * (validator - 5), 0,
            "aggr catalog: a member claim assumes its binding");
          assert_eq!(aggr_opt_address_eq(asm, Options::Option::None), 1,
            "aggr catalog: a member claim has assumptions");
          (&(Lists::Node::Cons(Blake3::bytes_to_addr(bytes), (&(Lists::Node::Nil))))) } ,
        _ => {  aggr_load_canonical_tree(aggr_parse_catalog(bytes)) } ,
      }
    }

  fn aggr_catalog_join(ixvm_vk_digest: [Field; 8], self_vk_digest: [Field; 8],
        verify_idx: Field, aggr_idx: Field, allowed_digest: [Field; 8],
        out_claim_digest: [Field; 8]) -> () {
      let left_digest = aggr_child_check_env_digest(1, 0,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      let right_digest = aggr_child_check_env_digest(1, 1,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      let left = aggr_catalog_part(left_digest);
      let right = aggr_catalog_part(right_digest);

      let (oidx, olen) = hint::<(Field, Field)>("stark.io.info", (2, 2));
      let output_bytes = StarkIO::read_byte_stream(2, oidx, olen);
      assert_eq!(Blake3::pack_digest(Blake3::hash(output_bytes)), out_claim_digest,
        "aggr catalog: output claim digest mismatch");
      let output = aggr_load_canonical_tree(aggr_parse_catalog(output_bytes));
      aggr_assert_union(left, right, output);
      ()
    }

  fn aggr_parse_range(bytes: Bytes::Stream) -> (Bytes::AddressRef, UInt64::U64, UInt64::U64, ProofDeserialize::Ext) {
      let (tag, s) = aggr_read_byte(bytes);
      assert_eq!(UInt8::to_field(tag), 82, "aggr range: statement has the wrong tag");
      let (d, s2) = aggr_read_address(s);
      let (lo, s3) = ProofDeserialize::read_u64(s2);
      let (hi, s4) = ProofDeserialize::read_u64(s3);
      let (r0, s5) = ProofDeserialize::read_u64(s4);
      let (r1, stop) = ProofDeserialize::read_u64(s5);
      let Lists::Node::Nil = (*(stop));
      assert_eq!(Goldilocks::gl_lt_p(lo), 1, "aggr range: non-canonical range start");
      assert_eq!(Goldilocks::gl_lt_p(hi), 1, "aggr range: non-canonical range end");
      assert_eq!(Goldilocks::gl_lt_p(r0), 1, "aggr range: non-canonical residual limb 0");
      assert_eq!(Goldilocks::gl_lt_p(r1), 1, "aggr range: non-canonical residual limb 1");
      (d, lo, hi, [Goldilocks::gl_val(r0), Goldilocks::gl_val(r1)])
    }

  fn aggr_read_digest(s: Bytes::Stream) -> (ProofDeserialize::DigestP, Bytes::Stream) {
      let (a, s1) = ProofDeserialize::read_u64(s);
      let (b, s2) = ProofDeserialize::read_u64(s1);
      let (c, s3) = ProofDeserialize::read_u64(s2);
      let (d, s4) = ProofDeserialize::read_u64(s3);
      ((&([a, b, c, d])), s4)
    }

  fn aggr_read_cap_n(s: Bytes::Stream, n: Field) -> (ProofDeserialize::MerkleCap, Bytes::Stream) {
      match n {
        0 => {  ((&(Lists::Node::Nil)), s) } ,
        _ => {
          let (x, s1) = aggr_read_digest(s);
          let (rest, s2) = aggr_read_cap_n(s1, n - 1);
          ((&(Lists::Node::Cons(x, rest))), s2) } ,
      }
    }

  fn aggr_read_bits_n(s: Bytes::Stream, n: Field) -> (Lists::List<Field>, Bytes::Stream) {
      match n {
        0 => {  ((&(Lists::Node::Nil)), s) } ,
        _ => {
          let (b, s1) = aggr_read_byte(s);
          let (rest, s2) = aggr_read_bits_n(s1, n - 1);
          ((&(Lists::Node::Cons(UInt8::to_field(b), rest))), s2) } ,
      }
    }

  fn aggr_read_bytes_n(s: Bytes::Stream, n: Field) -> (Lists::List<UInt8::U8>, Bytes::Stream) {
      match n {
        0 => {  ((&(Lists::Node::Nil)), s) } ,
        _ => {
          let (b, s1) = aggr_read_byte(s);
          let (rest, s2) = aggr_read_bytes_n(s1, n - 1);
          ((&(Lists::Node::Cons(b, rest))), s2) } ,
      }
    }

  fn aggr_read_header(s: Bytes::Stream) -> (ProofDeserialize::ShardHeader, Bytes::Stream) {
      let (na, s1) = ProofDeserialize::read_count(s);
      let (active, s2) = aggr_read_bits_n(s1, na);
      let (nc, s3) = ProofDeserialize::read_count(s2);
      assert_eq!(nc, 1, "aggr range: shard header Merkle cap must have length 1");
      let (cap, s4) = aggr_read_cap_n(s3, nc);
      let (nl, s5) = ProofDeserialize::read_count(s4);
      let (lds, s6) = aggr_read_bytes_n(s5, nl);
      let (claims, s7) = StarkVerifier::read_claims(s6);
      (ProofDeserialize::ShardHeader::Mk(active, cap, lds, claims), s7)
    }

  fn aggr_read_headers_n(s: Bytes::Stream, n: Field) -> (Lists::List<ProofDeserialize::ShardHeader>, Bytes::Stream) {
      match n {
        0 => {  ((&(Lists::Node::Nil)), s) } ,
        _ => {
          let (h, s1) = aggr_read_header(s);
          let (rest, s2) = aggr_read_headers_n(s1, n - 1);
          ((&(Lists::Node::Cons(h, rest))), s2) } ,
      }
    }

  fn aggr_read_message(s: Bytes::Stream) -> (ProofDeserialize::BatchMessage, Bytes::Stream) {
      let (args, s1) = StarkVerifier::read_one_claim(s);
      assert_eq!(ProofDeserialize::assert_u64_list_lt_p(args), 1);
      let (mult, s2) = ProofDeserialize::read_u64(s1);
      assert_eq!(Goldilocks::gl_lt_p(mult), 1);
      (ProofDeserialize::BatchMessage::Mk(args, mult), s2)
    }

  fn aggr_read_messages_n(s: Bytes::Stream, n: Field) -> (Lists::List<ProofDeserialize::BatchMessage>, Bytes::Stream) {
      match n {
        0 => {  ((&(Lists::Node::Nil)), s) } ,
        _ => {
          let (m, s1) = aggr_read_message(s);
          let (rest, s2) = aggr_read_messages_n(s1, n - 1);
          ((&(Lists::Node::Cons(m, rest))), s2) } ,
      }
    }

  fn aggr_load_preamble(key: Field, d: Bytes::AddressRef) -> (Lists::List<ProofDeserialize::ShardHeader>, Lists::List<ProofDeserialize::BatchMessage>) {
      let (idx, len) = hint::<(Field, Field)>("stark.io.info", (0, key));
      let bytes = StarkIO::read_byte_stream(0, idx, len);
      assert_eq!(Bytes::address_eq(Blake3::bytes_to_addr(bytes), d), 1,
        "aggr range: preamble does not hash to the statement's batch digest");
      let (nh, s1) = ProofDeserialize::read_count(bytes);
      let (headers, s2) = aggr_read_headers_n(s1, nh);
      let (nm, s3) = ProofDeserialize::read_count(s2);
      let (messages, stop) = aggr_read_messages_n(s3, nm);
      let Lists::Node::Nil = (*(stop));
      (headers, messages)
    }

  fn aggr_batch_challenges(sys: SystemDeserialize::Sys, headers: Lists::List<ProofDeserialize::ShardHeader>,
        messages: Lists::List<ProofDeserialize::BatchMessage>) -> (ProofDeserialize::Ext, ProofDeserialize::Ext, Bytes::Stream) {
      let SystemDeserialize::Sys::Mk(_params, tlimbs, _circuits, commit, _prep_indices) = sys;
      let prep_cap = StarkVerifier::opt_commit_cap(commit);
      Transcript::batch_fiat_shamir(tlimbs, prep_cap, headers, messages)
    }

  fn aggr_verify_range(sys: SystemDeserialize::Sys, headers: Lists::List<ProofDeserialize::ShardHeader>, i: Field, shard: Field,
        n: Field, input: Bytes::Stream, lch: ProofDeserialize::Ext, fch: ProofDeserialize::Ext, acc: ProofDeserialize::Ext) -> (ProofDeserialize::Ext, Field) {
      match n {
        0 => {  (acc, i) } ,
        _ => {
          let Lists::Node::Cons(h, hrest) = (*(headers));
          let (p, j) = ProofDeserialize::read_proof(i);
          let r = StarkVerifier::verify_shard(sys, h, shard, p, input, lch, fch);
          aggr_verify_range(sys, hrest, j, shard + 1, n - 1, input, lch, fch,
            Goldilocks::eg_add(acc, r)) } ,
      }
    }

  fn aggr_output_range(out_claim_digest: [Field; 8]) -> (Bytes::AddressRef, UInt64::U64, UInt64::U64, ProofDeserialize::Ext) {
      let (oidx, olen) = hint::<(Field, Field)>("stark.io.info", (2, 2));
      let output_bytes = StarkIO::read_byte_stream(2, oidx, olen);
      assert_eq!(Blake3::pack_digest(Blake3::hash(output_bytes)), out_claim_digest,
        "aggr range: output statement digest mismatch");
      aggr_parse_range(output_bytes)
    }

  fn aggr_child_range(key: Field, ixvm_vk_digest: [Field; 8], self_vk_digest: [Field; 8],
        verify_idx: Field, aggr_idx: Field, allowed_digest: [Field; 8])
        -> (Bytes::AddressRef, UInt64::U64, UInt64::U64, ProofDeserialize::Ext) {
      let digest = aggr_child_check_env_digest(1, key,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      aggr_parse_range(aggr_load_preimage(digest))
    }

  fn aggr_range_leaf(ixvm_vk_digest: [Field; 8], self_vk_digest: [Field; 8],
        out_claim_digest: [Field; 8]) -> () {
      let sys = aggr_load_sys(0, ixvm_vk_digest, self_vk_digest);
      let (d, lo_limb, hi_limb, r) = aggr_output_range(out_claim_digest);
      let (headers, messages) = aggr_load_preamble(0, d);
      let (lch, fch, input) = aggr_batch_challenges(sys, headers, messages);
      assert_eq!(StarkVerifier::bytes8_le(lo_limb, hi_limb), 1,
        "aggr range: the range ends before it starts");
      let lo = UInt64::to_field(lo_limb);
      let n = UInt64::to_field(hi_limb) - lo;
      let (pidx, plen) = hint::<(Field, Field)>("stark.io.info", (0, 1));
      let (count, j) = ProofDeserialize::read_count_at(pidx);
      assert_eq!(count, n, "aggr range: proof count differs from the range");
      let (total, stop) = aggr_verify_range(sys, Lists::drop(headers, lo), j, lo,
        n, input, lch, fch, [0, 0]);
      assert_eq!(stop, pidx + plen, "aggr range: trailing bytes after the proofs");
      assert_eq!(Goldilocks::eg_eq(total, r), 1,
        "aggr range: residual sum differs from the statement");
      ()
    }

  fn aggr_range_join(ixvm_vk_digest: [Field; 8], self_vk_digest: [Field; 8],
        verify_idx: Field, aggr_idx: Field, allowed_digest: [Field; 8],
        out_claim_digest: [Field; 8]) -> () {
      let (ld, llo, lhi, lr) = aggr_child_range(0,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      let (rd, rlo, rhi, rr) = aggr_child_range(1,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      let (d, lo, hi, r) = aggr_output_range(out_claim_digest);
      assert_eq!(Bytes::address_eq(ld, rd), 1,
        "aggr range: children verify different batches");
      assert_eq!(Bytes::address_eq(d, ld), 1,
        "aggr range: output names a different batch than the children");
      assert_eq!(UInt64::to_field(lhi), UInt64::to_field(rlo),
        "aggr range: children are not adjacent");
      assert_eq!(UInt64::to_field(lo), UInt64::to_field(llo),
        "aggr range: output starts elsewhere than the left child");
      assert_eq!(UInt64::to_field(hi), UInt64::to_field(rhi),
        "aggr range: output ends elsewhere than the right child");
      assert_eq!(Goldilocks::eg_eq(Goldilocks::eg_add(lr, rr), r), 1,
        "aggr range: output residual is not the children's sum");
      ()
    }

  fn aggr_range_root(ixvm_vk_digest: [Field; 8], self_vk_digest: [Field; 8],
        verify_idx: Field, aggr_idx: Field, allowed_digest: [Field; 8],
        out_claim_digest: [Field; 8]) -> () {
      let (d, lo, hi, r) = aggr_child_range(0,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      let sys = aggr_load_sys(0, ixvm_vk_digest, self_vk_digest);
      let (headers, messages) = aggr_load_preamble(1, d);
      let k = Lists::length(headers);
      assert_eq!(StarkVerifier::assert_shard_count_ok(k), 1);
      assert_eq!(StarkVerifier::assert_batch_bounds(sys, headers), 1);
      assert_eq!(UInt64::to_field(lo), 0,
        "aggr range: root range does not start at shard 0");
      assert_eq!(UInt64::to_field(hi), k,
        "aggr range: root range does not end at the last shard");
      assert_eq!(StarkVerifier::assert_closure_pairs(messages, 0, 0), 1);
      let SystemDeserialize::Sys::Mk(_params, _tlimbs, circuits, _commit, _prep_indices) = sys;
      assert_eq!(StarkVerifier::assert_closure_widths_ok(circuits, headers, messages), 1);
      let (lch, fch, _input) = aggr_batch_challenges(sys, headers, messages);
      let total = StarkVerifier::messages_acc(r, messages, lch, fch);
      assert_eq!(StarkVerifier::ext_is_zero(total), 1, "aggr range: the batch does not balance");
      let claim = aggr_only_claim(StarkVerifier::batch_claims(headers));
      assert_eq!(Lists::length(claim), 10,
        "aggr range: batch must carry a 10-word verify_claim claim");
      assert_eq!(aggr_claim_field(claim, 0), 1,
        "aggr range: batch claim has the wrong channel");
      assert_eq!(aggr_claim_field(claim, 1), verify_idx,
        "aggr range: batch claim has the wrong entrypoint");
      aggr_assert_digest(aggr_claim_digest(claim, 2), out_claim_digest)
    }

  -- ── Shape 17: Dynamic Circuit Linking (`aggr_dynamic_link`, tag 0xE8 0x0D) ──

  fn aggr_parse_dynamic_link(bytes: Bytes::Stream)
        -> (Bytes::AddressRef, UInt64::U64, Lists::List<UInt64::U64>, Lists::List<UInt64::U64>, AggrOptBridge) {
      let (tag0, s) = aggr_read_byte(bytes);
      assert_eq!(UInt8::to_field(tag0), 232, "aggr dynamic link: wrong tag byte 0");
      let (tag1, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(tag1), 13, "aggr dynamic link: wrong tag byte 1");
      let (vk_digest, s) = aggr_read_address(s);
      let (entry_idx, s) = aggr_read_u64(s);
      let (nin, s) = aggr_read_u32_le(s);
      let (pub_inputs, s) = aggr_read_u64_list_n(s, nin);
      let (nout, s) = aggr_read_u32_le(s);
      let (pub_outputs, s) = aggr_read_u64_list_n(s, nout);
      let (btag, s) = aggr_read_byte(s);
      match UInt8::to_field(btag) {
        0 => {
          let Lists::Node::Nil = (*(s));
          (vk_digest, entry_idx, pub_inputs, pub_outputs, AggrOptBridge::NoBridge) } ,
        1 => {
          let (spec, s1) = aggr_read_address(s);
          let (binding, s2) = aggr_read_address(s1);
          let (target_const, s3) = aggr_read_address(s2);
          let (codec, s4) = aggr_read_u64(s3);
          let (cert_const, stop) = aggr_read_address(s4);
          let Lists::Node::Nil = (*(stop));
          (vk_digest, entry_idx, pub_inputs, pub_outputs,
            AggrOptBridge::SomeBridge(spec, binding, target_const, codec, cert_const)) } ,
      }
    }

  -- Enforce the uniform Multi-STARK security envelope (`Ix.Aiur.meetsSecurityFloor` +
  -- `Ix.Cert.MultiStark.checkParams` + explicit per-`log_blowup` provable UD query floor)
  -- on an external accelerator verifying key:
  -- `cap_height = 0`, `log_final_poly_len = 0`, `max_log_arity = 1`,
  -- `1 <= log_blowup <= 4`, `num_queries >= 1`, `commit_pow_bits <= 32`,
  -- `query_pow_bits <= 32`, `log_blowup * num_queries + query_pow_bits >= 220`,
  -- and provable unique-decoding query soundness `>= 80` bits:
  -- `ud_millibits(log_blowup) * num_queries + 1000 * query_pow_bits >= 80000`,
  -- where `ud_millibits` is `floor(-1000 * log2((1 + 2^(-log_blowup)) / 2))`:
  -- `1 -> 415`, `2 -> 678`, `3 -> 830`, `4 -> 912` (blocking 50.2-bit `(4, 55, 0)` configs).
  fn aggr_assert_security_envelope(sys: SystemDeserialize::Sys) -> () {
      let SystemDeserialize::Sys::Mk(params, _tlimbs, _circuits, _commit, _prep_indices) = sys;
      let SystemDeserialize::SysParams::Mk(log_blowup, cap_height, log_final_poly_len,
        max_log_arity, num_queries, commit_pow_bits, query_pow_bits) = params;
      assert_eq!(cap_height, 0, "aggr dynamic link: cap_height must be 0");
      assert_eq!(log_final_poly_len, 0, "aggr dynamic link: log_final_poly_len must be 0");
      assert_eq!(max_log_arity, 1, "aggr dynamic link: max_log_arity must be 1");
      assert_eq!(UInt32::less_than_fields(0, log_blowup), 1,
        "aggr dynamic link: log_blowup must be >= 1");
      assert_eq!(UInt32::less_than_fields(log_blowup, 5), 1,
        "aggr dynamic link: log_blowup must be <= 4");
      assert_eq!(UInt32::less_than_fields(0, num_queries), 1,
        "aggr dynamic link: num_queries must be >= 1");
      assert_eq!(UInt32::less_than_fields(commit_pow_bits, 33), 1,
        "aggr dynamic link: commit_pow_bits exceeds 32");
      assert_eq!(UInt32::less_than_fields(query_pow_bits, 33), 1,
        "aggr dynamic link: query_pow_bits exceeds 32");
      assert_eq!(UInt32::less_than_fields(219, log_blowup * num_queries + query_pow_bits), 1,
        "aggr dynamic link: security bits below floor 220");
      let ud_millibits = match log_blowup {
        1 => {  415 } ,
        2 => {  678 } ,
        3 => {  830 } ,
        4 => {  912 } ,
      };
      assert_eq!(UInt32::less_than_fields(79999, ud_millibits * num_queries + 1000 * query_pow_bits), 1,
        "aggr dynamic link: provable UD query soundness below 80-bit floor");
      ()
    }

  fn aggr_parse_check(bytes: Bytes::Stream)
        -> ((Bytes::AddressRef, Bytes::AddressRef, Options::Option<Bytes::AddressRef>, Field), Bytes::AddressRef, Options::Option<Bytes::AddressRef>) {
      let (tag, s) = aggr_read_byte(bytes);
      assert_eq!(UInt8::to_field(tag), 228, "aggr: claim is not Check");
      let (format, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(format), 4, "aggr: unsupported object format");
      let (validator_byte, s) = aggr_read_byte(s);
      let validator = UInt8::to_field(validator_byte);
      assert_eq!((validator - 3) * (validator - 4), 0,
        "aggr: wrong validator identity");
      let (spec, s) = aggr_read_address(s);
      let (binding, s) = aggr_read_address(s);
      let (axioms, s) = aggr_get_opt_address(s);
      let (const_addr, s2) = aggr_read_address(s);
      let (assumptions, stop) = aggr_get_opt_address(s2);
      let Lists::Node::Nil = (*(stop));
      ((spec, binding, axioms, validator), const_addr, assumptions)
    }

  -- Enforce codec-specific separation of `pub_inputs` and `pub_outputs` arities:
  -- `ixonAddrPair` (`codec == 1`) requires strictly `8` input words + `8` output words;
  -- `ixonAddrSingle` (`codec == 2`) requires strictly `8` input words + `0` output words.
  fn aggr_assert_codec_arity(codec: UInt64::U64,
        pub_inputs: Lists::List<UInt64::U64>, pub_outputs: Lists::List<UInt64::U64>) -> () {
      let two = [UInt8::BYTE_2, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0,
                 UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0];
      match UInt64::eq(codec, UInt64::ONE) {
        1 => {
          assert_eq!(Lists::length(pub_inputs), 8,
            "aggr dynamic link: ixonAddrPair requires 8 pub_inputs words");
          assert_eq!(Lists::length(pub_outputs), 8,
            "aggr dynamic link: ixonAddrPair requires 8 pub_outputs words");
          () } ,
        _ => {
          match UInt64::eq(codec, two) {
            1 => {
              assert_eq!(Lists::length(pub_inputs), 8,
                "aggr dynamic link: ixonAddrSingle requires 8 pub_inputs words");
              assert_eq!(Lists::length(pub_outputs), 0,
                "aggr dynamic link: ixonAddrSingle requires 0 pub_outputs words");
              () } ,
            _ => { () } ,
          } } ,
      }
    }

  -- Verify that `cert_const` is attested by an unconditional, zero-axiom validator-3 IxVM/aggr
  -- proof under the exact `(expected_spec, expected_binding)` committed in `BridgeBinding`.
  -- Note: Shape 17 verifies computational trace soundness and cryptographic attestation of
  -- `cert_const` under `(expected_spec, expected_binding)`; semantic interpretation of
  -- `cert_const` is enforced by the Mode-3a verifier allowlist (`ClaimPolicy`) pinning the full
  -- `(vkDigest, entryIdx, codec = ixonAddrPair, targetConst, certConst, evalType)` tuple in
  -- `LinkedCircuitEntry` committed into validator `12`/`13` claims.
  fn aggr_verify_bridge_cert(expected_spec: Bytes::AddressRef, expected_binding: Bytes::AddressRef,
        cert_const: Bytes::AddressRef,
        ixvm_vk_digest: [Field; 8], self_vk_digest: [Field; 8],
        verify_idx: Field, aggr_idx: Field, allowed_digest: [Field; 8]) -> () {
      let (kidx, klen) = hint::<(Field, Field)>("stark.io.info", (6, 1));
      assert_eq!(klen, 1, "aggr dynamic link: bridge cert kind hint must be 1 byte");
      let kstream = StarkIO::read_byte_stream(6, kidx, klen);
      let (kbyte, kstop) = aggr_read_byte(kstream);
      let Lists::Node::Nil = (*(kstop));
      let cert_kind = UInt8::to_field(kbyte);
      assert_eq!(cert_kind * (cert_kind - 1), 0,
        "aggr dynamic link: bridge cert kind must be 0 or 1");
      let cert_digest = aggr_child_check_env_digest(cert_kind, 1,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      let cert_bytes = aggr_load_preimage(cert_digest);
      let cert_claim_addr = Blake3::bytes_to_addr(cert_bytes);
      let (tag, _rest) = aggr_read_byte(cert_bytes);
      match UInt8::to_field(tag) {
        228 => {
          let (ctx, checked_const, asm) = aggr_parse_check(cert_bytes);
          let (spec, binding, axioms, validator) = ctx;
          assert_eq!(validator, 3,
            "aggr dynamic link: bridge cert check claim must validate its binding");
          assert_eq!(Bytes::address_eq(spec, expected_spec), 1,
            "aggr dynamic link: bridge cert specification digest mismatch");
          assert_eq!(Bytes::address_eq(binding, expected_binding), 1,
            "aggr dynamic link: bridge cert role binding mismatch");
          assert_eq!(aggr_opt_address_eq(axioms, Options::Option::None), 1,
            "aggr dynamic link: bridge cert must not depend on user axioms");
          assert_eq!(aggr_opt_address_eq(asm, Options::Option::None), 1,
            "aggr dynamic link: bridge cert must be unconditional");
          let eq_claim = Bytes::address_eq(cert_claim_addr, cert_const);
          let eq_const = Bytes::address_eq(checked_const, cert_const);
          assert_eq!(Fields::is_zero((1 - eq_claim) * (1 - eq_const)), 1,
            "aggr dynamic link: bridge cert does not match certConst");
          () } ,
        229 => {
          let (ctx, _root, asm) = aggr_parse_check_env(cert_bytes);
          let (spec, binding, axioms, validator) = ctx;
          assert_eq!(validator, 3,
            "aggr dynamic link: bridge cert checkEnv must validate its role binding");
          assert_eq!(Bytes::address_eq(spec, expected_spec), 1,
            "aggr dynamic link: bridge cert specification digest mismatch");
          assert_eq!(Bytes::address_eq(binding, expected_binding), 1,
            "aggr dynamic link: bridge cert role binding mismatch");
          assert_eq!(aggr_opt_address_eq(axioms, Options::Option::None), 1,
            "aggr dynamic link: bridge cert must not depend on user axioms");
          assert_eq!(aggr_opt_address_eq(asm, Options::Option::None), 1,
            "aggr dynamic link: bridge cert must be unconditional");
          assert_eq!(Bytes::address_eq(cert_claim_addr, cert_const), 1,
            "aggr dynamic link: bridge cert claim digest does not match certConst");
          () } ,
      }
    }

  fn aggr_dynamic_link(ixvm_vk_digest: [Field; 8], self_vk_digest: [Field; 8],
        verify_idx: Field, aggr_idx: Field, allowed_digest: [Field; 8],
        out_claim_digest: [Field; 8]) -> () {
      let (sidx, slen) = hint::<(Field, Field)>("stark.io.info", (1, 2));
      let sbytes = StarkIO::read_byte_stream(1, sidx, slen);
      let ext_vk_addr = Blake3::bytes_to_addr(sbytes);
      let (sys, srest) = SystemDeserialize::read_system(sbytes);
      let Lists::Node::Nil = (*(srest));
      aggr_assert_security_envelope(sys);

      let ext_claim = aggr_only_claim(aggr_verify_child(sys, 0));

      let (oidx, olen) = hint::<(Field, Field)>("stark.io.info", (2, 2));
      let output_bytes = StarkIO::read_byte_stream(2, oidx, olen);
      assert_eq!(Blake3::pack_digest(Blake3::hash(output_bytes)), out_claim_digest,
        "aggr dynamic link: output statement digest mismatch");
      let (vk_digest, entry_idx, pub_inputs, pub_outputs, bridge) =
        aggr_parse_dynamic_link(output_bytes);
      assert_eq!(Bytes::address_eq(vk_digest, ext_vk_addr), 1,
        "aggr dynamic link: statement vkDigest does not match external VK");
      let expected_claim = (&(Lists::Node::Cons(UInt64::ONE,
        (&(Lists::Node::Cons(entry_idx, Lists::concat(pub_inputs, pub_outputs)))))));
      assert_eq!(StarkVerifier::assert_same_limbs(ext_claim, expected_claim), 1,
        "aggr dynamic link: external claim words mismatch");

      match bridge {
        AggrOptBridge::NoBridge => { () } ,
        AggrOptBridge::SomeBridge(b_spec, b_binding, _target_const, codec, cert_const) => {
          aggr_assert_codec_arity(codec, pub_inputs, pub_outputs);
          aggr_verify_bridge_cert(b_spec, b_binding, cert_const, ixvm_vk_digest, self_vk_digest,
            verify_idx, aggr_idx, allowed_digest) } ,
      }
    }

  -- ── Shape 18: Tier 2 Eval-Assumption Discharge (`aggr_discharge_eval`) ──

  fn aggr_parse_eval_assumption(bytes: Bytes::Stream)
        -> (Bytes::AddressRef, Bytes::AddressRef, Bytes::AddressRef, AggrOptCircuitRef) {
      let (tag0, s) = aggr_read_byte(bytes);
      assert_eq!(UInt8::to_field(tag0), 232, "aggr discharge eval: leaf wrong tag byte 0");
      let (tag1, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(tag1), 14, "aggr discharge eval: leaf wrong tag byte 1");
      let (lhs, s) = aggr_read_address(s);
      let (rhs, s) = aggr_read_address(s);
      let (typ, s) = aggr_read_address(s);
      let (ctag, s) = aggr_read_byte(s);
      match UInt8::to_field(ctag) {
        0 => {
          let Lists::Node::Nil = (*(s));
          (lhs, rhs, typ, AggrOptCircuitRef::NoCircuitRef) } ,
        1 => {
          let (vk, s1) = aggr_read_address(s);
          let (entry, stop) = aggr_read_u64(s1);
          let Lists::Node::Nil = (*(stop));
          (lhs, rhs, typ, AggrOptCircuitRef::SomeCircuitRef(vk, entry)) } ,
      }
    }

  fn aggr_put_u64(u: UInt64::U64, rest: Bytes::Stream) -> Bytes::Stream {
      let s7 = (&(Lists::Node::Cons(u[7], rest)));
      let s6 = (&(Lists::Node::Cons(u[6], s7)));
      let s5 = (&(Lists::Node::Cons(u[5], s6)));
      let s4 = (&(Lists::Node::Cons(u[4], s5)));
      let s3 = (&(Lists::Node::Cons(u[3], s4)));
      let s2 = (&(Lists::Node::Cons(u[2], s3)));
      let s1 = (&(Lists::Node::Cons(u[1], s2)));
      (&(Lists::Node::Cons(u[0], s1)))
    }

  -- Content address of a canonical `LinkedCircuitEntry` (`0xE8 0x0F`, variant 23 under `0xE`):
  -- `0xE8 || 0x0F || vkDigest || entryIdx || codec || targetConst || certConst || evalType || spec || binding`.
  fn aggr_linked_entry_addr(vk_digest: Bytes::AddressRef, entry_idx: UInt64::U64,
        codec: UInt64::U64, target_const: Bytes::AddressRef, cert_const: Bytes::AddressRef,
        eval_type: Bytes::AddressRef,
        spec: Bytes::AddressRef, binding: Bytes::AddressRef) -> Bytes::AddressRef {
      let s7 = aggr_put_address(binding, (&(Lists::Node::Nil)));
      let s6 = aggr_put_address(spec, s7);
      let s5 = aggr_put_address(eval_type, s6);
      let s4 = aggr_put_address(cert_const, s5);
      let s3 = aggr_put_address(target_const, s4);
      let s2 = aggr_put_u64(codec, s3);
      let s1 = aggr_put_u64(entry_idx, s2);
      let s0 = aggr_put_address(vk_digest, s1);
      Blake3::bytes_to_addr((&(Lists::Node::Cons(UInt8::BYTE_232,
        (&(Lists::Node::Cons(UInt8::BYTE_15, s0)))))))
    }

  -- Merge an optional prior sorted Merkle tree of `LinkedCircuitEntry` leaves (`prev_linked`)
  -- with an optional newly recorded entry address (`added_entry`), asserting `out_linked`
  -- commits to their exact sorted canonical union (mirroring `aggr_assert_axioms_merge`).
  fn aggr_assert_linked_merge(prev_linked: Options::Option<Bytes::AddressRef>,
        added_entry: Options::Option<Bytes::AddressRef>,
        out_linked: Options::Option<Bytes::AddressRef>) -> () {
      match added_entry {
        Options::Option::None => {
          assert_eq!(aggr_opt_address_eq(prev_linked, out_linked), 1,
            "aggr discharge eval: linked circuits mismatch");
          () } ,
        Options::Option::Some(entry_addr) => {
          let Options::Option::Some(out_root) = out_linked;
          let single_root = aggr_leaf_hash(entry_addr);
          match prev_linked {
            Options::Option::None => {
              assert_eq!(Bytes::address_eq(single_root, out_root), 1,
                "aggr discharge eval: singleton linked circuits root mismatch");
              () } ,
            Options::Option::Some(prev_root) => {
              match Bytes::address_eq(prev_root, single_root) {
                1 => {
                  assert_eq!(Bytes::address_eq(prev_root, out_root), 1,
                    "aggr discharge eval: linked circuits root mismatch");
                  () } ,
                _ => {
                  let prev_leaves = aggr_load_canonical_tree(prev_root);
                  let added_leaves = (&(Lists::Node::Cons(entry_addr, (&(Lists::Node::Nil)))));
                  let out_leaves = aggr_load_canonical_tree(out_root);
                  aggr_assert_union(prev_leaves, added_leaves, out_leaves) } ,
              } } ,
          } } ,
      }
    }

  fn aggr_parse_eval_assumed(bytes: Bytes::Stream)
        -> (Field, (Bytes::AddressRef, Bytes::AddressRef, Options::Option<Bytes::AddressRef>, Field),
            Bytes::AddressRef, Options::Option<Bytes::AddressRef>,
            Bytes::AddressRef, Options::Option<Bytes::AddressRef>) {
      let (tag_byte, s) = aggr_read_byte(bytes);
      let tag = UInt8::to_field(tag_byte);
      assert_eq!((tag - 228) * (tag - 229), 0,
        "aggr discharge eval: child 0 is not Check or CheckEnv");
      let (format, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(format), 4, "aggr discharge eval: unsupported object format");
      let (val_byte, s) = aggr_read_byte(s);
      let validator = UInt8::to_field(val_byte);
      let (spec, s) = aggr_read_address(s);
      let (binding, s) = aggr_read_address(s);
      let (axioms, s) = aggr_get_opt_address(s);
      let (target, s) = aggr_read_address(s);
      let (assumptions, s) = aggr_get_opt_address(s);
      match validator {
        10 => {
          let (eval_asm, stop) = aggr_read_address(s);
          let Lists::Node::Nil = (*(stop));
          (tag, (spec, binding, axioms, validator), target, assumptions,
            eval_asm, Options::Option::None) } ,
        11 => {
          let (eval_asm, stop) = aggr_read_address(s);
          let Lists::Node::Nil = (*(stop));
          (tag, (spec, binding, axioms, validator), target, assumptions,
            eval_asm, Options::Option::None) } ,
        12 => {
          let (eval_opt, s1) = aggr_get_opt_address(s);
          let Options::Option::Some(eval_asm) = eval_opt;
          let (linked_root, stop) = aggr_read_address(s1);
          let Lists::Node::Nil = (*(stop));
          (tag, (spec, binding, axioms, validator), target, assumptions,
            eval_asm, Options::Option::Some(linked_root)) } ,
        13 => {
          let (eval_opt, s1) = aggr_get_opt_address(s);
          let Options::Option::Some(eval_asm) = eval_opt;
          let (linked_root, stop) = aggr_read_address(s1);
          let Lists::Node::Nil = (*(stop));
          (tag, (spec, binding, axioms, validator), target, assumptions,
            eval_asm, Options::Option::Some(linked_root)) } ,
      }
    }

  fn aggr_parse_eval_discharge_out(bytes: Bytes::Stream, expected_tag: Field, c0_validator: Field)
        -> ((Bytes::AddressRef, Bytes::AddressRef, Options::Option<Bytes::AddressRef>, Field),
            Bytes::AddressRef, Options::Option<Bytes::AddressRef>,
            Options::Option<Bytes::AddressRef>, Options::Option<Bytes::AddressRef>) {
      let (tag_byte, s) = aggr_read_byte(bytes);
      assert_eq!(UInt8::to_field(tag_byte), expected_tag,
        "aggr discharge eval: output claim tag differs from child 0");
      let (format, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(format), 4, "aggr discharge eval: unsupported object format");
      let (val_byte, s) = aggr_read_byte(s);
      let out_validator = UInt8::to_field(val_byte);
      let (spec, s) = aggr_read_address(s);
      let (binding, s) = aggr_read_address(s);
      let (axioms, s) = aggr_get_opt_address(s);
      let (target, s) = aggr_read_address(s);
      let (assumptions, s) = aggr_get_opt_address(s);
      let linked_val = match c0_validator {
        10 => {  12 } ,
        11 => {  13 } ,
        12 => {  12 } ,
        13 => {  13 } ,
      };
      match Fields::is_zero(out_validator - linked_val) {
        1 => {
          let (eval_opt, s1) = aggr_get_opt_address(s);
          let (linked_root, stop) = aggr_read_address(s1);
          let Lists::Node::Nil = (*(stop));
          ((spec, binding, axioms, out_validator), target, assumptions,
            eval_opt, Options::Option::Some(linked_root)) } ,
        _ => {
          assert_eq!((c0_validator - 10) * (c0_validator - 11), 0,
            "aggr discharge eval: linked claim (validator 12/13) cannot transition to unlinked validator");
          match Fields::is_zero(out_validator - c0_validator) {
            1 => {
              let (eval_asm, stop) = aggr_read_address(s);
              let Lists::Node::Nil = (*(stop));
              ((spec, binding, axioms, out_validator), target, assumptions,
                Options::Option::Some(eval_asm), Options::Option::None) } ,
            _ => {
              assert_eq!(out_validator, c0_validator - 7,
                "aggr discharge eval: full unlinked discharge must transition validator 10->3 or 11->4");
              let Lists::Node::Nil = (*(s));
              ((spec, binding, axioms, out_validator), target, assumptions,
                Options::Option::None, Options::Option::None) } ,
          } } ,
      }
    }

  -- Extract the unique removed leaf `a` such that strictly sorted `before = after ∪ {a}` (`a ∉ after`).
  fn aggr_extract_removed_leaf(before: Lists::List<Bytes::AddressRef>,
        after: Lists::List<Bytes::AddressRef>) -> Bytes::AddressRef {
      let Lists::Node::Cons(a, ar) = (*(before));
      match (*(after)) {
        Lists::Node::Nil => {
          let Lists::Node::Nil = (*(ar));
          a } ,
        Lists::Node::Cons(b, br) => {
          match Bytes::address_eq(a, b) {
            1 => { aggr_extract_removed_leaf(ar, br) } ,
            _ => {
              aggr_assert_same_list(ar, after);
              a } ,
          } } ,
      }
    }

  fn aggr_assert_packed_addr_u64s(words: Lists::List<UInt64::U64>, addr: Bytes::AddressRef) -> () {
      let a = (*(addr));
      let Lists::Node::Cons(w0, r1) = (*(words));
      let Lists::Node::Cons(w1, r2) = (*(r1));
      let Lists::Node::Cons(w2, r3) = (*(r2));
      let Lists::Node::Cons(w3, r4) = (*(r3));
      let Lists::Node::Cons(w4, r5) = (*(r4));
      let Lists::Node::Cons(w5, r6) = (*(r5));
      let Lists::Node::Cons(w6, r7) = (*(r6));
      let Lists::Node::Cons(w7, r8) = (*(r7));
      let Lists::Node::Nil = (*(r8));
      assert_eq!(UInt64::eq(w0, [a[0], a[1], a[2], a[3], UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]), 1,
        "aggr discharge eval: packed address word 0 mismatch");
      assert_eq!(UInt64::eq(w1, [a[4], a[5], a[6], a[7], UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]), 1,
        "aggr discharge eval: packed address word 1 mismatch");
      assert_eq!(UInt64::eq(w2, [a[8], a[9], a[10], a[11], UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]), 1,
        "aggr discharge eval: packed address word 2 mismatch");
      assert_eq!(UInt64::eq(w3, [a[12], a[13], a[14], a[15], UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]), 1,
        "aggr discharge eval: packed address word 3 mismatch");
      assert_eq!(UInt64::eq(w4, [a[16], a[17], a[18], a[19], UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]), 1,
        "aggr discharge eval: packed address word 4 mismatch");
      assert_eq!(UInt64::eq(w5, [a[20], a[21], a[22], a[23], UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]), 1,
        "aggr discharge eval: packed address word 5 mismatch");
      assert_eq!(UInt64::eq(w6, [a[24], a[25], a[26], a[27], UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]), 1,
        "aggr discharge eval: packed address word 6 mismatch");
      assert_eq!(UInt64::eq(w7, [a[28], a[29], a[30], a[31], UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]), 1,
        "aggr discharge eval: packed address word 7 mismatch");
      ()
    }

  fn aggr_read_u16_le(stream: Bytes::Stream) -> (Field, Bytes::Stream) {
      let (b0, s1) = aggr_read_byte(stream);
      let (b1, s2) = aggr_read_byte(s1);
      (UInt8::to_field(b0) + 256 * UInt8::to_field(b1), s2)
    }

  fn aggr_read_u24_le(stream: Bytes::Stream) -> (Field, Bytes::Stream) {
      let (b0, s1) = aggr_read_byte(stream);
      let (b1, s2) = aggr_read_byte(s1);
      let (b2, s3) = aggr_read_byte(s2);
      (UInt8::to_field(b0) + 256 * UInt8::to_field(b1) + 65536 * UInt8::to_field(b2), s3)
    }

  fn aggr_read_tagn0(stream: Bytes::Stream) -> (Field, Bytes::Stream) {
      let (b, s1) = aggr_read_byte(stream);
      let bits = UInt8::bit_decomposition(b);
      let bv = UInt8::to_field(b);
      match bits[7] {
        0 => { (bv, s1) } ,
        _ => {
          match bits[6] {
            0 => {
              let (b1, s2) = aggr_read_byte(s1);
              (128 + (bv - 128) * 256 + UInt8::to_field(b1), s2) } ,
            _ => {
              match bv - 192 {
                0 => {
                  let (v, s2) = aggr_read_u16_le(s1);
                  (16512 + v, s2) } ,
                1 => {
                  let (v, s2) = aggr_read_u24_le(s1);
                  (82048 + v, s2) } ,
                2 => {
                  let (v, s2) = aggr_read_u32_le(s1);
                  (16859264 + v, s2) } ,
                3 => {
                  let (u, s2) = aggr_read_u64(s1);
                  (4311826560 + UInt64::to_field(u), s2) } ,
              } } ,
          } } ,
      }
    }

  fn aggr_skip_tagn0_n(stream: Bytes::Stream, n: Field) -> Bytes::Stream {
      match n {
        0 => { stream } ,
        _ => {
          let (_v, s1) = aggr_read_tagn0(stream);
          aggr_skip_tagn0_n(s1, n - 1) } ,
      }
    }

  fn aggr_read_tagn4(stream: Bytes::Stream) -> (Field, Field, Bytes::Stream) {
      let (b, s1) = aggr_read_byte(stream);
      let bits = UInt8::bit_decomposition(b);
      let flag = bits[4] + 2 * bits[5] + 4 * bits[6] + 8 * bits[7];
      let payload = bits[0] + 2 * bits[1] + 4 * bits[2] + 8 * bits[3];
      match bits[3] {
        0 => { (flag, payload, s1) } ,
        _ => {
          match bits[2] {
            0 => {
              let (b1, s2) = aggr_read_byte(s1);
              (flag, 8 + (payload - 8) * 256 + UInt8::to_field(b1), s2) } ,
            _ => {
              match payload - 12 {
                0 => {
                  let (v, s2) = aggr_read_u16_le(s1);
                  (flag, 1032 + v, s2) } ,
                1 => {
                  let (v, s2) = aggr_read_u24_le(s1);
                  (flag, 66568 + v, s2) } ,
                2 => {
                  let (v, s2) = aggr_read_u32_le(s1);
                  (flag, 16843784 + v, s2) } ,
                3 => {
                  let (u, s2) = aggr_read_u64(s1);
                  (flag, 4311811080 + UInt64::to_field(u), s2) } ,
              } } ,
          } } ,
      }
    }

  fn aggr_skip_expr(stream: Bytes::Stream) -> Bytes::Stream {
      let (flag, val, s1) = aggr_read_tagn4(stream);
      match flag {
        0 => { s1 } ,
        1 => { s1 } ,
        2 => { aggr_skip_tagn0_n(s1, 1 + val) } ,
        3 => { aggr_skip_tagn0_n(s1, 1 + val) } ,
        4 => {
          let (_tref, s2) = aggr_read_tagn0(s1);
          aggr_skip_expr(s2) } ,
        5 => { s1 } ,
        6 => { s1 } ,
        7 => {
          assert_eq!(Fields::is_zero(val), 0, "aggr discharge eval: empty app spine");
          aggr_skip_exprs_n(s1, 1 + val) } ,
        8 => {
          assert_eq!(Fields::is_zero(val), 0, "aggr discharge eval: empty lam telescope");
          aggr_skip_exprs_n(s1, 1 + val) } ,
        9 => {
          assert_eq!(Fields::is_zero(val), 0, "aggr discharge eval: empty all telescope");
          aggr_skip_exprs_n(s1, 1 + val) } ,
        10 => { aggr_skip_exprs_n(s1, 3) } ,
        11 => { s1 } ,
      }
    }

  fn aggr_skip_exprs_n(stream: Bytes::Stream, n: Field) -> Bytes::Stream {
      match n {
        0 => { stream } ,
        _ => {
          let s1 = aggr_skip_expr(stream);
          aggr_skip_exprs_n(s1, n - 1) } ,
      }
    }

  fn aggr_find_role_addr(stream: Bytes::Stream, remaining: Field, target_role: Field) -> Bytes::AddressRef {
      assert_eq!(Fields::is_zero(remaining), 0,
        "aggr discharge eval: role not found in binding section");
      let (role, s1) = aggr_read_byte(stream);
      let (addr, s2) = aggr_read_address(s1);
      match Fields::is_zero(UInt8::to_field(role) - target_role) {
        1 => { addr } ,
        _ => { aggr_find_role_addr(s2, remaining - 1, target_role) } ,
      }
    }

  fn aggr_binding_eq_addr(binding: Bytes::AddressRef) -> Bytes::AddressRef {
      let bytes = aggr_load_preimage(aggr_pack_address(binding));
      let (tag0, s) = aggr_read_byte(bytes);
      assert_eq!(UInt8::to_field(tag0), 232, "aggr discharge eval: not a role binding section");
      let (tag1, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(tag1), 3, "aggr discharge eval: not a role binding section");
      let (_version, s) = aggr_read_byte(s);
      let (count, s) = aggr_read_byte(s);
      aggr_find_role_addr(s, UInt8::to_field(count), 8)
    }

  -- Verify a `Claim.check` constant record is a safe, closed `defn`/`thm` whose type
  -- is `@Eq.{u} leaf.typ leaf.lhs leaf.rhs` with `refs[0..3] = [binding[Role.eq], typ, lhs, rhs]`.
  fn aggr_verify_eq_check_record(const_addr: Bytes::AddressRef, binding: Bytes::AddressRef,
        leaf_lhs: Bytes::AddressRef, leaf_rhs: Bytes::AddressRef, leaf_typ: Bytes::AddressRef) -> () {
      let eq_addr = aggr_binding_eq_addr(binding);
      let rec_bytes = aggr_load_preimage(aggr_pack_address(const_addr));
      let (ctag, s) = aggr_read_byte(rec_bytes);
      assert_eq!(UInt8::to_field(ctag), 208,
        "aggr discharge eval: check witness must be a Definition/Theorem constant");
      let (flags, s) = aggr_read_byte(s);
      let fbits = UInt8::bit_decomposition(flags);
      let safety = fbits[0] + 2 * fbits[1];
      let kind = fbits[2] + 2 * fbits[3];
      assert_eq!(safety, 1, "aggr discharge eval: check witness must be safe");
      assert_eq!(kind * (kind - 2), 0, "aggr discharge eval: check witness must be defn or thm");
      let (lvls, s) = aggr_read_tagn0(s);
      assert_eq!(lvls, 0, "aggr discharge eval: check witness must be closed (0 level params)");
      -- Type must be `App(3, Ref(0, [u]), Ref(1, []), Ref(2, []), Ref(3, []))`
      let (t0, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(t0), 115, "aggr discharge eval: type must be 3-arg App");
      let (t1, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(t1), 33, "aggr discharge eval: head must be Ref(_, [u])");
      let (t2, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(t2), 0, "aggr discharge eval: Eq ref index must be 0");
      let (_u_idx, s) = aggr_read_tagn0(s);
      let (t3, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(t3), 32, "aggr discharge eval: typ arg must be Ref(_, [])");
      let (t4, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(t4), 1, "aggr discharge eval: typ ref index must be 1");
      let (t5, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(t5), 32, "aggr discharge eval: lhs arg must be Ref(_, [])");
      let (t6, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(t6), 2, "aggr discharge eval: lhs ref index must be 2");
      let (t7, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(t7), 32, "aggr discharge eval: rhs arg must be Ref(_, [])");
      let (t8, s) = aggr_read_byte(s);
      assert_eq!(UInt8::to_field(t8), 3, "aggr discharge eval: rhs ref index must be 3");
      let s = aggr_skip_expr(s);
      let (nshare, s) = aggr_read_tagn0(s);
      let s = aggr_skip_exprs_n(s, nshare);
      let (nrefs, s) = aggr_read_tagn0(s);
      assert_eq!(UInt32::less_than_fields(3, nrefs), 1,
        "aggr discharge eval: check witness refs table too short");
      let (r0, s) = aggr_read_address(s);
      let (r1, s) = aggr_read_address(s);
      let (r2, s) = aggr_read_address(s);
      let (r3, _s) = aggr_read_address(s);
      assert_eq!(Bytes::address_eq(r0, eq_addr), 1,
        "aggr discharge eval: check witness ref[0] is not Eq");
      assert_eq!(Bytes::address_eq(r1, leaf_typ), 1,
        "aggr discharge eval: check witness ref[1] differs from leaf typ");
      assert_eq!(Bytes::address_eq(r2, leaf_lhs), 1,
        "aggr discharge eval: check witness ref[2] differs from leaf lhs");
      assert_eq!(Bytes::address_eq(r3, leaf_rhs), 1,
        "aggr discharge eval: check witness ref[3] differs from leaf rhs");
      ()
    }

  fn aggr_discharge_eval(ixvm_vk_digest: [Field; 8], self_vk_digest: [Field; 8],
        verify_idx: Field, aggr_idx: Field, allowed_digest: [Field; 8],
        out_claim_digest: [Field; 8]) -> () {
      let (kidx, klen) = hint::<(Field, Field)>("stark.io.info", (6, 1));
      assert_eq!(klen, 2, "aggr discharge eval: child-kind hint must be 2 bytes");
      let kstream = StarkIO::read_byte_stream(6, kidx, klen);
      let (k0b, ks1) = aggr_read_byte(kstream);
      let (k1b, kstop) = aggr_read_byte(ks1);
      let Lists::Node::Nil = (*(kstop));
      let kind0 = UInt8::to_field(k0b);
      let kind1 = UInt8::to_field(k1b);
      assert_eq!(kind0 * (kind0 - 1), 0, "aggr discharge eval: child 0 kind must be 0 or 1");
      assert_eq!(kind1 * (kind1 - 1), 0, "aggr discharge eval: child 1 kind must be 0 or 1");

      let c0_digest = aggr_child_check_env_digest(kind0, 0,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      let c1_digest = aggr_child_check_env_digest(kind1, 1,
        ixvm_vk_digest, self_vk_digest, verify_idx, aggr_idx, allowed_digest);
      let (c0_tag, c0_ctx, c0_target, c0_asm, c0_eval_root, c0_linked_opt) =
        aggr_parse_eval_assumed(aggr_load_preimage(c0_digest));
      let (c0_spec, c0_binding, c0_axioms, c0_validator) = c0_ctx;

      let (oidx, olen) = hint::<(Field, Field)>("stark.io.info", (2, 2));
      let output_bytes = StarkIO::read_byte_stream(2, oidx, olen);
      assert_eq!(Blake3::pack_digest(Blake3::hash(output_bytes)), out_claim_digest,
        "aggr discharge eval: output claim digest mismatch");
      let (out_ctx, out_target, out_asm, out_eval_opt, out_linked_opt) =
        aggr_parse_eval_discharge_out(output_bytes, c0_tag, c0_validator);
      let (out_spec, out_binding, out_axioms, _out_validator) = out_ctx;
      assert_eq!(Bytes::address_eq(c0_spec, out_spec), 1,
        "aggr discharge eval: output specification digest differs from child 0");
      assert_eq!(Bytes::address_eq(c0_binding, out_binding), 1,
        "aggr discharge eval: output binding differs from child 0");
      assert_eq!(Bytes::address_eq(c0_target, out_target), 1,
        "aggr discharge eval: output subject differs from child 0");
      assert_eq!(aggr_opt_address_eq(c0_asm, out_asm), 1,
        "aggr discharge eval: output typing assumptions differ from child 0");

      let c0_eval_leaves = aggr_load_canonical_tree(c0_eval_root);
      let out_eval_leaves = aggr_load_optional_tree(out_eval_opt);
      let removed_leaf_addr = aggr_extract_removed_leaf(c0_eval_leaves, out_eval_leaves);
      let leaf_bytes = aggr_load_preimage(aggr_pack_address(removed_leaf_addr));
      let (leaf_lhs, leaf_rhs, leaf_typ, leaf_circuit) = aggr_parse_eval_assumption(leaf_bytes);

      let c1_bytes = aggr_load_preimage(c1_digest);
      let (c1_tag, _c1_rest) = aggr_read_byte(c1_bytes);
      -- Mode 1 (`tag == 227`, `Claim.eval`) is disabled in 0.4 until `VerifyClaimCircuitSoundIn`
      -- is proved for `KernelEval::run_eval`.
      -- Mode 2 (`tag == 228`, `@Eq` `Claim.check`): sound unconditional discharge; transitions
      -- `10->3` / `11->4` ONLY when `eval_leaves` becomes empty AND `linkedCircuits == None`.
      -- Mode 3a (`tag == 232`, `DynamicLinkStatement`): ALWAYS commits `LinkedCircuitEntry`
      -- (`0xE8 0x0F`) into `out_linked_opt` under validators `12`/`13` (NEVER `3`/`4`).
      match UInt8::to_field(c1_tag) {
        228 => {
          let (c1_ctx, const_addr, c1_asm) = aggr_parse_check(c1_bytes);
          let (c1_spec, c1_binding, c1_axioms, c1_val) = c1_ctx;
          assert_eq!(c1_val, 3,
            "aggr discharge eval: check child must validate its binding");
          assert_eq!(Bytes::address_eq(c0_spec, c1_spec), 1,
            "aggr discharge eval: check child has different specification digest");
          assert_eq!(Bytes::address_eq(c0_binding, c1_binding), 1,
            "aggr discharge eval: check child has different binding");
          assert_eq!(aggr_opt_address_eq(c1_asm, Options::Option::None), 1,
            "aggr discharge eval: check child must be unconditional");
          aggr_verify_eq_check_record(const_addr, c0_binding, leaf_lhs, leaf_rhs, leaf_typ);
          aggr_assert_linked_merge(c0_linked_opt, Options::Option::None, out_linked_opt);
          aggr_assert_axioms_merge(c0_axioms, c1_axioms, out_axioms) } ,
        232 => {
          assert_eq!(kind1, 1,
            "aggr discharge eval: DynamicLink child must be an ix_aggr proof");
          let (dl_vk, dl_entry, dl_inputs, dl_outputs, dl_bridge) =
            aggr_parse_dynamic_link(c1_bytes);
          let AggrOptCircuitRef::SomeCircuitRef(leaf_vk, leaf_entry) = leaf_circuit;
          assert_eq!(Bytes::address_eq(dl_vk, leaf_vk), 1,
            "aggr discharge eval: DynamicLink vkDigest differs from leaf circuit");
          assert_eq!(UInt64::eq(dl_entry, leaf_entry), 1,
            "aggr discharge eval: DynamicLink entryIdx differs from leaf circuit");
          let AggrOptBridge::SomeBridge(dl_spec, dl_binding, target_const, codec, cert_const) = dl_bridge;
          assert_eq!(Bytes::address_eq(dl_spec, c0_spec), 1,
            "aggr discharge eval: DynamicLink bridge spec differs from child 0");
          assert_eq!(Bytes::address_eq(dl_binding, c0_binding), 1,
            "aggr discharge eval: DynamicLink bridge binding differs from child 0");
          assert_eq!(UInt64::eq(codec, UInt64::ONE), 1,
            "aggr discharge eval: DynamicLink codec must be ixonAddrPair (1)");
          aggr_assert_packed_addr_u64s(dl_inputs, leaf_lhs);
          aggr_assert_packed_addr_u64s(dl_outputs, leaf_rhs);
          let linked_entry_addr = aggr_linked_entry_addr(
            dl_vk, dl_entry, codec, target_const, cert_const, leaf_typ, dl_spec, dl_binding);
          aggr_assert_linked_merge(c0_linked_opt, Options::Option::Some(linked_entry_addr), out_linked_opt);
          aggr_assert_axioms_merge(c0_axioms, Options::Option::None, out_axioms) } ,
      }
    }
}
⟧

end MultiStark.Source
