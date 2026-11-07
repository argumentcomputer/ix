import Aiur.Modules.Frontend

/-! # IxVM module `RBTreeMap`

Red-black maps keyed by addresses, ordered by all 32 address bytes (`canon_addr_cmp`).

Formal Aiur source, written as Lean syntax (`aiur⟦ … ⟧`). `IxVM.source`
(`IxVM/IxVM/Program.lean`) composes the modules. -/

namespace IxVM.Source

def rbTreeMap : Aiur.Modules.Program Nat := aiur⟦
module RBTreeMap {
  enum RBTreeMap<V> {

      Node(Field, Bytes::AddressRef, V, &RBTreeMap::RBTreeMap<V>, &RBTreeMap::RBTreeMap<V>),
      Nil
    }

  fn rbtree_map_balance<V>(color: Field, key: Bytes::AddressRef, value: V, left: RBTreeMap::RBTreeMap<V>, right: RBTreeMap::RBTreeMap<V>) -> RBTreeMap::RBTreeMap<V> {
      match color {
        1 => {  rbtree_map_balance_fix(key, value, left, right) } ,
        _ => {  RBTreeMap::RBTreeMap::Node(color, key, value, (&(left)), (&(right))) } ,
      }
    }

  fn rbtree_map_balance_fix<V>(key: Bytes::AddressRef, value: V, left: RBTreeMap::RBTreeMap<V>, right: RBTreeMap::RBTreeMap<V>) -> RBTreeMap::RBTreeMap<V> {
      match (left, right) {

        (RBTreeMap::RBTreeMap::Node(0, yk, yv, &RBTreeMap::RBTreeMap::Node(0, xk, xv, a, b), c), d) => {
          RBTreeMap::RBTreeMap::Node(0, yk, yv,
            (&(RBTreeMap::RBTreeMap::Node(1, xk, xv, a, b))),
            (&(RBTreeMap::RBTreeMap::Node(1, key, value, c, (&(d)))))) } ,

        (RBTreeMap::RBTreeMap::Node(0, xk, xv, a, &RBTreeMap::RBTreeMap::Node(0, yk, yv, b, c)), d) => {
          RBTreeMap::RBTreeMap::Node(0, yk, yv,
            (&(RBTreeMap::RBTreeMap::Node(1, xk, xv, a, b))),
            (&(RBTreeMap::RBTreeMap::Node(1, key, value, c, (&(d)))))) } ,

        (a, RBTreeMap::RBTreeMap::Node(0, zk, zv, &RBTreeMap::RBTreeMap::Node(0, yk, yv, b, c), d)) => {
          RBTreeMap::RBTreeMap::Node(0, yk, yv,
            (&(RBTreeMap::RBTreeMap::Node(1, key, value, (&(a)), b))),
            (&(RBTreeMap::RBTreeMap::Node(1, zk, zv, c, d)))) } ,

        (a, RBTreeMap::RBTreeMap::Node(0, yk, yv, b, &RBTreeMap::RBTreeMap::Node(0, zk, zv, c, d))) => {
          RBTreeMap::RBTreeMap::Node(0, yk, yv,
            (&(RBTreeMap::RBTreeMap::Node(1, key, value, (&(a)), b))),
            (&(RBTreeMap::RBTreeMap::Node(1, zk, zv, c, d)))) } ,

        _ => {  RBTreeMap::RBTreeMap::Node(1, key, value, (&(left)), (&(right))) } ,
      }
    }

  fn rbtree_map_ins<V>(key: Bytes::AddressRef, value: V, tree: RBTreeMap::RBTreeMap<V>) -> RBTreeMap::RBTreeMap<V> {
      match tree {
        RBTreeMap::RBTreeMap::Nil => {
          RBTreeMap::RBTreeMap::Node(0, key, value, (&(RBTreeMap::RBTreeMap::Nil)), (&(RBTreeMap::RBTreeMap::Nil))) } ,
        RBTreeMap::RBTreeMap::Node(color, k, v, &left, &right) => {
          let lt = Fields::is_zero(canon_addr_cmp(key, k));
          match lt {
            1 => {  rbtree_map_balance(color, k, v, rbtree_map_ins(key, value, left), right) } ,
            _ => {

              let eq = canon_addr_cmp(key, k) - 1;
              match eq {
                0 => {  RBTreeMap::RBTreeMap::Node(color, key, value, (&(left)), (&(right))) } ,
                _ => {  rbtree_map_balance(color, k, v, left, rbtree_map_ins(key, value, right)) } ,
              } } ,
          } } ,
      }
    }

  fn rbtree_map_insert<V>(key: Bytes::AddressRef, value: V, tree: RBTreeMap::RBTreeMap<V>) -> RBTreeMap::RBTreeMap<V> {
      let result = rbtree_map_ins(key, value, tree);
      match result {
        RBTreeMap::RBTreeMap::Node(_, k, v, left, right) => {  RBTreeMap::RBTreeMap::Node(1, k, v, left, right) } ,
      }
    }

  fn rbtree_map_lookup_or_default<V>(key: Bytes::AddressRef, tree: RBTreeMap::RBTreeMap<V>, default: V) -> V {
      match tree {
        RBTreeMap::RBTreeMap::Nil => {  default } ,
        RBTreeMap::RBTreeMap::Node(_, k, v, &left, &right) => {
          let lt = Fields::is_zero(canon_addr_cmp(key, k));
          match lt {
            1 => {  rbtree_map_lookup_or_default(key, left, default) } ,
            _ => {
              let eq = canon_addr_cmp(key, k) - 1;
              match eq {
                0 => {  v } ,
                _ => {  rbtree_map_lookup_or_default(key, right, default) } ,
              } } ,
          } } ,
      }
    }

  -- Port divergence: address keys are values, never prover-chosen ROM addresses.
  -- The tree keeps main's balancing and compares all 32 address bytes.
  fn canon_ord_cmp_g(a: Field, b: Field) -> Field {
      match a - b {
        0 => {  1 } ,
        _ => {
          match UInt32::less_than_fields(a, b) {
            1 => {  0 } ,
            0 => {  2 } ,
          } } ,
      }
    }

  fn canon_ord_then(a: Field, b: Field) -> Field {
      match a {
        1 => {  b } ,
        _ => {  a } ,
      }
    }

  fn canon_addr_cmp(x: Bytes::AddressRef, y: Bytes::AddressRef) -> Field {
      let xa = (*(x));
      let ya = (*(y));
      canon_ord_then(canon_addr_chunk(UInt8::to_field(xa[0]), UInt8::to_field(xa[1]), UInt8::to_field(xa[2]), UInt8::to_field(xa[3]),
                                      UInt8::to_field(ya[0]), UInt8::to_field(ya[1]), UInt8::to_field(ya[2]), UInt8::to_field(ya[3])),
        canon_ord_then(canon_addr_chunk(UInt8::to_field(xa[4]), UInt8::to_field(xa[5]), UInt8::to_field(xa[6]), UInt8::to_field(xa[7]),
                                        UInt8::to_field(ya[4]), UInt8::to_field(ya[5]), UInt8::to_field(ya[6]), UInt8::to_field(ya[7])),
          canon_ord_then(canon_addr_chunk(UInt8::to_field(xa[8]), UInt8::to_field(xa[9]), UInt8::to_field(xa[10]), UInt8::to_field(xa[11]),
                                          UInt8::to_field(ya[8]), UInt8::to_field(ya[9]), UInt8::to_field(ya[10]), UInt8::to_field(ya[11])),
            canon_ord_then(canon_addr_chunk(UInt8::to_field(xa[12]), UInt8::to_field(xa[13]), UInt8::to_field(xa[14]), UInt8::to_field(xa[15]),
                                            UInt8::to_field(ya[12]), UInt8::to_field(ya[13]), UInt8::to_field(ya[14]), UInt8::to_field(ya[15])),
              canon_ord_then(canon_addr_chunk(UInt8::to_field(xa[16]), UInt8::to_field(xa[17]), UInt8::to_field(xa[18]), UInt8::to_field(xa[19]),
                                              UInt8::to_field(ya[16]), UInt8::to_field(ya[17]), UInt8::to_field(ya[18]), UInt8::to_field(ya[19])),
                canon_ord_then(canon_addr_chunk(UInt8::to_field(xa[20]), UInt8::to_field(xa[21]), UInt8::to_field(xa[22]), UInt8::to_field(xa[23]),
                                                UInt8::to_field(ya[20]), UInt8::to_field(ya[21]), UInt8::to_field(ya[22]), UInt8::to_field(ya[23])),
                  canon_ord_then(canon_addr_chunk(UInt8::to_field(xa[24]), UInt8::to_field(xa[25]), UInt8::to_field(xa[26]), UInt8::to_field(xa[27]),
                                                  UInt8::to_field(ya[24]), UInt8::to_field(ya[25]), UInt8::to_field(ya[26]), UInt8::to_field(ya[27])),
                                 canon_addr_chunk(UInt8::to_field(xa[28]), UInt8::to_field(xa[29]), UInt8::to_field(xa[30]), UInt8::to_field(xa[31]),
                                                  UInt8::to_field(ya[28]), UInt8::to_field(ya[29]), UInt8::to_field(ya[30]), UInt8::to_field(ya[31])))))))))
    }

  fn canon_addr_chunk(x0: Field, x1: Field, x2: Field, x3: Field,
                        y0: Field, y1: Field, y2: Field, y3: Field) -> Field {
      let xv = x0 * 16777216 + x1 * 65536 + x2 * 256 + x3;
      let yv = y0 * 16777216 + y1 * 65536 + y2 * 256 + y3;
      canon_ord_cmp_g(xv, yv)
    }
}
⟧

end IxVM.Source
