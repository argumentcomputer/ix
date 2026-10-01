module
public import Ix.Aiur.Meta

public section

namespace IxVM

def ixonDeserialize := ⟦
  -- ============================================================================
  -- Byte reading primitives
  -- ============================================================================

  -- Every reader rejects truncation, including cold declaration fields.
  fn read_byte(stream: ByteStream) -> (U8, ByteStream) {
    let ListNode.Cons(byte, rest) = load(stream);
    (byte, rest)
  }

  -- Read num_bytes little-endian bytes into a u64
  fn get_u64_le(stream: ByteStream, num_bytes: G) -> (U64, ByteStream) {
    match num_bytes {
      0 => ([0u8; 8], stream),
      _ =>
        let ListNode.Cons(byte, s) = load(stream);
        let (rest_bytes, s2) = get_u64_le(s, num_bytes - 1);
        let [r0, r1, r2, r3, r4, r5, r6, _] = rest_bytes;
        ([byte, r0, r1, r2, r3, r4, r5, r6], s2),
    }
  }

  -- ============================================================================
  -- TagN integers (`Ixon.getTagN`)
  -- ============================================================================

  -- Every integer of the wire format is a TagN integer: one header byte
  -- `[flag : f bits][payload : r = 8 - f bits]` (f = 4 for expression,
  -- constant and claim headers, 2 for universes, 0 for counts and indices)
  -- followed by 0, 1, 2, 3, 4 or 8 little-endian bytes. With L the top
  -- payload bit, M the next one, c the low r - 2 bits and h = 2^(r - 2):
  --   L = 0         rung 1: the low r - 1 payload bits,   [0, R1),  R1 = 2h
  --   L = 1, M = 0  rung 2: R1 + 256 c + one byte,        [R1, R2), R2 = 258h
  --   L = 1, M = 1  code c = 0, 1, 2, 3 selects 2, 3, 4, 8 bytes x, and the
  --                 value is R(c + 2) + x, with R3 = R2 + 2^16,
  --                 R4 = R3 + 2^24, R5 = R4 + 2^32.
  -- Each rung starts where the previous one ends, so every value has exactly
  -- one encoding and there is no non-canonical form to reject. A reader
  -- rejects only invalid codes (c >= 4, possible for f = 0 and 2), values
  -- reaching 2^64 on the 8-byte rung, and truncation.
  --
  -- The three readers keep rung 1, the common case, on one narrow row; the
  -- other rungs share `get_tagn_tail`, parameterised by h. R2's bytes are
  -- [2h, h], so the readers need no other constant.

  -- TagN, f = 4: [flag:4][L][M][c:2].
  fn get_tagn4(stream: ByteStream) -> ((G, U64), ByteStream) {
    let ListNode.Cons(byte, s) = load(stream);
    let [b0, b1, b2, b3, b4, b5, b6, b7] = u8_bit_decomposition(byte);
    let flag = b4 + 2 * b5 + 4 * b6 + 8 * b7;
    let low = b0 + 2 * b1 + 4 * b2;
    match b3 {
      0 => ((flag, [u8_from_field_unsafe(low), 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), s),
      1 =>
        let (value, rest) = get_tagn_tail(low, 4, s);
        ((flag, value), rest),
    }
  }

  -- TagN, f = 2: [flag:2][L][M][c:4].
  fn get_tagn2(stream: ByteStream) -> ((G, U64), ByteStream) {
    let ListNode.Cons(byte, s) = load(stream);
    let [b0, b1, b2, b3, b4, b5, b6, b7] = u8_bit_decomposition(byte);
    let flag = b6 + 2 * b7;
    let low = b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4;
    match b5 {
      0 => ((flag, [u8_from_field_unsafe(low), 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), s),
      1 =>
        let (value, rest) = get_tagn_tail(low, 16, s);
        ((flag, value), rest),
    }
  }

  -- TagN, f = 0: [L][M][c:6]. No flag, so one comparison replaces the bit
  -- decomposition, and a rung-1 value is the header byte itself.
  fn get_tagn0(stream: ByteStream) -> (U64, ByteStream) {
    let ListNode.Cons(byte, s) = load(stream);
    match u8_less_than(byte, 128u8) {
      1 => ([byte, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], s),
      0 => get_tagn_tail(to_field(byte) - 128, 64, s),
    }
  }

  -- Rungs 2 to 6. `q` is the payload below L (M then c) and `h` the weight
  -- of M, so `q < h` is rung 2 and `q - h` is the code otherwise.
  fn get_tagn_tail(q: G, h: G, stream: ByteStream) -> (U64, ByteStream) {
    match u8_less_than(u8_from_field_unsafe(q), u8_from_field_unsafe(h)) {
      -- R1 + 256 q + lo, with q < h <= 64: the high byte absorbs the carry.
      1 =>
        let ListNode.Cons(lo, s) = load(stream);
        let (v0, carry) = u8_add(lo, u8_from_field_unsafe(2 * h));
        ([v0, u8_from_field_unsafe(q + to_field(carry)), 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], s),
      0 => get_tagn_wide(q - h, h, stream),
    }
  }

  -- Rungs 3 to 6: code c reads 2, 3, 4 or 8 bytes and adds R(c + 2). Codes
  -- 4 and up (f = 0 and 2) have no arm, so the match rejects them.
  fn get_tagn_wide(c: G, h: G, stream: ByteStream) -> (U64, ByteStream) {
    let r0 = u8_from_field_unsafe(2 * h);
    let r1 = u8_from_field_unsafe(h);
    match c {
      0 =>
        let (x, s) = get_u64_le(stream, 2);
        let (value, _) = u64_add(x, [r0, r1, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
        (value, s),
      1 =>
        let (x, s) = get_u64_le(stream, 3);
        let (value, _) = u64_add(x, [r0, r1, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
        (value, s),
      2 =>
        let (x, s) = get_u64_le(stream, 4);
        let (value, _) = u64_add(x, [r0, r1, 1u8, 1u8, 0u8, 0u8, 0u8, 0u8]);
        (value, s),
      3 =>
        let (x, s) = get_u64_le(stream, 8);
        let (value, carry) = u64_add(x, [r0, r1, 1u8, 1u8, 1u8, 0u8, 0u8, 0u8]);
        assert_eq!(to_field(carry), 0, "TagN value exceeds UInt64");
        (value, s),
    }
  }

  -- ============================================================================
  -- U64 list deserialization
  -- ============================================================================

  fn get_u64_list(stream: ByteStream, count: U64) -> (List‹U64›, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => (store(ListNode.Nil), stream),
      0 =>
        let (val, s) = get_tagn0(stream);
        let (rest, s2) = get_u64_list(s, relaxed_u64_pred(count));
        (store(ListNode.Cons(val, rest)), s2),
    }
  }

  -- ============================================================================
  -- Expression deserialization
  -- ============================================================================

  -- Counted parsers consume each element through strict readers before
  -- recurring. Truncation therefore rejects during parsing, without a
  -- preliminary traversal of the byte stream.

  -- App telescope: read count args, wrapping func in App nodes. `func` is passed
  -- by pointer (loaded only at the base case) so the recursion doesn't carry the
  -- wide `Expr` union by value on every row.
  fn get_app_telescope(func: &Expr, stream: ByteStream, count: U64) -> (&Expr, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => (func, stream),
      0 =>
        let (arg, s) = get_expr(stream);
        get_app_telescope(store(Expr.App(func, arg)), s, relaxed_u64_pred(count)),
    }
  }

  -- Decode independent usage, ownership, and locality bits.
  fn value_contract_from_bits(owned_bit: G, locality_bit: G) -> ValueContract {
    let owned = match owned_bit { 0 => Owned.Unique, 1 => Owned.Shared, };
    let locality = match locality_bit { 0 => Locality.Unrestricted, 1 => Locality.Local, };
    ValueContract.Mk(owned, locality)
  }

  fn binder_contract_from_bits(b0: G, b1: G, b2: G, b3: G) -> BinderContract {
    let uses = match b0 + 2 * b1 { 0 => Uses.Erased, 1 => Uses.Linear, 2 => Uses.Affine, 3 => Uses.Many, };
    BinderContract.Mk(uses, value_contract_from_bits(b2, b3))
  }

  fn get_lam_mode(stream: ByteStream) -> (BinderContract, ByteStream) {
    let (mode, s) = read_byte(stream);
    let [b0, b1, b2, b3, b4, b5, b6, b7] = u8_bit_decomposition(mode);
    assert_eq!(b4 + b5 + b6 + b7, 0, "reserved binder contract bits");
    (binder_contract_from_bits(b0, b1, b2, b3), s)
  }

  -- Decode the complete input and result contracts.
  fn get_all_mode(stream: ByteStream) -> ((BinderContract, ValueContract), ByteStream) {
    let (mode, s) = read_byte(stream);
    let [b0, b1, b2, b3, b4, b5, b6, b7] = u8_bit_decomposition(mode);
    assert_eq!(b6 + b7, 0, "reserved forall contract bits");
    ((binder_contract_from_bits(b0, b1, b2, b3), value_contract_from_bits(b4, b5)), s)
  }

  -- Lam telescope: read count (contract, type) binders then body, wrap as nested
  -- Lams. The base may not itself be a Lam: the v3 encoding requires maximal
  -- telescope compression.
  fn get_lam_telescope(stream: ByteStream, count: U64) -> (&Expr, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 =>
        let (body, s) = get_expr(stream);
        match load(body) {
          Expr.Lam(_, _, _) =>
            assert_eq!(0, 1, "non-canonical lambda telescope");
            (body, s),
          _ => (body, s),
        },
      0 =>
        let (contract, s) = get_lam_mode(stream);
        let (ty, s2) = get_expr(s);
        let (inner, s3) = get_lam_telescope(s2, relaxed_u64_pred(count));
        (store(Expr.Lam(contract, ty, inner)), s3),
    }
  }

  -- All telescope: read count (input/result contracts, type) binders then body,
  -- wrap as nested Alls, again requiring maximal telescope compression.
  fn get_all_telescope(stream: ByteStream, count: U64) -> (&Expr, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 =>
        let (body, s) = get_expr(stream);
        match load(body) {
          Expr.All(_, _, _, _) =>
            assert_eq!(0, 1, "non-canonical forall telescope");
            (body, s),
          _ => (body, s),
        },
      0 =>
        let (mode, s) = get_all_mode(stream);
        let (input, result) = mode;
        let (ty, s2) = get_expr(s);
        let (inner, s3) = get_all_telescope(s2, relaxed_u64_pred(count));
        (store(Expr.All(input, result, ty, inner)), s3),
    }
  }

  fn get_expr(stream: ByteStream) -> (&Expr, ByteStream) {
    let (tag, s) = get_tagn4(stream);
    let (flag, size) = tag;
    match flag {
      -- Srt: TagN4(0x0, univ_idx)
      0x0 => (store(Expr.Srt(size)), s),

      -- Var: TagN4(0x1, idx)
      0x1 => (store(Expr.Var(size)), s),

      -- Ref: TagN4(0x2, len) + TagN0(ref_idx) + univ_list
      0x2 =>
        let (ref_idx, s2) = get_tagn0(s);
        let (univ_list, s3) = get_u64_list(s2, size);
        (store(Expr.Ref(ref_idx, univ_list)), s3),

      -- Rec: TagN4(0x3, len) + TagN0(rec_idx) + univ_list
      0x3 =>
        let (rec_idx, s2) = get_tagn0(s);
        let (univ_list, s3) = get_u64_list(s2, size);
        (store(Expr.Rec(rec_idx, univ_list)), s3),

      -- Prj: TagN4(0x4, field_idx) + TagN0(type_ref_idx) + expr(val)
      0x4 =>
        let (type_ref_idx, s2) = get_tagn0(s);
        let (val, s3) = get_expr(s2);
        (store(Expr.Prj(type_ref_idx, size, val)), s3),

      -- Str: TagN4(0x5, ref_idx)
      0x5 => (store(Expr.Str(size)), s),

      -- Nat: TagN4(0x6, ref_idx)
      0x6 => (store(Expr.Nat(size)), s),

      -- App: TagN4(0x7, count) + func + args...
      --
      -- A zero count is not a legal encoding — an `App` with no
      -- arguments, or a binder telescope with no binders, is not an
      -- expression this format can denote. Rust rejects all three
      -- outright (`crates/ixon/src/serialize.rs:501-530`).
      --
      -- Accepting them made every telescope helper the identity at
      -- count 0, so `0x70`/`0x80`/`0x90` became free no-op prefixes:
      -- any expression had 3^k encodings at k extra bytes, hence 3^k
      -- content addresses the circuit reads as the same constant and no
      -- host will parse at all. Address grinding at ~1.58 bits/byte
      -- against anything that compares addresses — `canon_addr_cmp`
      -- decides canonical Muts member order on external refs.
      0x7 =>
        assert_eq!(u64_is_zero(size), 0, "App with zero arguments");
        let (func, s2) = get_expr(s);
        -- Telescope compression is maximal: a nested App in the base
        -- would serialize as one larger telescope in every host codec.
        match load(func) {
          Expr.App(_, _) =>
            assert_eq!(0, 1, "non-canonical application telescope");
            get_app_telescope(func, s2, size),
          _ => get_app_telescope(func, s2, size),
        },

      -- Lam: TagN4(0x8, count) + (contract, type)... + body
      0x8 =>
        assert_eq!(u64_is_zero(size), 0, "Lam with zero binders");
        get_lam_telescope(s, size),

      -- All: TagN4(0x9, count) + (input|result<<4, type)... + body
      0x9 =>
        assert_eq!(u64_is_zero(size), 0, "All with zero binders");
        get_all_telescope(s, size),

      -- Let: TagN4(0xA, flags) + binder + expr(ty) + expr(val) + expr(body)
      0xA => get_expr_let(s, size),

      -- Share: TagN4(0xB, idx)
      0xB => (store(Expr.Share(size)), s),
    }
  }

  -- Let arm of get_expr, split out: three recursive `get_expr` calls make it the
  -- widest (and a rare) arm, so inlined it taxes every get_expr row.
  fn get_expr_let(s: ByteStream, size: U64) -> (&Expr, ByteStream) {
    let [head, b1, b2, b3, b4, b5, b6, b7] = size;
    assert_eq!(to_field(b1) + to_field(b2) + to_field(b3) + to_field(b4) +
      to_field(b5) + to_field(b6) + to_field(b7), 0, "oversized let flags");
    assert_eq!(u8_less_than(head, 4u8), 1, "reserved let flags");
    let bits = u8_bit_decomposition(head);
    let kind = match bits[1] { 0 => LetKind.Value, 1 => LetKind.BorrowShared, };
    let (contract, s1) = get_lam_mode(s);
    let (ty, s2) = get_expr(s1);
    let (value, s3) = get_expr(s2);
    let (body, rest) = get_expr(s3);
    (store(Expr.Let(LetContract.Mk(bits[0], kind, contract), ty, value, body)), rest)
  }


  -- ============================================================================
  -- Universe deserialization
  -- ============================================================================

  -- Build a chain of Succ constructors around a base universe
  fn build_succ_chain(base: Univ, count: U64) -> Univ {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => base,
      0 =>
        let inner = build_succ_chain(base, relaxed_u64_pred(count));
        Univ.Succ(store(inner)),
    }
  }

  fn get_univ(stream: ByteStream) -> (Univ, ByteStream) {
    let (tag, s) = get_tagn2(stream);
    let (flag, size) = tag;
    match flag {
      -- Zero/Succ: TagN2(0, count)
      0 =>
        let is_zero = u64_is_zero(size);
        match is_zero {
          1 => (Univ.Zero, s),
          0 =>
            let (base, s2) = get_univ(s);
            (build_succ_chain(base, size), s2),
        },

      -- Max: TagN2(1, 0) + univ(a) + univ(b)
      1 =>
        let (a, s2) = get_univ(s);
        let (b, s3) = get_univ(s2);
        (Univ.Max(store(a), store(b)), s3),

      -- IMax: TagN2(2, 0) + univ(a) + univ(b)
      2 =>
        let (a, s2) = get_univ(s);
        let (b, s3) = get_univ(s2);
        (Univ.IMax(store(a), store(b)), s3),

      -- Var: TagN2(3, idx)
      3 => (Univ.Var(size), s),
    }
  }

  -- ============================================================================
  -- Address deserialization (32 bytes)
  -- ============================================================================

  fn get_address(stream: ByteStream) -> (Addr, ByteStream) {
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
    (store([b0, b1, b2,
      b3, b4, b5,
      b6, b7, b8,
      b9, b10, b11,
      b12, b13, b14,
      b15, b16, b17,
      b18, b19, b20,
      b21, b22, b23,
      b24, b25, b26,
      b27, b28, b29,
      b30, b31]), s)
  }

  -- ============================================================================
  -- List deserialization
  -- ============================================================================

  fn get_expr_list(stream: ByteStream, count: U64) -> (List‹&Expr›, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => (store(ListNode.Nil), stream),
      0 =>
        let (expr, s) = get_expr(stream);
        let (rest, s2) = get_expr_list(s, relaxed_u64_pred(count));
        (store(ListNode.Cons(expr, rest)), s2),
    }
  }

  fn get_univ_list(stream: ByteStream, count: U64) -> (List‹&Univ›, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => (store(ListNode.Nil), stream),
      0 =>
        let (u, s) = get_univ(stream);
        let (rest, s2) = get_univ_list(s, relaxed_u64_pred(count));
        (store(ListNode.Cons(store(u), rest)), s2),
    }
  }

  fn get_address_list(stream: ByteStream, count: U64) -> (List‹Addr›, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => (store(ListNode.Nil), stream),
      0 =>
        let (addr, s) = get_address(stream);
        let (rest, s2) = get_address_list(s, relaxed_u64_pred(count));
        (store(ListNode.Cons(addr, rest)), s2),
    }
  }

  -- ============================================================================
  -- Sharing, refs, univs table deserialization
  -- ============================================================================

  fn get_sharing(stream: ByteStream) -> (List‹&Expr›, ByteStream) {
    let (len, s) = get_tagn0(stream);
    get_expr_list(s, len)
  }

  fn get_refs(stream: ByteStream) -> (List‹Addr›, ByteStream) {
    let (len, s) = get_tagn0(stream);
    get_address_list(s, len)
  }

  fn get_univs(stream: ByteStream) -> (List‹&Univ›, ByteStream) {
    let (len, s) = get_tagn0(stream);
    get_univ_list(s, len)
  }

  -- ============================================================================
  -- Constant structure deserialization
  -- ============================================================================

  -- Unpack DefKind and DefinitionSafety from packed byte
  -- Encoding: kind * 4 + safety
  -- kind: Definition=0, Opaque=1, Theorem=2
  -- safety: Unsafe=0, Safe=1, Partial=2
  fn unpack_def_kind_safety(byte: U8) -> (DefKind, DefinitionSafety) {
    match byte {
      0 => (DefKind.Definition, DefinitionSafety.Unsafe),
      1 => (DefKind.Definition, DefinitionSafety.Safe),
      2 => (DefKind.Definition, DefinitionSafety.Partial),
      4 => (DefKind.Opaque, DefinitionSafety.Unsafe),
      5 => (DefKind.Opaque, DefinitionSafety.Safe),
      6 => (DefKind.Opaque, DefinitionSafety.Partial),
      8 => (DefKind.Theorem, DefinitionSafety.Unsafe),
      9 => (DefKind.Theorem, DefinitionSafety.Safe),
      10 => (DefKind.Theorem, DefinitionSafety.Partial),
    }
  }

  -- Definition: byte(packed_kind_safety) + TagN0(lvls) + expr(typ) + expr(value)
  fn get_definition(stream: ByteStream) -> (Definition, ByteStream) {
    let (packed, s) = read_byte(stream);
    let (kind, safety) = unpack_def_kind_safety(packed);
    let (lvls, s2) = get_tagn0(s);
    let (typ, s3) = get_expr(s2);
    let (value, s4) = get_expr(s3);
    (Definition.Mk(kind, safety, lvls, typ, value), s4)
  }

  -- RecursorRule: TagN0(fields) + expr(rhs)
  fn get_recursor_rule(stream: ByteStream) -> (RecursorRule, ByteStream) {
    let (fields, s) = get_tagn0(stream);
    let (rhs, s2) = get_expr(s);
    (RecursorRule.Mk(fields, rhs), s2)
  }

  fn get_recursor_rule_list(stream: ByteStream, count: U64) -> (List‹RecursorRule›, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => (store(ListNode.Nil), stream),
      0 =>
        let (rule, s) = @get_recursor_rule(stream);
        let (rest, s2) = get_recursor_rule_list(s, relaxed_u64_pred(count));
        (store(ListNode.Cons(rule, rest)), s2),
    }
  }

  -- Recursor: byte(bools) + TagN0(lvls) + TagN0(params) + TagN0(indices) +
  --           TagN0(motives) + TagN0(minors) + expr(typ) + TagN0(rules_len) + rules...
  fn get_recursor(stream: ByteStream) -> (Recursor, ByteStream) {
    let (bools_byte, s) = read_byte(stream);
    assert_eq!(u8_less_than(bools_byte, 4u8), 1, "invalid recursor flags");
    let bits = u8_bit_decomposition(bools_byte);
    let k = bits[0];
    let is_unsafe = bits[1];
    let (lvls, s2) = get_tagn0(s);
    let (params, s3) = get_tagn0(s2);
    let (indices, s4) = get_tagn0(s3);
    let (motives, s5) = get_tagn0(s4);
    let (minors, s6) = get_tagn0(s5);
    let (typ, s7) = get_expr(s6);
    let (rules_len, s8) = get_tagn0(s7);
    let (rules, s9) = get_recursor_rule_list(s8, rules_len);
    (Recursor.Mk(k, is_unsafe, lvls, params, indices, motives, minors, typ, rules), s9)
  }

  -- Axiom: byte(is_unsafe) + TagN0(lvls) + expr(typ)
  -- A wire byte standing for a Bool must be 0 or 1, as Rust's `get_bool`
  -- requires (`crates/ixon/src/serialize.rs:55-61`).
  --
  -- Load-bearing, not hygiene: an unvalidated flag flows into
  -- `is_unsafe_ci` and is consumed MULTIPLICATIVELY by `safe_refs_only`
  -- (`Kernel/Check.lean:64-82`), which takes `1 - is_unsafe_ci(ci)` per
  -- `Const` and multiplies the arms together. Two references to
  -- constants carrying `is_unsafe = 2` give `(1-2)*(1-2) = 1` and
  -- satisfy the `assert_eq!(…, 1)` that is the entire Safe→Unsafe wall.
  fn assert_wire_bool(b: U8) {
    assert_eq!(u8_less_than(b, 2u8), 1, "Bool byte is not 0 or 1");
    ()
  }

  fn get_axiom(stream: ByteStream) -> (Axiom, ByteStream) {
    let (is_unsafe, s) = read_byte(stream);
    assert_wire_bool(is_unsafe);
    let (lvls, s2) = get_tagn0(s);
    let (typ, s3) = get_expr(s2);
    (Axiom.Mk(to_field(is_unsafe), lvls, typ), s3)
  }

  -- QuotKind: byte(0=Typ, 1=Ctor, 2=Lift, 3=Ind)
  fn get_quot_kind(byte: U8) -> QuotKind {
    match byte {
      0 => QuotKind.Typ,
      1 => QuotKind.Ctor,
      2 => QuotKind.Lift,
      3 => QuotKind.Ind,
    }
  }

  -- Quotient: byte(kind) + TagN0(lvls) + expr(typ)
  fn get_quotient(stream: ByteStream) -> (Quotient, ByteStream) {
    let (kind_byte, s) = read_byte(stream);
    let kind = get_quot_kind(kind_byte);
    let (lvls, s2) = get_tagn0(s);
    let (typ, s3) = get_expr(s2);
    (Quotient.Mk(kind, lvls, typ), s3)
  }

  -- Constructor: byte(is_unsafe) + TagN0(lvls) + TagN0(cidx) + TagN0(params) +
  --              TagN0(fields) + expr(typ)
  fn get_constructor(stream: ByteStream) -> (Constructor, ByteStream) {
    let (is_unsafe, s) = read_byte(stream);
    assert_wire_bool(is_unsafe);
    let (lvls, s2) = get_tagn0(s);
    let (cidx, s3) = get_tagn0(s2);
    let (params, s4) = get_tagn0(s3);
    let (fields, s5) = get_tagn0(s4);
    let (typ, s6) = get_expr(s5);
    (Constructor.Mk(to_field(is_unsafe), lvls, cidx, params, fields, typ), s6)
  }

  fn get_constructor_list(stream: ByteStream, count: U64) -> (List‹Constructor›, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => (store(ListNode.Nil), stream),
      0 =>
        let (ctor, s) = get_constructor(stream);
        let (rest, s2) = get_constructor_list(s, relaxed_u64_pred(count));
        (store(ListNode.Cons(ctor, rest)), s2),
    }
  }

  -- Inductive: byte(bools) + TagN0(lvls) + TagN0(params) + TagN0(indices) +
  --            expr(typ) + TagN0(ctors_len) + ctors...
  fn get_inductive(stream: ByteStream) -> (Inductive, ByteStream) {
    let (bools_byte, s) = read_byte(stream);
    assert_wire_bool(bools_byte);
    let bits = u8_bit_decomposition(bools_byte);
    let is_unsafe = bits[0];
    let (lvls, s2) = get_tagn0(s);
    let (params, s3) = get_tagn0(s2);
    let (indices, s4) = get_tagn0(s3);
    let (typ, s5) = get_expr(s4);
    let (ctors_len, s6) = get_tagn0(s5);
    let (ctors, s7) = get_constructor_list(s6, ctors_len);
    (Inductive.Mk(is_unsafe, lvls, params, indices, typ, ctors), s7)
  }

  -- ============================================================================
  -- Projection deserialization
  -- ============================================================================

  -- InductiveProj: TagN0(idx) + address(block)
  fn get_inductive_proj(stream: ByteStream) -> (InductiveProj, ByteStream) {
    let (idx, s) = get_tagn0(stream);
    let (block, s2) = get_address(s);
    (InductiveProj.Mk(idx, block), s2)
  }

  -- ConstructorProj: TagN0(idx) + TagN0(cidx) + address(block)
  fn get_constructor_proj(stream: ByteStream) -> (ConstructorProj, ByteStream) {
    let (idx, s) = get_tagn0(stream);
    let (cidx, s2) = get_tagn0(s);
    let (block, s3) = get_address(s2);
    (ConstructorProj.Mk(idx, cidx, block), s3)
  }

  -- RecursorProj: TagN0(idx) + address(block)
  fn get_recursor_proj(stream: ByteStream) -> (RecursorProj, ByteStream) {
    let (idx, s) = get_tagn0(stream);
    let (block, s2) = get_address(s);
    (RecursorProj.Mk(idx, block), s2)
  }

  -- DefinitionProj: TagN0(idx) + address(block)
  fn get_definition_proj(stream: ByteStream) -> (DefinitionProj, ByteStream) {
    let (idx, s) = get_tagn0(stream);
    let (block, s2) = get_address(s);
    (DefinitionProj.Mk(idx, block), s2)
  }

  -- ============================================================================
  -- Mutual constant deserialization
  -- ============================================================================

  -- MutConst: byte(tag) + payload
  fn get_mut_const(stream: ByteStream) -> (MutConst, ByteStream) {
    let (tag, s) = read_byte(stream);
    match tag {
      0 =>
        let (defn, s2) = get_definition(s);
        (MutConst.Defn(defn), s2),
      1 =>
        let (indc, s2) = get_inductive(s);
        (MutConst.Indc(indc), s2),
      2 =>
        let (recr, s2) = get_recursor(s);
        (MutConst.Recr(recr), s2),
    }
  }

  fn get_mut_const_list(stream: ByteStream, count: U64) -> (List‹MutConst›, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => (store(ListNode.Nil), stream),
      0 =>
        let (mc, s) = get_mut_const(stream);
        let (rest, s2) = get_mut_const_list(s, relaxed_u64_pred(count));
        (store(ListNode.Cons(mc, rest)), s2),
    }
  }

  -- ============================================================================
  -- Constant info deserialization
  -- ============================================================================

  -- Dispatch on variant number (0-7) to deserialize the appropriate ConstantInfo
  fn get_constant_info_by_variant(variant: G, stream: ByteStream) -> (ConstantInfo, ByteStream) {
    match variant {
      0 =>
        let (defn, s) = get_definition(stream);
        (ConstantInfo.Defn(defn), s),
      1 =>
        let (recr, s) = get_recursor(stream);
        (ConstantInfo.Recr(recr), s),
      2 =>
        let (axim, s) = get_axiom(stream);
        (ConstantInfo.Axio(axim), s),
      3 =>
        let (quot, s) = get_quotient(stream);
        (ConstantInfo.Quot(quot), s),
      4 =>
        let (prj, s) = get_constructor_proj(stream);
        (ConstantInfo.CPrj(prj), s),
      5 =>
        let (prj, s) = get_recursor_proj(stream);
        (ConstantInfo.RPrj(prj), s),
      6 =>
        let (prj, s) = get_inductive_proj(stream);
        (ConstantInfo.IPrj(prj), s),
      7 =>
        let (prj, s) = get_definition_proj(stream);
        (ConstantInfo.DPrj(prj), s),
    }
  }

  -- Parse ConstantInfo from flag (0xC for Muts, 0xD for non-Muts) and size
  fn get_constant_info(flag: G, size: U64, stream: ByteStream) -> (ConstantInfo, ByteStream) {
    match flag {
      -- Muts: flag=0xC, size is the entry count
      0xC =>
        let (mutuals, s) = get_mut_const_list(stream, size);
        (ConstantInfo.Muts(mutuals), s),
      -- Non-Muts: flag=0xD, size[0] is the variant number.
      --
      -- Dispatch on the FULL TagN size, matching Rust `ConstantInfo::get`
      -- which matches `tag.size: u64` and errors on anything outside
      -- 0-7. The variant is only ever 0-7, so the high 7 bytes must be
      -- zero; without this `0xD8 0xF8` (size 0x100) has low byte 0, and
      -- the circuit parses a `Defn` from a buffer Rust rejects outright.
      -- Same guard, same reasoning as `run_claim`'s (Kernel/Claim.lean).
      -- Sum is 0 iff every high byte is 0 (7 bytes, max sum 1785, no wrap).
      0xD =>
        let [_, sz1, sz2, sz3, sz4, sz5, sz6, sz7] = size;
        assert_eq!(((((((to_field(sz1) + to_field(sz2)) + to_field(sz3))
                      + to_field(sz4)) + to_field(sz5)) + to_field(sz6))
                      + to_field(sz7)), 0,
          "constant info: TagN size exceeds a single byte");
        get_constant_info_by_variant(to_field(size[0]), stream),
    }
  }

  -- ============================================================================
  -- Top-level constant deserialization
  -- ============================================================================

  fn get_constant(stream: ByteStream) -> (Constant, ByteStream) {
    let (tag, s) = get_tagn4(stream);
    let (flag, size) = tag;
    let (info, s2) = @get_constant_info(flag, size, s);
    let (sharing, s3) = @get_sharing(s2);
    let (refs, s4) = @get_refs(s3);
    let (univs, s5) = @get_univs(s4);
    (Constant.Mk(info, sharing, refs, univs), s5)
  }
⟧

end IxVM

end
