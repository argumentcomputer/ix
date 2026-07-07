/-
  # Aiur kernel claim dispatcher

  The flow mirrors how constants are loaded: hash the bytes, assert
  equality with the supplied digest, deserialize once into an Aiur
  ADT, and use the structured value. No scattered inline-parse
  comparisons.

      claim_digest ── IOBuffer ─▶ claim_bytes
                                  │
                                  ▼
                          blake3 assert
                                  │
                                  ▼
                           get_claim                    ◀ deserialize
                                  │
                                  ▼
                       match Claim variant              ◀ structured use

  Wire format mirrors `Ix/Claim.lean`:

    Variant 3  EvalClaim       (input output : Addr) (asm : Opt Addr)
    Variant 4  CheckClaim      (const : Addr)        (asm : Opt Addr)
    Variant 5  CheckEnvClaim   (root  : Addr)        (asm : Opt Addr)
    Variant 6  RevealClaim     (comm  : Addr) (info : RevealConstantInfo)
    Variant 7  ContainsClaim   (tree  : Addr) (const : Addr)

  Eval is the only `run_*` arm still placeholder — Rust kernel has
  not pinned reduction semantics yet.
-/
module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Ingress
public import Ix.IxVM.IxonSerialize
public import Ix.IxVM.IxonDeserialize
public import Ix.IxVM.Kernel.Check

public section

namespace IxVM

def claim := ⟦
  -- ============================================================================
  -- Reveal-specific ADT mirror. `RevealConstantInfo` parallels
  -- `ConstantInfo` (from `Ix/IxVM/Ixon.lean`) but every payload field
  -- is wrapped in `Option‹…›` for selective revelation, and Expr
  -- fields are replaced by their content-hashed `Addr`. The shape is
  -- a 1:1 copy of `Ix.RevealConstantInfo` in `Ix/Claim.lean`.
  -- ============================================================================

  -- (ruleIdx, fields, rhs_addr). `rhs_addr` = blake3(put_expr rhs).
  enum RevealRecursorRule {
    Mk(U64, U64, Addr)
  }

  -- (isUnsafe, lvls, cidx, params, fields, typ).
  enum RevealConstructorInfo {
    Mk(Option‹G›, Option‹U64›, Option‹U64›,
       Option‹U64›, Option‹U64›, Option‹Addr›)
  }

  enum RevealMutConstInfo {
    Defn(Option‹DefKind›, Option‹DefinitionSafety›,
         Option‹U64›, Option‹Addr›, Option‹Addr›),
    Indc(Option‹G›,
         Option‹U64›, Option‹U64›, Option‹U64›,
         Option‹Addr›,
         Option‹List‹(U64, RevealConstructorInfo)››),
    Recr(Option‹G›, Option‹G›,
         Option‹U64›, Option‹U64›, Option‹U64›,
         Option‹U64›, Option‹U64›,
         Option‹Addr›, Option‹List‹RevealRecursorRule››)
  }

  enum RevealConstantInfo {
    Defn(Option‹DefKind›, Option‹DefinitionSafety›,
         Option‹U64›, Option‹Addr›, Option‹Addr›),
    Recr(Option‹G›, Option‹G›,
         Option‹U64›, Option‹U64›, Option‹U64›,
         Option‹U64›, Option‹U64›,
         Option‹Addr›, Option‹List‹RevealRecursorRule››),
    Axio(Option‹G›, Option‹U64›, Option‹Addr›),
    Quot(Option‹QuotKind›, Option‹U64›, Option‹Addr›),
    CPrj(Option‹U64›, Option‹U64›, Option‹Addr›),
    RPrj(Option‹U64›, Option‹Addr›),
    IPrj(Option‹U64›, Option‹Addr›),
    DPrj(Option‹U64›, Option‹Addr›),
    Muts(List‹(U64, RevealMutConstInfo)›)
  }

  -- The full claim ADT — parallels `Ix.Claim` in `Ix/Claim.lean`.
  enum Claim {
    Eval(Addr, Addr, Option‹Addr›),
    Check(Addr, Option‹Addr›),
    CheckEnv(Addr, Option‹Addr›),
    Reveal(Addr, RevealConstantInfo),
    Contains(Addr, Addr)
  }

  -- ============================================================================
  -- Wire-format helpers shared across the deserializers.
  -- ============================================================================

  -- `Option<Address>` per `Ix/Claim.lean::putOptAddr` (top-level
  -- `assumptions` slot, NOT the bitmask-gated reveal-fields form).
  --   [0x00]              → none
  --   [0x01][addr:32]     → some addr
  fn get_opt_addr(stream: ByteStream) -> (Option‹Addr›, ByteStream) {
    let (tag, s) = read_byte(stream);
    match tag {
      0 => (Option.None, s),
      1 =>
        let (addr, s2) = get_address(s);
        (Option.Some(addr), s2),
    }
  }

  -- Bitmask-gated decoders for the per-field Reveal payloads.
  fn get_opt_u64_masked(mb: G, stream: ByteStream)
      -> (Option‹U64›, ByteStream) {
    match mb {
      0 => (Option.None, stream),
      _ =>
        let (n, s) = get_tag0(stream);
        (Option.Some(n), s),
    }
  }

  fn get_opt_addr_masked(mb: G, stream: ByteStream)
      -> (Option‹Addr›, ByteStream) {
    match mb {
      0 => (Option.None, stream),
      _ =>
        let (a, s) = get_address(stream);
        (Option.Some(a), s),
    }
  }

  fn get_opt_bool_masked(mb: G, stream: ByteStream)
      -> (Option‹G›, ByteStream) {
    match mb {
      0 => (Option.None, stream),
      _ =>
        let (b, s) = read_byte(stream);
        (Option.Some(to_field(b)), s),
    }
  }

  fn get_opt_def_kind_masked(mb: G, stream: ByteStream)
      -> (Option‹DefKind›, ByteStream) {
    match mb {
      0 => (Option.None, stream),
      _ =>
        let (b, s) = read_byte(stream);
        match b {
          0 => (Option.Some(DefKind.Definition), s),
          1 => (Option.Some(DefKind.Opaque), s),
          2 => (Option.Some(DefKind.Theorem), s),
        },
    }
  }

  fn get_opt_def_safety_masked(mb: G, stream: ByteStream)
      -> (Option‹DefinitionSafety›, ByteStream) {
    match mb {
      0 => (Option.None, stream),
      _ =>
        let (b, s) = read_byte(stream);
        match b {
          0 => (Option.Some(DefinitionSafety.Unsafe), s),
          1 => (Option.Some(DefinitionSafety.Safe), s),
          2 => (Option.Some(DefinitionSafety.Partial), s),
        },
    }
  }

  fn get_opt_quot_kind_masked(mb: G, stream: ByteStream)
      -> (Option‹QuotKind›, ByteStream) {
    match mb {
      0 => (Option.None, stream),
      _ =>
        let (b, s) = read_byte(stream);
        match b {
          0 => (Option.Some(QuotKind.Typ), s),
          1 => (Option.Some(QuotKind.Ctor), s),
          2 => (Option.Some(QuotKind.Lift), s),
          3 => (Option.Some(QuotKind.Ind), s),
        },
    }
  }

  -- ============================================================================
  -- RevealRecursorRule list parser.
  -- Wire: `Tag0(count) + count × (Tag0(idx) + Tag0(fields) + Address)`.
  -- ============================================================================
  fn get_reveal_rule(stream: ByteStream) -> (RevealRecursorRule, ByteStream) {
    let (rule_idx, s) = get_tag0(stream);
    let (fields, s) = get_tag0(s);
    let (rhs, s) = get_address(s);
    (RevealRecursorRule.Mk(rule_idx, fields, rhs), s)
  }

  fn get_reveal_rule_list_inner(stream: ByteStream, count: U64)
      -> (List‹RevealRecursorRule›, ByteStream) {
    match u64_is_zero(count) {
      1 => (store(ListNode.Nil), stream),
      _ =>
        let (rule, s) = get_reveal_rule(stream);
        let (rest, s2) = get_reveal_rule_list_inner(s, relaxed_u64_pred(count));
        (store(ListNode.Cons(rule, rest)), s2),
    }
  }

  fn get_opt_rule_list_masked(mb: G, stream: ByteStream)
      -> (Option‹List‹RevealRecursorRule››, ByteStream) {
    match mb {
      0 => (Option.None, stream),
      _ =>
        let (count, s) = get_tag0(stream);
        let (rules, s2) = get_reveal_rule_list_inner(s, count);
        (Option.Some(rules), s2),
    }
  }

  -- ============================================================================
  -- RevealConstructorInfo parser. 6 optional fields, mask bits 0..5.
  -- ============================================================================
  fn get_reveal_ctor_info(stream: ByteStream)
      -> (RevealConstructorInfo, ByteStream) {
    let (mask, s) = get_tag0(stream);
    let mask_lo = u8_bit_decomposition(mask[0]);
    let [b0, b1, b2, b3, b4, b5, _, _] = mask_lo;
    let (is_unsafe, s) = get_opt_bool_masked(b0, s);
    let (lvls, s) = get_opt_u64_masked(b1, s);
    let (cidx, s) = get_opt_u64_masked(b2, s);
    let (params, s) = get_opt_u64_masked(b3, s);
    let (fields, s) = get_opt_u64_masked(b4, s);
    let (typ, s) = get_opt_addr_masked(b5, s);
    (RevealConstructorInfo.Mk(is_unsafe, lvls, cidx, params, fields, typ), s)
  }

  fn get_ctor_entry(stream: ByteStream)
      -> ((U64, RevealConstructorInfo), ByteStream) {
    let (idx, s) = get_tag0(stream);
    let (info, s) = get_reveal_ctor_info(s);
    ((idx, info), s)
  }

  fn get_ctor_entry_list_inner(stream: ByteStream, count: U64)
      -> (List‹(U64, RevealConstructorInfo)›, ByteStream) {
    match u64_is_zero(count) {
      1 => (store(ListNode.Nil), stream),
      _ =>
        let (entry, s) = get_ctor_entry(stream);
        let (rest, s2) = get_ctor_entry_list_inner(s, relaxed_u64_pred(count));
        (store(ListNode.Cons(entry, rest)), s2),
    }
  }

  fn get_opt_ctor_entry_list_masked(mb: G, stream: ByteStream)
      -> (Option‹List‹(U64, RevealConstructorInfo)››, ByteStream) {
    match mb {
      0 => (Option.None, stream),
      _ =>
        let (count, s) = get_tag0(stream);
        let (list, s2) = get_ctor_entry_list_inner(s, count);
        (Option.Some(list), s2),
    }
  }

  -- ============================================================================
  -- RevealMutConstInfo parser. variant + mask + per-bit fields.
  -- ============================================================================
  fn get_reveal_mut_const_info(stream: ByteStream)
      -> (RevealMutConstInfo, ByteStream) {
    let (variant, s) = read_byte(stream);
    let (mask, s) = get_tag0(s);
    let mask_lo = u8_bit_decomposition(mask[0]);
    let [b0, b1, b2, b3, b4, b5, b6, b7] = mask_lo;
    let mask_hi = u8_bit_decomposition(mask[1]);
    let [b8, _, _, _, _, _, _, _] = mask_hi;
    match variant {
      0 =>
        let (kind, s) = get_opt_def_kind_masked(b0, s);
        let (safety, s) = get_opt_def_safety_masked(b1, s);
        let (lvls, s) = get_opt_u64_masked(b2, s);
        let (typ, s) = get_opt_addr_masked(b3, s);
        let (value, s) = get_opt_addr_masked(b4, s);
        (RevealMutConstInfo.Defn(kind, safety, lvls, typ, value), s),
      1 =>
        let (is_unsafe, s) = get_opt_bool_masked(b0, s);
        let (lvls, s) = get_opt_u64_masked(b1, s);
        let (params, s) = get_opt_u64_masked(b2, s);
        let (indices, s) = get_opt_u64_masked(b3, s);
        let (typ, s) = get_opt_addr_masked(b4, s);
        let (ctors, s) = get_opt_ctor_entry_list_masked(b5, s);
        (RevealMutConstInfo.Indc(is_unsafe, lvls, params,
                                  indices, typ, ctors), s),
      2 =>
        let (k, s) = get_opt_bool_masked(b0, s);
        let (is_unsafe, s) = get_opt_bool_masked(b1, s);
        let (lvls, s) = get_opt_u64_masked(b2, s);
        let (params, s) = get_opt_u64_masked(b3, s);
        let (indices, s) = get_opt_u64_masked(b4, s);
        let (motives, s) = get_opt_u64_masked(b5, s);
        let (minors, s) = get_opt_u64_masked(b6, s);
        let (typ, s) = get_opt_addr_masked(b7, s);
        let (rules, s) = get_opt_rule_list_masked(b8, s);
        (RevealMutConstInfo.Recr(k, is_unsafe, lvls, params, indices,
                                  motives, minors, typ, rules), s),
    }
  }

  fn get_mut_entry(stream: ByteStream)
      -> ((U64, RevealMutConstInfo), ByteStream) {
    let (idx, s) = get_tag0(stream);
    let (info, s) = get_reveal_mut_const_info(s);
    ((idx, info), s)
  }

  fn get_mut_entry_list_inner(stream: ByteStream, count: U64)
      -> (List‹(U64, RevealMutConstInfo)›, ByteStream) {
    match u64_is_zero(count) {
      1 => (store(ListNode.Nil), stream),
      _ =>
        let (entry, s) = get_mut_entry(stream);
        let (rest, s2) = get_mut_entry_list_inner(s, relaxed_u64_pred(count));
        (store(ListNode.Cons(entry, rest)), s2),
    }
  }

  -- ============================================================================
  -- RevealConstantInfo parser. `variant + mask:Tag0 + per-bit fields`.
  -- ============================================================================
  fn get_reveal_info(stream: ByteStream) -> (RevealConstantInfo, ByteStream) {
    let (variant, s) = read_byte(stream);
    let (mask, s) = get_tag0(s);
    let mask_lo = u8_bit_decomposition(mask[0]);
    let [b0, b1, b2, b3, b4, b5, b6, b7] = mask_lo;
    let mask_hi = u8_bit_decomposition(mask[1]);
    let [b8, _, _, _, _, _, _, _] = mask_hi;
    match variant {
      0 =>
        let (kind, s) = get_opt_def_kind_masked(b0, s);
        let (safety, s) = get_opt_def_safety_masked(b1, s);
        let (lvls, s) = get_opt_u64_masked(b2, s);
        let (typ, s) = get_opt_addr_masked(b3, s);
        let (value, s) = get_opt_addr_masked(b4, s);
        (RevealConstantInfo.Defn(kind, safety, lvls, typ, value), s),
      1 =>
        let (k, s) = get_opt_bool_masked(b0, s);
        let (is_unsafe, s) = get_opt_bool_masked(b1, s);
        let (lvls, s) = get_opt_u64_masked(b2, s);
        let (params, s) = get_opt_u64_masked(b3, s);
        let (indices, s) = get_opt_u64_masked(b4, s);
        let (motives, s) = get_opt_u64_masked(b5, s);
        let (minors, s) = get_opt_u64_masked(b6, s);
        let (typ, s) = get_opt_addr_masked(b7, s);
        let (rules, s) = get_opt_rule_list_masked(b8, s);
        (RevealConstantInfo.Recr(k, is_unsafe, lvls, params, indices,
                                  motives, minors, typ, rules), s),
      2 =>
        let (is_unsafe, s) = get_opt_bool_masked(b0, s);
        let (lvls, s) = get_opt_u64_masked(b1, s);
        let (typ, s) = get_opt_addr_masked(b2, s);
        (RevealConstantInfo.Axio(is_unsafe, lvls, typ), s),
      3 =>
        let (kind, s) = get_opt_quot_kind_masked(b0, s);
        let (lvls, s) = get_opt_u64_masked(b1, s);
        let (typ, s) = get_opt_addr_masked(b2, s);
        (RevealConstantInfo.Quot(kind, lvls, typ), s),
      4 =>
        let (idx, s) = get_opt_u64_masked(b0, s);
        let (cidx, s) = get_opt_u64_masked(b1, s);
        let (block, s) = get_opt_addr_masked(b2, s);
        (RevealConstantInfo.CPrj(idx, cidx, block), s),
      5 =>
        let (idx, s) = get_opt_u64_masked(b0, s);
        let (block, s) = get_opt_addr_masked(b1, s);
        (RevealConstantInfo.RPrj(idx, block), s),
      6 =>
        let (idx, s) = get_opt_u64_masked(b0, s);
        let (block, s) = get_opt_addr_masked(b1, s);
        (RevealConstantInfo.IPrj(idx, block), s),
      7 =>
        let (idx, s) = get_opt_u64_masked(b0, s);
        let (block, s) = get_opt_addr_masked(b1, s);
        (RevealConstantInfo.DPrj(idx, block), s),
      8 =>
        let (components, s) = match b0 {
          0 => (store(ListNode.Nil), s),
          1 =>
            let (count, s2) = get_tag0(s);
            get_mut_entry_list_inner(s2, count),
        };
        (RevealConstantInfo.Muts(components), s),
    }
  }

  -- ============================================================================
  -- Claim parser. Parses Tag4(0xE, variant) wrapper + per-variant
  -- payload into the `Claim` ADT.
  -- ============================================================================
  fn get_claim(bytes: ByteStream) -> (Claim, ByteStream) {
    let (tag, s) = get_tag4(bytes);
    let (flag, size) = tag;
    assert_eq!(flag, 0xE);
    let variant = size[0];
    match variant {
      3 =>
        let (input, s) = get_address(s);
        let (output, s) = get_address(s);
        let (asm, s) = get_opt_addr(s);
        (Claim.Eval(input, output, asm), s),
      4 =>
        let (c, s) = get_address(s);
        let (asm, s) = get_opt_addr(s);
        (Claim.Check(c, asm), s),
      5 =>
        let (root, s) = get_address(s);
        let (asm, s) = get_opt_addr(s);
        (Claim.CheckEnv(root, asm), s),
      6 =>
        let (comm, s) = get_address(s);
        let (info, s) = get_reveal_info(s);
        (Claim.Reveal(comm, info), s),
      7 =>
        let (tree, s) = get_address(s);
        let (target, s) = get_address(s);
        (Claim.Contains(tree, target), s),
    }
  }

  -- Load + verify a claim from the IOBuffer at key=`digest`. Mirrors
  -- `load_verified_constant`: read bytes, recompute blake3, assert
  -- equality, deserialize, assert no trailing data.
  -- Load + verify a claim from IOBuffer at `digest` (ch 0). Reads bytes,
  -- recomputes blake3, asserts equality, deserialises.
  fn load_verified_claim(digest: [U8; 32]) -> Claim {
    let (idx, len) = io_get_info(0, digest);
    let bytes = #read_byte_stream(0, idx, len);
    let _ = verify_bytes_against(bytes, digest);
    let (claim, rest) = get_claim(bytes);
    assert_eq!(load(rest), ListNode.Nil);
    claim
  }

  -- ============================================================================
  -- Content hash of an `Expr`: `blake3(put_expr expr)`. Per
  -- docs/Ixon.md:970-971 — Reveal claim's `Option<Address>` Expr
  -- fields bind to this hash.
  -- ============================================================================
  fn expr_addr(e_ref: &Expr) -> Addr {
    let bytes = put_expr(load(e_ref), store(ListNode.Nil));
    bytes_to_addr(bytes)
  }

  -- ============================================================================
  -- Per-field equality checks. None = no-op (selective reveal);
  -- Some(claimed) = assert equality with the real field.
  -- ============================================================================
  fn def_kind_tag(k: DefKind) -> G {
    match k {
      DefKind.Definition => 0,
      DefKind.Opaque => 1,
      DefKind.Theorem => 2,
    }
  }

  fn def_safety_tag(s: DefinitionSafety) -> G {
    match s {
      DefinitionSafety.Unsafe => 0,
      DefinitionSafety.Safe => 1,
      DefinitionSafety.Partial => 2,
    }
  }

  fn quot_kind_tag(k: QuotKind) -> G {
    match k {
      QuotKind.Typ => 0,
      QuotKind.Ctor => 1,
      QuotKind.Lift => 2,
      QuotKind.Ind => 3,
    }
  }

  fn check_opt_def_kind(real: DefKind, opt: Option‹DefKind›) {
    match opt {
      Option.None => (),
      Option.Some(claimed) =>
        assert_eq!(def_kind_tag(real), def_kind_tag(claimed));
        (),
    }
  }

  fn check_opt_def_safety(real: DefinitionSafety,
                          opt: Option‹DefinitionSafety›) {
    match opt {
      Option.None => (),
      Option.Some(claimed) =>
        assert_eq!(def_safety_tag(real), def_safety_tag(claimed));
        (),
    }
  }

  fn check_opt_quot_kind(real: QuotKind, opt: Option‹QuotKind›) {
    match opt {
      Option.None => (),
      Option.Some(claimed) =>
        assert_eq!(quot_kind_tag(real), quot_kind_tag(claimed));
        (),
    }
  }

  fn check_opt_bool(real: G, opt: Option‹G›) {
    match opt {
      Option.None => (),
      Option.Some(claimed) =>
        assert_eq!(real, claimed);
        (),
    }
  }

  fn check_opt_u64(real: U64, opt: Option‹U64›) {
    match opt {
      Option.None => (),
      Option.Some(claimed) =>
        assert_eq!(real, claimed);
        (),
    }
  }

  fn check_opt_addr(real: Addr, opt: Option‹Addr›) {
    match opt {
      Option.None => (),
      Option.Some(claimed) =>
        assert_eq!(load(real), load(claimed));
        (),
    }
  }

  fn check_opt_expr_addr(real_e: &Expr, opt: Option‹Addr›) {
    match opt {
      Option.None => (),
      Option.Some(claimed) =>
        let computed = expr_addr(real_e);
        assert_eq!(load(computed), load(claimed));
        (),
    }
  }

  -- Walk both lists in lockstep: claimed (idx, fields, rhs_addr) per
  -- entry vs real (fields, rhs:&Expr) — positional `idx` is read but
  -- not asserted (matches `Ix.RevealRecursorRule.ruleIdx` semantics).
  fn check_recr_rules(real: List‹RecursorRule›,
                      claimed: List‹RevealRecursorRule›) {
    match load(claimed) {
      ListNode.Nil =>
        match load(real) {
          ListNode.Nil => (),
        },
      ListNode.Cons(cr, rest_claimed) =>
        match load(real) {
          ListNode.Cons(rr, rest_real) =>
            match cr {
              RevealRecursorRule.Mk(_c_idx, c_fields, c_rhs) =>
                match rr {
                  RecursorRule.Mk(r_fields, r_rhs) =>
                    assert_eq!(r_fields, c_fields);
                    let _ = check_opt_expr_addr(r_rhs, Option.Some(c_rhs));
                    check_recr_rules(rest_real, rest_claimed),
                },
            },
        },
    }
  }

  fn check_opt_recr_rules(real: List‹RecursorRule›,
                          opt: Option‹List‹RevealRecursorRule››) {
    match opt {
      Option.None => (),
      Option.Some(claimed) => check_recr_rules(real, claimed),
    }
  }

  -- Constructor revelation: compare the Constructor at position `idx`
  -- in the real list against the per-field Option‹…› bits.
  fn check_ctor_entry(real_list: List‹Constructor›,
                      idx: U64,
                      info: RevealConstructorInfo) {
    let real_ctor = list_lookup_u64(real_list, idx);
    match info {
      RevealConstructorInfo.Mk(opt_unsafe, opt_lvls, opt_cidx,
                                opt_params, opt_fields, opt_typ) =>
        match real_ctor {
          Constructor.Mk(r_unsafe, r_lvls, r_cidx, r_params, r_fields, r_typ) =>
            let _ = check_opt_bool(r_unsafe, opt_unsafe);
            let _ = check_opt_u64(r_lvls, opt_lvls);
            let _ = check_opt_u64(r_cidx, opt_cidx);
            let _ = check_opt_u64(r_params, opt_params);
            let _ = check_opt_u64(r_fields, opt_fields);
            check_opt_expr_addr(r_typ, opt_typ),
        },
    }
  }

  fn check_ctor_entries(real_list: List‹Constructor›,
                        claimed: List‹(U64, RevealConstructorInfo)›) {
    match load(claimed) {
      ListNode.Nil => (),
      ListNode.Cons(entry, rest) =>
        match entry {
          (idx, info) =>
            let _ = check_ctor_entry(real_list, idx, info);
            check_ctor_entries(real_list, rest),
        },
    }
  }

  fn check_opt_ctor_entries(real_list: List‹Constructor›,
                            opt: Option‹List‹(U64, RevealConstructorInfo)››) {
    match opt {
      Option.None => (),
      Option.Some(claimed) => check_ctor_entries(real_list, claimed),
    }
  }

  -- MutConst revelation: dispatch on the real variant vs the claimed
  -- variant; mismatched pairs fail.
  fn check_mut_const(real: MutConst, claimed: RevealMutConstInfo) {
    match real {
      MutConst.Defn(d) =>
        match claimed {
          RevealMutConstInfo.Defn(opt_kind, opt_safety, opt_lvls,
                                   opt_typ, opt_value) =>
            match d {
              Definition.Mk(r_kind, r_safety, r_lvls, r_typ, r_value) =>
                let _ = check_opt_def_kind(r_kind, opt_kind);
                let _ = check_opt_def_safety(r_safety, opt_safety);
                let _ = check_opt_u64(r_lvls, opt_lvls);
                let _ = check_opt_expr_addr(r_typ, opt_typ);
                check_opt_expr_addr(r_value, opt_value),
            },
        },
      MutConst.Indc(i) =>
        match claimed {
          RevealMutConstInfo.Indc(opt_unsafe, opt_lvls,
                                   opt_params, opt_indices,
                                   opt_typ, opt_ctors) =>
            match i {
              Inductive.Mk(r_unsafe, r_lvls, r_params,
                            r_indices, r_typ, r_ctors) =>
                let _ = check_opt_bool(r_unsafe, opt_unsafe);
                let _ = check_opt_u64(r_lvls, opt_lvls);
                let _ = check_opt_u64(r_params, opt_params);
                let _ = check_opt_u64(r_indices, opt_indices);
                let _ = check_opt_expr_addr(r_typ, opt_typ);
                check_opt_ctor_entries(r_ctors, opt_ctors),
            },
        },
      MutConst.Recr(r) =>
        match claimed {
          RevealMutConstInfo.Recr(opt_k, opt_unsafe, opt_lvls, opt_params,
                                   opt_indices, opt_motives, opt_minors,
                                   opt_typ, opt_rules) =>
            match r {
              Recursor.Mk(r_k, r_unsafe, r_lvls, r_params, r_indices,
                           r_motives, r_minors, r_typ, r_rules) =>
                let _ = check_opt_bool(r_k, opt_k);
                let _ = check_opt_bool(r_unsafe, opt_unsafe);
                let _ = check_opt_u64(r_lvls, opt_lvls);
                let _ = check_opt_u64(r_params, opt_params);
                let _ = check_opt_u64(r_indices, opt_indices);
                let _ = check_opt_u64(r_motives, opt_motives);
                let _ = check_opt_u64(r_minors, opt_minors);
                let _ = check_opt_expr_addr(r_typ, opt_typ);
                check_opt_recr_rules(r_rules, opt_rules),
            },
        },
    }
  }

  fn check_muts_components(real: List‹MutConst›,
                           claimed: List‹(U64, RevealMutConstInfo)›) {
    match load(claimed) {
      ListNode.Nil => (),
      ListNode.Cons(entry, rest_claimed) =>
        match entry {
          (idx, info) =>
            let real_mc = list_lookup_u64(real, idx);
            let _ = check_mut_const(real_mc, info);
            check_muts_components(real, rest_claimed),
        },
    }
  }

  -- ============================================================================
  -- Merkle leaf / node hash (Ix.Merkle.leafHash / nodeHash).
  -- ============================================================================
  fn leaf_hash(addr: Addr) -> Addr {
    let tail = put_address(addr, store(ListNode.Nil));
    let bytes = store(ListNode.Cons(0u8, tail));
    bytes_to_addr(bytes)
  }

  fn node_hash(l: Addr, r: Addr) -> Addr {
    let tail = put_address(l, put_address(r, store(ListNode.Nil)));
    let bytes = store(ListNode.Cons(1u8, tail));
    bytes_to_addr(bytes)
  }

  -- ============================================================================
  -- Assumption-tree parser / loader. Same as constants: load bytes,
  -- recompute root via merkle fold, assert match.
  -- ============================================================================
  fn parse_atree_body(stream: ByteStream) -> (Addr, List‹Addr›, ByteStream) {
    let (tag, s) = read_byte(stream);
    match tag {
      0 =>
        let (addr, s2) = get_address(s);
        let h = leaf_hash(addr);
        (h, store(ListNode.Cons(addr, store(ListNode.Nil))), s2),
      1 =>
        (store([0u8; 32]), store(ListNode.Nil), s),
      2 =>
        let (lh, ll, s2) = parse_atree_body(s);
        let (rh, rl, s3) = parse_atree_body(s2);
        let h = node_hash(lh, rh);
        (h, list_concat(ll, rl), s3),
    }
  }

  fn load_assumption_tree(root: Addr) -> List‹Addr› {
    let raw = load(root);
    let (idx, len) = io_get_info(1, raw);
    let bytes = #read_byte_stream(1, idx, len);
    let (tag, s) = get_tag4(bytes);
    let (flag, size) = tag;
    assert_eq!(flag, 0xE);
    assert_eq!(to_field(size[0]), 2);
    let (computed_root, leaves, rest) = parse_atree_body(s);
    assert_eq!(load(rest), ListNode.Nil);
    let computed_arr = load(computed_root);
    assert_eq!(computed_arr, raw);
    leaves
  }

  fn addr_in_list(target: Addr, xs: List‹Addr›) -> G {
    match load(xs) {
      ListNode.Nil => 0,
      ListNode.Cons(a, rest) =>
        match address_eq(target, a) {
          1 => 1,
          _ => addr_in_list(target, rest),
        },
    }
  }

  -- Pack the first 4 address bytes (LE) into a u32 key for the skip-set rbtree.
  --
  -- Capped at 4 bytes because `RBTreeMap` orders keys with `u32_less_than`, a
  -- 32-bit comparator gadget — a wider key (a single `G` could hold 7 bytes in
  -- Goldilocks) would overflow it and corrupt the tree ordering. A 32-bit key
  -- space means key collisions are possible (~N²/2^33 over N leaves), but they
  -- are harmless: a collision makes `addr_in_set`'s confirming `address_eq`
  -- fail, yielding a false negative (a frontier const gets rechecked) never a
  -- false positive (a wrong skip). See `build_skip_set`.
  fn addr_key(a: Addr) -> G {
    let arr = load(a);
    to_field(arr[0])
      + to_field(arr[1]) * 256
      + to_field(arr[2]) * 65536
      + to_field(arr[3]) * 16777216
  }

  -- Build an O(log N) membership set from the assumption-leaf list, keyed on
  -- `addr_key`. Key collisions overwrite — sound because the only consequence is
  -- a missed skip (a frontier const gets rechecked, never wrongly trusted); the
  -- confirming `address_eq` in `addr_in_set` rules out false positives.
  fn build_skip_set(leaves: List‹Addr›, acc: RBTreeMap‹Addr›) -> RBTreeMap‹Addr› {
    match load(leaves) {
      ListNode.Nil => acc,
      ListNode.Cons(a, rest) =>
        build_skip_set(rest, rbtree_map_insert(addr_key(a), a, acc)),
    }
  }

  -- Membership via one rbtree lookup (cheap u32 key compares) + one confirming
  -- full `address_eq`, replacing the O(N) linear `addr_in_list` scan that
  -- dominated address_eq cost on sharded checks.
  fn addr_in_set(target: Addr, skip_set: RBTreeMap‹Addr›) -> G {
    let found = rbtree_map_lookup_or_default(addr_key(target), skip_set, store([0u8; 32]));
    address_eq(found, target)
  }

  -- ============================================================================
  -- check_all variant that skips positions whose addr is in the
  -- supplied assumption-leaf list.
  -- ============================================================================
  fn check_all_skipping(consts: List‹&KConstantInfo›,
                        top: List‹&KConstantInfo›,
                        addrs: List‹Addr›,
                        asm_leaves: List‹Addr›) {
    let _ = check_canonical_block_sort(top);
    -- Build the skip-set once (O(N log N)) instead of an O(N) linear scan per
    -- checked const.
    let skip_set = build_skip_set(asm_leaves, RBTreeMap.Nil);
    check_all_skipping_iter(consts, top, addrs, skip_set, 0)
  }

  fn check_all_skipping_iter(consts: List‹&KConstantInfo›,
                             top: List‹&KConstantInfo›,
                             addrs: List‹Addr›,
                             skip_set: RBTreeMap‹Addr›,
                             pos: G) {
    match load(consts) {
      ListNode.Nil => (),
      ListNode.Cons(&ci, rest) =>
        let addr = list_lookup(addrs, pos);
        match addr_in_set(addr, skip_set) {
          1 =>
            check_all_skipping_iter(rest, top, addrs, skip_set, pos + 1),
          _ =>
            let _ = check_const(ci, pos, top, addrs);
            check_all_skipping_iter(rest, top, addrs, skip_set, pos + 1),
        },
    }
  }

  -- ============================================================================
  -- Per-variant handlers. Each takes already-parsed claim fields.
  -- ============================================================================
  fn run_check(const_addr: Addr, asm: Option‹Addr›) {
    let (k_consts, addrs) = ingress_with_primitives(const_addr);
    match asm {
      Option.None => check_all(k_consts, k_consts, addrs),
      Option.Some(asm_root) =>
        let asm_leaves = load_assumption_tree(asm_root);
        check_all_skipping(k_consts, k_consts, addrs, asm_leaves),
    }
  }

  fn run_contains(tree_root: Addr, target_addr: Addr) {
    let leaves = load_assumption_tree(tree_root);
    assert_eq!(addr_in_list(target_addr, leaves), 1);
    ()
  }

  -- Ingress the union closure of all env leaves ONCE, then check every
  -- constant in it (skipping assumption leaves) via the same
  -- `check_all_skipping` path `run_check` uses. Structurally a
  -- `run_check` over a closure that happens to be the whole env, so the
  -- soundness rides on that existing pattern; the union order is verified by
  -- the single `check_canonical_block_sort(top)` inside `check_all_skipping`
  -- (a stronger global order than the per-leaf closures it replaces).
  fn run_check_env(env_root: Addr, asm: Option‹Addr›) {
    let env_leaves = load_assumption_tree(env_root);
    let (k_consts, addrs) = ingress_env(env_leaves);
    match asm {
      Option.None => check_all(k_consts, k_consts, addrs),
      Option.Some(asm_root) =>
        let asm_leaves = load_assumption_tree(asm_root);
        check_all_skipping(k_consts, k_consts, addrs, asm_leaves),
    }
  }

  -- Reveal: real constant at `comm` must match the variant of `info`
  -- AND every Some-field's claimed value must equal the real field.
  fn run_reveal(comm_addr: Addr, info: RevealConstantInfo) {
    let c = load_verified_constant(comm_addr);
    match c {
      Constant.Mk(ci, _, _, _) =>
        match ci {
          ConstantInfo.Defn(d) =>
            match info {
              RevealConstantInfo.Defn(opt_kind, opt_safety, opt_lvls,
                                       opt_typ, opt_value) =>
                match d {
                  Definition.Mk(r_kind, r_safety, r_lvls, r_typ, r_value) =>
                    let _ = check_opt_def_kind(r_kind, opt_kind);
                    let _ = check_opt_def_safety(r_safety, opt_safety);
                    let _ = check_opt_u64(r_lvls, opt_lvls);
                    let _ = check_opt_expr_addr(r_typ, opt_typ);
                    check_opt_expr_addr(r_value, opt_value),
                },
            },
          ConstantInfo.Recr(r) =>
            match info {
              RevealConstantInfo.Recr(opt_k, opt_unsafe, opt_lvls, opt_params,
                                       opt_indices, opt_motives, opt_minors,
                                       opt_typ, opt_rules) =>
                match r {
                  Recursor.Mk(r_k, r_unsafe, r_lvls, r_params, r_indices,
                               r_motives, r_minors, r_typ, r_rules) =>
                    let _ = check_opt_bool(r_k, opt_k);
                    let _ = check_opt_bool(r_unsafe, opt_unsafe);
                    let _ = check_opt_u64(r_lvls, opt_lvls);
                    let _ = check_opt_u64(r_params, opt_params);
                    let _ = check_opt_u64(r_indices, opt_indices);
                    let _ = check_opt_u64(r_motives, opt_motives);
                    let _ = check_opt_u64(r_minors, opt_minors);
                    let _ = check_opt_expr_addr(r_typ, opt_typ);
                    check_opt_recr_rules(r_rules, opt_rules),
                },
            },
          ConstantInfo.Axio(a) =>
            match info {
              RevealConstantInfo.Axio(opt_unsafe, opt_lvls, opt_typ) =>
                match a {
                  Axiom.Mk(r_unsafe, r_lvls, r_typ) =>
                    let _ = check_opt_bool(r_unsafe, opt_unsafe);
                    let _ = check_opt_u64(r_lvls, opt_lvls);
                    check_opt_expr_addr(r_typ, opt_typ),
                },
            },
          ConstantInfo.Quot(q) =>
            match info {
              RevealConstantInfo.Quot(opt_kind, opt_lvls, opt_typ) =>
                match q {
                  Quotient.Mk(r_kind, r_lvls, r_typ) =>
                    let _ = check_opt_quot_kind(r_kind, opt_kind);
                    let _ = check_opt_u64(r_lvls, opt_lvls);
                    check_opt_expr_addr(r_typ, opt_typ),
                },
            },
          ConstantInfo.CPrj(p) =>
            match info {
              RevealConstantInfo.CPrj(opt_idx, opt_cidx, opt_block) =>
                match p {
                  ConstructorProj.Mk(r_idx, r_cidx, r_block) =>
                    let _ = check_opt_u64(r_idx, opt_idx);
                    let _ = check_opt_u64(r_cidx, opt_cidx);
                    check_opt_addr(r_block, opt_block),
                },
            },
          ConstantInfo.RPrj(p) =>
            match info {
              RevealConstantInfo.RPrj(opt_idx, opt_block) =>
                match p {
                  RecursorProj.Mk(r_idx, r_block) =>
                    let _ = check_opt_u64(r_idx, opt_idx);
                    check_opt_addr(r_block, opt_block),
                },
            },
          ConstantInfo.IPrj(p) =>
            match info {
              RevealConstantInfo.IPrj(opt_idx, opt_block) =>
                match p {
                  InductiveProj.Mk(r_idx, r_block) =>
                    let _ = check_opt_u64(r_idx, opt_idx);
                    check_opt_addr(r_block, opt_block),
                },
            },
          ConstantInfo.DPrj(p) =>
            match info {
              RevealConstantInfo.DPrj(opt_idx, opt_block) =>
                match p {
                  DefinitionProj.Mk(r_idx, r_block) =>
                    let _ = check_opt_u64(r_idx, opt_idx);
                    check_opt_addr(r_block, opt_block),
                },
            },
          ConstantInfo.Muts(real_mc_list) =>
            match info {
              RevealConstantInfo.Muts(claimed_components) =>
                check_muts_components(real_mc_list, claimed_components),
            },
        },
    }
  }

  fn run_eval(input: Addr, output: Addr, asm: Option‹Addr›) {
    -- Eval semantics undefined upstream; placeholder until Rust kernel
    -- pins them.
    assert_eq!(0, 1);
    ()
  }

  -- ============================================================================
  -- Top-level entrypoint.
  -- ============================================================================
  --
  -- Public input: 32-G blake3 digest of `Claim.ser claim`. Flow
  -- mirrors `load_verified_constant`: hash-verified bytes deserialize
  -- into a typed `Claim`, then dispatch.
  pub fn verify_claim(claim_digest: [U8; 32]) {
    let claim = load_verified_claim(claim_digest);
    match claim {
      Claim.Eval(input, output, asm) => run_eval(input, output, asm),
      Claim.Check(c, asm) => run_check(c, asm),
      Claim.CheckEnv(root, asm) => run_check_env(root, asm),
      Claim.Reveal(comm, info) => run_reveal(comm, info),
      Claim.Contains(tree, target) => run_contains(tree, target),
    }
  }

  -- ============================================================================
  -- verify_const: subject-only typecheck entrypoint. Checks the
  -- constant at `target_addr` in isolation; transitive deps are
  -- trusted (not re-verified). NOT a claim path — the public
  -- `verify_claim` is the only entrypoint that goes through the
  -- claim-digest discipline. Used by the in-Lean arena test runner
  -- (`Tests/Ix/Kernel/Arena.lean::arenaTests`) where each fixture
  -- is a self-contained decl whose own well-typedness is the only
  -- thing the test cares about.
  -- ============================================================================
  pub fn verify_const(target_addr: [U8; 32]) {
    let target = store(target_addr);
    let (k_consts, addrs) = ingress_with_primitives(target);
    let target_pos = find_addr_idx(target, addrs, 0);
    let ci = load(list_lookup(k_consts, target_pos));
    check_const(ci, target_pos, k_consts, addrs)
  }
⟧

end IxVM

end
