module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel.Klimbs

set_option maxRecDepth 8192

public section

namespace IxVM

/-! ## Nat primitive dispatch

Nat/Str/BitVec/decidable reduction, mirroring
crates/kernel/src/primitive.rs. Recognizes Const-headed applications of
Nat.succ / Nat.pred / Nat.add / Nat.sub / Nat.mul / Nat.div / Nat.mod /
Nat.pow / Nat.gcd / Nat.land / Nat.lor / Nat.xor / Nat.shl / Nat.shr /
Nat.beq / Nat.ble on Nat literals (or on Nat.zero / App(Nat.succ, ...)
ctor chains) and reduces them to a Nat or Bool literal via the
`klimbs_*` bignum ops.

Recognition of a role (`Nat` and its operations, `Bool`, the literal support)
is by the claim's role binding (`role_is`, `role_addr`, `Ix/IxVM/Kernel/Roles.lean`):
a constant is `Nat.add` because the binding binds it to that role and the role
validated against its specification, never because of its address. The same
holds for the `Int`, `BitVec`, `String` and decision rules: each fires on a
role specified by its equations (`Spec.eqns`), and computes an instance of
them. No address is hardcoded.

Beyond literal-on-literal folding, the dispatch also produces "stuck
compact forms" for symbolic bases (`Nat.add x 3`, `x / n`): reducing
those to successor towers or unfolding the division algorithm is what
makes naive Nat reduction explode, so they are kept in offset form and
compared structurally instead.
-/

set_option maxRecDepth 16384 in
def natPrim := ⟦

  -- Nothing reduces natively. `Lean.reduceBool` and `Lean.reduceNat` are
  -- ordinary opaques that never reduce (and a claim that uses them depends on
  -- `Lean.trustCompiler`, which the axiom policy declines);
  -- `System.Platform.numBits` stays the value of the opaque `getNumBits ()`,
  -- as in Lean's kernel; and `SizeOf.sizeOf` (with the `PUnit` instance's
  -- `PUnit._sizeOf_1`) reduces through its definition.

  -- Bool value (0/1) → Const(Bool.false/Bool.true).
  fn mk_bool(rc: RoleCtx, g: G) -> KExpr {
    match g {
      0 => store(KExprNode.Const(role_addr(rc, role_bool_false()), store(ListNode.Nil))),
      _ => store(KExprNode.Const(role_addr(rc, role_bool_true()), store(ListNode.Nil))),
    }
  }

  -- Compute BitVec.toNat internally: given (width_e, val_e), returns
  -- (1, N mod 2^W) as KLimbs. (0, _) on miss.
  fn bv_to_nat_via(rc: RoleCtx, width_e: KExpr, val_e: KExpr) -> (G, KLimbs) {
    match bitvec_of_nat_args_direct(rc, val_e) {
      (0, _, _) => (0, store(ListNode.Nil)),
      (1, val_width, n_e) =>
        match try_extract_nat(rc, n_e) {
          (0, _) => (0, store(ListNode.Nil)),
          (1, n_kl) =>
            match try_extract_nat(rc, val_width) {
              (0, _) => (0, store(ListNode.Nil)),
              (1, w_kl) =>
                let two = store(ListNode.Cons(
                  [2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
                  store(ListNode.Nil)));
                let modulus = klimbs_pow(two, w_kl);
                (1, klimbs_normalize(klimbs_mod(n_kl, modulus))),
            },
        },
    }
  }

  -- BitVec.ult width lhs rhs → mk_bool(rc, lhs_nat < rhs_nat)
  fn try_reduce_bit_vec_ult(rc: RoleCtx, spine: List‹KExpr›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 3) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        let width_e = list_lookup(spine, 0);
        let lhs_e = list_lookup(spine, 1);
        let rhs_e = list_lookup(spine, 2);
        match bv_to_nat_via(rc, width_e, lhs_e) {
          (0, _) => (0, store(KExprNode.BVar(0))),
          (1, lhs_n) =>
            match bv_to_nat_via(rc, width_e, rhs_e) {
              (0, _) => (0, store(KExprNode.BVar(0))),
              (1, rhs_n) =>
                -- lhs < rhs iff !(rhs ≤ lhs)
                let r = 1 - klimbs_le(rhs_n, lhs_n);
                (1, mk_bool(rc, r)),
            },
        },
    }
  }

  -- Extract (width, value) from `BitVec.ofNat W N` shape. Returns
  -- (1, W, N) or (0, _, _). Direct form only: the `OfNat.ofNat`-wrapped
  -- form is not recognized here, so a wrapped literal stays stuck rather
  -- than folding.
  fn bitvec_of_nat_args_direct(rc: RoleCtx, e: KExpr) -> (G, KExpr, KExpr) {
    match collect_spine(e) {
      (head, args) =>
        match load(head) {
          KExprNode.Const(caddr, _) =>
            match role_is(rc, caddr, role_bit_vec_of_nat()) {
              1 =>
                match list_length(args) - 2 {
                  0 => (1, list_lookup(args, 0), list_lookup(args, 1)),
                  _ => (0, store(KExprNode.BVar(0)), store(KExprNode.BVar(0))),
                },
              _ => (0, store(KExprNode.BVar(0)), store(KExprNode.BVar(0))),
            },
          _ => (0, store(KExprNode.BVar(0)), store(KExprNode.BVar(0))),
        },
    }
  }

  -- BitVec.toNat / BitVec.ult dispatch: both heads are functions, and the
  -- spine is prepared (whnf inner (W, N) args first). The class methods
  -- `OfNat.ofNat (BitVec w) n inst` and `decide (@LT.lt (BitVec w) inst x
  -- y)` take their value from the instance, so neither is read here.
  fn try_bitvec_dispatch(rc: RoleCtx, head_addr: Addr, spine: List‹KExpr›,
                              types: List‹KExpr›) -> (G, KExpr) {
    match role_is(rc, head_addr, role_bit_vec_to_nat()) {
      1 =>
        match u32_less_than(list_length(spine), 2) {
          1 => (0, store(KExprNode.BVar(0))),
          _ =>
            let spine_p = bitvec_prep_spine(rc, spine, types);
            let width_e = list_lookup(spine_p, 0);
            let val_e = list_lookup(spine_p, 1);
            match bv_to_nat_via(rc, width_e, val_e) {
              (0, _) => (0, store(KExprNode.BVar(0))),
              (1, kl) => (1, mk_nat_lit(kl)),
            },
        },
      _ =>
        match role_is(rc, head_addr, role_bit_vec_ult()) {
          1 =>
            let spine_p = bitvec_prep_spine_ult(rc, spine, types);
            try_reduce_bit_vec_ult(rc, spine_p),
          _ => (0, store(KExprNode.BVar(0))),
        },
    }
  }

  -- BitVec.ult prep: whnf [width, lhs, rhs] and recursively whnf each
  -- BitVec.ofNat inner args, mirror bitvec_prep_spine (toNat) shape.
  fn bitvec_prep_spine_ult(rc: RoleCtx, spine: List‹KExpr›, types: List‹KExpr›)
                                -> List‹KExpr› {
    let sw = whnf_spine(rc, spine, types);
    match load(sw) {
      ListNode.Nil => sw,
      ListNode.Cons(width_e, r1) =>
        match load(r1) {
          ListNode.Nil => sw,
          ListNode.Cons(lhs_e, r2) =>
            match load(r2) {
              ListNode.Nil => sw,
              ListNode.Cons(rhs_e, tail) =>
                let lhs_p = np_whnf_inner_bv(rc, lhs_e, types);
                let rhs_p = np_whnf_inner_bv(rc, rhs_e, types);
                store(ListNode.Cons(width_e,
                  store(ListNode.Cons(lhs_p,
                    store(ListNode.Cons(rhs_p, tail)))))),
            },
        },
    }
  }

  -- If e = App*(head, args), whnf each arg once.
  fn np_whnf_inner_bv(rc: RoleCtx, e: KExpr, types: List‹KExpr›) -> KExpr {
    match collect_spine(e) {
      (h, a) => apply_spine(h, whnf_spine(rc, a, types)),
    }
  }

  -- Native string-value fast paths (mirror crates/kernel/src/primitive.rs
  -- `string_append` / `string_dec_eq`): literal append and literal
  -- decidable equality reduce natively in whnf, keeping evaluator-grade
  -- string values out of the structural ByteArray/UTF-8 model.

  -- String primitive dispatch. Handles:
  -- - String.utf8ByteSize (Lit(Str))          -> Lit(Nat len)
  -- - String.append (Lit(Str), Lit(Str))      -> Lit(Str concat)
  -- - String.ofList / String.mk (char-list)   -> Lit(Str) via UTF-8 fold
  -- Caller pre-whnfs spine's outermost args; the ofList arm recursively
  -- whnfs Cons tails to reach further literal-ctor nodes.
  fn try_str_dispatch(rc: RoleCtx, head_addr: Addr, spine: List‹KExpr›,
                          types: List‹KExpr›) -> (G, KExpr) {
    let spine_len = list_length(spine);
    match role_is(rc, head_addr, role_string_of_list()) {
      1 =>
        match spine_len {
          1 =>
            match walk_char_list_bytes(rc, list_lookup(spine, 0), types) {
              (1, bs) => (1, store(KExprNode.Lit(KLiteral.Str(bs)))),
              (0, _) => (0, store(KExprNode.BVar(0))),
            },
          _ => (0, store(KExprNode.BVar(0))),
        },
      _ =>
    match role_is(rc, head_addr, role_string_utf8_byte_size()) {
      1 =>
        match u32_less_than(spine_len, 1) {
          1 => (0, store(KExprNode.BVar(0))),
          _ =>
            let a0 = list_lookup(spine, 0);
            match load(a0) {
              KExprNode.Lit(lit) =>
                match lit {
                  KLiteral.Str(bs) =>
                    -- `klimbs_from_g` range-checks its byte decomposition
                    -- (so a length >= 256 lands in the right limb) and
                    -- returns a canonical `KLimbs` — required because
                    -- `klimbs_eq` (behind `Nat.beq`/`Nat.decEq`/
                    -- `literal_eq`) compares limbs without normalizing.
                    let limbs = klimbs_from_g(list_length(bs));
                    (1, store(KExprNode.Lit(KLiteral.Nat(limbs)))),
                  _ => (0, store(KExprNode.BVar(0))),
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
        },
      _ =>
    match role_is(rc, head_addr, role_string_back()) {
      1 => try_str_back(rc, spine),
      _ =>
    match role_is(rc, head_addr, role_string_to_byte_array()) {
      1 => try_str_to_byte_array(rc, spine),
      _ =>
    match role_is(rc, head_addr, role_string_dec_eq()) {
      1 => try_str_dec_eq(rc, head_addr, spine, types),
      _ =>
        match role_is(rc, head_addr, role_string_append()) {
          1 =>
            match u32_less_than(spine_len, 2) {
              1 => (0, store(KExprNode.BVar(0))),
              _ =>
                let a0 = list_lookup(spine, 0);
                let a1 = list_lookup(spine, 1);
                match load(a0) {
                  KExprNode.Lit(la) =>
                    match la {
                      KLiteral.Str(sa) =>
                        match load(a1) {
                          KExprNode.Lit(lb) =>
                            match lb {
                              KLiteral.Str(sb) =>
                                let joined = list_concat(sa, sb);
                                (1, store(KExprNode.Lit(KLiteral.Str(joined)))),
                              _ => (0, store(KExprNode.BVar(0))),
                            },
                          _ => (0, store(KExprNode.BVar(0))),
                        },
                      _ => (0, store(KExprNode.BVar(0))),
                    },
                  _ => (0, store(KExprNode.BVar(0))),
                },
            },
          _ => (0, store(KExprNode.BVar(0))),
        },
    },
    },
    },
    },
    }
  }

  -- String.back over Lit(Str(bs)) →
  -- App(Const(char_of_nat), Lit(Nat last_cp)). Empty bs → 65 ('A').
  fn try_str_back(rc: RoleCtx, spine: List‹KExpr›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 1) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        match load(list_lookup(spine, 0)) {
          KExprNode.Lit(lit) =>
            match lit {
              KLiteral.Str(bs) =>
                let cp = utf8_last_codepoint(bs);
                let cp_limbs = klimbs_from_g(cp);
                let cp_lit = store(KExprNode.Lit(KLiteral.Nat(cp_limbs)));
                let con = store(KExprNode.Const(role_addr(rc, role_char_of_nat()),
                                                 store(ListNode.Nil)));
                (1, store(KExprNode.App(con, cp_lit))),
              _ => (0, store(KExprNode.BVar(0))),
            },
          _ => (0, store(KExprNode.BVar(0))),
        },
    }
  }

  -- String.toByteArray on Lit(Str "")  →  Const(byte_array_empty).
  -- Non-empty bails to structural (caller falls back to Defn unfold).
  fn try_str_to_byte_array(rc: RoleCtx, spine: List‹KExpr›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 1) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        match load(list_lookup(spine, 0)) {
          KExprNode.Lit(lit) =>
            match lit {
              KLiteral.Str(bs) =>
                match load(bs) {
                  ListNode.Nil =>
                    (1, store(KExprNode.Const(role_used_implicitly(rc, role_byte_array_empty()),
                                                store(ListNode.Nil)))),
                  _ => (0, store(KExprNode.BVar(0))),
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
          _ => (0, store(KExprNode.BVar(0))),
        },
    }
  }

  -- Walk byte stream forward decoding UTF-8; return last codepoint.
  -- Empty → 65 ('A') per Rust default.
  -- Validate an entire byte stream as UTF-8, aborting on the first
  -- malformed scalar. `utf8_decode_one` rejects out-of-range
  -- continuation bytes, stray continuations as leaders, overlong forms,
  -- surrogates and code points above 0x10FFFF, so walking the stream with
  -- it is exactly the reference kernels' `String::from_utf8` check at
  -- ingress: the accepted literals are the encodings of Lean strings.
  --
  -- Needed at Str-literal CONVERSION, not just during string reduction:
  -- `KLiteral.Str` is typed `String` by `k_infer_lit` without inspecting
  -- the bytes, so a literal that is never decoded would otherwise
  -- typecheck as a `String` that no Lean `String` corresponds to.
  fn utf8_validate(bs: ByteStream) {
    match load(bs) {
      ListNode.Nil => (),
      ListNode.Cons(b0, rest) =>
        match utf8_decode_one(b0, rest) {
          (_, remaining) => utf8_validate(remaining),
        },
    }
  }

  fn utf8_last_codepoint(bs: ByteStream) -> G {
    utf8_last_go(bs, 65)
  }

  fn utf8_last_go(bs: ByteStream, prev: G) -> G {
    match load(bs) {
      ListNode.Nil => prev,
      ListNode.Cons(b0, rest) =>
        match utf8_decode_one(b0, rest) {
          (cp, remaining) => utf8_last_go(remaining, cp),
        },
    }
  }

  -- Decode one UTF-8 codepoint. Honors length prefix bits:
  -- 0xxxxxxx → 1 byte; 110xxxxx 10xxxxxx → 2; 1110xxxx 10*2 → 3;
  -- 11110xxx 10*3 → 4 bytes.
  -- A UTF-8 continuation byte is `10xxxxxx`, i.e. in [0x80, 0xC0). Only
  -- that range decodes to a 6-bit payload; matching the two valid-range
  -- outcomes makes any other byte fall off the match and abort (the
  -- kernel's reject). Both bounds are load-bearing for soundness, not
  -- conformance nicety: a byte < 0x80 makes `to_field(b) - 128` wrap to a
  -- ~2^64 field element, and a byte >= 0xC0 makes the payload spill into
  -- [64,128), so e.g. `[0xC0, 0xC0]` would decode to codepoint 64 and
  -- alias the valid char `'@'`.
  fn utf8_cont(b: U8) -> G {
    match u8_less_than(b, 128u8) {
      0 =>
        match u8_less_than(b, 192u8) {
          1 => to_field(b) - 128,
        },
    }
  }

  -- Decode one UTF-8 scalar, validating just enough to be INJECTIVE: no
  -- two distinct byte sequences may decode to the same codepoint, or the
  -- expanded `String.ofList` forms alias and def_eq accepts a false string
  -- equality. That requires (a) continuation bytes in range (`utf8_cont`),
  -- and (b) the per-length overlong minimum, so a codepoint that has a
  -- shorter valid encoding cannot also be produced by a longer one. The
  -- reference kernels validate the whole blob as UTF-8 at ingress; this is
  -- the same rejection, done per scalar. It also rejects what is not a
  -- Unicode scalar value: surrogates [0xD800, 0xDFFF] in the three-byte
  -- form, and code points of 0x110000 and above in the four-byte form
  -- (every leader from 0xF5 up gives one). Such a literal corresponds to
  -- no Lean `String`: its `String.ofList` expansion has a `Char.ofNat`
  -- that is `'\0'`, so a native rule that reads the bytes (the byte
  -- length) would disagree with the expansion's definitional value.
  fn utf8_decode_one(b0: U8, rest: ByteStream) -> (G, ByteStream) {
    match u8_less_than(b0, 128u8) {
      1 => (to_field(b0), rest),
      _ =>
        -- Reject stray continuation bytes [0x80, 0xC2) as leaders: [0x80,
        -- 0xC0) are continuations, and 0xC0/0xC1 only ever encode overlong
        -- two-byte forms. Valid multi-byte leaders are >= 0xC2.
        match u8_less_than(b0, 194u8) {
          0 =>
            match u8_less_than(b0, 224u8) {
              1 =>
                match load(rest) {
                  ListNode.Cons(b1, r1) =>
                    -- Two-byte cp is >= 0x80 for every leader >= 0xC2, so
                    -- no overlong is reachable once the leader is gated.
                    let cp = (to_field(b0) - 192) * 64 + utf8_cont(b1);
                    (cp, r1),
                },
              _ =>
                match u8_less_than(b0, 240u8) {
                  1 =>
                    match load(rest) {
                      ListNode.Cons(b1, r1) =>
                        match load(r1) {
                          ListNode.Cons(b2, r2) =>
                            let cp = (to_field(b0) - 224) * 4096
                                   + utf8_cont(b1) * 64
                                   + utf8_cont(b2);
                            -- Overlong: a real three-byte scalar is
                            -- >= 0x800. Reject anything below (e.g.
                            -- [0xE0,0x80,0x80] -> 0, which would alias
                            -- the one-byte NUL).
                            match u32_less_than(cp, 2048) {
                              0 =>
                                -- Surrogates [0xD800, 0xDFFF] are not
                                -- scalar values.
                                match u32_less_than(cp, 55296) {
                                  1 => (cp, r2),
                                  0 =>
                                    match u32_less_than(cp, 57344) {
                                      0 => (cp, r2),
                                    },
                                },
                            },
                        },
                    },
                  _ =>
                    match load(rest) {
                      ListNode.Cons(b1, r1) =>
                        match load(r1) {
                          ListNode.Cons(b2, r2) =>
                            match load(r2) {
                              ListNode.Cons(b3, r3) =>
                                let cp = (to_field(b0) - 240) * 262144
                                       + utf8_cont(b1) * 4096
                                       + utf8_cont(b2) * 64
                                       + utf8_cont(b3);
                                -- Overlong: a real four-byte scalar is
                                -- >= 0x10000.
                                match u32_less_than(cp, 65536) {
                                  0 =>
                                    -- The last scalar value is 0x10FFFF.
                                    match u32_less_than(cp, 1114112) {
                                      1 => (cp, r3),
                                    },
                                },
                            },
                        },
                    },
                },
            },
        },
    }
  }

  -- Mirror of Rust `def_eq.rs::str_lit_to_constructor`. Expands
  -- Lit(Str(bs)) to ctor form
  -- `String.ofList (List.cons.{0} Char (Char.ofNat c) (... List.nil.{0} Char))`
  -- over the binding's roles. The claim references none of these
  -- constants, so each is a dependency it checks (`role_used_implicitly`).
  fn str_lit_to_ctor(rc: RoleCtx, bs: ByteStream) -> KExpr {
    let zero_lvl = store(KLevelNode.Zero);
    let ulvls = store(ListNode.Cons(zero_lvl, store(ListNode.Nil)));
    let nil_const = store(KExprNode.Const(role_used_implicitly(rc, role_list_nil()), ulvls));
    let cons_const = store(KExprNode.Const(role_used_implicitly(rc, role_list_cons()), ulvls));
    let char_const =
      store(KExprNode.Const(role_used_implicitly(rc, role_char()), store(ListNode.Nil)));
    let con_const =
      store(KExprNode.Const(role_used_implicitly(rc, role_char_of_nat()), store(ListNode.Nil)));
    let str_const =
      store(KExprNode.Const(role_used_implicitly(rc, role_string_of_list()), store(ListNode.Nil)));
    let nil_app = store(KExprNode.App(nil_const, char_const));
    let cons_partial = store(KExprNode.App(cons_const, char_const));
    let list_expr = build_char_list(bs, nil_app, cons_partial, con_const);
    store(KExprNode.App(str_const, list_expr))
  }

  fn build_char_list(bs: ByteStream, nil_app: KExpr,
                         cons_partial: KExpr, con_const: KExpr) -> KExpr {
    match load(bs) {
      ListNode.Nil => nil_app,
      ListNode.Cons(b0, rest) =>
        match utf8_decode_one(b0, rest) {
          (cp, remaining) =>
            let cp_limbs = klimbs_from_g(cp);
            let cp_lit = store(KExprNode.Lit(KLiteral.Nat(cp_limbs)));
            let char_val = store(KExprNode.App(con_const, cp_lit));
            let with_head = store(KExprNode.App(cons_partial, char_val));
            let tail = build_char_list(remaining, nil_app, cons_partial, con_const);
            store(KExprNode.App(with_head, tail)),
        },
    }
  }

  -- Mirror str_lit_delta_step (Primitive.lean:3074): take ONE delta
  -- step past `String.ofList` when it is a Defn, settling the body with
  -- whnf_nd — a plain whnf of the ofList application would fold straight
  -- back into the Str literal via the native ofList collapse.
  fn str_lit_delta_step(rc: RoleCtx, expanded: KExpr, types: List‹KExpr›) -> KExpr {
    match load(expanded) {
      KExprNode.App(f, list_arg) =>
        match load(f) {
          KExprNode.Const(caddr, _) =>
            let ci = load(get_ci(caddr));
            match ci {
              KConstantInfo.Defn(_, _, value, _, _) =>
                let body = expr_inst_levels(value, store(ListNode.Nil));
                match load(body) {
                  KExprNode.Lam(_, lam_body) =>
                    whnf_nd(rc, expr_inst1(lam_body, list_arg, 0), types),
                  _ => whnf_nd(rc, store(KExprNode.App(body, list_arg)), types),
                },
              _ => expanded,
            },
          _ => expanded,
        },
      _ => expanded,
    }
  }

  -- Lit(Str) → ctor form with the delta step; other exprs unchanged.
  -- Mirror str_lit_to_ctor_app_or_self (Primitive.lean:3099).
  fn str_lit_to_ctor_app_or_self(rc: RoleCtx, e: KExpr, types: List‹KExpr›) -> KExpr {
    match load(e) {
      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Str(bs) => str_lit_delta_step(rc, str_lit_to_ctor(rc, bs), types),
          _ => e,
        },
      _ => e,
    }
  }

  -- G (< 2^32) → single-limb KLimbs via prover-provided 4-byte split.
  -- Pinned by u8 range checks + reconstruction assert. `x >= 2^32`
  -- rejected (assert fails), not silently truncated.
  fn split_u32(x: G) -> (G, G, G, G) {
    match divmod_256(x, 0) {
      (b0, q1) =>
        match divmod_256(q1, 0) {
          (b1, q2) =>
            match divmod_256(q2, 0) {
              (b2, q3) =>
                match divmod_256(q3, 0) {
                  (b3, _) => (b0, b1, b2, b3),
                },
            },
        },
    }
  }

  -- Convert G value (< 2^32) into single-limb KLimbs. The 4-byte
  -- decomposition is a prover-provided (unconstrained) witness, pinned by
  -- four u8 range checks + the reconstruction assert. `x >= 2^32` is
  -- rejected (assert fails) rather than silently truncated.
  fn klimbs_from_g(x: G) -> KLimbs {
    match #split_u32(x) {
      (rb0, rb1, rb2, rb3) =>
        let b0 = u8_xor(u8_from_field_unsafe(rb0), 0u8);
        let b1 = u8_xor(u8_from_field_unsafe(rb1), 0u8);
        let b2 = u8_xor(u8_from_field_unsafe(rb2), 0u8);
        let b3 = u8_xor(u8_from_field_unsafe(rb3), 0u8);
        -- Pins the unconstrained byte-split hint: the four witnessed
        -- bytes must recompose to exactly the field element they claim
        -- to decompose.
        assert_eq!(x, to_field(b0) + 256 * to_field(b1)
                   + 65536 * to_field(b2) + 16777216 * to_field(b3),
          "u32 byte split does not recompose to the original value");
        -- Normalize HERE, not at each caller: `x == 0` gives the all-zero
        -- limb, which is the denormalized `[[0;8]]`. `klimbs_eq` (behind
        -- `Nat.beq`/`decEq`) compares limbs without normalizing, so an
        -- unnormalized zero disagrees with the canonical empty list and
        -- makes a reducer's literal wrong. Callers used to normalize
        -- individually and one (`String.back`) was missed.
        klimbs_normalize(store(ListNode.Cons(
          [b0, b1, b2, b3, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)))),
    }
  }

  -- Mirror walk_char_list_bytes: whnf `list`, expect a fully applied
  -- `List.nil` (1 lvl arg) or `List.cons` (1 lvl + head + tail).
  -- Returns (0, _) on any non-literal-ctor node, wrong arity, or invalid
  -- codepoint — caller falls back to structural.
  fn walk_char_list_bytes(rc: RoleCtx, list: KExpr, types: List‹KExpr›)
                              -> (G, ByteStream) {
    let w = whnf(rc, list, types);
    match collect_spine(w) {
      (head, args) =>
        match load(head) {
          KExprNode.Const(caddr, _) =>
            match role_is(rc, caddr, role_list_nil()) {
              1 =>
                match list_length(args) {
                  1 => (1, store(ListNode.Nil)),
                  _ => (0, store(ListNode.Nil)),
                },
              _ =>
                match role_is(rc, caddr, role_list_cons()) {
                  0 => (0, store(ListNode.Nil)),
                  _ =>
                    match list_length(args) {
                      3 =>
                        match char_lit_codepoint(rc, list_lookup(args, 1), types) {
                          (0, _) => (0, store(ListNode.Nil)),
                          (1, cp) =>
                            match walk_char_list_bytes(rc, list_lookup(args, 2), types) {
                              (0, t) => (0, t),
                              (1, t) => (1, utf8_encode_prepend(cp, t)),
                            },
                        },
                      _ => (0, store(ListNode.Nil)),
                    },
                },
            },
          _ => (0, store(ListNode.Nil)),
        },
    }
  }

  -- Recognize App(Const(Char.ofNat), Nat-lit). Retry once through whnf
  -- when the syntactic match misses (mirror char_lit_value +
  -- whnf_prim_arg).
  fn char_lit_codepoint(rc: RoleCtx, e: KExpr, types: List‹KExpr›) -> (G, G) {
    match char_lit_codepoint_syn(rc, e) {
      (1, cp) => (1, cp),
      _ =>
        let w = whnf(rc, e, types);
        char_lit_codepoint_syn(rc, w),
    }
  }

  fn char_lit_codepoint_syn(rc: RoleCtx, e: KExpr) -> (G, G) {
    match load(e) {
      KExprNode.App(f, arg) =>
        match load(f) {
          KExprNode.Const(caddr, _) =>
            match role_is(rc, caddr, role_char_of_nat()) {
              0 => (0, 0),
              _ =>
                match load(arg) {
                  KExprNode.Lit(lit) =>
                    match lit {
                      KLiteral.Nat(limbs) => klimbs_scalar_value(limbs),
                      _ => (0, 0),
                    },
                  _ => (0, 0),
                },
            },
          _ => (0, 0),
        },
      _ => (0, 0),
    }
  }

  -- Single-limb KLimbs → codepoint; multi-limb literals bail. Guards
  -- to valid Unicode scalars (rejects surrogates 0xD800-0xDFFF and
  -- codepoints ≥ 0x110000).
  fn klimbs_scalar_value(limbs: KLimbs) -> (G, G) {
    match load(limbs) {
      ListNode.Cons(limb, rest) =>
        match load(rest) {
          ListNode.Nil =>
            let [b0, b1, b2, b3, b4, b5, b6, b7] = limb;
            let hi = to_field(b3) + to_field(b4) + to_field(b5) + to_field(b6) + to_field(b7);
            match eq_zero(hi) {
              0 => (0, 0),
              _ =>
                let cp = to_field(b0) + to_field(b1) * 256 + to_field(b2) * 65536;
                match u32_less_than(cp, 55296) {
                  1 => (1, cp),
                  _ =>
                    match u32_less_than(57343, cp) {
                      0 => (0, 0),
                      _ =>
                        match u32_less_than(cp, 1114112) {
                          1 => (1, cp),
                          _ => (0, 0),
                        },
                    },
                },
            },
          _ => (0, 0),
        },
      _ => (0, 0),
    }
  }

  -- Off-circuit 6-bit decomposition (repeated subtraction); prover-
  -- provided results MUST be pinned by u8 + window range checks +
  -- reconstruction assert.
  fn divmod_64u(x: G, q: G) -> (G, G) {
    match u32_less_than(x, 64) {
      1 => (x, q),
      _ => divmod_64u(x - 64, q + 1),
    }
  }

  fn utf8_groups(cp: G) -> (G, G, G, G) {
    match divmod_64u(cp, 0) {
      (g0, q1) =>
        match divmod_64u(q1, 0) {
          (g1, q2) =>
            match divmod_64u(q2, 0) {
              (g2, g3) => (g0, g1, g2, g3),
            },
        },
    }
  }

  -- Constrained UTF-8 encode of a valid scalar `cp`, prepended to `tail`.
  -- Length class chosen by u32_less_than compares on `cp` (already valid
  -- per caller — no overlong branch).
  fn utf8_encode_prepend(cp: G, tail: ByteStream) -> ByteStream {
    match #utf8_groups(cp) {
      (g0, g1, g2, g3) =>
        let g0u = u8_xor(u8_from_field_unsafe(g0), 0u8);
        let g1u = u8_xor(u8_from_field_unsafe(g1), 0u8);
        let g2u = u8_xor(u8_from_field_unsafe(g2), 0u8);
        let g3u = u8_xor(u8_from_field_unsafe(g3), 0u8);
        let f0 = to_field(g0u);
        let f1 = to_field(g1u);
        let f2 = to_field(g2u);
        let f3 = to_field(g3u);
        -- Pins the unconstrained UTF-8 group hint: each group is a
        -- 6-bit value and together they recompose to the codepoint.
        assert_eq!(u32_less_than(f0, 64), 1,
          "utf8 group 0 is not a 6-bit value");
        assert_eq!(u32_less_than(f1, 64), 1,
          "utf8 group 1 is not a 6-bit value");
        assert_eq!(u32_less_than(f2, 64), 1,
          "utf8 group 2 is not a 6-bit value");
        assert_eq!(u32_less_than(f3, 64), 1,
          "utf8 group 3 is not a 6-bit value");
        assert_eq!(cp, f0 + f1 * 64 + f2 * 4096 + f3 * 262144,
          "utf8 groups do not recompose to the codepoint");
        match u32_less_than(cp, 128) {
          1 => store(ListNode.Cons(u8_from_field_unsafe(cp), tail)),
          _ =>
            match u32_less_than(cp, 2048) {
              1 =>
                let t1 = u8_from_field_unsafe(f0 + 128);
                let l1 = u8_from_field_unsafe(f1 + 192);
                store(ListNode.Cons(l1, store(ListNode.Cons(t1, tail)))),
              _ =>
                match u32_less_than(cp, 65536) {
                  1 =>
                    let t2 = u8_from_field_unsafe(f0 + 128);
                    let t1 = u8_from_field_unsafe(f1 + 128);
                    let l2 = u8_from_field_unsafe(f2 + 224);
                    store(ListNode.Cons(l2, store(ListNode.Cons(t1, store(ListNode.Cons(t2, tail)))))),
                  _ =>
                    let t3 = u8_from_field_unsafe(f0 + 128);
                    let t2 = u8_from_field_unsafe(f1 + 128);
                    let t1 = u8_from_field_unsafe(f2 + 128);
                    let l3 = u8_from_field_unsafe(f3 + 240);
                    store(ListNode.Cons(l3, store(ListNode.Cons(t1, store(ListNode.Cons(t2, store(ListNode.Cons(t3, tail)))))))),
                },
            },
        },
    }
  }

  -- ============================================================================
  -- Extract Nat literal from KExpr
  -- ============================================================================
  fn try_extract_nat(rc: RoleCtx, e: KExpr) -> (G, KLimbs) {
    match load(e) {
      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Nat(limbs) => (1, limbs),
          _ => (0, store(ListNode.Nil)),
        },
      KExprNode.Const(caddr, _) =>
        match role_is(rc, caddr, role_nat_zero()) {
          1 => (1, store(ListNode.Nil)),
          _ => (0, store(ListNode.Nil)),
        },
      KExprNode.App(f, a) => try_extract_nat_app(rc, f, a),
      _ => (0, store(ListNode.Nil)),
    }
  }

  -- Cold-extracted App arm: list_lookup + address_eq + recursive
  -- try_extract_nat + klimbs_succ is the widest arm; pulling it out lets
  -- `try_extract_nat`'s main width drop to the leaf-arm width.
  fn try_extract_nat_app(rc: RoleCtx, f: KExpr, a: KExpr) -> (G, KLimbs) {
    match load(f) {
      KExprNode.Const(caddr, _) =>
        match role_is(rc, caddr, role_nat_succ()) {
          1 =>
            match try_extract_nat(rc, a) {
              (1, pred_limbs) => (1, klimbs_succ(pred_limbs)),
              _ => (0, store(ListNode.Nil)),
            },
          _ => (0, store(ListNode.Nil)),
        },
      _ => (0, store(ListNode.Nil)),
    }
  }

  fn mk_nat_lit(n: KLimbs) -> KExpr {
    store(KExprNode.Lit(KLiteral.Nat(n)))
  }

  -- Canonical Int literals are `Int.ofNat n` and `Int.negSucc n`.
  -- Internally use (sign, absolute magnitude), with sign=1 negative.
  fn try_extract_int_prim(rc: RoleCtx, e: KExpr) -> (G, G, KLimbs) {
    match load(e) {
      KExprNode.App(f, a) => match load(f) {
        KExprNode.Const(caddr, _) => match try_extract_nat(rc, a) {
          (1, n) => match role_is(rc, caddr, role_int_of_nat()) {
            1 => (1, 0, klimbs_normalize(n)),
            _ => match role_is(rc, caddr, role_int_neg_succ()) {
              1 => (1, 1, klimbs_normalize(klimbs_succ(n))),
              _ => (0, 0, store(ListNode.Nil)),
            },
          },
          _ => (0, 0, store(ListNode.Nil)),
        },
        _ => (0, 0, store(ListNode.Nil)),
      },
      _ => (0, 0, store(ListNode.Nil)),
    }
  }

  fn mk_int_prim(rc: RoleCtx, sign: G, magnitude: KLimbs) -> KExpr {
    let mag = klimbs_normalize(magnitude);
    let neg = sign * (1 - klimbs_is_zero(mag));
    let caddr = match neg {
      0 => role_used_implicitly(rc, role_int_of_nat()),
      _ => role_used_implicitly(rc, role_int_neg_succ()),
    };
    let arg = match neg { 0 => mag, _ => klimbs_normalize(klimbs_dec(mag)), };
    store(KExprNode.App(store(KExprNode.Const(caddr, store(ListNode.Nil))), mk_nat_lit(arg)))
  }

  fn int_add_prim(rc: RoleCtx, sa: G, a: KLimbs, sb: G, b: KLimbs) -> KExpr {
    match sa - sb {
      0 => mk_int_prim(rc, sa, klimbs_add(a, b)),
      _ => match klimbs_le(a, b) {
        1 => mk_int_prim(rc, sb, klimbs_sub(b, a)),
        _ => mk_int_prim(rc, sa, klimbs_sub(a, b)),
      },
    }
  }

  -- Euclidean quotient/remainder for signed a,b. Remainder is always
  -- nonnegative and smaller than |b| (unless b=0, where r=a and q=0).
  fn int_emod_prim(rc: RoleCtx, sa: G, a: KLimbs, b: KLimbs) -> KExpr {
    match klimbs_is_zero(b) {
      1 => mk_int_prim(rc, sa, a),
      _ =>
        let r0 = klimbs_mod(a, b);
        match sa * (1 - klimbs_is_zero(r0)) {
          1 => mk_int_prim(rc, 0, klimbs_sub(b, r0)),
          _ => mk_int_prim(rc, 0, r0),
        },
    }
  }

  fn int_ediv_prim(rc: RoleCtx, sa: G, a: KLimbs, sb: G, b: KLimbs) -> KExpr {
    match klimbs_is_zero(b) {
      1 => mk_int_prim(rc, 0, store(ListNode.Nil)),
      _ =>
        let q0 = klimbs_div(a, b);
        let r0 = klimbs_mod(a, b);
        let q = match sa * (1 - klimbs_is_zero(r0)) {
          1 => klimbs_succ(q0),
          _ => q0,
        };
        mk_int_prim(rc, (sa + sb - 2 * sa * sb) * (1 - klimbs_is_zero(q)), q),
    }
  }

  fn int_bmod_prim(rc: RoleCtx, sa: G, a: KLimbs, m: KLimbs) -> KExpr {
    match klimbs_is_zero(m) {
      1 => mk_int_prim(rc, sa, a),
      _ =>
        let r0 = klimbs_mod(a, m);
        let r = match sa * (1 - klimbs_is_zero(r0)) {
          1 => klimbs_sub(m, r0),
          _ => r0,
        };
        let two = store(ListNode.Cons([2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
        let half = klimbs_div(klimbs_succ(m), two);
        match klimbs_le(half, r) {
          1 => mk_int_prim(rc, 1, klimbs_sub(m, r)),
          _ => mk_int_prim(rc, 0, r),
        },
    }
  }

  fn int_bdiv_prim(rc: RoleCtx, sa: G, a: KLimbs, m: KLimbs) -> KExpr {
    match klimbs_is_zero(m) {
      1 => mk_int_prim(rc, 0, store(ListNode.Nil)),
      _ =>
        let r0 = klimbs_mod(a, m);
        let r = match sa * (1 - klimbs_is_zero(r0)) {
          1 => klimbs_sub(m, r0),
          _ => r0,
        };
        let q0 = klimbs_div(a, m);
        let qmag = match sa * (1 - klimbs_is_zero(r0)) { 1 => klimbs_succ(q0), _ => q0, };
        let qsign = sa * (1 - klimbs_is_zero(qmag));
        let two = store(ListNode.Cons([2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
        let half = klimbs_div(klimbs_succ(m), two);
        match klimbs_le(half, r) {
          0 => mk_int_prim(rc, qsign, qmag),
          _ => int_add_prim(rc, qsign, qmag, 0,
            store(ListNode.Cons([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)))),
        },
    }
  }

  fn try_int_prim_dispatch(rc: RoleCtx, head_addr: Addr, spine: List‹KExpr›,
                                types: List‹KExpr›) -> (G, KExpr) {
    let sw = whnf_spine(rc, spine, types);
    let n = list_length(sw);
    let unary = role_is(rc, head_addr, role_int_neg()) + role_is(rc, head_addr, role_int_nat_abs());
    match unary {
      1 => match u32_less_than(n, 1) {
        1 => (0, store(KExprNode.BVar(0))),
        _ => match try_extract_int_prim(rc, list_lookup(sw, 0)) {
          (1, s, a) =>
            let v = match role_is(rc, head_addr, role_int_nat_abs()) {
              1 => mk_nat_lit(a),
              _ => mk_int_prim(rc, (1 - s) * (1 - klimbs_is_zero(a)), a),
            };
            (1, np_apply_spine(v, list_drop(sw, 1))),
          _ => (0, store(KExprNode.BVar(0))),
        },
      },
      _ => match u32_less_than(n, 2) {
        1 => (0, store(KExprNode.BVar(0))),
        _ => match try_extract_int_prim(rc, list_lookup(sw, 0)) {
          (1, sa, a) => try_int_prim_second(rc, head_addr, sw, sa, a),
          _ => (0, store(KExprNode.BVar(0))),
        },
      },
    }
  }

  fn try_int_prim_second(rc: RoleCtx, head_addr: Addr, sw: List‹KExpr›,
                              sa: G, a: KLimbs) -> (G, KExpr) {
    let rhs_nat = role_is(rc, head_addr, role_int_bmod())
      + role_is(rc, head_addr, role_int_bdiv()) + role_is(rc, head_addr, role_int_pow());
    match rhs_nat {
      1 => match try_extract_nat(rc, list_lookup(sw, 1)) {
        (1, b) =>
          let v = match role_is(rc, head_addr, role_int_bmod()) {
            1 => int_bmod_prim(rc, sa, a, b),
            _ => match role_is(rc, head_addr, role_int_bdiv()) {
              1 => int_bdiv_prim(rc, sa, a, b),
              _ =>
                let two = store(ListNode.Cons([2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
                let odd = 1 - klimbs_is_zero(klimbs_mod(b, two));
                mk_int_prim(rc, sa * odd, klimbs_pow(a, b)),
            },
          };
          (1, np_apply_spine(v, list_drop(sw, 2))),
        _ => (0, store(KExprNode.BVar(0))),
      },
      _ => match try_extract_int_prim(rc, list_lookup(sw, 1)) {
        (1, sb, b) =>
          let v = match role_is(rc, head_addr, role_int_add()) {
            1 => int_add_prim(rc, sa, a, sb, b),
            _ => match role_is(rc, head_addr, role_int_sub()) {
              1 => int_add_prim(rc, sa, a, (1 - sb) * (1 - klimbs_is_zero(b)), b),
              _ => match role_is(rc, head_addr, role_int_mul()) {
                1 => mk_int_prim(rc, (sa + sb - 2 * sa * sb)
                  * (1 - klimbs_is_zero(a)) * (1 - klimbs_is_zero(b)), klimbs_mul(a, b)),
                _ => match role_is(rc, head_addr, role_int_emod()) {
                  1 => int_emod_prim(rc, sa, a, b),
                  _ => int_ediv_prim(rc, sa, a, sb, b),
                },
              },
            },
          };
          (1, np_apply_spine(v, list_drop(sw, 2))),
        _ => (0, store(KExprNode.BVar(0))),
      },
    }
  }

  -- ============================================================================
  -- Apply spine (rebuild App chain).
  -- ============================================================================
  fn np_apply_spine(head: KExpr, spine: List‹KExpr›) -> KExpr {
    match load(spine) {
      ListNode.Nil => head,
      ListNode.Cons(a, rest) =>
        np_apply_spine(store(KExprNode.App(head, a)), rest),
    }
  }

  -- ============================================================================
  -- Binop dispatch by head address on two literal args.
  -- ============================================================================
  fn try_nat_binop_addr(rc: RoleCtx, head_addr: Addr, a: KLimbs, b: KLimbs) -> (G, KExpr) {
    match role_is(rc, head_addr, role_nat_add()) {
      1 => (1, mk_nat_lit(klimbs_normalize(klimbs_add(a, b)))),
      _ =>
      match role_is(rc, head_addr, role_nat_sub()) {
        1 => (1, mk_nat_lit(klimbs_normalize(klimbs_sub(a, b)))),
        _ =>
        match role_is(rc, head_addr, role_nat_mul()) {
          1 => (1, mk_nat_lit(klimbs_normalize(klimbs_mul(a, b)))),
          _ =>
          match role_is(rc, head_addr, role_nat_div()) {
            1 => (1, mk_nat_lit(klimbs_normalize(klimbs_div(a, b)))),
            _ =>
            match role_is(rc, head_addr, role_nat_mod()) {
              1 => (1, mk_nat_lit(klimbs_normalize(klimbs_mod(a, b)))),
              _ =>
              match role_is(rc, head_addr, role_nat_gcd()) {
                1 => (1, mk_nat_lit(klimbs_normalize(klimbs_gcd(a, b)))),
                _ =>
                match role_is(rc, head_addr, role_nat_pow()) {
                  1 => (1, mk_nat_lit(klimbs_normalize(klimbs_pow(a, b)))),
                  _ =>
                  match role_is(rc, head_addr, role_nat_land()) {
                    1 => (1, mk_nat_lit(klimbs_normalize(klimbs_land(a, b)))),
                    _ =>
                    match role_is(rc, head_addr, role_nat_lor()) {
                      1 => (1, mk_nat_lit(klimbs_normalize(klimbs_lor(a, b)))),
                      _ =>
                      match role_is(rc, head_addr, role_nat_xor()) {
                        1 => (1, mk_nat_lit(klimbs_normalize(klimbs_xor_op(a, b)))),
                        _ =>
                        match role_is(rc, head_addr, role_nat_shift_left()) {
                          1 => (1, mk_nat_lit(klimbs_normalize(klimbs_shl(a, b)))),
                          _ =>
                          match role_is(rc, head_addr, role_nat_shift_right()) {
                            1 => (1, mk_nat_lit(klimbs_normalize(klimbs_shr(a, b)))),
                            _ =>
                            match role_is(rc, head_addr, role_nat_beq()) {
                              1 => (1, mk_bool(rc, klimbs_eq(a, b))),
                              _ =>
                              match role_is(rc, head_addr, role_nat_ble()) {
                                1 => (1, mk_bool(rc, klimbs_le(a, b))),
                                _ => (0, store(KExprNode.BVar(0))),
                              },
                            },
                          },
                        },
                      },
                    },
                  },
                },
              },
            },
          },
        },
      },
    }
  }

  -- ============================================================================
  -- : nat_offset canonicalization + linear-rec fast path
  -- ============================================================================

  -- If head is Const(nat_add) applied to 2 args with rhs a Lit(Nat),
  -- return (1, lhs, limbs). Else (0, _, _).
  fn try_match_nat_add(rc: RoleCtx, head: KExpr, args: List‹KExpr›) -> (G, KExpr, KLimbs) {
    match load(head) {
      KExprNode.Const(caddr, _) =>
        match role_is(rc, caddr, role_nat_add()) {
          0 => (0, head, store(ListNode.Nil)),
          _ =>
            match list_length(args) - 2 {
              0 =>
                let lhs = list_lookup(args, 0);
                let rhs = list_lookup(args, 1);
                match load(rhs) {
                  KExprNode.Lit(lit) =>
                    match lit {
                      KLiteral.Nat(limbs) => (1, lhs, limbs),
                      _ => (0, head, store(ListNode.Nil)),
                    },
                  _ => (0, head, store(ListNode.Nil)),
                },
              _ => (0, head, store(ListNode.Nil)),
            },
        },
      _ => (0, head, store(ListNode.Nil)),
    }
  }

  -- Build `Nat.succ pred` where pred = base if lit==1,
  -- else `Nat.add base (Lit lit-1)`.
  fn build_succ_offset(rc: RoleCtx, base: KExpr, lit: KLimbs) -> KExpr {
    let one = store(ListNode.Cons([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
                                  store(ListNode.Nil)));
    let pred_lit_norm = klimbs_normalize(klimbs_sub(lit, one));
    let succ_const = store(KExprNode.Const(role_addr(rc, role_nat_succ()), store(ListNode.Nil)));
    match klimbs_is_zero(pred_lit_norm) {
      1 => store(KExprNode.App(succ_const, base)),
      _ =>
        let add_const = store(KExprNode.Const(role_addr(rc, role_nat_add()), store(ListNode.Nil)));
        let pred_lit_expr = store(KExprNode.Lit(KLiteral.Nat(pred_lit_norm)));
        let pred = store(KExprNode.App(
          store(KExprNode.App(add_const, base)),
          pred_lit_expr));
        store(KExprNode.App(succ_const, pred)),
    }
  }

  -- Expose one Nat.succ layer if `e` matches `Nat.add base (Lit n)` with
  -- n > 0. Enables iota to fire on the exposed successor without
  -- unfolding into an n-deep succ tower. Non-matching inputs pass through.
  fn cleanup_nat_offset_major(rc: RoleCtx, e: KExpr) -> KExpr {
    match load(e) {
      KExprNode.Lit(_) => e,
      _ =>
        match collect_spine(e) {
          (head, args) =>
            match load(head) {
              KExprNode.Const(_, _) =>
                match try_match_nat_add(rc, head, args) {
                  (1, base, lit) =>
                    let lit_norm = klimbs_normalize(lit);
                    match klimbs_is_zero(lit_norm) {
                      1 => e,
                      _ => build_succ_offset(rc, base, lit_norm),
                    },
                  _ => e,
                },
              _ => e,
            },
        },
    }
  }

  -- Build the compact stuck offset `Nat.add base (Lit n)` applied to
  -- `post`. n = 0 collapses to bare `base`. Used by try_nat_linear_rec
  -- to keep symbolic-base Nat.rec reductions in a memoizable
  -- canonical form (defeq collapses across `Nat.add base k` with the
  -- same base + k).
  fn mk_nat_offset_stuck(rc: RoleCtx, base_w: KExpr, n: KLimbs,
                              post: List‹KExpr›) -> (G, KExpr) {
    match klimbs_is_zero(n) {
      1 => (1, np_apply_spine(base_w, post)),
      _ =>
        let add_const = store(KExprNode.Const(role_addr(rc, role_nat_add()), store(ListNode.Nil)));
        let off = store(KExprNode.App(
          store(KExprNode.App(add_const, base_w)),
          mk_nat_lit(n)));
        (1, np_apply_spine(off, post)),
    }
  }

  -- Recognize `λ _ (λ _ (Nat.succ #0))` step function shape.
  fn is_nat_succ_ih_step(rc: RoleCtx, step: KExpr) -> G {
    match load(step) {
      KExprNode.Lam(_, body1) =>
        match load(body1) {
          KExprNode.Lam(_, body2) =>
            match collect_spine(body2) {
              (head, args) =>
                match load(head) {
                  KExprNode.Const(caddr, _) =>
                    match role_is(rc, caddr, role_nat_succ()) {
                      0 => 0,
                      _ =>
                        match list_length(args) - 1 {
                          0 =>
                            match load(list_lookup(args, 0)) {
                              KExprNode.BVar(i) => eq_zero(i),
                              _ => 0,
                            },
                          _ => 0,
                        },
                    },
                  _ => 0,
                },
            },
          _ => 0,
        },
      _ => 0,
    }
  }

  -- Fast path for `Nat.rec base (fun _ ih => succ ih) (Lit n)`. Yields
  -- `Lit(base + n)` for literal base or the compact stuck offset
  -- `Nat.add base (Lit n)` for symbolic base. Caller pre-whnfs step +
  -- major (via whnf_spine).
  fn try_nat_linear_rec(rc: RoleCtx, spine: List‹KExpr›, nparams: G, nmotives: G,
                             nminors: G, major_idx: G) -> (G, KExpr) {
    match u32_less_than(nminors, 2) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        let raw_major = list_lookup(spine, major_idx);
        match try_extract_nat(rc, raw_major) {
          (0, _) => (0, store(KExprNode.BVar(0))),
          (1, n_klimbs) =>
            let base_idx = nparams + nmotives;
            let step = list_lookup(spine, base_idx + 1);
            match is_nat_succ_ih_step(rc, step) {
              0 => (0, store(KExprNode.BVar(0))),
              _ =>
                let base = list_lookup(spine, base_idx);
                let post = list_drop(spine, major_idx + 1);
                match try_extract_nat(rc, base) {
                  (1, b_klimbs) =>
                    (1, np_apply_spine(mk_nat_lit(klimbs_add(b_klimbs, n_klimbs)), post)),
                  _ => mk_nat_offset_stuck(rc, base, n_klimbs, post),
                },
            },
        },
    }
  }

  -- ============================================================================
  -- Top-level nat dispatch: unary (succ/pred) then binop.
  -- Caller must whnf spine args before matching Ctor / Lit / literal.
  -- ============================================================================
  fn try_nat_dispatch(rc: RoleCtx, head_addr: Addr, spine: List‹KExpr›,
                          types: List‹KExpr›) -> (G, KExpr) {
    let spine_len = list_length(spine);
    let is_pred = role_is(rc, head_addr, role_nat_pred());
    let is_succ = role_is(rc, head_addr, role_nat_succ());
    match is_succ {
      1 =>
        match u32_less_than(spine_len, 1) {
          1 => (0, store(KExprNode.BVar(0))),
          _ =>
            let a0 = list_lookup(spine, 0);
            match try_extract_nat(rc, a0) {
              (1, na) =>
                let post = list_drop(spine, 1);
                (1, np_apply_spine(mk_nat_lit(klimbs_succ(na)), post)),
              _ => (0, store(KExprNode.BVar(0))),
            },
        },
      _ =>
        match is_pred {
          1 =>
            match u32_less_than(spine_len, 1) {
              1 => (0, store(KExprNode.BVar(0))),
              _ =>
                let a0 = list_lookup(spine, 0);
                match try_extract_nat(rc, a0) {
                  (1, na) =>
                    let post = list_drop(spine, 1);
                    (1, np_apply_spine(mk_nat_lit(klimbs_normalize(klimbs_dec(na))), post)),
                  _ => (0, store(KExprNode.BVar(0))),
                },
            },
          _ => try_nat_binop_dispatch(rc, head_addr, spine, spine_len),
        },
    }
  }

  -- Cold-extracted binop arm (mirror try_nat_binop_dispatch,
  -- Primitive.lean:1671 / [[reference_aiur_hot_cold_split]]): the
  -- binop branch (2× extract + binop-addr chain + offset dispatch +
  -- apply_spine) is the widest arm of try_nat_dispatch, taxing
  -- every Nat.succ/Nat.pred row when inlined. Its width now only
  -- charges rows that actually dispatch a binop.
  fn try_nat_binop_dispatch(rc: RoleCtx, head_addr: Addr, spine: List‹KExpr›,
                                 spine_len: G) -> (G, KExpr) {
    match u32_less_than(spine_len, 2) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        let a0 = list_lookup(spine, 0);
        let a1 = list_lookup(spine, 1);
        match try_extract_nat(rc, a0) {
          (1, na) =>
            match try_extract_nat(rc, a1) {
              (1, nb) =>
                match try_nat_binop_addr(rc, head_addr, na, nb) {
                  (1, result) =>
                    let post = list_drop(spine, 2);
                    (1, np_apply_spine(result, post)),
                  _ => (0, store(KExprNode.BVar(0))),
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
          _ =>
            -- Symbolic base: route to the offset-stuck check
            -- (mirror try_nat_binop_dispatch's fall-through).
            match try_extract_nat(rc, a1) {
              (1, nb) =>
                try_nat_offset_dispatch(rc, head_addr, a0, nb, spine),
              _ => (0, store(KExprNode.BVar(0))),
            },
        },
    }
  }

  -- Mirror try_nat_offset_dispatch (Primitive.lean:1712): a binary
  -- Nat op whose whnf'd base is symbolic and whose second arg is
  -- `Lit nb`. For `Nat.add` (any nb) and `Nat.div`/`Nat.mod` (nb >= 2)
  -- the term is irreducible: return verdict 2 = "already stuck in
  -- compact offset form" so whnf keeps it instead of delta-unfolding
  -- into a succ^nb tower / the division algorithm. Pairs with the
  -- offset-aware def_eq (try_def_eq_nat).
  fn try_nat_offset_dispatch(rc: RoleCtx, head_addr: Addr, a0_w: KExpr, nb: KLimbs,
                                  spine: List‹KExpr›) -> (G, KExpr) {
    let is_add = role_is(rc, head_addr, role_nat_add());
    let is_divmod = role_is(rc, head_addr, role_nat_div())
      + role_is(rc, head_addr, role_nat_mod());
    let eligible =
      is_add + is_divmod * (1 - klimbs_is_zero(nb))
        * (1 - klimbs_is_zero(klimbs_normalize(klimbs_dec(nb))));
    match eligible {
      0 => (0, store(KExprNode.BVar(0))),
      _ =>
        let post = list_drop(spine, 2);
        -- `Nat.add` keeps the canonical add-offset shape (shared with
        -- the linear-rec collapse). Div/mod MUST keep their own head:
        -- routing them through the add builder rewrites `x / n` into
        -- `x + n`.
        match is_add {
          1 =>
            match mk_nat_offset_stuck(rc, a0_w, nb, post) {
              (1, stuck) => (2, stuck),
              _ => (0, store(KExprNode.BVar(0))),
            },
          _ => (2, mk_nat_binop_stuck(head_addr, a0_w, nb, post)),
        },
    }
  }

  -- Rebuild a stuck binary Nat op `op base (Lit n)` applied to `post`,
  -- preserving the op's own head (div stays div, mod stays mod).
  -- Mirror mk_nat_binop_stuck (Primitive.lean:1750), addr-first.
  fn mk_nat_binop_stuck(op_addr: Addr, base_w: KExpr, n: KLimbs,
                             post: List‹KExpr›) -> KExpr {
    let op_const = store(KExprNode.Const(op_addr, store(ListNode.Nil)));
    let stuck = store(KExprNode.App(
      store(KExprNode.App(op_const, base_w)),
      mk_nat_lit(n)));
    np_apply_spine(stuck, post)
  }
⟧

end IxVM

end

