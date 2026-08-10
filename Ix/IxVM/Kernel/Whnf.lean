module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel.Subst
public import Ix.IxVM.Kernel.Levels
public import Ix.IxVM.Kernel.NatPrim
public import Ix.IxVM.Ingress

public section

namespace IxVM

/-! ## Weak Head Normal Form

Two reducers live here, differing only in whether delta fires:

* `whnf` — the full reducer. Beta, zeta, iota (recursors, including the
  K rule and structure eta), quotient lifting/induction, projections,
  the Nat/BitVec/String primitive fast-paths, and delta on `Defn`.
  `Thm` heads stay stuck: a theorem only unfolds through def-eq's
  lazy-delta step, never by plain reduction.
* `whnf_nd` — the no-delta reducer (`_nd` suffix throughout). Everything
  above except delta, so `Defn` and `Thm` heads both stay stuck. Def-eq
  reduces with this first, since it is far cheaper and often enough to
  decide a pair, and only then pays for unfolding.

`get_ci(addr)` fault-loads and memoizes, so reduction needs no ambient
constant table — an addr is self-sufficient. The `types` argument is the
local binder context, threaded for the inference calls that gate the K
rule and structure eta.
-/

def whnf := ⟦
  fn apply_spine(head: KExpr, spine: List‹KExpr›) -> KExpr {
    match load(spine) {
      ListNode.Nil => head,
      ListNode.Cons(a, rest) =>
        apply_spine(store(KExprNode.App(head, a)), rest),
    }
  }

  -- Peel `Lam` telescope against spine, one arg per Lam.
  fn peel_beta(lam: KExpr, spine: List‹KExpr›, acc: List‹KExpr›)
                  -> (KExpr, List‹KExpr›, List‹KExpr›) {
    match load(lam) {
      KExprNode.Lam(_, body) =>
        match load(spine) {
          ListNode.Cons(a, rest) =>
            peel_beta(body, rest, store(ListNode.Cons(a, acc))),
          ListNode.Nil => (lam, acc, spine),
        },
      _ => (lam, acc, spine),
    }
  }

  -- Multi-arg beta (mirror crates/kernel/src/whnf.rs): peel the whole
  -- telescope and substitute all consumed args in ONE `expr_inst_many` walk,
  -- instead of one `expr_inst1` re-walk of the body per arg. Single-arg betas
  -- stay on the cheap `expr_inst1` path (no list overhead).
  fn whnf_apply_beta(spine: List‹KExpr›, lam: KExpr, types: List‹KExpr›) -> KExpr {
    match peel_beta(lam, spine, store(ListNode.Nil)) {
      (deep, consumed, rest) =>
        match list_length(consumed) {
          0 => apply_spine(lam, spine),
          1 =>
            let body2 = expr_inst1(deep, list_lookup(consumed, 0), 0);
            whnf_with_spine(body2, rest, types),
          _ =>
            let body2 = expr_inst_many(deep, consumed, 0);
            whnf_with_spine(body2, rest, types),
        },
    }
  }

  fn whnf_with_spine(head: KExpr, spine: List‹KExpr›, types: List‹KExpr›) -> KExpr {
    match load(head) {
      KExprNode.App(f, a) =>
        match collect_spine(head) {
          (inner_head, inner_spine) =>
            whnf_with_spine(inner_head, list_concat(inner_spine, spine), types),
        },
      KExprNode.Lam(ty, body) =>
        whnf_apply_beta(spine, head, types),
      KExprNode.Const(addr, lvls) =>
        whnf_const_head(addr, lvls, head, spine, types),
      KExprNode.Let(_, val, body) =>
        let next = expr_inst1(body, val, 0);
        whnf_with_spine(next, spine, types),
      KExprNode.Proj(struct_addr, fidx, inner) =>
        whnf_proj_head(struct_addr, fidx, inner, spine, types),
      _ => apply_spine(head, spine),
    }
  }

  -- Proj-head WHNF: whnf inner, if it's a Ctor application, pull the
  -- corresponding field.  Otherwise stays stuck as `Proj(struct, fidx, inner_whnf)`.
  -- : try_reduce_fin_val_decidable_rec hook — Fin.val on
  -- Decidable.rec pushes Proj inside minors, unblocks iota once
  -- major is Decidable.isTrue/isFalse.
  fn whnf_proj_head(struct_addr: Addr, fidx: G, inner: KExpr,
                        spine: List‹KExpr›, types: List‹KExpr›) -> KExpr {
    let inner_whnf = whnf(inner, types);
    -- Str-literal re-expansion (mirror whnf_proj_head): a Proj over
    -- a Lit(Str) scrutinee needs the ctor form to pull fields.
    let inner_exp = str_lit_to_ctor_app_or_self(inner_whnf, types);
    match collect_spine(inner_exp) {
      (inner_head, inner_args) =>
        match try_reduce_fin_val_decidable_rec(struct_addr, fidx,
                inner_head, inner_args) {
          (1, rewritten) => whnf_with_spine(rewritten, spine, types),
          _ =>
            match load(inner_head) {
              KExprNode.Const(_, _) =>
                match load(whnf_get_ctor_or_none(inner_head)) {
                  KConstantInfo.Ctor(_, _, _, _, _, nparams, _, _) =>
                    let field = list_lookup(inner_args, nparams + fidx);
                    whnf_with_spine(field, spine, types),
                  _ =>
                    let stuck = store(KExprNode.Proj(struct_addr, fidx, inner_whnf));
                    apply_spine(stuck, spine),
                },
              _ =>
                let stuck = store(KExprNode.Proj(struct_addr, fidx, inner_whnf));
                apply_spine(stuck, spine),
            },
        },
    }
  }

  fn fin_addr() -> Addr {
    store([0x74u8, 0x59u8, 0x36u8, 0xfcu8, 0xb9u8, 0xd8u8, 0x6cu8, 0x44u8,
     0x57u8, 0xf0u8, 0xfdu8, 0x1eu8, 0x53u8, 0x7eu8, 0x67u8, 0x07u8,
     0x7fu8, 0x46u8, 0xf7u8, 0x84u8, 0x11u8, 0x08u8, 0x41u8, 0x9du8,
     0xacu8, 0x79u8, 0x84u8, 0x00u8, 0x8bu8, 0x56u8, 0x5bu8, 0x97u8])
  }

  fn decidable_rec_addr() -> Addr {
    store([0xabu8, 0x37u8, 0x76u8, 0x98u8, 0x57u8, 0x43u8, 0xafu8, 0x13u8,
     0xa9u8, 0xcbu8, 0x1au8, 0x7du8, 0x2fu8, 0x84u8, 0x96u8, 0x99u8,
     0x78u8, 0x92u8, 0xe1u8, 0x79u8, 0x83u8, 0xd1u8, 0x4bu8, 0xe5u8,
     0x27u8, 0x0au8, 0x71u8, 0x65u8, 0x70u8, 0xb3u8, 0x57u8, 0x19u8])
  }

  fn nat_ty_addr() -> Addr {
    store([0x39u8, 0x8au8, 0x77u8, 0x06u8, 0xcfu8, 0x13u8, 0xf2u8, 0x23u8,
     0x99u8, 0x2du8, 0x17u8, 0x3du8, 0xceu8, 0x07u8, 0x94u8, 0x68u8,
     0x57u8, 0x24u8, 0x0fu8, 0x49u8, 0xafu8, 0xccu8, 0x74u8, 0x37u8,
     0x23u8, 0xe8u8, 0x39u8, 0xf8u8, 0xf3u8, 0xf2u8, 0xb6u8, 0x31u8])
  }

  -- The three quotient primitives reduction is allowed to fire on.
  -- Same literals as `Kernel/Check.lean`'s; `Tests/Ix/Kernel/PrimAddrs.lean`
  -- collects every `*_addr` function in the toplevel and asserts each
  -- resolves to the constant its name claims, so a drifted copy fails
  -- there rather than silently mis-reducing.
  fn quot_ctor_addr_iota() -> Addr {
    store([0x88u8, 0x26u8, 0x66u8, 0x77u8, 0xfeu8, 0xe7u8, 0x74u8, 0xd1u8,
     0x09u8, 0x86u8, 0x7eu8, 0x4bu8, 0x22u8, 0x40u8, 0x28u8, 0x1au8,
     0xa2u8, 0xeeu8, 0x12u8, 0xd9u8, 0x79u8, 0x20u8, 0xc1u8, 0x17u8,
     0x1cu8, 0xf5u8, 0xc1u8, 0xf6u8, 0xc8u8, 0x7du8, 0xecu8, 0xf6u8])
  }

  fn quot_lift_addr_iota() -> Addr {
    store([0x8du8, 0xc4u8, 0xa9u8, 0x75u8, 0x27u8, 0x81u8, 0x2fu8, 0x8bu8,
     0x78u8, 0x17u8, 0xb7u8, 0x7cu8, 0xd0u8, 0x79u8, 0xacu8, 0xe6u8,
     0x14u8, 0x50u8, 0xaau8, 0x01u8, 0x85u8, 0xacu8, 0x58u8, 0x85u8,
     0x66u8, 0x1eu8, 0xc2u8, 0xacu8, 0xbau8, 0x8bu8, 0x7bu8, 0xd0u8])
  }

  fn quot_ind_addr_iota() -> Addr {
    store([0x12u8, 0x49u8, 0x84u8, 0xbcu8, 0xb9u8, 0x52u8, 0x08u8, 0xa0u8,
     0xf3u8, 0x0bu8, 0xb6u8, 0x9du8, 0x67u8, 0x36u8, 0xd3u8, 0xd5u8,
     0x94u8, 0x04u8, 0xe1u8, 0x15u8, 0xe2u8, 0x20u8, 0x20u8, 0x43u8,
     0xfdu8, 0xa3u8, 0xd3u8, 0x4eu8, 0x01u8, 0xb0u8, 0xadu8, 0x16u8])
  }

  -- Mirror try_reduce_fin_val_decidable_rec (Primitive.lean:3141+).
  -- Rewrites `Proj Fin 0 (Decidable.rec α motive f_min t_min major post)`
  -- to  `Decidable.rec α (fun _ => Nat)
  --          (fun x => Proj Fin 0 (f_min x))
  --          (fun x => Proj Fin 0 (t_min x)) major post`
  -- so iota fires once major = Decidable.isTrue/isFalse.
  fn try_reduce_fin_val_decidable_rec(struct_addr: Addr, fidx: G,
                                            inner_head: KExpr,
                                            inner_args: List‹KExpr›)
                                            -> (G, KExpr) {
    match address_eq(struct_addr, fin_addr()) {
      0 => (0, store(KExprNode.BVar(0))),
      _ =>
        match fidx {
          0 =>
            match load(inner_head) {
              KExprNode.Const(rec_addr, rec_us) =>
                match address_eq(rec_addr, decidable_rec_addr()) {
                  0 => (0, store(KExprNode.BVar(0))),
                  _ =>
                    match u32_less_than(list_length(inner_args), 5) {
                      1 => (0, store(KExprNode.BVar(0))),
                      _ =>
                        let a0 = list_lookup(inner_args, 0);
                        let a1 = list_lookup(inner_args, 1);
                        let a2 = list_lookup(inner_args, 2);
                        let a3 = list_lookup(inner_args, 3);
                        let a4 = list_lookup(inner_args, 4);
                        match load(a1) {
                          KExprNode.Lam(motive_dom, _) =>
                            match load(a2) {
                              KExprNode.Lam(fdom, fbody) =>
                                let fproj = store(KExprNode.Proj(
                                  struct_addr, fidx, fbody));
                                let false_minor = store(KExprNode.Lam(
                                  fdom, fproj));
                                match load(a3) {
                                  KExprNode.Lam(tdom, tbody) =>
                                    let tproj = store(KExprNode.Proj(
                                      struct_addr, fidx, tbody));
                                    let true_minor = store(KExprNode.Lam(
                                      tdom, tproj));
                                    let nat_ty = store(KExprNode.Const(
                                      nat_ty_addr(), store(ListNode.Nil)));
                                    let new_motive = store(KExprNode.Lam(
                                      motive_dom, nat_ty));
                                    let head_const = store(KExprNode.Const(
                                      rec_addr, rec_us));
                                    let r1 = store(KExprNode.App(head_const, a0));
                                    let r2 = store(KExprNode.App(r1, new_motive));
                                    let r3 = store(KExprNode.App(r2, false_minor));
                                    let r4 = store(KExprNode.App(r3, true_minor));
                                    let r5 = store(KExprNode.App(r4, a4));
                                    let post = list_drop(inner_args, 5);
                                    (1, apply_spine(r5, post)),
                                  _ => (0, store(KExprNode.BVar(0))),
                                },
                              _ => (0, store(KExprNode.BVar(0))),
                            },
                          _ => (0, store(KExprNode.BVar(0))),
                        },
                    },
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
          _ => (0, store(KExprNode.BVar(0))),
        },
    }
  }

  -- Returns the Ctor KCI if `head` is a Const of a Ctor, else a stub axiom
  -- KCI (harmless — the caller falls through on the non-Ctor match).
  fn whnf_get_ctor_or_none(head: KExpr) -> &KConstantInfo {
    match load(head) {
      KExprNode.Const(addr, _) => get_ci(addr),
      _ =>
        store(KConstantInfo.Axiom(0, store(KExprNode.Srt(store(KLevelNode.Zero))), 0)),
    }
  }

  -- Const head: delta-unfold Defn or iota-reduce Rec applied to Ctor
  -- major. Ctor/Ind/Axiom/Quot etc. stay stuck. Before Defn delta, try
  -- projection-definition shortcut: `def field := fun x => Prj S i x`
  -- rewrites `field arg` to `Prj S i arg` without expanding the body.
  -- WHNF each spine arg (needed before calling nat dispatch — args
  -- must be normalized to Lit/Const-headed forms for try_extract_nat).
  fn whnf_spine(spine: List‹KExpr›, types: List‹KExpr›) -> List‹KExpr› {
    match load(spine) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(a, rest) =>
        let aw = whnf(a, types);
        store(ListNode.Cons(aw, whnf_spine(rest, types))),
    }
  }

  -- Pre-whnf wrapper for nat dispatch: whnfs unary/binop args first
  -- (2 first args or 1 first arg for succ/pred), then calls
  -- try_nat_dispatch.
  fn try_nat_dispatch_prewhnf(head_addr: Addr, spine: List‹KExpr›,
                                    types: List‹KExpr›) -> (G, KExpr) {
    let spine_w = whnf_spine(spine, types);
    try_nat_dispatch(head_addr, spine_w, types)
  }

  -- Address-keyed primitive dispatch. Runs BEFORE KConstantInfo
  -- discrimination so it fires regardless of whether the primitive
  -- lives as Defn/Axiom/etc. in the loaded env (matters for
  -- String.utf8ByteSize / String.append which may compile as Defn
  -- with an external body or as Axiom).
  -- For BitVec.toNat: whnf spine[1] (the val, expected to be
  -- BitVec.ofNat W N form) then further whnf its inner args (W and N)
  -- so try_extract_nat sees Lit(Nat) even when the source used
  -- OfNat.ofNat wrappers.
  fn bitvec_prep_spine(spine: List‹KExpr›, types: List‹KExpr›)
                            -> List‹KExpr› {
    let spine_w = whnf_spine(spine, types);
    match load(spine_w) {
      ListNode.Nil => spine_w,
      ListNode.Cons(width_e, rest) =>
        match load(rest) {
          ListNode.Nil => spine_w,
          ListNode.Cons(val_e, tail) =>
            match collect_spine(val_e) {
              (vh, va) =>
                let va_w = whnf_spine(va, types);
                let val_e2 = apply_spine(vh, va_w);
                let width_w = whnf(width_e, types);
                store(ListNode.Cons(width_w,
                  store(ListNode.Cons(val_e2, tail)))),
            },
        },
    }
  }

  -- Primitive-family classification (mirror prim_family,
  -- Primitive.lean:1419): map a Const-head address to the ONE reducer
  -- family that could fire on it — 0 = none, 1 = nat, 2 = str,
  -- 3 = bitvec, 4 = native, 5 = decidable. Keyed on the ADDRESS ALONE:
  -- one memo row per distinct constant address in the run, and the
  -- inner addr-set chains collapse after each address's first
  -- occurrence. Replaces running the is_* gauntlet from
  -- try_prim_dispatch, whose key includes the spine and context —
  -- 5 wide rows per Const-head whnf, almost all guaranteed misses.
  fn prim_family(a: Addr) -> G {
    match is_nat_prim_addr(a) {
      1 => 1,
      _ =>
        match is_str_prim_addr(a) {
          1 => 2,
          _ =>
            match is_bitvec_prim_addr(a) {
              1 => 3,
              _ =>
                match is_native_prim_addr(a) {
                  1 => 4,
                  _ =>
                    match is_dec_prim_addr(a) {
                      1 => 5,
                      _ => 0,
                    },
                },
            },
        },
    }
  }

  fn try_prim_dispatch(addr: Addr, lvls: List‹KLevel›,
                            spine: List‹KExpr›,
                            types: List‹KExpr›) -> (G, KExpr) {
    let fam = prim_family(addr);
    match fam {
      1 => try_nat_dispatch_prewhnf(addr, spine, types),
      2 =>
        let spine_w = whnf_spine(spine, types);
        try_str_dispatch(addr, spine_w, types),
      3 => try_bitvec_dispatch(addr, spine, types),
      4 => try_native_dispatch(addr, spine, types),
      5 => try_dec_dispatch(addr, lvls, spine, types),
      _ => (0, store(KExprNode.BVar(0))),
    }
  }

  -- Quot iota: Quot.lift α r β f sound (Quot.mk α' r' a) = f a
  -- and Quot.ind α r motive m (Quot.mk α' r' a) = m a. Anything else
  -- stays stuck.
  --
  -- Dispatch is on the ADDRESS alone, and the stored `QuotKind` is not
  -- consulted. All three references decide this way — Rust
  -- `try_quot_reduce` (`whnf.rs:3073-3120`) compares against
  -- `self.prims.quot_lift.addr` / `quot_ind.addr`, `Ix/Tc`
  -- `tryQuotReduce` (`Whnf.lean:1674-1698`) against `p.quotLift.addr` /
  -- `p.quotInd.addr`, and lean4lean `quotReduceRec` (`Quot.lean:85-100`)
  -- against the names `Quot.lift` / `Quot.ind`.
  --
  -- The kind field is a checked REDUNDANCY, not a dispatch input: Rust's
  -- `check_quot` and `Ix/Tc`'s `checkQuot` both DERIVE the expected kind
  -- from the address and assert the stored one matches. Reduction runs
  -- before any of that — `get_ci` typechecks nothing — so keying on the
  -- kind would trust a field no one has validated yet.
  fn try_quot_iota(addr: Addr, spine: List‹KExpr›,
                         types: List‹KExpr›) -> (G, KExpr) {
    match address_eq(addr, quot_lift_addr_iota()) {
      1 => try_quot_lift(spine, types),
      _ =>
        match address_eq(addr, quot_ind_addr_iota()) {
          1 => try_quot_ind(spine, types),
          _ => (0, store(KExprNode.BVar(0))),
        },
    }
  }

  fn try_quot_lift(spine: List‹KExpr›, types: List‹KExpr›) -> (G, KExpr) {
    let n = list_length(spine);
    match u32_less_than(n, 6) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        let f = list_lookup(spine, 3);
        let q = list_lookup(spine, 5);
        match quot_extract_arg(q, types) {
          (1, a) =>
            let post = list_drop(spine, 6);
            (1, apply_spine(store(KExprNode.App(f, a)), post)),
          _ => (0, store(KExprNode.BVar(0))),
        },
    }
  }

  fn try_quot_ind(spine: List‹KExpr›, types: List‹KExpr›) -> (G, KExpr) {
    let n = list_length(spine);
    match u32_less_than(n, 5) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        let m = list_lookup(spine, 3);
        let q = list_lookup(spine, 4);
        match quot_extract_arg(q, types) {
          (1, a) =>
            let post = list_drop(spine, 5);
            (1, apply_spine(store(KExprNode.App(m, a)), post)),
          _ => (0, store(KExprNode.BVar(0))),
        },
    }
  }

  -- WHNF q; if q reduces to `App-spine(Const(Quot.mk), [α, r, a])`,
  -- return (1, a). Else (0, _).
  --
  -- The head is recognised by ADDRESS and the arity must be exactly 3,
  -- which is all the references look at: Rust
  -- `if *mk_addr != self.prims.quot_ctor.addr { return Ok(None) }` then
  -- `if mk_args.len() != 3` (`whnf.rs:3108`), `Ix/Tc` the same against
  -- `p.quotCtor.addr` (`Whnf.lean:1690-1698`), lean4lean
  -- `if !mk.isAppOfArity ``Quot.mk 3` (`Quot.lean:88`). No `get_ci`, no
  -- stored kind — the constant need not even be resolvable for this to
  -- decide, and resolving it would only reintroduce the unvalidated tag.
  fn quot_extract_arg(q: KExpr, types: List‹KExpr›) -> (G, KExpr) {
    let q_w = whnf(q, types);
    match collect_spine(q_w) {
      (head, args) =>
        match load(head) {
          KExprNode.Const(caddr, _) =>
            match address_eq(caddr, quot_ctor_addr_iota()) {
              1 =>
                match list_length(args) - 3 {
                  0 => (1, list_lookup(args, 2)),
                  _ => (0, store(KExprNode.BVar(0))),
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
          _ => (0, store(KExprNode.BVar(0))),
        },
    }
  }

  -- Const-head WHNF dispatch, split out of `whnf_with_spine` (see its Const arm).
  -- `head` is the original `Const(idx, lvls)` KExpr, passed for the stuck
  -- `apply_spine(head, spine)` fallbacks.
  fn whnf_const_head(addr: Addr, lvls: List‹KLevel›, head: KExpr,
                         spine: List‹KExpr›, types: List‹KExpr›) -> KExpr {
    let prim = try_prim_dispatch(addr, lvls, spine, types);
    match prim {
      (1, reduced) => whnf(reduced, types),
      -- verdict 2: the reducer normalized the term to an already-stuck
      -- compact form (symbolic Nat offset); return it WITHOUT re-whnf
      -- and WITHOUT falling to the Defn arm — delta-unfolding it would
      -- expand a succ^n tower / the division algorithm. Mirror
      -- whnf_const_head:230.
      (2, stuck) => stuck,
      _ =>
    let ci = load(get_ci(addr));
    match ci {
      KConstantInfo.Defn(_, _, value, _, _) =>
        let pd = try_reduce_projection_definition(value, spine);
        match pd {
          (1, reduced) => whnf(reduced, types),
          _ =>
            let body = expr_inst_levels(value, lvls);
            whnf_with_spine(body, spine, types),
        },
      -- Thm stays stuck in the general reducer. The reference unfolds
      -- `Definition | Theorem` alike here (delta_unfold_one, whnf.rs),
      -- but doing that globally cost `Std.Time...ofDays._proof_1` 14x
      -- (5.1s -> 69.8s) for no verdict change: every proof term the
      -- check touches then gets driven through its body. Theorem
      -- unfolding is only NEEDED to drive an iota major to a
      -- constructor, so it lives at that one site (`whnf_iota_major`),
      -- and proof_irrel / congruence still get first shot at Thm-headed
      -- pairs everywhere else. Under-reducing relative to the reference
      -- is the safe direction: it can only leave a term stuck, never
      -- manufacture a reduction.
      KConstantInfo.Thm(_, _, _) => apply_spine(head, spine),
      KConstantInfo.Quot(_, _, _) =>
        let quot = try_quot_iota(addr, spine, types);
        match quot {
          (1, reduced) => whnf(reduced, types),
          _ => apply_spine(head, spine),
        },
      KConstantInfo.Rec(nlvls, rec_ty, nparams, nindices, nmotives, nminors,
                          rules, k_flag, _unsafe, _block, _ridx) =>
        -- K-like recursors: try to synthesize the nullary K-ctor from the
        -- RAW major BEFORE the major is whnf'd, mirroring the reference
        -- (whnf.rs:1349-1356, `let major = if recr.k { synth_ctor_when_k
        -- (major)... }` sits above the major-whnf). The gate costs one
        -- inference plus an index def-eq; whnf'ing the major first can
        -- cost arbitrarily more, because a K major is typically a PROOF
        -- and whnf of a proof evaluates whatever decision procedure
        -- produced it (`Std.Time...ofDays._proof_1` is an `Eq.rec` over a
        -- `decide +kernel` proof — reducing that major runs the whole
        -- Rat/Nat decision procedure over 14-digit literals).
        --
        -- Ordering only; the verdict is unchanged. `try_k_synth_iota`
        -- gates on `k_infer` of the raw major read from `spine`, so it
        -- computes the same answer before and after a major whnf — which
        -- is why the k_flag=1 stuck-fallback below is now redundant and
        -- simply keeps the stuck form.
        let k_skip = ((nparams + nmotives) + nminors) + nindices;
        let k_pre = match k_flag {
          1 =>
            -- The recursor's OWN inductive, read from its declared major
            -- premise. The K gate must check the major's inferred
            -- inductive against this — comparing the major against its
            -- own inductive's ctor is vacuous, and would strip an `I.rec`
            -- over a major of some other inductive `J`. (An inductive-addr
            -- comparison, not a `block`-field one, so the solo-wrapper
            -- mismatch noted in k_synth_gate does not apply.)
            match se_parent_addr(rec_ty, k_skip) {
              (_, rec_parent) =>
                try_k_synth_iota(lvls, spine, nparams, nmotives,
                                    nminors, nindices, rules,
                                    rec_parent, types),
            },
          _ => (0, head),
        };
        match k_pre {
          (1, k_reduct) => k_reduct,
          _ =>
        let iota = try_iota(lvls, spine, nparams, nmotives, nminors,
                                 nindices, rules, types, head,
                                 rec_to_parent_addr(rec_ty, nparams, nmotives,
                                   nminors, nindices));
        match iota {
          (1, reduced) => whnf(reduced, types),
          (2, stuck) =>
            match k_flag {
              -- Already attempted pre-whnf above with the same verdict.
              1 => stuck,
              _ =>
                -- Struct-eta iota (mirror try_struct_eta_iota /
                -- Rust whnf.rs:1244 / Lean toCtorWhenStructure): major
                -- stuck but inductive is a structure (1 ctor, 0
                -- indices, non-recursive, non-Prop major) → synthesize
                -- the ctor app from field projections of the major and
                -- fire the single rule anyway.
                match try_struct_eta_iota(rec_ty, lvls, spine, nparams,
                        nmotives, nminors, nindices, rules, types) {
                  (1, r) => whnf(r, types),
                  _ => stuck,
                },
            },
          _ => apply_spine(head, spine),
        },
        },
      _ => apply_spine(head, spine),
    },
    }
  }

  -- Recognize `λ x_1 ... x_n → Prj S i (BVar k)` and rewrite an
  -- application of the constant to a direct Prj. Mirrors the Rust
  -- implementation in crates/kernel/src. Pure perf — standard
  -- delta+beta produces the same result — but keeps binder-type WHNF
  -- inside a proj scrutinee stuck at Const-inductive form rather than
  -- descending into the body and getting stuck at a partially-applied
  -- Lam.
  fn try_reduce_projection_definition(value: KExpr,
                                          spine: List‹KExpr›) -> (G, KExpr) {
    match projection_definition_info(value, 0) {
      (1, arity, struct_addr, field, struct_arg_idx) =>
        match u32_less_than(list_length(spine), arity) {
          1 => (0, store(KExprNode.BVar(0))),
          _ =>
            let target_arg = list_lookup(spine, struct_arg_idx);
            let proj_expr = store(KExprNode.Proj(struct_addr, field, target_arg));
            let post = list_drop(spine, arity);
            (1, apply_spine(proj_expr, post)),
        },
      _ => (0, store(KExprNode.BVar(0))),
    }
  }

  -- Returns (found, arity, struct_addr, field, struct_arg_idx). Walks
  -- Lam bindings counting arity; expects body to be `Prj S i (BVar k)`
  -- with `k < arity`. struct_arg_idx = (arity - 1) - k.
  fn projection_definition_info(val: KExpr, arity: G)
                                    -> (G, G, Addr, G, G) {
    match load(val) {
      KExprNode.Lam(_, body) =>
        projection_definition_info(body, arity + 1),
      KExprNode.Proj(struct_addr, field, projected) =>
        match load(projected) {
          KExprNode.BVar(i) =>
            match u32_less_than(i, arity) {
              1 => (1, arity, struct_addr, field, (arity - 1) - i),
              _ => (0, 0, store([0u8; 32]), 0, 0),
            },
          _ => (0, 0, store([0u8; 32]), 0, 0),
        },
      _ => (0, 0, store([0u8; 32]), 0, 0),
    }
  }

  -- Canonical Nat.zero / Nat.succ addrs. Mirror
  -- crates/kernel/src, 490).
  fn nat_zero_addr_iota() -> Addr {
    store([0xd3u8, 0x97u8, 0x37u8, 0x01u8, 0x57u8, 0xfbu8, 0x9au8, 0xe2u8,
     0xc6u8, 0xe1u8, 0xedu8, 0xa7u8, 0x9fu8, 0xebu8, 0x10u8, 0xbfu8,
     0x49u8, 0x74u8, 0x01u8, 0x74u8, 0x1au8, 0xbau8, 0x78u8, 0x8fu8,
     0xabu8, 0x72u8, 0x6cu8, 0xfau8, 0x4cu8, 0x46u8, 0x7du8, 0xb6u8])
  }

  fn nat_succ_addr_iota() -> Addr {
    store([0xdeu8, 0xf5u8, 0x2du8, 0x1du8, 0xadu8, 0x5fu8, 0x10u8, 0xcfu8,
     0x98u8, 0x93u8, 0xc9u8, 0x45u8, 0xe1u8, 0x69u8, 0x71u8, 0x8du8,
     0x62u8, 0xb1u8, 0x5eu8, 0x2du8, 0xd2u8, 0xc9u8, 0x06u8, 0x6eu8,
     0x59u8, 0x7bu8, 0x9du8, 0x45u8, 0x70u8, 0xbau8, 0x05u8, 0x6eu8])
  }

  -- Convert `Lit(Nat n)` to `Nat.zero` or `App(Nat.succ, Lit(n-1))`.
  -- Non-Lit inputs pass through unchanged. Enables iota to fire on
  -- Lit majors.  Mirror crates/kernel/src.
  fn nat_lit_to_ctor_or_self(e: KExpr) -> KExpr {
    match load(e) {
      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Nat(klimbs) =>
            match klimbs_is_zero(klimbs) {
              1 => store(KExprNode.Const(nat_zero_addr_iota(),
                                          store(ListNode.Nil))),
              _ =>
                let pred_limbs = klimbs_normalize(klimbs_dec(klimbs));
                let pred = store(KExprNode.Lit(KLiteral.Nat(pred_limbs)));
                let succ_const = store(KExprNode.Const(nat_succ_addr_iota(),
                                                       store(ListNode.Nil)));
                store(KExprNode.App(succ_const, pred)),
            },
          _ => e,
        },
      _ => e,
    }
  }

  -- K-recursor synth: fire rule[0] assuming the nullary K-ctor, but only
  -- when the toCtorWhenK gate holds (mirror try_synth_k_ctor,
  -- crates/kernel/src: infer the major's type, require its
  -- head to be this recursor's inductive, synthesize the ctor app from
  -- the type's params, and require def_eq(major_ty, ctor_ty). Without
  -- the gate, an Eq.rec transport whose endpoints differ symbolically
  -- gets stripped, producing mistyped reducts.
  -- Returns (1, reduct) when the K gate fires, (0, _) on a miss.
  --
  -- The gate reads the RAW major out of `spine` and infers ITS type, so
  -- the outcome does not depend on whether the major has been whnf'd —
  -- which is what lets the caller run this BEFORE the major whnf (see
  -- the ordering note at the Rec arm of whnf_const_head).
  fn try_k_synth_iota(lvls: List‹KLevel›, spine: List‹KExpr›,
                          nparams: G, nmotives: G, nminors: G, nindices: G,
                          rules: List‹KRecRule›,
                          rec_parent: Addr, types: List‹KExpr›)
                          -> (G, KExpr) {
    match load(rules) {
      ListNode.Cons(r, _) =>
        match r {
          KRecRule.Mk(cidx, _rfields, rrhs) =>
            let major_idx = nparams + nmotives + nminors + nindices;
            -- Same spine-length guard `try_iota` applies before reading its
            -- major. A PARTIALLY APPLIED recursor has no major argument yet,
            -- and `list_lookup` past the end of the spine hits `Nil` against
            -- an irrefutable `Cons` binding and aborts. This used to be
            -- unreachable — the only caller was `try_iota`'s stuck branch,
            -- which had already proved the spine long enough — but the K gate
            -- now runs BEFORE `try_iota`, so it must re-establish the
            -- precondition itself. A recursor short of its major cannot iota
            -- at all, so declining here is also the right verdict.
            match memo_u32_less_than(major_idx, list_length(spine)) {
              0 => (0, store(KExprNode.BVar(0))),
              _ =>
                let raw_major = list_lookup(spine, major_idx);
                match k_synth_gate(raw_major, cidx, nparams, rec_parent, types) {
                  0 => (0, store(KExprNode.BVar(0))),
                  _ =>
                    let rhs_lvled = expr_inst_levels(rrhs, lvls);
                    let pmm_end = nparams + nmotives + nminors;
                    let pmm = list_take(spine, pmm_end);
                    let post_major = list_drop(spine, major_idx + 1);
                    let r1 = apply_spine(rhs_lvled, pmm);
                    let r3 = apply_spine(r1, post_major);
                    (1, whnf(r3, types)),
                },
            },
        },
      _ => (0, store(KExprNode.BVar(0))),
    }
  }

  -- The toCtorWhenK gate: 1 iff whnf(infer(major)) is `I params indices`
  -- for this recursor's own inductive AND the synthesized ctor app
  -- `I.ctor params` has type def-eq to the major's. Mirror
  -- try_synth_k_ctor's verification step.
  fn k_synth_gate(raw_major: KExpr, cidx: G, nparams: G,
                      rec_parent: Addr, types: List‹KExpr›) -> G {
    let major_ty = k_infer(raw_major, types);
    let major_ty_w = whnf(major_ty, types);
    match collect_spine(major_ty_w) {
      (ty_head, ty_args) =>
        match load(ty_head) {
          KExprNode.Const(ind_addr, ctor_us) =>
            -- Identity: the major's inductive must be the recursor's own.
            -- Everything below is derived from the major, so without this
            -- the def_eq compares the major against its OWN inductive's
            -- ctor and always holds — vacuous. `rec_parent` is the
            -- inductive named in the recursor's declared major premise, so
            -- this is an inductive-addr comparison, not the `block`-field
            -- comparison the solo-wrapper case breaks.
            match address_eq(ind_addr, rec_parent) {
              0 => 0,
              _ =>
                let ind_ci = load(get_ci(ind_addr));
                match ind_ci {
                  KConstantInfo.Induct(_, _, _, _, _, _, ind_block, ind_idx) =>
                    let cprj = canon_cprj_addr(ind_block, ind_idx, cidx);
                    let ctor_head = store(KExprNode.Const(cprj, ctor_us));
                    let params = list_take(ty_args, nparams);
                    let ctor_app = apply_spine(ctor_head, params);
                    let ctor_ty = k_infer(ctor_app, types);
                    k_is_def_eq(major_ty_w, ctor_ty, types),
                  _ => 0,
                },
            },
          _ => 0,
        },
    }
  }

  -- Attempt iota reduction: given a recursor head + spine, whnf the
  -- major argument. If it's a Ctor application matching one of the
  -- rules, apply the rule's rhs (Lam-wrapped) to
  -- params ++ motives ++ minors ++ ctor_fields ++ post_major via
  -- apply_spine so that outer whnf beta-reduces. Mirror
  -- crates/kernel/src.
  -- Rewrite spine with major (at major_idx) replaced by given whnf'd major.
  fn replace_spine_major(spine: List‹KExpr›, major_idx: G, major_w: KExpr)
                             -> List‹KExpr› {
    let pre = list_take(spine, major_idx);
    let post = list_drop(spine, major_idx + 1);
    let with_major = list_concat(pre,
      store(ListNode.Cons(major_w, store(ListNode.Nil))));
    list_concat(with_major, post)
  }

  -- whnf an iota MAJOR, unfolding theorem heads. `whnf` leaves a Thm
  -- head stuck (see the Thm arm of whnf_const_head), but a recursor can
  -- only fire once its major reaches constructor form, and a major can
  -- legitimately BE a theorem: `abstractNestedProofs` lifts inline
  -- proofs out into auto-theorems, so `And.rec motive minor MAJOR` gets
  -- a `..._proof_1` there (`Rat.instEncodable`; the `thmMajorUse`
  -- fixture). Without this the recursor stayed stuck and the constant
  -- was rejected as "inferred type is not def-eq to the expected type".
  --
  -- Recursive: a theorem body can be another theorem application, and
  -- the reference's delta loop steps those the same way. Only the major
  -- position pays this — the reference unfolds theorems in every full
  -- whnf, which measured 14x worse on ofDays for no verdict change.
  fn whnf_iota_major(e: KExpr, types: List‹KExpr›) -> KExpr {
    let w = whnf(e, types);
    match collect_spine(w) {
      (h, sp) =>
        match load(h) {
          KExprNode.Const(addr, lvls) =>
            match load(get_ci(addr)) {
              KConstantInfo.Thm(_, _, value) =>
                let body = expr_inst_levels(value, lvls);
                whnf_iota_major(whnf_with_spine(body, sp, types), types),
              _ => w,
            },
          _ => w,
        },
    }
  }

  -- Status codes returned by try_iota:
  --   1 = fired, use returned expr as reduced form (re-whnf)
  --   2 = stuck with major whnf'd, returned expr is the canonical
  --       stuck form — caller MUST NOT re-whnf (would infinite loop)
  --   0 = stuck without major work (major_idx >= spine_len)
  fn try_iota(lvls: List‹KLevel›, spine: List‹KExpr›,
                  nparams: G, nmotives: G, nminors: G, nindices: G,
                  rules: List‹KRecRule›, types: List‹KExpr›,
                  head: KExpr, rec_parent: Addr) -> (G, KExpr) {
    let major_idx = nparams + nmotives + nminors + nindices;
    let spine_len = list_length(spine);
    match u32_less_than(major_idx, spine_len) {
      0 => (0, store(KExprNode.BVar(0))),
      _ =>
        --  linear-rec fast path: `Nat.rec base (fun _ ih => succ ih) (Lit n)`
        -- collapses in O(1) to base+n / stuck offset, avoiding n iota expansions.
        let lin = try_nat_linear_rec(spine, nparams, nmotives, nminors, major_idx);
        match lin {
          (1, r) => (1, r),
          _ =>
        let raw_major = list_lookup(spine, major_idx);
        --  cleanup: expose one Nat.succ layer if major is
        -- `Nat.add base (Lit n)` with n>0, so iota can fire without
        -- unfolding into n unary succs.
        let major_clean1 = cleanup_nat_offset_major(raw_major);
        let major_w = whnf_iota_major(major_clean1, types);
        let major_clean2 = cleanup_nat_offset_major(major_w);
        let major = nat_lit_to_ctor_or_self(major_clean2);
        match collect_spine_of_ctor(major) {
          (1, ctor_cidx, ctor_parent, ctor_args) =>
            -- The constructor must belong to the inductive THIS recursor
            -- eliminates. Rules are otherwise selected by index alone, so
            -- any inductive's constructor with a matching index fires a
            -- rule and the redex reduces to a branch of an unrelated
            -- eliminator. Lean matches on the constructor's name, which
            -- pins the inductive; this is the addr-first equivalent.
            --
            -- `rec_to_parent_addr` reads the parent off the recursor's
            -- own type (the major premise's head), and Aiur memoizes it
            -- per argument tuple, so the walk is paid once per recursor
            -- rather than once per reduction.
            assert_eq!(address_eq(ctor_parent, rec_parent), 1,
              "iota: major's constructor belongs to a different inductive");
            let rule = find_rule(rules, ctor_cidx);
            match rule {
              (0, _, _) =>
                -- No rule for this ctor — rebuild stuck with whnf'd major.
                let new_spine = replace_spine_major(spine, major_idx, major_w);
                (2, apply_spine(head, new_spine)),
              (1, rfields, rrhs) =>
                let rhs_lvled = expr_inst_levels(rrhs, lvls);
                let pmm_end = nparams + nmotives + nminors;
                let pmm = list_take(spine, pmm_end);
                let ctor_fields_len = list_length(ctor_args);
                let field_start = ctor_fields_len - rfields;
                let field_args = list_drop(ctor_args, field_start);
                let post_major = list_drop(spine, major_idx + 1);
                let r1 = apply_spine(rhs_lvled, pmm);
                let r2 = apply_spine(r1, field_args);
                let r3 = apply_spine(r2, post_major);
                (1, r3),
            },
          _ =>
            -- Major not a Ctor — stuck, but rebuild spine with whnf'd major
            -- so downstream def_eq compares against canonical stuck form.
            let new_spine = replace_spine_major(spine, major_idx, major_w);
            (2, apply_spine(head, new_spine)),
        },
        },
    }
  }

  -- Collect a Ctor application: returns (1, cidx, args) if head is
  -- Const(ctor_addr) with a Ctor KCI, else (0, 0, []).
  -- Also returns the constructor's PARENT inductive, as the address of
  -- its projection wrapper, so the caller can check that the constructor
  -- actually belongs to the recursor being reduced. Without that, rules
  -- are selected by index alone and any inductive's constructor with a
  -- matching index fires a rule. Lean matches on the constructor's name,
  -- which pins the inductive.
  fn collect_spine_of_ctor(e: KExpr) -> (G, G, Addr, List‹KExpr›) {
    match collect_spine(e) {
      (head, args) =>
        match load(head) {
          KExprNode.Const(addr, _) =>
            let ci = load(get_ci(addr));
            match ci {
              KConstantInfo.Ctor(_, _, block_addr, ind_idx, cidx, _, _, _) =>
                (1, cidx, compute_iprj_addr(block_addr, ind_idx), args),
              _ => (0, 0, store([0u8; 32]), store(ListNode.Nil)),
            },
          _ => (0, 0, store([0u8; 32]), store(ListNode.Nil)),
        },
    }
  }

  -- Find rule matching cidx: returns (1, nfields, rhs) or (0, 0, ...).
  fn find_rule(rules: List‹KRecRule›, cidx: G) -> (G, G, KExpr) {
    match load(rules) {
      ListNode.Nil => (0, 0, store(KExprNode.BVar(0))),
      ListNode.Cons(r, rest) =>
        match r {
          KRecRule.Mk(rcidx, nfields, rhs) =>
            match rcidx - cidx {
              0 => (1, nfields, rhs),
              _ => find_rule(rest, cidx),
            },
        },
    }
  }

  -- Helpers (thin wrappers around Core list ops with concrete type params
  -- to avoid monomorphization clash under toplevel).

  -- ==========================================================================
  -- Struct-eta iota (mirror try_struct_eta_iota, Kernel/Whnf.lean:708;
  -- Rust whnf.rs:1244-1301; Lean toCtorWhenStructure). When a
  -- single-rule recursor's major premise is stuck but the parent
  -- inductive is struct-like (1 ctor, 0 indices, non-recursive) and the
  -- major isn't Prop-typed, the major is definitionally `Ctor major.0
  -- major.1 ...` (structure eta), so fire the rule with field
  -- projections in place of ctor args.
  -- ==========================================================================
  fn try_struct_eta_iota(rec_ty: KExpr, lvls: List‹KLevel›,
                               spine: List‹KExpr›, nparams: G, nmotives: G,
                               nminors: G, nindices: G,
                               rules: List‹KRecRule›,
                               types: List‹KExpr›) -> (G, KExpr) {
    match load(rules) {
      ListNode.Nil => (0, store(KExprNode.BVar(0))),
      ListNode.Cons(r, rest) =>
        match load(rest) {
          ListNode.Cons(_, _) => (0, store(KExprNode.BVar(0))),
          ListNode.Nil =>
            match r {
              KRecRule.Mk(_, nf, rhs) =>
                let skip = ((nparams + nmotives) + nminors) + nindices;
                match se_parent_addr(rec_ty, skip) {
                  (0, _) => (0, store(KExprNode.BVar(0))),
                  (_, parent) =>
                    let ci = load(get_ci(parent));
                    match ci {
                      KConstantInfo.Induct(_, _, _, ind_nidx, num_ctors,
                                             _, _, _) =>
                        match num_ctors - 1 {
                          0 =>
                            match ind_nidx {
                              0 =>
                                match struct_is_rec(parent) {
                                  1 => (0, store(KExprNode.BVar(0))),
                                  _ =>
                                    let major = list_lookup(spine, skip);
                                    let major_ty = k_infer(major, types);
                                    match is_prop_type(major_ty, types) {
                                      1 => (0, store(KExprNode.BVar(0))),
                                      _ =>
                                        let rhs_inst = expr_inst_levels(rhs, lvls);
                                        let pmm = list_take(spine,
                                          (nparams + nmotives) + nminors);
                                        let after_pmm = apply_spine(rhs_inst, pmm);
                                        let with_projs = apply_n_projs(
                                          after_pmm, parent, major, nf, 0);
                                        let post = list_drop(spine, skip + 1);
                                        (1, apply_spine(with_projs, post)),
                                    },
                                },
                              _ => (0, store(KExprNode.BVar(0))),
                            },
                          _ => (0, store(KExprNode.BVar(0))),
                        },
                      _ => (0, store(KExprNode.BVar(0))),
                    },
                },
            },
        },
    }
  }

  -- Parse the recursor's parent inductive addr from its type: peel
  -- (params+motives+minors+indices) foralls, take the major-premise
  -- forall's dom, return its spine head Const addr.
  fn se_parent_addr(rec_ty: KExpr, skip: G) -> (G, Addr) {
    match skip {
      0 =>
        match load(rec_ty) {
          KExprNode.Forall(dom, _) =>
            match collect_spine(dom) {
              (h, _) =>
                match load(h) {
                  KExprNode.Const(a, _) => (1, a),
                  _ => (0, store([0u8; 32])),
                },
            },
          _ => (0, store([0u8; 32])),
        },
      _ =>
        match load(rec_ty) {
          KExprNode.Forall(_, body) => se_parent_addr(body, skip - 1),
          _ => (0, store([0u8; 32])),
        },
    }
  }

  fn apply_n_projs(head: KExpr, parent: Addr, major: KExpr,
                        n_fields: G, i: G) -> KExpr {
    match n_fields - i {
      0 => head,
      _ =>
        let p = store(KExprNode.Proj(parent, i, major));
        apply_n_projs(store(KExprNode.App(head, p)), parent, major,
          n_fields, i + 1),
    }
  }

  -- 1 iff the inductive at `parent` is recursive: any ctor field dom
  -- mentions a block-member addr (mirror computed_is_rec_ind,
  -- Inductive.lean:376). Unknown shapes conservatively report 1
  -- (recursive) so struct-eta refuses. Aiur-memoized per parent.
  fn struct_is_rec(parent: Addr) -> G {
    let ci = load(get_ci(parent));
    match ci {
      KConstantInfo.Induct(_, _, n_params, _, num_ctors, _, block, idx) =>
        let members = struct_block_member_addrs(parent, block);
        struct_scan_ctors(block, idx, num_ctors, n_params, members, 0),
      _ => 1,
    }
  }

  fn struct_block_member_addrs(parent: Addr, block: Addr) -> List‹Addr› {
    let c = load_verified_constant(block);
    match c {
      Constant.Mk(info, _, _, _) =>
        match info {
          ConstantInfo.Muts(members) => build_recur_addrs(members, block),
          _ => store(ListNode.Cons(parent, store(ListNode.Nil))),
        },
    }
  }

  fn struct_scan_ctors(block: Addr, idx: G, num_ctors: G, n_params: G,
                             members: List‹Addr›, c: G) -> G {
    match num_ctors - c {
      0 => 0,
      _ =>
        let cci = load(get_ci_cprj(block, idx, c));
        match cci {
          KConstantInfo.Ctor(_, cty, _, _, _, _, _, _) =>
            let after = se_peel_tol(cty, n_params);
            match se_scan_fields(after, members) {
              1 => 1,
              _ => struct_scan_ctors(block, idx, num_ctors, n_params,
                     members, c + 1),
            },
          _ => 1,
        },
    }
  }

  fn se_peel_tol(ty: KExpr, n: G) -> KExpr {
    match n {
      0 => ty,
      _ =>
        match load(ty) {
          KExprNode.Forall(_, body) => se_peel_tol(body, n - 1),
          _ => ty,
        },
    }
  }

  fn se_scan_fields(ty: KExpr, members: List‹Addr›) -> G {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        match se_mentions(dom, members) {
          1 => 1,
          _ => se_scan_fields(body, members),
        },
      _ => 0,
    }
  }

  fn se_mentions(e: KExpr, members: List‹Addr›) -> G {
    match load(e) {
      KExprNode.Const(a, _) => se_addr_in(a, members),
      KExprNode.App(f, x) =>
        match se_mentions(f, members) {
          1 => 1,
          _ => se_mentions(x, members),
        },
      KExprNode.Lam(t, b) =>
        match se_mentions(t, members) {
          1 => 1,
          _ => se_mentions(b, members),
        },
      KExprNode.Forall(t, b) =>
        match se_mentions(t, members) {
          1 => 1,
          _ => se_mentions(b, members),
        },
      KExprNode.Let(t, v, b) =>
        match se_mentions(t, members) {
          1 => 1,
          _ =>
            match se_mentions(v, members) {
              1 => 1,
              _ => se_mentions(b, members),
            },
        },
      KExprNode.Proj(_, _, inner) => se_mentions(inner, members),
      _ => 0,
    }
  }

  fn se_addr_in(a: Addr, xs: List‹Addr›) -> G {
    match load(xs) {
      ListNode.Nil => 0,
      ListNode.Cons(x, rest) =>
        match address_eq(a, x) {
          1 => 1,
          _ => se_addr_in(a, rest),
        },
    }
  }

  -- Fast path (mirror whnf): trivial whnf normal forms skip the
  -- spine machinery and memo row entirely.
  fn whnf(e: KExpr, types: List‹KExpr›) -> KExpr {
    match load(e) {
      KExprNode.Srt(_) => e,
      KExprNode.Lit(_) => e,
      KExprNode.Lam(_, _) => e,
      KExprNode.Forall(_, _) => e,
      KExprNode.BVar(_) => e,
      _ => whnf_core(e, ctx_trim(types, expr_lbr(e))),
    }
  }

  fn whnf_core(e: KExpr, types: List‹KExpr›) -> KExpr {
    whnf_with_spine(e, store(ListNode.Nil), types)
  }

  -- ============================================================================
  -- whnf_nd: WHNF without delta-unfolding. Mirror whnf_nd
  -- crates/kernel/src / Rust whnf.rs::whnf_no_delta.
  --
  -- Same dispatch tree as whnf, but the Defn/Thm arms of the const
  -- head return the stuck application instead of unfolding. Beta / zeta /
  -- iota / proj / quot / primitives still fire — they don't need delta.
  --
  -- Used by def_eq's Tier 1d structural pre-check: many comparisons
  -- settle at no-delta whnf + ptr_eq or quick structural compare,
  -- avoiding the cascading full-delta unfold of large Defn bodies.
  -- ============================================================================
  fn whnf_nd(e: KExpr, types: List‹KExpr›) -> KExpr {
    match load(e) {
      KExprNode.Srt(_) => e,
      KExprNode.Lit(_) => e,
      KExprNode.Lam(_, _) => e,
      KExprNode.Forall(_, _) => e,
      KExprNode.BVar(_) => e,
      _ => whnf_nd_core(e, ctx_trim(types, expr_lbr(e))),
    }
  }

  fn whnf_nd_core(e: KExpr, types: List‹KExpr›) -> KExpr {
    whnf_nd_with_spine(e, store(ListNode.Nil), types)
  }

  fn whnf_nd_with_spine(head: KExpr, spine: List‹KExpr›,
                            types: List‹KExpr›) -> KExpr {
    match load(head) {
      KExprNode.App(f, a) =>
        match collect_spine(head) {
          (inner_head, inner_spine) =>
            whnf_nd_with_spine(inner_head, list_concat(inner_spine, spine), types),
        },
      KExprNode.Lam(ty, body) =>
        whnf_nd_apply_beta(spine, head, types),
      KExprNode.Const(addr, lvls) =>
        whnf_nd_const_head(addr, lvls, head, spine, types),
      KExprNode.Let(_, val, body) =>
        let next = expr_inst1(body, val, 0);
        whnf_nd_with_spine(next, spine, types),
      KExprNode.Proj(struct_addr, fidx, inner) =>
        whnf_nd_proj_head(struct_addr, fidx, inner, spine, types),
      _ => apply_spine(head, spine),
    }
  }

  fn whnf_nd_apply_beta(spine: List‹KExpr›, lam: KExpr,
                            types: List‹KExpr›) -> KExpr {
    match peel_beta(lam, spine, store(ListNode.Nil)) {
      (deep, consumed, rest) =>
        match list_length(consumed) {
          0 => apply_spine(lam, spine),
          1 =>
            let body2 = expr_inst1(deep, list_lookup(consumed, 0), 0);
            whnf_nd_with_spine(body2, rest, types),
          _ =>
            let body2 = expr_inst_many(deep, consumed, 0);
            whnf_nd_with_spine(body2, rest, types),
        },
    }
  }

  -- Proj head in no-delta mode: whnf_nd the scrutinee; ctor-field pull
  -- and the fin_val_decidable_rec push still apply.
  fn whnf_nd_proj_head(struct_addr: Addr, fidx: G, inner: KExpr,
                           spine: List‹KExpr›, types: List‹KExpr›) -> KExpr {
    let inner_whnf = whnf_nd(inner, types);
    -- Same Str-literal re-expansion as whnf_proj_head.
    let inner_exp = str_lit_to_ctor_app_or_self(inner_whnf, types);
    match collect_spine(inner_exp) {
      (inner_head, inner_args) =>
        match try_reduce_fin_val_decidable_rec(struct_addr, fidx,
                inner_head, inner_args) {
          (1, rewritten) => whnf_nd_with_spine(rewritten, spine, types),
          _ =>
            match load(inner_head) {
              KExprNode.Const(_, _) =>
                match load(whnf_get_ctor_or_none(inner_head)) {
                  KConstantInfo.Ctor(_, _, _, _, _, nparams, _, _) =>
                    let field = list_lookup(inner_args, nparams + fidx);
                    whnf_nd_with_spine(field, spine, types),
                  _ =>
                    let stuck = store(KExprNode.Proj(struct_addr, fidx, inner_whnf));
                    apply_spine(stuck, spine),
                },
              _ =>
                let stuck = store(KExprNode.Proj(struct_addr, fidx, inner_whnf));
                apply_spine(stuck, spine),
            },
        },
    }
  }

  -- Difference from whnf_const_head: Defn/Thm arms return the stuck
  -- application instead of unfolding. Iota, quot, primitives and the
  -- projection-definition shortcut still apply (proj-def reads the Defn
  -- value shape but never expands the body into the term).
  fn whnf_nd_const_head(addr: Addr, lvls: List‹KLevel›, head: KExpr,
                            spine: List‹KExpr›, types: List‹KExpr›) -> KExpr {
    let prim = try_prim_dispatch(addr, lvls, spine, types);
    match prim {
      (1, reduced) => whnf_nd(reduced, types),
      -- verdict 2: already-stuck compact form; do not re-whnf.
      (2, stuck) => stuck,
      _ =>
    let ci = load(get_ci(addr));
    match ci {
      KConstantInfo.Defn(_, _, value, _, _) =>
        let pd = try_reduce_projection_definition(value, spine);
        match pd {
          (1, reduced) => whnf_nd(reduced, types),
          _ => apply_spine(head, spine),
        },
      KConstantInfo.Quot(_, _, _) =>
        let quot = try_quot_iota(addr, spine, types);
        match quot {
          (1, reduced) => whnf_nd(reduced, types),
          _ => apply_spine(head, spine),
        },
      KConstantInfo.Rec(nlvls, rec_ty, nparams, nindices, nmotives, nminors,
                          rules, k_flag, _unsafe, _block, _ridx) =>
        let iota = try_iota(lvls, spine, nparams, nmotives, nminors,
                                 nindices, rules, types, head,
                                 rec_to_parent_addr(rec_ty, nparams, nmotives,
                                   nminors, nindices));
        match iota {
          (1, reduced) => whnf_nd(reduced, types),
          _ => apply_spine(head, spine),
        },
      _ => apply_spine(head, spine),
    },
    }
  }
⟧

end IxVM

end
