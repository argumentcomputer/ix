import Aiur.Modules.Function

/-! # IxVM module `Convert`

Conversion of Ixon constants to the kernel's constant info.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module Convert where

def bytes_to_u64_limb := aiur_fn⟦
  fn bytes_to_u64_limb(bytes: Bytes::Stream, acc: UInt64::U64, pos: Field) -> UInt64::U64 {
      match pos {
        8 => {  acc } ,
        _ => {
          match (*(bytes)) {
            Lists::Node::Nil => {  acc } ,
            Lists::Node::Cons(byte, rest) => {
              let [v0, v1, v2, v3, v4, v5, v6, v7] = acc;
              match pos {
                0 => {  bytes_to_u64_limb(rest, [byte, v1, v2, v3, v4, v5, v6, v7], 1) } ,
                1 => {  bytes_to_u64_limb(rest, [v0, byte, v2, v3, v4, v5, v6, v7], 2) } ,
                2 => {  bytes_to_u64_limb(rest, [v0, v1, byte, v3, v4, v5, v6, v7], 3) } ,
                3 => {  bytes_to_u64_limb(rest, [v0, v1, v2, byte, v4, v5, v6, v7], 4) } ,
                4 => {  bytes_to_u64_limb(rest, [v0, v1, v2, v3, byte, v5, v6, v7], 5) } ,
                5 => {  bytes_to_u64_limb(rest, [v0, v1, v2, v3, v4, byte, v6, v7], 6) } ,
                6 => {  bytes_to_u64_limb(rest, [v0, v1, v2, v3, v4, v5, byte, v7], 7) } ,
                _ => {  bytes_to_u64_limb(rest, [v0, v1, v2, v3, v4, v5, v6, byte], 8) } ,
              } } ,
          } } ,
      }
    }
⟧

def skip_bytes := aiur_fn⟦
  fn skip_bytes(bytes: Bytes::Stream, n: Field) -> Bytes::Stream {
      match n {
        0 => {  bytes } ,
        _ => {
          match (*(bytes)) {
            Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
            Lists::Node::Cons(_, rest) => {  skip_bytes(rest, n - 1) } ,
          } } ,
      }
    }
⟧

def bytes_to_limbs := aiur_fn⟦
  fn bytes_to_limbs(bytes: Bytes::Stream) -> KernelTypes::KLimbs {
      let limb = bytes_to_u64_limb(bytes, [UInt8::BYTE_0; 8], 0);
      let rest_bytes = skip_bytes(bytes, 8);
      let rest_limbs = match (*(rest_bytes)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        _ => {  bytes_to_limbs(rest_bytes) } ,
      };
      match (*(rest_limbs)) {
        Lists::Node::Nil => {
          match UInt64::is_zero(limb) {
            1 => {  (&(Lists::Node::Nil)) } ,
            0 => {  (&(Lists::Node::Cons(limb, (&(Lists::Node::Nil))))) } ,
          } } ,
        _ => {  (&(Lists::Node::Cons(limb, rest_limbs))) } ,
      }
    }
⟧

def convert_univ := aiur_fn⟦
  fn convert_univ(u: &Ixon::Univ) -> KernelTypes::KLevel {
      match (*(u)) {
        Ixon::Univ::Zero => {  (&(KernelTypes::KLevelNode::Zero)) } ,
        Ixon::Univ::Succ(inner) => {  (&(KernelTypes::KLevelNode::Succ(convert_univ(inner)))) } ,
        Ixon::Univ::Max(a, b) => {  (&(KernelTypes::KLevelNode::Max(convert_univ(a), convert_univ(b)))) } ,
        Ixon::Univ::IMax(a, b) => {  (&(KernelTypes::KLevelNode::IMax(convert_univ(a), convert_univ(b)))) } ,
        Ixon::Univ::Var(idx) => {  (&(KernelTypes::KLevelNode::Param(UInt64::to_field(idx)))) } ,
      }
    }
⟧

def convert_univ_idxs := aiur_fn⟦
  fn convert_univ_idxs(idxs: Lists::List<UInt64::U64>, univs: Lists::List<&Ixon::Univ>) -> Lists::List<KernelTypes::KLevel> {
      match (*(idxs)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(idx, rest) => {
          let u_ref = Lists::lookup(univs, UInt64::to_field(idx));
          (&(Lists::Node::Cons(convert_univ(u_ref), convert_univ_idxs(rest, univs)))) } ,
      }
    }
⟧

  -- Sharing in bounded form: `sharing` is the record's whole table, and `bound` the number of
  -- entries the expression may refer to. Entry `n` is converted with bound `n`, so it refers only
  -- to entries before it, and entry 0 to none (IxC's `MemberReader.mk'`). An entry is found by
  -- `Lists::drop` on the one table, whose calls all lookups share. (The earlier form converted
  -- entry `n` under `Lists::take(sharing, n)`, a new list per entry: quadratic, review K3-1.)
  --
  -- Binder data. Every `Lam` and `All` node carries its binder datum, read from the hint
  -- channel `ixvm.pw` (untrusted: the kernel's rules validate it at `Infer.lam` and
  -- `Infer.forallE`). A datum is keyed by `(rec, ekind, eidx, variant, ordinal)`: the record
  -- whose tables the expression is converted with, the entry (`(0, r)` the `r`-th root,
  -- `(1, n)` sharing entry `n`), the entry's variant (roots are converted at 0; a `Share`
  -- site reads the variant of its entry from `ixvm.pw.share`), and the node's position among
  -- the entry's `Lam`, `All` and `Share` nodes in pre-order (a `Share` is not entered).
  --
  -- `convert_expr` converts a tree without the key and returns, with the conversion, the
  -- tree's number of numbered nodes and whether it has a binder (through its shares). A tree
  -- without a binder needs no datum: its conversion is the one memoized here, shared by all
  -- its occurrences. A tree with a binder is converted by `convert_annotated` at its
  -- ordinal; for it the first component returned here is a placeholder, never used.

def convert_expr := aiur_fn⟦
  fn convert_expr(
      e: &Ixon::Expr,
      sharing: Lists::List<&Ixon::Expr>,
      bound: Field,
      refs: Lists::List<Bytes::AddressRef>,
      recur_addrs: Lists::List<Bytes::AddressRef>,
      univs: Lists::List<&Ixon::Univ>
    ) -> (KernelTypes::KExpr, Field, Field) {
      match (*(e)) {
        Ixon::Expr::Srt(univ_idx) => {
          let u_ref = Lists::lookup(univs, UInt64::to_field(univ_idx));
          ((&(KernelTypes::KExprNode::Srt(convert_univ(u_ref)))), 0, 0) } ,

        Ixon::Expr::Var(idx) => {
          ((&(KernelTypes::KExprNode::BVar(UInt64::to_field(idx)))), 0, 0) } ,

        Ixon::Expr::Ref(ref_idx, univ_idxs) => {
          let ref_addr = Lists::lookup(refs, UInt64::to_field(ref_idx));
          let levels = convert_univ_idxs(univ_idxs, univs);
          ((&(KernelTypes::KExprNode::Const(ref_addr, levels))), 0, 0) } ,

        Ixon::Expr::Rec(rec_idx, univ_idxs) => {

          let ref_addr = Lists::lookup(recur_addrs, UInt64::to_field(rec_idx));
          let levels = convert_univ_idxs(univ_idxs, univs);
          ((&(KernelTypes::KExprNode::Const(ref_addr, levels))), 0, 0) } ,

        Ixon::Expr::Prj(type_ref_idx, field_idx, inner) => {
          let (ki, ci, bi) = convert_expr(inner, sharing, bound, refs, recur_addrs, univs);
          match bi {
            0 => {
              let type_addr = Lists::lookup(refs, UInt64::to_field(type_ref_idx));
              ((&(KernelTypes::KExprNode::Proj(type_addr, UInt64::to_field(field_idx), ki))), ci, 0) } ,
            _ => {  (ki, ci, 1) } ,
          } } ,

        Ixon::Expr::Str(blob_ref_idx) => {
          let blob_addr = Lists::lookup(refs, UInt64::to_field(blob_ref_idx));
          let bs = Ingress::load_verified_blob(blob_addr);

          KernelNatPrim::utf8_validate(bs);
          ((&(KernelTypes::KExprNode::Lit(KernelTypes::KLiteral::Str(bs)))), 0, 0) } ,

        Ixon::Expr::Nat(blob_ref_idx) => {
          let blob_addr = Lists::lookup(refs, UInt64::to_field(blob_ref_idx));
          let bs = Ingress::load_verified_blob(blob_addr);
          let limbs = bytes_to_limbs(bs);
          ((&(KernelTypes::KExprNode::Lit(KernelTypes::KLiteral::Nat(limbs)))), 0, 0) } ,

        Ixon::Expr::App(f, a) => {
          let (kf, cf, bf) = convert_expr(f, sharing, bound, refs, recur_addrs, univs);
          let (ka, ca, ba) = convert_expr(a, sharing, bound, refs, recur_addrs, univs);
          match bf + ba {
            0 => {  ((&(KernelTypes::KExprNode::App(kf, ka))), cf + ca, 0) } ,
            _ => {  (kf, cf + ca, 1) } ,
          } } ,

        Ixon::Expr::Lam(_, ty, body) => {
          let (kt, ct, _bt) = convert_expr(ty, sharing, bound, refs, recur_addrs, univs);
          let (_kb, cb, _bb) = convert_expr(body, sharing, bound, refs, recur_addrs, univs);
          (kt, (ct + cb) + 1, 1) } ,

        Ixon::Expr::All(_, _, ty, body) => {
          let (kt, ct, _bt) = convert_expr(ty, sharing, bound, refs, recur_addrs, univs);
          let (_kb, cb, _bb) = convert_expr(body, sharing, bound, refs, recur_addrs, univs);
          (kt, (ct + cb) + 1, 1) } ,

        Ixon::Expr::Let(_, ty, val, body) => {
          let (kt, ct, bt) = convert_expr(ty, sharing, bound, refs, recur_addrs, univs);
          let (kv, cv, bv) = convert_expr(val, sharing, bound, refs, recur_addrs, univs);
          let (kb, cb, bb) = convert_expr(body, sharing, bound, refs, recur_addrs, univs);
          match (bt + bv) + bb {
            0 => {  ((&(KernelTypes::KExprNode::Let(kt, kv, kb))), (ct + cv) + cb, 0) } ,
            _ => {  (kt, (ct + cv) + cb, 1) } ,
          } } ,

        Ixon::Expr::Share(idx) => {
          let n = UInt64::to_field(idx);
          assert_eq!(UInt32::less_than_fields(n, bound), 1, "sharing reference is not to an earlier entry");
          let Lists::Node::Cons(s, _) = (*(Lists::drop(sharing, n)));
          let (ks, _cs, bs) = convert_expr(s, sharing, n, refs, recur_addrs, univs);
          (ks, 1, bs) } ,
      }
    }
⟧

  -- The datum of the binder at `(rec, ekind, eidx, variant, ord)` as a level:
  -- `never ↦ Succ(Zero)`, `ifAllZero [] ↦ Zero`, `ifAllZero [p₁…pₖ] ↦ Max(Param p₁, Max(…, Param pₖ))`.

def read_pw := aiur_fn⟦
  fn read_pw(rec: Bytes::AddressRef, ekind: Field, eidx: Field, variant: Field, ord: Field) -> KernelTypes::KLevel {
      let c = hint::<Field>("ixvm.pw", (Blake3::address_to_fields((*(rec))), ekind, eidx, variant, ord));
      match c {
        0 => {  (&(KernelTypes::KLevelNode::Succ((&(KernelTypes::KLevelNode::Zero))))) } ,
        1 => {  (&(KernelTypes::KLevelNode::Zero)) } ,
        _ => {  pw_params(rec, ekind, eidx, variant, ord, c - 1, 0) } ,
      }
    }
⟧

def pw_params := aiur_fn⟦
  fn pw_params(rec: Bytes::AddressRef, ekind: Field, eidx: Field, variant: Field, ord: Field,
               k: Field, j: Field) -> KernelTypes::KLevel {
      let p = hint::<Field>("ixvm.pw.param", (Blake3::address_to_fields((*(rec))), ekind, eidx, variant, ord, j));
      let lp = (&(KernelTypes::KLevelNode::Param(p)));
      match (k - j) - 1 {
        0 => {  lp } ,
        _ => {  (&(KernelTypes::KLevelNode::Max(lp, pw_params(rec, ekind, eidx, variant, ord, k, j + 1)))) } ,
      }
    }
⟧

  -- The variant the entry of the share site at `(rec, ekind, eidx, variant, ord)` is converted with.

def read_pw_share := aiur_fn⟦
  fn read_pw_share(rec: Bytes::AddressRef, ekind: Field, eidx: Field, variant: Field, ord: Field) -> Field {
      hint::<Field>("ixvm.pw.share", (Blake3::address_to_fields((*(rec))), ekind, eidx, variant, ord))
    }
⟧

  -- A tree with a binder (through its shares), its first numbered node at ordinal `ord`.

def convert_annotated := aiur_fn⟦
  fn convert_annotated(
      e: &Ixon::Expr,
      sharing: Lists::List<&Ixon::Expr>,
      bound: Field,
      refs: Lists::List<Bytes::AddressRef>,
      recur_addrs: Lists::List<Bytes::AddressRef>,
      univs: Lists::List<&Ixon::Univ>,
      rec: Bytes::AddressRef, ekind: Field, eidx: Field, variant: Field, ord: Field
    ) -> KernelTypes::KExpr {
      match (*(e)) {
        Ixon::Expr::App(f, a) => {
          let (kf, cf, bf) = convert_expr(f, sharing, bound, refs, recur_addrs, univs);
          let (ka, _ca, ba) = convert_expr(a, sharing, bound, refs, recur_addrs, univs);
          let kf2 = match bf {
            0 => {  kf } ,
            _ => {  convert_annotated(f, sharing, bound, refs, recur_addrs, univs, rec, ekind, eidx, variant, ord) } ,
          };
          let ka2 = match ba {
            0 => {  ka } ,
            _ => {  convert_annotated(a, sharing, bound, refs, recur_addrs, univs, rec, ekind, eidx, variant, ord + cf) } ,
          };
          (&(KernelTypes::KExprNode::App(kf2, ka2))) } ,

        Ixon::Expr::Lam(_, ty, body) => {
          let l = read_pw(rec, ekind, eidx, variant, ord);
          let (kt, ct, bt) = convert_expr(ty, sharing, bound, refs, recur_addrs, univs);
          let (kb, _cb, bb) = convert_expr(body, sharing, bound, refs, recur_addrs, univs);
          let kt2 = match bt {
            0 => {  kt } ,
            _ => {  convert_annotated(ty, sharing, bound, refs, recur_addrs, univs, rec, ekind, eidx, variant, ord + 1) } ,
          };
          let kb2 = match bb {
            0 => {  kb } ,
            _ => {  convert_annotated(body, sharing, bound, refs, recur_addrs, univs, rec, ekind, eidx, variant, (ord + 1) + ct) } ,
          };
          (&(KernelTypes::KExprNode::Lam(kt2, kb2, l))) } ,

        Ixon::Expr::All(_, _, ty, body) => {
          let l = read_pw(rec, ekind, eidx, variant, ord);
          let (kt, ct, bt) = convert_expr(ty, sharing, bound, refs, recur_addrs, univs);
          let (kb, _cb, bb) = convert_expr(body, sharing, bound, refs, recur_addrs, univs);
          let kt2 = match bt {
            0 => {  kt } ,
            _ => {  convert_annotated(ty, sharing, bound, refs, recur_addrs, univs, rec, ekind, eidx, variant, ord + 1) } ,
          };
          let kb2 = match bb {
            0 => {  kb } ,
            _ => {  convert_annotated(body, sharing, bound, refs, recur_addrs, univs, rec, ekind, eidx, variant, (ord + 1) + ct) } ,
          };
          (&(KernelTypes::KExprNode::Forall(kt2, kb2, l))) } ,

        Ixon::Expr::Let(_, ty, val, body) => {
          let (kt, ct, bt) = convert_expr(ty, sharing, bound, refs, recur_addrs, univs);
          let (kv, cv, bv) = convert_expr(val, sharing, bound, refs, recur_addrs, univs);
          let (kb, _cb, bb) = convert_expr(body, sharing, bound, refs, recur_addrs, univs);
          let kt2 = match bt {
            0 => {  kt } ,
            _ => {  convert_annotated(ty, sharing, bound, refs, recur_addrs, univs, rec, ekind, eidx, variant, ord) } ,
          };
          let kv2 = match bv {
            0 => {  kv } ,
            _ => {  convert_annotated(val, sharing, bound, refs, recur_addrs, univs, rec, ekind, eidx, variant, ord + ct) } ,
          };
          let kb2 = match bb {
            0 => {  kb } ,
            _ => {  convert_annotated(body, sharing, bound, refs, recur_addrs, univs, rec, ekind, eidx, variant, (ord + ct) + cv) } ,
          };
          (&(KernelTypes::KExprNode::Let(kt2, kv2, kb2))) } ,

        Ixon::Expr::Prj(type_ref_idx, field_idx, inner) => {
          let type_addr = Lists::lookup(refs, UInt64::to_field(type_ref_idx));
          (&(KernelTypes::KExprNode::Proj(
            type_addr,
            UInt64::to_field(field_idx),
            convert_annotated(inner, sharing, bound, refs, recur_addrs, univs, rec, ekind, eidx, variant, ord)))) } ,

        Ixon::Expr::Share(idx) => {
          let n = UInt64::to_field(idx);
          let Lists::Node::Cons(s, _) = (*(Lists::drop(sharing, n)));
          let v = read_pw_share(rec, ekind, eidx, variant, ord);
          convert_annotated(s, sharing, n, refs, recur_addrs, univs, rec, 1, n, v, 0) } ,
      }
    }
⟧

  -- A root expression of a record may refer to every sharing entry. Its bound is the largest
  -- `u32`: `Lists::drop` refuses an index past the table, and a table is shorter than its
  -- record's byte stream, whose length `IxByteStream::read_finite_byte_stream` checks below
  -- 2^32 - 1, so the comparison never refuses an index that `drop` accepts. Root `r` of the
  -- record `rec` is the entry `(0, r)`, converted at variant 0.

def convert_root := aiur_fn⟦
  inline fn convert_root(
      e: &Ixon::Expr,
      sharing: Lists::List<&Ixon::Expr>,
      refs: Lists::List<Bytes::AddressRef>,
      recur_addrs: Lists::List<Bytes::AddressRef>,
      univs: Lists::List<&Ixon::Univ>,
      rec: Bytes::AddressRef, r: Field
    ) -> KernelTypes::KExpr {
      let (k, _c, b) = convert_expr(e, sharing, 4294967295, refs, recur_addrs, univs);
      match b {
        0 => {  k } ,
        _ => {  convert_annotated(e, sharing, 4294967295, refs, recur_addrs, univs, rec, 0, r, 0, 0) } ,
      }
    }
⟧

  -- The number of root expressions a block member contributes (its roots are numbered
  -- consecutively across the block): a definition's type and value, an inductive's type
  -- and its constructors' types, a recursor's type and its rules' right-hand sides.

def mut_const_roots := aiur_fn⟦
  fn mut_const_roots(m: Ixon::MutConst) -> Field {
      match m {
        Ixon::MutConst::Defn(_) => {  2 } ,
        Ixon::MutConst::Indc(ind) => {
          match ind {
            Ixon::Inductive::Mk(_, _, _, _, _, ctors) => {  count_ctors(ctors) + 1 } ,
          } } ,
        Ixon::MutConst::Recr(r) => {
          match r {
            Ixon::Recursor::Mk(_, _, _, _, _, _, _, _, rules) => {  Lists::length(rules) + 1 } ,
          } } ,
      }
    }
⟧

  -- The index of member `idx`'s first root in its block.

def muts_root_offset := aiur_fn⟦
  fn muts_root_offset(members: Lists::List<Ixon::MutConst>, idx: Field) -> Field {
      match idx {
        0 => {  0 } ,
        _ => {
          match (*(members)) {
            Lists::Node::Cons(m, rest) => {  mut_const_roots(m) + muts_root_offset(rest, idx - 1) } ,
          } } ,
      }
    }
⟧

  -- A constant's level-parameter count, below 2^32: its four high bytes are zero.

def lvls_to_field := aiur_fn⟦
  fn lvls_to_field(lvls: UInt64::U64) -> Field {
      let [b0, b1, b2, b3, b4, b5, b6, b7] = lvls;
      assert_eq!(UInt8::to_field(b4), 0, "a level-parameter count is 2^32 or more");
      assert_eq!(UInt8::to_field(b5), 0, "a level-parameter count is 2^32 or more");
      assert_eq!(UInt8::to_field(b6), 0, "a level-parameter count is 2^32 or more");
      assert_eq!(UInt8::to_field(b7), 0, "a level-parameter count is 2^32 or more");
      UInt8::to_field(b0) + 256 * UInt8::to_field(b1) + 65536 * UInt8::to_field(b2)
        + 16777216 * UInt8::to_field(b3)
    }
⟧

def convert_definition := aiur_fn⟦
  fn convert_definition(d: Ixon::Definition, sharing: Lists::List<&Ixon::Expr>,
                              refs: Lists::List<Bytes::AddressRef>, recur_addrs: Lists::List<Bytes::AddressRef>,
                              univs: Lists::List<&Ixon::Univ>, hint: Field,
                              rec: Bytes::AddressRef, base: Field) -> KernelTypes::KConstantInfo {
      match d {
        Ixon::Definition::Mk(kind, safety, lvls, typ, value) => {
          let ktyp = convert_root(typ, sharing, refs, recur_addrs, univs, rec, base);
          let kval = convert_root(value, sharing, refs, recur_addrs, univs, rec, base + 1);
          let nlvls = lvls_to_field(lvls);
          match kind {
            Ixon::DefKind::Definition => {
              KernelTypes::KConstantInfo::Defn(nlvls, ktyp, kval, safety, hint) } ,
            Ixon::DefKind::Opaque => {
              let is_unsafe = match safety { Ixon::DefinitionSafety::Unsafe => {  1 } , _ => {  0 } , };
              KernelTypes::KConstantInfo::Opaque(nlvls, ktyp, kval, is_unsafe) } ,
            Ixon::DefKind::Theorem => {
              KernelTypes::KConstantInfo::Thm(nlvls, ktyp, kval) } ,
          } } ,
      }
    }
⟧

def convert_axiom := aiur_fn⟦
  fn convert_axiom(a: Ixon::Axiom, sharing: Lists::List<&Ixon::Expr>,
                         refs: Lists::List<Bytes::AddressRef>, recur_addrs: Lists::List<Bytes::AddressRef>,
                         univs: Lists::List<&Ixon::Univ>, rec: Bytes::AddressRef) -> KernelTypes::KConstantInfo {
      match a {
        Ixon::Axiom::Mk(is_unsafe, lvls, typ) => {
          let ktyp = convert_root(typ, sharing, refs, recur_addrs, univs, rec, 0);
          KernelTypes::KConstantInfo::Axiom(lvls_to_field(lvls), ktyp, is_unsafe) } ,
      }
    }
⟧

def convert_quotient := aiur_fn⟦
  fn convert_quotient(q: Ixon::Quotient, sharing: Lists::List<&Ixon::Expr>,
                            refs: Lists::List<Bytes::AddressRef>, recur_addrs: Lists::List<Bytes::AddressRef>,
                            univs: Lists::List<&Ixon::Univ>, rec: Bytes::AddressRef) -> KernelTypes::KConstantInfo {
      match q {
        Ixon::Quotient::Mk(kind, lvls, typ) => {
          let ktyp = convert_root(typ, sharing, refs, recur_addrs, univs, rec, 0);
          KernelTypes::KConstantInfo::Quot(lvls_to_field(lvls), ktyp, kind) } ,
      }
    }
⟧

def count_ctors := aiur_fn⟦
  fn count_ctors(cs: Lists::List<Ixon::Constructor>) -> Field {
      match (*(cs)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(_, rest) => {  count_ctors(rest) + 1 } ,
      }
    }
⟧

def ctor_at := aiur_fn⟦
  fn ctor_at(cs: Lists::List<Ixon::Constructor>, cidx: Field) -> Ixon::Constructor {
      match (*(cs)) {
        Lists::Node::Cons(c, rest) => {
          match cidx {
            0 => {  c } ,
            _ => {  ctor_at(rest, cidx - 1) } ,
          } } ,
      }
    }
⟧

def convert_inductive := aiur_fn⟦
  fn convert_inductive(ind: Ixon::Inductive, block_addr: Bytes::AddressRef, ind_idx: Field,
                             sharing: Lists::List<&Ixon::Expr>, refs: Lists::List<Bytes::AddressRef>,
                             recur_addrs: Lists::List<Bytes::AddressRef>,
                             univs: Lists::List<&Ixon::Univ>, base: Field) -> KernelTypes::KConstantInfo {
      match ind {
        Ixon::Inductive::Mk(is_unsafe, lvls, params, indices, typ, ctors) => {
          let ktyp = convert_root(typ, sharing, refs, recur_addrs, univs, block_addr, base);
          KernelTypes::KConstantInfo::Induct(
            lvls_to_field(lvls), ktyp,
            UInt64::to_field(params), UInt64::to_field(indices),
            count_ctors(ctors), is_unsafe,
            block_addr, ind_idx) } ,
      }
    }
⟧

def convert_constructor := aiur_fn⟦
  fn convert_constructor(c: Ixon::Constructor, block_addr: Bytes::AddressRef, ind_idx: Field,
                               sharing: Lists::List<&Ixon::Expr>, refs: Lists::List<Bytes::AddressRef>,
                               recur_addrs: Lists::List<Bytes::AddressRef>,
                               univs: Lists::List<&Ixon::Univ>, base: Field) -> KernelTypes::KConstantInfo {
      match c {
        Ixon::Constructor::Mk(is_unsafe, lvls, cidx, params, fields, typ) => {
          let ktyp = convert_root(typ, sharing, refs, recur_addrs, univs, block_addr, base);
          KernelTypes::KConstantInfo::Ctor(
            lvls_to_field(lvls), ktyp,
            block_addr, ind_idx, UInt64::to_field(cidx),
            UInt64::to_field(params), UInt64::to_field(fields), is_unsafe) } ,
      }
    }
⟧

def convert_rec_rules := aiur_fn⟦
  fn convert_rec_rules(rs: Lists::List<Ixon::RecursorRule>, sharing: Lists::List<&Ixon::Expr>,
                             refs: Lists::List<Bytes::AddressRef>, recur_addrs: Lists::List<Bytes::AddressRef>,
                             univs: Lists::List<&Ixon::Univ>, cidx: Field,
                             rec: Bytes::AddressRef, ridx: Field) -> Lists::List<KernelTypes::KRecRule> {
      match (*(rs)) {
        Lists::Node::Nil => {
          (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(r, rest) => {
          match r {
            Ixon::RecursorRule::Mk(fields, rhs) => {
              let krhs = convert_root(rhs, sharing, refs, recur_addrs, univs, rec, ridx);
              (&(Lists::Node::Cons(
                KernelTypes::KRecRule::Mk(cidx, UInt64::to_field(fields), krhs),
                convert_rec_rules(rest, sharing, refs, recur_addrs, univs, cidx + 1, rec, ridx + 1)))) } ,
          } } ,
      }
    }
⟧

def convert_recursor := aiur_fn⟦
  fn convert_recursor(r: Ixon::Recursor, block_addr: Bytes::AddressRef, rec_idx: Field,
                            sharing: Lists::List<&Ixon::Expr>, refs: Lists::List<Bytes::AddressRef>,
                            recur_addrs: Lists::List<Bytes::AddressRef>,
                            univs: Lists::List<&Ixon::Univ>, base: Field) -> KernelTypes::KConstantInfo {
      match r {
        Ixon::Recursor::Mk(k, is_unsafe, lvls, params, indices, motives, minors, typ, rules) => {
          -- The type is read with no recursive reference in scope: a recursor's type never
          -- mentions its own family (the kernel checks it before the family is installed); only
          -- its rules call the family's recursors.
          let ktyp = convert_root(typ, sharing, refs, (&(Lists::Node::Nil)), univs, block_addr, base);
          let krules = convert_rec_rules(rules, sharing, refs, recur_addrs, univs, 0, block_addr, base + 1);
          KernelTypes::KConstantInfo::Rec(
            lvls_to_field(lvls), ktyp,
            UInt64::to_field(params), UInt64::to_field(indices),
            UInt64::to_field(motives), UInt64::to_field(minors),
            krules, k, is_unsafe,
            block_addr, rec_idx) } ,
      }
    }
⟧

end

end IxVM
