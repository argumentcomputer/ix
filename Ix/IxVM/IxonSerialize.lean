import Ix.Aiur.Meta

namespace IxVM

def ixonSerialize := ⟦
  fn put_expr(expr: Expr, rest: ByteStream) -> ByteStream {
    match expr {
      -- Srt: Tag4(0x0, univ_idx)
      Expr.Srt(univ_idx) => put_tag4(0x0, univ_idx, rest),

      -- Var: Tag4(0x1, idx)
      Expr.Var(idx) => put_tag4(0x1, idx, rest),

      -- Ref: Tag4(0x2, len) + Tag0(ref_idx) + univ_list
      Expr.Ref(ref_idx, &univ_list) =>
        let len = u64_list_length(univ_list);
        put_tag4(0x2, len, put_tag0(ref_idx, put_u64_list(univ_list, rest))),

      -- Rec: Tag4(0x3, len) + Tag0(rec_idx) + univ_list
      Expr.Rec(rec_idx, &univ_list) =>
        let len = u64_list_length(univ_list);
        put_tag4(0x3, len, put_tag0(rec_idx, put_u64_list(univ_list, rest))),

      -- Prj: Tag4(0x4, field_idx) + Tag0(type_ref_idx) + put_expr(val)
      Expr.Prj(type_ref_idx, field_idx, &val) =>
        put_tag4(0x4, field_idx, put_tag0(type_ref_idx, put_expr(val, rest))),

      -- Str: Tag4(0x5, ref_idx)
      Expr.Str(ref_idx) => put_tag4(0x5, ref_idx, rest),

      -- Nat: Tag4(0x6, ref_idx)
      Expr.Nat(ref_idx) => put_tag4(0x6, ref_idx, rest),

      -- App: Tag4(0x7, count) + telescope
      Expr.App(_, _) =>
        let count = app_telescope_count(expr);
        put_tag4(0x7, count, put_app_telescope(expr, rest)),

      -- Lam: Tag4(0x8, count) + telescope
      Expr.Lam(_, _) =>
        let count = lam_telescope_count(expr);
        put_tag4(0x8, count, put_lam_telescope(expr, rest)),

      -- All: Tag4(0x9, count) + telescope
      Expr.All(_, _) =>
        let count = all_telescope_count(expr);
        put_tag4(0x9, count, put_all_telescope(expr, rest)),

      -- Let: Tag4(0xA, non_dep) + put_expr(ty) + put_expr(val) + put_expr(body)
      -- non_dep: 0 for dependent, 1 for non-dependent
      Expr.Let(non_dep, &ty, &val, &body) =>
        put_tag4(0xA, non_dep, put_expr(ty, put_expr(val, put_expr(body, rest)))),

      -- Share: Tag4(0xB, idx)
      Expr.Share(idx) => put_tag4(0xB, idx, rest),
    }
  }

  fn put_u64_le(bs: [G; 8], num_bytes: G, rest: ByteStream) -> ByteStream {
    match num_bytes {
      0 => rest,
      _ =>
        let [b1, b2, b3, b4, b5, b6, b7, b8] = bs;
        let rest_shifted = [b2, b3, b4, b5, b6, b7, b8, 0];
        ByteStream.Cons(b1, store(put_u64_le(rest_shifted, num_bytes - 1, rest))),
    }
  }

  fn put_tag0(bs: [G; 8], rest: ByteStream) -> ByteStream {
    let byte_count = u64_byte_count(bs);
    let small = u8_less_than(bs[0], 128);
    match (byte_count, small) {
      (1, 1) => ByteStream.Cons(bs[0], store(rest)),
      _ =>
        let head = 128 + (byte_count - 1);
        ByteStream.Cons(head, store(put_u64_le(bs, byte_count, rest))),
    }
  }

  fn put_tag4(flag: G, bs: [G; 8], rest: ByteStream) -> ByteStream {
    let byte_count = u64_byte_count(bs);
    let small = u8_less_than(bs[0], 8);
    match (byte_count, small) {
      (1, 1) =>
        let head = flag * 16 + bs[0];
        ByteStream.Cons(head, store(rest)),
      _ =>
        let head = flag * 16 + 8 + (byte_count - 1);
        ByteStream.Cons(head, store(put_u64_le(bs, byte_count, rest))),
    }
  }

  -- Serialize field list (each element as Tag0)
  fn put_u64_list(list: U64List, rest: ByteStream) -> ByteStream {
    match list {
      U64List.Nil => rest,
      U64List.Cons(idx, rest_list) =>
        put_tag0(idx, put_u64_list(load(rest_list), rest)),
    }
  }

  -- Count nested App expressions
  fn app_telescope_count(expr: Expr) -> [G; 8] {
    match expr {
      Expr.App(&func, _) => relaxed_u64_succ(app_telescope_count(func)),
      _ => [0; 8],
    }
  }

  -- Count nested Lam expressions
  fn lam_telescope_count(expr: Expr) -> [G; 8] {
    match expr {
      Expr.Lam(_, &body) => relaxed_u64_succ(lam_telescope_count(body)),
      _ => [0; 8],
    }
  }

  -- Count nested All expressions
  fn all_telescope_count(expr: Expr) -> [G; 8] {
    match expr {
      Expr.All(_, &body) => relaxed_u64_succ(all_telescope_count(body)),
      _ => [0; 8],
    }
  }

  -- Serialize App telescope body (function, then all args in order)
  fn put_app_telescope(expr: Expr, rest: ByteStream) -> ByteStream {
    match expr {
      Expr.App(&func, &arg) =>
        put_app_telescope(func, put_expr(arg, rest)),
      _ => put_expr(expr, rest),
    }
  }

  -- Serialize Lam telescope body (all types, then body)
  fn put_lam_telescope(expr: Expr, rest: ByteStream) -> ByteStream {
    match expr {
      Expr.Lam(&ty, &body) =>
        put_expr(ty, put_lam_telescope(body, rest)),
      _ => put_expr(expr, rest),
    }
  }

  -- Serialize All telescope body (all types, then body)
  fn put_all_telescope(expr: Expr, rest: ByteStream) -> ByteStream {
    match expr {
      Expr.All(&ty, &body) =>
        put_expr(ty, put_all_telescope(body, rest)),
      _ => put_expr(expr, rest),
    }
  }
⟧

end IxVM
