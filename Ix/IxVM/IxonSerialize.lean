import Ix.Aiur.Meta

namespace IxVM

def ixonSerialize := ⟦
  fn put_expr(expr: Expr) -> ByteStream {
    match expr {
      -- Srt: Tag4(0x0, univ_idx)
      Expr.Srt(univ_idx) => put_tag4(0x0, univ_idx),

      -- Var: Tag4(0x1, idx)
      Expr.Var(idx) => put_tag4(0x1, idx),

      -- Ref: Tag4(0x2, len) + Tag0(ref_idx) + univ_list
      Expr.Ref(ref_idx, &univ_list) =>
        let len = u64_list_length(univ_list);
        let tag = put_tag4(0x2, len);
        let ref_bytes = put_tag0(ref_idx);
        let univ_bytes = put_u64_list(univ_list);
        byte_stream_concat(tag, byte_stream_concat(ref_bytes, univ_bytes)),

      -- Rec: Tag4(0x3, len) + Tag0(rec_idx) + univ_list
      Expr.Rec(rec_idx, &univ_list) =>
        let len = u64_list_length(univ_list);
        let tag = put_tag4(0x3, len);
        let rec_bytes = put_tag0(rec_idx);
        let univ_bytes = put_u64_list(univ_list);
        byte_stream_concat(tag, byte_stream_concat(rec_bytes, univ_bytes)),

      -- Prj: Tag4(0x4, field_idx) + Tag0(type_ref_idx) + put_expr(val)
      Expr.Prj(type_ref_idx, field_idx, &val) =>
        let tag = put_tag4(0x4, field_idx);
        let type_bytes = put_tag0(type_ref_idx);
        let val_bytes = put_expr(val);
        byte_stream_concat(tag, byte_stream_concat(type_bytes, val_bytes)),

      -- Str: Tag4(0x5, ref_idx)
      Expr.Str(ref_idx) => put_tag4(0x5, ref_idx),

      -- Nat: Tag4(0x6, ref_idx)
      Expr.Nat(ref_idx) => put_tag4(0x6, ref_idx),

      -- App: Tag4(0x7, count) + telescope
      Expr.App(_, _) =>
        let count = app_telescope_count(expr);
        let tag = put_tag4(0x7, count);
        let telescope = put_app_telescope(expr);
        byte_stream_concat(tag, telescope),

      -- Lam: Tag4(0x8, count) + telescope
      Expr.Lam(_, _) =>
        let count = lam_telescope_count(expr);
        let tag = put_tag4(0x8, count);
        let telescope = put_lam_telescope(expr);
        byte_stream_concat(tag, telescope),

      -- All: Tag4(0x9, count) + telescope
      Expr.All(_, _) =>
        let count = all_telescope_count(expr);
        let tag = put_tag4(0x9, count);
        let telescope = put_all_telescope(expr);
        byte_stream_concat(tag, telescope),

      -- Let: Tag4(0xA, non_dep) + put_expr(ty) + put_expr(val) + put_expr(body)
      -- non_dep: 0 for dependent, 1 for non-dependent
      Expr.Let(non_dep, &ty, &val, &body) =>
        let tag = put_tag4(0xA, non_dep);
        let ty_bytes = put_expr(ty);
        let val_bytes = put_expr(val);
        let body_bytes = put_expr(body);
        byte_stream_concat(
          tag,
          byte_stream_concat(
            ty_bytes,
            byte_stream_concat(val_bytes, body_bytes)
          )
        ),

      -- Share: Tag4(0xB, idx)
      Expr.Share(idx) => put_tag4(0xB, idx),
    }
  }

  fn put_u64_le(bs: [G; 8], num_bytes: G) -> ByteStream {
    match num_bytes {
      0 => ByteStream.Nil,
      _ =>
        let [b1, b2, b3, b4, b5, b6, b7, b8] = bs;
        let rest = [b2, b3, b4, b5, b6, b7, b8, 0];
        ByteStream.Cons(b1, store(put_u64_le(rest, num_bytes - 1))),
    }
  }

  fn put_tag0(bs: [G; 8]) -> ByteStream {
    let byte_count = u64_byte_count(bs);
    let small = u8_less_than(bs[0], 128);
    match (byte_count, small) {
      (1, 1) => ByteStream.Cons(bs[0], store(ByteStream.Nil)),
      _ =>
        let head = 128 + (byte_count - 1);
        ByteStream.Cons(head, store(put_u64_le(bs, byte_count))),
    }
  }

  fn put_tag4(flag: G, bs: [G; 8]) -> ByteStream {
    let byte_count = u64_byte_count(bs);
    let small = u8_less_than(bs[0], 8);
    match (byte_count, small) {
      (1, 1) =>
        let head = flag * 16 + bs[0];
        ByteStream.Cons(head, store(ByteStream.Nil)),
      _ =>
        let head = flag * 16 + 8 + (byte_count - 1);
        let bs_bytes = put_u64_le(bs, byte_count);
        ByteStream.Cons(head, store(bs_bytes)),
    }
  }

  -- Serialize field list (each element as Tag0)
  fn put_u64_list(list: U64List) -> ByteStream {
    match list {
      U64List.Nil => ByteStream.Nil,
      U64List.Cons(idx, rest) =>
        let idx_bytes = put_tag0(idx);
        let rest_bytes = put_u64_list(load(rest));
        byte_stream_concat(idx_bytes, rest_bytes),
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
  fn put_app_telescope(expr: Expr) -> ByteStream {
    match expr {
      Expr.App(&func, &arg) =>
        let func_bytes = put_app_telescope(func);
        let arg_bytes = put_expr(arg);
        byte_stream_concat(func_bytes, arg_bytes),
      _ => put_expr(expr),
    }
  }

  -- Serialize Lam telescope body (all types, then body)
  fn put_lam_telescope(expr: Expr) -> ByteStream {
    match expr {
      Expr.Lam(&ty, &body) =>
        let ty_bytes = put_expr(ty);
        let rest_bytes = put_lam_telescope(body);
        byte_stream_concat(ty_bytes, rest_bytes),
      _ => put_expr(expr),
    }
  }

  -- Serialize All telescope body (all types, then body)
  fn put_all_telescope(expr: Expr) -> ByteStream {
    match expr {
      Expr.All(&ty, &body) =>
        let ty_bytes = put_expr(ty);
        let rest_bytes = put_all_telescope(body);
        byte_stream_concat(ty_bytes, rest_bytes),
      _ => put_expr(expr),
    }
  }
⟧

end IxVM
