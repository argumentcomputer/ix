module
import Ix.Aiur.Meta
public import Ix.Aiur.Stages.Source

public section

namespace IxVM

def ingress := ⟦
  -- Load a constant from IOBuffer by address, verify blake3, deserialize
  fn load_verified_constant(addr: [G; 32]) -> Constant {
    let (idx, len) = io_get_info(addr);
    let bytes = #read_byte_stream(idx, len);
    let h = blake3(bytes);
    assert_eq!(
      [
        h[0][0], h[0][1], h[0][2], h[0][3],
        h[1][0], h[1][1], h[1][2], h[1][3],
        h[2][0], h[2][1], h[2][2], h[2][3],
        h[3][0], h[3][1], h[3][2], h[3][3],
        h[4][0], h[4][1], h[4][2], h[4][3],
        h[5][0], h[5][1], h[5][2], h[5][3],
        h[6][0], h[6][1], h[6][2], h[6][3],
        h[7][0], h[7][1], h[7][2], h[7][3]
      ],
      addr
    );
    let (constant, rest) = get_constant(bytes);
    assert_eq!(rest, List.Nil);
    constant
  }

  -- Compare two 32-byte addresses for equality
  fn address_eq(a: [G; 32], b: [G; 32]) -> G {
    let [a0, a1, a2, a3, a4, a5, a6, a7,
         a8, a9, a10, a11, a12, a13, a14, a15,
         a16, a17, a18, a19, a20, a21, a22, a23,
         a24, a25, a26, a27, a28, a29, a30, a31] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7,
         b8, b9, b10, b11, b12, b13, b14, b15,
         b16, b17, b18, b19, b20, b21, b22, b23,
         b24, b25, b26, b27, b28, b29, b30, b31] = b;
    match [a0 - b0, a1 - b1, a2 - b2, a3 - b3,
           a4 - b4, a5 - b5, a6 - b6, a7 - b7,
           a8 - b8, a9 - b9, a10 - b10, a11 - b11,
           a12 - b12, a13 - b13, a14 - b14, a15 - b15,
           a16 - b16, a17 - b17, a18 - b18, a19 - b19,
           a20 - b20, a21 - b21, a22 - b22, a23 - b23,
           a24 - b24, a25 - b25, a26 - b26, a27 - b27,
           a28 - b28, a29 - b29, a30 - b30, a31 - b31] {
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] => 1,
      _ => 0,
    }
  }

  -- Load a blob from IOBuffer by address, verify blake3, return raw bytes.
  -- Blobs are stored under key [1] ++ addr to distinguish from constants.
  fn load_verified_blob(addr: [G; 32]) -> ByteStream {
    let [a0, a1, a2, a3, a4, a5, a6, a7,
         a8, a9, a10, a11, a12, a13, a14, a15,
         a16, a17, a18, a19, a20, a21, a22, a23,
         a24, a25, a26, a27, a28, a29, a30, a31] = addr;
    let blob_key = [1, a0, a1, a2, a3, a4, a5, a6, a7,
                    a8, a9, a10, a11, a12, a13, a14, a15,
                    a16, a17, a18, a19, a20, a21, a22, a23,
                    a24, a25, a26, a27, a28, a29, a30, a31];
    let (idx, len) = io_get_info(blob_key);
    let bytes = #read_byte_stream(idx, len);
    let h = blake3(bytes);
    assert_eq!(
      [
        h[0][0], h[0][1], h[0][2], h[0][3],
        h[1][0], h[1][1], h[1][2], h[1][3],
        h[2][0], h[2][1], h[2][2], h[2][3],
        h[3][0], h[3][1], h[3][2], h[3][3],
        h[4][0], h[4][1], h[4][2], h[4][3],
        h[5][0], h[5][1], h[5][2], h[5][3],
        h[6][0], h[6][1], h[6][2], h[6][3],
        h[7][0], h[7][1], h[7][2], h[7][3]
      ],
      addr
    );
    bytes
  }

  -- Build lit_blobs by loading and verifying each blob on demand.
  -- A ref is a blob if it's not in all_addrs (the constant address list).
  -- For constant refs, returns List.Nil (never read by conversion).
  fn build_lit_blobs(refs: List‹[G; 32]›, all_addrs: List‹[G; 32]›) -> List‹ByteStream› {
    match refs {
      List.Nil => List.Nil,
      List.Cons(addr, &rest) =>
        let blob = is_blob(addr, all_addrs);
        match blob {
          1 =>
            let bs = load_verified_blob(addr);
            List.Cons(bs, store(build_lit_blobs(rest, all_addrs))),
          0 =>
            List.Cons(List.Nil, store(build_lit_blobs(rest, all_addrs))),
        },
    }
  }

  -- Check if an address is a blob: it's a blob if it's NOT in the constant address list.
  -- Blob addresses and constant addresses are different by design (different hash preimage structures).
  fn is_blob(addr: [G; 32], all_addrs: List‹[G; 32]›) -> G {
    let found = address_in_list(addr, all_addrs);
    1 - found
  }

  -- Extract the Muts block address from a projection ConstantInfo.
  -- Returns [0; 32] for non-projection constants.
  fn get_proj_block_addr(info: ConstantInfo) -> [G; 32] {
    match info {
      ConstantInfo.IPrj(prj) =>
        match prj { InductiveProj.Mk(_, addr) => addr, },
      ConstantInfo.CPrj(prj) =>
        match prj { ConstructorProj.Mk(_, _, addr) => addr, },
      ConstantInfo.RPrj(prj) =>
        match prj { RecursorProj.Mk(_, addr) => addr, },
      ConstantInfo.DPrj(prj) =>
        match prj { DefinitionProj.Mk(_, addr) => addr, },
      ConstantInfo.Defn(_) => [0; 32],
      ConstantInfo.Recr(_) => [0; 32],
      ConstantInfo.Axio(_) => [0; 32],
      ConstantInfo.Quot(_) => [0; 32],
      ConstantInfo.Muts(_) => [0; 32],
    }
  }

  -- Find the Muts block address by scanning a constant's refs for any
  -- projection constant (IPrj, CPrj, RPrj, DPrj). Used for standalone
  -- recursors to locate their inductive's block.
  fn find_block_addr_from_refs(refs: List‹[G; 32]›, all_addrs: List‹[G; 32]›) -> [G; 32] {
    match refs {
      List.Nil => [0; 32],
      List.Cons(addr, &rest) =>
        let blob = is_blob(addr, all_addrs);
        match blob {
          1 => find_block_addr_from_refs(rest, all_addrs),
          0 =>
            let c = load_verified_constant(addr);
            match c {
              Constant.Mk(info, _, _, _) =>
                match info {
                  ConstantInfo.IPrj(prj) =>
                    match prj { InductiveProj.Mk(_, block_addr) => block_addr, },
                  ConstantInfo.CPrj(prj) =>
                    match prj { ConstructorProj.Mk(_, _, block_addr) => block_addr, },
                  ConstantInfo.RPrj(prj) =>
                    match prj { RecursorProj.Mk(_, block_addr) => block_addr, },
                  ConstantInfo.DPrj(prj) =>
                    match prj { DefinitionProj.Mk(_, block_addr) => block_addr, },
                  _ => find_block_addr_from_refs(rest, all_addrs),
                },
            },
        },
    }
  }

  fn recr_rule_count(recr: Recursor) -> G {
    match recr {
      Recursor.Mk(_, _, _, _, _, _, _, _, &rules) =>
        count_recr_rules(rules),
    }
  }

  -- Count recursor rules
  fn count_recr_rules(rules: List‹RecursorRule›) -> G {
    match rules {
      List.Nil => 0,
      List.Cons(_, &rest) => count_recr_rules(rest) + 1,
    }
  }

  -- Count constructors in a Muts block's first inductive
  fn count_block_ctors(members: List‹MutConst›) -> G {
    match members {
      List.Nil => 0,
      List.Cons(mc, &rest) =>
        match mc {
          MutConst.Indc(ind) =>
            match ind {
              Inductive.Mk(_, _, _, _, _, _, _, _, &ctors) =>
                list_length(ctors),
            },
          _ => count_block_ctors(rest),
        },
    }
  }

  -- Find the correct block address for a standalone recursor by matching
  -- the number of recursor rules to the number of constructors in the block.
  fn find_matching_block_addr(refs: List‹[G; 32]›, all_addrs: List‹[G; 32]›, nrules: G) -> [G; 32] {
    match refs {
      List.Nil => [0; 32],
      List.Cons(addr, &rest) =>
        let blob = is_blob(addr, all_addrs);
        match blob {
          1 => find_matching_block_addr(rest, all_addrs, nrules),
          0 =>
            let c = load_verified_constant(addr);
            match c {
              Constant.Mk(info, _, _, _) =>
                match info {
                  ConstantInfo.IPrj(prj) =>
                    match prj {
                      InductiveProj.Mk(_, block_addr) =>
                        let bc = load_verified_constant(block_addr);
                        match bc {
                          Constant.Mk(bi, _, _, _) =>
                            match bi {
                              ConstantInfo.Muts(&members) =>
                                let nctors = count_block_ctors(members);
                                let is_match = eq_zero(nctors - nrules);
                                match is_match {
                                  1 => block_addr,
                                  0 => find_matching_block_addr(rest, all_addrs, nrules),
                                },
                              _ => find_matching_block_addr(rest, all_addrs, nrules),
                            },
                        },
                    },
                  _ => find_matching_block_addr(rest, all_addrs, nrules),
                },
            },
        },
    }
  }

  -- ============================================================================
  -- Position map: maps loaded addresses to kernel constant positions.
  --
  -- When a Muts block is encountered, its members are expanded inline into
  -- kernel constants: each Indc becomes 1 Induct + N Ctors, each Recr becomes
  -- 1 Rec, each Defn becomes 1 Defn. Projection constants (IPrj, CPrj, RPrj,
  -- DPrj) are not emitted directly — instead they map to the position of their
  -- corresponding expanded member.
  -- ============================================================================

  -- Count the number of kernel entries a single MutConst member produces:
  -- Indc: 1 (inductive) + num_ctors
  -- Recr: 1
  -- Defn: 1
  fn member_kernel_size(mc: MutConst) -> G {
    match mc {
      MutConst.Indc(ind) =>
        match ind {
          Inductive.Mk(_, _, _, _, _, _, _, _, &ctors) =>
            list_length(ctors) + 1,
        },
      MutConst.Recr(_) => 1,
      MutConst.Defn(_) => 1,
    }
  }

  -- Count total kernel entries for an entire List‹MutConst›
  fn block_kernel_size(members: List‹MutConst›) -> G {
    match members {
      List.Nil => 0,
      List.Cons(mc, &rest) =>
        member_kernel_size(mc) + block_kernel_size(rest),
    }
  }

  -- Compute the offset of member at member_idx within a block's expansion.
  -- Members before member_idx each contribute member_kernel_size entries.
  fn member_offset(members: List‹MutConst›, target_idx: G) -> G {
    match target_idx {
      0 => 0,
      _ =>
        match members {
          List.Cons(mc, &rest) =>
            member_kernel_size(mc) + member_offset(rest, target_idx - 1),
        },
    }
  }

  -- Look up the kernel position for an address using parallel lists.
  fn lookup_addr_pos(target: [G; 32], all_addrs: List‹[G; 32]›, pos_map: List‹G›) -> G {
    match all_addrs {
      List.Nil => 0,
      List.Cons(addr, &rest_addrs) =>
        match pos_map {
          List.Cons(pos, &rest_pos) =>
            let eq = address_eq(target, addr);
            match eq {
              1 => pos,
              0 => lookup_addr_pos(target, rest_addrs, rest_pos),
            },
        },
    }
  }

  -- Find the start position of a block by its block address.
  fn lookup_block_start(target: [G; 32], block_addrs: List‹[G; 32]›, block_starts: List‹G›) -> G {
    match block_addrs {
      List.Nil => 0,
      List.Cons(addr, &rest_addrs) =>
        match block_starts {
          List.Cons(start, &rest_starts) =>
            let eq = address_eq(target, addr);
            match eq {
              1 => start,
              0 => lookup_block_start(target, rest_addrs, rest_starts),
            },
        },
    }
  }

  -- ============================================================================
  -- Layout pass: compute block start positions and total kernel size
  -- ============================================================================

  fn compute_layout(
    consts: List‹&Constant›,
    addrs: List‹[G; 32]›,
    pos: G
  ) -> (List‹[G; 32]›, List‹G›, G) {
    match consts {
      List.Nil => (List.Nil, List.Nil, pos),
      List.Cons(&c, &rest_consts) =>
        match addrs {
          List.Cons(addr, &rest_addrs) =>
            match c {
              Constant.Mk(info, _, _, _) =>
                match info {
                  ConstantInfo.Muts(&members) =>
                    let size = block_kernel_size(members);
                    let (ba, bs, next) = compute_layout(rest_consts, rest_addrs, pos + size);
                    (List.Cons(addr, store(ba)),
                     List.Cons(pos, store(bs)),
                     next),
                  ConstantInfo.IPrj(_) =>
                    compute_layout(rest_consts, rest_addrs, pos),
                  ConstantInfo.CPrj(_) =>
                    compute_layout(rest_consts, rest_addrs, pos),
                  ConstantInfo.RPrj(_) =>
                    compute_layout(rest_consts, rest_addrs, pos),
                  ConstantInfo.DPrj(_) =>
                    compute_layout(rest_consts, rest_addrs, pos),
                  ConstantInfo.Defn(_) =>
                    compute_layout(rest_consts, rest_addrs, pos + 1),
                  ConstantInfo.Axio(_) =>
                    compute_layout(rest_consts, rest_addrs, pos + 1),
                  ConstantInfo.Quot(_) =>
                    compute_layout(rest_consts, rest_addrs, pos + 1),
                  ConstantInfo.Recr(_) =>
                    compute_layout(rest_consts, rest_addrs, pos + 1),
                },
            },
        },
    }
  }

  -- ============================================================================
  -- Position map pass: build a List‹G› parallel to all_addrs
  -- ============================================================================

  fn build_pos_map(
    consts: List‹&Constant›,
    addrs: List‹[G; 32]›,
    block_addrs: List‹[G; 32]›,
    block_starts: List‹G›,
    pos: G
  ) -> List‹G› {
    match consts {
      List.Nil => List.Nil,
      List.Cons(&c, &rest_consts) =>
        match addrs {
          List.Cons(_, &rest_addrs) =>
            match c {
              Constant.Mk(info, _, _, _) =>
                match info {
                  ConstantInfo.Muts(&members) =>
                    let size = block_kernel_size(members);
                    List.Cons(0, store(build_pos_map(rest_consts, rest_addrs, block_addrs, block_starts, pos + size))),
                  ConstantInfo.IPrj(prj) =>
                    match prj {
                      InductiveProj.Mk(idx, block_addr) =>
                        let block_start = lookup_block_start(block_addr, block_addrs, block_starts);
                        let block_const = load_verified_constant(block_addr);
                        match block_const {
                          Constant.Mk(block_info, _, _, _) =>
                            match block_info {
                              ConstantInfo.Muts(&members) =>
                                let off = member_offset(members, flatten_u64(idx));
                                List.Cons(block_start + off,
                                  store(build_pos_map(rest_consts, rest_addrs, block_addrs, block_starts, pos))),
                            },
                        },
                    },
                  ConstantInfo.CPrj(prj) =>
                    match prj {
                      ConstructorProj.Mk(idx, cidx, block_addr) =>
                        let block_start = lookup_block_start(block_addr, block_addrs, block_starts);
                        let block_const = load_verified_constant(block_addr);
                        match block_const {
                          Constant.Mk(block_info, _, _, _) =>
                            match block_info {
                              ConstantInfo.Muts(&members) =>
                                let mem_off = member_offset(members, flatten_u64(idx));
                                List.Cons(block_start + mem_off + 1 + flatten_u64(cidx),
                                  store(build_pos_map(rest_consts, rest_addrs, block_addrs, block_starts, pos))),
                            },
                        },
                    },
                  ConstantInfo.RPrj(prj) =>
                    match prj {
                      RecursorProj.Mk(idx, block_addr) =>
                        let block_start = lookup_block_start(block_addr, block_addrs, block_starts);
                        let block_const = load_verified_constant(block_addr);
                        match block_const {
                          Constant.Mk(block_info, _, _, _) =>
                            match block_info {
                              ConstantInfo.Muts(&members) =>
                                let off = member_offset(members, flatten_u64(idx));
                                List.Cons(block_start + off,
                                  store(build_pos_map(rest_consts, rest_addrs, block_addrs, block_starts, pos))),
                            },
                        },
                    },
                  ConstantInfo.DPrj(prj) =>
                    match prj {
                      DefinitionProj.Mk(idx, block_addr) =>
                        let block_start = lookup_block_start(block_addr, block_addrs, block_starts);
                        let block_const = load_verified_constant(block_addr);
                        match block_const {
                          Constant.Mk(block_info, _, _, _) =>
                            match block_info {
                              ConstantInfo.Muts(&members) =>
                                let off = member_offset(members, flatten_u64(idx));
                                List.Cons(block_start + off,
                                  store(build_pos_map(rest_consts, rest_addrs, block_addrs, block_starts, pos))),
                            },
                        },
                    },
                  _ =>
                    List.Cons(pos,
                      store(build_pos_map(rest_consts, rest_addrs, block_addrs, block_starts, pos + 1))),
                },
            },
        },
    }
  }

  -- ============================================================================
  -- Ref index building using position map
  -- ============================================================================

  fn build_ref_idxs_mapped(refs: List‹[G; 32]›, all_addrs: List‹[G; 32]›, pos_map: List‹G›) -> List‹G› {
    match refs {
      List.Nil => List.Nil,
      List.Cons(addr, &rest) =>
        let pos = lookup_addr_pos(addr, all_addrs, pos_map);
        List.Cons(pos, store(build_ref_idxs_mapped(rest, all_addrs, pos_map))),
    }
  }

  fn build_recur_idxs(members: List‹MutConst›, block_start: G, member_idx: G) -> List‹G› {
    match members {
      List.Nil => List.Nil,
      List.Cons(_, &rest) =>
        let off = member_offset(members, member_idx);
        List.Cons(block_start + off,
          store(build_recur_idxs(rest, block_start, member_idx + 1))),
    }
  }

  fn build_ctor_idxs(num_ctors: G, induct_pos: G, cidx: G) -> List‹G› {
    match num_ctors {
      0 => List.Nil,
      _ =>
        List.Cons(induct_pos + 1 + cidx,
          store(build_ctor_idxs(num_ctors - 1, induct_pos, cidx + 1))),
    }
  }

  fn build_rule_ctor_idxs(members: List‹MutConst›, block_start: G, member_idx: G) -> List‹G› {
    match members {
      List.Nil => List.Nil,
      List.Cons(mc, &rest) =>
        match mc {
          MutConst.Indc(ind) =>
            match ind {
              Inductive.Mk(_, _, _, _, _, _, _, _, &ctors) =>
                let num_ctors = list_length(ctors);
                let induct_pos = block_start + member_offset(members, member_idx);
                let this_ctors = build_ctor_idxs(num_ctors, induct_pos, 0);
                let rest_ctors = build_rule_ctor_idxs(rest, block_start, member_idx + 1);
                list_concat(this_ctors, rest_ctors),
            },
          MutConst.Defn(_) =>
            build_rule_ctor_idxs(rest, block_start, member_idx + 1),
          MutConst.Recr(_) =>
            build_rule_ctor_idxs(rest, block_start, member_idx + 1),
        },
    }
  }

  -- ============================================================================
  -- ConvertInput construction: expand Muts blocks into kernel constants
  -- ============================================================================

  -- Expand a single MutConst member into ConvertInputs.
  -- For Indc: emits 1 Induct + N Ctors.
  -- For Recr: emits 1 Rec.
  -- For Defn: emits 1 Defn.
  fn expand_member(
    mc: MutConst,
    ctx: ConvertCtx,
    members: List‹MutConst›,
    block_start: G,
    member_idx: G
  ) -> List‹&ConvertInput› {
    match mc {
      MutConst.Indc(ind) =>
        match ind {
          Inductive.Mk(_, _, _, _, _, _, _, _, &ctors) =>
            let num_ctors = list_length(ctors);
            let induct_pos = block_start + member_offset(members, member_idx);
            let ctor_idxs = build_ctor_idxs(num_ctors, induct_pos, 0);
            let indc_input = ConvertInput.Mk(ctx, ConvertKind.CKIndc(ind, store(ctor_idxs)));
            let ctor_inputs = expand_ctors(ctors, ctx, induct_pos);
            List.Cons(store(indc_input), store(ctor_inputs)),
        },
      MutConst.Recr(recr) =>
        let rule_ctor_idxs = build_rule_ctor_idxs(members, block_start, 0);
        let input = ConvertInput.Mk(ctx, ConvertKind.CKRecr(recr, store(rule_ctor_idxs)));
        List.Cons(store(input), store(List.Nil)),
      MutConst.Defn(defn) =>
        let input = ConvertInput.Mk(ctx, ConvertKind.CKDefn(defn));
        List.Cons(store(input), store(List.Nil)),
    }
  }

  fn expand_ctors(ctors: List‹Constructor›, ctx: ConvertCtx, induct_pos: G) -> List‹&ConvertInput› {
    match ctors {
      List.Nil => List.Nil,
      List.Cons(ctor, &rest) =>
        let input = ConvertInput.Mk(ctx, ConvertKind.CKCtor(ctor, induct_pos));
        List.Cons(store(input), store(expand_ctors(rest, ctx, induct_pos))),
    }
  }

  fn expand_members(
    members: List‹MutConst›,
    ctx: ConvertCtx,
    all_members: List‹MutConst›,
    block_start: G,
    member_idx: G
  ) -> List‹&ConvertInput› {
    match members {
      List.Nil => List.Nil,
      List.Cons(mc, &rest) =>
        let this = expand_member(mc, ctx, all_members, block_start, member_idx);
        let more = expand_members(rest, ctx, all_members, block_start, member_idx + 1);
        list_concat(this, more),
    }
  }

  -- Build the full List‹&ConvertInput› by walking loaded constants.
  -- Muts blocks are expanded into their members.
  -- Projections are skipped (handled via block expansion).
  -- Standalone constants are converted directly.
  fn build_convert_inputs(
    consts: List‹&Constant›,
    all_addrs: List‹[G; 32]›,
    pos_map: List‹G›,
    block_addrs: List‹[G; 32]›,
    block_starts: List‹G›,
    pos: G
  ) -> List‹&ConvertInput› {
    match consts {
      List.Nil => List.Nil,
      List.Cons(&c, &rest) =>
        match c {
          Constant.Mk(info, &sharing, &refs, &univs) =>
            match info {
              ConstantInfo.Muts(&members) =>
                let size = block_kernel_size(members);
                let ref_idxs = build_ref_idxs_mapped(refs, all_addrs, pos_map);
                let lit_blobs = build_lit_blobs(refs, all_addrs);
                let recur_idxs = build_recur_idxs(members, pos, 0);
                let ctx = ConvertCtx.Mk(store(sharing), store(ref_idxs), store(recur_idxs), store(lit_blobs), store(univs));
                let expanded = expand_members(members, ctx, members, pos, 0);
                let more = build_convert_inputs(rest, all_addrs, pos_map, block_addrs, block_starts, pos + size);
                list_concat(expanded, more),
              ConstantInfo.IPrj(_) =>
                build_convert_inputs(rest, all_addrs, pos_map, block_addrs, block_starts, pos),
              ConstantInfo.CPrj(_) =>
                build_convert_inputs(rest, all_addrs, pos_map, block_addrs, block_starts, pos),
              ConstantInfo.RPrj(_) =>
                build_convert_inputs(rest, all_addrs, pos_map, block_addrs, block_starts, pos),
              ConstantInfo.DPrj(_) =>
                build_convert_inputs(rest, all_addrs, pos_map, block_addrs, block_starts, pos),
              ConstantInfo.Defn(defn) =>
                let ref_idxs = build_ref_idxs_mapped(refs, all_addrs, pos_map);
                let lit_blobs = build_lit_blobs(refs, all_addrs);
                let recur_idxs = List.Cons(pos, store(List.Nil));
                let ctx = ConvertCtx.Mk(store(sharing), store(ref_idxs), store(recur_idxs), store(lit_blobs), store(univs));
                let input = ConvertInput.Mk(ctx, ConvertKind.CKDefn(defn));
                List.Cons(store(input),
                  store(build_convert_inputs(rest, all_addrs, pos_map, block_addrs, block_starts, pos + 1))),
              ConstantInfo.Axio(axio) =>
                let ref_idxs = build_ref_idxs_mapped(refs, all_addrs, pos_map);
                let lit_blobs = build_lit_blobs(refs, all_addrs);
                let ctx = ConvertCtx.Mk(store(sharing), store(ref_idxs), store(List.Nil), store(lit_blobs), store(univs));
                let input = ConvertInput.Mk(ctx, ConvertKind.CKAxio(axio));
                List.Cons(store(input),
                  store(build_convert_inputs(rest, all_addrs, pos_map, block_addrs, block_starts, pos + 1))),
              ConstantInfo.Quot(quot) =>
                let ref_idxs = build_ref_idxs_mapped(refs, all_addrs, pos_map);
                let lit_blobs = build_lit_blobs(refs, all_addrs);
                let ctx = ConvertCtx.Mk(store(sharing), store(ref_idxs), store(List.Nil), store(lit_blobs), store(univs));
                let input = ConvertInput.Mk(ctx, ConvertKind.CKQuot(quot));
                List.Cons(store(input),
                  store(build_convert_inputs(rest, all_addrs, pos_map, block_addrs, block_starts, pos + 1))),
              ConstantInfo.Recr(recr) =>
                let ref_idxs = build_ref_idxs_mapped(refs, all_addrs, pos_map);
                let lit_blobs = build_lit_blobs(refs, all_addrs);
                let nrules = recr_rule_count(recr);
                let block_addr = find_matching_block_addr(refs, all_addrs, nrules);
                let block_const = load_verified_constant(block_addr);
                match block_const {
                  Constant.Mk(block_info, _, _, _) =>
                    match block_info {
                      ConstantInfo.Muts(&members) =>
                        let recur_idxs = List.Cons(pos, store(List.Nil));
                        let bs = lookup_block_start(block_addr, block_addrs, block_starts);
                        let rule_ctor_idxs = build_rule_ctor_idxs(members, bs, 0);
                        let ctx = ConvertCtx.Mk(store(sharing), store(ref_idxs), store(recur_idxs), store(lit_blobs), store(univs));
                        let input = ConvertInput.Mk(ctx, ConvertKind.CKRecr(recr, store(rule_ctor_idxs)));
                        List.Cons(store(input),
                          store(build_convert_inputs(rest, all_addrs, pos_map, block_addrs, block_starts, pos + 1))),
                    },
                },
            },
        },
    }
  }

  -- ============================================================================
  -- Loading and dependency tracking
  -- ============================================================================

  -- Check if an address is already in a list
  fn address_in_list(addr: [G; 32], list: List‹[G; 32]›) -> G {
    match list {
      List.Nil => 0,
      List.Cons(a, &rest) =>
        let eq = address_eq(addr, a);
        match eq {
          1 => 1,
          0 => address_in_list(addr, rest),
        },
    }
  }

  -- Recursively load constants and their transitive dependencies.
  -- Processes one address at a time from a worklist, deduplicating by
  -- checking the visited set. Blob addresses are detected via io_get_info:
  -- the prover provides len=0 for blobs (which are not serialized constants).
  -- For projection constants (IPrj, CPrj, RPrj, DPrj), also follows the
  -- Muts block's refs so that all dependencies of block members are loaded.
  fn load_with_deps(
    addr: [G; 32],
    worklist: List‹[G; 32]›,
    visited_addrs: List‹[G; 32]›,
    visited_consts: List‹&Constant›
  ) -> (List‹[G; 32]›, List‹&Constant›) {
    let already = address_in_list(addr, visited_addrs);
    match already {
      1 =>
        match worklist {
          List.Nil => (visited_addrs, visited_consts),
          List.Cons(next, &rest) =>
            load_with_deps(next, rest, visited_addrs, visited_consts),
        },
      0 =>
        -- Check if this address has constant data in IOBuffer.
        -- io_get_info is unconstrained; the prover provides (0, 0) for blob addresses.
        -- Soundness: if the prover lies and skips a real constant, type checking will fail.
        let (_, len) = io_get_info(addr);
        match len {
          0 =>
            -- Blob address: skip (blob values are loaded on demand in build_lit_blobs)
            match worklist {
              List.Nil => (visited_addrs, visited_consts),
              List.Cons(next, &rest) =>
                load_with_deps(next, rest, visited_addrs, visited_consts),
            },
          _ =>
            let new_addrs = List.Cons(addr, store(visited_addrs));
            let constant = load_verified_constant(addr);
            let new_consts = List.Cons(store(constant), store(visited_consts));
            match constant {
              Constant.Mk(info, _, &refs, _) =>
                let block_addr = get_proj_block_addr(info);
                match address_eq(block_addr, [0; 32]) {
                  1 =>
                    let combined_refs = list_concat(refs, List.Nil);
                    let next_worklist = list_concat(combined_refs, worklist);
                    match next_worklist {
                      List.Nil => (new_addrs, new_consts),
                      List.Cons(next, &rest) =>
                        load_with_deps(next, rest, new_addrs, new_consts),
                    },
                  0 =>
                    let combined_refs = list_concat(
                      refs,
                      List.Cons(block_addr, store(List.Nil))
                    );
                    let next_worklist = list_concat(combined_refs, worklist);
                    match next_worklist {
                      List.Nil => (new_addrs, new_consts),
                      List.Cons(next, &rest) =>
                        load_with_deps(next, rest, new_addrs, new_consts),
                    },
                },
            },
        },
    }
  }

  -- Transitively loads all dependencies of the target constant from IOBuffer,
  -- verifies blake3 hashes then converts to kernel types.
  fn ingress(target_addr: [G; 32]) -> List‹&KConstantInfo› {
    let (all_addrs, all_consts) = load_with_deps(
      target_addr, List.Nil, List.Nil, List.Nil);
    let (block_addrs, block_starts, _total) = compute_layout(all_consts, all_addrs, 0);
    let pos_map = build_pos_map(all_consts, all_addrs, block_addrs, block_starts, 0);
    let inputs = build_convert_inputs(all_consts, all_addrs, pos_map, block_addrs, block_starts, 0);
    convert_all(inputs)
  }

  -- Look up a constant's position by its blake3 address.
  -- Returns 0 - 1 (sentinel) if the address is not found.
  fn find_addr_pos(target: [G; 32], all_addrs: List‹[G; 32]›, pos_map: List‹G›) -> G {
    match all_addrs {
      List.Nil => 0 - 1,
      List.Cons(addr, &rest_addrs) =>
        match pos_map {
          List.Cons(pos, &rest_pos) =>
            let eq = address_eq(target, addr);
            match eq {
              1 => pos,
              0 => find_addr_pos(target, rest_addrs, rest_pos),
            },
        },
    }
  }

  -- Transitively loads all dependencies, converts to kernel types, and
  -- resolves primitive type indices (Nat, String) by hardcoded blake3 address.
  -- Returns (constants, nat_idx, str_idx).
  fn ingress_with_primitives(target_addr: [G; 32]) -> (List‹&KConstantInfo›, G, G) {
    let (all_addrs, all_consts) = load_with_deps(
      target_addr, List.Nil, List.Nil, List.Nil);
    let (block_addrs, block_starts, _total) = compute_layout(all_consts, all_addrs, 0);
    let pos_map = build_pos_map(all_consts, all_addrs, block_addrs, block_starts, 0);
    let inputs = build_convert_inputs(all_consts, all_addrs, pos_map, block_addrs, block_starts, 0);
    let k_consts = convert_all(inputs);
    let nat_idx = find_addr_pos(
      [252, 14, 30, 145, 47, 45, 127, 18, 4, 154, 91, 49, 93, 118, 238, 194, 149, 98, 227, 77, 195, 158, 188, 162, 82, 135, 174, 88, 128, 125, 177, 55],
      all_addrs, pos_map);
    let str_idx = find_addr_pos(
      [30, 88, 121, 25, 226, 100, 26, 91, 42, 106, 111, 127, 245, 153, 122, 104, 84, 186, 86, 190, 136, 220, 9, 88, 195, 67, 193, 38, 238, 117, 253, 155],
      all_addrs, pos_map);
    (k_consts, nat_idx, str_idx)
  }
⟧

end IxVM
