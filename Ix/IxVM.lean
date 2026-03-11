module
public import Ix.Aiur.Meta
public import Ix.IxVM.ByteStream
public import Ix.IxVM.Blake3
public import Ix.IxVM.Ixon
public import Ix.IxVM.IxonSerialize
public import Ix.IxVM.IxonDeserialize
public import Ix.IxVM.Convert
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel

public section

namespace IxVM

def entrypoints := ⟦
  /- # Test entrypoints -/

  fn ixon_serde_test(n: G) {
    match n {
      0 => (),
      _ =>
        let n_minus_1 = n - 1;
        let (idx, len) = io_get_info([n_minus_1]);
        let bytes = read_byte_stream(idx, len);
        let (const, rest) = get_constant(bytes);
        assert_eq!(rest, ByteStream.Nil);
        let bytes2 = put_constant(const, ByteStream.Nil);
        assert_eq!(bytes, bytes2);
        ixon_serde_test(n_minus_1),
    }
  }

  /- # Kernel check helpers -/

  -- Verify blake3 of a ByteStream against an expected address
  fn verify_blake3(data: ByteStream, addr: [G; 32]) {
    let h = blake3(data);
    let computed_addr = [
      h[0][0], h[0][1], h[0][2], h[0][3],
      h[1][0], h[1][1], h[1][2], h[1][3],
      h[2][0], h[2][1], h[2][2], h[2][3],
      h[3][0], h[3][1], h[3][2], h[3][3],
      h[4][0], h[4][1], h[4][2], h[4][3],
      h[5][0], h[5][1], h[5][2], h[5][3],
      h[6][0], h[6][1], h[6][2], h[6][3],
      h[7][0], h[7][1], h[7][2], h[7][3]
    ];
    assert_eq!(addr, computed_addr);
    ()
  }

  -- Load a constant from IOBuffer by address, verify blake3, deserialize
  fn load_verified_constant(addr: [G; 32]) -> Constant {
    let (idx, len) = io_get_info(addr);
    let bytes = read_byte_stream(idx, len);
    let _x = verify_blake3(bytes, addr);
    let (constant, rest) = get_constant(bytes);
    assert_eq!(rest, ByteStream.Nil);
    constant
  }

  /- # Content-addressed cross-reference computation -/

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

  -- Find the position of an address in the ordered address list.
  -- Returns [0; 8] if not found (blob refs are not in the address list).
  fn find_addr_position(target: [G; 32], addrs: AddressList, pos: [G; 8]) -> [G; 8] {
    match addrs {
      AddressList.Nil => [0; 8],
      AddressList.Cons(addr, &rest) =>
        let eq = address_eq(target, addr);
        match eq {
          1 => pos,
          0 => find_addr_position(target, rest, relaxed_u64_succ(pos)),
        },
    }
  }

  -- Map each ref address to its position in the ordered address list
  fn build_ref_idxs(refs: AddressList, all_addrs: AddressList) -> U64List {
    match refs {
      AddressList.Nil => U64List.Nil,
      AddressList.Cons(addr, &rest) =>
        let pos = find_addr_position(addr, all_addrs, [0; 8]);
        U64List.Cons(pos, store(build_ref_idxs(rest, all_addrs))),
    }
  }

  -- Look up a blob's decoded value by address. Returns [0; 8] if not a blob.
  fn lookup_blob_val(addr: [G; 32], blobs: BlobList) -> [G; 8] {
    match blobs {
      BlobList.Nil => [0; 8],
      BlobList.Cons(entry, &rest) =>
        match entry {
          BlobEntry.Mk(blob_addr, val) =>
            let eq = address_eq(addr, blob_addr);
            match eq {
              1 => val,
              0 => lookup_blob_val(addr, rest),
            },
        },
    }
  }

  -- Build lit_vals by looking up each ref address in the blob list.
  -- For constant refs (not blobs), returns [0; 8] (never read by conversion).
  fn build_lit_vals(refs: AddressList, blobs: BlobList) -> U64List {
    match refs {
      AddressList.Nil => U64List.Nil,
      AddressList.Cons(addr, &rest) =>
        let val = lookup_blob_val(addr, blobs);
        U64List.Cons(val, store(build_lit_vals(rest, blobs))),
    }
  }

  -- Check if an address is a blob address
  fn is_blob(addr: [G; 32], blobs: BlobList) -> G {
    match blobs {
      BlobList.Nil => 0,
      BlobList.Cons(entry, &rest) =>
        match entry {
          BlobEntry.Mk(blob_addr, _) =>
            let eq = address_eq(addr, blob_addr);
            match eq {
              1 => 1,
              0 => is_blob(addr, rest),
            },
        },
    }
  }

  -- Load blob table entries from IOBuffer
  #[unconstrained]
  fn load_blob_table_entries(base: G, remaining: G, offset: G) -> BlobList {
    match remaining {
      0 => BlobList.Nil,
      _ =>
        let addr = io_read(base + offset, 32);
        let val = io_read(base + offset + 32, 8);
        let entry = BlobEntry.Mk(addr, val);
        BlobList.Cons(entry, store(load_blob_table_entries(base, remaining - 1, offset + 40))),
    }
  }

  -- Load blob table from IOBuffer (key = [0; 32])
  #[unconstrained]
  fn load_blob_table() -> BlobList {
    let (base, len) = io_get_info([0; 32]);
    match len {
      0 => BlobList.Nil,
      _ =>
        let [count] = io_read(base, 1);
        load_blob_table_entries(base, count, 1),
    }
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
  fn find_block_addr_from_refs(refs: AddressList, blobs: BlobList) -> [G; 32] {
    match refs {
      AddressList.Nil => [0; 32],
      AddressList.Cons(addr, &rest) =>
        let blob = is_blob(addr, blobs);
        match blob {
          1 => find_block_addr_from_refs(rest, blobs),
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
                  _ => find_block_addr_from_refs(rest, blobs),
                },
            },
        },
    }
  }

  -- Count elements in a ConstructorList
  fn count_constructor_list_(ctors: ConstructorList) -> [G; 8] {
    match ctors {
      ConstructorList.Nil => [0; 8],
      ConstructorList.Cons(_, &rest) =>
        relaxed_u64_succ(count_constructor_list_(rest)),
    }
  }

  -- Count members in a MutConstList
  fn count_mut_const_list_(members: MutConstList) -> [G; 8] {
    match members {
      MutConstList.Nil => [0; 8],
      MutConstList.Cons(_, &rest) =>
        relaxed_u64_succ(count_mut_const_list_(rest)),
    }
  }

  -- Check if a ConstantInfo is a primary member projection (iPrj, dPrj, or rPrj)
  -- for the given block address and member index
  fn is_member_proj_for(info: ConstantInfo, block_addr: [G; 32], member_idx: [G; 8]) -> G {
    match info {
      ConstantInfo.IPrj(prj) =>
        match prj {
          InductiveProj.Mk(idx, baddr) =>
            address_eq(baddr, block_addr) * u64_eq(idx, member_idx),
        },
      ConstantInfo.DPrj(prj) =>
        match prj {
          DefinitionProj.Mk(idx, baddr) =>
            address_eq(baddr, block_addr) * u64_eq(idx, member_idx),
        },
      ConstantInfo.RPrj(prj) =>
        match prj {
          RecursorProj.Mk(idx, baddr) =>
            address_eq(baddr, block_addr) * u64_eq(idx, member_idx),
        },
      ConstantInfo.Defn(_) => 0,
      ConstantInfo.Recr(_) => 0,
      ConstantInfo.Axio(_) => 0,
      ConstantInfo.Quot(_) => 0,
      ConstantInfo.CPrj(_) => 0,
      ConstantInfo.Muts(_) => 0,
    }
  }

  -- Find the position of the first member projection for (block_addr, member_idx)
  fn find_member_proj_position(
    block_addr: [G; 32], member_idx: [G; 8],
    consts: ConstantList, pos: [G; 8]
  ) -> [G; 8] {
    match consts {
      ConstantList.Nil => [0; 8],
      ConstantList.Cons(&c, &rest) =>
        match c {
          Constant.Mk(info, _, _, _) =>
            let found = is_member_proj_for(info, block_addr, member_idx);
            match found {
              1 => pos,
              0 => find_member_proj_position(block_addr, member_idx, rest, relaxed_u64_succ(pos)),
            },
        },
    }
  }

  -- Build recur_idxs: for each member of a mutual block, find its projection position
  fn build_recur_idxs(
    block_addr: [G; 32], remaining: [G; 8], member_idx: [G; 8],
    all_consts: ConstantList
  ) -> U64List {
    let done = u64_is_zero(remaining);
    match done {
      1 => U64List.Nil,
      0 =>
        let pos = find_member_proj_position(block_addr, member_idx, all_consts, [0; 8]);
        U64List.Cons(pos, store(build_recur_idxs(
          block_addr, relaxed_u64_pred(remaining), relaxed_u64_succ(member_idx), all_consts))),
    }
  }

  -- Check if a ConstantInfo is a CPrj for the given (block, induct_idx, ctor_cidx)
  fn is_ctor_proj_for(
    info: ConstantInfo, block_addr: [G; 32],
    induct_idx: [G; 8], ctor_cidx: [G; 8]
  ) -> G {
    match info {
      ConstantInfo.CPrj(prj) =>
        match prj {
          ConstructorProj.Mk(idx, cidx, baddr) =>
            address_eq(baddr, block_addr) * u64_eq(idx, induct_idx) * u64_eq(cidx, ctor_cidx),
        },
      ConstantInfo.Defn(_) => 0,
      ConstantInfo.Recr(_) => 0,
      ConstantInfo.Axio(_) => 0,
      ConstantInfo.Quot(_) => 0,
      ConstantInfo.IPrj(_) => 0,
      ConstantInfo.RPrj(_) => 0,
      ConstantInfo.DPrj(_) => 0,
      ConstantInfo.Muts(_) => 0,
    }
  }

  -- Find the position of a specific constructor projection
  fn find_ctor_position(
    block_addr: [G; 32], induct_idx: [G; 8], ctor_cidx: [G; 8],
    consts: ConstantList, pos: [G; 8]
  ) -> [G; 8] {
    match consts {
      ConstantList.Nil => [0; 8],
      ConstantList.Cons(&c, &rest) =>
        match c {
          Constant.Mk(info, _, _, _) =>
            let found = is_ctor_proj_for(info, block_addr, induct_idx, ctor_cidx);
            match found {
              1 => pos,
              0 => find_ctor_position(block_addr, induct_idx, ctor_cidx, rest, relaxed_u64_succ(pos)),
            },
        },
    }
  }

  -- Build KU64List of constructor positions for an inductive, ordered by cidx
  fn build_ctor_idxs(
    block_addr: [G; 32], induct_idx: [G; 8],
    remaining: [G; 8], ctor_cidx: [G; 8],
    all_consts: ConstantList
  ) -> KU64List {
    let done = u64_is_zero(remaining);
    match done {
      1 => KU64List.Nil,
      0 =>
        let pos = find_ctor_position(block_addr, induct_idx, ctor_cidx, all_consts, [0; 8]);
        KU64List.Cons(pos, store(build_ctor_idxs(
          block_addr, induct_idx, relaxed_u64_pred(remaining),
          relaxed_u64_succ(ctor_cidx), all_consts))),
    }
  }

  -- Concatenate two KU64Lists
  fn ku64_list_concat(a: KU64List, b: KU64List) -> KU64List {
    match a {
      KU64List.Nil => b,
      KU64List.Cons(v, &rest) =>
        KU64List.Cons(v, store(ku64_list_concat(rest, b))),
    }
  }

  -- Build rule_ctor_idxs for a recursor: all constructor positions across all
  -- inductive members of the mutual block, in member-then-cidx order
  fn build_member_rule_ctor_idxs(
    block_addr: [G; 32], members: MutConstList, member_idx: [G; 8],
    all_consts: ConstantList
  ) -> KU64List {
    match members {
      MutConstList.Nil => KU64List.Nil,
      MutConstList.Cons(mc, &rest) =>
        match mc {
          MutConst.Indc(ind) =>
            match ind {
              Inductive.Mk(_, _, _, _, _, _, _, _, &ctors) =>
                let num_ctors = count_constructor_list_(ctors);
                let this_ctors = build_ctor_idxs(block_addr, member_idx, num_ctors, [0; 8], all_consts);
                let rest_ctors = build_member_rule_ctor_idxs(block_addr, rest, relaxed_u64_succ(member_idx), all_consts);
                ku64_list_concat(this_ctors, rest_ctors),
            },
          MutConst.Defn(_) =>
            build_member_rule_ctor_idxs(block_addr, rest, relaxed_u64_succ(member_idx), all_consts),
          MutConst.Recr(_) =>
            build_member_rule_ctor_idxs(block_addr, rest, relaxed_u64_succ(member_idx), all_consts),
        },
    }
  }

  /- # ConvertInput construction from content -/

  -- Build a ConvertInput from a deserialized Constant, deriving all
  -- cross-references from the content-addressed data in-circuit.
  fn build_convert_input(
    constant: Constant,
    all_addrs: AddressList,
    all_consts: ConstantList,
    blobs: BlobList
  ) -> ConvertInput {
    match constant {
      Constant.Mk(info, &sharing, &refs, &univs) =>
        match info {
          ConstantInfo.Defn(defn) =>

            let ref_idxs = build_ref_idxs(refs, all_addrs);
            let lit_vals = build_lit_vals(refs, blobs);
            let ctx = ConvertCtx.Mk(store(sharing), store(ref_idxs), store(U64List.Nil), store(lit_vals), store(univs));
            ConvertInput.Mk(ctx, ConvertKind.CKDefn(defn, KHints.Abbrev)),

          ConstantInfo.Axio(axio) =>

            let ref_idxs = build_ref_idxs(refs, all_addrs);
            let lit_vals = build_lit_vals(refs, blobs);
            let ctx = ConvertCtx.Mk(store(sharing), store(ref_idxs), store(U64List.Nil), store(lit_vals), store(univs));
            ConvertInput.Mk(ctx, ConvertKind.CKAxio(axio)),

          ConstantInfo.Quot(quot) =>

            let ref_idxs = build_ref_idxs(refs, all_addrs);
            let lit_vals = build_lit_vals(refs, blobs);
            let ctx = ConvertCtx.Mk(store(sharing), store(ref_idxs), store(U64List.Nil), store(lit_vals), store(univs));
            ConvertInput.Mk(ctx, ConvertKind.CKQuot(quot)),

          ConstantInfo.Recr(recr) =>
            let ref_idxs = build_ref_idxs(refs, all_addrs);
            let lit_vals = build_lit_vals(refs, blobs);
            let block_addr = find_block_addr_from_refs(refs, blobs);
            let block_const = load_verified_constant(block_addr);
            match block_const {
              Constant.Mk(block_info, _, _, _) =>
                match block_info {
                  ConstantInfo.Muts(&members) =>
                    let num_members = count_mut_const_list_(members);
                    let recur_idxs = build_recur_idxs(block_addr, num_members, [0; 8], all_consts);
                    let rule_ctor_idxs = build_member_rule_ctor_idxs(block_addr, members, [0; 8], all_consts);
                    let ctx = ConvertCtx.Mk(store(sharing), store(ref_idxs), store(recur_idxs), store(lit_vals), store(univs));
                    ConvertInput.Mk(ctx, ConvertKind.CKRecr(recr, store(rule_ctor_idxs))),
                },
            },

          ConstantInfo.IPrj(prj) =>

            match prj {
              InductiveProj.Mk(idx, block_addr) =>
                let block_const = load_verified_constant(block_addr);
                match block_const {
                  Constant.Mk(block_info, &block_sharing, &block_refs, &block_univs) =>
                    let ref_idxs = build_ref_idxs(block_refs, all_addrs);
                    let lit_vals = build_lit_vals(block_refs, blobs);
                    match block_info {
                      ConstantInfo.Muts(&members) =>
                        let num_members = count_mut_const_list_(members);
                        let recur_idxs = build_recur_idxs(block_addr, num_members, [0; 8], all_consts);
                        let ctx = ConvertCtx.Mk(store(block_sharing), store(ref_idxs), store(recur_idxs), store(lit_vals), store(block_univs));
                        let mc = mut_const_list_lookup(members, idx);
                        match mc {
                          MutConst.Indc(ind) =>
                            match ind {
                              Inductive.Mk(_, _, _, _, _, _, _, _, &ctors) =>
                                let num_ctors = count_constructor_list_(ctors);
                                let ctor_idxs = build_ctor_idxs(block_addr, idx, num_ctors, [0; 8], all_consts);
                                ConvertInput.Mk(ctx, ConvertKind.CKIndc(ind, store(ctor_idxs))),
                            },
                        },
                    },
                },
            },

          ConstantInfo.CPrj(prj) =>

            match prj {
              ConstructorProj.Mk(idx, cidx, block_addr) =>
                let block_const = load_verified_constant(block_addr);
                match block_const {
                  Constant.Mk(block_info, &block_sharing, &block_refs, &block_univs) =>
                    let ref_idxs = build_ref_idxs(block_refs, all_addrs);
                    let lit_vals = build_lit_vals(block_refs, blobs);
                    match block_info {
                      ConstantInfo.Muts(&members) =>
                        let num_members = count_mut_const_list_(members);
                        let recur_idxs = build_recur_idxs(block_addr, num_members, [0; 8], all_consts);
                        let ctx = ConvertCtx.Mk(store(block_sharing), store(ref_idxs), store(recur_idxs), store(lit_vals), store(block_univs));
                        let mc = mut_const_list_lookup(members, idx);
                        match mc {
                          MutConst.Indc(ind) =>
                            match ind {
                              Inductive.Mk(_, _, _, _, _, _, _, _, &ctors) =>
                                let ctor = constructor_list_lookup(ctors, cidx);
                                let induct_pos = find_member_proj_position(block_addr, idx, all_consts, [0; 8]);
                                ConvertInput.Mk(ctx, ConvertKind.CKCtor(ctor, induct_pos)),
                            },
                        },
                    },
                },
            },

          ConstantInfo.RPrj(prj) =>

            match prj {
              RecursorProj.Mk(idx, block_addr) =>
                let block_const = load_verified_constant(block_addr);
                match block_const {
                  Constant.Mk(block_info, &block_sharing, &block_refs, &block_univs) =>
                    let ref_idxs = build_ref_idxs(block_refs, all_addrs);
                    let lit_vals = build_lit_vals(block_refs, blobs);
                    match block_info {
                      ConstantInfo.Muts(&members) =>
                        let num_members = count_mut_const_list_(members);
                        let recur_idxs = build_recur_idxs(block_addr, num_members, [0; 8], all_consts);
                        let ctx = ConvertCtx.Mk(store(block_sharing), store(ref_idxs), store(recur_idxs), store(lit_vals), store(block_univs));
                        let mc = mut_const_list_lookup(members, idx);
                        match mc {
                          MutConst.Recr(recr) =>
                            let rule_ctor_idxs = build_member_rule_ctor_idxs(block_addr, members, [0; 8], all_consts);
                            ConvertInput.Mk(ctx, ConvertKind.CKRecr(recr, store(rule_ctor_idxs))),
                        },
                    },
                },
            },

          ConstantInfo.DPrj(prj) =>

            match prj {
              DefinitionProj.Mk(idx, block_addr) =>
                let block_const = load_verified_constant(block_addr);
                match block_const {
                  Constant.Mk(block_info, &block_sharing, &block_refs, &block_univs) =>
                    let ref_idxs = build_ref_idxs(block_refs, all_addrs);
                    let lit_vals = build_lit_vals(block_refs, blobs);
                    match block_info {
                      ConstantInfo.Muts(&members) =>
                        let num_members = count_mut_const_list_(members);
                        let recur_idxs = build_recur_idxs(block_addr, num_members, [0; 8], all_consts);
                        let ctx = ConvertCtx.Mk(store(block_sharing), store(ref_idxs), store(recur_idxs), store(lit_vals), store(block_univs));
                        let mc = mut_const_list_lookup(members, idx);
                        match mc {
                          MutConst.Defn(defn) =>
                            ConvertInput.Mk(ctx, ConvertKind.CKDefn(defn, KHints.Abbrev)),
                        },
                    },
                },
            },
        },
    }
  }

  -- Build ConvertInputList from all constants, skipping Muts blocks
  -- (Muts are containers accessed via projection constants)
  fn build_convert_input_list(
    consts: ConstantList,
    all_addrs: AddressList,
    all_consts: ConstantList,
    blobs: BlobList
  ) -> ConvertInputList {
    match consts {
      ConstantList.Nil => ConvertInputList.Nil,
      ConstantList.Cons(&c, &rest) =>
        match c {
          Constant.Mk(info, _, _, _) =>
            match info {
              ConstantInfo.Muts(_) =>
                build_convert_input_list(rest, all_addrs, all_consts, blobs),
              _ =>
                let input = build_convert_input(c, all_addrs, all_consts, blobs);
                ConvertInputList.Cons(store(input), store(build_convert_input_list(rest, all_addrs, all_consts, blobs))),
            },
        },
    }
  }

  -- Check if an address is already in a list
  fn address_in_list(addr: [G; 32], list: AddressList) -> G {
    match list {
      AddressList.Nil => 0,
      AddressList.Cons(a, &rest) =>
        let eq = address_eq(addr, a);
        match eq {
          1 => 1,
          0 => address_in_list(addr, rest),
        },
    }
  }

  -- Concatenate two AddressLists
  fn address_list_concat(a: AddressList, b: AddressList) -> AddressList {
    match a {
      AddressList.Nil => b,
      AddressList.Cons(addr, &rest) =>
        AddressList.Cons(addr, store(address_list_concat(rest, b))),
    }
  }

  -- Recursively load constants and their transitive dependencies.
  -- Processes one address at a time from a worklist, deduplicating by
  -- checking the visited set. Blob addresses (from pre-loaded blob table)
  -- are skipped since they are not constants.
  -- For projection constants (IPrj, CPrj, RPrj, DPrj), also follows the
  -- Muts block's refs so that all dependencies of block members are loaded.
  fn load_with_deps(
    addr: [G; 32],
    worklist: AddressList,
    visited_addrs: AddressList,
    visited_consts: ConstantList,
    blobs: BlobList
  ) -> (AddressList, ConstantList) {
    let already = address_in_list(addr, visited_addrs);
    let blob = is_blob(addr, blobs);
    let skip = g_or(already, blob);
    match skip {
      1 =>
        match worklist {
          AddressList.Nil => (visited_addrs, visited_consts),
          AddressList.Cons(next, &rest) =>
            load_with_deps(next, rest, visited_addrs, visited_consts, blobs),
        },
      0 =>
        let new_addrs = AddressList.Cons(addr, store(visited_addrs));
        let constant = load_verified_constant(addr);
        let new_consts = ConstantList.Cons(store(constant), store(visited_consts));
        match constant {
          Constant.Mk(info, _, &refs, _) =>
            -- For projections, also add the Muts block address so its
            -- refs (shared deps for all members) get followed.
            let block_addr = get_proj_block_addr(info);
            match address_eq(block_addr, [0; 32]) {
              1 =>
                let combined_refs = address_list_concat(refs, AddressList.Nil);
                let next_worklist = address_list_concat(combined_refs, worklist);
                match next_worklist {
                  AddressList.Nil => (new_addrs, new_consts),
                  AddressList.Cons(next, &rest) =>
                    load_with_deps(next, rest, new_addrs, new_consts, blobs),
                },
              0 =>
                let combined_refs = address_list_concat(
                  refs,
                  AddressList.Cons(block_addr, store(AddressList.Nil))
                );
                let next_worklist = address_list_concat(combined_refs, worklist);
                match next_worklist {
                  AddressList.Nil => (new_addrs, new_consts),
                  AddressList.Cons(next, &rest) =>
                    load_with_deps(next, rest, new_addrs, new_consts, blobs),
                },
            },
        },
    }
  }

  -- Filter Muts blocks out of an AddressList (paired with ConstantList).
  -- Muts blocks are containers accessed via projections; they should not
  -- appear in the kernel constant list so that positional indices are correct.
  fn filter_muts_addrs(consts: ConstantList, addrs: AddressList) -> AddressList {
    match consts {
      ConstantList.Nil => AddressList.Nil,
      ConstantList.Cons(&c, &rest_consts) =>
        match addrs {
          AddressList.Cons(addr, &rest_addrs) =>
            match c {
              Constant.Mk(info, _, _, _) =>
                match info {
                  ConstantInfo.Muts(_) =>
                    filter_muts_addrs(rest_consts, rest_addrs),
                  _ =>
                    AddressList.Cons(addr, store(filter_muts_addrs(rest_consts, rest_addrs))),
                },
            },
        },
    }
  }

  -- Filter Muts blocks out of a ConstantList.
  fn filter_muts_consts(consts: ConstantList) -> ConstantList {
    match consts {
      ConstantList.Nil => ConstantList.Nil,
      ConstantList.Cons(&c, &rest) =>
        match c {
          Constant.Mk(info, _, _, _) =>
            match info {
              ConstantInfo.Muts(_) =>
                filter_muts_consts(rest),
              _ =>
                ConstantList.Cons(store(c), store(filter_muts_consts(rest))),
            },
        },
    }
  }

  -- Full kernel check pipeline.
  -- Transitively loads all dependencies of the target constant from IOBuffer,
  -- verifies blake3 hashes, converts to kernel types, and typechecks.
  fn kernel_check_test(target_addr: [G; 32]) {
    let blobs = load_blob_table();
    let (all_addrs, all_consts) = load_with_deps(
      target_addr, AddressList.Nil, AddressList.Nil, ConstantList.Nil, blobs);
    -- Filter out Muts blocks so positional indices match the kernel constant list
    let kernel_addrs = filter_muts_addrs(all_consts, all_addrs);
    let kernel_consts = filter_muts_consts(all_consts);
    let inputs = build_convert_input_list(kernel_consts, kernel_addrs, kernel_consts, blobs);
    let k_consts = convert_all(inputs);
    let _result = k_check_all(k_consts, k_consts);
    ()
  }

  /- # Benchmark entrypoints -/

  fn ixon_serde_blake3_bench(n: G) {
    match n {
      0 => (),
      _ =>
        let n_minus_1 = n - 1;
        let (idx, len) = io_get_info([n_minus_1]);
        let bytes = read_byte_stream(idx, len);
        let (const, rest) = get_constant(bytes);
        assert_eq!(rest, ByteStream.Nil);
        let bytes2 = put_constant(const, ByteStream.Nil);
        assert_eq!(blake3(bytes), blake3(bytes2));
        ixon_serde_blake3_bench(n_minus_1),
    }
  }
⟧

def ixVM : Except Aiur.Global Aiur.Toplevel := do
  let vm ← byteStream.merge blake3
  let vm ← vm.merge ixon
  let vm ← vm.merge ixonSerialize
  let vm ← vm.merge ixonDeserialize
  let vm ← vm.merge convert
  let vm ← vm.merge kernelTypes
  let vm ← vm.merge kernel
  vm.merge entrypoints

end IxVM

end
