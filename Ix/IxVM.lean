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

  -- Load a constant from IOBuffer by address, assert blake3, deserialize
  fn load_verified_constant(addr: [G; 32]) -> Constant {
    let (idx, len) = io_get_info(addr);
    let bytes = read_byte_stream(idx, len);
    let h = blake3(bytes);
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

  -- Find the position of an address in the ordered address list
  fn find_addr_position(target: [G; 32], addrs: AddressList, pos: [G; 8]) -> [G; 8] {
    match addrs {
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

  -- Build an all-zero lit_vals list matching the refs length
  fn build_zero_lit_vals(refs: AddressList) -> U64List {
    match refs {
      AddressList.Nil => U64List.Nil,
      AddressList.Cons(_, &rest) =>
        U64List.Cons([0; 8], store(build_zero_lit_vals(rest))),
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
      1 => KU64List.KUNil,
      0 =>
        let pos = find_ctor_position(block_addr, induct_idx, ctor_cidx, all_consts, [0; 8]);
        KU64List.KUCons(pos, store(build_ctor_idxs(
          block_addr, induct_idx, relaxed_u64_pred(remaining),
          relaxed_u64_succ(ctor_cidx), all_consts))),
    }
  }

  -- Concatenate two KU64Lists
  fn ku64_list_concat(a: KU64List, b: KU64List) -> KU64List {
    match a {
      KU64List.KUNil => b,
      KU64List.KUCons(v, &rest) =>
        KU64List.KUCons(v, store(ku64_list_concat(rest, b))),
    }
  }

  -- Build rule_ctor_idxs for a recursor: all constructor positions across all
  -- inductive members of the mutual block, in member-then-cidx order
  fn build_member_rule_ctor_idxs(
    block_addr: [G; 32], members: MutConstList, member_idx: [G; 8],
    all_consts: ConstantList
  ) -> KU64List {
    match members {
      MutConstList.Nil => KU64List.KUNil,
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
    all_consts: ConstantList
  ) -> ConvertInput {
    match constant {
      Constant.Mk(info, &sharing, &refs, &univs) =>
        match info {
          ConstantInfo.Defn(defn) =>
            let ref_idxs = build_ref_idxs(refs, all_addrs);
            let lit_vals = build_zero_lit_vals(refs);
            let ctx = ConvertCtx.Mk(store(sharing), store(ref_idxs), store(U64List.Nil), store(lit_vals), store(univs));
            ConvertInput.Mk(ctx, ConvertKind.CKDefn(defn, KHints.HAbbrev)),

          ConstantInfo.Axio(axio) =>
            let ref_idxs = build_ref_idxs(refs, all_addrs);
            let lit_vals = build_zero_lit_vals(refs);
            let ctx = ConvertCtx.Mk(store(sharing), store(ref_idxs), store(U64List.Nil), store(lit_vals), store(univs));
            ConvertInput.Mk(ctx, ConvertKind.CKAxio(axio)),

          ConstantInfo.Quot(quot) =>
            let ref_idxs = build_ref_idxs(refs, all_addrs);
            let lit_vals = build_zero_lit_vals(refs);
            let ctx = ConvertCtx.Mk(store(sharing), store(ref_idxs), store(U64List.Nil), store(lit_vals), store(univs));
            ConvertInput.Mk(ctx, ConvertKind.CKQuot(quot)),

          ConstantInfo.Recr(recr) =>
            let ref_idxs = build_ref_idxs(refs, all_addrs);
            let lit_vals = build_zero_lit_vals(refs);
            let ctx = ConvertCtx.Mk(store(sharing), store(ref_idxs), store(U64List.Nil), store(lit_vals), store(univs));
            ConvertInput.Mk(ctx, ConvertKind.CKRecr(recr, store(KU64List.KUNil))),

          ConstantInfo.IPrj(prj) =>
            match prj {
              InductiveProj.Mk(idx, block_addr) =>
                let block_const = load_verified_constant(block_addr);
                match block_const {
                  Constant.Mk(block_info, &block_sharing, &block_refs, &block_univs) =>
                    let ref_idxs = build_ref_idxs(block_refs, all_addrs);
                    let lit_vals = build_zero_lit_vals(block_refs);
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
                    let lit_vals = build_zero_lit_vals(block_refs);
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
                    let lit_vals = build_zero_lit_vals(block_refs);
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
                    let lit_vals = build_zero_lit_vals(block_refs);
                    match block_info {
                      ConstantInfo.Muts(&members) =>
                        let num_members = count_mut_const_list_(members);
                        let recur_idxs = build_recur_idxs(block_addr, num_members, [0; 8], all_consts);
                        let ctx = ConvertCtx.Mk(store(block_sharing), store(ref_idxs), store(recur_idxs), store(lit_vals), store(block_univs));
                        let mc = mut_const_list_lookup(members, idx);
                        match mc {
                          MutConst.Defn(defn) =>
                            ConvertInput.Mk(ctx, ConvertKind.CKDefn(defn, KHints.HAbbrev)),
                        },
                    },
                },
            },
        },
    }
  }

  -- Build ConvertInputList from all constants
  fn build_convert_input_list(
    consts: ConstantList,
    all_addrs: AddressList,
    all_consts: ConstantList
  ) -> ConvertInputList {
    match consts {
      ConstantList.Nil => ConvertInputList.Nil,
      ConstantList.Cons(&c, &rest) =>
        let input = build_convert_input(c, all_addrs, all_consts);
        ConvertInputList.Cons(store(input), store(build_convert_input_list(rest, all_addrs, all_consts))),
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
  -- checking the visited set. When a new constant is loaded, its refs
  -- are prepended to the worklist.
  fn load_with_deps(
    addr: [G; 32],
    worklist: AddressList,
    visited_addrs: AddressList,
    visited_consts: ConstantList
  ) -> (AddressList, ConstantList) {
    let already = address_in_list(addr, visited_addrs);
    match already {
      1 =>
        -- Already loaded, continue with the rest of the worklist
        match worklist {
          AddressList.Nil => (visited_addrs, visited_consts),
          AddressList.Cons(next, &rest) =>
            load_with_deps(next, rest, visited_addrs, visited_consts),
        },
      0 =>
        -- Load and verify this constant
        let constant = load_verified_constant(addr);
        match constant {
          Constant.Mk(_, _, &refs, _) =>
            let new_addrs = AddressList.Cons(addr, store(visited_addrs));
            let new_consts = ConstantList.Cons(store(constant), store(visited_consts));
            -- Prepend this constant's refs to the worklist
            let next_worklist = address_list_concat(refs, worklist);
            match next_worklist {
              AddressList.Nil => (new_addrs, new_consts),
              AddressList.Cons(next, &rest) =>
                load_with_deps(next, rest, new_addrs, new_consts),
            },
        },
    }
  }

  -- Full kernel check pipeline.
  -- Transitively loads all dependencies of the target constant from IOBuffer,
  -- verifies blake3 hashes, converts to kernel types, and typechecks.
  fn kernel_check_test(target_addr: [G; 32]) {
    let (all_addrs, all_consts) = load_with_deps(
      target_addr, AddressList.Nil, AddressList.Nil, ConstantList.Nil);
    let inputs = build_convert_input_list(all_consts, all_addrs, all_consts);
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
