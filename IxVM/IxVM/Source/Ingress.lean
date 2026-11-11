import Aiur.Modules.Function

/-! # IxVM module `Ingress`

Loading constants and blobs by address, checked against their hashes.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module Ingress where

def load_verified_constant := aiur_fn⟦
  fn load_verified_constant(addr: Bytes::AddressRef) -> Ixon::Constant {
      let raw = (*(addr));
      let (idx, len) = IxVMCompat::io_get_info(2, raw);
      let bytes = IxByteStream::read_finite_byte_stream(2, idx, len);
      Blake3::verify_bytes_against(bytes, raw);
      let (constant, rest) = IxonDeserialize::get_constant(bytes);
      let Lists::Node::Nil = (*(rest));
      constant
    }
⟧

def definition_hint := aiur_fn⟦
  fn definition_hint(addr: Bytes::AddressRef, d: Ixon::Definition) -> Field {
      match d {
        Ixon::Definition::Mk(kind, _, _, _, _) => {
          match kind {
            Ixon::DefKind::Definition => {  load_constant_hint(addr) } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧


  -- Port divergence: the constant's tag is a typed hint on channel 3.

def load_constant_hint := aiur_fn⟦
  fn load_constant_hint(addr: Bytes::AddressRef) -> Field {
      hint::<Field>("ixvm.io.tag", (3, Blake3::address_to_fields((*(addr)))))
    }
⟧

def load_verified_blob := aiur_fn⟦
  fn load_verified_blob(addr: Bytes::AddressRef) -> Bytes::Stream {
      let raw = (*(addr));
      let (idx, len) = IxVMCompat::io_get_info(4, raw);
      let bytes = IxByteStream::read_finite_byte_stream(4, idx, len);
      Blake3::verify_bytes_against(bytes, raw);
      bytes
    }
⟧

def defn_is_unsafe_ci := aiur_fn⟦
  fn defn_is_unsafe_ci(kind: Ixon::DefKind, safety: Ixon::DefinitionSafety) -> Field {
      match kind {
        Ixon::DefKind::Theorem => {  0 } ,
        Ixon::DefKind::Opaque => {
          match safety {
            Ixon::DefinitionSafety::Unsafe => {  1 } ,
            _ => {  0 } ,
          } } ,
        Ixon::DefKind::Definition => {
          match safety {
            Ixon::DefinitionSafety::Safe => {  0 } ,
            _ => {  1 } ,
          } } ,
      }
    }
⟧

def defn_member_recur_addrs := aiur_fn⟦
  fn defn_member_recur_addrs(d: Ixon::Definition, members: Lists::List<Ixon::MutConst>,
                                    block_addr: Bytes::AddressRef) -> Lists::List<Bytes::AddressRef> {
      match d {
        Ixon::Definition::Mk(kind, safety, _, _, _) => {
          match defn_is_unsafe_ci(kind, safety) {
            0 => {  (&(Lists::Node::Nil)) } ,
            _ => {  build_recur_addrs(members, block_addr) } ,
          } } ,
      }
    }
⟧

def get_ci := aiur_fn⟦
  fn get_ci(addr: Bytes::AddressRef) -> &KernelTypes::KConstantInfo {
      let c = load_verified_constant(addr);
      match c {
        Ixon::Constant::Mk(info, sharing, refs, univs) => {
          match info {
            Ixon::ConstantInfo::Defn(defn) => {
              let hint = definition_hint(addr, defn);

              let self_recur = match defn {
                Ixon::Definition::Mk(kind, safety, _, _, _) => {
                  match defn_is_unsafe_ci(kind, safety) {
                    0 => {  (&(Lists::Node::Nil)) } ,
                    _ => {  (&(Lists::Node::Cons(addr, (&(Lists::Node::Nil))))) } ,
                  } } ,
              };
              (&(Convert::convert_definition(defn, sharing, refs,
                                            self_recur, univs, hint, addr, 0))) } ,
            Ixon::ConstantInfo::Axio(axio) => {

              (&(Convert::convert_axiom(axio, sharing, refs,
                                       (&(Lists::Node::Nil)), univs, addr))) } ,
            Ixon::ConstantInfo::Quot(quot) => {
              (&(Convert::convert_quotient(quot, sharing, refs,
                                          (&(Lists::Node::Nil)), univs, addr))) } ,
            Ixon::ConstantInfo::DPrj(prj) => {
              match prj {
                Ixon::DefinitionProj::Mk(idx, block_addr) => {
                  get_ci_dprj(addr, idx, block_addr) } ,
              } } ,
            Ixon::ConstantInfo::IPrj(prj) => {
              match prj {
                Ixon::InductiveProj::Mk(idx, block_addr) => {
                  get_ci_iprj(block_addr, UInt64::to_field(idx)) } ,
              } } ,
            Ixon::ConstantInfo::CPrj(prj) => {
              match prj {
                Ixon::ConstructorProj::Mk(idx, cidx, block_addr) => {
                  get_ci_cprj(block_addr, UInt64::to_field(idx), UInt64::to_field(cidx)) } ,
              } } ,
            Ixon::ConstantInfo::RPrj(prj) => {
              match prj {
                Ixon::RecursorProj::Mk(idx, block_addr) => {
                  get_ci_rprj(block_addr, UInt64::to_field(idx)) } ,
              } } ,

            Ixon::ConstantInfo::Recr(recr) => {

              let self_recur = (&(Lists::Node::Cons(addr, (&(Lists::Node::Nil)))));
              (&(Convert::convert_recursor(recr, addr, 0,
                                          sharing, refs, self_recur, univs, 0))) } ,
          } } ,
      }
    }
⟧

def get_ci_dprj := aiur_fn⟦
  fn get_ci_dprj(dprj_addr: Bytes::AddressRef, idx: UInt64::U64, block_addr: Bytes::AddressRef) -> &KernelTypes::KConstantInfo {
      KernelCheck::check_block_member_kinds(block_addr);
      let block_c = load_verified_constant(block_addr);
      match block_c {
        Ixon::Constant::Mk(info, sharing, refs, univs) => {
          match info {
            Ixon::ConstantInfo::Muts(members) => {
              let mc = WordLists::lookup_u64(members, idx);
              match mc {
                Ixon::MutConst::Defn(d) => {
                  let hint = definition_hint(dprj_addr, d);
                  let recur_addrs =
                    defn_member_recur_addrs(d, members, block_addr);
                  (&(Convert::convert_definition(d, sharing, refs, recur_addrs, univs, hint,
                    block_addr, Convert::muts_root_offset(members, UInt64::to_field(idx))))) } ,
              } } ,
          } } ,
      }
    }
⟧

def get_ci_iprj := aiur_fn⟦
  fn get_ci_iprj(block_addr: Bytes::AddressRef, idx: Field) -> &KernelTypes::KConstantInfo {
      let block_c = load_verified_constant(block_addr);
      match block_c {
        Ixon::Constant::Mk(info, sharing, refs, univs) => {
          match info {
            Ixon::ConstantInfo::Muts(members) => {
              let mc = muts_member_at(members, idx);
              match mc {
                Ixon::MutConst::Indc(ind) => {
                  let recur_addrs = build_recur_addrs(members, block_addr);
                  (&(Convert::convert_inductive(ind, block_addr, idx,
                                               sharing, refs, recur_addrs, univs, Convert::muts_root_offset(members, idx)))) } ,
              } } ,
          } } ,
      }
    }
⟧

def get_ci_cprj := aiur_fn⟦
  fn get_ci_cprj(block_addr: Bytes::AddressRef, idx: Field, cidx: Field) -> &KernelTypes::KConstantInfo {
      let block_c = load_verified_constant(block_addr);
      match block_c {
        Ixon::Constant::Mk(info, sharing, refs, univs) => {
          match info {
            Ixon::ConstantInfo::Muts(members) => {
              let mc = muts_member_at(members, idx);
              match mc {
                Ixon::MutConst::Indc(ind) => {
                  match ind {
                    Ixon::Inductive::Mk(_, _, _, _, _, ctors) => {
                      let c = Convert::ctor_at(ctors, cidx);
                      let recur_addrs = build_recur_addrs(members, block_addr);
                      (&(Convert::convert_constructor(c, block_addr, idx,
                                                    sharing, refs, recur_addrs, univs,
                                                    (Convert::muts_root_offset(members, idx) + 1) + cidx))) } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

def get_ci_rprj := aiur_fn⟦
  fn get_ci_rprj(block_addr: Bytes::AddressRef, idx: Field) -> &KernelTypes::KConstantInfo {
  let block_c = load_verified_constant(block_addr);
      match block_c {
        Ixon::Constant::Mk(info, sharing, refs, univs) => {
          match info {
            Ixon::ConstantInfo::Muts(members) => {
              let mc = muts_member_at(members, idx);
              match mc {
                Ixon::MutConst::Recr(r) => {
                  let recur_addrs = build_recur_addrs(members, block_addr);
                  (&(Convert::convert_recursor(r, block_addr, idx,
                                             sharing, refs, recur_addrs, univs, Convert::muts_root_offset(members, idx)))) } ,
              } } ,
          } } ,
      }
    }
⟧

def muts_member_at := aiur_fn⟦
  fn muts_member_at(members: Lists::List<Ixon::MutConst>, idx: Field) -> Ixon::MutConst {
      match (*(members)) {
        Lists::Node::Cons(m, rest) => {
          match idx {
            0 => {  m } ,
            _ => {  muts_member_at(rest, idx - 1) } ,
          } } ,
      }
    }
⟧

def projection_addr := aiur_fn⟦
  fn projection_addr(members: Lists::List<Ixon::MutConst>, block_addr: Bytes::AddressRef, idx: Field) -> Bytes::AddressRef {
      let mc = muts_member_at(members, idx);
      let idx_u64 = UInt64::from_field(idx);
      let info = match mc {
        Ixon::MutConst::Defn(_) => {
          Ixon::ConstantInfo::DPrj(Ixon::DefinitionProj::Mk(idx_u64, block_addr)) } ,
        Ixon::MutConst::Indc(_) => {
          Ixon::ConstantInfo::IPrj(Ixon::InductiveProj::Mk(idx_u64, block_addr)) } ,
        Ixon::MutConst::Recr(_) => {
          Ixon::ConstantInfo::RPrj(Ixon::RecursorProj::Mk(idx_u64, block_addr)) } ,
      };
      let proj_c = Ixon::Constant::Mk(info,
                                (&(Lists::Node::Nil)),
                                (&(Lists::Node::Nil)),
                                (&(Lists::Node::Nil)));
      let bytes = IxonSerialize::put_constant(proj_c, (&(Lists::Node::Nil)));
      Blake3::bytes_to_addr(bytes)
    }
⟧

def build_recur_addrs := aiur_fn⟦
  fn build_recur_addrs(members: Lists::List<Ixon::MutConst>, block_addr: Bytes::AddressRef) -> Lists::List<Bytes::AddressRef> {
      build_recur_addrs_walk(members, block_addr, members, 0)
    }
⟧

def build_recur_addrs_walk := aiur_fn⟦
  fn build_recur_addrs_walk(all_members: Lists::List<Ixon::MutConst>, block_addr: Bytes::AddressRef,
                                   cur: Lists::List<Ixon::MutConst>, idx: Field) -> Lists::List<Bytes::AddressRef> {
      match (*(cur)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(_, rest) => {
          (&(Lists::Node::Cons(
            projection_addr(all_members, block_addr, idx),
            build_recur_addrs_walk(all_members, block_addr, rest, idx + 1)))) } ,
      }
    }
⟧

end

end IxVM
