import Ix.Aiur.Meta
import Ix.IxVM.ByteStream
import Ix.IxVM.Blake3
import Ix.IxVM.Ixon
import Ix.IxVM.IxonSerialize
import Ix.IxVM.IxonDeserialize

namespace IxVM

def entrypoints := ⟦
  /- # Test entrypoints -/

  fn blake3_test() -> [[G; 4]; 8] {
    let (idx, len) = io_get_info([0]);
    let byte_stream = read_byte_stream(idx, len);
    blake3(byte_stream)
  }

  fn ixon_blake3_test(h: [[G; 4]; 8]) {
    let key = [
      h[0][0], h[0][1], h[0][2], h[0][3],
      h[1][0], h[1][1], h[1][2], h[1][3],
      h[2][0], h[2][1], h[2][2], h[2][3],
      h[3][0], h[3][1], h[3][2], h[3][3],
      h[4][0], h[4][1], h[4][2], h[4][3],
      h[5][0], h[5][1], h[5][2], h[5][3],
      h[6][0], h[6][1], h[6][2], h[6][3],
      h[7][0], h[7][1], h[7][2], h[7][3]
    ];
    let (idx, len) = io_get_info(key);
    let bytes_unconstrained = read_byte_stream(idx, len);
    let ixon_unconstrained = deserialize(bytes_unconstrained);
    let bytes = serialize(ixon_unconstrained);
    let bytes_hash = blake3(bytes);
    assert_eq!(h, bytes_hash);
  }

  /- # Benchmark entrypoints -/

  fn blake3_bench(num_hashes: G) -> G {
    let num_hashes_pred = num_hashes - 1;
    let key = [num_hashes_pred];
    let (idx, len) = io_get_info(key);
    let byte_stream = read_byte_stream(idx, len);
    let _x = blake3(byte_stream);
    match num_hashes_pred {
      0 => 0,
      _ => blake3_bench(num_hashes_pred),
    }
  }

  fn serde_bench_addr_list(addr_list: AddressList) {
    match addr_list {
      AddressList.Nil => (),
      AddressList.Cons(Address.Bytes(addr), tail_ptr) =>
        let _x = serde_bench(addr);
        serde_bench_addr_list(load(tail_ptr)),
    }
  }

  fn serde_bench_recursor_rules(rules_list: RecursorRuleList) {
    match rules_list {
      RecursorRuleList.Nil => (),
      RecursorRuleList.Cons(_, Address.Bytes(addr), tail_ptr) =>
        let _x = serde_bench(addr);
        serde_bench_recursor_rules(load(tail_ptr)),
    }
  }

  fn serde_bench_constructors(ctors: ConstructorList) {
    match ctors {
      ConstructorList.Nil => (),
      ConstructorList.Cons(_, _, _, _, _, Address.Bytes(addr), tail_ptr) =>
        let _x = serde_bench(addr);
        serde_bench_constructors(load(tail_ptr)),
    }
  }

  fn serde_bench_mut_consts(mut_consts: MutConstList) {
    match mut_consts {
      MutConstList.Nil => (),
      MutConstList.ConsDefn(_, _, _, Address.Bytes(a), Address.Bytes(b), tail_ptr) =>
        let _x = serde_bench(a);
        let _y = serde_bench(b);
        serde_bench_mut_consts(load(tail_ptr)),
      MutConstList.ConsIndc(_, _, _, _, _, _, _, Address.Bytes(a), ctor_list, tail_ptr) =>
        let _x = serde_bench(a);
        let _y = serde_bench_constructors(ctor_list);
        serde_bench_mut_consts(load(tail_ptr)),
      MutConstList.ConsRecr(_, _, _, _, _, _, _, Address.Bytes(a), rules_list, tail_ptr) =>
        let _x = serde_bench(a);
        let _y = serde_bench_recursor_rules(rules_list);
        serde_bench_mut_consts(load(tail_ptr)),
    }
  }

  fn serde_bench_ixon(ixon: Ixon) {
    match ixon {
      Ixon.NStr(Address.Bytes(a), Address.Bytes(b)) =>
        let _x = serde_bench(a);
        serde_bench(b),
      Ixon.NNum(Address.Bytes(a), Address.Bytes(b)) =>
        let _x = serde_bench(a);
        serde_bench(b),
      Ixon.USucc(Address.Bytes(a)) => serde_bench(a),
      Ixon.UMax(Address.Bytes(a), Address.Bytes(b)) =>
        let _x = serde_bench(a);
        serde_bench(b),
      Ixon.UIMax(Address.Bytes(a), Address.Bytes(b)) =>
        let _x = serde_bench(a);
        serde_bench(b),
      Ixon.ERef(Address.Bytes(a), addr_list) =>
        let _x = serde_bench(a);
        serde_bench_addr_list(addr_list),
      Ixon.ERec(_, addr_list) => serde_bench_addr_list(addr_list),
      Ixon.EPrj(Address.Bytes(a), _, Address.Bytes(b)) =>
        let _x = serde_bench(a);
        serde_bench(b),
      Ixon.ESort(Address.Bytes(a)) => serde_bench(a),
      Ixon.EStr(Address.Bytes(a)) => serde_bench(a),
      Ixon.ENat(Address.Bytes(a)) => serde_bench(a),
      Ixon.EApp(Address.Bytes(a), Address.Bytes(b)) =>
        let _x = serde_bench(a);
        serde_bench(b),
      Ixon.ELam(Address.Bytes(a), Address.Bytes(b)) =>
        let _x = serde_bench(a);
        serde_bench(b),
      Ixon.EAll(Address.Bytes(a), Address.Bytes(b)) =>
        let _x = serde_bench(a);
        serde_bench(b),
      Ixon.ELet(_, Address.Bytes(a), Address.Bytes(b), Address.Bytes(c)) =>
        let _x = serde_bench(a);
        let _y = serde_bench(b);
        serde_bench(c),
      Ixon.Defn(_, _, _, Address.Bytes(a), Address.Bytes(b)) =>
        let _x = serde_bench(a);
        serde_bench(b),
      Ixon.Recr(_, _, _, _, _, _, _, Address.Bytes(a), rules_list) =>
        let _x = serde_bench(a);
        serde_bench_recursor_rules(rules_list),
      Ixon.Axio(_, _, Address.Bytes(a)) => serde_bench(a),
      Ixon.Quot(_, _, Address.Bytes(a)) => serde_bench(a),
      Ixon.CPrj(_, _, Address.Bytes(a)) => serde_bench(a),
      Ixon.RPrj(_, Address.Bytes(a)) => serde_bench(a),
      Ixon.IPrj(_, Address.Bytes(a)) => serde_bench(a),
      Ixon.DPrj(_, Address.Bytes(a)) => serde_bench(a),
      Ixon.Muts(mut_consts) => serde_bench_mut_consts(mut_consts),
      _ => (),
    }
  }

  fn serde_bench(h: [[G; 4]; 8]) {
    let key = [
      h[0][0], h[0][1], h[0][2], h[0][3],
      h[1][0], h[1][1], h[1][2], h[1][3],
      h[2][0], h[2][1], h[2][2], h[2][3],
      h[3][0], h[3][1], h[3][2], h[3][3],
      h[4][0], h[4][1], h[4][2], h[4][3],
      h[5][0], h[5][1], h[5][2], h[5][3],
      h[6][0], h[6][1], h[6][2], h[6][3],
      h[7][0], h[7][1], h[7][2], h[7][3]
    ];
    let (idx, len) = io_get_info(key);
    let bytes_unconstrained = read_byte_stream(idx, len);
    let ixon_unconstrained = deserialize(bytes_unconstrained);
    let bytes = serialize(ixon_unconstrained);
    let bytes_hash = blake3(bytes);
    assert_eq!(h, bytes_hash);
    serde_bench_ixon(ixon_unconstrained)
  }
⟧

def ixVM : Except Aiur.Global Aiur.Toplevel := do
  let vm ← byteStream.merge blake3
  let vm ← vm.merge ixon
  let vm ← vm.merge ixonSerialize
  let vm ← vm.merge ixonDeserialize
  vm.merge entrypoints

end IxVM
