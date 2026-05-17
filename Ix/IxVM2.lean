module
public import Ix.Aiur.Meta
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
public import Ix.IxVM.Blake3
public import Ix.IxVM.Ingress
public import Ix.IxVM.Ixon
public import Ix.IxVM.IxonSerialize
public import Ix.IxVM.IxonDeserialize
public import Ix.IxVM.Convert
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel2.Primitive
public import Ix.IxVM.Kernel2.Check
public import Ix.IxVM.CheckHarness

public section

namespace IxVM2

def entrypoints := ⟦
  pub fn kernel_check_test(target_addr: [G; 32], check_deps: G) {
    let target = store(target_addr);
    let (k_consts, addrs) = ingress_with_primitives(target);
    match check_deps {
      0 =>
        let target_pos = find_addr_idx(target, addrs, 0);
        let ci = load(list_lookup(k_consts, target_pos));
        check_const(ci, target_pos, k_consts, addrs),
      _ => check_all(k_consts, k_consts, addrs),
    }
  }
⟧

def ixVM2 : Except Aiur.Global Aiur.Source.Toplevel := do
  let vm ← IxVM.core.merge IxVM.byteStream
  let vm ← vm.merge IxVM.blake3
  let vm ← vm.merge IxVM.ixon
  let vm ← vm.merge IxVM.ixonSerialize
  let vm ← vm.merge IxVM.ixonDeserialize
  let vm ← vm.merge IxVM.convert
  let vm ← vm.merge IxVM.ingress
  let vm ← vm.merge IxVM.kernelTypes
  let vm ← vm.merge IxVM.primitive
  let vm ← vm.merge IxVM.check
  vm.merge entrypoints

end IxVM2

end
