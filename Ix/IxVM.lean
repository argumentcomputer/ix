import Ix.Aiur.Meta
import Ix.IxVM.ByteStream
import Ix.IxVM.Blake3
import Ix.IxVM.Ixon
import Ix.IxVM.IxonSerialize
import Ix.IxVM.IxonDeserialize

namespace IxVM

def entrypoints := ⟦
  /- # Test entrypoints -/

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
⟧

def ixVM : Except Aiur.Global Aiur.Toplevel := do
  let vm ← byteStream.merge blake3
  let vm ← vm.merge ixon
  let vm ← vm.merge ixonSerialize
  let vm ← vm.merge ixonDeserialize
  vm.merge entrypoints

end IxVM
