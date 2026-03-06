module
public import Ix.Aiur.Meta
public import Ix.IxVM.ByteStream
public import Ix.IxVM.Blake3
public import Ix.IxVM.Ixon
public import Ix.IxVM.IxonSerialize
public import Ix.IxVM.IxonDeserialize

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
  vm.merge entrypoints

end IxVM

end
