import Aiur.Modules.Frontend

/-! Deferred pairing operands use the shared strict four-u128 G1 codec. -/
namespace MultiStark.Source

def kzgAccumulator : Aiur.Modules.Program Nat := aiur⟦
module KzgAccumulator {
  inline fn pack(a: BN254G1::Point, b: BN254G1::Point) -> [Field;4] {
    BN254G1Encoding::to_chunks(a,b)
  }
  inline fn unpack(raw: [Field;4]) -> (BN254G1::Point,BN254G1::Point) {
    BN254G1Encoding::from_chunks(raw)
  }
}
⟧

end MultiStark.Source
