import Aiur.Library.Field.BN254.G1

/-! Canonical compressed G1 pairs as four little-endian 128-bit scalar chunks.
Byte membership and recomposition enforce the chunk bound before point decoding. -/
namespace Aiur.Library.Field.BN254.G1Encoding
open Aiur

theorem chunk_bound : 2^128 < BN254.modulus := by decide

def dependencies : Modules.Program Nat := G1.dependencies.append G1.declarations

def declarations : Modules.Program Nat := aiur_library% dependencies ⟦
module BN254G1Encoding {
  type Point=BN254G1::Point;
  inline fn pack(bytes:[Field;16])->Field {
    BN254Fq::byte(bytes[0]);
    BN254Fq::byte(bytes[1]);
    BN254Fq::byte(bytes[2]);
    BN254Fq::byte(bytes[3]);
    BN254Fq::byte(bytes[4]);
    BN254Fq::byte(bytes[5]);
    BN254Fq::byte(bytes[6]);
    BN254Fq::byte(bytes[7]);
    BN254Fq::byte(bytes[8]);
    BN254Fq::byte(bytes[9]);
    BN254Fq::byte(bytes[10]);
    BN254Fq::byte(bytes[11]);
    BN254Fq::byte(bytes[12]);
    BN254Fq::byte(bytes[13]);
    BN254Fq::byte(bytes[14]);
    BN254Fq::byte(bytes[15]);
    1 * bytes[0] + 256 * bytes[1] + 65536 * bytes[2] + 16777216 * bytes[3] + 4294967296 * bytes[4] + 1099511627776 * bytes[5] + 281474976710656 * bytes[6] + 72057594037927936 * bytes[7] + 18446744073709551616 * bytes[8] + 4722366482869645213696 * bytes[9] + 1208925819614629174706176 * bytes[10] + 309485009821345068724781056 * bytes[11] + 79228162514264337593543950336 * bytes[12] + 20282409603651670423947251286016 * bytes[13] + 5192296858534827628530496329220096 * bytes[14] + 1329227995784915872903807060280344576 * bytes[15]
  }
  fn chunk_bytes(value:Field)->[Field;16] {
    let bytes=hint::<[Field;16]>("bn254.g1.u128_bytes",value);
    assert_eq!(pack(bytes),value,"canonical 128-bit chunk");
    bytes
  }
  fn from_chunks(chunks:[Field;4])->(Point,Point) {
    let a=chunk_bytes(chunks[0]);let b=chunk_bytes(chunks[1]);
    let c=chunk_bytes(chunks[2]);let d=chunk_bytes(chunks[3]);
    let p0=BN254G1::from_bytes([a[0],a[1],a[2],a[3],a[4],a[5],a[6],a[7],a[8],a[9],a[10],a[11],a[12],a[13],a[14],a[15],b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7],b[8],b[9],b[10],b[11],b[12],b[13],b[14],b[15]]);
    let p1=BN254G1::from_bytes([c[0],c[1],c[2],c[3],c[4],c[5],c[6],c[7],c[8],c[9],c[10],c[11],c[12],c[13],c[14],c[15],d[0],d[1],d[2],d[3],d[4],d[5],d[6],d[7],d[8],d[9],d[10],d[11],d[12],d[13],d[14],d[15]]);
    (p0,p1)
  }
  fn to_chunks(a:Point,b:Point)->[Field;4] {
    let x=BN254G1::to_bytes(a);let y=BN254G1::to_bytes(b);
    [pack([x[0],x[1],x[2],x[3],x[4],x[5],x[6],x[7],x[8],x[9],x[10],x[11],x[12],x[13],x[14],x[15]]),pack([x[16],x[17],x[18],x[19],x[20],x[21],x[22],x[23],x[24],x[25],x[26],x[27],x[28],x[29],x[30],x[31]]),pack([y[0],y[1],y[2],y[3],y[4],y[5],y[6],y[7],y[8],y[9],y[10],y[11],y[12],y[13],y[14],y[15]]),pack([y[16],y[17],y[18],y[19],y[20],y[21],y[22],y[23],y[24],y[25],y[26],y[27],y[28],y[29],y[30],y[31]])]
  }
}
⟧

def program : Modules.Program BN254.F := (dependencies.append declarations).toField BN254.F
end Aiur.Library.Field.BN254.G1Encoding
