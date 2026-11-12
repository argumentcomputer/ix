import Aiur.Library.Field.BN254.Pairing.Fp12
import Aiur.Library.Field.BN254.G1Encoding

/-! Two-pair BN254 product checks against trusted fixed G2 operands.
Prepared lines are immutable compiler tables. Their generator validates the
anchors and their subgroup membership; they are not witness advice. -/
namespace Aiur.Library.Field.BN254.Pairing
open Aiur

def dependencies : Modules.Program Nat :=
  Fp12.dependencies.append Fp12.declarations |>.append Library.List.declarations
    |>.append FqRelation.declarations |>.append G1.declarations |>.append G1Encoding.declarations

private def implementation : Modules.Program Nat := aiur_library% dependencies ⟦
module BN254Pairing {
  type Point = BN254G1::Point;
  type Fp12 = BN254Fp12::Fp12;
  table line_inputs: (Field,) {}
  table line_outputs: [Field; 51] {}
  map line(index: Field)->[Field;51] = line_inputs => line_outputs;
  fn ell(accumulator: Fp12,point: Point,active: Field,coefficients: [Field;24])->Fp12 {
    match active {
      0 => accumulator,
      1 => {
        let p=BN254G1::coordinates(point);
        match p.2 {
          1 => accumulator,
          0 => {
            let c0=BN254Fp2::from_raw([coefficients[0],coefficients[1],coefficients[2],coefficients[3],coefficients[4],coefficients[5],coefficients[6],coefficients[7]]);
            let c1=BN254Fp2::from_raw([coefficients[8],coefficients[9],coefficients[10],coefficients[11],coefficients[12],coefficients[13],coefficients[14],coefficients[15]]);
            let c2=BN254Fp2::from_raw([coefficients[16],coefficients[17],coefficients[18],coefficients[19],coefficients[20],coefficients[21],coefficients[22],coefficients[23]]);
            BN254Fp12::mul_034(accumulator,BN254Fp2::mul_fp(c0,p.1),BN254Fp2::mul_fp(c1,p.0),c2)
          },
        }
      },
    }
  }
  fn miller_step(index: Field,accumulator: Fp12,a: Point,b: Point)->Fp12 {
    match index {
      87 => accumulator,
      _ => {
        let row=line(index);
        let square=match row[0] {0 => accumulator,1 => BN254Fp12::square(accumulator)};
        let first=ell(square,a,row[1],[row[3],row[4],row[5],row[6],row[7],row[8],row[9],row[10],row[11],row[12],row[13],row[14],row[15],row[16],row[17],row[18],row[19],row[20],row[21],row[22],row[23],row[24],row[25],row[26]]);
        let second=ell(first,b,row[2],[row[27],row[28],row[29],row[30],row[31],row[32],row[33],row[34],row[35],row[36],row[37],row[38],row[39],row[40],row[41],row[42],row[43],row[44],row[45],row[46],row[47],row[48],row[49],row[50]]);
        miller_step(index+1,second,a,b)
      },
    }
  }
  fn miller(a: Point,b: Point)->Fp12 { miller_step(0,BN254Fp12::ONE,a,b) }
  fn check(a: Point,b: Point)->() { BN254Fp12::assert_one(BN254Fp12::final_exponentiation(miller(a,b))) }
  fn check_chunks(chunks:[Field;4])->() {
    let points=BN254G1Encoding::from_chunks(chunks);
    check(points.0,points.1)
  }
}
⟧

/-- The table must be derived from the independently authenticated G2 anchors.
All entries become part of the compiler artifact and its verifying key. -/
def declarations (lines : List (List Nat)) : Except String (Modules.Program Nat) := do
  unless lines.length == 87 && lines.all (·.length == 51) do
    throw "BN254 prepared lines require 87 rows of 51 fields"
  return { implementation with modules := implementation.modules.map fun m =>
      {m with body := match m.body with
        | .definitions d => .definitions {d with program.tables := [
            ⟨"line_inputs", .tuple [.field], (List.range 87).map fun n => .tuple [.literal n]⟩,
            ⟨"line_outputs", .array .field 51, lines.map fun row => .array (row.map fun n => .literal n)⟩]}
        | body => body} }

def signature : Modules.Program Nat := implementation

def program (lines : List (List Nat)) : Except String (Modules.Program BN254.F) := do
  return (dependencies.append (← declarations lines)).toField BN254.F
end Aiur.Library.Field.BN254.Pairing
