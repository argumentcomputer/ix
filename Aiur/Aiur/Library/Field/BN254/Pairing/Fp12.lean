import Aiur.Library.Field.BN254.Pairing.Fp6

/-! Fq12 = Fq6[w]/(w²-v), including sparse Miller-line multiplication and
cyclotomic squaring. Cyclotomic operations require the easy final-exponentiation
part's output; conjugation is an inverse only in that subgroup. -/
namespace Aiur.Library.Field.BN254.Pairing.Fp12
open Aiur

def dependencies : Modules.Program Nat := Fp6.dependencies.append Fp6.declarations

/-- The hard exponent chain differs from the normalized final exponent by
this invertible scalar on the prime-order target group. -/
def finalScale : Nat := 2 * 4965661367192848881 * (6 * 4965661367192848881^2 + 3 * 4965661367192848881 + 1)

theorem finalScale_coprime_order : Nat.Coprime finalScale BN254.modulus := by decide

private def implementation : Modules.Program Nat := aiur_library% dependencies ⟦
module BN254Fp12 {
  type Fp2 = BN254Fp2::Fp2;
  type Fp6 = BN254Fp6::Fp6;
  opaque type Fp12 = (Fp6,Fp6);
  const ZERO: Fp12 = (BN254Fp6::ZERO,BN254Fp6::ZERO);
  const ONE: Fp12 = (BN254Fp6::ONE,BN254Fp6::ZERO);
  table x_inputs: (Field,) {}
  table x_outputs: Field {}
  map x_bit(index: Field)->Field = x_inputs => x_outputs;
  inline fn make(a: Fp6,b: Fp6)->Fp12 { (a,b) }
  inline fn coefficients(a: Fp12)->(Fp6,Fp6) { a }
  fn from_raw(a: [Field; 48])->Fp12 { (BN254Fp6::from_raw([a[0],a[1],a[2],a[3],a[4],a[5],a[6],a[7],a[8],a[9],a[10],a[11],a[12],a[13],a[14],a[15],a[16],a[17],a[18],a[19],a[20],a[21],a[22],a[23]]),BN254Fp6::from_raw([a[24],a[25],a[26],a[27],a[28],a[29],a[30],a[31],a[32],a[33],a[34],a[35],a[36],a[37],a[38],a[39],a[40],a[41],a[42],a[43],a[44],a[45],a[46],a[47]])) }
  inline fn to_raw(a: Fp12)->[Field; 48] { let x=BN254Fp6::to_raw(a.0); let y=BN254Fp6::to_raw(a.1); [x[0],x[1],x[2],x[3],x[4],x[5],x[6],x[7],x[8],x[9],x[10],x[11],x[12],x[13],x[14],x[15],x[16],x[17],x[18],x[19],x[20],x[21],x[22],x[23],y[0],y[1],y[2],y[3],y[4],y[5],y[6],y[7],y[8],y[9],y[10],y[11],y[12],y[13],y[14],y[15],y[16],y[17],y[18],y[19],y[20],y[21],y[22],y[23]] }
  fn add(a: Fp12,b: Fp12)->Fp12 { (BN254Fp6::add(a.0,b.0),BN254Fp6::add(a.1,b.1)) }
  fn sub(a: Fp12,b: Fp12)->Fp12 { (BN254Fp6::sub(a.0,b.0),BN254Fp6::sub(a.1,b.1)) }
  fn conjugate(a: Fp12)->Fp12 { (a.0,BN254Fp6::neg(a.1)) }
  fn mul(a: Fp12,b: Fp12)->Fp12 {
    let aa=BN254Fp6::mul(a.0,b.0); let bb=BN254Fp6::mul(a.1,b.1);
    let cross=BN254Fp6::mul(BN254Fp6::add(a.0,a.1),BN254Fp6::add(b.0,b.1));
    (BN254Fp6::add(aa,BN254Fp6::mul_v(bb)),BN254Fp6::sub(BN254Fp6::sub(cross,aa),bb))
  }
  fn square(a: Fp12)->Fp12 {
    let ab=BN254Fp6::mul(a.0,a.1);
    let sum=BN254Fp6::mul(BN254Fp6::add(a.0,a.1),BN254Fp6::add(a.0,BN254Fp6::mul_v(a.1)));
    (BN254Fp6::sub(BN254Fp6::sub(sum,ab),BN254Fp6::mul_v(ab)),BN254Fp6::add(ab,ab))
  }
  fn inverse(a: Fp12)->Fp12 {
    let norm=BN254Fp6::sub(BN254Fp6::square(a.0),BN254Fp6::mul_v(BN254Fp6::square(a.1)));
    let inverse=BN254Fp6::inverse(norm);
    (BN254Fp6::mul(a.0,inverse),BN254Fp6::neg(BN254Fp6::mul(a.1,inverse)))
  }
  fn mul_034(a: Fp12,c0: Fp2,c3: Fp2,c4: Fp2)->Fp12 {
    let aa=BN254Fp6::mul_fp2(a.0,c0);
    let bb=BN254Fp6::mul_01(a.1,c3,c4);
    let cross=BN254Fp6::mul_01(BN254Fp6::add(a.0,a.1),BN254Fp2::add(c0,c3),c4);
    (BN254Fp6::add(aa,BN254Fp6::mul_v(bb)),BN254Fp6::sub(BN254Fp6::sub(cross,aa),bb))
  }
  fn cyclotomic_pair(a: Fp2,b: Fp2)->(Fp2,Fp2) {
    let product=BN254Fp2::mul(a,b);
    let square=BN254Fp2::sub(BN254Fp2::sub(BN254Fp2::mul(BN254Fp2::add(a,b),BN254Fp2::add(a,BN254Fp2::mul_xi(b))),product),BN254Fp2::mul_xi(product));
    (square,BN254Fp2::add(product,product))
  }
  fn adjust_minus(t: Fp2,z: Fp2)->Fp2 { let d=BN254Fp2::sub(t,z); BN254Fp2::add(BN254Fp2::add(d,d),t) }
  fn adjust_plus(t: Fp2,z: Fp2)->Fp2 { let d=BN254Fp2::add(t,z); BN254Fp2::add(BN254Fp2::add(d,d),t) }
  fn cyclotomic_square(a: Fp12)->Fp12 {
    let x=BN254Fp6::coefficients(a.0); let y=BN254Fp6::coefficients(a.1);
    let t01=cyclotomic_pair(x.0,y.1);
    let t23=cyclotomic_pair(y.0,x.2);
    let t45=cyclotomic_pair(x.1,y.2);
    (BN254Fp6::make(adjust_minus(t01.0,x.0),adjust_minus(t23.0,x.1),adjust_minus(t45.0,x.2)),
     BN254Fp6::make(adjust_plus(BN254Fp2::mul_xi(t45.1),y.0),adjust_plus(t01.1,y.1),adjust_plus(t23.1,y.2)))
  }
  fn frobenius1(a: Fp12)->Fp12 {
    let coefficient=BN254Fp2::from_raw([158030233215959002899568,561492039244248129218863,864712486116523230470109,4740,943989816277925379662508,85390811048248121724654,712850572231007024610558,9321]);
    (BN254Fp6::frobenius1(a.0),BN254Fp6::mul_fp2(BN254Fp6::frobenius1(a.1),coefficient))
  }
  fn frobenius2(a: Fp12)->Fp12 {
    let coefficient=BN254Fp2::from_raw([520602046910120459042121,1060997681646177756363670,370463741415267146521063,12388,0,0,0,0]);
    (BN254Fp6::frobenius2(a.0),BN254Fp6::mul_fp2(BN254Fp6::frobenius2(a.1),coefficient))
  }
  fn frobenius3(a: Fp12)->Fp12 {
    let coefficient=BN254Fp2::from_raw([993078769207303499720319,985437358891909864341077,613018488905868654502028,6620,273536865766464026624257,252463552818300632405972,1174505052965274177498851,171]);
    (BN254Fp6::frobenius3(a.0),BN254Fp6::mul_fp2(BN254Fp6::frobenius3(a.1),coefficient))
  }
  fn easy_final(a: Fp12)->Fp12 {
    let first=mul(conjugate(a),inverse(a));
    mul(frobenius2(first),first)
  }
  fn exp_x_loop(a: Fp12,index: Field,accumulator: Fp12)->Fp12 {
    match index {
      63 => accumulator,
      _ => {
        let square=cyclotomic_square(accumulator);
        let next=match x_bit(index) { 0 => square, 1 => mul(square,a) };
        exp_x_loop(a,index+1,next)
      },
    }
  }
  fn exp_neg_x(a: Fp12)->Fp12 { conjugate(exp_x_loop(a,1,a)) }
  fn hard_final(r: Fp12)->Fp12 {
    let y0=exp_neg_x(r);
    let y1=cyclotomic_square(y0);
    let y2=cyclotomic_square(y1);
    let y3=mul(y2,y1);
    let y4=exp_neg_x(y3);
    let y5=cyclotomic_square(y4);
    let y6=conjugate(exp_neg_x(y5));
    let y7=mul(y6,y4);
    let y8=mul(y7,conjugate(y3));
    let y9=mul(y8,y1);
    let y10=mul(y8,y4);
    let y11=mul(y10,r);
    let y12=frobenius1(y9);
    let y13=mul(y12,y11);
    let y14=mul(frobenius2(y8),y13);
    let y15=frobenius3(mul(conjugate(r),y9));
    mul(y15,y14)
  }
  fn final_exponentiation(a: Fp12)->Fp12 { hard_final(easy_final(a)) }
  fn assert_one(a: Fp12)->() {
    let raw=to_raw(a);
    assert_eq!(raw[0],1,"Fp12 identity");
    assert_eq!(raw[1],0,"Fp12 identity");
    assert_eq!(raw[2],0,"Fp12 identity");
    assert_eq!(raw[3],0,"Fp12 identity");
    assert_eq!(raw[4],0,"Fp12 identity");
    assert_eq!(raw[5],0,"Fp12 identity");
    assert_eq!(raw[6],0,"Fp12 identity");
    assert_eq!(raw[7],0,"Fp12 identity");
    assert_eq!(raw[8],0,"Fp12 identity");
    assert_eq!(raw[9],0,"Fp12 identity");
    assert_eq!(raw[10],0,"Fp12 identity");
    assert_eq!(raw[11],0,"Fp12 identity");
    assert_eq!(raw[12],0,"Fp12 identity");
    assert_eq!(raw[13],0,"Fp12 identity");
    assert_eq!(raw[14],0,"Fp12 identity");
    assert_eq!(raw[15],0,"Fp12 identity");
    assert_eq!(raw[16],0,"Fp12 identity");
    assert_eq!(raw[17],0,"Fp12 identity");
    assert_eq!(raw[18],0,"Fp12 identity");
    assert_eq!(raw[19],0,"Fp12 identity");
    assert_eq!(raw[20],0,"Fp12 identity");
    assert_eq!(raw[21],0,"Fp12 identity");
    assert_eq!(raw[22],0,"Fp12 identity");
    assert_eq!(raw[23],0,"Fp12 identity");
    assert_eq!(raw[24],0,"Fp12 identity");
    assert_eq!(raw[25],0,"Fp12 identity");
    assert_eq!(raw[26],0,"Fp12 identity");
    assert_eq!(raw[27],0,"Fp12 identity");
    assert_eq!(raw[28],0,"Fp12 identity");
    assert_eq!(raw[29],0,"Fp12 identity");
    assert_eq!(raw[30],0,"Fp12 identity");
    assert_eq!(raw[31],0,"Fp12 identity");
    assert_eq!(raw[32],0,"Fp12 identity");
    assert_eq!(raw[33],0,"Fp12 identity");
    assert_eq!(raw[34],0,"Fp12 identity");
    assert_eq!(raw[35],0,"Fp12 identity");
    assert_eq!(raw[36],0,"Fp12 identity");
    assert_eq!(raw[37],0,"Fp12 identity");
    assert_eq!(raw[38],0,"Fp12 identity");
    assert_eq!(raw[39],0,"Fp12 identity");
    assert_eq!(raw[40],0,"Fp12 identity");
    assert_eq!(raw[41],0,"Fp12 identity");
    assert_eq!(raw[42],0,"Fp12 identity");
    assert_eq!(raw[43],0,"Fp12 identity");
    assert_eq!(raw[44],0,"Fp12 identity");
    assert_eq!(raw[45],0,"Fp12 identity");
    assert_eq!(raw[46],0,"Fp12 identity");
    assert_eq!(raw[47],0,"Fp12 identity");
    ()
  }
}
⟧

/-- The positive BN254 parameter x=4965661367192848881, most significant bit first. -/
def xBits : List Nat := [1,0,0,0,1,0,0,1,1,1,0,1,0,0,1,1,0,0,1,0,0,1,0,1,0,1,1,0,1,0,0,0,1,0,0,1,0,1,0,0,1,1,0,1,0,0,1,0,0,0,0,1,0,0,1,1,1,1,1,0,0,0,1]

def declarations : Modules.Program Nat :=
  { implementation with modules := implementation.modules.map fun m =>
      {m with body := match m.body with
        | .definitions d => .definitions {d with program.tables := [
            ⟨"x_inputs", .tuple [.field], (List.range 63).map fun n => .tuple [.literal n]⟩,
            ⟨"x_outputs", .field, xBits.map fun n => .literal n⟩]}
        | body => body} }

def program : Modules.Program BN254.F := (dependencies.append declarations).toField BN254.F
end Aiur.Library.Field.BN254.Pairing.Fp12
