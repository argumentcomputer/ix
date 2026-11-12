import Aiur.Library.Field.BN254.Pairing.Fp2

/-! The cubic tower Fq2[v]/(v³ - (9+u)). -/
namespace Aiur.Library.Field.BN254.Pairing.Fp6
open Aiur

def dependencies : Modules.Program Nat := Fp2.dependencies.append Fp2.declarations

def declarations : Modules.Program Nat := aiur_library% dependencies ⟦
module BN254Fp6 {
  type Fp2 = BN254Fp2::Fp2;
  opaque type Fp6 = (Fp2, Fp2, Fp2);
  const ZERO: Fp6 = (BN254Fp2::ZERO, BN254Fp2::ZERO, BN254Fp2::ZERO);
  const ONE: Fp6 = (BN254Fp2::ONE, BN254Fp2::ZERO, BN254Fp2::ZERO);
  inline fn make(a: Fp2, b: Fp2, c: Fp2) -> Fp6 { (a,b,c) }
  inline fn coefficients(a: Fp6) -> (Fp2,Fp2,Fp2) { a }
  fn from_raw(a: [Field; 24]) -> Fp6 {
    (BN254Fp2::from_raw([a[0],a[1],a[2],a[3],a[4],a[5],a[6],a[7]]),
     BN254Fp2::from_raw([a[8],a[9],a[10],a[11],a[12],a[13],a[14],a[15]]),
     BN254Fp2::from_raw([a[16],a[17],a[18],a[19],a[20],a[21],a[22],a[23]]))
  }
  inline fn to_raw(a: Fp6) -> [Field; 24] {
    let x=BN254Fp2::to_raw(a.0); let y=BN254Fp2::to_raw(a.1); let z=BN254Fp2::to_raw(a.2);
    [x[0],x[1],x[2],x[3],x[4],x[5],x[6],x[7],y[0],y[1],y[2],y[3],y[4],y[5],y[6],y[7],z[0],z[1],z[2],z[3],z[4],z[5],z[6],z[7]]
  }
  fn add(a: Fp6,b: Fp6)->Fp6 { (BN254Fp2::add(a.0,b.0),BN254Fp2::add(a.1,b.1),BN254Fp2::add(a.2,b.2)) }
  fn sub(a: Fp6,b: Fp6)->Fp6 { (BN254Fp2::sub(a.0,b.0),BN254Fp2::sub(a.1,b.1),BN254Fp2::sub(a.2,b.2)) }
  fn neg(a: Fp6)->Fp6 { (BN254Fp2::neg(a.0),BN254Fp2::neg(a.1),BN254Fp2::neg(a.2)) }
  fn mul_v(a: Fp6)->Fp6 { (BN254Fp2::mul_xi(a.2),a.0,a.1) }
  fn mul_fp2(a: Fp6,b: Fp2)->Fp6 { (BN254Fp2::mul(a.0,b),BN254Fp2::mul(a.1,b),BN254Fp2::mul(a.2,b)) }
  fn mul(a: Fp6,b: Fp6)->Fp6 {
    let aa=BN254Fp2::mul(a.0,b.0); let bb=BN254Fp2::mul(a.1,b.1); let cc=BN254Fp2::mul(a.2,b.2);
    let cross12=BN254Fp2::sub(BN254Fp2::sub(BN254Fp2::mul(BN254Fp2::add(a.1,a.2),BN254Fp2::add(b.1,b.2)),bb),cc);
    let cross01=BN254Fp2::sub(BN254Fp2::sub(BN254Fp2::mul(BN254Fp2::add(a.0,a.1),BN254Fp2::add(b.0,b.1)),aa),bb);
    let cross02=BN254Fp2::sub(BN254Fp2::sub(BN254Fp2::mul(BN254Fp2::add(a.0,a.2),BN254Fp2::add(b.0,b.2)),aa),cc);
    (BN254Fp2::add(aa,BN254Fp2::mul_xi(cross12)),BN254Fp2::add(cross01,BN254Fp2::mul_xi(cc)),BN254Fp2::add(cross02,bb))
  }
  fn square(a: Fp6)->Fp6 {
    let s0=BN254Fp2::square(a.0);
    let t1=BN254Fp2::mul(a.0,a.1); let s1=BN254Fp2::add(t1,t1);
    let s2=BN254Fp2::square(BN254Fp2::add(BN254Fp2::sub(a.0,a.1),a.2));
    let t3=BN254Fp2::mul(a.1,a.2); let s3=BN254Fp2::add(t3,t3);
    let s4=BN254Fp2::square(a.2);
    (BN254Fp2::add(s0,BN254Fp2::mul_xi(s3)),BN254Fp2::add(s1,BN254Fp2::mul_xi(s4)),
     BN254Fp2::sub(BN254Fp2::sub(BN254Fp2::add(BN254Fp2::add(s1,s2),s3),s0),s4))
  }
  fn mul_01(a: Fp6,c0: Fp2,c1: Fp2)->Fp6 {
    let aa=BN254Fp2::mul(a.0,c0); let bb=BN254Fp2::mul(a.1,c1);
    let t0=BN254Fp2::add(aa,BN254Fp2::mul_xi(BN254Fp2::sub(BN254Fp2::mul(c1,BN254Fp2::add(a.1,a.2)),bb)));
    let t1=BN254Fp2::sub(BN254Fp2::sub(BN254Fp2::mul(BN254Fp2::add(c0,c1),BN254Fp2::add(a.0,a.1)),aa),bb);
    let t2=BN254Fp2::add(BN254Fp2::sub(BN254Fp2::mul(c0,BN254Fp2::add(a.0,a.2)),aa),bb);
    (t0,t1,t2)
  }
  fn inverse(a: Fp6)->Fp6 {
    let c0=BN254Fp2::sub(BN254Fp2::square(a.0),BN254Fp2::mul_xi(BN254Fp2::mul(a.1,a.2)));
    let c1=BN254Fp2::sub(BN254Fp2::mul_xi(BN254Fp2::square(a.2)),BN254Fp2::mul(a.0,a.1));
    let c2=BN254Fp2::sub(BN254Fp2::square(a.1),BN254Fp2::mul(a.0,a.2));
    let norm=BN254Fp2::add(BN254Fp2::mul(a.0,c0),BN254Fp2::mul_xi(BN254Fp2::add(BN254Fp2::mul(a.2,c1),BN254Fp2::mul(a.1,c2))));
    let inverse=BN254Fp2::inverse(norm);
    (BN254Fp2::mul(c0,inverse),BN254Fp2::mul(c1,inverse),BN254Fp2::mul(c2,inverse))
  }
  fn frobenius1(a: Fp6)->Fp6 {
    let c1=BN254Fp2::from_raw([241073140426145224676669,1158634321780406576267971,338097652011103670758460,12211,745213181020077862931362,1016969546900786011507580,1082904720027740455357579,5833]);
    let c2=BN254Fp2::from_raw([1116590969262051336038242,425457904430772869643924,374808219024803331555511,1461,941591081555171371352358,278824595442047931522014,447959003012038389301424,11284]);
    (BN254Fp2::conjugate(a.0),BN254Fp2::mul(BN254Fp2::conjugate(a.1),c1),BN254Fp2::mul(BN254Fp2::conjugate(a.2),c2))
  }
  fn frobenius2(a: Fp6)->Fp6 {
    let c1=BN254Fp2::from_raw([520602046910120459042120,1060997681646177756363670,370463741415267146521063,12388,0,0,0,0]);
    let c2=BN254Fp2::from_raw([435921306160812200558590,759499411656174449306843,1508010958,0,0,0,0,0]);
    (a.0,BN254Fp2::mul(a.1,c1),BN254Fp2::mul(a.2,c2))
  }
  fn frobenius3(a: Fp6)->Fp6 {
    let c1=BN254Fp2::from_raw([315577346726058052615021,706568352941122112019817,1060036912179557001272439,2134,180357855599828165560030,1115180137004358021650687,1049577354829677244649069,1265]);
    let c2=BN254Fp2::from_raw([509038919000018173816934,858036775969075719665072,663014154675328888266999,3013,712586186450840081671071,60544305026682141045631,1103149996135511751718639,9173]);
    (BN254Fp2::conjugate(a.0),BN254Fp2::mul(BN254Fp2::conjugate(a.1),c1),BN254Fp2::mul(BN254Fp2::conjugate(a.2),c2))
  }
}
⟧

def program : Modules.Program BN254.F := (dependencies.append declarations).toField BN254.F
end Aiur.Library.Field.BN254.Pairing.Fp6
