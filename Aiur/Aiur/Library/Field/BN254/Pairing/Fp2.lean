import Aiur.Library.Field.BN254.Pairing.FqProducts

/-! The quadratic BN254 tower Fq[u]/(u² + 1), using canonical base-field
components. Every arithmetic result is constrained by the Fq library. -/
namespace Aiur.Library.Field.BN254.Pairing.Fp2
open Aiur

def dependencies : Modules.Program Nat := FqProducts.dependencies.append FqProducts.declarations

def declarations : Modules.Program Nat := aiur_library% dependencies ⟦
module BN254Fp2 {
  type Fq = BN254Fq::Fq;
  opaque type Fp2 = (Fq, Fq);
  const ZERO: Fp2 = (BN254Fq::ZERO, BN254Fq::ZERO);
  const ONE: Fp2 = (BN254Fq::ONE, BN254Fq::ZERO);
  inline fn make(a: Fq, b: Fq) -> Fp2 { (a, b) }
  inline fn coefficients(a: Fp2) -> (Fq, Fq) { a }
  fn from_raw(a: [Field; 8]) -> Fp2 {
    (BN254Fq::from_limbs([a[0],a[1],a[2],a[3]]), BN254Fq::from_limbs([a[4],a[5],a[6],a[7]]))
  }
  inline fn to_raw(a: Fp2) -> [Field; 8] {
    let x = BN254Fq::to_limbs(a.0);
    let y = BN254Fq::to_limbs(a.1);
    [x[0],x[1],x[2],x[3],y[0],y[1],y[2],y[3]]
  }
  fn add(a: Fp2, b: Fp2) -> Fp2 { (BN254Fq::add(a.0,b.0), BN254Fq::add(a.1,b.1)) }
  fn sub(a: Fp2, b: Fp2) -> Fp2 { (BN254Fq::sub(a.0,b.0), BN254Fq::sub(a.1,b.1)) }
  fn neg(a: Fp2) -> Fp2 { (BN254Fq::neg(a.0), BN254Fq::neg(a.1)) }
  fn conjugate(a: Fp2) -> Fp2 { (a.0, BN254Fq::neg(a.1)) }
  fn mul(a: Fp2, b: Fp2) -> Fp2 {
    (BN254FqProducts::difference(a.0,b.0,a.1,b.1),BN254FqProducts::sum(a.0,b.1,a.1,b.0))
  }
  fn square(a: Fp2) -> Fp2 {
    (BN254FqProducts::difference(a.0,a.0,a.1,a.1),BN254FqProducts::sum(a.0,a.1,a.0,a.1))
  }
  fn mul_fp(a: Fp2, b: Fq) -> Fp2 { (BN254Fq::mul(a.0,b), BN254Fq::mul(a.1,b)) }
  fn mul_xi(a: Fp2) -> Fp2 {
    let nine = BN254Fq::from_limbs([9,0,0,0]);
    (BN254FqProducts::difference(a.0,nine,a.1,BN254Fq::ONE),BN254FqProducts::sum(a.1,nine,a.0,BN254Fq::ONE))
  }
  fn inverse(a: Fp2) -> Fp2 {
    let norm = BN254FqProducts::sum(a.0,a.0,a.1,a.1);
    let inverse = BN254Fq::inverse(norm);
    (BN254Fq::mul(a.0,inverse), BN254Fq::neg(BN254Fq::mul(a.1,inverse)))
  }
}
⟧

def program : Modules.Program BN254.F := (dependencies.append declarations).toField BN254.F
end Aiur.Library.Field.BN254.Pairing.Fp2
