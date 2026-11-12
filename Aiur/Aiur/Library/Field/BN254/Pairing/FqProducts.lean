import Aiur.Library.Field.BN254.Fq

/-! Canonical reductions of two base-field products. The added p² keeps the
integer numerator nonnegative for subtraction. Four radix-2^80 quotient limbs
cover its bound below 3p. Biased carries have a separate 86-bit range. -/
namespace Aiur.Library.Field.BN254.Pairing.FqProducts
open Aiur

def radix : Nat := 2^80

theorem coefficient_bound : 128 * radix^2 + 128 * radix < BN254.modulus := by decide
theorem quotient_capacity : 3 * Fq.modulus < radix^4 := by decide
theorem carry_margin : 20 * radix < 32 * radix ∧ 32 * radix + 20 * radix < 64 * radix := by decide

def dependencies : Modules.Program Nat := Fq.dependencies.append Fq.declarations

def declarations : Modules.Program Nat := aiur_library% dependencies ⟦
module BN254FqProducts {
  type Fq = BN254Fq::Fq;
  const RADIX:Field=1208925819614629174706176;
  const BIAS:Field=38685626227668133590597632;
  const CORRECTION:Field=46768052394588893382517875961294828960856250777600;
  fn range86(value:Field)->() {
    let raw=hint::<[Field;6]>("bn254.pairing.u16_86",value);
    let low=BN254Fq::checked_pack80_u16([raw[0],raw[1],raw[2],raw[3],raw[4]]);
    BN254Fq::byte(raw[5]);BN254Fq::byte(4*raw[5]);
    assert_eq!(low+RADIX*raw[5],value,"Fq product carry range");
    ()
  }
  fn reduce(a:Fq,b:Fq,c:Fq,d:Fq,subtract:Field)->Fq {
    assert_eq!(subtract*(subtract-1),0,"Fq product sign");
    let x=BN254Fq::to_limbs(a);let y=BN254Fq::to_limbs(b);
    let z=BN254Fq::to_limbs(c);let w=BN254Fq::to_limbs(d);
    let (raw,quotient,carry)=hint::<([Field;4],[Field;4],[Field;7])>("bn254.pairing.fq_products",(x,y,z,w,subtract));
    let result=BN254Fq::from_limbs(raw);
    BN254Fq::bound(quotient);
    range86(carry[0]);range86(carry[1]);range86(carry[2]);range86(carry[3]);range86(carry[4]);range86(carry[5]);range86(carry[6]);
    assert_eq!((x[0]*y[0]) + (1-2*subtract)*(z[0]*w[0]) + 914936924970060099801990896005996338401951705521 - (quotient[0]*956523353070932659600711) - raw[0] + BIAS + CORRECTION,RADIX*carry[0],"Fq product limb 0");
    assert_eq!((x[0]*y[1] + x[1]*y[0]) + (1-2*subtract)*(z[0]*w[1] + z[1]*w[0]) + 1169964410699283770982789944584053094471401687214 - (quotient[0]*611571273687723030964337 + quotient[1]*956523353070932659600711) - raw[1] + carry[0] + CORRECTION,RADIX*carry[1],"Fq product limb 1");
    assert_eq!((x[0]*y[2] + x[1]*y[1] + x[2]*y[0]) + (1-2*subtract)*(z[0]*w[2] + z[1]*w[1] + z[2]*w[0]) + 1082733863059495263095485766189540767770332784853 - (quotient[0]*370463741415268654532022 + quotient[1]*611571273687723030964337 + quotient[2]*956523353070932659600711) - raw[2] + carry[1] + CORRECTION,RADIX*carry[2],"Fq product limb 2");
    assert_eq!((x[0]*y[3] + x[1]*y[2] + x[2]*y[1] + x[3]*y[0]) + (1-2*subtract)*(z[0]*w[3] + z[1]*w[2] + z[2]*w[1] + z[3]*w[0]) + 453129964384910239618984530931620088318480214564 - (quotient[0]*12388 + quotient[1]*370463741415268654532022 + quotient[2]*611571273687723030964337 + quotient[3]*956523353070932659600711) - raw[3] + carry[2] + CORRECTION,RADIX*carry[3],"Fq product limb 3");
    assert_eq!((x[1]*y[3] + x[2]*y[2] + x[3]*y[1]) + (1-2*subtract)*(z[1]*w[3] + z[2]*w[2] + z[3]*w[1]) + 137243383703399039743539294142326861774995821996 - (quotient[1]*12388 + quotient[2]*370463741415268654532022 + quotient[3]*611571273687723030964337) + carry[3] + CORRECTION,RADIX*carry[4],"Fq product limb 4");
    assert_eq!((x[2]*y[3] + x[3]*y[2]) + (1-2*subtract)*(z[2]*w[3] + z[3]*w[2]) + 9178609657304696184685377072 - (quotient[2]*12388 + quotient[3]*370463741415268654532022) + carry[4] + CORRECTION,RADIX*carry[5],"Fq product limb 5");
    assert_eq!((x[3]*y[3]) + (1-2*subtract)*(z[3]*w[3]) + 153462544 - (quotient[3]*12388) + carry[5] + CORRECTION,RADIX*carry[6],"Fq product limb 6");
    assert_eq!((0) + (1-2*subtract)*(0) + 0 - (0) + carry[6] + CORRECTION,RADIX*BIAS,"Fq product limb 7");
    result
  }
  inline fn sum(a:Fq,b:Fq,c:Fq,d:Fq)->Fq { reduce(a,b,c,d,0) }
  inline fn difference(a:Fq,b:Fq,c:Fq,d:Fq)->Fq { reduce(a,b,c,d,1) }
}
⟧

def program : Modules.Program BN254.F := (dependencies.append declarations).toField BN254.F
end Aiur.Library.Field.BN254.Pairing.FqProducts
