import Aiur.Library.Field.BN254.Fq

/-! Bounded signed quadratic relations over canonical Fq operands. An opaque
expression carries its positive and negative product, linear and constant
weights. Constructors check these budgets before another expression can use
the result. Advice supplies only a biased quotient and three paired carries.
The closed integer inequalities justify lifting the four Fr equations to
integer equations; they are not a source-level correctness proof. -/
namespace Aiur.Library.Field.BN254.FqRelation
open Aiur

def radix : Nat := 2^80
def coefficientBound : Nat := 16 * radix^2 + 3 * radix + 4
def carryBias : Nat := 2^88

theorem quotient_capacity :
    (3 * (Fq.modulus - 1)^2 + 3 * (Fq.modulus - 1) + 4) / Fq.modulus < 2^256 := by decide

theorem centered_coefficient_bound :
    2 * (12 * radix^2 + 3 * radix + 4) < BN254.modulus := by decide

theorem paired_equation_bound :
    (radix + 1) * coefficientBound + (radix^2 + 1) * carryBias < BN254.modulus := by decide

theorem carry_margin :
    (radix + 1) * coefficientBound + carryBias < radix^2 * carryBias := by decide

theorem range_pack_bound : 2^96 < BN254.modulus := by decide

theorem paired_telescope (b bias c0 c1 c2 c3 c4 c5 c6 c7 u v w : Int)
    (h0 : c0 + b*c1 + b^2*bias = b^2*u)
    (h1 : c2 + b*c3 + u - bias + b^2*bias = b^2*v)
    (h2 : c4 + b*c5 + v - bias + b^2*bias = b^2*w)
    (h3 : c6 + b*c7 + w - bias = 0) :
    c0 + b*c1 + b^2*c2 + b^3*c3 + b^4*c4 + b^5*c5 + b^6*c6 + b^7*c7 = 0 := by
  linear_combination h0 + b^2 * h1 + b^4 * h2 + b^6 * h3

def dependencies : Modules.Program Nat := Fq.dependencies.append Fq.declarations

def declarations : Modules.Program Nat := aiur_library% dependencies ⟦
module BN254FqRelation {
  type Fq = BN254Fq::Fq;
  opaque type Expression = ([Field; 8], [Field; 6]);
  const ZERO: Expression = ([0; 8], [0; 6]);
  const RADIX: Field = 1208925819614629174706176;
  const PAIR_RADIX: Field = 1461501637330902918203684832716283019655932542976;
  const CARRY_BIAS: Field = 309485009821345068724781056;
  const PAIR_BIAS: Field = 452312848583266388373324160190187140051835877600158453279131187530910662656;

  table weight_inputs: (Field,) { (0,), (1,), (2,), (3,) }
  table weight_units: () { (), (), (), () }
  map weight(value: Field) -> () = weight_inputs => weight_units;
  table constant_inputs: (Field,) { (0,), (1,), (2,), (3,), (4,) }
  table constant_units: () { (), (), (), (), () }
  map constant_weight(value: Field) -> () = constant_inputs => constant_units;

  inline fn product(a: Fq, b: Fq) -> Expression {
    let x = BN254Fq::to_limbs(a);
    let y = BN254Fq::to_limbs(b);
    ([x[0]*y[0],
      x[0]*y[1] + x[1]*y[0],
      x[0]*y[2] + x[1]*y[1] + x[2]*y[0],
      x[0]*y[3] + x[1]*y[2] + x[2]*y[1] + x[3]*y[0],
      x[1]*y[3] + x[2]*y[2] + x[3]*y[1],
      x[2]*y[3] + x[3]*y[2], x[3]*y[3], 0], [1, 0, 0, 0, 0, 0])
  }

  inline fn linear(a: Fq) -> Expression {
    let x = BN254Fq::to_limbs(a);
    ([x[0], x[1], x[2], x[3], 0, 0, 0, 0], [0, 0, 1, 0, 0, 0])
  }

  inline fn constant(value: Field) -> Expression {
    constant_weight(value);
    ([value, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, value, 0])
  }

  inline fn neg(a: Expression) -> Expression {
    let (x, w) = a;
    ([0-x[0], 0-x[1], 0-x[2], 0-x[3], 0-x[4], 0-x[5], 0-x[6], 0-x[7]],
      [w[1], w[0], w[3], w[2], w[5], w[4]])
  }

  inline fn add(a: Expression, b: Expression) -> Expression {
    let (x, u) = a;
    let (y, v) = b;
    let w = [u[0]+v[0], u[1]+v[1], u[2]+v[2], u[3]+v[3], u[4]+v[4], u[5]+v[5]];
    weight(w[0]); weight(w[1]); weight(w[2]); weight(w[3]);
    constant_weight(w[4]); constant_weight(w[5]);
    ([x[0]+y[0], x[1]+y[1], x[2]+y[2], x[3]+y[3],
      x[4]+y[4], x[5]+y[5], x[6]+y[6], x[7]+y[7]], w)
  }

  inline fn sub(a: Expression, b: Expression) -> Expression { add(a, neg(b)) }
  inline fn twice(a: Expression) -> Expression { add(a, a) }
  inline fn thrice(a: Expression) -> Expression { add(twice(a), a) }

  fn range17(value: Field) -> () {
    let raw = hint::<[Field; 2]>("bn254.fq_relation.u16_17", value);
    BN254Fq::limb16(raw[0]);
    assert_eq!(raw[1] * (raw[1] - 1), 0, "Fq relation quotient top bit");
    assert_eq!(raw[0] + 65536 * raw[1], value, "Fq relation quotient range");
    ()
  }

  fn range89(value: Field) -> () {
    let raw = hint::<[Field; 6]>("bn254.fq_relation.u16_89", value);
    let low = BN254Fq::checked_pack80_u16([raw[0], raw[1], raw[2], raw[3], raw[4]]);
    BN254Fq::limb16(raw[5]); BN254Fq::limb16(128 * raw[5]);
    assert_eq!(low + RADIX * raw[5], value, "Fq relation carry range");
    ()
  }

  fn assert_zero(expression: Expression) -> () {
    let (c, weights) = expression;
    let (q, carry) = hint::<([Field; 4], [Field; 3])>("bn254.fq_relation.zero", c);
    BN254Fq::range80(q[0]); BN254Fq::range80(q[1]); BN254Fq::range80(q[2]); range17(q[3]);
    range89(carry[0]); range89(carry[1]); range89(carry[2]);
    let top = q[3] - 65536;
    let d0 = c[0] - q[0]*956523353070932659600711;
    let d1 = c[1] - q[0]*611571273687723030964337 - q[1]*956523353070932659600711;
    let d2 = c[2] - q[0]*370463741415268654532022 - q[1]*611571273687723030964337 - q[2]*956523353070932659600711;
    let d3 = c[3] - q[0]*12388 - q[1]*370463741415268654532022 - q[2]*611571273687723030964337 - top*956523353070932659600711;
    let d4 = c[4] - q[1]*12388 - q[2]*370463741415268654532022 - top*611571273687723030964337;
    let d5 = c[5] - q[2]*12388 - top*370463741415268654532022;
    let d6 = c[6] - top*12388;
    assert_eq!(d0 + RADIX*d1 + PAIR_BIAS, PAIR_RADIX*carry[0], "Fq relation pair 0");
    assert_eq!(d2 + RADIX*d3 + carry[0] - CARRY_BIAS + PAIR_BIAS, PAIR_RADIX*carry[1], "Fq relation pair 1");
    assert_eq!(d4 + RADIX*d5 + carry[1] - CARRY_BIAS + PAIR_BIAS, PAIR_RADIX*carry[2], "Fq relation pair 2");
    assert_eq!(d6 + RADIX*c[7] + carry[2] - CARRY_BIAS, 0, "Fq relation pair 3");
    ()
  }
}
⟧

def program : Modules.Program BN254.F := (dependencies.append declarations).toField BN254.F

end Aiur.Library.Field.BN254.FqRelation
