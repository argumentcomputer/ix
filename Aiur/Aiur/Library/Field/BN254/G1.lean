import Aiur.Library.Field.BN254.Fq
import Aiur.Library.List

/-! Complete affine BN254 G1 operations over canonical Fq coordinates.
G1 has cofactor one, so the curve equation establishes subgroup membership.
Infinity has the unique internal encoding `(0, 0, 1)`. Scalars are decomposed
canonically below Fr before binary multiplication; the radix recurrences have
fixed lengths and a zero endpoint. Compressed points use arkworks SWFlags,
with a lexicographic y sign rather than a parity bit. -/
namespace Aiur.Library.Field.BN254.G1
open Aiur

theorem scalar_limb_bound : 2^80 < BN254.modulus := by decide
theorem scalar_width_bound : BN254.modulus < 2^254 := by decide

def dependencies : Modules.Program Nat :=
  Fq.dependencies.append Fq.declarations |>.append Library.List.declarations

def declarations : Modules.Program Nat := aiur_library% dependencies ⟦
module BN254G1 {
  type Fq = BN254Fq::Fq;
  opaque type Point = (Fq, Fq, Field);
  const INFINITY: Point = (BN254Fq::ZERO, BN254Fq::ZERO, 1);

  inline fn fq_equal(a: Fq, b: Fq) -> Field {
    let x = BN254Fq::to_limbs(a);
    let y = BN254Fq::to_limbs(b);
    Fields::is_zero(x[0] - y[0]) * Fields::is_zero(x[1] - y[1])
      * Fields::is_zero(x[2] - y[2]) * Fields::is_zero(x[3] - y[3])
  }

  fn from_raw(raw: [Field; 9]) -> Point {
    let x = BN254Fq::from_limbs([raw[0], raw[1], raw[2], raw[3]]);
    let y = BN254Fq::from_limbs([raw[4], raw[5], raw[6], raw[7]]);
    match raw[8] {
      1 => {
        assert_eq!(BN254Fq::is_zero(x), 1, "G1 infinity x");
        assert_eq!(BN254Fq::is_zero(y), 1, "G1 infinity y");
        INFINITY
      },
      0 => {
        let xx = BN254Fq::mul(x, x);
        let xxx = BN254Fq::mul(xx, x);
        let rhs = BN254Fq::add(xxx, BN254Fq::from_limbs([3, 0, 0, 0]));
        assert_eq!(fq_equal(BN254Fq::mul(y, y), rhs), 1, "G1 curve equation");
        (x, y, 0)
      },
    }
  }

  inline fn to_raw(point: Point) -> [Field; 9] {
    let x = BN254Fq::to_limbs(point.0);
    let y = BN254Fq::to_limbs(point.1);
    [x[0], x[1], x[2], x[3], y[0], y[1], y[2], y[3], point.2]
  }

  inline fn coordinates(point: Point) -> (Fq, Fq, Field) { point }

  inline fn neg(point: Point) -> Point { (point.0, BN254Fq::neg(point.1), point.2) }

  fn double(point: Point) -> Point {
    match point.2 {
      1 => INFINITY,
      0 => match BN254Fq::is_zero(point.1) {
        1 => INFINITY,
        0 => {
          let xx = BN254Fq::mul(point.0, point.0);
          let numerator = BN254Fq::add(BN254Fq::add(xx, xx), xx);
          let denominator = BN254Fq::add(point.1, point.1);
          let slope = BN254Fq::div(numerator, denominator);
          let x = BN254Fq::sub(BN254Fq::mul(slope, slope), BN254Fq::add(point.0, point.0));
          let y = BN254Fq::sub(BN254Fq::mul(slope, BN254Fq::sub(point.0, x)), point.1);
          (x, y, 0)
        },
      },
    }
  }

  fn add(a: Point, b: Point) -> Point {
    match a.2 {
      1 => b,
      0 => match b.2 {
        1 => a,
        0 => match fq_equal(a.0, b.0) {
          1 => match fq_equal(a.1, b.1) {
            1 => double(a),
            0 => {
              assert_eq!(BN254Fq::is_zero(BN254Fq::add(a.1, b.1)), 1, "G1 opposite points");
              INFINITY
            },
          },
          0 => {
            let slope = BN254Fq::div(BN254Fq::sub(b.1, a.1), BN254Fq::sub(b.0, a.0));
            let x = BN254Fq::sub(BN254Fq::sub(BN254Fq::mul(slope, slope), a.0), b.0);
            let y = BN254Fq::sub(BN254Fq::mul(slope, BN254Fq::sub(a.0, x)), a.1);
            (x, y, 0)
          },
        },
      },
    }
  }

  fn scalar_limbs(value: Field) -> [Field; 4] {
    let (raw, difference, borrow) = hint::<([Field; 4], [Field; 4], [Field; 4])>("bn254.g1.scalar", value);
    BN254Fq::bound(raw);
    BN254Fq::bound(difference);
    assert_eq!(borrow[0] * (borrow[0] - 1), 0, "Fr canonical borrow");
    assert_eq!(531584715432774185517056 - raw[0] - 0 + 1208925819614629174706176 * borrow[0], difference[0], "Fr canonical subtraction");
    assert_eq!(borrow[1] * (borrow[1] - 1), 0, "Fr canonical borrow");
    assert_eq!(611571273565344341981625 - raw[1] - borrow[0] + 1208925819614629174706176 * borrow[1], difference[1], "Fr canonical subtraction");
    assert_eq!(borrow[2] * (borrow[2] - 1), 0, "Fr canonical borrow");
    assert_eq!(370463741415268654532022 - raw[2] - borrow[1] + 1208925819614629174706176 * borrow[2], difference[2], "Fr canonical subtraction");
    assert_eq!(borrow[3] * (borrow[3] - 1), 0, "Fr canonical borrow");
    assert_eq!(12388 - raw[3] - borrow[2] + 1208925819614629174706176 * borrow[3], difference[3], "Fr canonical subtraction");
    assert_eq!(borrow[3], 0, "noncanonical Fr decomposition");
    assert_eq!(1 * raw[0] + 1208925819614629174706176 * raw[1] + 1461501637330902918203684832716283019655932542976 * raw[2] + 1766847064778384329583297500742918515827483896875618958121606201292619776 * raw[3], value, "Fr scalar recomposition");
    raw
  }

  fn mul_limb(point: Point, limb: Field, count: Field, accumulator: Point) -> Point {
    match count {
      0 => { assert_eq!(limb, 0, "G1 scalar bit endpoint"); accumulator },
      _ => {
        let (quotient, bit) = hint::<(Field, Field)>("bn254.g1.halve", limb);
        assert_eq!(bit * (bit - 1), 0, "G1 scalar bit");
        assert_eq!(2 * quotient + bit, limb, "G1 scalar bit recurrence");
        let previous = mul_limb(point, quotient, count - 1, accumulator);
        let doubled = double(previous);
        match bit { 0 => doubled, 1 => add(doubled, point) }
      },
    }
  }

  fn mul(point: Point, scalar: Field) -> Point {
    let limbs = scalar_limbs(scalar);
    let a = mul_limb(point, limbs[3], 14, INFINITY);
    let b = mul_limb(point, limbs[2], 80, a);
    let c = mul_limb(point, limbs[1], 80, b);
    mul_limb(point, limbs[0], 80, c)
  }

  fn msm(terms: Lists::List<(Point, Field)>) -> Point {
    match *terms {
      Lists::Node::Nil => INFINITY,
      Lists::Node::Cons((point, scalar), rest) => add(mul(point, scalar), msm(rest)),
    }
  }

  fn fq_bytes(value: Fq) -> [Field; 32] {
    let limbs = BN254Fq::to_limbs(value);
    let b0 = hint::<[Field; 10]>("bn254.fq.bytes80", limbs[0]);
    assert_eq!(BN254Fq::checked_pack80(b0), limbs[0], "G1 coordinate bytes");
    let b1 = hint::<[Field; 10]>("bn254.fq.bytes80", limbs[1]);
    assert_eq!(BN254Fq::checked_pack80(b1), limbs[1], "G1 coordinate bytes");
    let b2 = hint::<[Field; 10]>("bn254.fq.bytes80", limbs[2]);
    assert_eq!(BN254Fq::checked_pack80(b2), limbs[2], "G1 coordinate bytes");
    let b3 = hint::<[Field; 10]>("bn254.fq.bytes80", limbs[3]);
    assert_eq!(BN254Fq::checked_pack80(b3), limbs[3], "G1 coordinate bytes");
    assert_eq!(b3[2], 0, "G1 unused coordinate byte");
    assert_eq!(b3[3], 0, "G1 unused coordinate byte");
    assert_eq!(b3[4], 0, "G1 unused coordinate byte");
    assert_eq!(b3[5], 0, "G1 unused coordinate byte");
    assert_eq!(b3[6], 0, "G1 unused coordinate byte");
    assert_eq!(b3[7], 0, "G1 unused coordinate byte");
    assert_eq!(b3[8], 0, "G1 unused coordinate byte");
    assert_eq!(b3[9], 0, "G1 unused coordinate byte");
    [b0[0], b0[1], b0[2], b0[3], b0[4], b0[5], b0[6], b0[7], b0[8], b0[9], b1[0], b1[1], b1[2], b1[3], b1[4], b1[5], b1[6], b1[7], b1[8], b1[9], b2[0], b2[1], b2[2], b2[3], b2[4], b2[5], b2[6], b2[7], b2[8], b2[9], b3[0], b3[1]]
  }

  fn sign(value: Fq) -> Field {
    let raw = BN254Fq::to_limbs(value);
    let (difference, borrow) = hint::<([Field; 4], [Field; 4])>("bn254.g1.sign", raw);
    BN254Fq::bound(difference);
    assert_eq!(borrow[0] * (borrow[0] - 1), 0, "G1 sign borrow");
    assert_eq!(1082724586342780917153443 - raw[0] - 0 + 1208925819614629174706176 * borrow[0], difference[0], "G1 sign subtraction");
    assert_eq!(borrow[1] * (borrow[1] - 1), 0, "G1 sign borrow");
    assert_eq!(305785636843861515482168 - raw[1] - borrow[0] + 1208925819614629174706176 * borrow[1], difference[1], "G1 sign subtraction");
    assert_eq!(borrow[2] * (borrow[2] - 1), 0, "G1 sign borrow");
    assert_eq!(185231870707634327266011 - raw[2] - borrow[1] + 1208925819614629174706176 * borrow[2], difference[2], "G1 sign subtraction");
    assert_eq!(borrow[3] * (borrow[3] - 1), 0, "G1 sign borrow");
    assert_eq!(6194 - raw[3] - borrow[2] + 1208925819614629174706176 * borrow[3], difference[3], "G1 sign subtraction");
    borrow[3]
  }

  fn to_bytes(point: Point) -> [Field; 32] {
    let x = fq_bytes(point.0);
    let last = x[31] + 64 * point.2 + 128 * sign(point.1);
    BN254Fq::byte(last);
    [x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7], x[8], x[9], x[10], x[11], x[12], x[13], x[14], x[15], x[16], x[17], x[18], x[19], x[20], x[21], x[22], x[23], x[24], x[25], x[26], x[27], x[28], x[29], x[30], last]
  }

  fn from_bytes(raw: [Field; 32]) -> Point {
    BN254Fq::byte(raw[0]);
    BN254Fq::byte(raw[1]);
    BN254Fq::byte(raw[2]);
    BN254Fq::byte(raw[3]);
    BN254Fq::byte(raw[4]);
    BN254Fq::byte(raw[5]);
    BN254Fq::byte(raw[6]);
    BN254Fq::byte(raw[7]);
    BN254Fq::byte(raw[8]);
    BN254Fq::byte(raw[9]);
    BN254Fq::byte(raw[10]);
    BN254Fq::byte(raw[11]);
    BN254Fq::byte(raw[12]);
    BN254Fq::byte(raw[13]);
    BN254Fq::byte(raw[14]);
    BN254Fq::byte(raw[15]);
    BN254Fq::byte(raw[16]);
    BN254Fq::byte(raw[17]);
    BN254Fq::byte(raw[18]);
    BN254Fq::byte(raw[19]);
    BN254Fq::byte(raw[20]);
    BN254Fq::byte(raw[21]);
    BN254Fq::byte(raw[22]);
    BN254Fq::byte(raw[23]);
    BN254Fq::byte(raw[24]);
    BN254Fq::byte(raw[25]);
    BN254Fq::byte(raw[26]);
    BN254Fq::byte(raw[27]);
    BN254Fq::byte(raw[28]);
    BN254Fq::byte(raw[29]);
    BN254Fq::byte(raw[30]);
    BN254Fq::byte(raw[31]);
    let point = from_raw(hint::<[Field; 9]>("bn254.g1.decode", raw));
    let canonical = to_bytes(point);
    assert_eq!(canonical[0], raw[0], "noncanonical G1 bytes");
    assert_eq!(canonical[1], raw[1], "noncanonical G1 bytes");
    assert_eq!(canonical[2], raw[2], "noncanonical G1 bytes");
    assert_eq!(canonical[3], raw[3], "noncanonical G1 bytes");
    assert_eq!(canonical[4], raw[4], "noncanonical G1 bytes");
    assert_eq!(canonical[5], raw[5], "noncanonical G1 bytes");
    assert_eq!(canonical[6], raw[6], "noncanonical G1 bytes");
    assert_eq!(canonical[7], raw[7], "noncanonical G1 bytes");
    assert_eq!(canonical[8], raw[8], "noncanonical G1 bytes");
    assert_eq!(canonical[9], raw[9], "noncanonical G1 bytes");
    assert_eq!(canonical[10], raw[10], "noncanonical G1 bytes");
    assert_eq!(canonical[11], raw[11], "noncanonical G1 bytes");
    assert_eq!(canonical[12], raw[12], "noncanonical G1 bytes");
    assert_eq!(canonical[13], raw[13], "noncanonical G1 bytes");
    assert_eq!(canonical[14], raw[14], "noncanonical G1 bytes");
    assert_eq!(canonical[15], raw[15], "noncanonical G1 bytes");
    assert_eq!(canonical[16], raw[16], "noncanonical G1 bytes");
    assert_eq!(canonical[17], raw[17], "noncanonical G1 bytes");
    assert_eq!(canonical[18], raw[18], "noncanonical G1 bytes");
    assert_eq!(canonical[19], raw[19], "noncanonical G1 bytes");
    assert_eq!(canonical[20], raw[20], "noncanonical G1 bytes");
    assert_eq!(canonical[21], raw[21], "noncanonical G1 bytes");
    assert_eq!(canonical[22], raw[22], "noncanonical G1 bytes");
    assert_eq!(canonical[23], raw[23], "noncanonical G1 bytes");
    assert_eq!(canonical[24], raw[24], "noncanonical G1 bytes");
    assert_eq!(canonical[25], raw[25], "noncanonical G1 bytes");
    assert_eq!(canonical[26], raw[26], "noncanonical G1 bytes");
    assert_eq!(canonical[27], raw[27], "noncanonical G1 bytes");
    assert_eq!(canonical[28], raw[28], "noncanonical G1 bytes");
    assert_eq!(canonical[29], raw[29], "noncanonical G1 bytes");
    assert_eq!(canonical[30], raw[30], "noncanonical G1 bytes");
    assert_eq!(canonical[31], raw[31], "noncanonical G1 bytes");
    point
  }

  fn bytes64(value: Field) -> [Field; 8] {
    let raw = hint::<[Field; 8]>("bn254.g1.bytes64", value);
    BN254Fq::byte(raw[0]);
    BN254Fq::byte(raw[1]);
    BN254Fq::byte(raw[2]);
    BN254Fq::byte(raw[3]);
    BN254Fq::byte(raw[4]);
    BN254Fq::byte(raw[5]);
    BN254Fq::byte(raw[6]);
    BN254Fq::byte(raw[7]);
    assert_eq!(1 * raw[0] + 256 * raw[1] + 65536 * raw[2] + 16777216 * raw[3] + 4294967296 * raw[4] + 1099511627776 * raw[5] + 281474976710656 * raw[6] + 72057594037927936 * raw[7], value, "commitment length bytes");
    raw
  }

  inline fn prepend8(raw: [Field; 8], tail: Lists::List<Field>) -> Lists::List<Field> {
    let tail = &(Lists::Node::Cons(raw[7], tail));
    let tail = &(Lists::Node::Cons(raw[6], tail));
    let tail = &(Lists::Node::Cons(raw[5], tail));
    let tail = &(Lists::Node::Cons(raw[4], tail));
    let tail = &(Lists::Node::Cons(raw[3], tail));
    let tail = &(Lists::Node::Cons(raw[2], tail));
    let tail = &(Lists::Node::Cons(raw[1], tail));
    let tail = &(Lists::Node::Cons(raw[0], tail));
    tail
  }

  inline fn prepend32(raw: [Field; 32], tail: Lists::List<Field>) -> Lists::List<Field> {
    let tail = &(Lists::Node::Cons(raw[31], tail));
    let tail = &(Lists::Node::Cons(raw[30], tail));
    let tail = &(Lists::Node::Cons(raw[29], tail));
    let tail = &(Lists::Node::Cons(raw[28], tail));
    let tail = &(Lists::Node::Cons(raw[27], tail));
    let tail = &(Lists::Node::Cons(raw[26], tail));
    let tail = &(Lists::Node::Cons(raw[25], tail));
    let tail = &(Lists::Node::Cons(raw[24], tail));
    let tail = &(Lists::Node::Cons(raw[23], tail));
    let tail = &(Lists::Node::Cons(raw[22], tail));
    let tail = &(Lists::Node::Cons(raw[21], tail));
    let tail = &(Lists::Node::Cons(raw[20], tail));
    let tail = &(Lists::Node::Cons(raw[19], tail));
    let tail = &(Lists::Node::Cons(raw[18], tail));
    let tail = &(Lists::Node::Cons(raw[17], tail));
    let tail = &(Lists::Node::Cons(raw[16], tail));
    let tail = &(Lists::Node::Cons(raw[15], tail));
    let tail = &(Lists::Node::Cons(raw[14], tail));
    let tail = &(Lists::Node::Cons(raw[13], tail));
    let tail = &(Lists::Node::Cons(raw[12], tail));
    let tail = &(Lists::Node::Cons(raw[11], tail));
    let tail = &(Lists::Node::Cons(raw[10], tail));
    let tail = &(Lists::Node::Cons(raw[9], tail));
    let tail = &(Lists::Node::Cons(raw[8], tail));
    let tail = &(Lists::Node::Cons(raw[7], tail));
    let tail = &(Lists::Node::Cons(raw[6], tail));
    let tail = &(Lists::Node::Cons(raw[5], tail));
    let tail = &(Lists::Node::Cons(raw[4], tail));
    let tail = &(Lists::Node::Cons(raw[3], tail));
    let tail = &(Lists::Node::Cons(raw[2], tail));
    let tail = &(Lists::Node::Cons(raw[1], tail));
    let tail = &(Lists::Node::Cons(raw[0], tail));
    tail
  }

  fn point_list_bytes(points: Lists::List<Point>) -> Lists::List<Field> {
    match *points {
      Lists::Node::Nil => &(Lists::Node::Nil),
      Lists::Node::Cons(point, rest) => prepend32(to_bytes(point), point_list_bytes(rest)),
    }
  }

  fn row_list_bytes(rows: Lists::List<Lists::List<Point>>) -> Lists::List<Field> {
    match *rows {
      Lists::Node::Nil => &(Lists::Node::Nil),
      Lists::Node::Cons(points, rest) => {
        let row = prepend8(bytes64(Lists::length(points)), point_list_bytes(points));
        Lists::concat(row, row_list_bytes(rest))
      },
    }
  }

  fn commitment_bytes(rows: Lists::List<Lists::List<Point>>) -> Lists::List<Field> {
    prepend8(bytes64(Lists::length(rows)), row_list_bytes(rows))
  }
}
⟧

def program : Modules.Program BN254.F :=
  (dependencies.append declarations).toField BN254.F

end Aiur.Library.Field.BN254.G1
