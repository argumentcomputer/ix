import Aiur.Library.Field.BN254
import Aiur.Library.Field
import Aiur.Library.Frontend

/-! Canonical BN254 base-field elements in four radix-2^80 limbs over Fr.
Advice supplies candidate bytes, remainders, quotients and signed carries.
Fixed 8- and 16-bit lookups, boolean borrows and integer limb equations constrain them.
The bounds below justify interpreting every limb equation over the integers;
they do not constitute a source-level correctness proof of the library. -/
namespace Aiur.Library.Field.BN254.Fq
open Aiur

def modulus : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583
def radix : Nat := 2^80

theorem coefficient_bound : 32 * radix^2 + 32 * radix < BN254.modulus := by decide
theorem byte_pack_bound : 2^88 < BN254.modulus := by decide
theorem canonical_bound : 4 * radix < BN254.modulus := by decide

def dependencies : Modules.Program Nat := Library.Field.declarations

private def implementation : Modules.Program Nat := aiur_library% dependencies ⟦
module BN254Fq {
  table byte_inputs: (Field,) {}
  table byte_units: () {}
  map byte(value: Field) -> () = byte_inputs => byte_units;
  table limb16_inputs: (Field,) {}
  table limb16_units: () {}
  map limb16(value: Field) -> () = limb16_inputs => limb16_units;
  opaque type Fq = [Field; 4];
  const RADIX: Field = 1208925819614629174706176;
  const BIAS: Field = 9671406556917033397649408;
  const CORRECTION: Field = 11692013098647223345629468990323707240214062694400;
  const ZERO: Fq = [0; 4];
  const ONE: Fq = [1, 0, 0, 0];

  inline fn checked_pack80(raw: [Field; 10]) -> Field {
    byte(raw[0]);
    byte(raw[1]);
    byte(raw[2]);
    byte(raw[3]);
    byte(raw[4]);
    byte(raw[5]);
    byte(raw[6]);
    byte(raw[7]);
    byte(raw[8]);
    byte(raw[9]);
    1 * raw[0] + 256 * raw[1] + 65536 * raw[2] + 16777216 * raw[3] + 4294967296 * raw[4] + 1099511627776 * raw[5] + 281474976710656 * raw[6] + 72057594037927936 * raw[7] + 18446744073709551616 * raw[8] + 4722366482869645213696 * raw[9]
  }

  inline fn checked_pack80_u16(raw: [Field; 5]) -> Field {
    limb16(raw[0]); limb16(raw[1]); limb16(raw[2]); limb16(raw[3]); limb16(raw[4]);
    raw[0] + 65536 * raw[1] + 4294967296 * raw[2] + 281474976710656 * raw[3] + 18446744073709551616 * raw[4]
  }

  fn range80(value: Field) -> () {
    let raw = hint::<[Field; 5]>("bn254.fq.u16_80", value);
    assert_eq!(checked_pack80_u16(raw), value, "Fq 80-bit decomposition");
    ()
  }

  fn range84(value: Field) -> () {
    let raw = hint::<[Field; 6]>("bn254.fq.u16_84", value);
    let low = checked_pack80_u16([raw[0], raw[1], raw[2], raw[3], raw[4]]);
    byte(raw[5]);
    byte(16 * raw[5]);
    assert_eq!(low + RADIX * raw[5], value, "Fq 84-bit decomposition");
    ()
  }

  inline fn bound(raw: [Field; 4]) -> () {
    range80(raw[0]); range80(raw[1]); range80(raw[2]); range80(raw[3]); ()
  }

  fn from_limbs(raw: [Field; 4]) -> Fq {
    bound(raw);
    let (difference, borrow) = hint::<([Field; 4], [Field; 4])>("bn254.fq.canonical", raw);
    bound(difference);
    assert_eq!(borrow[0] * (borrow[0] - 1), 0, "Fq canonical borrow");
    assert_eq!(956523353070932659600710 - raw[0] - 0 + RADIX * borrow[0], difference[0], "Fq canonical subtraction");
    assert_eq!(borrow[1] * (borrow[1] - 1), 0, "Fq canonical borrow");
    assert_eq!(611571273687723030964337 - raw[1] - borrow[0] + RADIX * borrow[1], difference[1], "Fq canonical subtraction");
    assert_eq!(borrow[2] * (borrow[2] - 1), 0, "Fq canonical borrow");
    assert_eq!(370463741415268654532022 - raw[2] - borrow[1] + RADIX * borrow[2], difference[2], "Fq canonical subtraction");
    assert_eq!(borrow[3] * (borrow[3] - 1), 0, "Fq canonical borrow");
    assert_eq!(12388 - raw[3] - borrow[2] + RADIX * borrow[3], difference[3], "Fq canonical subtraction");
    assert_eq!(borrow[3], 0, "noncanonical Fq");
    raw
  }

  inline fn to_limbs(value: Fq) -> [Field; 4] { value }
  inline fn is_zero(value: Fq) -> Field {
    Fields::is_zero(value[0] + value[1] + value[2] + value[3])
  }

  fn add(a: Fq, b: Fq) -> Fq {
    let (raw, quotient, carry) = hint::<([Field; 4], Field, [Field; 3])>("bn254.fq.add", (to_limbs(a), to_limbs(b)));
    let result = from_limbs(raw);
    assert_eq!(quotient * (quotient - 1), 0, "Fq add/sub quotient");
    range84(carry[0]);
    range84(carry[1]);
    range84(carry[2]);
    assert_eq!(a[0] + b[0] - raw[0] - quotient * 956523353070932659600711 + BIAS + CORRECTION, RADIX * carry[0], "Fq add limb 0");
    assert_eq!(a[1] + b[1] - raw[1] - quotient * 611571273687723030964337 + carry[0] + CORRECTION, RADIX * carry[1], "Fq add limb 1");
    assert_eq!(a[2] + b[2] - raw[2] - quotient * 370463741415268654532022 + carry[1] + CORRECTION, RADIX * carry[2], "Fq add limb 2");
    assert_eq!(a[3] + b[3] - raw[3] - quotient * 12388 + carry[2] + CORRECTION, RADIX * BIAS, "Fq add limb 3");
    result
  }

  fn sub(a: Fq, b: Fq) -> Fq {
    let (raw, quotient, carry) = hint::<([Field; 4], Field, [Field; 3])>("bn254.fq.sub", (to_limbs(a), to_limbs(b)));
    let result = from_limbs(raw);
    assert_eq!(quotient * (quotient - 1), 0, "Fq add/sub quotient");
    range84(carry[0]);
    range84(carry[1]);
    range84(carry[2]);
    assert_eq!(a[0] + quotient * 956523353070932659600711 - b[0] - raw[0] + BIAS + CORRECTION, RADIX * carry[0], "Fq sub limb 0");
    assert_eq!(a[1] + quotient * 611571273687723030964337 - b[1] - raw[1] + carry[0] + CORRECTION, RADIX * carry[1], "Fq sub limb 1");
    assert_eq!(a[2] + quotient * 370463741415268654532022 - b[2] - raw[2] + carry[1] + CORRECTION, RADIX * carry[2], "Fq sub limb 2");
    assert_eq!(a[3] + quotient * 12388 - b[3] - raw[3] + carry[2] + CORRECTION, RADIX * BIAS, "Fq sub limb 3");
    result
  }

  inline fn neg(value: Fq) -> Fq { sub(ZERO, value) }

  fn mul(a: Fq, b: Fq) -> Fq {
    let (raw, quotient, carry) = hint::<([Field; 4], [Field; 4], [Field; 7])>("bn254.fq.mul", (to_limbs(a), to_limbs(b)));
    let result = from_limbs(raw);
    bound(quotient);
    range84(carry[0]);
    range84(carry[1]);
    range84(carry[2]);
    range84(carry[3]);
    range84(carry[4]);
    range84(carry[5]);
    range84(carry[6]);
    assert_eq!(a[0] * b[0] - quotient[0] * 956523353070932659600711 - raw[0] + BIAS + CORRECTION, RADIX * carry[0], "Fq mul limb 0");
    assert_eq!(a[0] * b[1] + a[1] * b[0] - quotient[0] * 611571273687723030964337 - quotient[1] * 956523353070932659600711 - raw[1] + carry[0] + CORRECTION, RADIX * carry[1], "Fq mul limb 1");
    assert_eq!(a[0] * b[2] + a[1] * b[1] + a[2] * b[0] - quotient[0] * 370463741415268654532022 - quotient[1] * 611571273687723030964337 - quotient[2] * 956523353070932659600711 - raw[2] + carry[1] + CORRECTION, RADIX * carry[2], "Fq mul limb 2");
    assert_eq!(a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0] - quotient[0] * 12388 - quotient[1] * 370463741415268654532022 - quotient[2] * 611571273687723030964337 - quotient[3] * 956523353070932659600711 - raw[3] + carry[2] + CORRECTION, RADIX * carry[3], "Fq mul limb 3");
    assert_eq!(a[1] * b[3] + a[2] * b[2] + a[3] * b[1] - quotient[1] * 12388 - quotient[2] * 370463741415268654532022 - quotient[3] * 611571273687723030964337 + carry[3] + CORRECTION, RADIX * carry[4], "Fq mul limb 4");
    assert_eq!(a[2] * b[3] + a[3] * b[2] - quotient[2] * 12388 - quotient[3] * 370463741415268654532022 + carry[4] + CORRECTION, RADIX * carry[5], "Fq mul limb 5");
    assert_eq!(a[3] * b[3] - quotient[3] * 12388 + carry[5] + CORRECTION, RADIX * carry[6], "Fq mul limb 6");
    assert_eq!(0 + carry[6] + CORRECTION, RADIX * BIAS, "Fq mul limb 7");
    result
  }

  fn inverse(a: Fq) -> Fq {
    let result = from_limbs(hint::<[Field; 4]>("bn254.fq.inverse", to_limbs(a)));
    let product = to_limbs(mul(a, result));
    assert_eq!(product[0], 1, "Fq inverse product");
    assert_eq!(product[1], 0, "Fq inverse product");
    assert_eq!(product[2], 0, "Fq inverse product");
    assert_eq!(product[3], 0, "Fq inverse product");
    result
  }

  inline fn div(a: Fq, b: Fq) -> Fq { mul(a, inverse(b)) }
}
⟧

/-- Complete range tables, independent of advice or the workload. -/
def declarations : Modules.Program Nat :=
  { implementation with modules := implementation.modules.map fun m =>
      {m with body := match m.body with
        | .definitions d => .definitions {d with program.tables := [
            ⟨"byte_inputs", .tuple [.field], (List.range 256).map fun n => .tuple [.literal n]⟩,
            ⟨"byte_units", .tuple [], (List.range 256).map fun _ => .tuple []⟩,
            ⟨"limb16_inputs", .tuple [.field], (List.range 65536).map fun n => .tuple [.literal n]⟩,
            ⟨"limb16_units", .tuple [], (List.range 65536).map fun _ => .tuple []⟩]}
        | body => body} }

def program : Modules.Program BN254.F :=
  (Library.Field.declarations.append declarations).toField BN254.F

end Aiur.Library.Field.BN254.Fq
