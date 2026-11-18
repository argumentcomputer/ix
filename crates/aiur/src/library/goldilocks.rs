//! Advice for Goldilocks residues emulated in a field larger than `2^128`.
//! All returned residues, carries and quotient bytes are checked by the Aiur
//! library. These callbacks do not replace its range or arithmetic constraints.
use crate::{
  FieldWord,
  bytecode::Type,
  field::{FieldBackend, PrimeField},
  hints::HintChannels,
};

pub const MODULUS: u64 = 0xffff_ffff_0000_0001;

fn operand<B: FieldBackend>(
  field: B,
  value: B::Element,
) -> Result<u64, String> {
  let value = field.try_to_u64(value)?;
  if value < MODULUS {
    Ok(value)
  } else {
    Err("noncanonical emulated Goldilocks operand".into())
  }
}

pub fn register<B: FieldBackend<Word = FieldWord>>(
  channels: &mut HintChannels<B::Element>,
  field: B,
) -> Result<(), String> {
  if field.modulus() <= FieldWord::from_limbs_le([0, 0, 1, 0]) {
    return Err(
      "emulated Goldilocks requires a field larger than 2^128".into(),
    );
  }
  let pair = Type::Tuple { items: vec![Type::Field; 2] };
  channels.insert_fixed::<2, 2>(
    "goldilocks.emulated.add",
    pair.clone(),
    pair.clone(),
    move |[a, b]| {
      let sum = u128::from(operand(field, a)?) + u128::from(operand(field, b)?);
      Ok([
        field.from_u64(u64::try_from(sum % u128::from(MODULUS)).unwrap()),
        field.from_u64(u64::try_from(sum / u128::from(MODULUS)).unwrap()),
      ])
    },
  )?;
  channels.insert_fixed::<2, 2>(
    "goldilocks.emulated.sub",
    pair.clone(),
    pair.clone(),
    move |[a, b]| {
      let (a, b) = (operand(field, a)?, operand(field, b)?);
      let borrow = u64::from(a < b);
      let result = u128::from(a) + u128::from(borrow) * u128::from(MODULUS)
        - u128::from(b);
      Ok([
        field.from_u64(u64::try_from(result).unwrap()),
        field.from_u64(borrow),
      ])
    },
  )?;
  channels.insert_fixed::<2, 9>(
    "goldilocks.emulated.mul",
    pair,
    Type::Tuple {
      items: vec![Type::Field, Type::Tuple { items: vec![Type::Field; 8] }],
    },
    move |[a, b]| {
      let product =
        u128::from(operand(field, a)?) * u128::from(operand(field, b)?);
      let remainder = u64::try_from(product % u128::from(MODULUS)).unwrap();
      let quotient = u64::try_from(product / u128::from(MODULUS)).unwrap();
      let bytes = quotient.to_le_bytes();
      Ok(std::array::from_fn(|i| {
        field.from_u64(if i == 0 { remainder } else { u64::from(bytes[i - 1]) })
      }))
    },
  )?;
  let goldilocks = PrimeField::new(MODULUS)?;
  channels.insert_fixed::<1, 1>(
    "goldilocks.emulated.inverse",
    Type::Field,
    Type::Field,
    move |[a]| {
      let inverse = goldilocks.inverse(operand(field, a)?).unwrap_or(0);
      Ok([field.from_u64(inverse)])
    },
  )
}
