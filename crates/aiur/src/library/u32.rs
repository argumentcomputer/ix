//! Advice for `Aiur.Library.U32`. All answers are raw fields; the source library
//! constrains them before constructing opaque bytes or words. No Goldilocks
//! arithmetic is needed here.
use crate::{bytecode::Type, field::FieldBackend, hints::HintChannels};

pub const MIN_MODULUS: u64 = 3 * (1_u64 << 32);

pub fn register<B: FieldBackend>(
  channels: &mut HintChannels<B::Element>,
  field: B,
) -> Result<(), String> {
  if field.modulus() < MIN_MODULUS {
    return Err(format!(
      "u32 arithmetic requires a field modulus >= {MIN_MODULUS}"
    ));
  }
  let bytes = Type::Tuple { items: vec![Type::Field; 4] };
  channels.insert_fixed::<1, 4>(
    "u32.bytes",
    Type::Field,
    bytes.clone(),
    #[inline(always)]
    move |input| Ok(bytes_of(field.to_u64(input[0]) as u32, field)),
  )?;
  channels.insert_fixed::<2, 4>(
    "u32.sub",
    Type::Tuple { items: vec![Type::Field; 2] },
    bytes.clone(),
    #[inline(always)]
    move |input| {
      Ok(bytes_of(
        (field.to_u64(input[0]) as u32)
          .wrapping_sub(field.to_u64(input[1]) as u32),
        field,
      ))
    },
  )?;
  register_sum::<8, _>(channels, field, "u32.add", &bytes)?;
  register_sum::<12, _>(channels, field, "u32.add3", &bytes)?;
  let pair = Type::Tuple { items: vec![Type::Field; 2] };
  channels.insert_fixed::<2, 12>(
    "u32.lt",
    pair,
    Type::Tuple { items: vec![bytes; 3] },
    #[inline(always)]
    move |input| {
      let (a, b) =
        (field.to_u64(input[0]) as u32, field.to_u64(input[1]) as u32);
      let a_bytes = bytes_of(a, field);
      let delta = bytes_of(a.wrapping_sub(b), field);
      let b_bytes = bytes_of(b, field);
      Ok(std::array::from_fn(|i| match i / 4 {
        0 => a_bytes[i],
        1 => delta[i - 4],
        _ => b_bytes[i - 8],
      }))
    },
  )
}

fn register_sum<const INPUTS: usize, B: FieldBackend>(
  channels: &mut HintChannels<B::Element>,
  field: B,
  name: &str,
  bytes: &Type,
) -> Result<(), String> {
  channels.insert_fixed::<INPUTS, 4>(
    name,
    Type::Tuple { items: vec![bytes.clone(); INPUTS / 4] },
    bytes.clone(),
    #[inline(always)]
    move |input| {
      let mut sum = 0u32;
      for word in input.as_chunks::<4>().0 {
        let mut bytes = [0u8; 4];
        for (byte, &value) in bytes.iter_mut().zip(word) {
          *byte = u8::try_from(field.to_u64(value))
            .map_err(|_| "non-byte u32 sum operand")?;
        }
        sum = sum.wrapping_add(u32::from_le_bytes(bytes));
      }
      Ok(sum.to_le_bytes().map(|byte| field.from_u64(u64::from(byte))))
    },
  )
}

#[inline(always)]
fn bytes_of<B: FieldBackend>(word: u32, field: B) -> [B::Element; 4] {
  word.to_le_bytes().map(|byte| field.from_u64(u64::from(byte)))
}
