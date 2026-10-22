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
  channels.insert(
    "u32.bytes",
    Type::Field,
    bytes.clone(),
    move |input, output| {
      write_bytes(field.to_u64(input[0]) as u32, output, field);
      Ok(())
    },
  )?;
  channels.insert(
    "u32.sub",
    Type::Tuple { items: vec![Type::Field; 2] },
    bytes.clone(),
    move |input, output| {
      write_bytes(
        (field.to_u64(input[0]) as u32)
          .wrapping_sub(field.to_u64(input[1]) as u32),
        output,
        field,
      );
      Ok(())
    },
  )?;
  register_sum::<8, _>(channels, field, "u32.add", &bytes)?;
  register_sum::<12, _>(channels, field, "u32.add3", &bytes)?;
  let pair = Type::Tuple { items: vec![Type::Field; 2] };
  channels.insert(
    "u32.lt",
    pair,
    Type::Tuple { items: vec![bytes; 3] },
    move |input, output| {
      let (a, b) =
        (field.to_u64(input[0]) as u32, field.to_u64(input[1]) as u32);
      write_bytes(a, &mut output[..4], field);
      write_bytes(a.wrapping_sub(b), &mut output[4..8], field);
      write_bytes(b, &mut output[8..], field);
      Ok(())
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

fn write_bytes<B: FieldBackend>(
  word: u32,
  output: &mut [B::Element],
  field: B,
) {
  for (dest, byte) in output.iter_mut().zip(word.to_le_bytes()) {
    *dest = field.from_u64(u64::from(byte));
  }
}
