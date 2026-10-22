//! Raw byte-decomposition advice shared by word arithmetic and IxVM conversion.
//! Aiur range lookups and recomposition constraints validate the answer.
use crate::{bytecode::Type, field::FieldBackend, hints::HintChannels};

pub fn register<B: FieldBackend>(
  channels: &mut HintChannels<B::Element>,
  field: B,
) -> Result<(), String> {
  channels.insert(
    "bytes_le",
    Type::Field,
    Type::Tuple { items: vec![Type::Field; 8] },
    move |input, output| {
      for (dest, byte) in
        output.iter_mut().zip(field.to_u64(input[0]).to_le_bytes())
      {
        *dest = field.from_u64(u64::from(byte));
      }
      Ok(())
    },
  )
}
