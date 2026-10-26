//! Raw byte-decomposition advice shared by word arithmetic and IxVM conversion.
//! Aiur range lookups and recomposition constraints validate the answer.
use crate::{bytecode::Type, field::FieldBackend, hints::HintChannels};

pub fn register<B: FieldBackend>(
  channels: &mut HintChannels<B::Element>,
  field: B,
) -> Result<(), String> {
  channels.insert_fixed::<1, 8>(
    "bytes_le",
    Type::Field,
    Type::Tuple { items: vec![Type::Field; 8] },
    #[inline(always)]
    move |input| {
      Ok(
        field
          .to_u64(input[0])
          .to_le_bytes()
          .map(|byte| field.from_u64(u64::from(byte))),
      )
    },
  )
}
