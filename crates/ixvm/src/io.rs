//! The IxVM fixture stores constant and blob bytes at contiguous offsets.
//! Bind those rows to immutable field-element vectors once, without a per-byte
//! key hash. Metadata hints still use the ordinary address-keyed data provider.
use aiur::{
  bytecode::Type,
  field::FieldBackend,
  hints::{HintChannels, HintEntry},
};

pub(super) const READ_CHANNEL: &str = "ixvm.io.read";

/// Returns false for sparse/other IO channels, retaining the ordinary data
/// provider. In particular, missing entries must not silently become zeroes.
/// Sorting avoids allocating an arena proportional to an unchecked offset.
pub(super) fn register<B: FieldBackend>(
  field: B,
  entries: &[HintEntry],
  channels: &mut HintChannels<B::Element>,
) -> Result<bool, String> {
  let key_type = Type::Tuple { items: vec![Type::Field; 2] };
  let mut rows = [vec![], vec![]];
  for entry in entries.iter().filter(|e| e.channel == READ_CHANNEL) {
    if entry.key_type != key_type
      || entry.r#type != Type::Field
      || entry.key.len() != 2
      || entry.output.len() != 1
    {
      return Err("invalid IO byte hint signature".into());
    }
    if !entry.key.iter().chain(&entry.output).all(|&word| field.contains(word))
    {
      return Err("noncanonical IO byte hint field element".into());
    }
    let arena = match entry.key[0] {
      2 => 0,
      4 => 1,
      _ => return Ok(false),
    };
    rows[arena].push(entry);
  }
  let mut arenas = [vec![], vec![]];
  for (rows, arena) in rows.iter_mut().zip(&mut arenas) {
    rows.sort_unstable_by_key(|entry| entry.key[1]);
    for entry in rows {
      let offset = entry.key[1];
      if offset > arena.len() as u64 {
        return Ok(false);
      }
      let value = field.from_u64(entry.output[0]);
      if offset == arena.len() as u64 {
        arena.push(value);
      } else if arena[offset as usize] != value {
        return Err("conflicting IO byte hint entries".into());
      }
    }
  }
  let [constants, blobs] = arenas;
  channels.insert(
    READ_CHANNEL,
    key_type,
    Type::Field,
    move |key, output| {
      let arena = match field.to_u64(key[0]) {
        2 => &constants,
        4 => &blobs,
        _ => return Err("missing hint data: unknown IO channel".into()),
      };
      let offset = usize::try_from(field.to_u64(key[1]))
        .map_err(|_| "IO byte offset exceeds host index range")?;
      output[0] = *arena
        .get(offset)
        .ok_or("missing hint data: IO byte offset out of bounds")?;
      Ok(())
    },
  )?;
  Ok(true)
}
