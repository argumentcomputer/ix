//! Immutable stream advice shared by applications. These are ordinary hint
//! closures: they do not add operations to Aiur or trust the supplied bytes.
use crate::{
  bytecode::Type,
  field::FieldBackend,
  hints::{HintChannels, HintEntry},
};
use std::sync::Arc;

/// One input stream: a channel, its key, and the values read under it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stream {
  pub channel: u64,
  pub key: Vec<u64>,
  pub values: Vec<u64>,
}

/// Compact interchange format. One entry per stream, rather than per byte.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Streams(pub Vec<Stream>);

/// An entry point, its public arguments and its input streams. Hosts read
/// invocations in Ixon (`crate::artifact`, `Invocation::load`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Invocation {
  pub entry: String,
  pub args: Vec<u64>,
  pub streams: Streams,
}

pub struct Arenas<'s, B: FieldBackend> {
  field: B,
  values: Arc<Vec<Vec<B::Element>>>,
  entries: Vec<(&'s Stream, usize)>,
}

impl Streams {
  pub fn prepare<B: FieldBackend>(
    &self,
    field: B,
  ) -> Result<Arenas<'_, B>, String> {
    let mut values = Vec::new();
    let mut entries = Vec::new();
    let mut keys = std::collections::HashSet::new();
    for stream in &self.0 {
      // This host adapter supports small numbered stream channels. The hint
      // mechanism itself has no such restriction; another closure may be used.
      let channel =
        usize::try_from(stream.channel).ok().ok_or("IO channel overflow")?;
      if channel >= 256 {
        return Err("IO arena channel must be below 256".into());
      }
      field.decode(&stream.key)?;
      if !keys.insert((stream.channel, &stream.key)) {
        return Err("duplicate IO stream key".into());
      }
      values.resize_with(values.len().max(channel + 1), Vec::new);
      let offset = values[channel].len();
      values[channel].extend(field.decode(&stream.values)?);
      entries.push((stream, offset));
    }
    Ok(Arenas { field, values: Arc::new(values), entries })
  }
}

/// A source of stream advice that applications bind to their hint names.
/// [`Arenas`] is the reference adapter over the JSON interchange format;
/// [`super::advice::Advice`] is the compact representation.
pub trait StreamAdvice<B: FieldBackend> {
  /// Bind a fixed-size array read. Array elements are raw fields; the Aiur
  /// program must range-check them before constructing opaque bytes.
  fn register_read<const N: usize>(
    &self,
    name: &str,
    scalar: bool,
    channels: &mut HintChannels<B::Element>,
  ) -> Result<(), String>;

  /// Metadata and tag hints for the streams `accepts` selects by channel and
  /// key, in submission order. With `value`, each selected stream must hold
  /// one field, which becomes the hint output; otherwise the output is its
  /// `(offset, length)`.
  fn metadata(
    &self,
    name: &str,
    key_type: &Type,
    fixed_channel: Option<u64>,
    accepts: impl Fn(u64, &[u64]) -> bool,
    value: bool,
  ) -> Result<Vec<HintEntry>, String>;
}

#[expect(clippy::too_many_arguments, reason = "one stream's metadata row")]
pub(super) fn metadata_entry(
  name: &str,
  key_type: &Type,
  fixed_channel: Option<u64>,
  value: bool,
  channel: u64,
  stream_key: &[u64],
  offset: usize,
  len: usize,
  single_value: impl FnOnce() -> u64,
) -> Result<Option<HintEntry>, String> {
  let mut key = if let Some(fixed) = fixed_channel {
    if channel != fixed {
      return Ok(None);
    }
    vec![]
  } else {
    vec![channel]
  };
  key.extend(stream_key);
  let output = if value {
    if len != 1 {
      return Err("IO value hint must contain one field".into());
    }
    vec![single_value()]
  } else {
    vec![offset as u64, len as u64]
  };
  Ok(Some(HintEntry {
    channel: name.to_owned(),
    key_type: key_type.clone(),
    key,
    r#type: if value {
      Type::Field
    } else {
      Type::Tuple { items: vec![Type::Field; 2] }
    },
    output,
  }))
}

impl<B: FieldBackend> Arenas<'_, B> {
  /// Bytes held by the prepared field-element arenas.
  pub fn retained_bytes(&self) -> usize {
    self.values.capacity() * size_of::<Vec<B::Element>>()
      + self
        .values
        .iter()
        .map(|v| v.capacity() * size_of::<B::Element>())
        .sum::<usize>()
  }
}

impl<B: FieldBackend> StreamAdvice<B> for Arenas<'_, B> {
  fn register_read<const N: usize>(
    &self,
    name: &str,
    scalar: bool,
    channels: &mut HintChannels<B::Element>,
  ) -> Result<(), String> {
    if scalar && N != 1 {
      return Err("scalar IO read must have width one".into());
    }
    let values = self.values.clone();
    let field = self.field;
    channels.insert_fixed::<2, N>(
      name,
      Type::Tuple { items: vec![Type::Field; 2] },
      if scalar {
        Type::Field
      } else {
        Type::Tuple { items: vec![Type::Field; N] }
      },
      move |[channel, offset]| {
        let channel = usize::try_from(field.to_u64(channel))
          .ok()
          .ok_or("IO channel overflow")?;
        let offset = usize::try_from(field.to_u64(offset))
          .ok()
          .ok_or("IO offset overflow")?;
        let end = offset.checked_add(N).ok_or("IO offset overflow")?;
        let row = values
          .get(channel)
          .and_then(|a| a.get(offset..end))
          .ok_or("missing hint data: IO read out of bounds")?;
        Ok(std::array::from_fn(|i| row[i]))
      },
    )
  }

  /// Reads use the shared vectors above, including when hints are replayed
  /// during tracing.
  fn metadata(
    &self,
    name: &str,
    key_type: &Type,
    fixed_channel: Option<u64>,
    accepts: impl Fn(u64, &[u64]) -> bool,
    value: bool,
  ) -> Result<Vec<HintEntry>, String> {
    let mut result = Vec::new();
    for (stream, offset) in &self.entries {
      if !accepts(stream.channel, &stream.key) {
        continue;
      }
      result.extend(metadata_entry(
        name,
        key_type,
        fixed_channel,
        value,
        stream.channel,
        &stream.key,
        *offset,
        stream.values.len(),
        || stream.values[0],
      )?);
    }
    Ok(result)
  }
}
