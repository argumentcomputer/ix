//! Immutable stream advice shared by applications. These are ordinary hint
//! closures: they do not add operations to Aiur or trust the supplied bytes.
use crate::{
  bytecode::Type,
  field::FieldBackend,
  hints::{HintChannels, HintEntry},
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Stream {
  pub channel: u64,
  pub key: Vec<u64>,
  pub values: Vec<u64>,
}

/// Compact interchange format. One entry per stream, rather than per byte.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Streams(pub Vec<Stream>);

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Invocation {
  pub entry: String,
  pub args: Vec<u64>,
  #[serde(default)]
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
        usize::try_from(stream.channel).map_err(|_| "IO channel overflow")?;
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

impl<B: FieldBackend> Arenas<'_, B> {
  /// Bind a fixed-size array read. Array elements are raw fields; the Aiur
  /// program must range-check them before constructing opaque bytes.
  pub fn register_read<const N: usize>(
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
          .map_err(|_| "IO channel overflow")?;
        let offset = usize::try_from(field.to_u64(offset))
          .map_err(|_| "IO offset overflow")?;
        let end = offset.checked_add(N).ok_or("IO offset overflow")?;
        let row = values
          .get(channel)
          .and_then(|a| a.get(offset..end))
          .ok_or("missing hint data: IO read out of bounds")?;
        Ok(std::array::from_fn(|i| row[i]))
      },
    )
  }

  /// Metadata and tag hints retain ordinary data semantics. Reads use the
  /// shared vectors above, including when hints are replayed during tracing.
  pub fn metadata(
    &self,
    name: &str,
    key_type: Type,
    fixed_channel: Option<u64>,
    accepts: impl Fn(&Stream) -> bool,
    value: bool,
  ) -> Result<Vec<HintEntry>, String> {
    let mut result = Vec::new();
    for (stream, offset) in &self.entries {
      if !accepts(stream) {
        continue;
      }
      let mut key = if let Some(channel) = fixed_channel {
        if stream.channel != channel {
          continue;
        }
        vec![]
      } else {
        vec![stream.channel]
      };
      key.extend(&stream.key);
      let output = if value {
        if stream.values.len() != 1 {
          return Err("IO value hint must contain one field".into());
        }
        stream.values.clone()
      } else {
        vec![*offset as u64, stream.values.len() as u64]
      };
      result.push(HintEntry {
        channel: name.to_owned(),
        key_type: key_type.clone(),
        key,
        r#type: if value {
          Type::Field
        } else {
          Type::Tuple { items: vec![Type::Field; 2] }
        },
        output,
      });
    }
    Ok(result)
  }
}
