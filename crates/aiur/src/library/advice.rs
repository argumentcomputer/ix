//! Compact immutable stream advice. Byte streams are retained as bytes and
//! numeric streams as validated field words; a read converts only the bytes
//! it returns. Streams are addressed exactly as [`super::io::Streams`] lays
//! them out: each channel is one contiguous arena, and a stream's offset is
//! the channel's length when it is appended, so the same submission order
//! yields the same offsets, hint values and execution records.
use super::io::{StreamAdvice, metadata_entry};
use crate::{
  bytecode::Type,
  field::FieldBackend,
  hints::{HintChannels, HintEntry},
};
use std::{collections::HashSet, sync::Arc};

/// Channels are numbered below this limit, as for the JSON stream adapter.
pub const CHANNEL_LIMIT: u64 = 256;

/// One stream's values: bytes, or arbitrary field words that must be
/// canonical. Both are read back as field elements with the same values.
#[derive(Clone, Copy, Debug)]
pub enum Payload<'a> {
  Bytes(&'a [u8]),
  Words(&'a [u64]),
}

/// One stream as submitted, borrowing its key and payload.
#[derive(Clone, Copy, Debug)]
pub struct Entry<'a> {
  pub channel: u64,
  pub key: &'a [u64],
  pub payload: Payload<'a>,
}

/// A channel stays in byte form until a numeric stream is appended to it;
/// it is then widened once, preserving every earlier value and offset.
#[derive(Clone, Debug)]
enum Arena<E> {
  Bytes(Vec<u8>),
  Words(Vec<E>),
}

impl<E: Copy> Arena<E> {
  fn len(&self) -> usize {
    match self {
      Arena::Bytes(bytes) => bytes.len(),
      Arena::Words(words) => words.len(),
    }
  }

  fn retained_bytes(&self) -> usize {
    match self {
      Arena::Bytes(bytes) => bytes.capacity(),
      Arena::Words(words) => words.capacity() * size_of::<E>(),
    }
  }

  fn shrink_to_fit(&mut self) {
    match self {
      Arena::Bytes(bytes) => bytes.shrink_to_fit(),
      Arena::Words(words) => words.shrink_to_fit(),
    }
  }

  fn read<B: FieldBackend<Element = E>, const N: usize>(
    &self,
    field: B,
    offset: usize,
  ) -> Option<[E; N]> {
    let end = offset.checked_add(N)?;
    Some(match self {
      Arena::Bytes(bytes) => {
        let row = bytes.get(offset..end)?;
        std::array::from_fn(|i| field.from_u64(u64::from(row[i])))
      },
      Arena::Words(words) => {
        let row = words.get(offset..end)?;
        std::array::from_fn(|i| row[i])
      },
    })
  }
}

/// Where a stream lives. Keys are kept only to build metadata hints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StreamInfo {
  pub channel: u64,
  pub key: Box<[u64]>,
  pub offset: usize,
  pub len: usize,
}

/// Bytes held by an [`Advice`]. Hint closures retain `payload` for as long
/// as the prepared hints (or any replay of them) live; `metadata` is needed
/// only while binding, after which the hint data maps hold their own copy.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AdviceBytes {
  pub payload: usize,
  pub metadata: usize,
}

impl AdviceBytes {
  pub fn total(self) -> usize {
    self.payload + self.metadata
  }
}

/// Immutable advice for one job. Cloning shares the payload arenas.
#[derive(Clone, Debug)]
pub struct Advice<B: FieldBackend> {
  field: B,
  arenas: Arc<[Arena<B::Element>]>,
  streams: Vec<StreamInfo>,
}

/// Appends streams in submission order, validating each one.
pub struct AdviceBuilder<B: FieldBackend> {
  field: B,
  arenas: Vec<Arena<B::Element>>,
  streams: Vec<StreamInfo>,
  keys: HashSet<(u64, Box<[u64]>)>,
}

impl<B: FieldBackend> AdviceBuilder<B> {
  pub fn new(field: B) -> Result<Self, String> {
    if !field.contains(u64::from(u8::MAX)) {
      return Err("field cannot represent every byte".into());
    }
    Ok(Self { field, arenas: vec![], streams: vec![], keys: HashSet::new() })
  }

  /// Validates the channel and key and reserves the stream's offset.
  fn arena(
    &mut self,
    channel: u64,
    key: &[u64],
  ) -> Result<&mut Arena<B::Element>, String> {
    if channel >= CHANNEL_LIMIT {
      return Err("IO arena channel must be below 256".into());
    }
    if !key.iter().all(|&word| self.field.contains(word)) {
      return Err("noncanonical field element".into());
    }
    if !self.keys.insert((channel, key.into())) {
      return Err("duplicate IO stream key".into());
    }
    let index = channel as usize;
    if self.arenas.len() <= index {
      self.arenas.resize_with(index + 1, || Arena::Bytes(vec![]));
    }
    Ok(&mut self.arenas[index])
  }

  fn record(&mut self, channel: u64, key: &[u64], offset: usize, len: usize) {
    self.streams.push(StreamInfo { channel, key: key.into(), offset, len });
  }

  pub fn push(&mut self, entry: Entry<'_>) -> Result<(), String> {
    match entry.payload {
      Payload::Bytes(bytes) => self.push_bytes(entry.channel, entry.key, bytes),
      Payload::Words(words) => self.push_words(entry.channel, entry.key, words),
    }
  }

  pub fn push_bytes(
    &mut self,
    channel: u64,
    key: &[u64],
    bytes: &[u8],
  ) -> Result<(), String> {
    let field = self.field;
    let arena = self.arena(channel, key)?;
    let offset = arena.len();
    match arena {
      Arena::Bytes(arena) => arena.extend_from_slice(bytes),
      Arena::Words(arena) => {
        arena.extend(bytes.iter().map(|&b| field.from_u64(u64::from(b))));
      },
    }
    self.record(channel, key, offset, bytes.len());
    Ok(())
  }

  /// Words must be canonical. After any error the builder is discarded: the
  /// rejected stream may already have reserved its key.
  pub fn push_words(
    &mut self,
    channel: u64,
    key: &[u64],
    words: &[u64],
  ) -> Result<(), String> {
    let field = self.field;
    let arena = self.arena(channel, key)?;
    let offset = arena.len();
    if let Arena::Bytes(bytes) = arena {
      let mut widened = Vec::with_capacity(bytes.len() + words.len());
      widened.extend(bytes.iter().map(|&b| field.from_u64(u64::from(b))));
      *arena = Arena::Words(widened);
    }
    let Arena::Words(arena) = arena else { unreachable!() };
    arena.extend(field.decode(words)?);
    self.record(channel, key, offset, words.len());
    Ok(())
  }

  pub fn finish(self) -> Advice<B> {
    let mut arenas = self.arenas;
    arenas.iter_mut().for_each(Arena::shrink_to_fit);
    let mut streams = self.streams;
    streams.shrink_to_fit();
    Advice { field: self.field, arenas: arenas.into(), streams }
  }
}

impl<B: FieldBackend> Advice<B> {
  /// Builds advice from typed entries in submission order.
  pub fn from_entries<'a>(
    field: B,
    entries: impl IntoIterator<Item = Entry<'a>>,
  ) -> Result<Self, String> {
    let mut builder = AdviceBuilder::new(field)?;
    for entry in entries {
      builder.push(entry)?;
    }
    Ok(builder.finish())
  }

  /// Adapter for the JSON interchange format. A stream is stored as bytes
  /// only when every value is below 256, so every read returns the value
  /// the reference adapter would return and invalid words are rejected
  /// identically.
  pub fn from_streams(
    field: B,
    streams: &super::io::Streams,
  ) -> Result<Self, String> {
    let mut builder = AdviceBuilder::new(field)?;
    let mut bytes = vec![];
    for stream in &streams.0 {
      if stream.values.iter().all(|&v| v <= u64::from(u8::MAX)) {
        bytes.clear();
        bytes.extend(stream.values.iter().map(|&v| v as u8));
        builder.push_bytes(stream.channel, &stream.key, &bytes)?;
      } else {
        builder.push_words(stream.channel, &stream.key, &stream.values)?;
      }
    }
    Ok(builder.finish())
  }

  pub fn streams(&self) -> &[StreamInfo] {
    &self.streams
  }

  /// Whether `channel` is held as bytes. Unused channels are empty byte
  /// arenas.
  pub fn is_byte_channel(&self, channel: u64) -> bool {
    matches!(self.arenas.get(channel as usize), Some(Arena::Bytes(_)))
  }

  pub fn retained_bytes(&self) -> AdviceBytes {
    let payload = self.arenas.iter().map(Arena::retained_bytes).sum::<usize>()
      + self.arenas.len() * size_of::<Arena<B::Element>>();
    let metadata = self.streams.capacity() * size_of::<StreamInfo>()
      + self.streams.iter().map(|s| s.key.len() * 8).sum::<usize>();
    AdviceBytes { payload, metadata }
  }

  fn value(&self, stream: &StreamInfo) -> u64 {
    match &self.arenas[stream.channel as usize] {
      Arena::Bytes(bytes) => u64::from(bytes[stream.offset]),
      Arena::Words(words) => self.field.to_u64(words[stream.offset]),
    }
  }
}

impl<B: FieldBackend> StreamAdvice<B> for Advice<B> {
  fn register_read<const N: usize>(
    &self,
    name: &str,
    scalar: bool,
    channels: &mut HintChannels<B::Element>,
  ) -> Result<(), String> {
    if scalar && N != 1 {
      return Err("scalar IO read must have width one".into());
    }
    let arenas = self.arenas.clone();
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
        offset.checked_add(N).ok_or("IO offset overflow")?;
        arenas
          .get(channel)
          .and_then(|arena| arena.read::<B, N>(field, offset))
          .ok_or_else(|| "missing hint data: IO read out of bounds".into())
      },
    )
  }

  fn metadata(
    &self,
    name: &str,
    key_type: Type,
    fixed_channel: Option<u64>,
    accepts: impl Fn(u64, &[u64]) -> bool,
    value: bool,
  ) -> Result<Vec<HintEntry>, String> {
    let mut result = vec![];
    for stream in &self.streams {
      if !accepts(stream.channel, &stream.key) {
        continue;
      }
      let entry = metadata_entry(
        name,
        &key_type,
        fixed_channel,
        value,
        stream.channel,
        &stream.key,
        stream.offset,
        stream.len,
        || self.value(stream),
      )?;
      result.extend(entry);
    }
    Ok(result)
  }
}

#[cfg(test)]
mod tests;
