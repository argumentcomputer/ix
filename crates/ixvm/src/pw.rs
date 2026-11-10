//! The binder data of IxVM's conversion (decision D2), served from IO
//! channel 7. Nothing here is trusted: the circuit validates every datum
//! where the kernel's rules do, so a wrong one can only fail a claim.
//!
//! The Lean annotator (`Ix/IxVM/PwHints.lean`) writes one stream per record,
//! keyed by the record's 32 address bytes, whose values are the record's
//! entry conversions:
//!
//! ```text
//! values = nblocks (ekind eidx variant nnodes node*)*
//! node   = 0            a binder, `never`
//!        | 1 v          a share site, its entry converted at variant `v`
//!        | 2+k p1 … pk  a binder, `ifAllZero [p1 … pk]`
//! ```
//!
//! The circuit reads three channels, keyed by
//! `(rec, ekind, eidx, variant, ordinal)`, `rec` the address as 32 fields:
//! `ixvm.pw` (`0` for `never`, `k + 1` for `ifAllZero` with `k` parameters),
//! `ixvm.pw.param` (the key and `j`: the `j`-th parameter) and
//! `ixvm.pw.share` (the variant of a share site). A key the table lacks is a
//! host error that names it.
use aiur::{
  bytecode::Type, field::FieldBackend, hints::HintChannels,
  library::io::Streams,
};
use std::collections::HashMap;
use std::sync::Arc;

/// The IO channel of the binder data.
pub(super) const STREAM_CHANNEL: u64 = 7;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Node {
  Never,
  AllZero { start: u32, len: u32 },
  Share(u64),
}

/// `(rec, ekind, eidx, variant)`: one conversion of one entry.
type BlockKey = ([u8; 32], u64, u64, u64);

/// Every record's conversions, by entry and variant, their nodes by ordinal.
#[derive(Debug, Default)]
pub(super) struct Table {
  params: Vec<u64>,
  blocks: HashMap<BlockKey, Vec<Node>>,
}

struct Reader<'a> {
  values: &'a [u64],
  next: usize,
}

impl Reader<'_> {
  fn read(&mut self) -> Result<u64, String> {
    let v = *self
      .values
      .get(self.next)
      .ok_or("binder data: a record's stream ends early")?;
    self.next += 1;
    Ok(v)
  }
}

fn hex(address: &[u8; 32]) -> String {
  use std::fmt::Write as _;
  address.iter().fold(String::new(), |mut s, b| {
    let _ = write!(s, "{b:02x}");
    s
  })
}

fn address(fields: &[u64]) -> Result<[u8; 32], String> {
  if fields.len() != 32 {
    return Err("binder data: a record address is not 32 bytes".into());
  }
  let mut out = [0u8; 32];
  for (byte, &field) in out.iter_mut().zip(fields) {
    *byte = u8::try_from(field)
      .map_err(|_| "binder data: a record address byte exceeds 255")?;
  }
  Ok(out)
}

impl Table {
  /// The table of the streams on `STREAM_CHANNEL`.
  pub(super) fn from_streams(streams: &Streams) -> Result<Self, String> {
    let mut table = Self::default();
    for s in streams.0.iter().filter(|s| s.channel == STREAM_CHANNEL) {
      table.add_record(address(&s.key)?, &s.values)?;
    }
    Ok(table)
  }

  fn add_record(&mut self, rec: [u8; 32], values: &[u64]) -> Result<(), String> {
    let mut r = Reader { values, next: 0 };
    for _ in 0..r.read()? {
      let (ekind, eidx, variant) = (r.read()?, r.read()?, r.read()?);
      let size = r.read()?;
      let mut nodes = Vec::with_capacity(
        usize::try_from(size).unwrap_or(usize::MAX).min(values.len()),
      );
      for _ in 0..size {
        let node = match r.read()? {
          0 => Node::Never,
          1 => Node::Share(r.read()?),
          tag => {
            let len = u32::try_from(tag - 2)
              .map_err(|_| "binder data: too many parameters")?;
            let start = u32::try_from(self.params.len())
              .map_err(|_| "binder data: too many parameters")?;
            for _ in 0..len {
              let p = r.read()?;
              self.params.push(p);
            }
            Node::AllZero { start, len }
          },
        };
        nodes.push(node);
      }
      if self.blocks.insert((rec, ekind, eidx, variant), nodes).is_some() {
        return Err(format!(
          "binder data: record {} has two blocks for entry ({ekind}, {eidx}) \
           variant {variant}",
          hex(&rec)
        ));
      }
    }
    if r.next != values.len() {
      return Err(format!(
        "binder data: record {}'s stream has trailing values",
        hex(&rec)
      ));
    }
    Ok(())
  }

  /// The node at a 36-field key, or the error naming the key.
  fn node(&self, channel: &str, key: &[u64]) -> Result<Node, String> {
    let rec = address(&key[..32])?;
    let (ekind, eidx, variant, ordinal) = (key[32], key[33], key[34], key[35]);
    let missing = || {
      format!(
        "missing hint data: {channel} at record {}, entry ({ekind}, {eidx}), \
         variant {variant}, ordinal {ordinal}",
        hex(&rec)
      )
    };
    let nodes =
      self.blocks.get(&(rec, ekind, eidx, variant)).ok_or_else(missing)?;
    let ordinal = usize::try_from(ordinal).map_err(|_| missing())?;
    nodes.get(ordinal).copied().ok_or_else(missing)
  }

  /// `ixvm.pw`: `0` for `never`, `k + 1` for `ifAllZero` with `k`
  /// parameters.
  pub(super) fn pw(&self, key: &[u64; 36]) -> Result<u64, String> {
    match self.node("ixvm.pw", key)? {
      Node::Never => Ok(0),
      Node::AllZero { len, .. } => Ok(u64::from(len) + 1),
      Node::Share(_) => {
        Err(format!("{} (a share site)", self.node_error("ixvm.pw", key)))
      },
    }
  }

  /// `ixvm.pw.param`: the `j`-th parameter of an `ifAllZero` datum.
  pub(super) fn param(&self, key: &[u64; 37]) -> Result<u64, String> {
    let j = key[36];
    match self.node("ixvm.pw.param", &key[..36])? {
      Node::AllZero { start, len } if j < u64::from(len) => {
        let at = usize::try_from(u64::from(start) + j)
          .map_err(|_| "binder data: parameter index overflow")?;
        Ok(self.params[at])
      },
      _ => Err(format!(
        "{} (no parameter {j})",
        self.node_error("ixvm.pw.param", &key[..36])
      )),
    }
  }

  /// `ixvm.pw.share`: the variant a share site's entry is converted with.
  pub(super) fn share(&self, key: &[u64; 36]) -> Result<u64, String> {
    match self.node("ixvm.pw.share", key)? {
      Node::Share(v) => Ok(v),
      _ => Err(format!(
        "{} (a binder)",
        self.node_error("ixvm.pw.share", key)
      )),
    }
  }

  fn node_error(&self, channel: &str, key: &[u64]) -> String {
    let rec = address(&key[..32]).map(|a| hex(&a)).unwrap_or_default();
    format!(
      "missing hint data: {channel} at record {rec}, entry ({}, {}), variant \
       {}, ordinal {}",
      key[32], key[33], key[34], key[35]
    )
  }
}

/// Bind `ixvm.pw`, `ixvm.pw.param` and `ixvm.pw.share` to `table`.
pub(super) fn register<B: FieldBackend>(
  field: B,
  table: Arc<Table>,
  channels: &mut HintChannels<B::Element>,
) -> Result<(), String> {
  let address = Type::Tuple { items: vec![Type::Field; 32] };
  let key = |fields: usize| {
    let mut items = vec![address.clone()];
    items.extend(std::iter::repeat_n(Type::Field, fields));
    Type::Tuple { items }
  };
  let t = table.clone();
  channels.insert_fixed::<36, 1>(
    "ixvm.pw",
    key(4),
    Type::Field,
    move |k| Ok([field.from_u64(t.pw(&k.map(|w| field.to_u64(w)))?)]),
  )?;
  let t = table.clone();
  channels.insert_fixed::<37, 1>(
    "ixvm.pw.param",
    key(5),
    Type::Field,
    move |k| Ok([field.from_u64(t.param(&k.map(|w| field.to_u64(w)))?)]),
  )?;
  channels.insert_fixed::<36, 1>(
    "ixvm.pw.share",
    key(4),
    Type::Field,
    move |k| Ok([field.from_u64(table.share(&k.map(|w| field.to_u64(w)))?)]),
  )?;
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use aiur::library::io::Stream;

  fn key(ordinal: u64) -> [u64; 36] {
    let mut k = [0u64; 36];
    for (i, byte) in k.iter_mut().take(32).enumerate() {
      *byte = i as u64;
    }
    k[32] = 1; // a sharing entry
    k[33] = 3; // entry 3
    k[34] = 1; // variant 1
    k[35] = ordinal;
    k
  }

  fn table() -> Table {
    let rec: Vec<u64> = (0..32).collect();
    // one block: entry (1, 3) variant 1, nodes: never, share 2,
    // ifAllZero [4, 7], ifAllZero []
    let values = vec![1, 1, 3, 1, 4, 0, 1, 2, 4, 4, 7, 2];
    let streams = Streams(vec![
      Stream { channel: STREAM_CHANNEL, key: rec, values },
      Stream { channel: 2, key: vec![9; 32], values: vec![1, 2, 3] },
    ]);
    Table::from_streams(&streams).unwrap()
  }

  #[test]
  fn lookups() {
    let t = table();
    assert_eq!(t.pw(&key(0)), Ok(0));
    assert_eq!(t.share(&key(1)), Ok(2));
    assert_eq!(t.pw(&key(2)), Ok(3));
    let mut p = [0u64; 37];
    p[..36].copy_from_slice(&key(2));
    assert_eq!(t.param(&p), Ok(4));
    p[36] = 1;
    assert_eq!(t.param(&p), Ok(7));
    assert_eq!(t.pw(&key(3)), Ok(1));
  }

  #[test]
  fn missing_keys_are_named() {
    let t = table();
    let e = t.pw(&key(4)).unwrap_err();
    assert!(e.starts_with("missing hint data: ixvm.pw at record 000102"), "{e}");
    assert!(e.ends_with("entry (1, 3), variant 1, ordinal 4"), "{e}");
    let mut other = key(0);
    other[34] = 0;
    assert!(t.pw(&other).unwrap_err().starts_with("missing hint data"));
    // a datum of the wrong kind is a host error too
    assert!(t.pw(&key(1)).unwrap_err().contains("a share site"));
    assert!(t.share(&key(0)).unwrap_err().contains("a binder"));
    let mut p = [0u64; 37];
    p[..36].copy_from_slice(&key(2));
    p[36] = 2;
    assert!(t.param(&p).unwrap_err().contains("no parameter 2"));
  }

  #[test]
  fn malformed_streams_are_refused() {
    let rec: Vec<u64> = (0..32).collect();
    for values in [vec![1, 1, 3, 1, 2, 0], vec![0, 5], vec![1, 0, 0, 0, 1, 7]]
    {
      let s = Streams(vec![Stream {
        channel: STREAM_CHANNEL,
        key: rec.clone(),
        values,
      }]);
      assert!(Table::from_streams(&s).is_err());
    }
    let s = Streams(vec![Stream {
      channel: STREAM_CHANNEL,
      key: vec![256; 32],
      values: vec![0],
    }]);
    assert!(Table::from_streams(&s).is_err());
  }
}
