//! Hint sites a compiled writer evaluates itself, under
//! [`aiur::trace::describe::WORD_HINT_CONTRACT`]: the word providers of
//! `aiur::library::u32` and `aiur::library::u64`, identified by channel and
//! by the exact key and output types they are registered with. Each
//! implementation mirrors the registered closure, including its errors.
use aiur::{bytecode::Type, trace::describe::HintSite};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum WordHint {
  /// `u32.bytes`: the bytes of the key truncated to 32 bits.
  Bytes,
  /// `u32.sub`: the bytes of the wrapping 32-bit difference.
  Sub,
  /// `u32.add` and `u32.add3`: the bytes of the wrapping sum of `words`
  /// little-endian byte words; a key word above 255 is an error.
  Sum { words: usize },
  /// `u32.lt`: the bytes of `a`, `a - b` and `b`.
  Lt,
  /// `bytes_le`: the eight little-endian bytes of the key.
  BytesLe,
}

fn fields(n: usize) -> Type {
  Type::Tuple { items: vec![Type::Field; n] }
}

impl WordHint {
  /// The contract implementation of `site`, if it has one.
  pub(crate) fn of(site: &HintSite) -> Option<Self> {
    let bytes = fields(4);
    let words = |n: usize| Type::Tuple { items: vec![bytes.clone(); n] };
    let (hint, key, output) = match site.channel.as_str() {
      "u32.bytes" => (Self::Bytes, Type::Field, bytes.clone()),
      "u32.sub" => (Self::Sub, fields(2), bytes.clone()),
      "u32.add" => (Self::Sum { words: 2 }, words(2), bytes.clone()),
      "u32.add3" => (Self::Sum { words: 3 }, words(3), bytes.clone()),
      "u32.lt" => (Self::Lt, fields(2), words(3)),
      "bytes_le" => (Self::BytesLe, Type::Field, fields(8)),
      _ => return None,
    };
    (site.key_type == key && site.r#type == output).then_some(hint)
  }

  pub(crate) fn key_width(self) -> usize {
    match self {
      Self::Bytes | Self::BytesLe => 1,
      Self::Sub | Self::Lt => 2,
      Self::Sum { words } => 4 * words,
    }
  }

  pub(crate) fn output_width(self) -> usize {
    match self {
      Self::Bytes | Self::Sub | Self::Sum { .. } => 4,
      Self::Lt => 12,
      Self::BytesLe => 8,
    }
  }

  /// CUDA statements assigning `out` from `key`; an invalid key runs the
  /// statement `fail`.
  pub(crate) fn emit(
    self,
    key: &[String],
    out: &[String],
    s: &mut String,
    fail: &str,
  ) {
    use std::fmt::Write;
    let bytes = |s: &mut String, word: &str, out: &[String]| {
      for (i, o) in out.iter().enumerate() {
        let _ = writeln!(s, "{o} = (uint64_t)(({word}) >> {}) & 255u;", 8 * i);
      }
    };
    match self {
      Self::Bytes => bytes(s, &format!("(uint32_t)({})", key[0]), out),
      Self::Sub => bytes(
        s,
        &format!("(uint32_t)((uint32_t)({}) - (uint32_t)({}))", key[0], key[1]),
        out,
      ),
      Self::Sum { words } => {
        let _ = writeln!(s, "{{ uint32_t sum = 0u;");
        for w in 0..words {
          let limbs = &key[4 * w..4 * w + 4];
          let _ = writeln!(
            s,
            "if (({}) > 255u || ({}) > 255u || ({}) > 255u || ({}) > 255u) {{ {fail} }}",
            limbs[0], limbs[1], limbs[2], limbs[3]
          );
          let _ = writeln!(
            s,
            "sum += (uint32_t)({}) | ((uint32_t)({}) << 8) | ((uint32_t)({}) << 16) | ((uint32_t)({}) << 24);",
            limbs[0], limbs[1], limbs[2], limbs[3]
          );
        }
        bytes(s, "sum", out);
        s.push_str("}\n");
      },
      Self::Lt => {
        let a = format!("(uint32_t)({})", key[0]);
        let b = format!("(uint32_t)({})", key[1]);
        bytes(s, &a, &out[..4]);
        bytes(s, &format!("(uint32_t)({a} - {b})"), &out[4..8]);
        bytes(s, &b, &out[8..]);
      },
      Self::BytesLe => bytes(s, &key[0], out),
    }
  }
}
