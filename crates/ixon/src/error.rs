//! Errors of Ixon serialization and deserialization.

/// Errors during serialization/deserialization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SerializeError {
  /// Unexpected end of buffer
  UnexpectedEof { expected: String },
  /// Invalid tag byte
  InvalidTag { tag: u8, context: String },
  /// Invalid flag in tag
  InvalidFlag { flag: u8, context: String },
  /// Invalid variant discriminant
  InvalidVariant { variant: u64, context: String },
  /// Invalid boolean value
  InvalidBool { value: u8 },
  /// Address parsing error
  AddressError,
  /// Invalid Share index
  InvalidShareIndex { idx: u64, max: usize },
}

impl std::fmt::Display for SerializeError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::UnexpectedEof { expected } => {
        write!(f, "unexpected EOF, expected {expected}")
      },
      Self::InvalidTag { tag, context } => {
        write!(f, "invalid tag 0x{tag:02X} in {context}")
      },
      Self::InvalidFlag { flag, context } => {
        write!(f, "invalid flag {flag} in {context}")
      },
      Self::InvalidVariant { variant, context } => {
        write!(f, "invalid variant {variant} in {context}")
      },
      Self::InvalidBool { value } => write!(f, "invalid bool value {value}"),
      Self::AddressError => write!(f, "address parsing error"),
      Self::InvalidShareIndex { idx, max } => {
        write!(f, "invalid Share index {idx}, max is {max}")
      },
    }
  }
}

impl std::error::Error for SerializeError {}
