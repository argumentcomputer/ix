//! Custom error types for Ixon serialization and compilation.

use crate::ix::address::Address;

/// Errors during serialization/deserialization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SerializeError {
  /// Unexpected end of buffer
  UnexpectedEof { expected: &'static str },
  /// Invalid tag byte
  InvalidTag { tag: u8, context: &'static str },
  /// Invalid flag in tag
  InvalidFlag { flag: u8, context: &'static str },
  /// Invalid variant discriminant
  InvalidVariant { variant: u64, context: &'static str },
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

/// Errors during compilation (Lean → Ixon).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompileError {
  /// Referenced constant not found
  MissingConstant { name: String },
  /// Address not found in store
  MissingAddress(Address),
  /// Invalid mutual block structure
  InvalidMutualBlock { reason: &'static str },
  /// Unsupported expression variant
  UnsupportedExpr { desc: &'static str },
  /// Serialization error during compilation
  Serialize(SerializeError),
}

impl std::fmt::Display for CompileError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::MissingConstant { name } => write!(f, "missing constant: {name}"),
      Self::MissingAddress(addr) => write!(f, "missing address: {addr:?}"),
      Self::InvalidMutualBlock { reason } => {
        write!(f, "invalid mutual block: {reason}")
      },
      Self::UnsupportedExpr { desc } => {
        write!(f, "unsupported expression: {desc}")
      },
      Self::Serialize(e) => write!(f, "serialization error: {e}"),
    }
  }
}

impl std::error::Error for CompileError {
  fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
    match self {
      Self::Serialize(e) => Some(e),
      _ => None,
    }
  }
}

impl From<SerializeError> for CompileError {
  fn from(e: SerializeError) -> Self {
    Self::Serialize(e)
  }
}

/// Errors during decompilation (Ixon → Lean).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecompileError {
  /// Address not found in store
  MissingAddress(Address),
  /// Metadata not found for address
  MissingMetadata(Address),
  /// Invalid Share(idx) reference - sharing vector too small
  InvalidShareIndex { idx: u64, max: usize, constant: String },
  /// Invalid Rec(idx) reference - mutual context doesn't have this index
  InvalidRecIndex { idx: u64, ctx_size: usize, constant: String },
  /// Invalid Ref(idx) reference - refs table too small
  InvalidRefIndex { idx: u64, refs_len: usize, constant: String },
  /// Invalid universe index - univs table too small
  InvalidUnivIndex { idx: u64, univs_len: usize, constant: String },
  /// Invalid Univ::Var(idx) reference - level names too small
  InvalidUnivVarIndex { idx: u64, max: usize, constant: String },
  /// Missing name in metadata
  MissingName { context: &'static str },
  /// Serialization error during decompilation
  Serialize(SerializeError),
}

impl std::fmt::Display for DecompileError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::MissingAddress(addr) => write!(f, "missing address: {addr:?}"),
      Self::MissingMetadata(addr) => {
        write!(f, "missing metadata for: {addr:?}")
      },
      Self::InvalidShareIndex { idx, max, constant } => {
        write!(
          f,
          "invalid Share({idx}) in '{constant}': sharing vector has {max} entries"
        )
      },
      Self::InvalidRecIndex { idx, ctx_size, constant } => {
        write!(
          f,
          "invalid Rec({idx}) in '{constant}': mutual context has {ctx_size} entries"
        )
      },
      Self::InvalidRefIndex { idx, refs_len, constant } => {
        write!(
          f,
          "invalid Ref({idx}) in '{constant}': refs table has {refs_len} entries"
        )
      },
      Self::InvalidUnivIndex { idx, univs_len, constant } => {
        write!(
          f,
          "invalid univ index {idx} in '{constant}': univs table has {univs_len} entries"
        )
      },
      Self::InvalidUnivVarIndex { idx, max, constant } => {
        write!(
          f,
          "invalid Univ::Var({idx}) in '{constant}': only {max} level params"
        )
      },
      Self::MissingName { context } => {
        write!(f, "missing name in metadata: {context}")
      },
      Self::Serialize(e) => write!(f, "serialization error: {e}"),
    }
  }
}

impl std::error::Error for DecompileError {
  fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
    match self {
      Self::Serialize(e) => Some(e),
      _ => None,
    }
  }
}

impl From<SerializeError> for DecompileError {
  fn from(e: SerializeError) -> Self {
    Self::Serialize(e)
  }
}
