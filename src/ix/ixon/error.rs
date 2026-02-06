//! Custom error types for Ixon serialization and compilation.

use crate::ix::address::Address;

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

/// Errors during compilation (Lean → Ixon).
///
/// Variant order matches Lean constructor tags (0–5).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompileError {
  /// Referenced constant not found (tag 0)
  MissingConstant { name: String },
  /// Address not found in store (tag 1)
  MissingAddress(Address),
  /// Invalid mutual block structure (tag 2)
  InvalidMutualBlock { reason: String },
  /// Unsupported expression variant (tag 3)
  UnsupportedExpr { desc: String },
  /// Unknown universe parameter (tag 4)
  UnknownUnivParam { curr: String, param: String },
  /// Serialization error during compilation (tag 5)
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
      Self::UnknownUnivParam { curr, param } => {
        write!(f, "unknown universe parameter: compiling {curr}, param {param}")
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
///
/// Variant order matches Lean constructor tags (0–10).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecompileError {
  /// Invalid Ref(idx) reference - refs table too small (tag 0)
  InvalidRefIndex { idx: u64, refs_len: usize, constant: String },
  /// Invalid universe index - univs table too small (tag 1)
  InvalidUnivIndex { idx: u64, univs_len: usize, constant: String },
  /// Invalid Share(idx) reference - sharing vector too small (tag 2)
  InvalidShareIndex { idx: u64, max: usize, constant: String },
  /// Invalid Rec(idx) reference - mutual context doesn't have this index (tag 3)
  InvalidRecIndex { idx: u64, ctx_size: usize, constant: String },
  /// Invalid Univ::Var(idx) reference - level names too small (tag 4)
  InvalidUnivVarIndex { idx: u64, max: usize, constant: String },
  /// Address not found in store (tag 5)
  MissingAddress(Address),
  /// Metadata not found for address (tag 6)
  MissingMetadata(Address),
  /// Blob not found at address (tag 7)
  BlobNotFound(Address),
  /// Bad blob format at address (tag 8)
  BadBlobFormat { addr: Address, expected: String },
  /// Bad constant format (tag 9)
  BadConstantFormat { msg: String },
  /// Serialization error during decompilation (tag 10)
  Serialize(SerializeError),
}

impl std::fmt::Display for DecompileError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
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
      Self::InvalidUnivVarIndex { idx, max, constant } => {
        write!(
          f,
          "invalid Univ::Var({idx}) in '{constant}': only {max} level params"
        )
      },
      Self::MissingAddress(addr) => write!(f, "missing address: {addr:?}"),
      Self::MissingMetadata(addr) => {
        write!(f, "missing metadata for: {addr:?}")
      },
      Self::BlobNotFound(addr) => write!(f, "blob not found at: {addr:?}"),
      Self::BadBlobFormat { addr, expected } => {
        write!(f, "bad blob format at {addr:?}, expected {expected}")
      },
      Self::BadConstantFormat { msg } => {
        write!(f, "bad constant format: {msg}")
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
