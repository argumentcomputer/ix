//! Structured errors for the Ixon text format (R8: errors are data).
//!
//! Every error carries a byte [`Span`]; line/column are derived from
//! the source at construction time (1-based, column counted in
//! Unicode scalar values). The variant set is mirrored by the Lean
//! implementation and is part of the cross-language parity surface.

use crate::syntax::ast::Span;

/// Which parser limit was exceeded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cap {
  Bytes,
  Nodes,
  Depth,
}

/// Structured error kind. Parse-stage variants only; the resolve
/// stage (unknown names, import realization, …) extends this enum
/// later.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ErrorKind {
  /// The workhorse: what the parser wanted vs. what it saw.
  UnexpectedToken { expected: String, found: String },
  /// Header version this parser does not speak.
  UnknownVersion { found: u64, supported: u64 },
  /// A parser limit was hit (R2 metering).
  CapExceeded { which: Cap, limit: usize },
  /// Malformed `#hex` reference (bad char, bad length, uppercase).
  InvalidHash { reason: String },
  /// Import hashes must be exactly 64 hex digits.
  ImportHashLength { found: usize },
  /// Malformed string escape.
  InvalidEscape,
  /// Unterminated string literal.
  UnterminatedString,
  /// Unterminated `«…»` name component.
  UnterminatedQuotedName,
  /// Unterminated `/- … -/` block comment.
  UnterminatedComment,
  /// Numeric literal out of range for its position (e.g. a count
  /// annotation beyond `u64`).
  NatOutOfRange,
  /// `_` used where a term is required (R4: no holes).
  Placeholder,
  /// Explicit `.{}` with no levels.
  EmptyLevels,
  /// A declaration form not permitted here (e.g. `axiom` inside
  /// `mutual`).
  BadMutualMember,
  /// A `⊢ value : type` main expression must be the last item in the
  /// file (and there can be only one).
  MainExprNotLast,
}

/// A positioned, structured syntax error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxError {
  pub kind: ErrorKind,
  pub span: Span,
  /// 1-based line of `span.start`.
  pub line: u32,
  /// 1-based column (in Unicode scalar values) of `span.start`.
  pub col: u32,
}

impl SyntaxError {
  /// Build an error, deriving line/column from `src`.
  pub fn new(kind: ErrorKind, span: Span, src: &str) -> Self {
    let (line, col) = line_col(src, span.start);
    SyntaxError { kind, span, line, col }
  }
}

/// Derive (1-based line, 1-based char column) for a byte offset.
pub fn line_col(src: &str, pos: usize) -> (u32, u32) {
  let pos = pos.min(src.len());
  let mut line = 1u32;
  let mut col = 1u32;
  for (i, c) in src.char_indices() {
    if i >= pos {
      break;
    }
    if c == '\n' {
      line += 1;
      col = 1;
    } else {
      col += 1;
    }
  }
  (line, col)
}

impl std::fmt::Display for SyntaxError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}:{}: ", self.line, self.col)?;
    match &self.kind {
      ErrorKind::UnexpectedToken { expected, found } => {
        write!(f, "expected {expected}, found {found}")
      },
      ErrorKind::UnknownVersion { found, supported } => write!(
        f,
        "unknown ixon version {found} (this parser speaks {supported})"
      ),
      ErrorKind::CapExceeded { which, limit } => {
        let w = match which {
          Cap::Bytes => "byte",
          Cap::Nodes => "node",
          Cap::Depth => "depth",
        };
        write!(f, "{w} limit exceeded (max {limit})")
      },
      ErrorKind::InvalidHash { reason } => {
        write!(f, "invalid #hash reference: {reason}")
      },
      ErrorKind::ImportHashLength { found } => {
        write!(f, "import hashes must be exactly 64 hex digits, found {found}")
      },
      ErrorKind::InvalidEscape => write!(f, "invalid string escape"),
      ErrorKind::UnterminatedString => {
        write!(f, "unterminated string literal")
      },
      ErrorKind::UnterminatedQuotedName => {
        write!(f, "unterminated «…» name component")
      },
      ErrorKind::UnterminatedComment => {
        write!(f, "unterminated block comment")
      },
      ErrorKind::NatOutOfRange => {
        write!(f, "numeric literal out of range for this position")
      },
      ErrorKind::Placeholder => {
        write!(f, "`_` is not a term (the grammar has no holes)")
      },
      ErrorKind::EmptyLevels => {
        write!(f, "`.{{}}` must list at least one universe")
      },
      ErrorKind::BadMutualMember => {
        write!(
          f,
          "only def/theorem/opaque, inductive, and recursor \
                   declarations may appear in a mutual block"
        )
      },
      ErrorKind::MainExprNotLast => {
        write!(
          f,
          "a main expression (`⊢ value : type`) must be the last \
                   item in the file"
        )
      },
    }
  }
}

impl std::error::Error for SyntaxError {}
