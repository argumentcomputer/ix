//! `nom` parser for the Ixon text format.
//!
//! Total, deterministic, metered (R2): every input yields a [`File`]/
//! [`Term`] or a structured [`SyntaxError`]; byte/node/depth caps are
//! parser parameters checked before and during the work they bound.
//! Recursive descent over `&str` with single-token lookahead; the one
//! reinterpretation point is `(x y : A)`-as-binder-group vs.
//! parenthesized term, decided by a bounded committed attempt (each
//! token is scanned at most twice — linear time).
//!
//! Errors ride a custom nom error ([`PErr`]) that keeps the *furthest*
//! failure position and merges expectations there, plus a `special`
//! channel for structured kinds (caps, bad escapes, …) that must not
//! be washed out by backtracking.

use std::cell::Cell;

use bignat::Nat;
use ix_common::env::{BinderInfo, NameComponent};
use nom::{Err as NErr, IResult};
use num_bigint::BigUint;

use crate::syntax::Limits;
use crate::syntax::VERSION;
use crate::syntax::ast::{
  AxiomDecl, BinderGroup, BinderName, ConstRef, CtorDecl, Decl, DefDecl, DefKw,
  File, HashRef, ImportDecl, IndDecl, MainExpr, Modifiers, PrjDecl, PrjKind,
  QuotDecl, QuotKindKw, RecrDecl, RuleDecl, SName, SortKind, Span, Term,
  UParam, UnivExpr, count_file_nodes, count_term_nodes,
};
use crate::syntax::error::{Cap, ErrorKind, SyntaxError};

/// Reserved words: rejected as bare name components everywhere in the
/// grammar (escape as `«def»` if a real name needs one). Contextual
/// words (`params`, `rule`, `max`, `type`, …) are matched positionally
/// and stay usable as names.
pub const RESERVED: &[&str] = &[
  "import",
  "def",
  "theorem",
  "opaque",
  "axiom",
  "quot",
  "inductive",
  "recursor",
  "mutual",
  "end",
  "unsafe",
  "partial",
  "fun",
  "let",
  "have",
  "where",
  "proj",
  "Prop",
  "Type",
  "Sort",
  // Declaration-starting words must be reserved: a preceding
  // declaration's final term would otherwise absorb them as
  // application arguments in multi-decl files.
  "dprj",
  "iprj",
  "cprj",
  "rprj",
];

/// Is `s` a reserved word?
pub fn is_reserved(s: &str) -> bool {
  RESERVED.contains(&s)
}

/// Lean's `isLetterLike` character ranges. Must stay in sync with the
/// Lean lexer (parity-tested; see plans/ixon-syntax.md §1).
pub fn is_letter_like(c: char) -> bool {
  let v = c as u32;
  ((0x3b1..=0x3c9).contains(&v) && v != 0x3bb)                   // greek lower (no λ)
    || ((0x391..=0x3a9).contains(&v) && v != 0x3a0 && v != 0x3a3) // greek upper (no Π Σ)
    || (0x3ca..=0x3fb).contains(&v)                               // accented greek
    || (0x1f00..=0x1ffe).contains(&v)                             // polytonic greek
    || (0x2100..=0x214f).contains(&v)                             // letterlike symbols
    || (0x1d49c..=0x1d59f).contains(&v) // script/fraktur/double-struck
}

/// Lean's `isSubScriptAlnum` ranges.
pub fn is_sub_script(c: char) -> bool {
  let v = c as u32;
  (0x2080..=0x209c).contains(&v)
    || (0x1d62..=0x1d6a).contains(&v)
    || v == 0x2c7c
}

/// First character of an identifier component.
pub fn is_id_first(c: char) -> bool {
  c.is_ascii_alphabetic() || c == '_' || is_letter_like(c)
}

/// Continuation character of an identifier component.
pub fn is_id_rest(c: char) -> bool {
  c.is_ascii_alphanumeric()
    || c == '_'
    || c == '\''
    || c == '!'
    || c == '?'
    || is_sub_script(c)
    || is_letter_like(c)
}

/// Internal parse error: furthest-failure tracking plus a structured
/// override channel. `rem` is the *remaining input length* at the
/// failure (position = `src.len() - rem`), so merging can pick the
/// deeper failure without knowing the source.
#[derive(Debug, Clone)]
pub struct PErr {
  rem: usize,
  expected: Vec<&'static str>,
  special: Option<(ErrorKind, Span)>,
}

impl PErr {
  fn merge(mut self, other: Self) -> Self {
    if self.special.is_some() {
      return self;
    }
    if other.special.is_some() {
      return other;
    }
    match self.rem.cmp(&other.rem) {
      std::cmp::Ordering::Less => self,
      std::cmp::Ordering::Greater => other,
      std::cmp::Ordering::Equal => {
        for e in other.expected {
          if !self.expected.contains(&e) {
            self.expected.push(e);
          }
        }
        self
      },
    }
  }
}

impl<'a> nom::error::ParseError<&'a str> for PErr {
  fn from_error_kind(input: &'a str, _kind: nom::error::ErrorKind) -> Self {
    PErr { rem: input.len(), expected: vec![], special: None }
  }

  fn append(
    _input: &'a str,
    _kind: nom::error::ErrorKind,
    other: Self,
  ) -> Self {
    other
  }

  fn or(self, other: Self) -> Self {
    self.merge(other)
  }
}

type R<'a, T> = IResult<&'a str, T, PErr>;

/// Convert a backtrackable `Error` into a committed `Failure` (nom's
/// `cut`, method-friendly).
fn cut<T>(r: R<'_, T>) -> R<'_, T> {
  r.map_err(|e| match e {
    NErr::Error(x) => NErr::Failure(x),
    o => o,
  })
}

/// RAII depth-guard: decrements on scope exit.
struct Guard<'p>(&'p Cell<usize>);

impl Drop for Guard<'_> {
  fn drop(&mut self) {
    self.0.set(self.0.get() - 1);
  }
}

struct P<'a> {
  src: &'a str,
  limits: &'a Limits,
  depth: Cell<usize>,
}

impl<'a> P<'a> {
  fn off(&self, i: &str) -> usize {
    self.src.len() - i.len()
  }

  /// Span from the start of `from` to the start of `to` (both suffixes
  /// of `src`).
  fn sp(&self, from: &str, to: &str) -> Span {
    Span::new(self.off(from), self.off(to))
  }

  fn fail<T>(&self, i: &'a str, what: &'static str) -> R<'a, T> {
    Err(NErr::Error(PErr { rem: i.len(), expected: vec![what], special: None }))
  }

  fn fatal<T>(&self, kind: ErrorKind, span: Span) -> R<'a, T> {
    Err(NErr::Failure(PErr {
      rem: 0,
      expected: vec![],
      special: Some((kind, span)),
    }))
  }

  fn enter(&self, i: &'a str) -> Result<Guard<'_>, NErr<PErr>> {
    let d = self.depth.get();
    if d >= self.limits.max_depth {
      let p = self.off(i);
      return Err(NErr::Failure(PErr {
        rem: 0,
        expected: vec![],
        special: Some((
          ErrorKind::CapExceeded {
            which: Cap::Depth,
            limit: self.limits.max_depth,
          },
          Span::new(p, p),
        )),
      }));
    }
    self.depth.set(d + 1);
    Ok(Guard(&self.depth))
  }

  /// Skip whitespace, `--` line comments, and nested `/- -/` block
  /// comments. Whitespace is the explicit set `{' ', '\t', '\r',
  /// '\n'}` — NOT the Unicode class, which drifts by Unicode version
  /// and would break cross-language parity (the Lean twin uses the
  /// same list).
  fn ws(&self, mut i: &'a str) -> Result<&'a str, NErr<PErr>> {
    loop {
      i = i.trim_start_matches([' ', '\t', '\r', '\n']);
      if let Some(r) = i.strip_prefix("--") {
        i = match r.find('\n') {
          Some(n) => &r[n + 1..],
          None => "",
        };
      } else if i.starts_with("/-") {
        i = self.block_comment(i)?;
      } else {
        return Ok(i);
      }
    }
  }

  fn block_comment(&self, i0: &'a str) -> Result<&'a str, NErr<PErr>> {
    let open = self.off(i0);
    let mut depth = 0usize;
    let mut i = i0;
    loop {
      if let Some(r) = i.strip_prefix("/-") {
        depth += 1;
        i = r;
      } else if let Some(r) = i.strip_prefix("-/") {
        depth -= 1;
        i = r;
        if depth == 0 {
          return Ok(i);
        }
      } else {
        match i.chars().next() {
          Some(c) => i = &i[c.len_utf8()..],
          None => {
            return Err(NErr::Failure(PErr {
              rem: 0,
              expected: vec![],
              special: Some((
                ErrorKind::UnterminatedComment,
                Span::new(open, open + 2),
              )),
            }));
          },
        }
      }
    }
  }

  /// Lex one identifier component, no whitespace skip.
  fn ident_raw(i: &'a str) -> Option<(&'a str, &'a str)> {
    let mut chars = i.chars();
    let c0 = chars.next()?;
    if !is_id_first(c0) {
      return None;
    }
    let mut end = c0.len_utf8();
    for c in chars {
      if is_id_rest(c) {
        end += c.len_utf8();
      } else {
        break;
      }
    }
    Some((&i[..end], &i[end..]))
  }

  /// Lex one ascii-digit run, no whitespace skip.
  fn digits_raw(i: &'a str) -> Option<(&'a str, &'a str)> {
    let end = i.find(|c: char| !c.is_ascii_digit()).unwrap_or(i.len());
    if end == 0 { None } else { Some((&i[..end], &i[end..])) }
  }

  /// `«…»` quoted name component (any chars except `»`, nonempty).
  fn quoted_component(&self, i: &'a str) -> R<'a, String> {
    let start = i;
    let Some(r) = i.strip_prefix('«') else {
      return self.fail(i, "name");
    };
    match r.find('»') {
      Some(0) => self.fail(i, "nonempty «…» component"),
      Some(n) => {
        let content = r[..n].to_string();
        Ok((&r[n + '»'.len_utf8()..], content))
      },
      None => self.fatal(
        ErrorKind::UnterminatedQuotedName,
        Span::new(self.off(start), self.off(start) + '«'.len_utf8()),
      ),
    }
  }

  /// Keyword or contextual word: a full identifier component equal to
  /// `w`.
  fn kw(&self, i: &'a str, w: &'static str) -> R<'a, Span> {
    let i = self.ws(i)?;
    match Self::ident_raw(i) {
      Some((c, r)) if c == w => Ok((r, self.sp(i, r))),
      _ => self.fail(i, w),
    }
  }

  /// Peek the next identifier word (after ws) without consuming.
  fn peek_word(
    &self,
    i: &'a str,
  ) -> Result<(&'a str, Option<&'a str>), NErr<PErr>> {
    let j = self.ws(i)?;
    Ok((j, Self::ident_raw(j).map(|x| x.0)))
  }

  /// Punctuation token. `":"` deliberately refuses to match the
  /// prefix of `":="`, and `"|"` the prefix of `"|-"` (the ASCII main
  /// expression turnstile) — so ctor/rule bars never absorb it.
  fn sym(&self, i: &'a str, s: &'static str) -> R<'a, Span> {
    let i = self.ws(i)?;
    if s == ":" && i.starts_with(":=") {
      return self.fail(i, ":");
    }
    if s == "|" && i.starts_with("|-") {
      return self.fail(i, "|");
    }
    match i.strip_prefix(s) {
      Some(r) => Ok((r, self.sp(i, r))),
      None => self.fail(i, s),
    }
  }

  /// `⊢` or `|-` — the main expression marker.
  fn turnstile_tok(&self, i: &'a str) -> R<'a, Span> {
    let i = self.ws(i)?;
    if let Some(r) = i.strip_prefix('⊢') {
      return Ok((r, self.sp(i, r)));
    }
    if let Some(r) = i.strip_prefix("|-") {
      return Ok((r, self.sp(i, r)));
    }
    self.fail(i, "⊢")
  }

  /// `→` or `->`.
  fn arrow_tok(&self, i: &'a str) -> R<'a, Span> {
    let i = self.ws(i)?;
    if let Some(r) = i.strip_prefix('→') {
      return Ok((r, self.sp(i, r)));
    }
    if let Some(r) = i.strip_prefix("->") {
      return Ok((r, self.sp(i, r)));
    }
    self.fail(i, "→")
  }

  /// Dotted surface name. Leading component: identifier or `«…»`;
  /// continuations may also be bare digit runs (numeric components).
  /// Stops before `.{` (levels/uparams) and before a reserved
  /// continuation component.
  fn name(&self, i: &'a str) -> R<'a, SName> {
    let i = self.ws(i)?;
    let start = i;
    let (mut rest, first) = if let Some((c, r)) = Self::ident_raw(i) {
      if is_reserved(c) {
        return self.fail(i, "name");
      }
      (r, NameComponent::Str(c.to_string()))
    } else if i.starts_with('«') {
      let (r, s) = self.quoted_component(i)?;
      (r, NameComponent::Str(s))
    } else {
      return self.fail(i, "name");
    };
    let mut parts = vec![first];
    while let Some(r) = rest.strip_prefix('.') {
      if r.starts_with('{') {
        break; // `.{…}` levels
      }
      if let Some((c, r2)) = Self::ident_raw(r) {
        if is_reserved(c) {
          break; // leave `.def` unconsumed; escape as «def»
        }
        parts.push(NameComponent::Str(c.to_string()));
        rest = r2;
      } else if r.starts_with('«') {
        let (r2, s) = self.quoted_component(r)?;
        parts.push(NameComponent::Str(s));
        rest = r2;
      } else if let Some((d, r2)) = Self::digits_raw(r) {
        parts.push(NameComponent::Num(nat_from_decimal(d)));
        rest = r2;
      } else {
        break; // trailing `.` stays unconsumed
      }
    }
    Ok((rest, SName { parts, span: self.sp(start, rest) }))
  }

  /// `#hex` reference, NO leading whitespace skip (callers control
  /// adjacency). 4–64 lowercase hex digits.
  fn hash_raw(&self, i: &'a str) -> R<'a, HashRef> {
    let start = i;
    let Some(r) = i.strip_prefix('#') else {
      return self.fail(i, "#hash");
    };
    let end = r.find(|c: char| !c.is_ascii_hexdigit()).unwrap_or(r.len());
    let run = &r[..end];
    let after = &r[end..];
    let span = self.sp(start, after);
    if let Some(bad) = run.chars().find(|c| c.is_ascii_uppercase()) {
      return self.fatal(
        ErrorKind::InvalidHash {
          reason: format!("uppercase digit '{bad}' (addresses are lowercase)"),
        },
        span,
      );
    }
    if after.chars().next().is_some_and(is_id_rest) {
      return self.fatal(
        ErrorKind::InvalidHash { reason: "invalid character in hash".into() },
        span,
      );
    }
    if run.len() < 4 {
      return self.fatal(
        ErrorKind::InvalidHash {
          reason: format!("too short ({} digits, minimum 4)", run.len()),
        },
        span,
      );
    }
    if run.len() > 64 {
      return self.fatal(
        ErrorKind::InvalidHash {
          reason: format!("too long ({} digits, maximum 64)", run.len()),
        },
        span,
      );
    }
    Ok((after, HashRef { hex: run.to_string(), span }))
  }

  /// Nat literal: decimal, `0x`, `0b`, or `0o`. Arbitrary precision.
  fn natlit(&self, i: &'a str) -> R<'a, (Nat, Span)> {
    let i = self.ws(i)?;
    let start = i;
    let (radix, digits_input) = if let Some(r) = i.strip_prefix("0x") {
      (16u32, r)
    } else if let Some(r) = i.strip_prefix("0b") {
      (2u32, r)
    } else if let Some(r) = i.strip_prefix("0o") {
      (8u32, r)
    } else {
      (10u32, i)
    };
    let end = digits_input
      .find(|c: char| !c.is_digit(radix))
      .unwrap_or(digits_input.len());
    if end == 0 {
      return self.fail(i, "number");
    }
    let run = &digits_input[..end];
    let rest = &digits_input[end..];
    let n = Nat(
      BigUint::parse_bytes(run.as_bytes(), radix)
        .expect("digit run parses in its radix"),
    );
    Ok((rest, (n, self.sp(start, rest))))
  }

  /// Nat literal bounded to `u64` (count annotations, indices, …).
  fn nat_u64(&self, i: &'a str) -> R<'a, (u64, Span)> {
    let (r, (n, span)) = self.natlit(i)?;
    match n.to_u64() {
      Some(v) => Ok((r, (v, span))),
      None => self.fatal(ErrorKind::NatOutOfRange, span),
    }
  }

  /// String literal with Lean escapes.
  fn strlit(&self, i: &'a str) -> R<'a, (String, Span)> {
    let i = self.ws(i)?;
    let start = i;
    let Some(mut r) = i.strip_prefix('"') else {
      return self.fail(i, "string literal");
    };
    let mut out = String::new();
    loop {
      let Some(c) = r.chars().next() else {
        return self.fatal(
          ErrorKind::UnterminatedString,
          Span::new(self.off(start), self.src.len()),
        );
      };
      r = &r[c.len_utf8()..];
      match c {
        '"' => return Ok((r, (out, self.sp(start, r)))),
        '\\' => {
          let esc_start = self.off(r) - 1;
          let Some(e) = r.chars().next() else {
            return self.fatal(
              ErrorKind::InvalidEscape,
              Span::new(esc_start, self.src.len()),
            );
          };
          r = &r[e.len_utf8()..];
          match e {
            'n' => out.push('\n'),
            't' => out.push('\t'),
            'r' => out.push('\r'),
            '\\' => out.push('\\'),
            '"' => out.push('"'),
            '\'' => out.push('\''),
            'x' => match self.hex_escape(r, 2, esc_start) {
              Ok((r2, ch)) => {
                out.push(ch);
                r = r2;
              },
              Err(e) => return Err(e),
            },
            'u' => match self.hex_escape(r, 4, esc_start) {
              Ok((r2, ch)) => {
                out.push(ch);
                r = r2;
              },
              Err(e) => return Err(e),
            },
            _ => {
              return self.fatal(
                ErrorKind::InvalidEscape,
                Span::new(esc_start, self.off(r)),
              );
            },
          }
        },
        c => out.push(c),
      }
    }
  }

  fn hex_escape(
    &self,
    r: &'a str,
    n: usize,
    esc_start: usize,
  ) -> Result<(&'a str, char), NErr<PErr>> {
    // `get` guards both length and char boundaries (a multibyte char
    // right after `\x` must not panic the slicer).
    let valid =
      r.get(..n).is_some_and(|h| h.chars().all(|c| c.is_ascii_hexdigit()));
    if !valid {
      return Err(NErr::Failure(PErr {
        rem: 0,
        expected: vec![],
        special: Some((
          ErrorKind::InvalidEscape,
          Span::new(esc_start, self.off(r)),
        )),
      }));
    }
    let v = u32::from_str_radix(&r[..n], 16).expect("checked hex");
    match char::from_u32(v) {
      Some(c) => Ok((&r[n..], c)),
      None => Err(NErr::Failure(PErr {
        rem: 0,
        expected: vec![],
        special: Some((
          ErrorKind::InvalidEscape,
          Span::new(esc_start, self.off(r) + n),
        )),
      })),
    }
  }

  /// Universe expression: `uatom ("+" nat)?`.
  fn univ(&self, i: &'a str) -> R<'a, UnivExpr> {
    let (i, a) = self.uatom(i)?;
    let j = self.ws(i)?;
    if let Some(r) = j.strip_prefix('+') {
      let (r2, (n, nsp)) = cut(self.nat_u64(r))?;
      let span = a.span().to(nsp);
      Ok((r2, UnivExpr::Add(Box::new(a), n, span)))
    } else {
      Ok((i, a))
    }
  }

  /// Universe atom: literal, var, parens, `max`/`imax` (contextual
  /// operators — a universe parameter literally named `max` needs
  /// `«max»`).
  fn uatom(&self, i: &'a str) -> R<'a, UnivExpr> {
    let _g = self.enter(i)?;
    let i = self.ws(i)?;
    let start = i;
    if i.starts_with(|c: char| c.is_ascii_digit()) {
      let (r, (n, span)) = self.nat_u64(i)?;
      return Ok((r, UnivExpr::Nat(n, span)));
    }
    if let Some(r) = i.strip_prefix('(') {
      let (r, u) = cut(self.univ(r))?;
      let (r, _) = cut(self.sym(r, ")"))?;
      return Ok((r, u));
    }
    if i.starts_with('«') {
      let (r, s) = self.quoted_component(i)?;
      return Ok((r, UnivExpr::Var(NameComponent::Str(s), self.sp(start, r))));
    }
    match Self::ident_raw(i) {
      Some(("max", r)) => {
        let (r, a) = cut(self.uatom(r))?;
        let (r, b) = cut(self.uatom(r))?;
        let span = Span::new(self.off(start), b.span().end);
        Ok((r, UnivExpr::Max(Box::new(a), Box::new(b), span)))
      },
      Some(("imax", r)) => {
        let (r, a) = cut(self.uatom(r))?;
        let (r, b) = cut(self.uatom(r))?;
        let span = Span::new(self.off(start), b.span().end);
        Ok((r, UnivExpr::IMax(Box::new(a), Box::new(b), span)))
      },
      Some((c, r)) if !is_reserved(c) => Ok((
        r,
        UnivExpr::Var(NameComponent::Str(c.to_string()), self.sp(start, r)),
      )),
      _ => self.fail(i, "universe"),
    }
  }

  /// Adjacent `.{u, v}` level list (no whitespace before `.{`).
  fn levels_adj(&self, i: &'a str) -> R<'a, Option<Vec<UnivExpr>>> {
    if !i.starts_with(".{") {
      return Ok((i, None));
    }
    let open = i;
    let r = &i[2..];
    // Empty `.{}` is a structured error.
    let j = self.ws(r)?;
    if let Some(after) = j.strip_prefix('}') {
      return self.fatal(ErrorKind::EmptyLevels, self.sp(open, after));
    }
    let (mut rest, first) = cut(self.univ(r))?;
    let mut levels = vec![first];
    loop {
      let j = self.ws(rest)?;
      if let Some(r2) = j.strip_prefix(',') {
        let (r3, u) = cut(self.univ(r2))?;
        levels.push(u);
        rest = r3;
      } else if let Some(r2) = j.strip_prefix('}') {
        return Ok((r2, Some(levels)));
      } else {
        return cut(self.fail(j, "`,` or `}`"));
      }
    }
  }

  /// Constant reference: `Name`, `#hash`, `Name#hash`, each with
  /// optional adjacent `.{levels}`.
  fn cref(&self, i: &'a str) -> R<'a, ConstRef> {
    let i = self.ws(i)?;
    let start = i;
    if i.starts_with('#') {
      let (r, h) = self.hash_raw(i)?;
      let (r, levels) = self.levels_adj(r)?;
      return Ok((
        r,
        ConstRef { name: None, hash: Some(h), levels, span: self.sp(start, r) },
      ));
    }
    let (r, name) = self.name(i)?;
    let (r, hash) = if r.starts_with('#') {
      let (r2, h) = self.hash_raw(r)?;
      (r2, Some(h))
    } else {
      (r, None)
    };
    let (r, levels) = self.levels_adj(r)?;
    Ok((
      r,
      ConstRef { name: Some(name), hash, levels, span: self.sp(start, r) },
    ))
  }

  /// Greedy optional universe argument for `Type`/`Sort`: a numeral, a
  /// *simple* identifier or `«…»` component (not dotted/hashed — those
  /// start the next application atom instead), or a parenthesized
  /// universe.
  fn uarg_opt(&self, i: &'a str) -> R<'a, Option<UnivExpr>> {
    let j = self.ws(i)?;
    if j.starts_with(|c: char| c.is_ascii_digit()) {
      let (r, (n, span)) = self.nat_u64(j)?;
      return Ok((r, Some(UnivExpr::Nat(n, span))));
    }
    if j.starts_with('«') {
      // The printer's escape for universe variables spelled like
      // operators (`Type «max»`) reparses here.
      let (r, s) = self.quoted_component(j)?;
      if r.starts_with('#') || r.starts_with('.') {
        return Ok((i, None)); // a constant reference, not a uarg
      }
      let span = self.sp(j, r);
      return Ok((r, Some(UnivExpr::Var(NameComponent::Str(s), span))));
    }
    if j.starts_with('(') {
      // Committed attempt: a parse failure inside backtracks to "no
      // argument" (the parens then read as an application argument).
      match (|| -> R<'a, UnivExpr> {
        let r = &j[1..];
        let (r, u) = self.univ(r)?;
        let (r, _) = self.sym(r, ")")?;
        Ok((r, u))
      })() {
        Ok((r, u)) => return Ok((r, Some(u))),
        Err(NErr::Failure(e)) => return Err(NErr::Failure(e)),
        Err(_) => return Ok((i, None)),
      }
    }
    if let Some((c, r)) = Self::ident_raw(j) {
      // A dotted or hash-pinned continuation means this identifier is
      // a constant reference (the next application atom), not a
      // universe variable — including `u.{…}` (levels).
      let simple = !is_reserved(c)
        && c != "max"
        && c != "imax"
        && c != "_"
        && !r.starts_with('#')
        && !r.starts_with('.');
      if simple {
        let span = self.sp(j, r);
        return Ok((
          r,
          Some(UnivExpr::Var(NameComponent::Str(c.to_string()), span)),
        ));
      }
    }
    Ok((i, None))
  }

  /// Application atom.
  fn atom(&self, i: &'a str) -> R<'a, Term> {
    let _g = self.enter(i)?;
    let i = self.ws(i)?;
    let start = i;
    let Some(c0) = i.chars().next() else {
      return self.fail(i, "term");
    };
    match c0 {
      '(' => {
        let r = &i[1..];
        let (r, t) = cut(self.term(r))?;
        let (r, _) = cut(self.sym(r, ")"))?;
        Ok((r, t))
      },
      '"' => {
        let (r, (s, span)) = self.strlit(i)?;
        Ok((r, Term::StrLit(s, span)))
      },
      '#' | '«' => {
        let (r, c) = self.cref(i)?;
        Ok((r, Term::Ref(c)))
      },
      c if c.is_ascii_digit() => {
        let (r, (n, span)) = self.natlit(i)?;
        Ok((r, Term::NatLit(n, span)))
      },
      c if is_id_first(c) => {
        let (word, _) = Self::ident_raw(i).expect("id_first implies ident");
        match word {
          "_" => self.fatal(ErrorKind::Placeholder, self.sp(i, &i[1..])),
          "Prop" => {
            let (r, span) = self.kw(i, "Prop")?;
            Ok((r, Term::Sort(SortKind::Prop, span)))
          },
          "Type" => {
            let (r, ksp) = self.kw(i, "Type")?;
            let (r, u) = self.uarg_opt(r)?;
            let span = u.as_ref().map_or(ksp, |x| ksp.to(x.span()));
            Ok((r, Term::Sort(SortKind::Type(u), span)))
          },
          "Sort" => {
            let (r, ksp) = self.kw(i, "Sort")?;
            let (r, u) = self.uarg_opt(r)?;
            match u {
              Some(u) => {
                let span = ksp.to(u.span());
                Ok((r, Term::Sort(SortKind::Sort(u), span)))
              },
              None => cut(self.fail(r, "universe")),
            }
          },
          "proj" => {
            let (r, ksp) = self.kw(i, "proj")?;
            let (r, type_ref) = cut(self.cref(r))?;
            let (r, (idx, _)) = cut(self.nat_u64(r))?;
            let (r, val) = cut(self.atom(r))?;
            let span = ksp.to(val.span());
            Ok((r, Term::Proj { type_ref, idx, val: Box::new(val), span }))
          },
          w if is_reserved(w) => self.fail(i, "term"),
          _ => {
            let (r, c) = self.cref(i)?;
            Ok((r, Term::Ref(c)))
          },
        }
      },
      _ => self.fail(start, "term"),
    }
  }

  /// Application spine: `atom+`, left-associated, flat.
  fn app(&self, i: &'a str) -> R<'a, Term> {
    let (mut rest, head) = self.atom(i)?;
    let mut args = Vec::new();
    loop {
      match self.atom(rest) {
        Ok((r, t)) => {
          args.push(t);
          rest = r;
        },
        Err(NErr::Failure(e)) => return Err(NErr::Failure(e)),
        Err(_) => break,
      }
    }
    if args.is_empty() {
      Ok((rest, head))
    } else {
      let span = head.span().to(args.last().expect("nonempty").span());
      Ok((rest, Term::App { head: Box::new(head), args, span }))
    }
  }

  /// Binder name: identifier component or `_`.
  fn binder_name(&self, i: &'a str) -> R<'a, BinderName> {
    let i = self.ws(i)?;
    if let Some((c, r)) = Self::ident_raw(i) {
      let span = self.sp(i, r);
      if c == "_" {
        return Ok((r, BinderName::Anon(span)));
      }
      if is_reserved(c) {
        return self.fail(i, "binder name");
      }
      return Ok((
        r,
        BinderName::Ident(NameComponent::Str(c.to_string()), span),
      ));
    }
    if i.starts_with('«') {
      let start = i;
      let (r, s) = self.quoted_component(i)?;
      return Ok((
        r,
        BinderName::Ident(NameComponent::Str(s), self.sp(start, r)),
      ));
    }
    self.fail(i, "binder name")
  }

  /// One bracketed binder group. `(…)` is a *tentative* parse (a
  /// backtrackable failure before the `:` lets callers re-read it as a
  /// parenthesized term); `{…}`, `[…]`, `⦃…⦄` commit immediately —
  /// no term starts with those brackets.
  fn binder_group(&self, i: &'a str) -> R<'a, BinderGroup> {
    let i = self.ws(i)?;
    let start = i;
    let (open, close, info): (char, &'static str, BinderInfo) =
      if i.starts_with('(') {
        ('(', ")", BinderInfo::Default)
      } else if i.starts_with('{') {
        ('{', "}", BinderInfo::Implicit)
      } else if i.starts_with('[') {
        ('[', "]", BinderInfo::InstImplicit)
      } else if i.starts_with('⦃') {
        ('⦃', "⦄", BinderInfo::StrictImplicit)
      } else {
        return self.fail(i, "binder");
      };
    let r = &i[open.len_utf8()..];
    if open == '[' {
      // `[inst : T]` or unnamed `[T]`.
      if let Ok((r2, names)) = self.binder_names_colon(r) {
        let (r3, ty) = cut(self.term(r2))?;
        let (r4, _) = cut(self.sym(r3, close))?;
        return Ok((
          r4,
          BinderGroup { info, names, ty, span: self.sp(start, r4) },
        ));
      }
      let (r2, ty) = cut(self.term(r))?;
      let (r3, _) = cut(self.sym(r2, close))?;
      return Ok((
        r3,
        BinderGroup { info, names: vec![], ty, span: self.sp(start, r3) },
      ));
    }
    let names_colon = self.binder_names_colon(r);
    let (r2, names) = if open == '(' {
      names_colon? // backtrackable: `(f a)` is a term
    } else {
      cut(names_colon)?
    };
    let (r3, ty) = cut(self.term(r2))?;
    let (r4, _) = cut(self.sym(r3, close))?;
    Ok((r4, BinderGroup { info, names, ty, span: self.sp(start, r4) }))
  }

  /// `ident+ :` — the committing prefix of a named binder group.
  fn binder_names_colon(&self, i: &'a str) -> R<'a, Vec<BinderName>> {
    let (mut rest, first) = self.binder_name(i)?;
    let mut names = vec![first];
    loop {
      match self.binder_name(rest) {
        Ok((r, n)) => {
          names.push(n);
          rest = r;
        },
        Err(NErr::Failure(e)) => return Err(NErr::Failure(e)),
        Err(_) => break,
      }
    }
    let (rest, _) = self.sym(rest, ":")?;
    Ok((rest, names))
  }

  /// `fun binder+ => term`.
  fn fun_term(&self, i: &'a str) -> R<'a, Term> {
    let (r, ksp) = self.kw(i, "fun")?;
    let (r, groups) = cut(self.binder_groups1(r))?;
    let (r, _) = cut(self.sym(r, "=>"))?;
    let (r, body) = cut(self.term(r))?;
    let span = ksp.to(body.span());
    Ok((r, Term::Fun { binders: groups, body: Box::new(body), span }))
  }

  fn binder_groups1(&self, i: &'a str) -> R<'a, Vec<BinderGroup>> {
    let (mut rest, first) = self.binder_group(i)?;
    let mut groups = vec![first];
    loop {
      match self.binder_group(rest) {
        Ok((r, g)) => {
          groups.push(g);
          rest = r;
        },
        Err(NErr::Failure(e)) => return Err(NErr::Failure(e)),
        Err(_) => break,
      }
    }
    Ok((rest, groups))
  }

  /// `let x : T := v; b` / `have x : T := v; b`.
  fn let_term(&self, i: &'a str, non_dep: bool) -> R<'a, Term> {
    let word = if non_dep { "have" } else { "let" };
    let (r, ksp) = self.kw(i, word)?;
    let (r, name) = cut(self.binder_name(r))?;
    let (r, _) = cut(self.sym(r, ":"))?;
    let (r, ty) = cut(self.term(r))?;
    let (r, _) = cut(self.sym(r, ":="))?;
    let (r, val) = cut(self.term(r))?;
    let (r, _) = cut(self.sym(r, ";"))?;
    let (r, body) = cut(self.term(r))?;
    let span = ksp.to(body.span());
    Ok((
      r,
      Term::Let {
        non_dep,
        name,
        ty: Box::new(ty),
        val: Box::new(val),
        body: Box::new(body),
        span,
      },
    ))
  }

  /// Dependent domain: `binder+ → term`. Succeeding at the first
  /// binder group commits (a `(x : A)` group not followed by `→` is a
  /// hard error — `(x : A)` alone is not a term).
  fn pi_term(&self, i: &'a str) -> R<'a, Term> {
    let start = self.ws(i)?;
    let (r, first) = self.binder_group(i)?;
    let mut groups = vec![first];
    let mut rest = r;
    loop {
      match self.binder_group(rest) {
        Ok((r, g)) => {
          groups.push(g);
          rest = r;
        },
        Err(NErr::Failure(e)) => return Err(NErr::Failure(e)),
        Err(_) => break,
      }
    }
    let (r, _) = cut(self.arrow_tok(rest))?;
    let (r, body) = cut(self.term(r))?;
    let span = self.sp(start, start).to(body.span());
    Ok((r, Term::Pi { binders: groups, body: Box::new(body), span }))
  }

  /// Arrow layer: dependent domain, or application with optional `→`.
  fn pi_or_arrow(&self, i: &'a str) -> R<'a, Term> {
    let j = self.ws(i)?;
    if j.starts_with('(')
      || j.starts_with('{')
      || j.starts_with('[')
      || j.starts_with('⦃')
    {
      match self.pi_term(j) {
        Ok(v) => return Ok(v),
        Err(NErr::Failure(e)) => return Err(NErr::Failure(e)),
        Err(_) => {},
      }
    }
    let (r, lhs) = self.app(j)?;
    match self.arrow_tok(r) {
      Ok((r2, _)) => {
        let (r3, cod) = cut(self.term(r2))?;
        let span = lhs.span().to(cod.span());
        Ok((r3, Term::Arrow { dom: Box::new(lhs), cod: Box::new(cod), span }))
      },
      Err(NErr::Failure(e)) => Err(NErr::Failure(e)),
      Err(_) => Ok((r, lhs)),
    }
  }

  /// Term entry point.
  fn term(&self, i: &'a str) -> R<'a, Term> {
    let _g = self.enter(i)?;
    let (j, word) = self.peek_word(i)?;
    match word {
      Some("fun") => self.fun_term(j),
      Some("let") => self.let_term(j, false),
      Some("have") => self.let_term(j, true),
      _ => self.pi_or_arrow(j),
    }
  }

  /// `.{u, v}` universe-parameter binders on a declaration.
  fn uparams(&self, i: &'a str) -> R<'a, Vec<UParam>> {
    if !i.starts_with(".{") {
      return Ok((i, vec![]));
    }
    let r = &i[2..];
    let mut out = Vec::new();
    let mut rest = r;
    loop {
      let j = self.ws(rest)?;
      let start = j;
      let (r2, comp) = if let Some((c, r2)) = Self::ident_raw(j) {
        if is_reserved(c) || c == "_" {
          return cut(self.fail(j, "universe parameter"));
        }
        (r2, NameComponent::Str(c.to_string()))
      } else if j.starts_with('«') {
        let (r2, s) = self.quoted_component(j)?;
        (r2, NameComponent::Str(s))
      } else {
        return cut(self.fail(j, "universe parameter"));
      };
      out.push(UParam { name: comp, span: self.sp(start, r2) });
      let j = self.ws(r2)?;
      if let Some(r3) = j.strip_prefix(',') {
        rest = r3;
      } else if let Some(r3) = j.strip_prefix('}') {
        return Ok((r3, out));
      } else {
        return cut(self.fail(j, "`,` or `}`"));
      }
    }
  }

  /// Optional declaration name + optional universe parameters. The
  /// uparams attach adjacently to the name (`Foo.{u}`), or stand alone
  /// after the keyword for anonymous declarations (`def .{u} : …`).
  fn decl_name(&self, i: &'a str) -> R<'a, (Option<SName>, Vec<UParam>)> {
    let j = self.ws(i)?;
    if j.starts_with(".{") {
      let (r, ups) = self.uparams(j)?;
      return Ok((r, (None, ups)));
    }
    if j.starts_with('«')
      || Self::ident_raw(j).is_some_and(|(c, _)| !is_reserved(c))
    {
      let (r, n) = self.name(j)?;
      let (r, ups) = self.uparams(r)?;
      return Ok((r, (Some(n), ups)));
    }
    Ok((j, (None, vec![])))
  }

  /// `(<key> := <nat>)` count annotation.
  fn annot(
    &self,
    i: &'a str,
    key: &'static str,
    label: &'static str,
  ) -> R<'a, u64> {
    let i = self.ws(i)?;
    let Some(r) = i.strip_prefix('(') else {
      return self.fail(i, label);
    };
    let (r, _) = match self.kw(r, key) {
      Ok(v) => v,
      Err(NErr::Failure(e)) => return Err(NErr::Failure(e)),
      Err(_) => return self.fail(i, label),
    };
    let (r, _) = cut(self.sym(r, ":="))?;
    let (r, (v, _)) = cut(self.nat_u64(r))?;
    let (r, _) = cut(self.sym(r, ")"))?;
    Ok((r, v))
  }

  /// Optional `(k := true|false)` on a recursor.
  fn k_annot(&self, i: &'a str) -> R<'a, bool> {
    let j = self.ws(i)?;
    let Some(r) = j.strip_prefix('(') else {
      return Ok((i, false));
    };
    match self.kw(r, "k") {
      Ok((r, _)) => {
        let (r, _) = cut(self.sym(r, ":="))?;
        let (r, word) = self.peek_word(r)?;
        let (r, v) = match word {
          Some("true") => (self.kw(r, "true")?.0, true),
          Some("false") => (self.kw(r, "false")?.0, false),
          _ => return cut(self.fail(r, "true or false")),
        };
        let (r, _) = cut(self.sym(r, ")"))?;
        Ok((r, v))
      },
      Err(NErr::Failure(e)) => Err(NErr::Failure(e)),
      Err(_) => Ok((i, false)),
    }
  }

  fn def_decl(
    &self,
    i: &'a str,
    kw: DefKw,
    kw_word: &'static str,
    mods: Modifiers,
    start: &'a str,
  ) -> R<'a, Decl> {
    let (r, _) = self.kw(i, kw_word)?;
    if mods.partial_ && kw != DefKw::Def {
      return cut(self.fail(start, "def after partial"));
    }
    let (r, (name, uparams)) = cut(self.decl_name(r))?;
    let (r, _) = cut(self.sym(r, ":"))?;
    let (r, ty) = cut(self.term(r))?;
    let (r, _) = cut(self.sym(r, ":="))?;
    let (r, value) = cut(self.term(r))?;
    let span = self.sp(start, r);
    Ok((r, Decl::Def(DefDecl { kw, mods, name, uparams, ty, value, span })))
  }

  fn axiom_decl(
    &self,
    i: &'a str,
    mods: Modifiers,
    start: &'a str,
  ) -> R<'a, Decl> {
    let (r, _) = self.kw(i, "axiom")?;
    if mods.partial_ {
      return cut(self.fail(start, "def after partial"));
    }
    let (r, (name, uparams)) = cut(self.decl_name(r))?;
    let (r, _) = cut(self.sym(r, ":"))?;
    let (r, ty) = cut(self.term(r))?;
    let span = self.sp(start, r);
    Ok((
      r,
      Decl::Axiom(AxiomDecl { unsafe_: mods.unsafe_, name, uparams, ty, span }),
    ))
  }

  fn quot_decl(&self, i: &'a str, start: &'a str) -> R<'a, Decl> {
    let (r, _) = self.kw(i, "quot")?;
    let (r, word) = self.peek_word(r)?;
    let (r, kind) = match word {
      Some("type") => (self.kw(r, "type")?.0, QuotKindKw::Type),
      Some("ctor") => (self.kw(r, "ctor")?.0, QuotKindKw::Ctor),
      Some("lift") => (self.kw(r, "lift")?.0, QuotKindKw::Lift),
      Some("ind") => (self.kw(r, "ind")?.0, QuotKindKw::Ind),
      _ => return cut(self.fail(r, "quotient kind (type|ctor|lift|ind)")),
    };
    let (r, (name, uparams)) = cut(self.decl_name(r))?;
    let (r, _) = cut(self.sym(r, ":"))?;
    let (r, ty) = cut(self.term(r))?;
    let span = self.sp(start, r);
    Ok((r, Decl::Quot(QuotDecl { kind, name, uparams, ty, span })))
  }

  fn ind_decl(
    &self,
    i: &'a str,
    mods: Modifiers,
    start: &'a str,
  ) -> R<'a, Decl> {
    let (r, _) = self.kw(i, "inductive")?;
    if mods.partial_ {
      return cut(self.fail(start, "def after partial"));
    }
    let (r, (name, uparams)) = cut(self.decl_name(r))?;
    let (r, params) = cut(self.annot(r, "params", "(params := _)"))?;
    let (r, indices) = cut(self.annot(r, "indices", "(indices := _)"))?;
    let (r, _) = cut(self.sym(r, ":"))?;
    let (r, ty) = cut(self.term(r))?;
    let (r, ctors) = self.ctor_block(r)?;
    let span = self.sp(start, r);
    Ok((
      r,
      Decl::Ind(IndDecl {
        unsafe_: mods.unsafe_,
        name,
        uparams,
        params,
        indices,
        ty,
        ctors,
        span,
      }),
    ))
  }

  fn ctor_block(&self, i: &'a str) -> R<'a, Vec<CtorDecl>> {
    let (j, word) = self.peek_word(i)?;
    if word != Some("where") {
      return Ok((i, vec![]));
    }
    let (mut rest, _) = self.kw(j, "where")?;
    let mut ctors = Vec::new();
    loop {
      match self.sym(rest, "|") {
        Ok((r, bar_sp)) => {
          let (r, (name, ups)) = cut(self.decl_name(r))?;
          if let Some(up) = ups.first() {
            return self.fatal(
              ErrorKind::UnexpectedToken {
                expected: "(params := _)".into(),
                found: "universe parameters (constructors inherit the \
                        inductive's)"
                  .into(),
              },
              up.span,
            );
          }
          let (r, params) = cut(self.annot(r, "params", "(params := _)"))?;
          let (r, fields) = cut(self.annot(r, "fields", "(fields := _)"))?;
          let (r, _) = cut(self.sym(r, ":"))?;
          let (r, ty) = cut(self.term(r))?;
          ctors.push(CtorDecl {
            name,
            params,
            fields,
            ty,
            span: bar_sp.to(Span::new(self.off(r), self.off(r))),
          });
          rest = r;
        },
        Err(NErr::Failure(e)) => return Err(NErr::Failure(e)),
        Err(_) => break,
      }
    }
    if ctors.is_empty() {
      return cut(self.fail(rest, "|"));
    }
    Ok((rest, ctors))
  }

  fn recr_decl(
    &self,
    i: &'a str,
    mods: Modifiers,
    start: &'a str,
  ) -> R<'a, Decl> {
    let (r, _) = self.kw(i, "recursor")?;
    if mods.partial_ {
      return cut(self.fail(start, "def after partial"));
    }
    let (r, (name, uparams)) = cut(self.decl_name(r))?;
    let (r, params) = cut(self.annot(r, "params", "(params := _)"))?;
    let (r, indices) = cut(self.annot(r, "indices", "(indices := _)"))?;
    let (r, motives) = cut(self.annot(r, "motives", "(motives := _)"))?;
    let (r, minors) = cut(self.annot(r, "minors", "(minors := _)"))?;
    let (r, k) = self.k_annot(r)?;
    let (r, _) = cut(self.sym(r, ":"))?;
    let (r, ty) = cut(self.term(r))?;
    let (r, rules) = self.rule_block(r)?;
    let span = self.sp(start, r);
    Ok((
      r,
      Decl::Recr(RecrDecl {
        unsafe_: mods.unsafe_,
        name,
        uparams,
        params,
        indices,
        motives,
        minors,
        k,
        ty,
        rules,
        span,
      }),
    ))
  }

  fn rule_block(&self, i: &'a str) -> R<'a, Vec<RuleDecl>> {
    let (j, word) = self.peek_word(i)?;
    if word != Some("where") {
      return Ok((i, vec![]));
    }
    let (mut rest, _) = self.kw(j, "where")?;
    let mut rules = Vec::new();
    loop {
      match self.sym(rest, "|") {
        Ok((r, bar_sp)) => {
          let (r, _) = cut(self.kw(r, "rule"))?;
          let (r, fields) = cut(self.annot(r, "fields", "(fields := _)"))?;
          let (r, _) = cut(self.sym(r, ":="))?;
          let (r, rhs) = cut(self.term(r))?;
          rules.push(RuleDecl {
            fields,
            rhs,
            span: bar_sp.to(Span::new(self.off(r), self.off(r))),
          });
          rest = r;
        },
        Err(NErr::Failure(e)) => return Err(NErr::Failure(e)),
        Err(_) => break,
      }
    }
    if rules.is_empty() {
      return cut(self.fail(rest, "|"));
    }
    Ok((rest, rules))
  }

  fn prj_decl(
    &self,
    i: &'a str,
    kind: PrjKind,
    word: &'static str,
    start: &'a str,
  ) -> R<'a, Decl> {
    let (r, _) = self.kw(i, word)?;
    let (r, (name, uparams)) = cut(self.decl_name(r))?;
    if let Some(up) = uparams.first() {
      return self.fatal(
        ErrorKind::UnexpectedToken {
          expected: ":=".into(),
          found: "universe parameters".into(),
        },
        up.span,
      );
    }
    let (r, _) = cut(self.sym(r, ":="))?;
    let r = self.ws(r)?;
    let (r, block) = cut(self.hash_raw(r))?;
    let (r, (idx, _)) = cut(self.nat_u64(r))?;
    let (r, cidx) = if kind == PrjKind::CPrj {
      let (r, (c, _)) = cut(self.nat_u64(r))?;
      (r, Some(c))
    } else {
      (r, None)
    };
    let span = self.sp(start, r);
    Ok((r, Decl::Prj(PrjDecl { kind, name, block, idx, cidx, span })))
  }

  fn mutual_decl(&self, i: &'a str, start: &'a str) -> R<'a, Decl> {
    let (mut rest, _) = self.kw(i, "mutual")?;
    let mut members = Vec::new();
    loop {
      let (j, word) = self.peek_word(rest)?;
      if word == Some("end") {
        let (r, _) = self.kw(j, "end")?;
        if members.is_empty() {
          return cut(self.fail(j, "declaration"));
        }
        return Ok((r, Decl::Mutual(members, self.sp(start, r))));
      }
      let (r, d) = cut(self.decl(rest))?;
      match &d {
        Decl::Def(_) | Decl::Ind(_) | Decl::Recr(_) => members.push(d),
        other => {
          return self.fatal(ErrorKind::BadMutualMember, other.span());
        },
      }
      rest = r;
    }
  }

  /// One declaration.
  fn decl(&self, i: &'a str) -> R<'a, Decl> {
    let start = self.ws(i)?;
    let mut mods = Modifiers::default();
    let mut rest = start;
    loop {
      let (j, word) = self.peek_word(rest)?;
      match word {
        Some("unsafe") if !mods.unsafe_ => {
          mods.unsafe_ = true;
          rest = self.kw(j, "unsafe")?.0;
        },
        Some("partial") if !mods.partial_ => {
          mods.partial_ = true;
          rest = self.kw(j, "partial")?.0;
        },
        _ => break,
      }
    }
    if mods.unsafe_ && mods.partial_ {
      return cut(self.fail(start, "either unsafe or partial (not both)"));
    }
    let (j, word) = self.peek_word(rest)?;
    let has_mods = mods.unsafe_ || mods.partial_;
    match word {
      Some("def") => self.def_decl(j, DefKw::Def, "def", mods, start),
      Some("theorem") => {
        self.def_decl(j, DefKw::Theorem, "theorem", mods, start)
      },
      Some("opaque") => self.def_decl(j, DefKw::Opaque, "opaque", mods, start),
      Some("axiom") => self.axiom_decl(j, mods, start),
      Some("inductive") => self.ind_decl(j, mods, start),
      Some("recursor") => self.recr_decl(j, mods, start),
      Some("quot") if !has_mods => self.quot_decl(j, start),
      Some("mutual") if !has_mods => self.mutual_decl(j, start),
      Some("dprj") if !has_mods => {
        self.prj_decl(j, PrjKind::DPrj, "dprj", start)
      },
      Some("iprj") if !has_mods => {
        self.prj_decl(j, PrjKind::IPrj, "iprj", start)
      },
      Some("cprj") if !has_mods => {
        self.prj_decl(j, PrjKind::CPrj, "cprj", start)
      },
      Some("rprj") if !has_mods => {
        self.prj_decl(j, PrjKind::RPrj, "rprj", start)
      },
      _ => self.fail(j, "declaration"),
    }
  }

  /// `import Foo.Bar#hash` / `import #hash`.
  fn import_decl(&self, i: &'a str) -> R<'a, ImportDecl> {
    let start = self.ws(i)?;
    let (r, _) = self.kw(start, "import")?;
    let j = self.ws(r)?;
    let (r, prefix, hash) = if j.starts_with('#') {
      let (r, h) = cut(self.hash_raw(j))?;
      (r, None, h)
    } else {
      let (r, n) = cut(self.name(j))?;
      if !r.starts_with('#') {
        return cut(self.fail(r, "#hash"));
      }
      let (r, h) = cut(self.hash_raw(r))?;
      (r, Some(n), h)
    };
    if hash.hex.len() != 64 {
      return self.fatal(
        ErrorKind::ImportHashLength { found: hash.hex.len() },
        hash.span,
      );
    }
    Ok((r, ImportDecl { prefix, hash, span: self.sp(start, r) }))
  }

  /// The trailing `⊢ value : type` main expression. The turnstile is
  /// load-bearing: without it, a preceding declaration's final term
  /// absorbs an atom-headed value as an application argument (found
  /// by property testing); the marker is not an atom, so application
  /// spines stop at it. Enforces EOF after the expression — at most
  /// one main, and it must be last.
  fn main_expr(&self, i: &'a str) -> R<'a, MainExpr> {
    let start = self.ws(i)?;
    let (r, _) = self.turnstile_tok(start)?;
    self.main_expr_tail(start, r)
  }

  /// The `value : type` interior — deterministic on its own: no term
  /// production consumes a bare `:`, so the value spine stops at the
  /// annotation. Only the decl→main *boundary* needs the turnstile.
  fn main_expr_tail(&self, start: &'a str, r: &'a str) -> R<'a, MainExpr> {
    let (r, value) = cut(self.term(r))?;
    let (r, _) = cut(self.sym(r, ":"))?;
    let (r, ty) = cut(self.term(r))?;
    let j = self.ws(r)?;
    if !j.is_empty() {
      let p = self.off(j);
      return self.fatal(ErrorKind::MainExprNotLast, Span::new(p, p));
    }
    Ok((j, MainExpr { value, ty, span: self.sp(start, r) }))
  }

  /// Whole file: `ixon <version>` header, imports, declarations,
  /// optional main expression, EOF.
  fn file(&self, i: &'a str) -> R<'a, File> {
    let start = self.ws(i)?;
    // Optional version header: absent means version 1, forever
    // (grammar versions ≥ 2 must declare themselves). A leading
    // `ixon` followed by a numeral is always the header (a constant
    // literally named `ixon` applied to a literal at file start needs
    // parens); followed by anything else it is content.
    let (r, version) = {
      let (_, word) = self.peek_word(start)?;
      if word == Some("ixon") {
        let (after, _) = self.kw(start, "ixon")?;
        let j = self.ws(after)?;
        if j.starts_with(|c: char| c.is_ascii_digit()) {
          let (r, (version, vsp)) = self.nat_u64(after)?;
          if version != VERSION {
            return self.fatal(
              ErrorKind::UnknownVersion { found: version, supported: VERSION },
              vsp,
            );
          }
          (r, version)
        } else {
          (start, VERSION)
        }
      } else {
        (start, VERSION)
      }
    };
    let mut imports = Vec::new();
    let mut rest = r;
    loop {
      let (_, word) = self.peek_word(rest)?;
      if word != Some("import") {
        break;
      }
      let (r, imp) = self.import_decl(rest)?;
      imports.push(imp);
      rest = r;
    }
    let mut decls = Vec::new();
    let mut main = None;
    loop {
      let j = self.ws(rest)?;
      if j.is_empty() {
        rest = j;
        break;
      }
      if j.starts_with('⊢') || j.starts_with("|-") {
        let (r, m) = self.main_expr(j)?;
        main = Some(m);
        rest = r;
        break;
      }
      // Bare `value : type` (no turnstile) is accepted only as the
      // file's SOLE item: with no preceding declaration term there is
      // no boundary to absorb into, and the interior is deterministic.
      // After declarations the turnstile is required (bare form errors
      // on the orphaned `:` — never a silent re-split).
      let (_, word) = self.peek_word(j)?;
      let keyword_item = matches!(
        word,
        Some(
          "def"
            | "theorem"
            | "opaque"
            | "axiom"
            | "inductive"
            | "recursor"
            | "quot"
            | "mutual"
            | "unsafe"
            | "partial"
            | "dprj"
            | "iprj"
            | "cprj"
            | "rprj"
            | "import"
        )
      );
      if !keyword_item && decls.is_empty() {
        let (r, m) = self.main_expr_tail(j, j)?;
        main = Some(m);
        rest = r;
        break;
      }
      let (r, d) = self.decl(j)?;
      decls.push(d);
      rest = r;
    }
    Ok((
      rest,
      File { version, imports, decls, main, span: self.sp(start, rest) },
    ))
  }
}

fn nat_from_decimal(digits: &str) -> Nat {
  Nat(
    BigUint::parse_bytes(digits.as_bytes(), 10)
      .expect("decimal digit run parses"),
  )
}

/// Short description of what sits at `pos`, for `UnexpectedToken`.
fn found_snippet(src: &str, pos: usize) -> String {
  let rest = &src[pos.min(src.len())..];
  let Some(c0) = rest.chars().next() else {
    return "end of input".to_string();
  };
  if is_id_first(c0) || c0.is_ascii_digit() {
    let end = rest
      .find(|c: char| !is_id_rest(c) && !c.is_ascii_digit())
      .unwrap_or(rest.len());
    // Truncate by chars, not bytes — a byte cap could split a
    // multibyte character and panic.
    let word: String = rest[..end].chars().take(24).collect();
    format!("`{word}`")
  } else {
    format!("`{c0}`")
  }
}

fn convert(src: &str, e: NErr<PErr>) -> SyntaxError {
  let pe = match e {
    NErr::Error(x) | NErr::Failure(x) => x,
    NErr::Incomplete(_) => {
      PErr { rem: 0, expected: vec!["more input"], special: None }
    },
  };
  if let Some((kind, span)) = pe.special {
    return SyntaxError::new(kind, span, src);
  }
  let pos = src.len().saturating_sub(pe.rem);
  let expected = if pe.expected.is_empty() {
    "valid syntax".to_string()
  } else {
    pe.expected.join(" or ")
  };
  SyntaxError::new(
    ErrorKind::UnexpectedToken { expected, found: found_snippet(src, pos) },
    Span::new(pos, pos),
    src,
  )
}

fn check_caps_pre(src: &str, limits: &Limits) -> Result<(), SyntaxError> {
  if src.len() > limits.max_bytes {
    return Err(SyntaxError::new(
      ErrorKind::CapExceeded { which: Cap::Bytes, limit: limits.max_bytes },
      Span::new(0, 0),
      src,
    ));
  }
  Ok(())
}

/// Parse a whole `.ixon` file.
pub fn parse_file(src: &str, limits: &Limits) -> Result<File, SyntaxError> {
  check_caps_pre(src, limits)?;
  let p = P { src, limits, depth: Cell::new(0) };
  match p.file(src) {
    Ok((_, f)) => {
      let nodes = count_file_nodes(&f);
      if nodes > limits.max_nodes {
        return Err(SyntaxError::new(
          ErrorKind::CapExceeded { which: Cap::Nodes, limit: limits.max_nodes },
          Span::new(0, 0),
          src,
        ));
      }
      Ok(f)
    },
    Err(e) => Err(convert(src, e)),
  }
}

/// Parse a standalone term (whole input, for tools and tests).
pub fn parse_term(src: &str, limits: &Limits) -> Result<Term, SyntaxError> {
  check_caps_pre(src, limits)?;
  let p = P { src, limits, depth: Cell::new(0) };
  let r = p.term(src).and_then(|(rest, t)| {
    let rest = p.ws(rest)?;
    if rest.is_empty() { Ok((rest, t)) } else { p.fail(rest, "end of input") }
  });
  match r {
    Ok((_, t)) => {
      let nodes = count_term_nodes(&t);
      if nodes > limits.max_nodes {
        return Err(SyntaxError::new(
          ErrorKind::CapExceeded { which: Cap::Nodes, limit: limits.max_nodes },
          Span::new(0, 0),
          src,
        ));
      }
      Ok(t)
    },
    Err(e) => Err(convert(src, e)),
  }
}
