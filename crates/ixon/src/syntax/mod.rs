//! Ixon text format (`.ixon`): parser and canonical pretty-printer.
//!
//! The textual syntax denotes the *named Ix level* — a Lean-resembling
//! closed grammar over `Ix.Expr`-shaped trees — never the pack-level
//! tables (sharing/refs/univs are derived by the one canonical compile
//! pipeline). See `plans/ixon-syntax.md` for the design and
//! requirements (R1–R8).
//!
//! This module is the AST-level layer: text ↔ [`ast`] both ways, with
//! structured errors and metered parsing. The `Constant` ↔ AST stages
//! (resolve/ingress and the metadata-arena printer walk) build on top.
//!
//! Layering:
//! - [`ast`] — the surface AST, spans, node counting
//! - [`parse`] — `nom` parser: `&str → File/Term`
//! - [`print`] — canonical printer: `File/Term → String`
//! - [`error`] — structured, positioned errors (R8)

pub mod ast;
pub mod error;
pub mod parse;
pub mod print;

pub use ast::{Decl, File, Span, Term};
pub use error::{Cap, ErrorKind, SyntaxError};
pub use parse::{parse_file, parse_term};
pub use print::{print_decl, print_file, print_term};

/// Grammar version this implementation speaks (R7). The `ixon <n>`
/// header is optional: absent means version 1, forever; grammar
/// versions ≥ 2 must declare themselves, and canonical version-1
/// output omits the header.
pub const VERSION: u64 = 1;

/// Parser resource caps (R2: gas for admission — parse cost is
/// chargeable up front). Defaults are deliberately generous for
/// interactive use; doors pass their own.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Limits {
  /// Maximum input length in bytes (checked before any work).
  pub max_bytes: usize,
  /// Maximum AST node count (checked after parse; the grammar has no
  /// ε-productions, so `max_bytes` already bounds it — this is the
  /// number downstream stages meter against).
  pub max_nodes: usize,
  /// Maximum nesting depth (checked during descent; guards the stack).
  pub max_depth: usize,
}

impl Default for Limits {
  fn default() -> Self {
    Limits { max_bytes: 1 << 20, max_nodes: 1 << 20, max_depth: 512 }
  }
}

#[cfg(test)]
mod props;

#[cfg(test)]
mod tests {
  use super::*;
  use crate::syntax::error::Cap;

  fn lims() -> Limits {
    Limits::default()
  }

  /// Text-level roundtrip fixpoint: `print (parse (print (parse s)))`
  /// equals `print (parse s)`.
  fn roundtrip_term(src: &str) -> String {
    let t1 = parse_term(src, &lims())
      .unwrap_or_else(|e| panic!("parse failed on {src:?}: {e}"));
    let p1 = print_term(&t1);
    let t2 = parse_term(&p1, &lims())
      .unwrap_or_else(|e| panic!("reparse failed on {p1:?}: {e}"));
    let p2 = print_term(&t2);
    assert_eq!(p1, p2, "printer not a fixpoint for {src:?}");
    p1
  }

  fn roundtrip_file(src: &str) -> String {
    let f1 = parse_file(src, &lims())
      .unwrap_or_else(|e| panic!("parse failed: {e}\n---\n{src}"));
    let p1 = print_file(&f1);
    let f2 = parse_file(&p1, &lims())
      .unwrap_or_else(|e| panic!("reparse failed: {e}\n---\n{p1}"));
    let p2 = print_file(&f2);
    assert_eq!(p1, p2, "printer not a fixpoint");
    assert_eq!(f1.decls.len(), f2.decls.len());
    p1
  }

  #[test]
  fn term_roundtrips() {
    for src in [
      "Nat",
      "Nat.add",
      "Nat.add x y",
      "f (g x) y",
      "(f x) y z",
      "fun (x : Nat) => x",
      "fun (x y : Nat) (z : Bool) => f x z",
      "fun {α : Type u} (a : α) => a",
      "fun [inst : Monad m] => inst",
      "fun ⦃p : Prop⦄ => p",
      "(x : Nat) → Vec x",
      "(x y : Nat) (z : Bool) → f x y z",
      "Nat → Bool",
      "Nat → Bool → Prop",
      "(Nat → Bool) → Prop",
      "let x : Nat := 5; f x",
      "have h : And p q := trivial; h",
      "let f : Nat → Nat := fun (x : Nat) => x; f 3",
      "Prop",
      "Type",
      "Type 1",
      "Type u",
      "Type (max u v)",
      "Sort (u + 1)",
      "Sort (imax u v)",
      "List.{0} Nat",
      "Except.ok.{0, 0} PatchError String s",
      "Nat.add_comm#deadbeef",
      "#deadbeef",
      "#deadbeef.{u} x",
      "proj Prod 0 p",
      "proj #abcd1234 1 (mk x y)",
      "42",
      "0xff",
      "\"hello\"",
      "\"line\\nbreak \\\"quoted\\\"\"",
      "«weird name».foo",
      "Nat.«0».bar",
      "f Nat.0.bar",
      "α.«β»",
      "f _x y'",
      "x!? y",
    ] {
      roundtrip_term(src);
    }
  }

  #[test]
  fn adjacency_is_significant() {
    // `f#abcd` is one pinned reference; `f #abcd` is an application.
    let pinned = parse_term("f#abcd", &lims()).unwrap();
    assert!(matches!(&pinned, Term::Ref(r) if r.hash.is_some()));
    let applied = parse_term("f #abcd", &lims()).unwrap();
    assert!(matches!(&applied, Term::App { args, .. } if args.len() == 1));
    assert_eq!(print_term(&pinned), "f#abcd");
    assert_eq!(print_term(&applied), "f #abcd");
  }

  #[test]
  fn type_argument_is_greedy() {
    // `f Type 1` reads the 1 as Type's universe argument…
    let t = parse_term("f Type 1", &lims()).unwrap();
    let Term::App { args, .. } = &t else { panic!("expected app") };
    assert_eq!(args.len(), 1);
    // …so the printer parenthesizes Sort atoms in argument position.
    assert_eq!(roundtrip_term("f (Type) 1"), "f (Type) 1");
    assert_eq!(roundtrip_term("f Type 1"), "f (Type 1)");
  }

  #[test]
  fn let_vs_have_is_address_relevant() {
    let l = parse_term("let x : N := v; x", &lims()).unwrap();
    let h = parse_term("have x : N := v; x", &lims()).unwrap();
    assert!(matches!(l, Term::Let { non_dep: false, .. }));
    assert!(matches!(h, Term::Let { non_dep: true, .. }));
  }

  #[test]
  fn acceptance_fixture_file() {
    // Hand-formatted input…
    let src = "\
ixon 1
import #9c41aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9c41

def : String → Except PatchError String :=
  fun (s : String) => Except.ok PatchError String s
";
    // …normalizes to the canonical form (no version header — absent
    // means version 1; the def fits in WIDTH columns, so it stays
    // flat).
    let canonical = "\
import #9c41aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9c41

def : String → Except PatchError String := \
fun (s : String) => Except.ok PatchError String s
";
    let printed = roundtrip_file(src);
    assert_eq!(printed, canonical);
  }

  #[test]
  fn kitchen_sink_file() {
    let src = r#"ixon 1

import #aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
import Std.V2#bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb

def id.{u} : (α : Sort u) → α → α := fun (α : Sort u) (a : α) => a

theorem trivial : True := True.intro

unsafe opaque magic : Nat := 0

partial def loop : Nat → Nat := fun (n : Nat) => loop n

axiom choice.{u} : (α : Sort u) → Nonempty α → α

quot type Quot.{u} : (α : Sort u) → (α → α → Prop) → Sort u

inductive Nat' (params := 0) (indices := 0) : Type where
  | zero (params := 0) (fields := 0) : Nat'
  | succ (params := 0) (fields := 1) : Nat' → Nat'

recursor Nat'.rec.{u} (params := 0) (indices := 0) (motives := 1) (minors := 2) :
    (motive : Nat' → Sort u) → motive Nat'.zero →
    ((n : Nat') → motive n → motive (Nat'.succ n)) → (t : Nat') → motive t where
  | rule (fields := 0) := z
  | rule (fields := 1) := fun (n : Nat') (ih : motive n) => s n ih

mutual
def even : Nat → Bool := fun (n : Nat) => odd n
def odd : Nat → Bool := fun (n : Nat) => even n
end

dprj even := #cccccccccccccccccccccccccccccccc 0
cprj Nat'.succ := #dddd 0 1

⊢ even (succ zero) : Bool
"#;
    let f = parse_file(src, &lims()).expect("kitchen sink parses");
    assert!(f.main.is_some());
    roundtrip_file(src);
  }

  #[test]
  fn main_expression() {
    // Minimal main-only file is already canonical (no header).
    assert_eq!(roundtrip_file("⊢ 1 : Nat\n"), "⊢ 1 : Nat\n");
    // An explicit `ixon 1` header is accepted and canonically omitted.
    assert_eq!(roundtrip_file("ixon 1\n⊢ 1 : Nat\n"), "⊢ 1 : Nat\n");
    // The ASCII turnstile normalizes to `⊢`.
    assert_eq!(roundtrip_file("|- 1 : Nat\n"), "⊢ 1 : Nat\n");
    // Low-precedence values parenthesize canonically (both spellings
    // reparse identically) — shared golden with the Lean suite.
    assert_eq!(
      roundtrip_file("⊢ fun (x : Nat) => x : Nat → Nat\n"),
      "⊢ (fun (x : Nat) => x) : Nat → Nat\n"
    );
    // The annotation is mandatory.
    let e = parse_file("⊢ 1\n", &lims()).unwrap_err();
    assert!(matches!(e.kind, ErrorKind::UnexpectedToken { .. }));
    // Bare form (no turnstile) is accepted as the file's SOLE item —
    // the door wire, now ceremony-free — and normalizes to `⊢`.
    assert_eq!(roundtrip_file("1 : Nat\n"), "⊢ 1 : Nat\n");
    assert_eq!(
      roundtrip_file(
        "import \
         #aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n\
         fun (x : Nat) => x : Nat → Nat\n"
      ),
      "import \
       #aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n\n\
       ⊢ (fun (x : Nat) => x) : Nat → Nat\n"
    );
    // Leading `ixon` NOT followed by a numeral is content, not a
    // header (a constant may be named `ixon`).
    assert_eq!(roundtrip_file("ixon : Nat\n"), "⊢ ixon : Nat\n");
    // The fully minimal wire: no header, no imports (resolution uses
    // the application's default env), no turnstile — one judgment.
    assert_eq!(
      roundtrip_file(
        "fun (s : String) => Except.ok PatchError String s : \
         String -> Except PatchError String\n"
      ),
      "⊢ (fun (s : String) => Except.ok PatchError String s) : \
       String → Except PatchError String\n"
    );
    // After a declaration the turnstile is required: the bare form
    // errors (the decl's value absorbs the atom, orphaning the `:`) —
    // never a silent re-split.
    let e =
      parse_file("ixon 1\ndef x : N := v\n1 : Nat\n", &lims()).unwrap_err();
    assert!(matches!(e.kind, ErrorKind::UnexpectedToken { .. }));
    // At most one, and it must be last.
    let e = parse_file("⊢ 1 : Nat ⊢ 2 : Nat\n", &lims()).unwrap_err();
    assert!(matches!(e.kind, ErrorKind::MainExprNotLast));
    let e = parse_file("⊢ 1 : Nat def x : A := b\n", &lims()).unwrap_err();
    assert!(matches!(e.kind, ErrorKind::MainExprNotLast));
  }

  #[test]
  fn main_after_term_final_decl() {
    // Regression (found by quickcheck): the turnstile stops the
    // preceding declaration's application spine — without it, `⊢ Prop`
    // would be absorbed as an argument of the inductive's type.
    let printed = roundtrip_file(
      "ixon 1\ninductive N (params := 0) (indices := 0) : Prop\n\n⊢ Prop : Prop\n",
    );
    let f = parse_file(&printed, &lims()).unwrap();
    assert_eq!(f.decls.len(), 1);
    assert!(f.main.is_some());
    // Same shape after a where-block: `|` in ctor loops must not eat
    // the `|-` spelling.
    roundtrip_file(
      "ixon 1\ninductive N (params := 0) (indices := 0) : Prop where\n  \
       | c (params := 0) (fields := 0) : N\n|- c : N\n",
    );
  }

  #[test]
  fn version_gate() {
    let e = parse_file("ixon 2\n", &lims()).unwrap_err();
    assert!(matches!(
      e.kind,
      ErrorKind::UnknownVersion { found: 2, supported: 1 }
    ));
  }

  #[test]
  fn import_hash_must_be_full() {
    let e = parse_file("ixon 1\nimport #abcd\n", &lims()).unwrap_err();
    assert!(matches!(e.kind, ErrorKind::ImportHashLength { found: 4 }));
  }

  #[test]
  fn error_shapes() {
    // Unexpected token, positioned.
    let e = parse_term("fun (x : Nat) x", &lims()).unwrap_err();
    let ErrorKind::UnexpectedToken { expected, .. } = &e.kind else {
      panic!("expected UnexpectedToken, got {:?}", e.kind)
    };
    assert!(expected.contains("=>"), "expected mentions `=>`: {expected}");

    // Uppercase hash digits are rejected with a reason.
    let e = parse_term("#DEAD", &lims()).unwrap_err();
    assert!(matches!(e.kind, ErrorKind::InvalidHash { .. }));

    // Placeholders are not terms.
    let e = parse_term("f _", &lims()).unwrap_err();
    assert!(matches!(e.kind, ErrorKind::Placeholder));

    // `(x : A)` without an arrow is committed as a binder.
    let e = parse_term("(x : Nat)", &lims()).unwrap_err();
    let ErrorKind::UnexpectedToken { expected, .. } = &e.kind else {
      panic!("expected UnexpectedToken, got {:?}", e.kind)
    };
    assert!(expected.contains('→'), "expected mentions arrow: {expected}");

    // Empty explicit levels.
    let e = parse_term("Nat.{}", &lims()).unwrap_err();
    assert!(matches!(e.kind, ErrorKind::EmptyLevels));

    // Line/col are 1-based and positioned.
    let e = parse_file("ixon 1\ndef x : Nat :=\n", &lims()).unwrap_err();
    assert_eq!(e.line, 3);
  }

  #[test]
  fn depth_cap() {
    let mut limits = lims();
    limits.max_depth = 16;
    let deep = format!("{}x{}", "(".repeat(64), ")".repeat(64));
    let e = parse_term(&deep, &limits).unwrap_err();
    assert!(matches!(e.kind, ErrorKind::CapExceeded { which: Cap::Depth, .. }));
  }

  #[test]
  fn byte_cap() {
    let mut limits = lims();
    limits.max_bytes = 8;
    let e = parse_term("f x y z w", &limits).unwrap_err();
    assert!(matches!(e.kind, ErrorKind::CapExceeded { which: Cap::Bytes, .. }));
  }

  #[test]
  fn comments_and_whitespace() {
    let t =
      parse_term("f -- line comment\n  /- block /- nested -/ -/ x", &lims())
        .unwrap();
    assert_eq!(print_term(&t), "f x");
    let e = parse_term("f /- open", &lims()).unwrap_err();
    assert!(matches!(e.kind, ErrorKind::UnterminatedComment));
  }

  #[test]
  fn reserved_components_escape() {
    // `def` as a component must be escaped; bare it terminates the
    // name.
    let t = parse_term("Nat.«def»", &lims()).unwrap();
    assert_eq!(print_term(&t), "Nat.«def»");
    // «123» stays a Str component, distinct from bare-digit Num.
    let s = parse_term("Foo.«123»", &lims()).unwrap();
    let n = parse_term("Foo.123", &lims()).unwrap();
    assert_eq!(print_term(&s), "Foo.«123»");
    assert_eq!(print_term(&n), "Foo.123");
    assert_ne!(s, n);
  }
}
