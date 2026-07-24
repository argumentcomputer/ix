//! Canonical pretty-printer for the Ixon text format.
//!
//! Deterministic by construction: same AST ⇒ same bytes (LF newlines,
//! two-space indent, [`WIDTH`]-column layout, minimal parentheses).
//! `parse ∘ print` is the identity on the printed text (the roundtrip
//! fixpoint the tests enforce): every spelling choice here — when to
//! parenthesize, when to `«…»`-escape, how `Type`/`Sort` arguments and
//! pinned `Name#hash` references are laid out — exists to reparse to
//! the same tree.

use ix_common::env::{BinderInfo, NameComponent};

use crate::syntax::ast::{
  BinderGroup, BinderName, ConstRef, Decl, DefKw, File, HashRef, ImportDecl,
  PrjKind, QuotKindKw, SName, SortKind, Term, UParam, UnivExpr,
};
use crate::syntax::parse::{is_id_first, is_id_rest, is_reserved};

/// Canonical layout width, in columns. Part of the canonical form:
/// both language implementations must agree on it.
pub const WIDTH: usize = 100;

/// Canonical indent step.
const INDENT: usize = 2;

// ---------------------------------------------------------------------------
// Doc engine (Wadler-style, group-local fitting, iterative rendering)
// ---------------------------------------------------------------------------

/// A layout document. `width` caches the flattened width (`None` when
/// the doc contains a hard newline), so grouping decisions are O(1)
/// and whole-document rendering is O(n).
struct Doc {
  width: Option<usize>,
  kind: DocKind,
}

enum DocKind {
  Text(String),
  Cat(Vec<Doc>),
  /// Space when flat, newline when broken.
  Line,
  /// Always a newline.
  Hard,
  Group(Box<Doc>),
  Nest(usize, Box<Doc>),
}

fn text(s: impl Into<String>) -> Doc {
  let s = s.into();
  Doc { width: Some(s.chars().count()), kind: DocKind::Text(s) }
}

fn cat(ds: Vec<Doc>) -> Doc {
  let width = ds.iter().try_fold(0usize, |acc, d| d.width.map(|w| acc + w));
  Doc { width, kind: DocKind::Cat(ds) }
}

fn line() -> Doc {
  Doc { width: Some(1), kind: DocKind::Line }
}

fn hard() -> Doc {
  Doc { width: None, kind: DocKind::Hard }
}

fn group(d: Doc) -> Doc {
  Doc { width: d.width, kind: DocKind::Group(Box::new(d)) }
}

fn nest(d: Doc) -> Doc {
  Doc { width: d.width, kind: DocKind::Nest(INDENT, Box::new(d)) }
}

#[derive(Clone, Copy, PartialEq)]
enum Mode {
  Flat,
  Break,
}

fn render(doc: &Doc, width: usize) -> String {
  let mut out = String::new();
  let mut col = 0usize;
  let mut stack: Vec<(usize, Mode, &Doc)> = vec![(0, Mode::Break, doc)];
  while let Some((ind, mode, d)) = stack.pop() {
    match &d.kind {
      DocKind::Text(s) => {
        out.push_str(s);
        col += s.chars().count();
      },
      DocKind::Cat(ds) => {
        for child in ds.iter().rev() {
          stack.push((ind, mode, child));
        }
      },
      DocKind::Line => match mode {
        Mode::Flat => {
          out.push(' ');
          col += 1;
        },
        Mode::Break => {
          out.push('\n');
          out.extend(std::iter::repeat_n(' ', ind));
          col = ind;
        },
      },
      DocKind::Hard => {
        out.push('\n');
        out.extend(std::iter::repeat_n(' ', ind));
        col = ind;
      },
      DocKind::Nest(n, child) => stack.push((ind + n, mode, child)),
      DocKind::Group(child) => {
        let flat = match child.width {
          Some(w) => col + w <= width,
          None => false,
        };
        stack.push((ind, if flat { Mode::Flat } else { Mode::Break }, child));
      },
    }
  }
  out
}

// ---------------------------------------------------------------------------
// Lexical spelling
// ---------------------------------------------------------------------------

/// Can `s` print as a bare identifier component?
fn is_bare_component(s: &str) -> bool {
  let mut chars = s.chars();
  let Some(c0) = chars.next() else { return false };
  is_id_first(c0) && chars.all(is_id_rest) && !is_reserved(s)
}

/// Print one name component: bare when possible, `«…»` otherwise.
/// `Num` components print as bare digits (the parser reads bare digit
/// runs in non-leading position as `Num`; `«123»` stays `Str`).
fn component_str(c: &NameComponent) -> String {
  match c {
    NameComponent::Str(s) => {
      if is_bare_component(s) {
        s.clone()
      } else {
        format!("«{s}»")
      }
    },
    NameComponent::Num(n) => n.0.to_string(),
  }
}

fn sname_str(n: &SName) -> String {
  n.parts.iter().map(component_str).collect::<Vec<_>>().join(".")
}

fn hash_str(h: &HashRef) -> String {
  format!("#{}", h.hex)
}

/// Lean-style string escaping.
fn escape_string(s: &str) -> String {
  let mut out = String::with_capacity(s.len() + 2);
  out.push('"');
  for c in s.chars() {
    match c {
      '"' => out.push_str("\\\""),
      '\\' => out.push_str("\\\\"),
      '\n' => out.push_str("\\n"),
      '\t' => out.push_str("\\t"),
      '\r' => out.push_str("\\r"),
      c if (c as u32) < 0x20 || c as u32 == 0x7f => {
        out.push_str(&format!("\\x{:02x}", c as u32));
      },
      c => out.push(c),
    }
  }
  out.push('"');
  out
}

// ---------------------------------------------------------------------------
// Universes
// ---------------------------------------------------------------------------

/// Print a universe variable component; `max`/`imax` are operators in
/// universe positions, so a parameter spelled that way must escape.
fn uvar_str(c: &NameComponent) -> String {
  match c {
    NameComponent::Str(s) if s == "max" || s == "imax" => format!("«{s}»"),
    other => component_str(other),
  }
}

/// `atom_ctx`: the position only admits a universe *atom* (arguments
/// of `max`/`imax`, `Type`/`Sort` arguments) — compounds parenthesize.
fn univ_str(u: &UnivExpr, atom_ctx: bool) -> String {
  match u {
    UnivExpr::Nat(n, _) => n.to_string(),
    UnivExpr::Var(c, _) => uvar_str(c),
    UnivExpr::Add(a, n, _) => {
      // Fold nested `Add`s: the grammar admits a single `+ n`.
      let (base, total) = fold_add(a, *n);
      let s = format!("{} + {}", univ_str(base, false), total);
      if atom_ctx { format!("({s})") } else { s }
    },
    UnivExpr::Max(a, b, _) => {
      let s = format!("max {} {}", univ_str(a, true), univ_str(b, true));
      if atom_ctx { format!("({s})") } else { s }
    },
    UnivExpr::IMax(a, b, _) => {
      let s = format!("imax {} {}", univ_str(a, true), univ_str(b, true));
      if atom_ctx { format!("({s})") } else { s }
    },
  }
}

fn fold_add(u: &UnivExpr, acc: u64) -> (&UnivExpr, u64) {
  match u {
    UnivExpr::Add(inner, n, _) => fold_add(inner, acc + n),
    other => (other, acc),
  }
}

fn cref_str(c: &ConstRef) -> String {
  let mut s = String::new();
  if let Some(n) = &c.name {
    s.push_str(&sname_str(n));
  }
  if let Some(h) = &c.hash {
    s.push_str(&hash_str(h));
  }
  if let Some(ls) = &c.levels {
    s.push_str(".{");
    let parts: Vec<String> = ls.iter().map(|u| univ_str(u, false)).collect();
    s.push_str(&parts.join(", "));
    s.push('}');
  }
  s
}

// ---------------------------------------------------------------------------
// Terms
// ---------------------------------------------------------------------------

/// Precedence: 0 = `fun`/`let` layer, 1 = arrow layer, 2 = "loose
/// atoms" (application spines, `Type u`/`Sort u`, `proj`), 3 = closed
/// atoms. A node prints bare iff its precedence ≥ the context's
/// minimum; `Type`/`Sort` sit at 2 even when argument-less so a spine
/// argument can never be captured as their universe argument.
fn term_prec(t: &Term) -> u8 {
  match t {
    Term::Fun { .. } | Term::Let { .. } => 0,
    Term::Pi { .. } | Term::Arrow { .. } => 1,
    Term::Sort(SortKind::Prop, _)
    | Term::Ref(_)
    | Term::NatLit(..)
    | Term::StrLit(..) => 3,
    Term::App { .. } | Term::Proj { .. } | Term::Sort(..) => 2,
  }
}

fn term_doc(t: &Term, min_prec: u8) -> Doc {
  let d = term_doc_bare(t);
  if term_prec(t) < min_prec { cat(vec![text("("), d, text(")")]) } else { d }
}

fn term_doc_bare(t: &Term) -> Doc {
  match t {
    Term::Ref(c) => text(cref_str(c)),
    Term::Sort(k, _) => match k {
      SortKind::Prop => text("Prop"),
      SortKind::Type(None) => text("Type"),
      SortKind::Type(Some(u)) => text(format!("Type {}", univ_str(u, true))),
      SortKind::Sort(u) => text(format!("Sort {}", univ_str(u, true))),
    },
    Term::NatLit(n, _) => text(n.0.to_string()),
    Term::StrLit(s, _) => text(escape_string(s)),
    Term::App { head, args, .. } => {
      // Flatten nested spines: `(f a) b` prints `f a b`.
      let mut h: &Term = head;
      let mut all: Vec<&Term> = args.iter().collect();
      while let Term::App { head: h2, args: a2, .. } = h {
        let mut front: Vec<&Term> = a2.iter().collect();
        front.extend(all);
        all = front;
        h = h2;
      }
      let mut ds = vec![term_doc(h, 3)];
      for a in all {
        ds.push(line());
        ds.push(term_doc(a, 3));
      }
      group(nest(cat(ds)))
    },
    Term::Fun { binders, body, .. } => {
      let mut ds = vec![text("fun")];
      for b in binders {
        ds.push(text(" "));
        ds.push(binder_doc(b));
      }
      ds.push(text(" =>"));
      ds.push(group(nest(cat(vec![line(), term_doc(body, 0)]))));
      cat(ds)
    },
    Term::Pi { binders, body, .. } => {
      let mut ds = Vec::new();
      for b in binders {
        ds.push(binder_doc(b));
        ds.push(text(" "));
      }
      ds.push(text("→"));
      ds.push(group(nest(cat(vec![line(), term_doc(body, 1)]))));
      cat(ds)
    },
    Term::Arrow { dom, cod, .. } => cat(vec![
      term_doc(dom, 2),
      text(" →"),
      group(nest(cat(vec![line(), term_doc(cod, 1)]))),
    ]),
    Term::Let { non_dep, name, ty, val, body, .. } => {
      let kw = if *non_dep { "have" } else { "let" };
      cat(vec![
        text(format!("{kw} {} : ", binder_name_str(name))),
        term_doc(ty, 0),
        text(" :="),
        group(nest(cat(vec![line(), term_doc(val, 0)]))),
        text(";"),
        hard(),
        term_doc(body, 0),
      ])
    },
    Term::Proj { type_ref, idx, val, .. } => cat(vec![
      text(format!("proj {} {idx} ", cref_str(type_ref))),
      term_doc(val, 3),
    ]),
  }
}

fn binder_name_str(b: &BinderName) -> String {
  match b {
    BinderName::Ident(c, _) => component_str(c),
    BinderName::Anon(_) => "_".to_string(),
  }
}

fn binder_doc(b: &BinderGroup) -> Doc {
  let (open, close) = match b.info {
    BinderInfo::Default => ("(", ")"),
    BinderInfo::Implicit => ("{", "}"),
    BinderInfo::StrictImplicit => ("⦃", "⦄"),
    BinderInfo::InstImplicit => ("[", "]"),
  };
  let mut ds = vec![text(open)];
  if b.names.is_empty() {
    // Unnamed instance binder `[T]`.
    ds.push(term_doc(&b.ty, 0));
  } else {
    let names: Vec<String> = b.names.iter().map(binder_name_str).collect();
    ds.push(text(format!("{} : ", names.join(" "))));
    ds.push(term_doc(&b.ty, 0));
  }
  ds.push(text(close));
  group(cat(ds))
}

// ---------------------------------------------------------------------------
// Declarations
// ---------------------------------------------------------------------------

fn uparams_str(ups: &[UParam]) -> String {
  if ups.is_empty() {
    return String::new();
  }
  let parts: Vec<String> = ups.iter().map(|u| uvar_str(&u.name)).collect();
  format!(".{{{}}}", parts.join(", "))
}

/// `def Foo.{u}` header prefix: keyword, optional name, uparams.
fn head_str(kw: &str, name: &Option<SName>, ups: &[UParam]) -> String {
  let mut s = String::from(kw);
  if let Some(n) = name {
    s.push(' ');
    s.push_str(&sname_str(n));
    s.push_str(&uparams_str(ups));
  } else if !ups.is_empty() {
    s.push(' ');
    s.push_str(&uparams_str(ups));
  }
  s
}

fn sig_doc(head: String, ty: &Term) -> Doc {
  cat(vec![
    text(head),
    text(" :"),
    group(nest(cat(vec![line(), term_doc(ty, 0)]))),
  ])
}

fn decl_doc(d: &Decl) -> Doc {
  match d {
    Decl::Def(x) => {
      let mut kw = String::new();
      if x.mods.unsafe_ {
        kw.push_str("unsafe ");
      }
      if x.mods.partial_ {
        kw.push_str("partial ");
      }
      kw.push_str(match x.kw {
        DefKw::Def => "def",
        DefKw::Theorem => "theorem",
        DefKw::Opaque => "opaque",
      });
      cat(vec![
        sig_doc(head_str(&kw, &x.name, &x.uparams), &x.ty),
        text(" :="),
        group(nest(cat(vec![line(), term_doc(&x.value, 0)]))),
      ])
    },
    Decl::Axiom(x) => {
      let kw = if x.unsafe_ { "unsafe axiom" } else { "axiom" };
      sig_doc(head_str(kw, &x.name, &x.uparams), &x.ty)
    },
    Decl::Quot(x) => {
      let kind = match x.kind {
        QuotKindKw::Type => "type",
        QuotKindKw::Ctor => "ctor",
        QuotKindKw::Lift => "lift",
        QuotKindKw::Ind => "ind",
      };
      sig_doc(head_str(&format!("quot {kind}"), &x.name, &x.uparams), &x.ty)
    },
    Decl::Ind(x) => {
      let kw = if x.unsafe_ { "unsafe inductive" } else { "inductive" };
      let head = format!(
        "{} (params := {}) (indices := {})",
        head_str(kw, &x.name, &x.uparams),
        x.params,
        x.indices
      );
      let mut ds = vec![sig_doc(head, &x.ty)];
      if !x.ctors.is_empty() {
        ds.push(text(" where"));
        let mut items = Vec::new();
        for c in &x.ctors {
          items.push(hard());
          let chead = format!(
            "{} (params := {}) (fields := {})",
            head_str("|", &c.name, &[]),
            c.params,
            c.fields
          );
          items.push(sig_doc(chead, &c.ty));
        }
        ds.push(nest(cat(items)));
      }
      cat(ds)
    },
    Decl::Recr(x) => {
      let kw = if x.unsafe_ { "unsafe recursor" } else { "recursor" };
      let mut head = format!(
        "{} (params := {}) (indices := {}) (motives := {}) (minors := {})",
        head_str(kw, &x.name, &x.uparams),
        x.params,
        x.indices,
        x.motives,
        x.minors
      );
      if x.k {
        head.push_str(" (k := true)");
      }
      let mut ds = vec![sig_doc(head, &x.ty)];
      if !x.rules.is_empty() {
        ds.push(text(" where"));
        let mut items = Vec::new();
        for r in &x.rules {
          items.push(hard());
          items.push(cat(vec![
            text(format!("| rule (fields := {}) :=", r.fields)),
            group(nest(cat(vec![line(), term_doc(&r.rhs, 0)]))),
          ]));
        }
        ds.push(nest(cat(items)));
      }
      cat(ds)
    },
    Decl::Mutual(members, _) => {
      let mut items = Vec::new();
      for m in members {
        items.push(hard());
        items.push(decl_doc(m));
      }
      cat(vec![text("mutual"), nest(cat(items)), hard(), text("end")])
    },
    Decl::Prj(x) => {
      let kw = match x.kind {
        PrjKind::DPrj => "dprj",
        PrjKind::IPrj => "iprj",
        PrjKind::CPrj => "cprj",
        PrjKind::RPrj => "rprj",
      };
      let mut s = head_str(kw, &x.name, &[]);
      s.push_str(&format!(" := {} {}", hash_str(&x.block), x.idx));
      if let Some(c) = x.cidx {
        s.push_str(&format!(" {c}"));
      }
      text(s)
    },
  }
}

fn import_str(i: &ImportDecl) -> String {
  match &i.prefix {
    Some(p) => format!("import {}{}", sname_str(p), hash_str(&i.hash)),
    None => format!("import {}", hash_str(&i.hash)),
  }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Print a term (canonical form, no trailing newline).
pub fn print_term(t: &Term) -> String {
  render(&group(term_doc(t, 0)), WIDTH)
}

/// Print one declaration (canonical form, no trailing newline).
pub fn print_decl(d: &Decl) -> String {
  render(&decl_doc(d), WIDTH)
}

/// Print a whole file in canonical form: sections (imports block,
/// declarations, optional trailing main expression) separated by
/// blank lines, trailing newline. The version header is emitted only
/// for versions ≥ 2 — absent means version 1, forever. The main
/// expression's value prints at precedence 2 — `fun`/`let`/arrows
/// parenthesize, so `⊢ (fun (x : A) => x) : A → A` rather than the
/// visually ambiguous bare form (both reparse identically).
pub fn print_file(f: &File) -> String {
  let mut sections: Vec<String> = Vec::new();
  if f.version != 1 {
    sections.push(format!("ixon {}", f.version));
  }
  if !f.imports.is_empty() {
    sections
      .push(f.imports.iter().map(import_str).collect::<Vec<_>>().join("\n"));
  }
  for d in &f.decls {
    sections.push(print_decl(d));
  }
  if let Some(m) = &f.main {
    let doc = cat(vec![
      text("⊢ "),
      term_doc(&m.value, 2),
      text(" :"),
      group(nest(cat(vec![line(), term_doc(&m.ty, 0)]))),
    ]);
    sections.push(render(&doc, WIDTH));
  }
  let mut out = sections.join("\n\n");
  out.push('\n');
  out
}
