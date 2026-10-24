//! The plan of a changed definition clique, as data, and the side-car record
//! it puts in the canonical functional (a port of
//! `Ix/Compile/Pass/Clique/Plan.lean`).
//!
//! The types are separate from the planner so that the compile environment
//! can carry the per-clique plan table: a clique's plan is computed once, by
//! the first block of its unit that needs it, and read back by the later
//! ones.
//!
//! The side-car record ([`CliquePlan::record`]) holds typed data only: names,
//! numbers and enumeration tags. The free-form reasons (why the specification
//! could not be recovered, why a constant kept Lean's form) stay in the plan
//! for diagnostics and are never part of the record.

use rustc_hash::FxHashMap;

use ix_common::env::Name;

use super::basic::{Cause, Decl, arr_nat, arr_str};

/// The encoding of a definition clique (`Encoding`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Encoding {
  WellFounded,
  Structural,
  PartialFixpoint,
}

impl Encoding {
  /// `Encoding.tag`.
  pub fn tag(self) -> &'static str {
    match self {
      Encoding::WellFounded => "well-founded",
      Encoding::Structural => "structural",
      Encoding::PartialFixpoint => "partial_fixpoint",
    }
  }
}

/// Where a clique's canonical order came from (`OrderSource`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum OrderSource {
  /// Pass 1's classes over (type, normalised specification)
  Specification,
  /// the specification could not be recovered (the reason, for
  /// diagnostics); the statements decide
  Statements(String),
}

impl OrderSource {
  /// `OrderSource.tag`: the source's tag, as the side-car record carries it
  /// (never the recovery error).
  pub fn tag(&self) -> &'static str {
    match self {
      OrderSource::Specification => "specification",
      OrderSource::Statements(_) => "statements",
    }
  }

  /// `OrderSource.describe`: the source for display, the tag with the
  /// recovery error of `statements`.
  pub fn describe(&self) -> String {
    match self {
      OrderSource::Specification => "specification".to_string(),
      OrderSource::Statements(why) => format!("statements ({why})"),
    }
  }
}

impl Decl {
  /// `Decl.same`: exact equality of two declarations: name, universe
  /// parameters, kind, and type and value (Lean compares them by content
  /// hash, which covers binder names and `mdata`, as the compiled bytes and
  /// metadata do; Rust's `==` compares them structurally, hashes included).
  pub fn same(&self, b: &Decl) -> bool {
    self.name == b.name
      && self.level_params == b.level_params
      && self.is_thm == b.is_thm
      && self.typ == b.typ
      && self.value == b.value
  }
}

/// A changed clique's transport, ready for the members' blocks
/// (`CliquePlan`).
#[derive(Clone, Debug)]
pub struct CliquePlan {
  /// Lean's order (`all`)
  pub all: Vec<Name>,
  pub encoding: Encoding,
  pub sigma: Vec<usize>,
  pub classes: Vec<Vec<Name>>,
  pub source: OrderSource,
  /// the transported members, by Lean name
  pub members: FxHashMap<Name, Decl>,
  /// the canonical constants, each with the Lean constant it transports
  pub canon: Vec<(Decl, Name)>,
  /// the canonical functional(s): the side-car record goes on these
  pub functionals: Vec<Name>,
  /// the transport's causes: the constant, the cause, and the reason (for
  /// diagnostics; the record carries the first two only)
  pub causes: Vec<(Name, Cause, String)>,
  /// a member ↦ the representative of its class, whose constant it is (the
  /// aliases of equal members)
  pub aliases: Vec<(Name, Name)>,
}

/// What the hook does with a clique (`CliqueOutcome`).
#[derive(Clone, Debug)]
pub enum CliqueOutcome {
  /// not an encoded clique (compiled as today)
  NotEncoded(String),
  /// the canonical order is Lean's (compiled as today)
  Unchanged(Encoding, OrderSource),
  /// the order is undetermined ([`Cause::NoSpec`]) or the transport kept
  /// Lean's form ([`Cause::Shape`]): compiled as today; the reason is for
  /// diagnostics
  Baseline(Encoding, Cause, String),
  Transported(Box<CliquePlan>),
}

impl CliquePlan {
  /// `CliquePlan.record`: the side-car record of a plan (`_ix.clique`),
  /// typed data only:
  ///
  /// ```text
  /// record  ::= enc "; lean order " names "; sigma " nats "; order by " source
  ///             "; classes " classes "; aliases " aliases "; causes " causes
  /// enc     ::= "well-founded" | "structural" | "partial_fixpoint"   -- Encoding::tag
  /// source  ::= "specification" | "statements"                       -- OrderSource::tag
  /// cause   ::= "SHAPE" | "GUESSLEX" | "NOSPEC"                      -- Cause::tag
  /// names   ::= array(name)          -- Lean's order, `all`
  /// nats    ::= array(nat)           -- σ, decimal
  /// classes ::= array(names)
  /// aliases ::= array(name " = " name)       -- member = representative
  /// causes  ::= array(name " " cause)        -- constant, cause
  /// array(x) ::= "#[" (x (", " x)*)? "]"
  /// ```
  ///
  /// `name` is [`Name::pretty`] (Lean's `Ix.Name.pretty`: components joined
  /// by `.`, no escaping). Example (on one line):
  /// `well-founded; lean order #[f, g]; sigma #[1, 0]; order by
  /// specification; classes #[#[g], #[f]]; aliases #[]; causes
  /// #[g._ix._mutual._proof_1 SHAPE]`.
  pub fn record(&self) -> String {
    let names =
      |xs: &[Name]| arr_str(&xs.iter().map(Name::pretty).collect::<Vec<_>>());
    let classes: Vec<String> = self.classes.iter().map(|c| names(c)).collect();
    let aliases: Vec<String> = self
      .aliases
      .iter()
      .map(|(m, r)| format!("{} = {}", m.pretty(), r.pretty()))
      .collect();
    let causes: Vec<String> = self
      .causes
      .iter()
      .map(|(n, c, _)| format!("{} {}", n.pretty(), c.tag()))
      .collect();
    format!(
      "{}; lean order {}; sigma {}; order by {}; classes {}; aliases {}; \
       causes {}",
      self.encoding.tag(),
      names(&self.all),
      arr_nat(&self.sigma),
      self.source.tag(),
      arr_str(&classes),
      arr_str(&aliases),
      arr_str(&causes)
    )
  }

  /// `CliquePlan.same`: exact equality of two plans (the plan-cache check):
  /// every field, declarations by [`Decl::same`], the member map by key, the
  /// reasons included.
  pub fn same(&self, b: &CliquePlan) -> bool {
    self.all == b.all
      && self.encoding == b.encoding
      && self.sigma == b.sigma
      && self.classes == b.classes
      && self.source == b.source
      && self.functionals == b.functionals
      && self.aliases == b.aliases
      && self.causes == b.causes
      && self.canon.len() == b.canon.len()
      && self
        .canon
        .iter()
        .zip(&b.canon)
        .all(|((d, s), (d2, s2))| d.same(d2) && s == s2)
      && self.members.len() == b.members.len()
      && self
        .members
        .iter()
        .all(|(n, d)| b.members.get(n).is_some_and(|d2| d.same(d2)))
  }
}

impl CliqueOutcome {
  /// `CliqueOutcome.same`: exact equality of two outcomes (the plan-cache
  /// check), the reasons included.
  pub fn same(&self, b: &CliqueOutcome) -> bool {
    match (self, b) {
      (CliqueOutcome::NotEncoded(w), CliqueOutcome::NotEncoded(w2)) => w == w2,
      (CliqueOutcome::Unchanged(e, s), CliqueOutcome::Unchanged(e2, s2)) => {
        e == e2 && s == s2
      },
      (
        CliqueOutcome::Baseline(e, c, w),
        CliqueOutcome::Baseline(e2, c2, w2),
      ) => e == e2 && c == c2 && w == w2,
      (CliqueOutcome::Transported(p), CliqueOutcome::Transported(p2)) => {
        p.same(p2)
      },
      _ => false,
    }
  }

  /// `CliqueOutcome.tag`: a short description of an outcome, for the
  /// check's error (with the reasons).
  pub fn tag(&self) -> String {
    match self {
      CliqueOutcome::NotEncoded(w) => format!("not encoded ({w})"),
      CliqueOutcome::Unchanged(e, s) => {
        format!("unchanged ({}, {})", e.tag(), s.describe())
      },
      CliqueOutcome::Baseline(e, c, w) => {
        format!("baseline {} ({}: {w})", c.tag(), e.tag())
      },
      CliqueOutcome::Transported(p) => format!("transported ({})", p.record()),
    }
  }
}

#[cfg(test)]
mod tests {
  use rustc_hash::FxHashMap;

  use ix_common::env::Name;

  use super::{CliqueOutcome, CliquePlan, Encoding, OrderSource};
  use crate::compile::pass3::clique::basic::{Cause, Decl, dotted, sort0};
  use crate::compile::pass3::expr::nat;

  fn plan() -> CliquePlan {
    let (f, g) = (dotted("f"), dotted("g"));
    CliquePlan {
      all: vec![f.clone(), g.clone()],
      encoding: Encoding::WellFounded,
      sigma: vec![1, 0],
      classes: vec![vec![g.clone()], vec![f.clone()]],
      source: OrderSource::Statements("no specification".into()),
      members: FxHashMap::default(),
      canon: vec![],
      functionals: vec![],
      causes: vec![(
        dotted("g._ix._mutual._proof_1"),
        Cause::Shape,
        "eq_def: PSigma nesting bound exhausted".into(),
      )],
      aliases: vec![],
    }
  }

  #[test]
  fn record_is_the_lean_text() {
    let p = plan();
    assert_eq!(
      p.record(),
      "well-founded; lean order #[f, g]; sigma #[1, 0]; order by \
       statements; classes #[#[g], #[f]]; aliases #[]; causes \
       #[g._ix._mutual._proof_1 SHAPE]"
    );
    // aliases, the other tags, and numeric components (`Ix.Name.pretty`:
    // no escaping)
    let num = Name::num(dotted("f"), nat(2));
    let q = CliquePlan {
      encoding: Encoding::PartialFixpoint,
      source: OrderSource::Specification,
      classes: vec![vec![dotted("f"), num.clone()]],
      aliases: vec![(num.clone(), dotted("f"))],
      causes: vec![
        (dotted("f"), Cause::NoSpec, String::new()),
        (num, Cause::GuessLex, String::new()),
      ],
      sigma: vec![0, 10],
      ..plan()
    };
    assert_eq!(
      q.record(),
      "partial_fixpoint; lean order #[f, g]; sigma #[0, 10]; order by \
       specification; classes #[#[f, f.2]]; aliases #[f.2 = f]; causes \
       #[f NOSPEC, f.2 GUESSLEX]"
    );
    assert_eq!(Encoding::Structural.tag(), "structural");
  }

  #[test]
  fn sources_outcomes_and_equality() {
    let why = OrderSource::Statements("e".into());
    assert_eq!(why.tag(), "statements");
    assert_eq!(why.describe(), "statements (e)");
    assert_eq!(OrderSource::Specification.describe(), "specification");
    let p = plan();
    assert!(p.same(&plan()));
    // the reasons are part of the plan's equality, not of the record
    let mut q = plan();
    q.causes[0].2 = "another reason".into();
    assert_eq!(p.record(), q.record());
    assert!(!p.same(&q));
    let mut q = plan();
    q.source = OrderSource::Statements("other".into());
    assert!(!p.same(&q));
    let d = Decl {
      name: dotted("f"),
      level_params: vec![],
      typ: sort0(),
      value: sort0(),
      is_thm: false,
    };
    let mut q = plan();
    q.members.insert(dotted("f"), d.clone());
    assert!(!p.same(&q));
    let mut r = plan();
    r.members.insert(dotted("f"), Decl { is_thm: true, ..d });
    assert!(!q.same(&r));
    let base =
      CliqueOutcome::Baseline(Encoding::Structural, Cause::Shape, "w".into());
    assert_eq!(base.tag(), "baseline SHAPE (structural: w)");
    assert!(base.same(&base.clone()));
    let unchanged = CliqueOutcome::Unchanged(Encoding::WellFounded, why);
    assert_eq!(unchanged.tag(), "unchanged (well-founded, statements (e))");
    assert!(!unchanged.same(&base));
    assert_eq!(
      CliqueOutcome::NotEncoded("no marker".into()).tag(),
      "not encoded (no marker)"
    );
    let transported = CliqueOutcome::Transported(Box::new(plan()));
    assert_eq!(transported.tag(), format!("transported ({})", plan().record()));
    assert!(transported.same(&CliqueOutcome::Transported(Box::new(plan()))));
  }
}
