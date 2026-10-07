//! The interface of the clique transport and the plan types (a port of
//! `Ix/Compile/Clique/Transport.lean` and `Plan.lean`).

use rustc_hash::FxHashMap;

use ix_common::env::{Expr, Name};

use super::basic::*;
use super::pf::transport_pf;
use super::structural::{proj_chain, transport_structural};
use super::wf::transport_wf;
use crate::compile::pass3::expr::{get_app_fn_args, strip_mdata};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Encoding {
  WellFounded,
  Structural,
  PartialFixpoint,
}

impl Encoding {
  pub fn tag(self) -> &'static str {
    match self {
      Encoding::WellFounded => "well-founded",
      Encoding::Structural => "structural",
      Encoding::PartialFixpoint => "partial_fixpoint",
    }
  }
}

#[derive(Clone, Debug)]
pub enum OrderSource {
  Specification,
  Statements(String),
}

impl OrderSource {
  pub fn tag(&self) -> String {
    match self {
      OrderSource::Specification => "specification".into(),
      OrderSource::Statements(why) => format!("statements ({why})"),
    }
  }
}

pub struct Input<'a> {
  pub encoding: Encoding,
  pub members: Vec<Decl>,
  pub aux: Vec<Decl>,
  pub sigma: Vec<usize>,
  pub new_enc_name: Name,
  pub const_of: ConstOf<'a>,
  pub lemmas: Vec<(Decl, Name)>,
}

pub struct Output {
  pub decls: Vec<Decl>,
  pub renames: Vec<(Name, Name)>,
  pub causes: Vec<(Name, Cause, String)>,
  pub baseline: bool,
}

/// `findPacked?`.
pub fn find_packed(members: &[Decl], aux: &[Decl]) -> Option<Decl> {
  let m = members.first()?;
  let (_, body) = peel_lams(lam_arity(&m.value), &m.value);
  let (h, _) = get_app_fn_args(&strip_mdata(&body));
  let (steps, base) = proj_chain(&h);
  let target: Expr = if steps.is_empty() { body } else { base };
  let (h2, _, _) = const_app(&target)?;
  aux.iter().find(|d| d.name == h2).cloned()
}

fn baseline_of(inp: &Input<'_>, why: &str) -> Output {
  let decls: Vec<Decl> =
    inp.aux.iter().chain(inp.members.iter()).cloned().collect();
  let causes = decls
    .iter()
    .map(|d| (d.name.clone(), Cause::Shape, why.to_string()))
    .collect();
  Output { decls, renames: Vec::new(), causes, baseline: true }
}

/// `transport`.
pub fn transport(inp: &Input<'_>) -> Output {
  if inp.sigma.len() != inp.members.len() || !is_perm(&inp.sigma) {
    return baseline_of(
      inp,
      "transport: bad permutation (expected one distinct position for every member)",
    );
  }
  if inp.sigma.iter().enumerate().all(|(i, &s)| s == i) {
    return Output {
      decls: inp.aux.iter().chain(inp.members.iter()).cloned().collect(),
      renames: Vec::new(),
      causes: Vec::new(),
      baseline: false,
    };
  }
  let causes_of =
    |out: &[super::wf::Transported]| -> Vec<(Name, Cause, String)> {
      out
        .iter()
        .filter_map(|t| {
          t.fallback
            .as_ref()
            .map(|why| (t.decl.name.clone(), Cause::Shape, why.clone()))
        })
        .collect()
    };
  match inp.encoding {
    Encoding::WellFounded => match find_packed(&inp.members, &inp.aux) {
      None => baseline_of(inp, "no packed function"),
      Some(packed) => {
        let proofs: Vec<Decl> =
          inp.aux.iter().filter(|d| d.name != packed.name).cloned().collect();
        let mut tm = Tm::default();
        match transport_wf(
          &mut tm,
          &inp.members,
          &packed,
          &proofs,
          &inp.sigma,
          &inp.new_enc_name,
          &inp.lemmas,
          inp.const_of,
        ) {
          Err(e) => baseline_of(inp, &e),
          Ok(out) => Output {
            causes: causes_of(&out.decls),
            decls: out.decls.into_iter().map(|t| t.decl).collect(),
            renames: out.renames,
            baseline: false,
          },
        }
      },
    },
    Encoding::Structural => {
      let mut tm = Tm::default();
      match transport_structural(
        &mut tm,
        &inp.members,
        &inp.aux,
        &inp.sigma,
        inp.const_of,
        &inp.lemmas,
        false,
      ) {
        Err(e) => baseline_of(inp, &e),
        Ok(out) => Output {
          causes: causes_of(&out),
          decls: out.into_iter().map(|t| t.decl).collect(),
          renames: Vec::new(),
          baseline: false,
        },
      }
    },
    Encoding::PartialFixpoint => match find_packed(&inp.members, &inp.aux) {
      None => baseline_of(inp, "no packed fixpoint"),
      Some(packed) => {
        let proofs: Vec<Decl> =
          inp.aux.iter().filter(|d| d.name != packed.name).cloned().collect();
        let mut tm = Tm::default();
        match transport_pf(
          &mut tm,
          &inp.members,
          &packed,
          &proofs,
          &inp.sigma,
          &inp.new_enc_name,
          inp.const_of,
          &inp.lemmas,
        ) {
          Err(e) => baseline_of(inp, &e),
          Ok(out) => Output {
            causes: causes_of(&out.decls),
            decls: out.decls.into_iter().map(|t| t.decl).collect(),
            renames: out.renames,
            baseline: false,
          },
        }
      },
    },
  }
}

// ---------------------------------------------------------------------------
// Plan
// ---------------------------------------------------------------------------

/// `CliquePlan`.
#[derive(Clone, Debug)]
pub struct CliquePlan {
  pub all: Vec<Name>,
  pub encoding: Encoding,
  pub sigma: Vec<usize>,
  pub classes: Vec<Vec<Name>>,
  pub source: OrderSource,
  pub members: FxHashMap<Name, Decl>,
  pub canon: Vec<(Decl, Name)>,
  pub functionals: Vec<Name>,
  pub causes: Vec<(Name, Cause, String)>,
  pub aliases: Vec<(Name, Name)>,
}

/// `CliqueOutcome`.
#[derive(Clone, Debug)]
pub enum CliqueOutcome {
  NotEncoded(String),
  Unchanged(Encoding, OrderSource),
  Baseline(Encoding, String, String),
  Transported(Box<CliquePlan>),
}

impl CliquePlan {
  /// `CliquePlan.record`: the side-car record `_ix.clique`.
  pub fn record(&self) -> String {
    let causes: Vec<String> = self
      .causes
      .iter()
      .map(|(n, c, why)| format!("{} {}: {}", n.pretty(), c.tag(), why))
      .collect();
    let all: Vec<String> = self.all.iter().map(|n| n.pretty()).collect();
    let classes: Vec<String> = self
      .classes
      .iter()
      .map(|c| arr_str(&c.iter().map(|n| n.pretty()).collect::<Vec<_>>()))
      .collect();
    let aliases: Vec<String> = self
      .aliases
      .iter()
      .map(|(m, r)| format!("{} = {}", m.pretty(), r.pretty()))
      .collect();
    format!(
      "{}; lean order {}; sigma {}; order by {}; classes {}; aliases (O17) {}; causes {}",
      self.encoding.tag(),
      arr_str(&all),
      arr_nat(&self.sigma),
      self.source.tag(),
      arr_str(&classes),
      arr_str(&aliases),
      arr_str(&causes)
    )
  }
}
