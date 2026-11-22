//! Narrow template layout (`aiur-structural-gap.md` §7.2 S4b; soundness
//! obligations in `docs/aiur-template-backend.md`).
//!
//! - **Lowering.** Products are hash-consed on normalized operands, and a
//!   product used once linearly is fused into that relation. A relation is a
//!   *span* of consecutive lanes summed into one constraint; only a span's
//!   first lane may hold a product, so every constraint has degree 3. Longer
//!   relations chain full-row spans through carry slots.
//! - **Unrolled `Blake3::compress`.** One template holds the stage
//!   bodies of a compression: the stage-0 receive with `stage = 0`, the
//!   stage selector and activity columns fixed per body, and each body's
//!   receive wired to the previous body's self-call payload. Self-calls are
//!   dropped on both sides.
//! - **Messages.** A message whose payload has at most three values occupies
//!   one lane (`[mult, p0, p1, p2]`); larger ones occupy a row
//!   (`[mult, p0..p_{W-2}]`), or keyed chunk rows when wider than a row. Every
//!   multiplicity is `mk + mc·x0` with fixed `mk, mc`, so constant
//!   multiplicities need no cell. A chunked receive's key is the instance's
//!   fixed invocation id. `tag` and `sub` are packed into one coordinate
//!   `ts = tag + 4·sub`.
//! - **Periodic shards.** Every shard holds `⌈cap_f / S⌉` instances of every
//!   function in the same rows, so all shards read one fixed matrix,
//!   committed and opened once. Shard `s` adds the constants `s·ids` to
//!   invocation ids and `s·labels` to copy labels inside its own lookup
//!   expressions.
//! - **Numbering** (the verified layout's, `Periodic*.lean`;
//!   `aiur-template-lean-plan.md` §5e). Copy labels count every logical slot
//!   ([`Template::logical_slots`]): instance `i` of function `f` in a shard
//!   has labels `label_base_f + i·logical_slots_f + slot`, starting at 1, and
//!   shard `s` adds `s·labels_per_shard` (`Sharded.labelOffset`). Every
//!   occupied cell carries its label; cells of a single-occurrence slot have
//!   multiplicity 0. Invocation ids are `id_base_f + i` per shard plus
//!   `s·ids_per_shard` (`Sharded.idOffset`), and map-claim rows continue the
//!   ids after the last chip shard.
//! - **Stacked tables** ([`Stacked`], `Periodic.Stacked`). Beside the shards,
//!   each called map and each ROM width is its own circuit: fixed `sel`,
//!   `key` and (maps) the claim payload, main count and (ROM) words. ROM
//!   addresses are fixed `0..capacity` per width and the words are witness
//!   values, so the key does not depend on the execution's memory.

use super::{
  CALL, CHUNK_STRIDE, CircuitCount, ROM, canonical, count, group_size,
};
use crate::kzg::{KzgConfig, Scalar};
use aiur::{Execution, field::FieldBackend, trace::TracePlan};
use multi_stark::{
  expr::{Expr, RowOffset, Source},
  graph::{ConstraintGraph, Node, NodeId},
  lookup::Lookup,
  system::{CircuitInputs, extension_params},
  traits::{Algebra, Field, PrimeField},
};
use p3_matrix::{Matrix, dense::RowMajorMatrix};
use p3_maybe_rayon::prelude::*;
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::aiur_backend::{Bn254, kzg::Compiler};

pub mod lean;

/// Copy-constraint bus tag. Every tuple's first coordinate is
/// `tag + 4·x` with `tag ∈ {CALL, ROM, COPY}` and `x < 2^62`, so the buses
/// are disjoint.
pub const COPY: u64 = 3;
pub const COMPRESS: &str = "Blake3::compress";

/// Stage bodies of one unrolled `Blake3::compress`, read off its bytecode:
/// `compress(stage, state)` recurses on `stage + 1` until the one branch
/// that tests the `stage` argument (register 0) against a constant `k`, so a
/// compression entered at stage 0 has `k + 1` stages. The count is not
/// trusted: a body count other than the program's leaves the unrolled
/// template unsatisfiable, and the unrolling is checked either way
/// (`Unroll.check`).
pub fn program_compress_stages(
  plan: &TracePlan<'_, Bn254>,
) -> Result<Option<usize>, String> {
  let program = plan.program().program();
  program
    .functions
    .iter()
    .find(|f| f.name == COMPRESS)
    .map(compress_stages)
    .transpose()
}

/// [`program_compress_stages`] of one function.
pub fn compress_stages<W: aiur::field::Word>(
  f: &aiur::bytecode::Function<W>,
) -> Result<usize, String> {
  use aiur::bytecode::Instruction;
  let arms: Vec<&W> = f
    .code
    .iter()
    .filter_map(|i| match i {
      Instruction::Branch { tests, .. } => match tests[..] {
        [(0, ref k)] => Some(k),
        _ => None,
      },
      _ => None,
    })
    .collect();
  let [k] = arms[..] else {
    return Err(format!(
      "{}: expected one branch on the stage argument, found {}",
      f.name,
      arms.len()
    ));
  };
  let k = k.try_to_u64().map_err(|e| format!("{}: final stage: {e}", f.name))?;
  usize::try_from(k)
    .ok()
    .and_then(|k| k.checked_add(1))
    .ok_or_else(|| format!("{}: final stage {k} out of range", f.name))
}

pub type Slot = u32;

/// A lowering-internal index (slot, product, linear form or column) as the
/// `u32` the templates and circuits store.
fn index(i: usize) -> u32 {
  u32::try_from(i).expect("template index exceeds u32")
}

fn ts(tag: u64, sub: u64) -> Scalar {
  Scalar::from_u64(tag) + Scalar::from_u64(4) * Scalar::from_u64(sub)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Atom {
  /// Wide main column `col` of stage body `body`.
  Col(u32, u32),
  /// Product of two interned normalized linear forms.
  Prod(u32),
}

type Lin = Vec<(Atom, Scalar)>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Form {
  terms: Lin,
  k: Scalar,
}

impl Form {
  fn constant(k: Scalar) -> Self {
    Self { terms: vec![], k }
  }

  fn atom(a: Atom, c: Scalar) -> Self {
    Self { terms: vec![(a, c)], k: Scalar::ZERO }
  }

  fn combine(&self, other: &Self, scale: Scalar) -> Self {
    let mut terms = Vec::with_capacity(self.terms.len() + other.terms.len());
    let (mut i, mut j) = (0, 0);
    while i < self.terms.len() || j < other.terms.len() {
      let pick = match (self.terms.get(i), other.terms.get(j)) {
        (Some(a), Some(b)) => a.0.cmp(&b.0),
        (Some(_), None) => std::cmp::Ordering::Less,
        (None, _) => std::cmp::Ordering::Greater,
      };
      match pick {
        std::cmp::Ordering::Less => {
          terms.push(self.terms[i]);
          i += 1;
        },
        std::cmp::Ordering::Greater => {
          let c = other.terms[j].1 * scale;
          if c != Scalar::ZERO {
            terms.push((other.terms[j].0, c));
          }
          j += 1;
        },
        std::cmp::Ordering::Equal => {
          let c = self.terms[i].1 + other.terms[j].1 * scale;
          if c != Scalar::ZERO {
            terms.push((self.terms[i].0, c));
          }
          i += 1;
          j += 1;
        },
      }
    }
    Self { terms, k: self.k + other.k * scale }
  }

  fn scale(&self, c: Scalar) -> Self {
    if c == Scalar::ZERO {
      return Self::constant(Scalar::ZERO);
    }
    Self {
      terms: self.terms.iter().map(|&(a, v)| (a, v * c)).collect(),
      k: self.k * c,
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Term {
  Linear(Scalar, Slot),
  Product(Scalar, Slot, Slot),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SlotDef {
  /// Wide main column of a stage body (body 0 unless unrolled).
  Column {
    body: usize,
    col: usize,
  },
  Sum(Vec<Term>, Scalar),
  /// Callee invocation id or table row of a chunked send: chosen by the
  /// prover and bound only through the keyed chunk messages.
  Key(usize),
}

/// One lane of a gate row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LaneUse {
  Empty,
  /// `qm·x0·x1 + q·x + qc`; `qm` is nonzero only in a span's first lane.
  Gate {
    qm: Scalar,
    q: [Scalar; 4],
    qc: Scalar,
    cells: [Option<Slot>; 4],
  },
  /// Lookup `push(mk + mc·x0, [ts, x1, x2, x3])`.
  Message {
    ts: Scalar,
    mk: Scalar,
    mc: Scalar,
    cells: [Option<Slot>; 4],
  },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Row {
  /// `spans` are `(first lane, lanes)`; each is one constraint.
  Gate { lanes: Vec<LaneUse>, spans: Vec<(usize, usize)> },
  /// Lookup `push(mk + mc·x0, [ts, x1 + key, x2..x_{W−1}])`, where `key` is
  /// the instance's global invocation id on a chunked receive's rows (whose
  /// `x1` is then constrained to zero) and 0 elsewhere.
  Message {
    ts: Scalar,
    mk: Scalar,
    mc: Scalar,
    receive_key: bool,
    cells: Vec<Option<Slot>>,
  },
}

impl Row {
  pub fn cells(&self) -> Vec<Option<Slot>> {
    match self {
      Row::Gate { lanes, .. } => lanes
        .iter()
        .flat_map(|l| match l {
          LaneUse::Empty => [None; 4],
          LaneUse::Gate { cells, .. } | LaneUse::Message { cells, .. } => {
            *cells
          },
        })
        .collect(),
      Row::Message { cells, .. } => cells.clone(),
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Target {
  Receive,
  Call(usize),
  Map(usize),
  Rom(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Placement {
  Lane,
  Row,
  Chunked,
}

#[derive(Clone, Debug)]
pub struct Message {
  pub target: Target,
  /// Multiplicity `mk + mc·mult`.
  pub mk: Scalar,
  pub mc: Scalar,
  pub mult: Option<Slot>,
  /// The original payload after `[tag, id]` (ROM: address first).
  pub payload: Vec<Slot>,
  /// The first payload value when it is a constant (a call's stage
  /// argument, checked for unrolled callees).
  pub first_const: Option<Scalar>,
  pub placement: Placement,
  pub chunks: usize,
  pub key: Option<Slot>,
}

impl Message {
  pub fn multiplicity(&self, v: &[Scalar]) -> Scalar {
    self.mk + self.mult.map_or(Scalar::ZERO, |m| self.mc * v[m as usize])
  }

  /// Whether the verified layout gives this message a virtual multiplicity
  /// slot (`Template2.virtual`).
  pub fn is_virtual(&self) -> bool {
    self.mk != Scalar::ZERO || self.mult.is_none()
  }
}

#[derive(Clone, Debug)]
pub struct Template {
  pub width: usize,
  pub rows: Vec<Row>,
  pub slots: Vec<SlotDef>,
  /// Slots of the verified layout (`Lower2.lean`): `slots`, then one
  /// invocation slot if the receive is chunked, then one virtual slot per
  /// message with a constant or offset multiplicity (`mk ≠ 0` or no cell).
  /// The extra slots hold no cell but take copy labels, so this is the
  /// per-instance label stride.
  pub logical_slots: usize,
  pub occurrences: Vec<u32>,
  pub messages: Vec<Message>,
  pub bodies: usize,
  pub stats: BTreeMap<&'static str, u64>,
}

/// One compiled circuit instance inside a template.
pub struct Body<'g> {
  pub graph: &'g ConstraintGraph<Scalar>,
  /// Columns fixed to constants.
  pub subst: HashMap<u32, Scalar>,
  /// `(col, lookup, arg)`: column `col` equals argument `arg` of the
  /// previous body's lookup `lookup`.
  pub alias: Vec<(u32, usize, usize)>,
  /// Lookups that are not emitted.
  pub drop: HashSet<usize>,
}

#[derive(Clone, Copy, Debug)]
enum Item {
  Product { c: Scalar, a: Slot, b: Slot, ca: Scalar, cb: Scalar },
  Linear { c: Scalar, s: Slot },
}

impl Item {
  fn cells(&self) -> usize {
    match self {
      Self::Product { .. } => 2,
      Self::Linear { .. } => 1,
    }
  }

  fn terms(&self) -> Vec<Term> {
    match *self {
      Self::Product { c, a, b, ca, cb } => {
        let mut t = vec![Term::Product(c, a, b)];
        if ca != Scalar::ZERO {
          t.push(Term::Linear(ca, a));
        }
        if cb != Scalar::ZERO {
          t.push(Term::Linear(cb, b));
        }
        t
      },
      Self::Linear { c, s } => vec![Term::Linear(c, s)],
    }
  }
}

struct GateRowBuild {
  lanes: Vec<LaneUse>,
  spans: Vec<(usize, usize)>,
}

struct Lowerer {
  width: usize,
  lanes: usize,
  functions: usize,
  lins: Vec<Lin>,
  lin_ids: HashMap<Lin, u32>,
  prods: Vec<(u32, u32)>,
  prod_ids: HashMap<(u32, u32), u32>,
  uses_lin: HashMap<Atom, u32>,
  uses_cell: HashMap<Atom, u32>,
  done: HashSet<u32>,
  need_lin: HashSet<u32>,
  need_exact: HashSet<Form>,
  inline: HashSet<u32>,
  slots: Vec<SlotDef>,
  cell_memo: HashMap<Atom, Slot>,
  lin_memo: HashMap<u32, Slot>,
  exact_memo: HashMap<Form, Slot>,
  gate_rows: Vec<GateRowBuild>,
  /// Gate rows with free lanes.
  open: Vec<usize>,
  msg_rows: Vec<Row>,
  messages: Vec<Message>,
  stats: BTreeMap<&'static str, u64>,
}

struct Demand {
  lookup: usize,
  args: Vec<Form>,
  mult: Form,
}

/// Lower one function (one body) or one unrolled function (several bodies)
/// to a template of `width`-cell rows. `functions` is the number of function
/// callables; callables at or above it are fixed maps.
pub fn lower(
  bodies: &[Body<'_>],
  width: usize,
  functions: usize,
) -> Result<Template, String> {
  if width < 8 || !width.is_multiple_of(4) {
    return Err("v2 template width must be a multiple of 4, at least 8".into());
  }
  let mut b = Lowerer {
    width,
    lanes: width / 4,
    functions,
    lins: vec![],
    lin_ids: HashMap::new(),
    prods: vec![],
    prod_ids: HashMap::new(),
    uses_lin: HashMap::new(),
    uses_cell: HashMap::new(),
    done: HashSet::new(),
    need_lin: HashSet::new(),
    need_exact: HashSet::new(),
    inline: HashSet::new(),
    slots: vec![],
    cell_memo: HashMap::new(),
    lin_memo: HashMap::new(),
    exact_memo: HashMap::new(),
    gate_rows: vec![],
    open: vec![],
    msg_rows: vec![],
    messages: vec![],
    stats: BTreeMap::new(),
  };
  let mut zeros = vec![];
  let mut demands: Vec<Demand> = vec![];
  let mut prev: Option<Vec<Form>> = None;
  for (bi, body) in bodies.iter().enumerate() {
    let bi = u32::try_from(bi).map_err(|e| format!("body {bi}: {e}"))?;
    let forms = b.forms(body, bi, prev.as_deref())?;
    for &z in &body.graph.zeros {
      zeros.push(forms[z.index()].clone());
    }
    for (j, l) in body.graph.lookups.iter().enumerate() {
      if body.drop.contains(&j) {
        continue;
      }
      let args: Vec<Form> =
        l.args.iter().map(|a| forms[a.index()].clone()).collect();
      demands.push(Demand {
        lookup: j,
        args,
        mult: forms[l.multiplicity.index()].clone(),
      });
    }
    prev = Some(forms);
  }
  // Identical unchunked lookups merge by adding multiplicities (LogUp is
  // additive in the multiplicity of a tuple).
  let mut merged: Vec<Demand> = vec![];
  let mut seen: HashMap<Vec<Form>, usize> = HashMap::new();
  for d in demands {
    if d.mult.terms.is_empty() && d.mult.k == Scalar::ZERO {
      continue;
    }
    let unchunked = d.args.len() <= width + 1;
    if d.lookup != 0 && unchunked {
      if let Some(&at) = seen.get(&d.args) {
        merged[at].mult = merged[at].mult.combine(&d.mult, Scalar::ONE);
        *b.stats.entry("merged_lookups").or_default() += 1;
        continue;
      }
      seen.insert(d.args.clone(), merged.len());
    }
    merged.push(d);
  }
  for z in &zeros {
    for &(a, _) in &z.terms {
      b.use_atom(a, false);
    }
  }
  for d in &merged {
    if d.mult.terms.len() > 1 {
      b.exact_demand(&d.mult);
    } else if let [(a, _)] = d.mult.terms[..] {
      b.use_atom(a, true);
    }
    for a in &d.args[2..] {
      b.exact_demand(a);
    }
  }
  b.inline = (0..index(b.prods.len()))
    .filter(|p| {
      let a = Atom::Prod(*p);
      matches!(b.uses_lin.get(&a), Some(1)) && !b.uses_cell.contains_key(&a)
    })
    .collect();
  for z in &zeros {
    if z.terms.is_empty() {
      if z.k != Scalar::ZERO {
        return Err("unsatisfiable constant constraint".into());
      }
      continue;
    }
    let items = b.items(&z.terms)?;
    b.relation(items, z.k)?;
  }
  for d in &merged {
    b.message(d)?;
  }
  let mut rows: Vec<Row> = b
    .gate_rows
    .drain(..)
    .map(|r| {
      let mut lanes = r.lanes;
      lanes.resize(b.lanes, LaneUse::Empty);
      Row::Gate { lanes, spans: r.spans }
    })
    .collect();
  let gate_rows = rows.len() as u64;
  rows.append(&mut b.msg_rows);
  let mut occurrences = vec![0u32; b.slots.len()];
  for row in &rows {
    for s in row.cells().into_iter().flatten() {
      occurrences[s as usize] += 1;
    }
  }
  b.stats.insert("gate_rows", gate_rows);
  b.stats.insert("message_rows", rows.len() as u64 - gate_rows);
  b.stats.insert("cells_used", occurrences.iter().map(|&o| u64::from(o)).sum());
  b.stats.insert(
    "copies",
    occurrences.iter().map(|&o| u64::from(o.saturating_sub(1))).sum(),
  );
  b.stats.insert("slots", b.slots.len() as u64);
  let invocation = b
    .messages
    .iter()
    .any(|m| m.target == Target::Receive && m.placement == Placement::Chunked);
  let virtuals = b.messages.iter().filter(|m| m.is_virtual()).count();
  let logical_slots = b.slots.len() + usize::from(invocation) + virtuals;
  Ok(Template {
    width,
    rows,
    logical_slots,
    slots: b.slots,
    occurrences,
    messages: b.messages,
    bodies: bodies.len(),
    stats: b.stats,
  })
}

impl Lowerer {
  fn intern(&mut self, lin: Lin) -> u32 {
    if let Some(&id) = self.lin_ids.get(&lin) {
      return id;
    }
    let id = index(self.lins.len());
    self.lins.push(lin.clone());
    self.lin_ids.insert(lin, id);
    id
  }

  /// `(α, β, g)` with `form = α·g + β` and `g`'s first coefficient 1.
  fn norm(&mut self, f: &Form) -> (Scalar, Scalar, u32) {
    let al = f.terms[0].1;
    let ia = al.inverse();
    let g: Lin = f.terms.iter().map(|&(a, c)| (a, c * ia)).collect();
    (al, f.k, self.intern(g))
  }

  fn lin_form(&self, id: u32) -> Form {
    Form { terms: self.lins[id as usize].clone(), k: Scalar::ZERO }
  }

  fn mul(&mut self, a: &Form, b: &Form) -> Form {
    if a.terms.is_empty() {
      return b.scale(a.k);
    }
    if b.terms.is_empty() {
      return a.scale(b.k);
    }
    let (al, be, ga) = self.norm(a);
    let (gm, de, gb) = self.norm(b);
    let key = (ga.min(gb), ga.max(gb));
    let p = match self.prod_ids.get(&key) {
      Some(&p) => p,
      None => {
        let p = index(self.prods.len());
        self.prods.push(key);
        self.prod_ids.insert(key, p);
        p
      },
    };
    let mut f = Form::atom(Atom::Prod(p), al * gm);
    f = f.combine(&self.lin_form(ga), al * de);
    f = f.combine(&self.lin_form(gb), be * gm);
    f.k += be * de;
    f
  }

  fn forms(
    &mut self,
    body: &Body<'_>,
    bi: u32,
    prev: Option<&[Form]>,
  ) -> Result<Vec<Form>, String> {
    let g = body.graph;
    let alias: HashMap<u32, (usize, usize)> =
      body.alias.iter().map(|&(c, l, a)| (c, (l, a))).collect();
    let mut forms: Vec<Form> = Vec::with_capacity(g.nodes.len());
    for node in &g.nodes {
      let f = match *node {
        Node::Const(k) => Form::constant(k),
        Node::Var(c) => {
          if c.source != Source::Main || c.offset != RowOffset::Current {
            return Err("template input reads a non-local column".into());
          }
          if let Some(&k) = body.subst.get(&c.index) {
            Form::constant(k)
          } else if let Some(&(l, a)) = alias.get(&c.index) {
            let prev = prev.ok_or("alias without a previous body")?;
            // The previous body has the same graph.
            prev[g.lookups[l].args[a].index()].clone()
          } else {
            Form::atom(Atom::Col(bi, c.index), Scalar::ONE)
          }
        },
        Node::Public(_)
        | Node::IsFirstRow
        | Node::IsLastRow
        | Node::IsTransition => {
          return Err("template input uses a row selector or public".into());
        },
        Node::Add(x, y) => {
          forms[x.index()].combine(&forms[y.index()], Scalar::ONE)
        },
        Node::Sub(x, y) => {
          forms[x.index()].combine(&forms[y.index()], -Scalar::ONE)
        },
        Node::Neg(x) => forms[x.index()].scale(-Scalar::ONE),
        Node::Mul(x, y) => {
          let (fx, fy) = (forms[x.index()].clone(), forms[y.index()].clone());
          self.mul(&fx, &fy)
        },
      };
      forms.push(f);
    }
    Ok(forms)
  }

  fn use_atom(&mut self, a: Atom, cell: bool) {
    *(if cell { &mut self.uses_cell } else { &mut self.uses_lin })
      .entry(a)
      .or_default() += 1;
    if let Atom::Prod(p) = a
      && self.done.insert(p)
    {
      let (x, y) = self.prods[p as usize];
      self.operand_demand(x);
      self.operand_demand(y);
    }
  }

  fn operand_demand(&mut self, lid: u32) {
    let g = self.lins[lid as usize].clone();
    if g.len() == 1 {
      self.use_atom(g[0].0, true);
    } else if self.need_lin.insert(lid) {
      for (a, _) in g {
        self.use_atom(a, false);
      }
    }
  }

  fn exact_demand(&mut self, f: &Form) {
    match (&f.terms[..], f.k) {
      ([], _) => {},
      ([(a, c)], k) if *c == Scalar::ONE && k == Scalar::ZERO => {
        self.use_atom(*a, true)
      },
      _ => {
        if self.need_exact.insert(f.clone()) {
          for &(a, _) in &f.terms {
            self.use_atom(a, false);
          }
        }
      },
    }
  }

  fn new_slot(&mut self, def: SlotDef) -> Slot {
    self.slots.push(def);
    index(self.slots.len() - 1)
  }

  /// A slot defined as `Σ items + k`, with its defining relation emitted.
  fn define(
    &mut self,
    mut items: Vec<Item>,
    k: Scalar,
  ) -> Result<Slot, String> {
    let terms = items.iter().flat_map(Item::terms).collect();
    let out = self.new_slot(SlotDef::Sum(terms, k));
    items.push(Item::Linear { c: -Scalar::ONE, s: out });
    self.relation(items, k)?;
    Ok(out)
  }

  fn cell(&mut self, a: Atom) -> Result<Slot, String> {
    if let Some(&s) = self.cell_memo.get(&a) {
      return Ok(s);
    }
    let s = match a {
      Atom::Col(body, col) => self
        .new_slot(SlotDef::Column { body: body as usize, col: col as usize }),
      Atom::Prod(p) => {
        if self.inline.contains(&p) {
          return Err("fused product used as a cell".into());
        }
        let (x, y) = self.prods[p as usize];
        let (a, b) = (self.opcell(x)?, self.opcell(y)?);
        *self.stats.entry("product_cells").or_default() += 1;
        self.define(
          vec![Item::Product {
            c: Scalar::ONE,
            a,
            b,
            ca: Scalar::ZERO,
            cb: Scalar::ZERO,
          }],
          Scalar::ZERO,
        )?
      },
    };
    self.cell_memo.insert(a, s);
    Ok(s)
  }

  fn opcell(&mut self, lid: u32) -> Result<Slot, String> {
    let g = self.lins[lid as usize].clone();
    if g.len() == 1 {
      return self.cell(g[0].0);
    }
    if let Some(&s) = self.lin_memo.get(&lid) {
      return Ok(s);
    }
    let items = self.items(&g)?;
    let s = self.define(items, Scalar::ZERO)?;
    self.lin_memo.insert(lid, s);
    Ok(s)
  }

  fn exact_cell(&mut self, f: &Form) -> Result<Slot, String> {
    if let ([(a, c)], k) = (&f.terms[..], f.k)
      && *c == Scalar::ONE
      && k == Scalar::ZERO
    {
      return self.cell(*a);
    }
    if let Some(&s) = self.exact_memo.get(f) {
      return Ok(s);
    }
    let items = self.items(&f.terms)?;
    let s = self.define(items, f.k)?;
    self.exact_memo.insert(f.clone(), s);
    Ok(s)
  }

  fn items(&mut self, terms: &Lin) -> Result<Vec<Item>, String> {
    let mut items = vec![];
    for &(a, c) in terms {
      match a {
        Atom::Prod(p) if self.inline.contains(&p) => {
          let (x, y) = self.prods[p as usize];
          let (a, b) = (self.opcell(x)?, self.opcell(y)?);
          items.push(Item::Product {
            c,
            a,
            b,
            ca: Scalar::ZERO,
            cb: Scalar::ZERO,
          });
        },
        _ => {
          let s = self.cell(a)?;
          items.push(Item::Linear { c, s });
        },
      }
    }
    Ok(items)
  }

  /// Merge repeated linear slots and absorb linear terms on a product's
  /// operands into that product's lane.
  fn normalize(items: Vec<Item>) -> Vec<Item> {
    let mut linear: BTreeMap<Slot, Scalar> = BTreeMap::new();
    let mut products = vec![];
    for item in items {
      match item {
        Item::Linear { c, s } => *linear.entry(s).or_insert(Scalar::ZERO) += c,
        p @ Item::Product { .. } => products.push(p),
      }
    }
    for p in &mut products {
      if let Item::Product { a, b, ca, cb, .. } = p {
        if let Some(c) = linear.remove(a) {
          *ca += c;
        }
        if let Some(c) = linear.remove(b) {
          *cb += c;
        }
      }
    }
    let mut out = products;
    out.extend(
      linear
        .into_iter()
        .filter(|&(_, c)| c != Scalar::ZERO)
        .map(|(s, c)| Item::Linear { c, s }),
    );
    out
  }

  /// Emit `Σ items + k = 0` as one span, or as full-row spans chained by
  /// carry slots. Every span holds at most one product, in its first lane.
  fn relation(&mut self, items: Vec<Item>, k: Scalar) -> Result<(), String> {
    let items = Self::normalize(items);
    if items.is_empty() {
      return if k == Scalar::ZERO {
        Ok(())
      } else {
        Err("unsatisfiable relation".into())
      };
    }
    let cap = 4 * self.lanes;
    let mut rest = items;
    let mut k = k;
    let mut carry: Option<Slot> = None;
    loop {
      let reserved = usize::from(carry.is_some());
      let prods = rest.iter().filter(|i| i.cells() == 2).count();
      let cells: usize = rest.iter().map(Item::cells).sum::<usize>() + reserved;
      if prods <= 1 && cells <= cap {
        let mut piece = std::mem::take(&mut rest);
        if let Some(c) = carry {
          piece.push(Item::Linear { c: Scalar::ONE, s: c });
        }
        self.span(&piece, k, cells.div_ceil(4).max(1));
        return Ok(());
      }
      // One product (if any) and linear items, leaving a cell for the
      // outgoing carry.
      let mut room = cap - 1 - reserved;
      let mut piece = vec![];
      let mut keep = vec![];
      let mut took_product = false;
      for item in rest.drain(..) {
        let fits = item.cells() <= room && (item.cells() == 1 || !took_product);
        if fits {
          room -= item.cells();
          took_product |= item.cells() == 2;
          piece.push(item);
        } else {
          keep.push(item);
        }
      }
      rest = keep;
      if piece.is_empty() {
        return Err("relation item does not fit a row".into());
      }
      if let Some(c) = carry {
        piece.push(Item::Linear { c: Scalar::ONE, s: c });
      }
      let terms = piece.iter().flat_map(Item::terms).collect();
      let next = self.new_slot(SlotDef::Sum(terms, k));
      piece.push(Item::Linear { c: -Scalar::ONE, s: next });
      self.span(&piece, k, self.lanes);
      *self.stats.entry("carries").or_default() += 1;
      k = Scalar::ZERO;
      carry = Some(next);
    }
  }

  fn span(&mut self, items: &[Item], k: Scalar, n: usize) {
    let mut lanes: Vec<(Scalar, [Scalar; 4], Scalar, [Option<Slot>; 4])> =
      vec![(Scalar::ZERO, [Scalar::ZERO; 4], Scalar::ZERO, [None; 4]); n];
    let mut free: Vec<(usize, usize)> = vec![];
    let mut product = false;
    for item in items {
      if let Item::Product { c, a, b, ca, cb } = *item {
        lanes[0] = (
          c,
          [ca, cb, Scalar::ZERO, Scalar::ZERO],
          Scalar::ZERO,
          [Some(a), Some(b), None, None],
        );
        product = true;
      }
    }
    for l in 0..n {
      let start = if l == 0 && product { 2 } else { 0 };
      free.extend((start..4).map(|c| (l, c)));
    }
    let mut free = free.into_iter();
    for item in items {
      if let Item::Linear { c, s } = *item {
        let (l, cell) = free.next().expect("relation fits its span");
        lanes[l].3[cell] = Some(s);
        lanes[l].1[cell] = c;
      }
    }
    lanes[0].2 = k;
    let lanes: Vec<LaneUse> = lanes
      .into_iter()
      .map(|(qm, q, qc, cells)| LaneUse::Gate { qm, q, qc, cells })
      .collect();
    *self.stats.entry("gate_lanes").or_default() += n as u64;
    self.place(lanes);
  }

  /// First-fit placement of a span (or a lane message) into gate rows.
  fn place(&mut self, lanes: Vec<LaneUse>) {
    let n = lanes.len();
    let found = self
      .open
      .iter()
      .position(|&r| self.lanes - self.gate_rows[r].lanes.len() >= n);
    let r = match found {
      Some(i) => self.open[i],
      None => {
        self.gate_rows.push(GateRowBuild { lanes: vec![], spans: vec![] });
        self.open.push(self.gate_rows.len() - 1);
        self.gate_rows.len() - 1
      },
    };
    let row = &mut self.gate_rows[r];
    let start = row.lanes.len();
    if matches!(lanes[0], LaneUse::Gate { .. }) {
      row.spans.push((start, n));
    }
    row.lanes.extend(lanes);
    if row.lanes.len() == self.lanes {
      self.open.retain(|&x| x != r);
    }
  }

  fn message(&mut self, d: &Demand) -> Result<(), String> {
    let w = self.width;
    if d.args.len() < 2 {
      return Err("lookup without [tag, id] prefix".into());
    }
    let tag = canonical(
      d.args[0]
        .terms
        .is_empty()
        .then_some(d.args[0].k)
        .ok_or("non-constant lookup tag")?,
    )?;
    let id = canonical(
      d.args[1]
        .terms
        .is_empty()
        .then_some(d.args[1].k)
        .ok_or("non-constant lookup id")?,
    )?;
    let target_id =
      usize::try_from(id).map_err(|e| format!("lookup id {id}: {e}"))?;
    let target = if d.lookup == 0 {
      if tag != CALL {
        return Err("receive is not a call".into());
      }
      Target::Receive
    } else if tag == ROM {
      Target::Rom(target_id)
    } else if tag == CALL && target_id < self.functions {
      Target::Call(target_id)
    } else if tag == CALL {
      Target::Map(target_id)
    } else {
      return Err("unknown lookup tag".into());
    };
    let (mk, mc, mult) = match (&d.mult.terms[..], d.mult.k) {
      ([], k) => (k, Scalar::ZERO, None),
      ([(a, c)], k) => (k, *c, Some(self.cell(*a)?)),
      _ => (Scalar::ZERO, Scalar::ONE, Some(self.exact_cell(&d.mult)?)),
    };
    let first_const =
      d.args.get(2).and_then(|f| f.terms.is_empty().then_some(f.k));
    let payload = d.args[2..]
      .iter()
      .map(|f| self.exact_cell(f))
      .collect::<Result<Vec<_>, _>>()?;
    let p = payload.len();
    let rom = matches!(target, Target::Rom(_));
    if rom && p == 0 {
      return Err("ROM lookup without address".into());
    }
    let mcell = mult;
    let base_ts = match target {
      Target::Rom(_) => ts(ROM, id),
      _ => ts(CALL, id),
    };
    let (placement, chunks, key) = if p <= 3 {
      let mut cells = [None; 4];
      cells[0] = mcell;
      for (i, &v) in payload.iter().enumerate() {
        cells[1 + i] = Some(v);
      }
      self.place(vec![LaneUse::Message { ts: base_ts, mk, mc, cells }]);
      *self.stats.entry("lane_messages").or_default() += 1;
      (Placement::Lane, 1, None)
    } else if p < w {
      let mut cells = vec![None; w];
      cells[0] = mcell;
      for (i, &v) in payload.iter().enumerate() {
        cells[1 + i] = Some(v);
      }
      self.msg_rows.push(Row::Message {
        ts: base_ts,
        mk,
        mc,
        receive_key: false,
        cells,
      });
      *self.stats.entry("row_messages").or_default() += 1;
      (Placement::Row, 1, None)
    } else {
      // Keyed chunks: `[ts_j, key, values_j]`.
      let (key, values): (Option<Slot>, Vec<Slot>) = match target {
        Target::Rom(_) => (Some(payload[0]), payload[1..].to_vec()),
        Target::Receive => (None, payload.clone()),
        _ => (
          Some(self.new_slot(SlotDef::Key(self.messages.len()))),
          payload.clone(),
        ),
      };
      if target != Target::Receive {
        // Keyed chunks from one sender are bound to a single endpoint only
        // when its multiplicity is 0 or 1: `M² − M = 0` with `M = mk + mc·x`.
        match mcell {
          None => {
            if mk != Scalar::ZERO && mk != Scalar::ONE {
              return Err(
                "chunked send with a non-boolean constant multiplicity".into(),
              );
            }
          },
          Some(x) => {
            let two = Scalar::from_u64(2);
            self.relation(
              vec![Item::Product {
                c: mc * mc,
                a: x,
                b: x,
                ca: two * mk * mc - mc,
                cb: Scalar::ZERO,
              }],
              mk * mk - mk,
            )?;
            *self.stats.entry("booleanity_relations").or_default() += 1;
          },
        }
      }
      let per = w - 2;
      let chunks = values.len().div_ceil(per).max(1);
      for c in 0..chunks {
        let mut cells = vec![None; w];
        cells[0] = mcell;
        cells[1] = key;
        for (i, &v) in values.iter().skip(c * per).take(per).enumerate() {
          cells[2 + i] = Some(v);
        }
        let sub = if rom {
          id + c as u64 * CHUNK_STRIDE
        } else {
          id + (c as u64 + 1) * CHUNK_STRIDE
        };
        let t = ts(if rom { ROM } else { CALL }, sub);
        self.msg_rows.push(Row::Message {
          ts: t,
          mk,
          mc,
          receive_key: target == Target::Receive,
          cells,
        });
      }
      *self.stats.entry("chunk_rows").or_default() += chunks as u64;
      (Placement::Chunked, chunks, key)
    };
    self.messages.push(Message {
      target,
      mk,
      mc,
      mult,
      payload,
      first_const,
      placement,
      chunks,
      key,
    });
    Ok(())
  }
}

/// Evaluate `terms + k` from already-known slot values.
pub fn evaluate(terms: &[Term], k: Scalar, values: &[Scalar]) -> Scalar {
  terms.iter().fold(k, |acc, t| match *t {
    Term::Linear(c, s) => acc + c * values[s as usize],
    Term::Product(c, a, b) => acc + c * values[a as usize] * values[b as usize],
  })
}

/// Evaluate every node of a one-row graph on a wide row.
fn eval_graph(
  g: &ConstraintGraph<Scalar>,
  row: &[Scalar],
  nodes: &[NodeId],
) -> Vec<Scalar> {
  let mut v: Vec<Scalar> = Vec::with_capacity(g.nodes.len());
  let last = nodes.iter().map(|n| n.index()).max().unwrap_or(0);
  for node in &g.nodes[..=last] {
    let x = match *node {
      Node::Const(k) => k,
      Node::Var(c) => row[c.index as usize],
      Node::Add(a, b) => v[a.index()] + v[b.index()],
      Node::Sub(a, b) => v[a.index()] - v[b.index()],
      Node::Mul(a, b) => v[a.index()] * v[b.index()],
      Node::Neg(a) => -v[a.index()],
      _ => Scalar::ZERO,
    };
    v.push(x);
  }
  nodes.iter().map(|n| v[n.index()]).collect()
}

#[derive(Clone, Debug)]
pub struct Config {
  /// Cells per narrow row, a multiple of 4 (`W / 4` lanes).
  pub width: usize,
  /// Instances per function circuit in compiler circuit order. For the
  /// unrolled `Blake3::compress` an instance is one whole compression.
  pub capacities: Vec<usize>,
  /// Objects per ROM width, in increasing width order.
  pub rom_capacities: Vec<usize>,
  /// Maximum rows per narrow shard (`2^log`).
  pub log_shard_rows: usize,
  /// Shard count; the minimum that fits `2^log_shard_rows` when `None`.
  pub shards: Option<usize>,
  pub lookup_budget: usize,
  pub unroll_compress: bool,
  /// Per-shard id and label offsets. Disabling them is unsound and exists
  /// only so tests can show the forgeries they prevent.
  pub shard_offsets: bool,
  /// The entry point whose claim the verifier supplies. Its function's
  /// region comes first and the root invocation is its instance 0, so the
  /// root's invocation id is 0, the key of a chunked request in the
  /// verified layout (`Part.request`). `None` keeps compiler order and keys
  /// a chunked request by wherever the root lands.
  pub entry: Option<String>,
}

struct Region {
  /// Local invocation id of instance 0 (global id adds the shard offset).
  id_base: u64,
  row_base: usize,
  /// Local copy label of slot 0 of instance 0.
  label_base: u64,
}

struct LeanFixed {
  fixed: RowMajorMatrix<Scalar>,
  request: Vec<Vec<Scalar>>,
  /// The map and ROM tables of `Periodic.narrow_heap_sound_compact`, when the
  /// export has them; otherwise the tables are [`Backend::stacked`].
  compact: Option<[CompactTable; 2]>,
  /// The exported shard circuits (`S.circuit k`), one per shard, and the
  /// compact table circuits (`Compact.circuit W`), map table first: the
  /// circuits proved, read literally.
  narrow: Vec<lean::Graph>,
  compact_circuits: Vec<lean::Graph>,
}

/// A compact table exported by the Lean pass (`Periodic.Compact`,
/// `aiur-template-lean-plan.md` §5g): one circuit holding many receiver
/// parts, one narrow row tuple per physical row. With shard width `W` and
/// `n = n_fixed`, main column 0 is the count and main columns
/// `1 … W − 1 − n` are cells `n … W − 2`; the fixed columns are `selL`,
/// `selW`, the row's code and cells `0 … n − 1`, exactly the exported
/// matrix. The map table has `n = W − 1`, the ROM table `n = 1`.
#[derive(Clone)]
pub struct CompactTable {
  pub n_fixed: usize,
  pub main_width: usize,
  pub rows: usize,
  /// The exported fixed rows, zero-padded to [`Self::height`].
  pub fixed: RowMajorMatrix<Scalar>,
}

impl CompactTable {
  pub fn height(&self) -> usize {
    self.rows.next_power_of_two().max(MIN_TABLE_HEIGHT)
  }
}

struct MapInfo {
  callable: usize,
  rows: Vec<Vec<Scalar>>,
}

/// Rows of a stacked table, padded to a power of two, at least
/// [`MIN_TABLE_HEIGHT`]. Packed commitments group matrices by height, so
/// padding the small tables to one height keeps them in one pack per round
/// instead of one per distinct height; the padding rows have `sel = 0`.
pub const MIN_TABLE_HEIGHT: usize = 1 << 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TableSource {
  /// Index into the called maps.
  Map(usize),
  /// Index into the memory widths.
  Rom(usize),
}

/// A stacked table in the column shape of `Periodic.Stacked`
/// (`Aiur/Tiling/PeriodicStacked.lean`): its own circuit beside the shards.
/// Main column 0 is the count and the other main columns are witness values
/// (the ROM words); the fixed columns are `sel`, `key` and the per-row data
/// (a map row's payload). Variables `v < main_width` are main columns, the
/// others fixed column `v − main_width`. Narrow row `c` of a table row reads
/// the variables `slices[c]`, keyed by `key` when there are several.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stacked {
  pub tag: u64,
  pub sub: u64,
  pub rows: usize,
  pub key_base: u64,
  pub main_width: usize,
  pub slices: Vec<Vec<usize>>,
  pub source: TableSource,
}

impl Stacked {
  pub fn chunked(&self) -> bool {
    self.slices.len() >= 2
  }
  pub fn sel_col(&self) -> usize {
    self.main_width
  }
  pub fn key_col(&self) -> usize {
    self.main_width + 1
  }
  pub fn height(&self) -> usize {
    self.rows.next_power_of_two().max(MIN_TABLE_HEIGHT)
  }
  fn fixed_width(&self, data: &[Vec<Scalar>]) -> usize {
    2 + data.first().map_or(0, Vec::len)
  }
  /// `subOf`: chunk subs are `sub + (c+1)·2^32` on calls and `sub + c·2^32`
  /// on the ROM.
  pub fn code(&self, c: usize) -> Scalar {
    let sub = match (self.chunked(), self.tag == ROM) {
      (false, _) => self.sub,
      (true, true) => self.sub + c as u64 * CHUNK_STRIDE,
      (true, false) => self.sub + (c as u64 + 1) * CHUNK_STRIDE,
    };
    ts(self.tag, sub)
  }
}

struct Unrolled {
  circuit: usize,
  function: usize,
  selfcall: usize,
  stage_col: usize,
  sel_col: usize,
  act_col: usize,
  /// Bodies per compression ([`compress_stages`]).
  stages: usize,
  /// The receive's multiplicity column, fixed to 1 in every body after the
  /// first (see [`compress_bodies`]).
  recv_mult_col: usize,
}

/// The stage bodies of one unrolled `Blake3::compress`. Every body fixes the
/// activity column to 1 and the self-call multiplicity to 1 (0 in the last
/// body) and drops the self-call; body 0 fixes the stage argument to 0. Body
/// `s > 0` reads each receive column as body `s − 1`'s self-call argument,
/// drops its receive, and fixes the receive multiplicity column to 1: that
/// column holds no cell, and pinning it makes each dropped receive of body
/// `s` cancel body `s − 1`'s dropped self-call (multiplicities `−1` and `+1`
/// on identical tuples), which the soundness argument for the unrolled
/// circuit pairs up (`aiur-template-lean-plan.md` §5e).
fn compress_bodies<'g>(
  g: &'g ConstraintGraph<Scalar>,
  u: &Unrolled,
) -> Result<Vec<Body<'g>>, String> {
  let rvars: Vec<u32> = g.lookups[0].args[2..]
    .iter()
    .map(|a| match g.nodes[a.index()] {
      Node::Var(v) => Ok(v.index),
      _ => Err("compress receive argument is not a column".to_owned()),
    })
    .collect::<Result<_, _>>()?;
  let col = |c: usize| {
    u32::try_from(c).map_err(|e| format!("compress column {c}: {e}"))
  };
  let (sel_col, act_col) = (col(u.sel_col)?, col(u.act_col)?);
  let (stage_col, recv_mult_col) = (col(u.stage_col)?, col(u.recv_mult_col)?);
  Ok(
    (0..u.stages)
      .map(|s| {
        let mut subst = HashMap::new();
        subst.insert(sel_col, Scalar::from_bool(s + 1 < u.stages));
        subst.insert(act_col, Scalar::ONE);
        if s == 0 {
          subst.insert(stage_col, Scalar::ZERO);
        } else {
          subst.insert(recv_mult_col, Scalar::ONE);
        }
        let alias = if s == 0 {
          vec![]
        } else {
          rvars
            .iter()
            .enumerate()
            .filter(|(_, ix)| !subst.contains_key(ix))
            .map(|(pos, &ix)| (ix, u.selfcall, 2 + pos))
            .collect()
        };
        let mut drop: HashSet<usize> = [u.selfcall].into();
        if s > 0 {
          drop.insert(0);
        }
        Body { graph: g, subst, alias, drop }
      })
      .collect(),
  )
}

pub struct Backend<'c, 'p, 'a> {
  compiler: &'c Compiler<'p, 'a>,
  plan: &'p TracePlan<'a, Bn254>,
  pub config: Config,
  pub templates: Vec<Template>,
  /// The graph each function circuit's template is lowered from.
  graphs: Vec<ConstraintGraph<Scalar>>,
  unrolled: Option<Unrolled>,
  regions: Vec<Region>,
  /// Instances of each function per shard.
  pub per_shard: Vec<usize>,
  pub shards: usize,
  pub rows_per_shard: usize,
  pub height: usize,
  ids_per_shard: u64,
  labels_per_shard: u64,
  maps: Vec<MapInfo>,
  memory_widths: Vec<usize>,
  callee_circuit: Vec<usize>,
  /// The entry function's circuit when [`Config::entry`] is set.
  entry_circuit: Option<usize>,
  /// Function circuits in region order.
  order: Vec<usize>,
  /// The shared fixed matrix and request of an adopted Lean export.
  lean: Option<LeanFixed>,
  /// Whether padding instances must copy a real instance (a template that
  /// all-zero cells do not satisfy).
  copy_padding: Vec<bool>,
}

/// Narrow fixed-column layout for `W` cells and `L = W/4` lanes.
#[derive(Clone, Copy)]
struct Columns {
  w: usize,
  l: usize,
}

impl Columns {
  fn lane(&self, l: usize) -> usize {
    6 * l
  }
  fn flag(&self, l: usize, m: usize) -> usize {
    debug_assert!(l <= m);
    6 * self.l + l * self.l - l * (l.saturating_sub(1)) / 2 + (m - l)
  }
  fn lane_msg(&self, l: usize) -> usize {
    6 * self.l + self.l * (self.l + 1) / 2 + 3 * l
  }
  fn row_msg(&self) -> usize {
    9 * self.l + self.l * (self.l + 1) / 2
  }
  fn labels(&self) -> usize {
    self.row_msg() + 5
  }
  fn mults(&self) -> usize {
    self.labels() + self.w
  }
  fn width(&self) -> usize {
    self.mults() + self.w
  }
}

impl<'c, 'p, 'a> Backend<'c, 'p, 'a> {
  /// The backend over this crate's own lowering of the compiler circuits
  /// (`compile_graph`): for sizing a configuration, for the backend's tests
  /// and as a cross-check of a Lean export ([`Self::from_lean`] proves).
  pub fn new(
    compiler: &'c Compiler<'p, 'a>,
    plan: &'p TracePlan<'a, Bn254>,
    config: Config,
  ) -> Result<Self, String> {
    Self::with_graphs(compiler, plan, config, None)
  }

  /// The backend over `graphs`, one per function circuit in compiler
  /// circuit order, or over `compile_graph` of the compiler circuits.
  pub fn with_graphs(
    compiler: &'c Compiler<'p, 'a>,
    plan: &'p TracePlan<'a, Bn254>,
    config: Config,
    graphs: Option<Vec<ConstraintGraph<Scalar>>>,
  ) -> Result<Self, String> {
    let w = config.width;
    let nf = compiler.function_circuits();
    if config.capacities.len() != nf {
      return Err("one capacity per function circuit".into());
    }
    let program = plan.program().program();
    let functions = program.functions.len();
    let params = extension_params::<KzgConfig>();
    let layout = plan.layout()?;
    let callee_circuit: Vec<usize> = plan
      .function_chips()
      .iter()
      .map(|&chip| layout.placements[chip].circuit)
      .collect();
    let graphs = match graphs {
      Some(g) if g.len() == nf => g,
      Some(_) => return Err("one graph per function circuit".into()),
      None => compiler.inputs()[..nf]
        .par_iter()
        .zip(&compiler.names()[..nf])
        .map(|(input, name)| {
          input.compile_graph(&params).map_err(|e| format!("{name}: {e:?}"))
        })
        .collect::<Result<Vec<_>, String>>()?,
    };
    let mut unrolled = None;
    if config.unroll_compress
      && let Some(function) =
        program.functions.iter().position(|f| f.name == COMPRESS)
    {
      let circuit = callee_circuit[function];
      let g = &graphs[circuit];
      let var = |n: NodeId| match g.nodes[n.index()] {
        Node::Var(c) => Some(c.index as usize),
        Node::Sub(z, x) if matches!(g.nodes[z.index()], Node::Const(k) if k == Scalar::ZERO) => {
          match g.nodes[x.index()] {
            Node::Var(c) => Some(c.index as usize),
            _ => None,
          }
        },
        Node::Neg(x) => match g.nodes[x.index()] {
          Node::Var(c) => Some(c.index as usize),
          _ => None,
        },
        _ => None,
      };
      let constant = |n: NodeId| match g.nodes[n.index()] {
        Node::Const(k) => k.canonical_u64(),
        _ => None,
      };
      let calls: Vec<usize> = (1..g.lookups.len())
        .filter(|&j| constant(g.lookups[j].args[1]) == Some(function as u64))
        .collect();
      let [selfcall] = calls[..] else {
        return Err("Blake3::compress: expected one self-call".into());
      };
      let sel_col = var(g.lookups[selfcall].multiplicity)
        .ok_or("self-call multiplicity is not a column")?;
      let stage_col =
        var(g.lookups[0].args[2]).ok_or("stage argument is not a column")?;
      let recv_mult_col = var(g.lookups[0].multiplicity)
        .ok_or("compress receive multiplicity is not a column")?;
      let main_width = compiler.inputs()[circuit].main_width;
      let stages = compress_stages(&program.functions[function])?;
      unrolled = Some(Unrolled {
        circuit,
        function,
        selfcall,
        stage_col,
        sel_col,
        act_col: main_width - 2,
        stages,
        recv_mult_col,
      });
    }
    let templates = (0..nf)
      .into_par_iter()
      .map(|c| {
        let name = &compiler.names()[c];
        let bodies: Vec<Body<'_>> = match &unrolled {
          Some(u) if u.circuit == c => compress_bodies(&graphs[c], u)?,
          _ => vec![Body {
            graph: &graphs[c],
            subst: HashMap::new(),
            alias: vec![],
            drop: HashSet::new(),
          }],
        };
        lower(&bodies, w, functions).map_err(|e| format!("{name}: {e}"))
      })
      .collect::<Result<Vec<_>, String>>()?;
    for t in &templates {
      for m in &t.messages {
        if let Target::Call(c) = m.target {
          let callee = &templates[callee_circuit[c]].messages[0];
          if callee.payload.len() != m.payload.len() {
            return Err("call arity differs from its callee's receive".into());
          }
          if let Some(u) = &unrolled
            && u.function == c
            && m.first_const != Some(Scalar::ZERO)
          {
            return Err("a caller enters Blake3::compress at a stage other than a constant 0".into());
          }
        }
      }
    }
    let real: Vec<usize> = config.capacities.clone();
    let rows_total: usize =
      templates.iter().zip(&real).map(|(t, &c)| t.rows.len() * c).sum();
    let cap = 1usize << config.log_shard_rows;
    let mut shards =
      config.shards.unwrap_or_else(|| rows_total.div_ceil(cap).max(1));
    let (per_shard, rows_per_shard) = loop {
      let per: Vec<usize> = real.iter().map(|&c| c.div_ceil(shards)).collect();
      let rows: usize =
        templates.iter().zip(&per).map(|(t, &p)| t.rows.len() * p).sum();
      if rows <= cap || config.shards.is_some() {
        break (per, rows);
      }
      shards += 1;
    };
    if rows_per_shard > cap {
      let mut largest: Vec<(usize, usize)> = templates
        .iter()
        .zip(&per_shard)
        .enumerate()
        .map(|(f, (t, &p))| (t.rows.len() * p, f))
        .collect();
      largest.sort_unstable_by(|a, b| b.cmp(a));
      let names = compiler.names();
      let largest: Vec<String> = largest
        .iter()
        .take(8)
        .map(|&(rows, f)| {
          format!(
            "{} {rows} ({} rows x {})",
            names[f], templates[f].rows.len(), per_shard[f]
          )
        })
        .collect();
      return Err(format!(
        "{rows_per_shard} rows per shard exceed 2^{}; largest: {}",
        config.log_shard_rows,
        largest.join(", ")
      ));
    }
    let entry_circuit = match &config.entry {
      Some(name) => Some(callee_circuit[plan.program().entry(name)?.function]),
      None => None,
    };
    let order: Vec<usize> = entry_circuit
      .into_iter()
      .chain((0..nf).filter(|&f| Some(f) != entry_circuit))
      .collect();
    let mut regions: Vec<Option<Region>> = (0..nf).map(|_| None).collect();
    let (mut id, mut row, mut label) = (0u64, 0usize, 1u64);
    for &f in &order {
      let (t, p) = (&templates[f], per_shard[f]);
      regions[f] =
        Some(Region { id_base: id, row_base: row, label_base: label });
      id += p as u64;
      row += p * t.rows.len();
      label += p as u64 * t.logical_slots as u64;
    }
    let regions: Vec<Region> = regions
      .into_iter()
      .map(|r| r.expect("every circuit has a region"))
      .collect();
    let called: HashSet<usize> = templates
      .iter()
      .flat_map(|t| t.messages.iter())
      .filter_map(|m| match m.target {
        Target::Map(c) => Some(c),
        _ => None,
      })
      .collect();
    let mut maps = vec![];
    for (map, def) in program.maps.iter().enumerate() {
      if !called.contains(&(functions + map)) {
        continue;
      }
      let height = program.tables[def.input].rows.len();
      let rows = (0..height)
        .map(|r| {
          program.tables[def.input].rows[r]
            .iter()
            .chain(&program.tables[def.output].rows[r])
            .map(|&x| Bn254.from_word(x))
            .collect()
        })
        .collect();
      maps.push(MapInfo { callable: functions + map, rows });
    }
    let memory_widths: Vec<usize> = compiler
      .names()
      .iter()
      .filter_map(|n| {
        n.strip_prefix("<ROM:")?.strip_suffix('>')?.parse::<usize>().ok()
      })
      .collect();
    if config.rom_capacities.len() != memory_widths.len() {
      return Err("one ROM capacity per memory width".into());
    }
    let mut b = Self {
      compiler,
      plan,
      config,
      templates,
      graphs,
      unrolled,
      regions,
      per_shard,
      shards,
      rows_per_shard,
      height: rows_per_shard.next_power_of_two().max(1),
      ids_per_shard: id,
      labels_per_shard: label,
      maps,
      memory_widths,
      callee_circuit,
      entry_circuit,
      order,
      lean: None,
      copy_padding: vec![],
    };
    b.copy_padding = (0..nf).map(|f| !b.zero_instance_ok(f)).collect();
    Ok(b)
  }

  fn cols(&self) -> Columns {
    Columns { w: self.config.width, l: self.config.width / 4 }
  }

  pub fn id_offset(&self, shard: usize) -> u64 {
    if self.config.shard_offsets {
      shard as u64 * self.ids_per_shard
    } else {
      0
    }
  }

  fn label_offset(&self, shard: usize) -> u64 {
    if self.config.shard_offsets {
      shard as u64 * self.labels_per_shard
    } else {
      0
    }
  }

  /// Whether all-zero columns satisfy function `f`'s template with no
  /// message multiplicity.
  fn zero_instance_ok(&self, f: usize) -> bool {
    let t = &self.templates[f];
    let mut v = vec![Scalar::ZERO; t.slots.len()];
    for (s, def) in t.slots.iter().enumerate() {
      if let SlotDef::Sum(terms, k) = def {
        v[s] = evaluate(terms, *k, &v);
      }
    }
    let lanes_ok = t.rows.iter().all(|row| match row {
      Row::Gate { lanes, spans } => spans.iter().all(|&(start, n)| {
        lanes[start..start + n]
          .iter()
          .fold(Scalar::ZERO, |acc, l| acc + lane_value(l, &v))
          == Scalar::ZERO
      }),
      Row::Message { .. } => true,
    });
    lanes_ok && t.messages.iter().all(|m| m.multiplicity(&v) == Scalar::ZERO)
  }

  fn narrow_circuit(
    &self,
    shard: usize,
    fixed: Option<RowMajorMatrix<Scalar>>,
  ) -> CircuitInputs<Scalar> {
    let c = self.cols();
    let (w, l) = (c.w, c.l);
    let x = |i: usize| Expr::main(index(i));
    let q = |i: usize| Expr::preprocessed(index(i));
    let k = |v: Scalar| Expr::constant(v);
    let lin = |m: usize| {
      let b = c.lane(m);
      q(b + 1) * x(4 * m)
        + q(b + 2) * x(4 * m + 1)
        + q(b + 3) * x(4 * m + 2)
        + q(b + 4) * x(4 * m + 3)
        + q(b + 5)
    };
    let constraints = (0..l)
      .map(|m| {
        let mut e = q(c.lane(m)) * x(4 * m) * x(4 * m + 1);
        for n in m..l {
          e = e + q(c.flag(m, n)) * lin(n);
        }
        e
      })
      .collect();
    let copy_base = Scalar::from_u64(COPY)
      + Scalar::from_u64(4) * Scalar::from_u64(self.label_offset(shard));
    let mut lookups: Vec<_> = (0..w)
      .map(|j| {
        Lookup::push(
          q(c.mults() + j),
          vec![k(copy_base) + k(Scalar::from_u64(4)) * q(c.labels() + j), x(j)],
        )
      })
      .collect();
    for m in 0..l {
      let b = c.lane_msg(m);
      lookups.push(Lookup::push(
        q(b + 1) + q(b + 2) * x(4 * m),
        vec![q(b), x(4 * m + 1), x(4 * m + 2), x(4 * m + 3)],
      ));
    }
    let r = c.row_msg();
    let offset = Scalar::from_u64(self.id_offset(shard));
    let mut args = vec![q(r), x(1) + q(r + 3) + q(r + 4) * k(offset)];
    args.extend((2..w).map(x));
    lookups.push(Lookup::push(q(r + 1) + q(r + 2) * x(0), args));
    // Group sizes depend only on expression shapes: probe with a one-row
    // stand-in for the fixed matrix.
    let mut input = CircuitInputs {
      main_width: w,
      preprocessed: Some(RowMajorMatrix::new(
        vec![Scalar::ZERO; c.width()],
        c.width(),
      )),
      constraints,
      lookups,
      ..Default::default()
    };
    input.lookup_group_size = group_size(&input, self.config.lookup_budget);
    input.preprocessed = fixed;
    input
  }

  /// Invocation id of the first row of every map. Map-claim rows are the
  /// instances of the stacked map tables, which follow the chip shards: their
  /// ids continue after the chips' (`Sharded.idOffset`), map by map in
  /// callable order, and a chunked row is keyed by its id, not its row index.
  fn map_id_bases(&self) -> Vec<u64> {
    let mut id = self.id_offset(self.shards);
    self
      .maps
      .iter()
      .map(|m| {
        let base = id;
        id += m.rows.len() as u64;
        base
      })
      .collect()
  }

  /// Channel code of every bus and whether its messages occupy a lane, in
  /// first-use order over the templates in region order (`busesOf`).
  pub fn buses(&self) -> Vec<(Scalar, bool)> {
    let mut buses: Vec<(Scalar, bool)> = vec![];
    for &f in &self.order {
      for row in &self.templates[f].rows {
        let uses: Vec<(Scalar, bool)> = match row {
          Row::Gate { lanes, .. } => lanes
            .iter()
            .filter_map(|l| match l {
              LaneUse::Message { ts, .. } => Some((*ts, true)),
              _ => None,
            })
            .collect(),
          Row::Message { ts, .. } => vec![(*ts, false)],
        };
        for u in uses {
          if !buses.iter().any(|b| b.0 == u.0) {
            buses.push(u);
          }
        }
      }
    }
    buses
  }

  /// The stacked tables beside the shards (`Periodic.Stacked`): one map
  /// table per called map in callable order, keyed by global ids after the
  /// chip shards, then one ROM table per memory width with one row per
  /// address `0..capacity`.
  pub fn stacked(&self) -> Vec<Stacked> {
    let w = self.config.width;
    let ids = self.map_id_bases();
    let chunks = |n: usize, col: &dyn Fn(usize) -> usize| -> Vec<Vec<usize>> {
      (0..n.div_ceil(w - 2))
        .map(|c| (c * (w - 2)..n.min((c + 1) * (w - 2))).map(col).collect())
        .collect()
    };
    let mut out = vec![];
    for (mi, m) in self.maps.iter().enumerate() {
      let n = m.rows.first().map_or(0, Vec::len);
      let data = |j: usize| 3 + j;
      let slices =
        if n < w { vec![(0..n).map(data).collect()] } else { chunks(n, &data) };
      out.push(Stacked {
        tag: CALL,
        sub: m.callable as u64,
        rows: m.rows.len(),
        key_base: ids[mi],
        main_width: 1,
        slices,
        source: TableSource::Map(mi),
      });
    }
    for (b, (&width, &cap)) in
      self.memory_widths.iter().zip(&self.config.rom_capacities).enumerate()
    {
      let slices = if width + 2 <= w {
        vec![std::iter::once(width + 2).chain(1..=width).collect()]
      } else {
        chunks(width, &|j| 1 + j)
      };
      out.push(Stacked {
        tag: ROM,
        sub: width as u64,
        rows: cap,
        key_base: 0,
        main_width: 1 + width,
        slices,
        source: TableSource::Rom(b),
      });
    }
    out
  }

  /// Fixed columns of a stacked table: `sel`, `key = key_base + r`, then the
  /// map row's payload; zero on padding rows.
  fn stacked_fixed(&self, t: &Stacked) -> RowMajorMatrix<Scalar> {
    let data: &[Vec<Scalar>] = match t.source {
      TableSource::Map(mi) => &self.maps[mi].rows,
      TableSource::Rom(_) => &[],
    };
    let fw = t.fixed_width(data);
    let mut values = vec![Scalar::ZERO; t.height() * fw];
    values.par_chunks_mut(fw).take(t.rows).enumerate().for_each(|(r, out)| {
      out[0] = Scalar::ONE;
      out[1] = Scalar::from_u64(t.key_base + r as u64);
      if let Some(d) = data.get(r) {
        out[2..2 + d.len()].copy_from_slice(d);
      }
    });
    RowMajorMatrix::new(values, fw)
  }

  /// `Stacked.circuit`: no constraints; lookup `c` is
  /// `push(−sel·count, [code_c, key?, slice_c…, 0…])` at the channel's tuple
  /// length (4 on a lane bus, `W` on a row bus).
  fn stacked_circuit(
    &self,
    t: &Stacked,
    buses: &[(Scalar, bool)],
    fixed: RowMajorMatrix<Scalar>,
  ) -> CircuitInputs<Scalar> {
    let w = self.config.width;
    let var = |v: usize| {
      if v < t.main_width {
        Expr::main(index(v))
      } else {
        Expr::preprocessed(index(v - t.main_width))
      }
    };
    let lookups = (0..t.slices.len())
      .map(|c| {
        let code = t.code(c);
        let lane = buses.iter().find(|b| b.0 == code).is_some_and(|b| b.1);
        let len = if lane { 4 } else { w };
        let mut args = vec![Expr::constant(code)];
        if t.chunked() {
          args.push(var(t.key_col()));
        }
        args.extend(t.slices[c].iter().map(|&v| var(v)));
        args.resize(len.max(args.len()), Expr::constant(Scalar::ZERO));
        Lookup::pull(var(t.sel_col()) * var(0), args)
      })
      .collect();
    let mut input = CircuitInputs {
      main_width: t.main_width,
      preprocessed: Some(fixed),
      lookups,
      ..Default::default()
    };
    input.lookup_group_size = group_size(&input, self.config.lookup_budget);
    input
  }

  /// The shared narrow fixed matrix (local ids and labels).
  pub fn narrow_fixed(&self) -> RowMajorMatrix<Scalar> {
    let c = self.cols();
    let fw = c.width();
    let mut values = vec![Scalar::ZERO; fw * self.height];
    for (f, (t, region)) in self.templates.iter().zip(&self.regions).enumerate()
    {
      let tr = t.rows.len();
      let n = self.per_shard[f];
      // Per template row: the instance-independent fixed row, the occupied
      // cells (each carries its slot's copy label, `System.labelAt`), and
      // whether the row holds the receive key.
      let roles = copy_roles(t);
      let rows: Vec<(Vec<Scalar>, Vec<(usize, u64)>, bool)> = t
        .rows
        .iter()
        .enumerate()
        .map(|(r, row)| {
          let mut out = vec![Scalar::ZERO; fw];
          let mut key = false;
          match row {
            Row::Gate { lanes, spans } => {
              for (m, lane) in lanes.iter().enumerate() {
                match lane {
                  LaneUse::Empty => {},
                  LaneUse::Gate { qm, q, qc, .. } => {
                    let b = c.lane(m);
                    out[b] = *qm;
                    out[b + 1..b + 5].copy_from_slice(q);
                    out[b + 5] = *qc;
                  },
                  LaneUse::Message { ts, mk, mc, .. } => {
                    let b = c.lane_msg(m);
                    out[b] = *ts;
                    out[b + 1] = *mk;
                    out[b + 2] = *mc;
                  },
                }
              }
              for &(start, len) in spans {
                for n in start..start + len {
                  out[c.flag(start, n)] = Scalar::ONE;
                }
              }
            },
            Row::Message { ts, mk, mc, receive_key, .. } => {
              let b = c.row_msg();
              out[b] = *ts;
              out[b + 1] = *mk;
              out[b + 2] = *mc;
              if *receive_key {
                key = true;
                out[b + 4] = Scalar::ONE;
                // `x1 = 0`: lane 0's linear part is `x1`, its own span.
                out[c.lane(0) + 2] = Scalar::ONE;
                out[c.flag(0, 0)] = Scalar::ONE;
              }
            },
          }
          let mut labels = vec![];
          for (j, cell) in row.cells().iter().enumerate() {
            if let Some(slot) = cell {
              out[c.mults() + j] = roles[r][j];
              labels.push((j, u64::from(*slot)));
            }
          }
          (out, labels, key)
        })
        .collect();
      let first = region.row_base;
      values[first * fw..(first + n * tr) * fw]
        .par_chunks_mut(fw)
        .enumerate()
        .for_each(|(i, out)| {
          let instance = i / tr;
          let (base, labels, key) = &rows[i % tr];
          out.copy_from_slice(base);
          let label0 =
            region.label_base + instance as u64 * t.logical_slots as u64;
          for &(j, slot) in labels {
            out[c.labels() + j] = Scalar::from_u64(label0 + slot);
          }
          if *key {
            out[c.row_msg() + 3] =
              Scalar::from_u64(region.id_base + instance as u64);
          }
        });
    }
    RowMajorMatrix::new(values, fw)
  }

  pub fn circuit_names(&self) -> Vec<String> {
    let mut n: Vec<String> =
      (0..self.shards).map(|s| format!("narrow[{s}]")).collect();
    if self.compact().is_some() {
      n.extend(["compact-map".to_string(), "compact-rom".to_string()]);
      return n;
    }
    n.extend(self.stacked().iter().map(|t| match t.source {
      TableSource::Map(_) => format!("map[{}]", t.sub),
      TableSource::Rom(_) => format!("rom[{}]", t.sub),
    }));
    n
  }

  /// Circuits and, per circuit, the earlier circuit whose fixed matrix it
  /// reads (`multi_stark::system::System::new_shared`): the shards, then the
  /// stacked tables.
  pub fn circuit_inputs(
    &self,
  ) -> (Vec<CircuitInputs<Scalar>>, Vec<Option<usize>>) {
    let fixed = match &self.lean {
      Some(l) => l.fixed.clone(),
      None => self.narrow_fixed(),
    };
    self.inputs_with(fixed)
  }

  /// [`Self::circuit_inputs`], moving an adopted Lean fixed matrix out of
  /// the backend instead of copying it.
  pub fn take_circuit_inputs(
    &mut self,
  ) -> (Vec<CircuitInputs<Scalar>>, Vec<Option<usize>>) {
    let fixed = match self.lean.as_mut() {
      Some(l) => {
        std::mem::replace(&mut l.fixed, RowMajorMatrix::new(vec![], 1))
      },
      None => self.narrow_fixed(),
    };
    self.inputs_with(fixed)
  }

  fn inputs_with(
    &self,
    fixed: RowMajorMatrix<Scalar>,
  ) -> (Vec<CircuitInputs<Scalar>>, Vec<Option<usize>>) {
    let budget = self.config.lookup_budget;
    let narrow =
      |s: usize, fixed: Option<RowMajorMatrix<Scalar>>| match &self.lean {
        Some(l) => l.narrow[s].circuit_inputs(fixed, budget),
        None => self.narrow_circuit(s, fixed),
      };
    let mut out = vec![narrow(0, Some(fixed))];
    let mut shared = vec![None];
    for s in 1..self.shards {
      out.push(narrow(s, None));
      shared.push(Some(0));
    }
    if let Some(tables) = self.compact() {
      let graphs = &self
        .lean
        .as_ref()
        .expect("compact tables come from a Lean export")
        .compact_circuits;
      for (t, g) in tables.iter().zip(graphs) {
        out.push(g.circuit_inputs(Some(t.fixed.clone()), budget));
        shared.push(None);
      }
      return (out, shared);
    }
    let buses = self.buses();
    for t in self.stacked() {
      out.push(self.stacked_circuit(&t, &buses, self.stacked_fixed(&t)));
      shared.push(None);
    }
    (out, shared)
  }

  /// The adopted compact tables, if the Lean export has them.
  pub fn compact(&self) -> Option<&[CompactTable; 2]> {
    self.lean.as_ref().and_then(|l| l.compact.as_ref())
  }

  /// `Compact.circuit`: no constraints; the lookups are
  /// `push(−selL·count, [code, cell₀, cell₁, cell₂])` and
  /// `push(−selW·count, [code, cell₀, …, cell_{W−2}])`, where cell `j` is
  /// fixed column `3 + j` for `j < n` and main column `1 + j − n` otherwise.
  fn compact_circuit(
    &self,
    t: &CompactTable,
    fixed: RowMajorMatrix<Scalar>,
  ) -> CircuitInputs<Scalar> {
    let w = self.config.width;
    let n = t.n_fixed;
    let cell = |j: usize| {
      if j < n {
        Expr::preprocessed(index(3 + j))
      } else {
        Expr::main(index(1 + j - n))
      }
    };
    let code = Expr::preprocessed(2);
    let count = Expr::main(0);
    let lane = std::iter::once(code.clone()).chain((0..3).map(cell)).collect();
    let row = std::iter::once(code).chain((0..w - 1).map(cell)).collect();
    let lookups = vec![
      Lookup::pull(Expr::preprocessed(0) * count.clone(), lane),
      Lookup::pull(Expr::preprocessed(1) * count, row),
    ];
    let mut input = CircuitInputs {
      main_width: t.main_width,
      preprocessed: Some(fixed),
      lookups,
      ..Default::default()
    };
    input.lookup_group_size = group_size(&input, self.config.lookup_budget);
    input
  }

  /// Replaces the stacked-table traces at the end of `traces` (as
  /// [`Self::witness`] builds them) by the compact tables' traces. Rows
  /// follow the export: map claims in table order, then ROM entries by width
  /// and address, a chunked part's rows in chunk order. Each row's code and
  /// fixed cells are checked against the exported fixed row before its count
  /// and words are written, so a witness never disagrees with the export
  /// about which entry a row holds.
  pub fn compact_traces(
    &self,
    traces: &mut Vec<RowMajorMatrix<Scalar>>,
  ) -> Result<(), String> {
    let Some([map, rom]) = self.compact() else { return Ok(()) };
    let stacked = self.stacked();
    let start = traces
      .len()
      .checked_sub(stacked.len())
      .ok_or("fewer traces than stacked tables")?;
    let tables: Vec<RowMajorMatrix<Scalar>> = traces.split_off(start);
    let w = self.config.width;
    fn fixed_row(t: &CompactTable, r: usize) -> Result<&[Scalar], String> {
      if r >= t.rows {
        return Err("compact table has fewer rows than its parts".into());
      }
      let fw = t.fixed.width;
      Ok(&t.fixed.values[r * fw..(r + 1) * fw])
    }
    // Map table: one count column.
    let mut counts = vec![Scalar::ZERO; map.height()];
    let mut r = 0;
    for (t, trace) in stacked.iter().zip(&tables) {
      let TableSource::Map(mi) = t.source else { continue };
      let claims = &self.maps[mi].rows;
      for (i, payload) in claims.iter().enumerate() {
        let count = trace.values[i];
        let chunks = if payload.len() < w {
          None
        } else {
          Some(payload.chunks(w - 2).collect::<Vec<_>>())
        };
        match chunks {
          None => {
            let f = fixed_row(map, r)?;
            let mut cells = payload.clone();
            cells.resize(w - 1, Scalar::ZERO);
            if f[2] != ts(CALL, t.sub) || f[3..3 + w - 1] != cells[..] {
              return Err(format!(
                "compact map row {r} is not claim {i} of map {}",
                t.sub
              ));
            }
            counts[r] = count;
            r += 1;
          },
          Some(chunks) => {
            let key = Scalar::from_u64(t.key_base + i as u64);
            for (c, chunk) in chunks.iter().enumerate() {
              let f = fixed_row(map, r)?;
              let mut cells = vec![key];
              cells.extend_from_slice(chunk);
              cells.resize(w - 1, Scalar::ZERO);
              if f[2] != t.code(c) || f[3..3 + w - 1] != cells[..] {
                return Err(format!(
                  "compact map row {r} is not chunk {c} of claim {i} of map {}",
                  t.sub
                ));
              }
              counts[r] = count;
              r += 1;
            }
          },
        }
      }
    }
    if r != map.rows {
      return Err(format!(
        "compact map table has {} rows, the claims {r}",
        map.rows
      ));
    }
    // ROM table: the count, then cells 1 … W − 2 (the words).
    let mw = rom.main_width;
    if mw != w - 1 || rom.n_fixed != 1 {
      return Err("compact ROM table shape".into());
    }
    let mut values = vec![Scalar::ZERO; rom.height() * mw];
    let mut r = 0;
    for (t, trace) in stacked.iter().zip(&tables) {
      let TableSource::Rom(_) = t.source else { continue };
      let width = t.main_width - 1;
      let nrows = if width + 2 <= w { 1 } else { width.div_ceil(w - 2) };
      for a in 0..t.rows {
        let src = &trace.values[a * t.main_width..(a + 1) * t.main_width];
        let words = &src[1..];
        for c in 0..nrows {
          let f = fixed_row(rom, r)?;
          let code = if nrows == 1 { ts(ROM, t.sub) } else { t.code(c) };
          if f[2] != code || f[3] != Scalar::from_u64(a as u64) {
            return Err(format!(
              "compact ROM row {r} is not chunk {c} of address {a} of width {width}"
            ));
          }
          let out = &mut values[r * mw..(r + 1) * mw];
          out[0] = src[0];
          let part = if nrows == 1 {
            words
          } else {
            &words[c * (w - 2)..width.min((c + 1) * (w - 2))]
          };
          out[1..1 + part.len()].copy_from_slice(part);
          r += 1;
        }
      }
    }
    if r != rom.rows {
      return Err(format!(
        "compact ROM table has {} rows, the ROM {r}",
        rom.rows
      ));
    }
    traces.push(RowMajorMatrix::new(counts, 1));
    traces.push(RowMajorMatrix::new(values, mw));
    Ok(())
  }

  /// Dimensions without materializing fixed columns; the shared fixed
  /// matrix is counted once.
  pub fn counts(&self) -> Vec<CircuitCount> {
    let dummy = |w: usize| RowMajorMatrix::new(vec![Scalar::ZERO; w], w);
    let mut narrow = count(
      "narrow",
      &self.narrow_circuit(0, Some(dummy(self.cols().width()))),
      self.rows_per_shard * self.shards,
      vec![self.height; self.shards],
    );
    let fixed = narrow.fixed;
    narrow.evaluations -= (self.shards - 1) * fixed;
    narrow.fixed_cells = fixed * self.height;
    let buses = self.buses();
    let names = self.circuit_names();
    let mut out = vec![narrow];
    for (t, name) in self.stacked().iter().zip(&names[self.shards..]) {
      let fw = match t.source {
        TableSource::Map(mi) => t.fixed_width(&self.maps[mi].rows),
        TableSource::Rom(_) => 2,
      };
      out.push(count(
        name,
        &self.stacked_circuit(t, &buses, dummy(fw)),
        t.rows,
        vec![t.height()],
      ));
    }
    out
  }

  fn instances(
    &self,
    wide: &[RowMajorMatrix<Scalar>],
    raw: &[usize],
  ) -> Result<Vec<Vec<Vec<usize>>>, String> {
    let nf = self.templates.len();
    let mut out: Vec<Vec<Vec<usize>>> = (0..nf)
      .map(|f| (0..raw[f].min(wide[f].height())).map(|r| vec![r]).collect())
      .collect();
    if let Some(u) = &self.unrolled {
      let g = &self.graphs[u.circuit];
      let m = &wide[u.circuit];
      let rows: Vec<&[Scalar]> = (0..raw[u.circuit].min(m.height()))
        .map(|r| &m.values[r * m.width..(r + 1) * m.width])
        .collect();
      let recv: Vec<NodeId> = g.lookups[0].args[2..].to_vec();
      let call: Vec<NodeId> = g.lookups[u.selfcall].args[2..].to_vec();
      let by_payload: HashMap<Vec<Scalar>, usize> = rows
        .par_iter()
        .enumerate()
        .map(|(r, row)| (eval_graph(g, row, &recv), r))
        .collect();
      let starts: Vec<usize> = (0..rows.len())
        .filter(|&r| {
          rows[r][u.stage_col] == Scalar::ZERO
            && rows[r][u.act_col] == Scalar::ONE
        })
        .collect();
      let chains = starts
        .par_iter()
        .map(|&r0| {
          let mut chain = vec![r0];
          for s in 0..u.stages {
            let r = *chain.last().unwrap();
            if rows[r][u.sel_col] != Scalar::from_bool(s + 1 < u.stages)
              || rows[r][u.act_col] != Scalar::ONE
              || (s > 0 && rows[r][u.recv_mult_col] != Scalar::ONE)
            {
              return Err(format!(
                "compression stage {s} does not match its unrolled body"
              ));
            }
            if s + 1 < u.stages {
              let next = eval_graph(g, rows[r], &call);
              chain.push(
                *by_payload
                  .get(&next)
                  .ok_or("compression self-call without a callee row")?,
              );
            }
          }
          Ok(chain)
        })
        .collect::<Result<Vec<_>, String>>()?;
      out[u.circuit] = chains;
    }
    Ok(out)
  }

  fn slot_values(
    &self,
    f: usize,
    rows: &[&[Scalar]],
    zero: bool,
  ) -> Vec<Scalar> {
    let t = &self.templates[f];
    let mut v = vec![Scalar::ZERO; t.slots.len()];
    for (s, def) in t.slots.iter().enumerate() {
      v[s] = match def {
        SlotDef::Column { body, col } => {
          if zero {
            Scalar::ZERO
          } else {
            rows[*body][*col]
          }
        },
        SlotDef::Sum(terms, k) => evaluate(terms, *k, &v),
        SlotDef::Key(_) => Scalar::ZERO,
      };
    }
    v
  }

  /// Rejects an execution that exceeds a configured capacity.
  pub fn admit(
    &self,
    instances: &[Vec<Vec<usize>>],
    record: &Execution<Bn254>,
  ) -> Result<(), String> {
    for (f, inst) in instances.iter().enumerate() {
      if inst.len() > self.per_shard[f] * self.shards {
        return Err(format!(
          "{}: {} instances exceed capacity",
          self.compiler.names()[f],
          inst.len()
        ));
      }
    }
    let raw = self.compiler.raw_row_counts(record)?;
    let rom_start = raw.len() - self.memory_widths.len();
    for (b, &cap) in self.config.rom_capacities.iter().enumerate() {
      if raw[rom_start + b] > cap {
        return Err(format!(
          "ROM width {}: objects exceed capacity",
          self.memory_widths[b]
        ));
      }
    }
    Ok(())
  }

  /// `(shard, local instance)` of the `n`-th instance of `f`.
  pub fn place_of(&self, f: usize, n: usize) -> (usize, usize) {
    (n / self.per_shard[f], n % self.per_shard[f])
  }

  pub fn global_id(&self, f: usize, n: usize) -> Scalar {
    let (s, i) = self.place_of(f, n);
    Scalar::from_u64(self.id_offset(s) + self.regions[f].id_base + i as u64)
  }

  /// Public claims in narrow tuple form: `[CALL + 4f, payload]`, or keyed
  /// chunks under `key` (the entry instance's global id).
  pub fn claims(&self, claim: &[Scalar], key: Scalar) -> Vec<Vec<Scalar>> {
    let w = self.config.width;
    let f = claim[1].canonical_u64().unwrap_or(u64::MAX);
    if claim.len() - 2 < w {
      let mut c = vec![ts(CALL, f)];
      c.extend_from_slice(&claim[2..]);
      return vec![c];
    }
    claim[2..]
      .chunks(w - 2)
      .enumerate()
      .map(|(j, chunk)| {
        let mut c = vec![ts(CALL, f + (j as u64 + 1) * CHUNK_STRIDE), key];
        c.extend_from_slice(chunk);
        c
      })
      .collect()
  }

  /// Narrow main traces (in [`Self::circuit_inputs`] order) and the entry
  /// instance's global id.
  pub fn witness(
    &self,
    record: &Execution<Bn254>,
    entry: &str,
    args: &[Scalar],
  ) -> Result<(Vec<RowMajorMatrix<Scalar>>, Scalar), String> {
    let wide = self.compiler.generate(record, entry, args)?;
    self.witness_from_wide(&wide, entry, args, record)
  }

  pub fn witness_from_wide(
    &self,
    wide: &[RowMajorMatrix<Scalar>],
    entry: &str,
    args: &[Scalar],
    record: &Execution<Bn254>,
  ) -> Result<(Vec<RowMajorMatrix<Scalar>>, Scalar), String> {
    let w = self.config.width;
    let nf = self.templates.len();
    let raw = self.compiler.raw_row_counts(record)?;
    let mut instances = self.instances(wide, &raw)?;
    self.admit(&instances, record)?;
    let row_of = |f: usize, rows: &[usize]| -> Vec<&[Scalar]> {
      let m = &wide[f];
      rows.iter().map(|&r| &m.values[r * m.width..(r + 1) * m.width]).collect()
    };
    let claim = self.plan.public_claim(
      entry,
      &self.plan.public_args(record, entry, args)?,
      &record.output,
    )?;
    if let Some(f) = self.entry_circuit {
      if self.config.entry.as_deref() != Some(entry) {
        return Err(format!(
          "the layout's entry is {:?}, not {entry}",
          self.config.entry
        ));
      }
      let recv = &self.templates[f].messages[0];
      let root = instances[f]
        .iter()
        .position(|rows| {
          let v = self.slot_values(f, &row_of(f, rows), false);
          recv.multiplicity(&v) != Scalar::ZERO
            && recv
              .payload
              .iter()
              .map(|&p| v[p as usize])
              .eq(claim[2..].iter().copied())
        })
        .ok_or("no instance of the entry function receives the claim")?;
      instances[f].swap(0, root);
    }
    // Receive payload → global id, for every chunked receive.
    let mut call_keys: HashMap<usize, HashMap<Vec<Scalar>, Scalar>> =
      HashMap::new();
    for (f, (t, instances)) in self.templates.iter().zip(&instances).enumerate()
    {
      if t.messages[0].target != Target::Receive
        || t.messages[0].placement != Placement::Chunked
      {
        continue;
      }
      let m = &t.messages[0];
      let h = instances
        .par_iter()
        .enumerate()
        .filter_map(|(n, rows)| {
          let v = self.slot_values(f, &row_of(f, rows), false);
          (m.multiplicity(&v) != Scalar::ZERO).then(|| {
            (
              m.payload.iter().map(|&p| v[p as usize]).collect::<Vec<_>>(),
              self.global_id(f, n),
            )
          })
        })
        .collect();
      call_keys.insert(f, h);
    }
    let map_index: HashMap<usize, (usize, HashMap<&[Scalar], usize>)> = self
      .maps
      .iter()
      .enumerate()
      .map(|(mi, m)| {
        (
          m.callable,
          (
            mi,
            m.rows.iter().enumerate().map(|(r, p)| (p.as_slice(), r)).collect(),
          ),
        )
      })
      .collect();
    let map_ids = self.map_id_bases();
    // Values of every instance, padding included; the padding copy of a
    // real instance receives nothing.
    let per_instance = |f: usize, n: usize| -> Result<Vec<Scalar>, String> {
      let t = &self.templates[f];
      let mut v = if n < instances[f].len() {
        self.slot_values(f, &row_of(f, &instances[f][n]), false)
      } else if self.copy_padding[f] {
        let rows = instances[f].first().ok_or_else(|| {
          format!(
            "{}: padding needs one real instance",
            self.compiler.names()[f]
          )
        })?;
        let mut v = self.slot_values(f, &row_of(f, rows), false);
        if let Some(m) = t.messages[0].mult {
          v[m as usize] = Scalar::ZERO;
          for (s, def) in t.slots.iter().enumerate() {
            if let SlotDef::Sum(terms, k) = def {
              v[s] = evaluate(terms, *k, &v);
            }
          }
        }
        if t.messages.iter().any(|m| {
          matches!(m.target, Target::Call(_) | Target::Rom(_))
            && m.multiplicity(&v) != Scalar::ZERO
        }) {
          return Err("copy padding would send calls".into());
        }
        v
      } else {
        self.slot_values(f, &[], true)
      };
      for (mi, m) in t.messages.iter().enumerate() {
        let Some(k) = m.key else { continue };
        if !matches!(t.slots[k as usize], SlotDef::Key(x) if x == mi)
          || m.multiplicity(&v) == Scalar::ZERO
        {
          continue;
        }
        let payload: Vec<Scalar> =
          m.payload.iter().map(|&p| v[p as usize]).collect();
        v[k as usize] = match m.target {
          Target::Call(c) => *call_keys
            .get(&self.callee_circuit[c])
            .and_then(|h| h.get(&payload))
            .ok_or("chunked call without a callee instance")?,
          Target::Map(c) => {
            let (mi, h) =
              map_index.get(&c).ok_or("chunked map call without a table")?;
            let r = h
              .get(payload.as_slice())
              .ok_or("chunked map call outside its table")?;
            Scalar::from_u64(map_ids[*mi] + *r as u64)
          },
          _ => return Err("unexpected key target".into()),
        };
      }
      Ok(v)
    };
    let mut table_counts: Vec<Vec<Scalar>> =
      self.maps.iter().map(|m| vec![Scalar::ZERO; m.rows.len()]).collect();
    let mut rom_counts: Vec<HashMap<u64, Scalar>> =
      vec![HashMap::new(); self.memory_widths.len()];
    let mut traces = vec![];
    for s in 0..self.shards {
      let mut values = vec![Scalar::ZERO; self.height * w];
      for f in 0..nf {
        let t = &self.templates[f];
        let tr = t.rows.len();
        let per = self.per_shard[f];
        let region = &self.regions[f];
        let filled = (0..per)
          .into_par_iter()
          .map(
            |i| -> Result<
              (Vec<Scalar>, Vec<(usize, Vec<Scalar>, Scalar)>),
              String,
            > {
              let v = per_instance(f, s * per + i)?;
              let mut cells = vec![Scalar::ZERO; tr * w];
              for (r, row) in t.rows.iter().enumerate() {
                for (j, cell) in row.cells().iter().enumerate() {
                  if let Some(x) = cell {
                    cells[r * w + j] = v[*x as usize];
                  }
                }
              }
              let sends = t
                .messages
                .iter()
                .filter(|m| matches!(m.target, Target::Map(_) | Target::Rom(_)))
                .filter_map(|m| {
                  let mult = m.multiplicity(&v);
                  (mult != Scalar::ZERO).then(|| {
                    let id = match m.target {
                      Target::Map(c) | Target::Rom(c) => c,
                      _ => unreachable!(),
                    };
                    let kind = usize::from(matches!(m.target, Target::Rom(_)));
                    (
                      2 * id + kind,
                      m.payload.iter().map(|&p| v[p as usize]).collect(),
                      mult,
                    )
                  })
                })
                .collect();
              Ok((cells, sends))
            },
          )
          .collect::<Result<Vec<_>, String>>()?;
        for (i, (cells, sends)) in filled.into_iter().enumerate() {
          let at = (region.row_base + i * tr) * w;
          values[at..at + tr * w].copy_from_slice(&cells);
          for (key, payload, mult) in sends {
            let id = key / 2;
            if key % 2 == 1 {
              let b = self
                .memory_widths
                .iter()
                .position(|&x| x == id)
                .ok_or("ROM width without a circuit")?;
              let addr = payload[0]
                .canonical_u64()
                .ok_or("non-canonical ROM address")?;
              *rom_counts[b].entry(addr).or_insert(Scalar::ZERO) += mult;
            } else {
              let (mi, h) = map_index.get(&id).ok_or("map without a table")?;
              let r = h
                .get(payload.as_slice())
                .ok_or("map call outside its table")?;
              table_counts[*mi][*r] += mult;
            }
          }
        }
      }
      traces.push(RowMajorMatrix::new(values, w));
    }
    let rom_start = wide.len() - self.memory_widths.len();
    for t in self.stacked() {
      let height = t.height();
      match t.source {
        TableSource::Map(mi) => {
          let mut counts = vec![Scalar::ZERO; height];
          counts[..t.rows].copy_from_slice(&table_counts[mi]);
          traces.push(RowMajorMatrix::new(counts, 1));
        },
        TableSource::Rom(b) => {
          let width = self.memory_widths[b];
          let m = &wide[rom_start + b];
          let mut rom = vec![Scalar::ZERO; height * t.main_width];
          rom.par_chunks_mut(t.main_width).take(t.rows).enumerate().for_each(
            |(addr, out)| {
              out[0] = rom_counts[b]
                .get(&(addr as u64))
                .copied()
                .unwrap_or(Scalar::ZERO);
              if addr < m.height() {
                let src = &m.values[addr * m.width..(addr + 1) * m.width];
                for (k, &x) in src[3..].iter().take(width).enumerate() {
                  out[1 + k] = x;
                }
              }
            },
          );
          traces.push(RowMajorMatrix::new(rom, t.main_width));
        },
      }
    }

    let claim_key = {
      let id = self.plan.program().entry(entry)?.function;
      let f = self.callee_circuit[id];
      call_keys
        .get(&f)
        .and_then(|h| h.get(&claim[2..]))
        .copied()
        .unwrap_or(Scalar::ZERO)
    };
    Ok((traces, claim_key))
  }

  /// Every cell `(circuit, row, column)` holding `slot` of the `n`-th
  /// instance of function `f`.
  pub fn cells_of(
    &self,
    f: usize,
    n: usize,
    slot: u32,
  ) -> Vec<(usize, usize, usize)> {
    let t = &self.templates[f];
    let (s, i) = self.place_of(f, n);
    let base = self.regions[f].row_base + i * t.rows.len();
    let mut out = vec![];
    for (r, row) in t.rows.iter().enumerate() {
      for (c, cell) in row.cells().iter().enumerate() {
        if *cell == Some(slot) {
          out.push((s, base + r, c));
        }
      }
    }
    out
  }

  /// `(shard, first row)` of the `n`-th instance of `f`.
  pub fn instance(&self, f: usize, n: usize) -> (usize, usize) {
    let (s, i) = self.place_of(f, n);
    (s, self.regions[f].row_base + i * self.templates[f].rows.len())
  }

  pub fn compress_circuit(&self) -> Option<usize> {
    self.unrolled.as_ref().map(|u| u.circuit)
  }
}

fn lane_value(l: &LaneUse, v: &[Scalar]) -> Scalar {
  match l {
    LaneUse::Gate { qm, q, qc, cells } => {
      let x = |i: usize| cells[i].map_or(Scalar::ZERO, |s| v[s as usize]);
      *qm * x(0) * x(1)
        + q[0] * x(0)
        + q[1] * x(1)
        + q[2] * x(2)
        + q[3] * x(3)
        + *qc
    },
    _ => Scalar::ZERO,
  }
}

/// Copy multiplicity of every template cell: a slot with `o > 1` cells has
/// `o − 1` at its first cell and `−1` at the others; single cells have 0.
fn copy_roles(t: &Template) -> Vec<Vec<Scalar>> {
  let mut seen = vec![false; t.slots.len()];
  t.rows
    .iter()
    .map(|row| {
      row
        .cells()
        .iter()
        .map(|cell| match cell {
          Some(s) if t.occurrences[*s as usize] > 1 => {
            if std::mem::replace(&mut seen[*s as usize], true) {
              -Scalar::ONE
            } else {
              Scalar::from_u64(u64::from(t.occurrences[*s as usize] - 1))
            }
          },
          _ => Scalar::ZERO,
        })
        .collect()
    })
    .collect()
}
