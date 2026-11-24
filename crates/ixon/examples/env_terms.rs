//! Dump the terms of a serialized `.ixe` environment as flat term graphs, the
//! form a model that reads terms consumes.
//!
//! ```text
//! env_terms ENV.ixe OUT-DIR [--value-cap N]
//! ```
//!
//! Every stored constant gets an id: its rank among the environment's
//! addresses in byte order. A constant that holds expressions (a definition,
//! recursor, axiom, quotient or mutual block) is an *owner*: its expressions
//! are hash-consed into one graph, with `Share` references resolved, so equal
//! subterms of an owner are one node. A projection into a mutual block has no
//! graph of its own and points into its block's.
//!
//! Files written to `OUT-DIR`:
//!
//! * `nodes.bin`: the owners' graphs one after another, each node four
//!   little-endian `u32` words `tag a b c`. Child references are indices
//!   relative to the owner's first node, and a child always precedes its
//!   parent.
//!
//!   | tag | node | `a` | `b` | `c` |
//!   |---|---|---|---|---|
//!   | 0 | sort | universe code | | |
//!   | 1 | bound variable | de Bruijn index | | |
//!   | 2 | constant | constant id | | |
//!   | 3 | block member | constant id | member index | |
//!   | 4 | projection | structure's constant id | field | value |
//!   | 5 | string literal | | | |
//!   | 6 | number literal | magnitude code | | |
//!   | 7 | application | function | argument | |
//!   | 8 | lambda | binder type | body | |
//!   | 9 | forall | domain | body | |
//!   | 10 | let | type | value | body |
//!
//!   A constant id of `u32::MAX` is a reference the environment does not
//!   hold. The universe code is `n` for the `n`-th successor of zero up to
//!   14, then 15 a parameter, 16 a maximum, 17 an impredicative maximum and
//!   18 the successor of one of those. The magnitude code of a number is its
//!   value below 65536, and above that 65536 plus the length of its blob in
//!   bytes.
//!
//! * `consts.tsv`: one row per constant, in id order:
//!   `id addr kind safety lvls owner member ctor node_start node_count
//!   type_root value_root value_size`. `kind` is `def`, `opaque`, `thm`,
//!   `axiom`, `quot`, `rec`, `ind`, `ctor` or `block`; `safety` is 0 safe, 1
//!   unsafe, 2 partial; `owner` is the id of the constant whose graph holds
//!   the roots; `member` and `ctor` are the indices of a block member and of
//!   its constructor, or -1; `node_start` and `node_count` locate an owner's
//!   graph in `nodes.bin` and are 0 for other rows; the roots are indices
//!   into the owner's graph, or -1. A theorem's value is never written, and a
//!   definition's only when it has at most `--value-cap` nodes (4096 by
//!   default); `value_size` is the value's node count either way, counting a
//!   shared subterm once.
//!
//! * `trefs.tsv` and `vrefs.tsv`: `id<TAB>id id …`, the constants a
//!   constant's type and value refer to, ascending. For a theorem the second
//!   is the set of constants its proof uses.

use ix_common::{address::Address, env::DefinitionSafety};
use ixon::{
  Constant, ConstantInfo, Env, Expr, Univ,
  constant::{
    DefKind, Definition, MutConst, defn_proj_address, indc_proj_address,
    recr_proj_address,
  },
};
use rustc_hash::FxHashMap;
use std::{
  fs::File,
  io::{BufWriter, Write},
  path::Path,
  sync::Arc,
};

const NONE: u32 = u32::MAX;

const SORT: u32 = 0;
const VAR: u32 = 1;
const REF: u32 = 2;
const REC: u32 = 3;
const PRJ: u32 = 4;
const STR: u32 = 5;
const NAT: u32 = 6;
const APP: u32 = 7;
const LAM: u32 = 8;
const ALL: u32 = 9;
const LET: u32 = 10;

fn word(x: u64) -> u32 {
  u32::try_from(x).unwrap_or(NONE)
}

fn index(x: usize) -> u32 {
  u32::try_from(x).unwrap_or(NONE)
}

fn signed(x: u32) -> i64 {
  if x == NONE { -1 } else { i64::from(x) }
}

fn univ_code(u: &Univ) -> u32 {
  let mut depth = 0u32;
  let mut cur = u;
  loop {
    match cur {
      Univ::Zero => return depth.min(14),
      Univ::Succ(inner) => {
        depth += 1;
        cur = inner;
      },
      Univ::Var(_) | Univ::Max(..) | Univ::IMax(..) if depth > 0 => return 18,
      Univ::Var(_) => return 15,
      Univ::Max(..) => return 16,
      Univ::IMax(..) => return 17,
    }
  }
}

fn safety_code(safety: DefinitionSafety) -> u8 {
  match safety {
    DefinitionSafety::Safe => 0,
    DefinitionSafety::Unsafe => 1,
    DefinitionSafety::Partial => 2,
  }
}

/// One owner's hash-consed graph, and the tables its expressions index.
struct Graph<'a> {
  env: &'a Env,
  ids: &'a FxHashMap<Address, u32>,
  constant: &'a Constant,
  /// Constant id of each member a `Rec` index names.
  rec_ids: Vec<u32>,
  nodes: Vec<[u32; 4]>,
  cons: FxHashMap<[u32; 4], u32>,
  /// Node of each sharing-table entry already written.
  shares: Vec<u32>,
}

impl<'a> Graph<'a> {
  fn new(
    env: &'a Env,
    ids: &'a FxHashMap<Address, u32>,
    constant: &'a Constant,
    rec_ids: Vec<u32>,
  ) -> Self {
    Graph {
      env,
      ids,
      constant,
      rec_ids,
      nodes: Vec::new(),
      cons: FxHashMap::default(),
      shares: vec![NONE; constant.sharing.len()],
    }
  }

  fn node(&mut self, key: [u32; 4]) -> u32 {
    if let Some(&at) = self.cons.get(&key) {
      return at;
    }
    let at = index(self.nodes.len());
    self.nodes.push(key);
    self.cons.insert(key, at);
    at
  }

  fn ref_id(&self, r: u64) -> u32 {
    usize::try_from(r)
      .ok()
      .and_then(|r| self.constant.refs.get(r))
      .and_then(|addr| self.ids.get(addr))
      .copied()
      .unwrap_or(NONE)
  }

  fn rec_id(&self, i: u64) -> u32 {
    usize::try_from(i)
      .ok()
      .and_then(|i| self.rec_ids.get(i))
      .copied()
      .unwrap_or(NONE)
  }

  fn nat_code(&self, r: u64) -> u32 {
    let blob = usize::try_from(r)
      .ok()
      .and_then(|r| self.constant.refs.get(r))
      .and_then(|addr| self.env.get_blob(addr));
    match blob {
      None => NONE,
      Some(bytes) => {
        let significant =
          bytes.iter().rposition(|b| *b != 0).map_or(0, |last| last + 1);
        if significant <= 2 {
          bytes
            .iter()
            .take(significant)
            .rev()
            .fold(0u32, |acc, b| (acc << 8) | u32::from(*b))
        } else {
          65536 + index(significant)
        }
      },
    }
  }

  fn emit(&mut self, e: &Expr) -> u32 {
    match e {
      Expr::Sort(u) => {
        let code = usize::try_from(*u)
          .ok()
          .and_then(|u| self.constant.univs.get(u))
          .map_or(NONE, |u| univ_code(u));
        self.node([SORT, code, 0, 0])
      },
      Expr::Var(i) => self.node([VAR, word(*i), 0, 0]),
      Expr::Ref(r, _) => {
        let id = self.ref_id(*r);
        self.node([REF, id, 0, 0])
      },
      Expr::Rec(i, _) => {
        let id = self.rec_id(*i);
        self.node([REC, id, word(*i), 0])
      },
      Expr::Prj(ty, field, value) => {
        let value = self.emit(value);
        let id = self.ref_id(*ty);
        self.node([PRJ, id, word(*field), value])
      },
      Expr::Str(_) => self.node([STR, 0, 0, 0]),
      Expr::Nat(r) => {
        let code = self.nat_code(*r);
        self.node([NAT, code, 0, 0])
      },
      Expr::App(f, a) => {
        let f = self.emit(f);
        let a = self.emit(a);
        self.node([APP, f, a, 0])
      },
      Expr::Lam(_, ty, body) => {
        let ty = self.emit(ty);
        let body = self.emit(body);
        self.node([LAM, ty, body, 0])
      },
      Expr::All(_, _, dom, body) => {
        let dom = self.emit(dom);
        let body = self.emit(body);
        self.node([ALL, dom, body, 0])
      },
      Expr::Let(_, ty, value, body) => {
        let ty = self.emit(ty);
        let value = self.emit(value);
        let body = self.emit(body);
        self.node([LET, ty, value, body])
      },
      Expr::Share(i) => {
        let constant = self.constant;
        let Some(i) = usize::try_from(*i).ok().filter(|i| *i < self.shares.len())
        else {
          return self.node([REF, NONE, 0, 0]);
        };
        if self.shares[i] == NONE {
          let at = self.emit(&constant.sharing[i]);
          self.shares[i] = at;
        }
        self.shares[i]
      },
    }
  }

  /// The constants `e` refers to, and its node count with every sharing-table
  /// entry counted once. `seen` marks the entries already visited.
  fn scan(&self, e: &Expr, seen: &mut [bool], refs: &mut Vec<u32>) -> u64 {
    match e {
      Expr::Sort(_) | Expr::Var(_) | Expr::Str(_) | Expr::Nat(_) => 1,
      Expr::Ref(r, _) => {
        refs.push(self.ref_id(*r));
        1
      },
      Expr::Rec(i, _) => {
        refs.push(self.rec_id(*i));
        1
      },
      Expr::Prj(ty, _, value) => {
        refs.push(self.ref_id(*ty));
        1 + self.scan(value, seen, refs)
      },
      Expr::App(f, a) => 1 + self.scan(f, seen, refs) + self.scan(a, seen, refs),
      Expr::Lam(_, ty, body) | Expr::All(_, _, ty, body) => {
        1 + self.scan(ty, seen, refs) + self.scan(body, seen, refs)
      },
      Expr::Let(_, ty, value, body) => {
        1 + self.scan(ty, seen, refs)
          + self.scan(value, seen, refs)
          + self.scan(body, seen, refs)
      },
      Expr::Share(i) => {
        let Some(i) = usize::try_from(*i).ok().filter(|i| *i < seen.len()) else {
          return 0;
        };
        if seen[i] {
          return 0;
        }
        seen[i] = true;
        self.scan(&self.constant.sharing[i], seen, refs)
      },
    }
  }

  fn refs_of(&self, e: &Expr) -> (Vec<u32>, u64) {
    let mut seen = vec![false; self.constant.sharing.len()];
    let mut refs = Vec::new();
    let size = self.scan(e, &mut seen, &mut refs);
    refs.retain(|id| *id != NONE);
    refs.sort_unstable();
    refs.dedup();
    (refs, size)
  }
}

#[derive(Clone)]
struct Row {
  kind: &'static str,
  safety: u8,
  lvls: u64,
  owner: u32,
  member: i64,
  ctor: i64,
  node_start: u64,
  node_count: u32,
  type_root: u32,
  value_root: u32,
  value_size: u64,
}

impl Row {
  fn of(kind: &'static str, owner: u32) -> Self {
    Row {
      kind,
      safety: 0,
      lvls: 0,
      owner,
      member: -1,
      ctor: -1,
      node_start: 0,
      node_count: 0,
      type_root: NONE,
      value_root: NONE,
      value_size: 0,
    }
  }
}

/// A projection whose row is filled in from its block once the block is read.
enum Pending {
  Member { block: Address, idx: u64 },
  Ctor { block: Address, idx: u64, cidx: u64 },
}

struct Member {
  row: Row,
  ctors: Vec<Row>,
}

struct Out {
  nodes: BufWriter<File>,
  trefs: BufWriter<File>,
  vrefs: BufWriter<File>,
  written: u64,
  value_cap: u64,
}

impl Out {
  fn refs_line(
    out: &mut BufWriter<File>,
    id: u32,
    refs: &[u32],
  ) -> std::io::Result<()> {
    if id == NONE {
      return Ok(());
    }
    write!(out, "{id}\t")?;
    for (k, r) in refs.iter().enumerate() {
      if k > 0 {
        write!(out, " ")?;
      }
      write!(out, "{r}")?;
    }
    writeln!(out)
  }

  /// Write the type's graph and references under constant `id`.
  fn typ(
    &mut self,
    graph: &mut Graph<'_>,
    id: u32,
    typ: &Expr,
  ) -> std::io::Result<u32> {
    let (refs, _) = graph.refs_of(typ);
    Self::refs_line(&mut self.trefs, id, &refs)?;
    Ok(graph.emit(typ))
  }

  fn definition(
    &mut self,
    graph: &mut Graph<'_>,
    id: u32,
    owner: u32,
    d: &Definition,
  ) -> std::io::Result<Row> {
    let kind = match d.kind {
      DefKind::Definition => "def",
      DefKind::Opaque => "opaque",
      DefKind::Theorem => "thm",
    };
    let mut row = Row::of(kind, owner);
    row.safety = safety_code(d.safety);
    row.lvls = d.lvls;
    row.type_root = self.typ(graph, id, &d.typ)?;
    let (refs, size) = graph.refs_of(&d.value);
    Self::refs_line(&mut self.vrefs, id, &refs)?;
    row.value_size = size;
    if d.kind != DefKind::Theorem && size <= self.value_cap {
      row.value_root = graph.emit(&d.value);
    }
    Ok(row)
  }

  /// Append the owner's graph to `nodes.bin` and record where it lies.
  fn finish(&mut self, graph: &Graph<'_>, row: &mut Row) -> std::io::Result<()> {
    row.node_start = self.written;
    row.node_count = index(graph.nodes.len());
    for node in &graph.nodes {
      for w in node {
        self.nodes.write_all(&w.to_le_bytes())?;
      }
    }
    self.written += graph.nodes.len() as u64;
    Ok(())
  }
}

fn run(args: &[String]) -> Result<(), String> {
  let usage = "usage: env_terms ENV.ixe OUT-DIR [--value-cap N]";
  let path = args.get(1).ok_or(usage)?;
  let out_dir = Path::new(args.get(2).ok_or(usage)?);
  let value_cap = match args.iter().position(|a| a == "--value-cap") {
    Some(at) => args
      .get(at + 1)
      .and_then(|n| n.parse::<u64>().ok())
      .ok_or("--value-cap takes a number")?,
    None => 4096,
  };
  let io = |e: std::io::Error| e.to_string();

  let env = Env::get_anon_mmap(Path::new(path))?;
  let mut addrs: Vec<Address> =
    env.consts.iter().map(|entry| entry.key().clone()).collect();
  addrs.sort_unstable_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
  let ids: FxHashMap<Address, u32> =
    addrs.iter().enumerate().map(|(i, a)| (a.clone(), index(i))).collect();

  std::fs::create_dir_all(out_dir).map_err(io)?;
  let create = |name: &str| {
    File::create(out_dir.join(name)).map(BufWriter::new).map_err(io)
  };
  let mut out = Out {
    nodes: create("nodes.bin")?,
    trefs: create("trefs.tsv")?,
    vrefs: create("vrefs.tsv")?,
    written: 0,
    value_cap,
  };

  let mut rows: Vec<Option<Row>> = vec![None; addrs.len()];
  let mut pending: Vec<(u32, Pending)> = Vec::new();
  let mut members: FxHashMap<u32, Vec<Member>> = FxHashMap::default();

  for (i, addr) in addrs.iter().enumerate() {
    let id = index(i);
    let constant: Arc<Constant> = env
      .try_get_const(addr)
      .ok_or_else(|| format!("constant {} disappeared", addr.hex()))?
      .map_err(|e| format!("cannot parse constant {}: {e}", addr.hex()))?;
    match &constant.info {
      ConstantInfo::Defn(d) => {
        let mut graph = Graph::new(&env, &ids, &constant, vec![id]);
        let mut row = out.definition(&mut graph, id, id, d).map_err(io)?;
        out.finish(&graph, &mut row).map_err(io)?;
        rows[i] = Some(row);
      },
      ConstantInfo::Recr(r) => {
        let mut graph = Graph::new(&env, &ids, &constant, vec![id]);
        let mut row = Row::of("rec", id);
        row.safety = u8::from(r.is_unsafe);
        row.lvls = r.lvls;
        row.type_root = out.typ(&mut graph, id, &r.typ).map_err(io)?;
        out.finish(&graph, &mut row).map_err(io)?;
        rows[i] = Some(row);
      },
      ConstantInfo::Axio(a) => {
        let mut graph = Graph::new(&env, &ids, &constant, vec![id]);
        let mut row = Row::of("axiom", id);
        row.safety = u8::from(a.is_unsafe);
        row.lvls = a.lvls;
        row.type_root = out.typ(&mut graph, id, &a.typ).map_err(io)?;
        out.finish(&graph, &mut row).map_err(io)?;
        rows[i] = Some(row);
      },
      ConstantInfo::Quot(q) => {
        let mut graph = Graph::new(&env, &ids, &constant, vec![id]);
        let mut row = Row::of("quot", id);
        row.lvls = q.lvls;
        row.type_root = out.typ(&mut graph, id, &q.typ).map_err(io)?;
        out.finish(&graph, &mut row).map_err(io)?;
        rows[i] = Some(row);
      },
      ConstantInfo::Muts(muts) => {
        let member_id = |k: usize, m: &MutConst| {
          let k = k as u64;
          let proj = match m {
            MutConst::Defn(_) => defn_proj_address(k, addr),
            MutConst::Indc(_) => indc_proj_address(k, addr),
            MutConst::Recr(_) => recr_proj_address(k, addr),
          };
          ids.get(&proj).copied().unwrap_or(NONE)
        };
        let rec_ids: Vec<u32> =
          muts.iter().enumerate().map(|(k, m)| member_id(k, m)).collect();
        let mut graph = Graph::new(&env, &ids, &constant, rec_ids.clone());
        let mut table = Vec::with_capacity(muts.len());
        for (k, m) in muts.iter().enumerate() {
          let mid = rec_ids[k];
          let mut ctors = Vec::new();
          let mut row = match m {
            MutConst::Defn(d) => {
              out.definition(&mut graph, mid, id, d).map_err(io)?
            },
            MutConst::Recr(r) => {
              let mut row = Row::of("rec", id);
              row.safety = u8::from(r.is_unsafe);
              row.lvls = r.lvls;
              row.type_root = out.typ(&mut graph, mid, &r.typ).map_err(io)?;
              row
            },
            MutConst::Indc(ind) => {
              let mut row = Row::of("ind", id);
              row.safety = u8::from(ind.is_unsafe);
              row.lvls = ind.lvls;
              row.type_root = out.typ(&mut graph, mid, &ind.typ).map_err(io)?;
              for c in &ind.ctors {
                let cid = ids
                  .get(&ixon::constant::ctor_proj_address(k as u64, c.cidx, addr))
                  .copied()
                  .unwrap_or(NONE);
                let mut crow = Row::of("ctor", id);
                crow.safety = u8::from(c.is_unsafe);
                crow.lvls = c.lvls;
                crow.member = k as i64;
                crow.ctor = i64::try_from(c.cidx).unwrap_or(-1);
                crow.type_root = out.typ(&mut graph, cid, &c.typ).map_err(io)?;
                ctors.push(crow);
              }
              row
            },
          };
          row.member = k as i64;
          table.push(Member { row, ctors });
        }
        let mut row = Row::of("block", id);
        out.finish(&graph, &mut row).map_err(io)?;
        rows[i] = Some(row);
        members.insert(id, table);
      },
      ConstantInfo::DPrj(p) => {
        pending.push((id, Pending::Member { block: p.block.clone(), idx: p.idx }));
      },
      ConstantInfo::IPrj(p) => {
        pending.push((id, Pending::Member { block: p.block.clone(), idx: p.idx }));
      },
      ConstantInfo::RPrj(p) => {
        pending.push((id, Pending::Member { block: p.block.clone(), idx: p.idx }));
      },
      ConstantInfo::CPrj(p) => pending.push((
        id,
        Pending::Ctor { block: p.block.clone(), idx: p.idx, cidx: p.cidx },
      )),
    }
  }

  let mut unresolved = 0usize;
  for (id, p) in &pending {
    let (block, idx) = match p {
      Pending::Member { block, idx } | Pending::Ctor { block, idx, .. } => {
        (block, *idx)
      },
    };
    let member = ids
      .get(block)
      .and_then(|b| members.get(b))
      .and_then(|table| usize::try_from(idx).ok().and_then(|k| table.get(k)));
    let row = match (p, member) {
      (Pending::Member { .. }, Some(m)) => Some(m.row.clone()),
      (Pending::Ctor { cidx, .. }, Some(m)) => m
        .ctors
        .iter()
        .find(|c| c.ctor == i64::try_from(*cidx).unwrap_or(-1))
        .cloned(),
      (_, None) => None,
    };
    if row.is_none() {
      unresolved += 1;
    }
    rows[*id as usize] = row;
  }

  let mut consts = create("consts.tsv")?;
  let mut by_kind: FxHashMap<&'static str, usize> = FxHashMap::default();
  for (i, row) in rows.iter().enumerate() {
    let row = row.clone().unwrap_or_else(|| Row::of("unresolved", NONE));
    *by_kind.entry(row.kind).or_default() += 1;
    writeln!(
      consts,
      "{i}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
      addrs[i].hex(),
      row.kind,
      row.safety,
      row.lvls,
      signed(row.owner),
      row.member,
      row.ctor,
      row.node_start,
      row.node_count,
      signed(row.type_root),
      signed(row.value_root),
      row.value_size,
    )
    .map_err(io)?;
  }
  consts.flush().map_err(io)?;
  out.nodes.flush().map_err(io)?;
  out.trefs.flush().map_err(io)?;
  out.vrefs.flush().map_err(io)?;

  let mut kinds: Vec<_> = by_kind.into_iter().collect();
  kinds.sort_unstable();
  eprintln!("constants: {}", addrs.len());
  for (kind, count) in kinds {
    eprintln!("  {kind}: {count}");
  }
  eprintln!("nodes: {}", out.written);
  eprintln!("projections without a block member: {unresolved}");
  Ok(())
}

fn main() -> Result<(), String> {
  let args: Vec<String> = std::env::args().collect();
  // Expressions nest as deep as the proofs are long, and the walks recurse.
  let worker = std::thread::Builder::new()
    .stack_size(8 << 30)
    .spawn(move || run(&args))
    .map_err(|e| e.to_string())?;
  worker.join().map_err(|_| "the worker thread panicked".to_string())?
}
