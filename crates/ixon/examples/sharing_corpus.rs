//! Corpus runner for the exact sharing constructions.
//!
//! Runs the tiered canonical construction (`sharing_exact`) on every
//! constant of an `.ixe` file (or a deterministic subset), in parallel, and
//! prints a report: certified count, failures with names and candidate
//! counts, byte totals under Tag4 and TagN prices against the stored and
//! unshared encodings, the per-constant delta distribution, phase
//! statistics, the slowest constants, wall time and peak RSS.
//!
//! ```text
//! cargo run --release -p ixon --example sharing_corpus -- <file.ixe>
//!   [--layout tagN|tag4]      layout of the construction (default tagN)
//!   [--threads N]             worker threads (default: all cores)
//!   [--limit N]               only the first N constants (address order)
//!   [--csv PATH]              per-constant CSV
//!   [--select-out PATH]       write a selection: every --select-stride-th
//!                             constant plus those with more than
//!                             --select-min-cand R1/R2 candidates
//!   [--select-stride N]       (default 50)
//!   [--select-min-cand N]     (default 2000)
//!   [--width-experiment]      experiment, not the canonical construction:
//!                             run phases 1-3 at each phase-1 width
//!                             w in 1, 2, 3 and report the best of the
//!                             three against the K-based choice
//! ```
//!
//! Candidate counts are reported two ways: `cand`, the R1/R2 search
//! candidates (`candidate_terms`: at least two expanded occurrences and an
//! unshared encoding longer than one byte), and `k`, the tiered count
//! (compact in-degree >= 2 and unshared length >= 2).

#![allow(clippy::cast_precision_loss)]
#![allow(clippy::cast_possible_truncation)]

use std::collections::BTreeMap;
use std::io::Write;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use ix_common::address::Address;
use ixon::Env;
use ixon::constant::{Constant, ConstantInfo};
use ixon::sharing_exact::{
  ExactSharingLimits, Phase1Choice, ShareLayout, SharingDag, SharingError,
  candidate_terms, constant_fixed_len, constant_len, layout_bytes,
  normalize_constant_sharing_tiered, normalize_constant_sharing_tiered_with,
};
use rayon::prelude::*;

struct Args {
  path: String,
  layout: ShareLayout,
  threads: Option<usize>,
  limit: Option<usize>,
  csv: Option<String>,
  select_out: Option<String>,
  select_stride: usize,
  select_min_cand: usize,
  width_experiment: bool,
}

fn parse_args() -> Result<Args, String> {
  let mut it = std::env::args().skip(1);
  let mut a = Args {
    path: String::new(),
    layout: ShareLayout::TagN,
    threads: None,
    limit: None,
    csv: None,
    select_out: None,
    select_stride: 50,
    select_min_cand: 2000,
    width_experiment: false,
  };
  let num = |v: Option<String>| -> Result<usize, String> {
    v.ok_or("missing value")?.parse::<usize>().map_err(|e| e.to_string())
  };
  while let Some(arg) = it.next() {
    match arg.as_str() {
      "--layout" => {
        a.layout = match it.next().as_deref() {
          Some("tagN") => ShareLayout::TagN,
          Some("tag4") => ShareLayout::Tag4,
          other => return Err(format!("unknown layout {other:?}")),
        }
      },
      "--threads" => a.threads = Some(num(it.next())?),
      "--limit" => a.limit = Some(num(it.next())?),
      "--csv" => a.csv = it.next(),
      "--select-out" => a.select_out = it.next(),
      "--select-stride" => a.select_stride = num(it.next())?,
      "--select-min-cand" => a.select_min_cand = num(it.next())?,
      "--width-experiment" => a.width_experiment = true,
      p if !p.starts_with("--") && a.path.is_empty() => a.path = p.to_string(),
      other => return Err(format!("unknown argument {other}")),
    }
  }
  if a.path.is_empty() {
    return Err("usage: sharing_corpus <file.ixe> [options]".into());
  }
  Ok(a)
}

/// One processed constant.
#[derive(Default, Clone)]
struct Row {
  idx: usize,
  addr: String,
  status: String,
  kind: &'static str,
  raw: u64,
  n: u64,
  cand: u64,
  k: u64,
  /// Real (Tag4-serialized) bytes of the output.
  real: u64,
  /// The same output priced with TagN Shares.
  tagn: u64,
  unshared: Option<u64>,
  w: u64,
  uncertain: u64,
  max_comp: u64,
  comps: u64,
  slot_states: u64,
  uniform_states: u64,
  ms: f64,
}

fn kind_of(c: &Constant) -> &'static str {
  match &c.info {
    ConstantInfo::Defn(_) => "defn",
    ConstantInfo::Recr(_) => "recr",
    ConstantInfo::Axio(_) => "axio",
    ConstantInfo::Quot(_) => "quot",
    ConstantInfo::CPrj(_) => "cprj",
    ConstantInfo::RPrj(_) => "rprj",
    ConstantInfo::IPrj(_) => "iprj",
    ConstantInfo::DPrj(_) => "dprj",
    ConstantInfo::Muts(_) => "muts",
  }
}

fn projection_block(c: &Constant) -> Option<Address> {
  match &c.info {
    ConstantInfo::CPrj(p) => Some(p.block.clone()),
    ConstantInfo::RPrj(p) => Some(p.block.clone()),
    ConstantInfo::IPrj(p) => Some(p.block.clone()),
    ConstantInfo::DPrj(p) => Some(p.block.clone()),
    _ => None,
  }
}

fn process(
  idx: usize,
  addr: &Address,
  mut bytes: &[u8],
  layout: ShareLayout,
  limits: &ExactSharingLimits,
) -> Row {
  let mut row =
    Row { idx, addr: addr.hex(), raw: bytes.len() as u64, ..Row::default() };
  let c = match Constant::get(&mut bytes) {
    Ok(c) => c,
    Err(e) => {
      row.status = format!("decode: {e}");
      return row;
    },
  };
  row.kind = kind_of(&c);
  if let Ok(dag) =
    SharingDag::from_constant(&c, &ExactSharingLimits::unbounded())
  {
    row.n = dag.len() as u64;
    row.cand = candidate_terms(&dag).len() as u64;
  }
  let start = Instant::now();
  let r = normalize_constant_sharing_tiered(layout, &c, limits);
  row.ms = start.elapsed().as_secs_f64() * 1e3;
  match r {
    Ok((out, res)) => {
      row.status = "ok".into();
      let real = constant_len(&out).unwrap_or(u64::MAX);
      let fixed = constant_fixed_len(&c).unwrap_or(0);
      row.real = real;
      row.tagn = fixed
        + layout_bytes(ShareLayout::TagN, &res.sharing, &res.roots)
          .unwrap_or(u64::MAX - fixed);
      row.unshared = res.unshared_len.map(|u| fixed + u);
      row.k = res.stats.candidate_count;
      row.w = res.stats.w;
      row.uncertain = res.phase1.uncertain.len() as u64;
      row.comps = res.phase1.components.len() as u64;
      row.max_comp =
        res.phase1.components.iter().map(Vec::len).max().unwrap_or(0) as u64;
      row.slot_states = res.stats.slot_states;
      row.uniform_states = res.phase1.states_visited;
    },
    Err(SharingError::ResourceExhausted(e)) => {
      row.status = format!("resource:{:?}", e.resource);
    },
    Err(e) => row.status = format!("error: {e}"),
  }
  row
}

fn signed(x: u64) -> i64 {
  i64::try_from(x).unwrap_or(i64::MAX)
}

fn peak_rss_kib() -> Option<u64> {
  let s = std::fs::read_to_string("/proc/self/status").ok()?;
  let line = s.lines().find(|l| l.starts_with("VmHWM:"))?;
  line.split_whitespace().nth(1)?.parse().ok()
}

fn percentiles(mut xs: Vec<i64>) -> String {
  if xs.is_empty() {
    return "n/a".into();
  }
  xs.sort_unstable();
  // Nearest-rank percentile, rounding the rank down.
  let at = |num: usize, den: usize| xs[(xs.len() - 1) * num / den];
  format!(
    "min {} p1 {} p10 {} p50 {} p90 {} p99 {} p99.9 {} max {}",
    xs[0],
    at(1, 100),
    at(10, 100),
    at(50, 100),
    at(90, 100),
    at(99, 100),
    at(999, 1000),
    xs[xs.len() - 1]
  )
}

fn main() -> Result<(), String> {
  let args = parse_args()?;
  if let Some(t) = args.threads {
    rayon::ThreadPoolBuilder::new()
      .num_threads(t)
      .build_global()
      .map_err(|e| e.to_string())?;
  }
  let t0 = Instant::now();
  let file = std::fs::File::open(&args.path).map_err(|e| e.to_string())?;
  // SAFETY: the corpus file is not modified while it is mapped.
  let mmap =
    Arc::new(unsafe { memmap2::Mmap::map(&file) }.map_err(|e| e.to_string())?);
  let index = Env::parse_lazy_index(&mmap)?;
  let load_ms = t0.elapsed().as_millis();
  let mut consts = index.consts.clone();
  if let Some(n) = args.limit {
    consts.truncate(n);
  }
  eprintln!(
    "[sharing_corpus] {}: {} constants, {} names, index parsed in {load_ms} ms; processing {} under {:?}",
    args.path,
    index.consts.len(),
    index.named.len(),
    consts.len(),
    args.layout
  );
  // Names: the least name of each address; anonymous mutual blocks get the
  // least name of a projection into them.
  let window: BTreeMap<&Address, (usize, usize)> =
    index.consts.iter().map(|c| (&c.addr, (c.offset, c.len))).collect();
  let mut names: BTreeMap<Address, String> = BTreeMap::new();
  for n in &index.named {
    let s = n.name.pretty();
    let e = names.entry(n.addr.clone()).or_insert_with(|| s.clone());
    if s < *e {
      *e = s;
    }
  }
  let mut block_names: BTreeMap<Address, String> = BTreeMap::new();
  for (addr, name) in &names {
    if let Some(&(off, len)) = window.get(addr)
      && let Ok(c) = Constant::get(&mut &mmap[off..off + len])
      && let Some(b) = projection_block(&c)
    {
      let e = block_names.entry(b).or_insert_with(|| format!("{name} [block]"));
      let cand = format!("{name} [block]");
      if cand < *e {
        *e = cand;
      }
    }
  }
  let name_of = |hex: &str, addr: &Address| -> String {
    names
      .get(addr)
      .or_else(|| block_names.get(addr))
      .cloned()
      .unwrap_or_else(|| format!("<{}>", &hex[..16]))
  };
  let limits = ExactSharingLimits::default();
  if args.width_experiment {
    return width_experiment(&args, &consts, &mmap, &limits, &name_of, t0);
  }
  let done = AtomicUsize::new(0);
  let t1 = Instant::now();
  let total = consts.len();
  let rows: Vec<Row> = consts
    .par_iter()
    .enumerate()
    .map(|(i, c)| {
      let row = process(
        i,
        &c.addr,
        &mmap[c.offset..c.offset + c.len],
        args.layout,
        &limits,
      );
      let d = done.fetch_add(1, Ordering::Relaxed) + 1;
      if d.is_multiple_of(50_000) {
        eprintln!(
          "[sharing_corpus] {d}/{total} in {:.1} s",
          t1.elapsed().as_secs_f64()
        );
      }
      row
    })
    .collect();
  let run_s = t1.elapsed().as_secs_f64();
  // CSV.
  if let Some(path) = &args.csv {
    let mut f = std::io::BufWriter::new(
      std::fs::File::create(path).map_err(|e| e.to_string())?,
    );
    writeln!(f, "idx,addr,name,kind,status,raw,real,tagn,unshared,n,cand,k,w,uncertain,comps,max_comp,slot_states,uniform_states,ms").map_err(|e| e.to_string())?;
    for (r, c) in rows.iter().zip(&consts) {
      writeln!(
        f,
        "{},{},\"{}\",{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{:.3}",
        r.idx,
        r.addr,
        name_of(&r.addr, &c.addr).replace('"', "'"),
        r.kind,
        r.status,
        r.raw,
        r.real,
        r.tagn,
        r.unshared.map_or(String::new(), |u| u.to_string()),
        r.n,
        r.cand,
        r.k,
        r.w,
        r.uncertain,
        r.comps,
        r.max_comp,
        r.slot_states,
        r.uniform_states,
        r.ms
      )
      .map_err(|e| e.to_string())?;
    }
  }
  // Selection for the Lean differential.
  if let Some(path) = &args.select_out {
    let mut f = std::io::BufWriter::new(
      std::fs::File::create(path).map_err(|e| e.to_string())?,
    );
    let mut count = 0;
    for r in &rows {
      if r.idx % args.select_stride == 0 || r.cand > args.select_min_cand as u64
      {
        writeln!(f, "{}", r.addr).map_err(|e| e.to_string())?;
        count += 1;
      }
    }
    eprintln!("[sharing_corpus] wrote {count} selected addresses to {path}");
  }
  // Report.
  let ok: Vec<&Row> = rows.iter().filter(|r| r.status == "ok").collect();
  let failed: Vec<(&Row, &Address)> = rows
    .iter()
    .zip(&consts)
    .filter(|(r, _)| r.status != "ok")
    .map(|(r, c)| (r, &c.addr))
    .collect();
  let sum = |f: &dyn Fn(&Row) -> u64| ok.iter().map(|r| f(r)).sum::<u64>();
  println!("# sharing_corpus report");
  println!(
    "- corpus: {} ({} constants; {} processed); layout {:?}",
    args.path,
    index.consts.len(),
    rows.len(),
    args.layout
  );
  println!(
    "- wall: index {load_ms} ms, processing {run_s:.1} s with {} threads; peak RSS {} KiB",
    rayon::current_num_threads(),
    peak_rss_kib().map_or("?".into(), |k| k.to_string())
  );
  println!(
    "- certified: {} / {}; failed: {}",
    ok.len(),
    rows.len(),
    failed.len()
  );
  let mut by_status: BTreeMap<&str, usize> = BTreeMap::new();
  for (r, _) in &failed {
    *by_status.entry(r.status.as_str()).or_default() += 1;
  }
  println!("- failures by status: {by_status:?}");
  for (r, a) in &failed {
    println!(
      "  - FAILED {} ({}): {}; N {}, cand {}, raw {} B, {:.0} ms",
      name_of(&r.addr, a),
      &r.addr[..16],
      r.status,
      r.n,
      r.cand,
      r.raw,
      r.ms
    );
  }
  let raw = sum(&|r| r.raw);
  let real = sum(&|r| r.real);
  let tagn = sum(&|r| r.tagn);
  let un_known: Vec<&&Row> =
    ok.iter().filter(|r| r.unshared.is_some()).collect();
  let unshared: u64 = un_known.iter().map(|r| r.unshared.unwrap_or(0)).sum();
  let raw_known: u64 = un_known.iter().map(|r| r.raw).sum();
  let real_known: u64 = un_known.iter().map(|r| r.real).sum();
  println!(
    "- certified constants: stored (heuristic) {raw} B; output under Tag4 {real} B ({:+.2}%); under TagN {tagn} B ({:+.2}%)",
    (real as f64 - raw as f64) / raw as f64 * 100.0,
    (tagn as f64 - raw as f64) / raw as f64 * 100.0
  );
  println!(
    "- unshared (where it fits u64, {} constants): {unshared} B; stored {raw_known} B; Tag4 output {real_known} B",
    un_known.len()
  );
  let deltas: Vec<i64> =
    ok.iter().map(|r| signed(r.real) - signed(r.raw)).collect();
  let (neg, zero, pos) = (
    deltas.iter().filter(|d| **d < 0).count(),
    deltas.iter().filter(|d| **d == 0).count(),
    deltas.iter().filter(|d| **d > 0).count(),
  );
  println!(
    "- Tag4 output - stored per constant: {neg} smaller, {zero} equal, {pos} larger; {}",
    percentiles(deltas)
  );
  let tdeltas: Vec<i64> =
    ok.iter().map(|r| signed(r.tagn) - signed(r.raw)).collect();
  println!("- TagN price - stored per constant: {}", percentiles(tdeltas));
  println!(
    "- phase-1 width w: {:?}",
    ok.iter().fold(BTreeMap::<u64, usize>::new(), |mut m, r| {
      *m.entry(r.w).or_default() += 1;
      m
    })
  );
  println!(
    "- uncertain terms per constant: {}",
    percentiles(ok.iter().map(|r| signed(r.uncertain)).collect())
  );
  println!(
    "- largest component per constant: {}",
    percentiles(ok.iter().map(|r| signed(r.max_comp)).collect())
  );
  println!(
    "- uniform search states per constant: {}",
    percentiles(ok.iter().map(|r| signed(r.uniform_states)).collect())
  );
  println!(
    "- first-tier search states per constant: {}",
    percentiles(ok.iter().map(|r| signed(r.slot_states)).collect())
  );
  println!(
    "- R1/R2 candidates per constant (all): {}",
    percentiles(rows.iter().map(|r| signed(r.cand)).collect())
  );
  println!(
    "- milliseconds per constant (certified): {}",
    percentiles(ok.iter().map(|r| r.ms.round() as i64).collect())
  );
  let mut slow: Vec<(&Row, &Address)> =
    rows.iter().zip(&consts).map(|(r, c)| (r, &c.addr)).collect();
  slow.sort_by(|a, b| b.0.ms.total_cmp(&a.0.ms));
  println!("- slowest 10:");
  for (r, a) in slow.iter().take(10) {
    println!(
      "  - {:.0} ms {} ({}): {} {}, N {}, cand {}, k {}, w {}, uncertain {}, components {} (largest {}), states uniform {} first-tier {}",
      r.ms,
      name_of(&r.addr, a),
      &r.addr[..16],
      r.kind,
      r.status,
      r.n,
      r.cand,
      r.k,
      r.w,
      r.uncertain,
      r.comps,
      r.max_comp,
      r.uniform_states,
      r.slot_states
    );
  }
  println!("- total wall {:.1} s", t0.elapsed().as_secs_f64());
  Ok(())
}

// ---------------------------------------------------------------------------
// Width experiment (not the canonical construction)
// ---------------------------------------------------------------------------

/// One constant under the width experiment: phases 1-3 at each phase-1
/// width `w` in 1, 2, 3, and with every candidate stored ("all"). `bytes[i]`
/// is the complete constant priced by the layout (for Tag4, the serialized
/// length) at `w = i + 1` for `i < 3`, and for "all" at `i = 3`.
#[derive(Default, Clone)]
struct WRow {
  idx: usize,
  addr: String,
  kind: &'static str,
  raw: u64,
  k: u64,
  status: [String; 4],
  stored: [u64; 4],
  bytes: [Option<u64>; 4],
  ms: [f64; 4],
}

impl WRow {
  /// Phase-1 width of the canonical (`K`-based) construction.
  fn wk(&self, layout: ShareLayout) -> usize {
    usize::try_from(layout.uniform_width(self.k)).unwrap_or(3)
  }
  /// Fewest layout bytes over the three widths; ties to the lower width.
  fn best(&self) -> Option<(usize, u64)> {
    self.best_of(3)
  }
  /// Fewest layout bytes over the widths 1, 2, 3 and then "all" (index 4);
  /// ties to the earlier candidate.
  fn best4(&self) -> Option<(usize, u64)> {
    self.best_of(4)
  }
  fn best_of(&self, n: usize) -> Option<(usize, u64)> {
    let mut best: Option<(usize, u64)> = None;
    for (i, b) in self.bytes.iter().take(n).enumerate() {
      if let Some(b) = *b
        && best.is_none_or(|(_, x)| b < x)
      {
        best = Some((i + 1, b));
      }
    }
    best
  }
  /// The width chosen from the stored count of the `K`-based run.
  fn rewidth(&self, layout: ShareLayout) -> usize {
    let wk = self.wk(layout);
    usize::try_from(layout.uniform_width(self.stored[wk - 1])).unwrap_or(3)
  }
}

fn process_widths(
  idx: usize,
  addr: &Address,
  mut bytes: &[u8],
  layout: ShareLayout,
  limits: &ExactSharingLimits,
) -> WRow {
  let mut row =
    WRow { idx, addr: addr.hex(), raw: bytes.len() as u64, ..WRow::default() };
  let c = match Constant::get(&mut bytes) {
    Ok(c) => c,
    Err(e) => {
      row.status = std::array::from_fn(|_| format!("decode: {e}"));
      return row;
    },
  };
  row.kind = kind_of(&c);
  let fixed = constant_fixed_len(&c).unwrap_or(0);
  for i in 0..4 {
    let start = Instant::now();
    let choice = if i < 3 {
      Phase1Choice::Width(i as u64 + 1)
    } else {
      Phase1Choice::AllCandidates
    };
    let r = normalize_constant_sharing_tiered_with(layout, &c, limits, choice);
    row.ms[i] = start.elapsed().as_secs_f64() * 1e3;
    match r {
      Ok((_, res)) => {
        row.status[i] = "ok".into();
        row.k = res.stats.candidate_count;
        row.stored[i] = res.table_terms.len() as u64;
        row.bytes[i] = Some(fixed + res.model_len);
      },
      Err(SharingError::ResourceExhausted(e)) => {
        row.status[i] = format!("resource:{:?}", e.resource);
      },
      Err(e) => row.status[i] = format!("error: {e}"),
    }
  }
  row
}

fn width_experiment(
  args: &Args,
  consts: &[ixon::env::LazyConstSlice],
  mmap: &[u8],
  limits: &ExactSharingLimits,
  name_of: &dyn Fn(&str, &Address) -> String,
  t0: Instant,
) -> Result<(), String> {
  let layout = args.layout;
  let done = AtomicUsize::new(0);
  let t1 = Instant::now();
  let total = consts.len();
  let rows: Vec<WRow> = consts
    .par_iter()
    .enumerate()
    .map(|(i, c)| {
      let row = process_widths(
        i,
        &c.addr,
        &mmap[c.offset..c.offset + c.len],
        layout,
        limits,
      );
      let d = done.fetch_add(1, Ordering::Relaxed) + 1;
      if d.is_multiple_of(50_000) {
        eprintln!(
          "[sharing_corpus] {d}/{total} in {:.1} s",
          t1.elapsed().as_secs_f64()
        );
      }
      row
    })
    .collect();
  let run_s = t1.elapsed().as_secs_f64();
  if let Some(path) = &args.csv {
    let mut f = std::io::BufWriter::new(
      std::fs::File::create(path).map_err(|e| e.to_string())?,
    );
    writeln!(
      f,
      "idx,addr,name,kind,raw,k,wk,status1,status2,status3,stored1,stored2,stored3,bytes1,bytes2,bytes3,kbased,best,best_w,rewidth,rewidth_w,ms1,ms2,ms3,status_all,stored_all,bytes_all,best4,best4_w,ms_all"
    )
    .map_err(|e| e.to_string())?;
    let opt = |b: Option<u64>| b.map_or(String::new(), |b| b.to_string());
    let wname =
      |w: usize| if w == 4 { "all".to_string() } else { w.to_string() };
    for (r, c) in rows.iter().zip(consts) {
      let wk = r.wk(layout);
      let rw = r.rewidth(layout);
      let (bw, bb) =
        r.best().map_or((String::new(), String::new()), |(w, b)| {
          (w.to_string(), b.to_string())
        });
      let (bw4, bb4) =
        r.best4().map_or((String::new(), String::new()), |(w, b)| {
          (wname(w), b.to_string())
        });
      writeln!(
        f,
        "{},{},\"{}\",{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{:.3},{:.3},{:.3},{},{},{},{},{},{:.3}",
        r.idx,
        r.addr,
        name_of(&r.addr, &c.addr).replace('"', "'"),
        r.kind,
        r.raw,
        r.k,
        wk,
        r.status[0],
        r.status[1],
        r.status[2],
        r.stored[0],
        r.stored[1],
        r.stored[2],
        opt(r.bytes[0]),
        opt(r.bytes[1]),
        opt(r.bytes[2]),
        opt(r.bytes[wk - 1]),
        bb,
        bw,
        opt(r.bytes[rw - 1]),
        rw,
        r.ms[0],
        r.ms[1],
        r.ms[2],
        r.status[3],
        r.stored[3],
        opt(r.bytes[3]),
        bb4,
        bw4,
        r.ms[3]
      )
      .map_err(|e| e.to_string())?;
    }
  }
  // Summary over constants where all four candidates succeeded.
  let mut failed = [0u64; 4];
  let (mut n_all, mut kb, mut best, mut rew) = (0u64, 0u128, 0u128, 0u128);
  let (mut best4_total, mut all_total) = (0u128, 0u128);
  let mut wins = [0u64; 3];
  let mut wins4 = [0u64; 4];
  let (mut b4_better, mut b4_equal) = (0u64, 0u64);
  let (mut b_better, mut b_equal) = (0u64, 0u64);
  let (mut r_better, mut r_equal, mut r_worse) = (0u64, 0u64, 0u64);
  let mut gains: Vec<i64> = Vec::new();
  for r in &rows {
    for (f, b) in failed.iter_mut().zip(&r.bytes) {
      if b.is_none() {
        *f += 1;
      }
    }
    if r.bytes.iter().any(Option::is_none) {
      continue;
    }
    n_all += 1;
    let wk = r.wk(layout);
    let k_b = r.bytes[wk - 1].unwrap_or(0);
    let (bw, b_b) = r.best().unwrap_or((wk, k_b));
    let (bw4, b_b4) = r.best4().unwrap_or((bw, b_b));
    let r_b = r.bytes[r.rewidth(layout) - 1].unwrap_or(0);
    kb += u128::from(k_b);
    best += u128::from(b_b);
    best4_total += u128::from(b_b4);
    all_total += u128::from(r.bytes[3].unwrap_or(0));
    rew += u128::from(r_b);
    wins[bw - 1] += 1;
    wins4[bw4 - 1] += 1;
    if b_b4 < b_b {
      b4_better += 1;
    } else {
      b4_equal += 1;
    }
    if b_b < k_b {
      b_better += 1;
      gains.push(signed(b_b) - signed(k_b));
    } else {
      b_equal += 1;
    }
    match r_b.cmp(&k_b) {
      std::cmp::Ordering::Less => r_better += 1,
      std::cmp::Ordering::Equal => r_equal += 1,
      std::cmp::Ordering::Greater => r_worse += 1,
    }
  }
  println!(
    "# sharing_corpus width experiment (not the canonical construction)"
  );
  println!(
    "- corpus: {} ({} constants processed); layout {:?}; phases 1-3 at w = 1, 2, 3",
    args.path,
    rows.len(),
    layout
  );
  println!(
    "- wall: processing {run_s:.1} s with {} threads; peak RSS {} KiB",
    rayon::current_num_threads(),
    peak_rss_kib().map_or("?".into(), |k| k.to_string())
  );
  println!(
    "- failures by candidate: w=1 {}, w=2 {}, w=3 {}, all {}; constants with all four ok: {n_all}",
    failed[0], failed[1], failed[2], failed[3]
  );
  println!(
    "- best of four (w = 1, 2, 3, all; ties to the earlier): {best4_total} ({:+} vs best of three); all candidates stored: {all_total}",
    best4_total.cast_signed() - best.cast_signed()
  );
  println!(
    "- best-of-four winner: w=1 {}, w=2 {}, w=3 {}, all {}; best of four vs best of three per constant: better {b4_better}, equal {b4_equal}",
    wins4[0], wins4[1], wins4[2], wins4[3]
  );
  println!(
    "- layout bytes over those constants: K-based {kb}; best of three {best} ({:+}); stored-count re-solve {rew} ({:+})",
    best.cast_signed() - kb.cast_signed(),
    rew.cast_signed() - kb.cast_signed()
  );
  println!(
    "- best-of-three width (ties to the lower w): w=1 {}, w=2 {}, w=3 {}",
    wins[0], wins[1], wins[2]
  );
  println!(
    "- best of three vs K-based per constant: better {b_better}, equal {b_equal}; change {}",
    percentiles(gains)
  );
  println!(
    "- stored-count re-solve vs K-based per constant: better {r_better}, equal {r_equal}, worse {r_worse}"
  );
  println!("- total wall {:.1} s", t0.elapsed().as_secs_f64());
  Ok(())
}
