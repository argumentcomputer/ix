//! Corpus runner for the canonical sharing construction.
//!
//! Runs the tiered canonical construction (`sharing_exact`, TagN layout) on
//! every constant of an `.ixe` file (or a deterministic subset), in parallel,
//! and prints a report: certified count, failures with names and candidate
//! counts, serialized and TagN-priced byte totals against the stored and
//! unshared encodings, the per-constant delta distribution, phase
//! statistics, the slowest constants, wall time and peak RSS. The
//! `--select-out` address lists feed the Lean/Rust corpus differential
//! (`IX_SHARING_CORPUS_SELECT` of the `exact-sharing-ffi` suite).
//!
//! ```text
//! cargo run --release -p ixon --example sharing_corpus -- <file.ixe>
//!   [--threads N]             worker threads (default: all cores)
//!   [--limit N]               only the first N constants (address order)
//!   [--csv PATH]              per-constant CSV (with the blake3 of the
//!                             output and, per phase-1 width, the final
//!                             bytes, model bytes, states and work)
//!   [--select-out PATH]       write a selection: every --select-stride-th
//!                             constant plus those with more than
//!                             --select-min-cand R1/R2 candidates
//!   [--select-stride N]       (default 50)
//!   [--select-min-cand N]     (default 2000)
//!   [--only HEX]              only constants whose address starts with HEX
//!                             (repeatable)
//!   [--par-widths N] [--par-components N] [--par-materialize N]
//!                             thread budgets inside one constant
//!   [--serial-constants]      one constant at a time (per-constant latency)
//!   [--check-sequential]      also run the sequential reference (under the
//!                             same limits) and compare
//!   [--max-states N]          override the max_states limit
//!   [--sharing-limits SPEC]   override limits (`ExactSharingLimits::
//!                             with_overrides`, the grammar of `ix compile
//!                             --sharing-limits`), after --max-states
//!   [--full-check]            the checked mode (`ExactSharingLimits::
//!                             full_check`): build and check every candidate
//!                             and cross-check every shortcut; the output
//!                             and every column but `ms` are those of the
//!                             default mode, and a discrepancy is a failure
//!                             with an `internal error` status
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
  ExactSharingLimits, Parallelism, ShareLayout, SharingDag, SharingError,
  TieredSharingResult, candidate_terms, constant_fixed_len, constant_len,
  layout_bytes, normalize_constant_sharing_tiered,
  normalize_constant_sharing_tiered_par,
};
use rayon::prelude::*;

// The allocator of the `ix` binary (`crates/ffi`), so per-constant times
// match the compiler's.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// The Share layout of the construction: TagN, the wire Share code.
const LAYOUT: ShareLayout = ShareLayout::TagN;

struct Args {
  path: String,
  threads: Option<usize>,
  limit: Option<usize>,
  csv: Option<String>,
  select_out: Option<String>,
  select_stride: usize,
  select_min_cand: usize,
  parallel: Parallelism,
  check_sequential: bool,
  only: Vec<String>,
  serial_constants: bool,
  max_states: Option<u64>,
  sharing_limits: Option<String>,
  full_check: bool,
}

fn parse_args() -> Result<Args, String> {
  let mut it = std::env::args().skip(1);
  let mut a = Args {
    path: String::new(),
    threads: None,
    limit: None,
    csv: None,
    select_out: None,
    select_stride: 50,
    select_min_cand: 2000,
    parallel: Parallelism::SEQUENTIAL,
    check_sequential: false,
    only: Vec::new(),
    serial_constants: false,
    max_states: None,
    sharing_limits: None,
    full_check: false,
  };
  let num = |v: Option<String>| -> Result<usize, String> {
    v.ok_or("missing value")?.parse::<usize>().map_err(|e| e.to_string())
  };
  while let Some(arg) = it.next() {
    match arg.as_str() {
      "--threads" => a.threads = Some(num(it.next())?),
      "--limit" => a.limit = Some(num(it.next())?),
      "--csv" => a.csv = it.next(),
      "--select-out" => a.select_out = it.next(),
      "--select-stride" => a.select_stride = num(it.next())?,
      "--select-min-cand" => a.select_min_cand = num(it.next())?,
      "--par-widths" => a.parallel.widths = num(it.next())?,
      "--par-components" => a.parallel.components = num(it.next())?,
      "--par-materialize" => a.parallel.materialize = num(it.next())?,
      "--check-sequential" => a.check_sequential = true,
      "--only" => a.only.push(it.next().ok_or("missing value")?),
      "--serial-constants" => a.serial_constants = true,
      "--max-states" => a.max_states = Some(num(it.next())? as u64),
      "--sharing-limits" => {
        a.sharing_limits = Some(it.next().ok_or("missing value")?);
      },
      "--full-check" => a.full_check = true,
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
  /// Serialized bytes of the output (the wire Share code).
  real: u64,
  /// The same output priced by the TagN layout (`layout_bytes`); the
  /// construction checks that it equals `real`.
  tagn: u64,
  unshared: Option<u64>,
  w: u64,
  uncertain: u64,
  max_comp: u64,
  comps: u64,
  slot_states: u64,
  /// `--check-sequential`: how the sequential reference compares.
  seq_check: &'static str,
  uniform_states: u64,
  /// blake3 of the serialized output Constant (empty on failure).
  out_hash: String,
  /// Per phase-1 width 1, 2, 3: `(final layout bytes, phase-1 model bytes,
  /// states_created, work)` of that candidate's run.
  per_width: Vec<(u64, u64, u64, u64)>,
  /// Candidates whose phase 3 ran per prefix.
  per_prefix: u64,
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
  limits: &ExactSharingLimits,
  par: Parallelism,
  check_sequential: bool,
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
  let r = normalize_constant_sharing_tiered_par(LAYOUT, &c, limits, par);
  row.ms = start.elapsed().as_secs_f64() * 1e3;
  if check_sequential {
    // The sequential reference under the same limits: a difference is a
    // difference of the parallel path, not of the limits.
    let s = normalize_constant_sharing_tiered(LAYOUT, &c, limits);
    row.seq_check = compare_sequential(&r, &s);
  }
  match r {
    Ok((out, res)) => {
      row.status = "ok".into();
      let real = constant_len(&out).unwrap_or(u64::MAX);
      let fixed = constant_fixed_len(&c).unwrap_or(0);
      row.real = real;
      row.tagn = fixed
        + layout_bytes(LAYOUT, &res.sharing, &res.roots)
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
      let mut bytes = Vec::new();
      out.put(&mut bytes);
      row.out_hash = blake3::hash(&bytes).to_hex().to_string();
      row.per_prefix = res.stats.per_prefix_candidates;
      row.per_width = res
        .stats
        .candidate_lengths
        .iter()
        .zip(&res.stats.candidate_meters)
        .map(|(&(_, len), &(_, model, states, work))| {
          (len, model, states, work)
        })
        .collect();
    },
    Err(SharingError::ResourceExhausted(e)) => {
      row.status = format!("resource:{:?}", e.resource);
    },
    Err(e) => row.status = format!("error: {e}"),
  }
  row
}

type Normalized = Result<(Constant, TieredSharingResult), SharingError>;

/// How a run compares with the sequential reference (`--check-sequential`).
fn compare_sequential(p: &Normalized, s: &Normalized) -> &'static str {
  match (p, s) {
    (Ok((pc, pr)), Ok((sc, sr))) => {
      let (mut a, mut b) = (Vec::new(), Vec::new());
      pc.put(&mut a);
      sc.put(&mut b);
      if a != b {
        "bytes differ"
      } else if pr != sr {
        "result differs"
      } else {
        "same"
      }
    },
    (Err(e), Err(f)) if e == f => "same error",
    (
      Err(SharingError::ResourceExhausted(_)),
      Err(SharingError::ResourceExhausted(_)),
    ) => "both exhausted, other resource",
    (Err(_), Err(_)) => "errors differ",
    _ => "outcome differs",
  }
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
  if !args.only.is_empty() {
    consts.retain(|c| {
      let h = c.addr.hex();
      args.only.iter().any(|p| h.starts_with(p.as_str()))
    });
  }
  eprintln!(
    "[sharing_corpus] {}: {} constants, {} names, index parsed in {load_ms} ms; processing {} under {:?}",
    args.path,
    index.consts.len(),
    index.named.len(),
    consts.len(),
    LAYOUT
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
  let mut limits = ExactSharingLimits::default();
  if let Some(m) = args.max_states {
    limits.max_states = m;
  }
  if let Some(spec) = &args.sharing_limits {
    limits = limits.with_overrides(spec)?;
  }
  limits.full_check = args.full_check;
  let done = AtomicUsize::new(0);
  let t1 = Instant::now();
  let total = consts.len();
  let one = |(i, c): (usize, &ixon::env::LazyConstSlice)| {
    let row = process(
      i,
      &c.addr,
      &mmap[c.offset..c.offset + c.len],
      &limits,
      args.parallel,
      args.check_sequential,
    );
    let d = done.fetch_add(1, Ordering::Relaxed) + 1;
    if d.is_multiple_of(50_000) {
      eprintln!(
        "[sharing_corpus] {d}/{total} in {:.1} s",
        t1.elapsed().as_secs_f64()
      );
    }
    row
  };
  // `--serial-constants`: one constant at a time, so the pool serves only the
  // parallelism inside a constant (per-constant latency).
  let rows: Vec<Row> = if args.serial_constants {
    consts.iter().enumerate().map(one).collect()
  } else {
    consts.par_iter().enumerate().map(one).collect()
  };
  let run_s = t1.elapsed().as_secs_f64();
  // CSV.
  if let Some(path) = &args.csv {
    let mut f = std::io::BufWriter::new(
      std::fs::File::create(path).map_err(|e| e.to_string())?,
    );
    writeln!(f, "idx,addr,name,kind,status,raw,real,tagn,unshared,n,cand,k,w,uncertain,comps,max_comp,slot_states,uniform_states,out_hash,len1,len2,len3,model1,model2,model3,states1,states2,states3,work1,work2,work3,ms").map_err(|e| e.to_string())?;
    for (r, c) in rows.iter().zip(&consts) {
      let col = |k: usize, f: fn(&(u64, u64, u64, u64)) -> u64| {
        r.per_width.get(k).map_or(String::new(), |x| f(x).to_string())
      };
      let cols = |f: fn(&(u64, u64, u64, u64)) -> u64| {
        format!("{},{},{}", col(0, f), col(1, f), col(2, f))
      };
      writeln!(
        f,
        "{},{},\"{}\",{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{:.3}",
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
        r.out_hash,
        cols(|x| x.0),
        cols(|x| x.1),
        cols(|x| x.2),
        cols(|x| x.3),
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
    "- corpus: {} ({} constants; {} processed); layout {:?}{}",
    args.path,
    index.consts.len(),
    rows.len(),
    LAYOUT,
    if args.full_check { "; checked mode (--full-check)" } else { "" }
  );
  if args.max_states.is_some() || args.sharing_limits.is_some() {
    println!("- limits: {limits:?}");
  }
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
  if args.check_sequential {
    let mut by_check: BTreeMap<&str, usize> = BTreeMap::new();
    for r in &rows {
      *by_check.entry(r.seq_check).or_default() += 1;
    }
    println!(
      "- sequential check (parallel {:?} vs the sequential reference): {by_check:?}",
      args.parallel
    );
    for (r, a) in rows.iter().zip(&consts) {
      if r.seq_check != "same" && r.seq_check != "same error" {
        println!(
          "  - {}: {} ({})",
          r.seq_check,
          name_of(&r.addr, &a.addr),
          &r.addr[..16]
        );
      }
    }
  }
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
    "- certified constants: stored {raw} B; serialized output {real} B ({:+.2}%); under TagN {tagn} B ({:+.2}%)",
    (real as f64 - raw as f64) / raw as f64 * 100.0,
    (tagn as f64 - raw as f64) / raw as f64 * 100.0
  );
  println!(
    "- unshared (where it fits u64, {} constants): {unshared} B; stored {raw_known} B; serialized output {real_known} B",
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
    "- serialized output - stored per constant: {neg} smaller, {zero} equal, {pos} larger; {}",
    percentiles(deltas)
  );
  let tdeltas: Vec<i64> =
    ok.iter().map(|r| signed(r.tagn) - signed(r.raw)).collect();
  println!("- TagN price - stored per constant: {}", percentiles(tdeltas));
  println!(
    "- candidates with a per-prefix phase 3 (order not closed under stored \
     descendants): {}; largest work charged to one candidate: {}",
    ok.iter().map(|r| r.per_prefix).sum::<u64>(),
    ok.iter().flat_map(|r| r.per_width.iter().map(|x| x.3)).max().unwrap_or(0)
  );
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
  // Phase timers (only with the `sharing-profile` feature of ixon).
  let profile = ixon::sharing_exact::profile_report();
  if !profile.is_empty() {
    println!("- phase timers (summed over threads):");
    for (name, ns, calls) in profile {
      println!("  - {name}: {:.3} s in {calls} scopes", ns as f64 / 1e9);
    }
  }
  println!("- total wall {:.1} s", t0.elapsed().as_secs_f64());
  Ok(())
}
