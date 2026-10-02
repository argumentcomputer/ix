//! PROTOTYPE (measurement only, not for merging): wall time per code area
//! of the compile pipeline, exclusive and inclusive, summed over threads.
//!
//! Enabled with `IX_AREAS=1`; otherwise every [`scope`] is one relaxed load.
//! A thread keeps a stack of open scopes: a scope's exclusive time is its
//! elapsed time minus the elapsed time of the scopes opened inside it on the
//! same thread, so the exclusive times of the outermost scopes and everything
//! nested in them add up to the outermost scopes' elapsed time. Thread-local
//! sums are flushed to process-wide counters whenever a thread's stack
//! becomes empty.

use std::cell::RefCell;
use std::sync::LazyLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

macro_rules! areas {
  ($($v:ident => $s:literal),* $(,)?) => {
    /// A timed area.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    #[repr(usize)]
    pub enum Area { $($v),* }
    /// Number of areas.
    pub const N: usize = [$($s),*].len();
    const NAMES: [&str; N] = [$($s),*];
  };
}

areas! {
  Block => "sched.block (bookkeeping)",
  Release => "sched.release deps",
  QueueWait => "sched.queue wait",
  Admission => "sched.admission",
  NoAux => "sched.no_aux path",
  CrossScc => "sched.cross_scc path",
  Fetch => "lean decode (LazyEnv fetch)",
  Evict => "LazyEnv evict (drop)",
  Audit => "plan-head audit",
  Preseed => "preseed tables",
  SortConsts => "sort_consts",
  MkIndc => "mk_indc",
  CompileConst => "compile_{def,rec,ind,...} excl expr",
  CompileExpr => "compile_expr",
  Share => "sharing (share_roots glue)",
  ShareDag => "sharing: dag",
  ShareTotal => "sharing: tiered (excl phases)",
  SharePrep => "sharing: prep",
  ShareClassify => "sharing: p1.classify",
  ShareSearch => "sharing: p1.search",
  ShareKnapsack => "sharing: p1.knapsack",
  ShareUMat => "sharing: p1.materialize",
  ShareUCheck => "sharing: p1.check",
  ShareAllocate => "sharing: p2.allocate",
  ShareP3Costs => "sharing: p3.costs",
  ShareP3Decide => "sharing: p3.decide",
  ShareP3Build => "sharing: p3.build",
  ShareP3Check => "sharing: p3.check",
  ShareOutput => "sharing: output",
  Serialize => "Constant::put (block)",
  HashAddr => "Address::hash (block)",
  Publish => "publish (store/register)",
  AuxGen => "aux_gen (excl nested)",
  AuxPatches => "aux_gen: generate_aux_patches (excl nested)",
  KernelIngress => "ensure_in_kenv",
  Other => "other",
}

/// Whether area timing is on (`IX_AREAS=1`).
pub static ENABLED: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_AREAS").as_deref() == Ok("1"));

static INCL: [AtomicU64; N] = [const { AtomicU64::new(0) }; N];
static EXCL: [AtomicU64; N] = [const { AtomicU64::new(0) }; N];
static CALLS: [AtomicU64; N] = [const { AtomicU64::new(0) }; N];

/// Whether area timing is on.
pub fn enabled() -> bool {
  *ENABLED
}

/// Named counters of the width-certificate experiment.
#[derive(Clone, Copy, Debug)]
#[repr(usize)]
pub enum Ctr {
  Calls,
  W1Ns,
  W2Ns,
  W3Ns,
  WinW1,
  WinW2,
  WinW3,
  Violations,
  CertAfterW1,
  CertAfterW1Ns,
  CertAfterW2,
  CertAfterW2Ns,
  SmallTable,
  SmallTableNs,
}
const CTR_NAMES: [&str; 14] = [
  "tiered calls",
  "width-1 ns",
  "width-2 ns",
  "width-3 ns",
  "w1 wins",
  "w2 wins",
  "w3 wins",
  "lower-bound violations (some L_w < M_1)",
  "certified after w1 (L_1 == M_1)",
  "  ns of w2+w3 there",
  "certified after w2 (min(L_1,L_2) == M_1)",
  "  ns of w3 there",
  "w1 table <= 8 entries",
  "  ns of all widths there",
];
static CTRS: [AtomicU64; 14] = [const { AtomicU64::new(0) }; 14];

/// Add to a named counter.
pub fn ctr(c: Ctr, v: u64) {
  CTRS[c as usize].fetch_add(v, Ordering::Relaxed);
}

/// Add to a counter by index.
pub fn ctr_ix(i: usize, v: u64) {
  CTRS[i].fetch_add(v, Ordering::Relaxed);
}

/// Extra counters: duplicate constructions.
pub static DUP_SHARE_NS: AtomicU64 = AtomicU64::new(0);
pub static DUP_PUTHASH_NS: AtomicU64 = AtomicU64::new(0);
pub static DUP_COUNT: AtomicU64 = AtomicU64::new(0);
pub static STORE_COUNT: AtomicU64 = AtomicU64::new(0);
pub static STORE_SHARE_NS: AtomicU64 = AtomicU64::new(0);

struct State {
  stack: Vec<(usize, Instant, u64)>,
  incl: [u64; N],
  excl: [u64; N],
  calls: [u64; N],
  dirty: u64,
  /// Elapsed ns of the last `Share` scope and of the last put+hash on this
  /// thread (for the duplicate accounting).
  last_share: u64,
  last_puthash: u64,
}

thread_local! {
  static ST: RefCell<State> = const { RefCell::new(State {
    stack: Vec::new(),
    incl: [0; N],
    excl: [0; N],
    calls: [0; N],
    dirty: 0,
    last_share: 0,
    last_puthash: 0,
  }) };
}

/// An open scope; closes on drop.
pub struct Scope {
  active: bool,
}

/// Open a scope of `area`.
#[inline]
pub fn scope(area: Area) -> Scope {
  if !*ENABLED {
    return Scope { active: false };
  }
  ST.with(|s| s.borrow_mut().stack.push((area as usize, Instant::now(), 0)));
  Scope { active: true }
}

impl Drop for Scope {
  fn drop(&mut self) {
    if !self.active {
      return;
    }
    ST.with(|s| {
      let mut s = s.borrow_mut();
      let Some((a, t, child)) = s.stack.pop() else { return };
      let el = u64::try_from(t.elapsed().as_nanos()).unwrap_or(0);
      s.incl[a] += el;
      s.excl[a] += el.saturating_sub(child);
      s.calls[a] += 1;
      s.dirty |= 1u64 << a;
      if a == Area::Share as usize {
        s.last_share = el;
      }
      if let Some(top) = s.stack.last_mut() {
        top.2 += el;
      } else {
        let mut d = s.dirty;
        while d != 0 {
          let i = d.trailing_zeros() as usize;
          d &= d - 1;
          INCL[i].fetch_add(s.incl[i], Ordering::Relaxed);
          EXCL[i].fetch_add(s.excl[i], Ordering::Relaxed);
          CALLS[i].fetch_add(s.calls[i], Ordering::Relaxed);
          s.incl[i] = 0;
          s.excl[i] = 0;
          s.calls[i] = 0;
        }
        s.dirty = 0;
      }
    });
  }
}

/// Record the put+hash time of the block constant just built.
pub fn note_puthash(ns: u64) {
  if *ENABLED {
    ST.with(|s| s.borrow_mut().last_puthash = ns);
  }
}

/// Before storing a block constant: `exists` says whether its address was
/// already in the environment (a duplicate construction).
pub fn note_store(exists: bool) {
  if !*ENABLED {
    return;
  }
  ST.with(|s| {
    let s = s.borrow();
    STORE_COUNT.fetch_add(1, Ordering::Relaxed);
    STORE_SHARE_NS.fetch_add(s.last_share, Ordering::Relaxed);
    if exists {
      DUP_COUNT.fetch_add(1, Ordering::Relaxed);
      DUP_SHARE_NS.fetch_add(s.last_share, Ordering::Relaxed);
      DUP_PUTHASH_NS.fetch_add(s.last_puthash, Ordering::Relaxed);
    }
  });
}

/// Print the counters to stderr (seconds summed over threads).
pub fn report(label: &str) {
  if !*ENABLED {
    return;
  }
  let mut tot_excl = 0u64;
  for i in 0..N {
    tot_excl += EXCL[i].load(Ordering::Relaxed);
  }
  eprintln!(
    "[areas] {label}: area | excl s | incl s | calls | excl % (sum excl {:.1} s)",
    tot_excl as f64 / 1e9
  );
  for i in 0..N {
    let e = EXCL[i].load(Ordering::Relaxed);
    let c = CALLS[i].load(Ordering::Relaxed);
    if c == 0 {
      continue;
    }
    eprintln!(
      "[areas] {:<40} | {:>9.2} | {:>9.2} | {:>10} | {:>5.1}",
      NAMES[i],
      e as f64 / 1e9,
      INCL[i].load(Ordering::Relaxed) as f64 / 1e9,
      c,
      100.0 * e as f64 / tot_excl.max(1) as f64
    );
  }
  eprintln!(
    "[areas] {label}: block constants stored {} (share {:.2} s); duplicates {} (share {:.2} s, put+hash {:.2} s)",
    STORE_COUNT.load(Ordering::Relaxed),
    STORE_SHARE_NS.load(Ordering::Relaxed) as f64 / 1e9,
    DUP_COUNT.load(Ordering::Relaxed),
    DUP_SHARE_NS.load(Ordering::Relaxed) as f64 / 1e9,
    DUP_PUTHASH_NS.load(Ordering::Relaxed) as f64 / 1e9,
  );
  for (i, name) in CTR_NAMES.iter().enumerate() {
    let v = CTRS[i].load(Ordering::Relaxed);
    if name.ends_with(" ns") || name.contains("ns of") {
      eprintln!("[areas] ctr {name}: {:.2} s", v as f64 / 1e9);
    } else {
      eprintln!("[areas] ctr {name}: {v}");
    }
  }
}

static HIST_N: [AtomicU64; 40] = [const { AtomicU64::new(0) }; 40];
static HIST_NS: [AtomicU64; 40] = [const { AtomicU64::new(0) }; 40];
static AUXH_N: [AtomicU64; 40] = [const { AtomicU64::new(0) }; 40];
static AUXH_NS: [AtomicU64; 40] = [const { AtomicU64::new(0) }; 40];
static SLOW: std::sync::Mutex<Vec<(u64, String)>> =
  std::sync::Mutex::new(Vec::new());

fn bucket(ns: u64) -> usize {
  (64 - ns.max(1).leading_zeros() as usize).min(39)
}

/// Record one scheduler block's wall time (and its name if slow).
pub fn note_block(ns: u64, name: impl FnOnce() -> String) {
  if !*ENABLED {
    return;
  }
  let b = bucket(ns);
  HIST_N[b].fetch_add(1, Ordering::Relaxed);
  HIST_NS[b].fetch_add(ns, Ordering::Relaxed);
  if ns >= 200_000_000 {
    SLOW.lock().unwrap().push((ns, name()));
  }
}

/// Record one aux_gen call's wall time.
pub fn note_aux(ns: u64) {
  if !*ENABLED {
    return;
  }
  let b = bucket(ns);
  AUXH_N[b].fetch_add(1, Ordering::Relaxed);
  AUXH_NS[b].fetch_add(ns, Ordering::Relaxed);
}

/// Print the block-time histograms and the slowest blocks.
pub fn report_blocks() {
  if !*ENABLED {
    return;
  }
  for (label, n, s) in
    [("block", &HIST_N, &HIST_NS), ("aux_gen", &AUXH_N, &AUXH_NS)]
  {
    let tot: u64 = s.iter().map(|x| x.load(Ordering::Relaxed)).sum();
    eprintln!("[areas] {label} time histogram (bucket < 2^k ns): count | sum s | share");
    for k in 0..40 {
      let c = n[k].load(Ordering::Relaxed);
      if c == 0 {
        continue;
      }
      let ns = s[k].load(Ordering::Relaxed);
      eprintln!(
        "[areas] {label} <2^{k:<2} ns ({:>10.3} ms) | {:>8} | {:>9.2} | {:>5.1}%",
        (1u64 << k) as f64 / 1e6,
        c,
        ns as f64 / 1e9,
        100.0 * ns as f64 / tot.max(1) as f64
      );
    }
  }
  let mut slow = SLOW.lock().unwrap().clone();
  slow.sort_by(|a, b| b.0.cmp(&a.0));
  let total: f64 = slow.iter().map(|x| x.0 as f64).sum::<f64>() / 1e9;
  eprintln!("[areas] blocks >= 0.2 s: {} totalling {:.1} s; slowest 40:", slow.len(), total);
  for (ns, name) in slow.iter().take(40) {
    eprintln!("[areas]   {:>8.3} s  {name}", *ns as f64 / 1e9);
  }
}

// Kernel-env use during aux_gen: distinct constants the kernel looks up
// outside ingress, against the constants ingressed.
thread_local! {
  static KTRACK: RefCell<(bool, u32, std::collections::HashSet<[u8; 32]>)> =
    RefCell::new((false, 0, std::collections::HashSet::new()));
}
static KT_CALLS: AtomicU64 = AtomicU64::new(0);
static KT_INGESTED: AtomicU64 = AtomicU64::new(0);
static KT_TOUCHED: AtomicU64 = AtomicU64::new(0);
static KT_MAX_INGESTED: AtomicU64 = AtomicU64::new(0);

/// Start tracking kernel lookups on this thread (one aux_gen call).
pub fn ktrack_begin() {
  if *ENABLED {
    KTRACK.with(|k| {
      let mut k = k.borrow_mut();
      k.0 = true;
      k.2.clear();
    });
  }
}

/// Stop tracking; record the env size and the distinct constants looked up.
pub fn ktrack_end(ingested: usize) {
  if *ENABLED {
    let touched = KTRACK.with(|k| {
      let mut k = k.borrow_mut();
      k.0 = false;
      k.2.len()
    });
    KT_CALLS.fetch_add(1, Ordering::Relaxed);
    KT_INGESTED.fetch_add(ingested as u64, Ordering::Relaxed);
    KT_TOUCHED.fetch_add(touched as u64, Ordering::Relaxed);
    KT_MAX_INGESTED.fetch_max(ingested as u64, Ordering::Relaxed);
  }
}

/// Entering (`true`) or leaving ingress code: lookups there do not count.
pub fn ktrack_ingress(enter: bool) {
  if *ENABLED {
    KTRACK.with(|k| {
      let mut k = k.borrow_mut();
      if enter {
        k.1 += 1;
      } else {
        k.1 = k.1.saturating_sub(1);
      }
    });
  }
}

/// RAII marker of ingress code.
pub struct KIngress;
impl KIngress {
  pub fn new() -> Self {
    ktrack_ingress(true);
    KIngress
  }
}
impl Default for KIngress {
  fn default() -> Self {
    Self::new()
  }
}
impl Drop for KIngress {
  fn drop(&mut self) {
    ktrack_ingress(false);
  }
}

/// A kernel-env lookup of `addr`.
#[inline]
pub fn ktrack_get(addr: &[u8; 32]) {
  if *ENABLED {
    KTRACK.with(|k| {
      let mut k = k.borrow_mut();
      if k.0 && k.1 == 0 {
        k.2.insert(*addr);
      }
    });
  }
}

/// Print the kernel-use counters.
pub fn report_ktrack() {
  if *ENABLED {
    eprintln!(
      "[areas] kernel use in aux_gen: {} calls, {} constants ingested (max {} in one call), {} distinct looked up outside ingress",
      KT_CALLS.load(Ordering::Relaxed),
      KT_INGESTED.load(Ordering::Relaxed),
      KT_MAX_INGESTED.load(Ordering::Relaxed),
      KT_TOUCHED.load(Ordering::Relaxed),
    );
  }
}

/// Reset all counters (between phases).
pub fn reset() {
  for i in 0..N {
    INCL[i].store(0, Ordering::Relaxed);
    EXCL[i].store(0, Ordering::Relaxed);
    CALLS[i].store(0, Ordering::Relaxed);
  }
}
