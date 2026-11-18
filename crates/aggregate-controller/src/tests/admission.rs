//! Predicted-size admission against the fixed three-executions-per-GPU
//! policy, simulated in whole seconds over the record pool's own ledger.
//!
//! Claims execute on single-threaded executors whose records grow linearly
//! to their actual size, hand their records to one GPU through a one-slot
//! prepared queue, and release them when proven. An executor is busy from
//! admission until the prepared queue takes its record. The fixed policy is
//! the controller before predicted admission: three executor threads per
//! GPU, each admitted with an equal slot of the pool (`P / (3G + 2L)`) and
//! growing on demand. The predicted policy is the controller's: claims are
//! charged by `claim_prediction` and admitted by `Ledger::admit` with the record share `s` as overshoot
//! buffer and the fixed policy as its floor, on one executor thread per
//! core. Both share the ledger's growth, contention and ceiling rules.
//! Joins are not simulated. Each scenario prints both policies' finish
//! time, most executions at once, cancellations and the executor-seconds
//! they discarded, growth waits, frozen seconds, GPU idle seconds after the
//! first proof, mean executions at once, and executor-seconds blocked on
//! growth.

#![allow(
  clippy::cast_precision_loss,
  clippy::cast_possible_truncation,
  clippy::cast_sign_loss
)]

use ixon::shard::{
  RECORD_STORAGE_FACTOR, RecordShare, ShardInfo, predicted_record_bytes,
  record_share,
};
use record_pool::{Growth, Ledger};

use crate::lanes::{
  admission::{
    AGGREGATION_RECORD_BYTES, Basis, Prediction, aggregation_prediction,
    claim_prediction,
  },
  cell_workspace,
};

const GIB: usize = 1 << 30;
const RECORD_LIMIT: usize = 128 * GIB;

/// The 2026-11-16 Mathlib host: `MemTotal` less 10%, one GPU, 1.5e9
/// cells, 6.1 GiB resident, 32 cores.
fn machine() -> (usize, RecordShare) {
  let limit = 2247 * GIB / 10;
  let workspace = cell_workspace(1_500_000_000).unwrap();
  let records = limit - workspace - 61 * GIB / 10;
  (records, record_share(limit, workspace, 1))
}
const CORES: usize = 32;

/// Seconds of execution and of proof per GiB of record, and the slowdown
/// each further concurrent execution adds. Init on one GPU: a 29 GiB claim
/// executes in about 105 s and proves in about 52 s, and four executions
/// run 12–18% slower than one.
#[derive(Clone, Copy)]
struct Timing {
  exec_per_gib: f64,
  prove_per_gib: f64,
  slowdown: f64,
}

const MEASURED: Timing =
  Timing { exec_per_gib: 3.6, prove_per_gib: 1.8, slowdown: 0.04 };

#[derive(Clone, Copy, Debug)]
struct Claim {
  prediction: Prediction,
  actual: usize,
}

/// A claim whose model prediction is `predicted` GiB: owned bytes only, as
/// `claim_prediction` reads them from its manifest entry.
fn claim(predicted_gib: f64, actual_gib: f64) -> Claim {
  let per_byte = predicted_record_bytes(1 << 20, 0) as f64
    * RECORD_STORAGE_FACTOR
    / f64::from(1 << 20);
  let info = info((predicted_gib * GIB as f64 / per_byte).round() as u64);
  Claim {
    prediction: claim_prediction(&info),
    actual: (actual_gib * GIB as f64) as usize,
  }
}

/// The 55 claims of the 2026-11-04 Mathlib run (`mathlib-230.ixes`, one
/// GPU, `--exec-jobs 3`), in manifest order: owned bytes, frontier bytes and
/// the measured record bytes, at the storage layout before
/// [`RECORD_STORAGE_FACTOR`].
const MATHLIB: [(u64, u64, usize); 55] = [
  (17822058, 8338027, 43168991472),
  (19225441, 9817141, 39531291296),
  (22392754, 11351992, 45902594792),
  (17611571, 8936320, 46781913044),
  (16561896, 12971863, 53549961992),
  (22565039, 9923860, 52650889808),
  (18415050, 9410102, 46321726036),
  (20376992, 6228888, 41780294716),
  (22781330, 8151969, 44862730720),
  (22059308, 9805436, 48642830860),
  (19453649, 9599625, 50213120464),
  (18367358, 9646412, 54734315704),
  (18260912, 10382571, 51333514444),
  (17947820, 11720996, 52331037120),
  (17414867, 10229348, 52365398812),
  (16304535, 11571776, 53225750200),
  (22700859, 10203664, 67041339356),
  (21820833, 9671370, 50626722608),
  (21417071, 8749795, 50445988112),
  (19389637, 10187410, 79627708032),
  (20483193, 7129877, 60011261016),
  (20008823, 8919794, 64622447612),
  (18993696, 11258898, 57528593712),
  (21091105, 8018853, 49130846716),
  (24954639, 7983467, 52007349012),
  (21080364, 7697443, 77542818484),
  (19003084, 10507422, 91453811292),
  (21544988, 8375169, 63455145336),
  (19562055, 11376157, 60804828596),
  (27955248, 6916057, 54468257896),
  (22311762, 11132517, 49804012956),
  (21207636, 9675323, 57934794848),
  (21778748, 8304794, 57024220248),
  (19621758, 11967760, 55654604644),
  (18396443, 6871727, 46619326812),
  (16405968, 8768445, 48637713176),
  (21355155, 7609722, 66140282968),
  (19749080, 11777499, 58172026636),
  (21131527, 6491739, 81801946788),
  (19367797, 10705694, 91017394008),
  (27597096, 6042239, 64730684600),
  (16546219, 8919947, 58371568784),
  (19824933, 10598221, 63373321512),
  (25732050, 3282071, 82674370604),
  (22802623, 7941750, 43259690216),
  (20279062, 10409189, 47191067388),
  (29068718, 4030128, 51069452312),
  (16849823, 10424824, 51016079076),
  (19459401, 10282144, 55814797548),
  (25403534, 4822254, 58676616228),
  (27186678, 6110194, 50411829048),
  (18453784, 6364148, 45865722704),
  (17091450, 10537896, 50491011940),
  (25200129, 3079681, 60063975532),
  (22444735, 6903775, 56662093760),
];

fn mathlib_claims() -> Vec<Claim> {
  MATHLIB
    .iter()
    .map(|&(own_size, cross_ingress, actual)| Claim {
      prediction: claim_prediction(&ShardInfo {
        own_size,
        cross_ingress,
        ..info(0)
      }),
      actual: (actual as f64 * RECORD_STORAGE_FACTOR) as usize,
    })
    .collect()
}

fn info(own_size: u64) -> ShardInfo {
  ShardInfo {
    id: 0,
    blocks: Vec::new(),
    heartbeats: 0,
    own_size,
    foreign_blocks: Vec::new(),
    cross_ingress: 0,
    assumption_root: None,
    measured_peak_bytes: 0,
    measured_record_bytes: 0,
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Policy {
  Fixed,
  Predicted,
}

#[derive(Debug, Default)]
struct Outcome {
  finish: u64,
  max_executing: usize,
  cancellations: usize,
  discarded_secs: u64,
  frozen_secs: u64,
  waits: usize,
  splits: usize,
  gpu_idle: u64,
  executing_secs: u64,
  stalled_secs: u64,
}

struct Execution {
  claim: Claim,
  id: u64,
  started: u64,
  progress: f64,
  used: usize,
  credit: usize,
  waiting: bool,
  done: bool,
}

fn simulate(claims: &[Claim], policy: Policy, timing: Timing) -> Outcome {
  let (records, RecordShare { share, records: held }) = machine();
  let (mut ledger, threads) = match policy {
    Policy::Fixed => (Ledger::new(records, records / held), 3),
    Policy::Predicted => {
      (Ledger::new(records, share).with_buffer(share), CORES)
    },
  };
  ledger = ledger.with_record_limit(RECORD_LIMIT);
  let secs = |bytes: usize, per_gib: f64| bytes as f64 / GIB as f64 * per_gib;
  let mut queue: std::collections::VecDeque<Claim> =
    claims.iter().copied().collect();
  let mut running: Vec<Execution> = Vec::new();
  let mut prepared: Option<(u64, Claim)> = None;
  let mut proving: Option<(u64, f64)> = None;
  let mut to_split: Vec<Claim> = Vec::new();
  let mut cancelled: Vec<u64> = Vec::new();
  let mut proven = 0;
  let mut expected = claims.len();
  let mut out = Outcome::default();
  for now in 0..1_000_000u64 {
    // The GPU proves one record at a time from the one-slot queue.
    if let Some((id, left)) = proving.as_mut() {
      *left -= 1.0;
      if *left <= 0.0 {
        ledger.remove(*id);
        proving = None;
        proven += 1;
      }
    }
    if proving.is_none()
      && let Some((id, claim)) = prepared.take()
    {
      proving = Some((id, secs(claim.actual, timing.prove_per_gib)));
    }
    if let Some(index) = running.iter().position(|e| e.done)
      && prepared.is_none()
    {
      let execution = running.remove(index);
      prepared = Some((execution.id, execution.claim));
    }
    if proven == expected {
      out.finish = now;
      break;
    }
    // An over-ceiling claim is split once everything else has drained.
    if !to_split.is_empty()
      && running.is_empty()
      && prepared.is_none()
      && proving.is_none()
    {
      for claim in to_split.drain(..) {
        let prediction =
          Prediction { bytes: claim.prediction.bytes / 2, ..claim.prediction };
        let half = Claim { prediction, actual: claim.actual / 2 };
        queue.push_front(half);
        queue.push_front(half);
        expected += 2;
        out.splits += 1;
      }
    }
    while to_split.is_empty() && running.len() < threads {
      let Some(&claim) = queue.front() else { break };
      let admitted = match policy {
        Policy::Fixed => ledger.admit_initial(),
        Policy::Predicted => {
          ledger.admit(claim.prediction.bytes, running.len() < 3)
        },
      };
      let Some((id, grant)) = admitted else { break };
      queue.pop_front();
      running.push(Execution {
        claim,
        id,
        started: now,
        progress: 0.0,
        used: 0,
        credit: grant,
        waiting: false,
        done: false,
      });
    }
    let executing = running.iter().filter(|e| !e.done).count();
    out.executing_secs += executing as u64;
    out.stalled_secs += running.iter().filter(|e| e.waiting).count() as u64;
    if proving.is_none() && proven > 0 {
      out.gpu_idle += 1;
    }
    out.max_executing = out.max_executing.max(executing);
    if policy == Policy::Predicted && ledger.frozen() {
      out.frozen_secs += 1;
    }
    // A blocked execution waits on a condition variable and slows nobody.
    let progressing = running.iter().filter(|e| !e.done && !e.waiting).count();
    let speed =
      1.0 / (1.0 + timing.slowdown * progressing.saturating_sub(1) as f64);
    let mut index = 0;
    while index < running.len() {
      if running[index].done {
        index += 1;
        continue;
      }
      let id = running[index].id;
      if cancelled.contains(&id) {
        let execution = running.remove(index);
        ledger.remove(id);
        out.cancellations += 1;
        out.discarded_secs += now - execution.started;
        queue.push_back(execution.claim);
        continue;
      }
      let execution = &mut running[index];
      let duration = secs(execution.claim.actual, timing.exec_per_gib).max(1.0);
      let progress = (execution.progress + speed).min(duration);
      let target =
        (execution.claim.actual as f64 * progress / duration) as usize;
      let need = target - execution.used;
      if need > execution.credit {
        match ledger.grow(id, execution.credit, need, !execution.waiting) {
          Growth::Granted(extra) => execution.credit += extra,
          Growth::Wait { cancel } => {
            if !execution.waiting {
              out.waits += 1;
            }
            execution.waiting = true;
            cancelled.extend(cancel);
            index += 1;
            continue;
          },
          Growth::Exceeded { .. } => {
            let execution = running.remove(index);
            ledger.remove(id);
            to_split.push(execution.claim);
            expected -= 1;
            continue;
          },
          Growth::Cancelled => unreachable!("cancellations are handled first"),
        }
      }
      execution.waiting = false;
      execution.credit -= need;
      execution.used = target;
      execution.progress = progress;
      if progress >= duration {
        ledger.finish_execution(id, execution.credit);
        execution.credit = 0;
        execution.done = true;
      }
      index += 1;
    }
  }
  assert!(out.finish > 0, "{policy:?} never finished");
  assert_eq!(ledger.stats().reserved, 0);
  out
}

fn compare(name: &str, claims: &[Claim], timing: Timing) -> (Outcome, Outcome) {
  let fixed = simulate(claims, Policy::Fixed, timing);
  let predicted = simulate(claims, Policy::Predicted, timing);
  for (policy, out) in [("fixed 3/GPU", &fixed), ("predicted", &predicted)] {
    eprintln!(
      "{name:<34} {policy:<12} finish {:>6}s  max executing {:>2}  cancelled {:>2} ({:>5} executor-s)  growth waits {:>3}  frozen {:>5}s  splits {} gpu-idle {} mean-exec {:.2} stalled {}",
      out.finish,
      out.max_executing,
      out.cancellations,
      out.discarded_secs,
      out.waits,
      out.frozen_secs,
      out.splits,
      out.gpu_idle,
      out.executing_secs as f64 / out.finish as f64,
      out.stalled_secs,
    );
  }
  (fixed, predicted)
}

/// Sizes cycling through 34–46 GiB: a seeded Mathlib partition.
fn ordinary(count: usize) -> Vec<f64> {
  (0..count).map(|i| 34.0 + (i * 5 % 13) as f64).collect()
}

/// No more cancellations or discarded work than the fixed policy, and a
/// finish within 2% of it: when the GPU is the bottleneck both policies
/// finish together, and the extra executions only contend for the cores.
fn assert_no_worse(fixed: &Outcome, predicted: &Outcome) {
  assert!(predicted.cancellations <= fixed.cancellations);
  assert!(predicted.discarded_secs <= fixed.discarded_secs);
  assert!(predicted.finish * 50 <= fixed.finish * 51);
}

fn ordinary_claims() -> Vec<Claim> {
  ordinary(24).into_iter().map(|gib| claim(gib, gib)).collect()
}

#[test]
fn accurate_predictions_never_cancel_or_freeze() {
  let (fixed, predicted) =
    compare("accurate, 34-46 GiB", &ordinary_claims(), MEASURED);
  assert_no_worse(&fixed, &predicted);
  assert_eq!(predicted.cancellations, 0);
  assert_eq!(predicted.frozen_secs, 0);
}

#[test]
fn mathlib_claims_as_measured() {
  let (fixed, predicted) =
    compare("Mathlib, 55 measured claims", &mathlib_claims(), MEASURED);
  assert_no_worse(&fixed, &predicted);
}

#[test]
fn light_claims_run_many_at_once() {
  let (_, RecordShare { share, .. }) = machine();
  let quarter = share as f64 / GIB as f64 / 4.0;
  let claims: Vec<Claim> = (0..64).map(|_| claim(quarter, quarter)).collect();
  let (fixed, predicted) = compare("light, s/4", &claims, MEASURED);
  assert_no_worse(&fixed, &predicted);
  assert!(predicted.max_executing >= 4 * fixed.max_executing);
  // Execution-bound: claims whose execution takes twice as long per byte,
  // as typechecking-heavy shards do.
  let slow = Timing { exec_per_gib: 7.2, ..MEASURED };
  let (fixed, predicted) = compare("light, s/4, exec-bound", &claims, slow);
  assert_no_worse(&fixed, &predicted);
  assert!(predicted.finish * 10 < fixed.finish * 9);
}

#[test]
fn one_claim_heavier_than_predicted() {
  // Three times its prediction but within one share over it: absorbed by
  // the buffer.
  let mut claims = ordinary_claims();
  claims[1] = claim(15.0, 45.0);
  let (fixed, predicted) =
    compare("one 3x claim, 15 -> 45 GiB", &claims, MEASURED);
  assert_no_worse(&fixed, &predicted);
  assert_eq!(predicted.cancellations, 0);
  assert_eq!(predicted.frozen_secs, 0);
  // Three times a share-sized prediction, twice the buffer past it, and
  // over the ceiling, at each of the first twelve places in the order.
  let mut sweeps = Vec::new();
  for (predicted_gib, actual_gib) in
    [(40.0, 80.0), (40.0, 120.0), (40.0, 200.0)]
  {
    let mut totals = [Outcome::default(), Outcome::default()];
    for place in 0..12 {
      let mut claims = ordinary_claims();
      claims[place] = claim(predicted_gib, actual_gib);
      for (total, policy) in
        totals.iter_mut().zip([Policy::Fixed, Policy::Predicted])
      {
        let out = simulate(&claims, policy, MEASURED);
        total.finish += out.finish;
        total.cancellations += out.cancellations;
        total.discarded_secs += out.discarded_secs;
        total.splits += out.splits;
      }
    }
    let [fixed, predicted] = totals;
    eprintln!(
      "one claim {predicted_gib} -> {actual_gib} GiB at places 0-11, summed: fixed finish {}s, {} cancelled ({} executor-s), {} splits; predicted finish {}s, {} cancelled ({} executor-s), {} splits",
      fixed.finish,
      fixed.cancellations,
      fixed.discarded_secs,
      fixed.splits,
      predicted.finish,
      predicted.cancellations,
      predicted.discarded_secs,
      predicted.splits,
    );
    sweeps.push((fixed, predicted));
  }
  // An overshoot of exactly the buffer is absorbed without a wait or a
  // freeze; the finish differs from the fixed policy's by up to 19 s either
  // way per placement, from which execution the pool happens to feed
  // first, and 0.3% summed.
  let (fixed, predicted) = &sweeps[0];
  assert_eq!(predicted.cancellations, 0);
  assert!(predicted.finish * 100 <= fixed.finish * 101);
  for (fixed, predicted) in &sweeps[1..] {
    assert_no_worse(fixed, predicted);
  }
}

#[test]
fn a_claim_over_the_ceiling_is_split() {
  let mut claims = ordinary_claims();
  claims[2] = claim(40.0, 200.0);
  let (fixed, predicted) =
    compare("one claim over the ceiling", &claims, MEASURED);
  assert_eq!((fixed.splits, predicted.splits), (1, 1));
  assert_no_worse(&fixed, &predicted);
}

#[test]
fn small_and_large_claims_mixed() {
  let claims: Vec<Claim> = (0..32)
    .map(|i| if i % 2 == 0 { claim(10.0, 10.0) } else { claim(60.0, 60.0) })
    .collect();
  let (fixed, predicted) = compare("mixed 10 and 60 GiB", &claims, MEASURED);
  assert_no_worse(&fixed, &predicted);
  assert_eq!(predicted.cancellations, 0);
}

/// Claims predicted light that all turn out four times heavier, for the
/// whole run or after a stretch of accurate ones: many heavy claims start
/// together, and their correlated overshoot far exceeds the one-share
/// buffer. Each claim is charged by its own prediction, never by what other
/// claims measured, so nothing holds the extra executions back: the pool
/// fills, and executions that cannot grow are cancelled and rerun. The GPU
/// stays fed by the executions that do finish, so the cost is bounded to a
/// few percent of the run.
#[test]
fn correlated_overshoot() {
  let claims: Vec<Claim> = (0..24).map(|_| claim(10.0, 40.0)).collect();
  let (fixed, predicted) =
    compare("correlated 4x, 10 -> 40 GiB", &claims, MEASURED);
  assert!(predicted.finish * 20 <= fixed.finish * 21);
  let claims: Vec<Claim> = (0..48)
    .map(|i| if i < 16 { claim(10.0, 10.0) } else { claim(10.0, 40.0) })
    .collect();
  let (fixed, predicted) =
    compare("16 accurate, then 32 at 4x", &claims, MEASURED);
  assert!(predicted.finish * 20 <= fixed.finish * 21);
  eprintln!(
    "correlated overshoot: predicted finishes {:+.1}% against fixed, {} cancellations discarding {} executor-s against {} and {}",
    (predicted.finish as f64 / fixed.finish as f64 - 1.0) * 100.0,
    predicted.cancellations,
    predicted.discarded_secs,
    fixed.cancellations,
    fixed.discarded_secs,
  );
}

/// A join is charged its larger input once both are measured, whatever
/// larger aggregations came before; the largest aggregation so far only
/// stands in for an unmeasured input, and the constant for an empty run.
#[test]
fn aggregation_charges() {
  let both = aggregation_prediction(Some(40 * GIB), [Some(20 * GIB), Some(25 * GIB)]);
  assert_eq!(both, Prediction { bytes: 25 * GIB, basis: Basis::Inputs });
  let one = aggregation_prediction(Some(40 * GIB), [Some(20 * GIB), None]);
  assert_eq!(one, Prediction { bytes: 40 * GIB, basis: Basis::Observed });
  let none = aggregation_prediction(None, [None, Some(20 * GIB)]);
  assert_eq!(
    none,
    Prediction { bytes: AGGREGATION_RECORD_BYTES, basis: Basis::Constant }
  );
}
