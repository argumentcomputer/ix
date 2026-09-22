//! Aggregated host timings and counters, with one record per proving boundary.

use std::{
  collections::{BTreeMap, HashMap},
  fs::{File, OpenOptions},
  io::Write,
  sync::{
    Arc, Mutex,
    atomic::{AtomicU64, Ordering},
  },
  thread::ThreadId,
  time::{Instant, SystemTime, UNIX_EPOCH},
};

use serde_json::{Map, Value, json};
use tracing::{
  Event, Subscriber,
  field::{Field, Visit},
  span,
};
use tracing_subscriber::{Layer, layer::Context, registry::LookupSpan};

const TARGET: &str = "prover_metrics";
static NEXT_ID: AtomicU64 = AtomicU64::new(1);

pub(super) fn selected(metadata: &tracing::Metadata<'_>) -> bool {
  if metadata.is_event() {
    return metadata.target() == TARGET;
  }
  matches!(
    metadata.name(),
    "aiur/metrics_unit"
      | "aiur/prove_planned"
      | "aiur/prove_records"
      | "aiur/witness"
      | "stark/batch_round_1"
      | "stark/batch_round_2"
      | "aiur/cpu_circuit"
      | "aiur/codegen_seeds"
      | "aiur/codegen_filter"
      | "aiur/codegen_pack"
      | "aiur/codegen_widen"
      | "aiur/codegen_concat"
      | "aiur/codegen_memory_seeds"
      | "stark/stage1_commit"
      | "stark/commit_merkle"
      | "stark/lookup_construction"
      | "stark/quotient"
      | "stark/fri_open"
      | "stark/fri_prepare"
      | "stark/fri_interpolate"
      | "stark/fri_reduce"
      | "stark/fri_prove"
      | "stark/fri_queries"
      | "cuda/lde"
      | "cuda/lookup_lde"
      | "cuda/quotient_lde"
      | "cuda/dft_batch"
      | "cuda/coset_lde_batch"
  )
}

#[derive(Default)]
struct Fields(Map<String, Value>);

impl Visit for Fields {
  fn record_u64(&mut self, f: &Field, v: u64) {
    self.0.insert(f.name().into(), v.into());
  }
  fn record_i64(&mut self, f: &Field, v: i64) {
    self.0.insert(f.name().into(), v.into());
  }
  fn record_bool(&mut self, f: &Field, v: bool) {
    self.0.insert(f.name().into(), v.into());
  }
  fn record_str(&mut self, f: &Field, v: &str) {
    self.0.insert(f.name().into(), v.into());
  }
  fn record_debug(&mut self, f: &Field, v: &dyn std::fmt::Debug) {
    let value = format!("{v:?}");
    self.0.insert(
      f.name().into(),
      value.parse::<u64>().map_or_else(|_| value.into(), Value::from),
    );
  }
}

#[derive(Default)]
struct Total {
  count: u64,
  elapsed_sum_ns: u64,
  counters: BTreeMap<String, u64>,
  last: BTreeMap<String, u64>,
}

#[derive(Default)]
struct Aggregate(BTreeMap<(String, String), Total>);

impl Aggregate {
  fn add(
    &mut self,
    name: &str,
    labels: &Map<String, Value>,
    elapsed: u64,
    counters: BTreeMap<String, u64>,
    last: BTreeMap<String, u64>,
  ) {
    let key =
      (name.into(), serde_json::to_string(labels).expect("metric labels"));
    let total = self.0.entry(key).or_default();
    total.count += 1;
    total.elapsed_sum_ns = total.elapsed_sum_ns.saturating_add(elapsed);
    for (key, value) in counters {
      let count = total.counters.entry(key).or_default();
      *count = count.saturating_add(value);
    }
    total.last.extend(last);
  }

  fn rows(&self) -> Vec<Value> {
    self.0.iter().map(|((name, labels), total)| json!({
      "name": name, "labels": serde_json::from_str::<Value>(labels).expect("metric labels"),
      "count": total.count, "elapsed_sum_ns": total.elapsed_sum_ns,
      "counters": total.counters, "last": total.last,
    })).collect()
  }
}

struct Bucket {
  id: u64,
  parent: Option<u64>,
  identity: Map<String, Value>,
  started: Instant,
  totals: Mutex<Aggregate>,
}

struct State {
  bucket: Arc<Bucket>,
  name: &'static str,
  fields: Map<String, Value>,
  boundary: bool,
  // A carrier span can be entered on both the producer and consumer threads.
  // Count each thread's outermost entry; these durations are sums, not unions.
  active: HashMap<ThreadId, (usize, Instant)>,
  elapsed: u64,
}

pub(super) struct Metrics {
  output: Mutex<File>,
}

impl Metrics {
  pub(super) fn from_env() -> Option<Self> {
    let path = std::env::var_os("AIUR_METRICS")?;
    match OpenOptions::new().write(true).create_new(true).open(&path) {
      Ok(file) => {
        let layer = Self { output: Mutex::new(file) };
        let controls: BTreeMap<_, _> = [
          "AIUR_GPU_TRACE",
          "AIUR_TRACE_ONLY_LOOKUPS",
          "AIUR_GPU_TRACE_MEMORY",
          "AIUR_GPU_SEED_CACHE_BYTES",
          "AIUR_MAX_PIECE_LOG_HEIGHT",
          "AIUR_TRACE_SHARD_MAX_CELLS",
          "MULTI_STARK_CUDA_MIN_FREE_BYTES",
          "CUDA_VISIBLE_DEVICES",
          "RAYON_NUM_THREADS",
          "AIUR_METRICS_RUN_ID",
        ]
        .into_iter()
        .filter_map(|name| std::env::var(name).ok().map(|v| (name, v)))
        .collect();
        layer.write(&json!({"type": "metadata", "schema": 1,
          "pid": std::process::id(), "controls": controls,
          "executable": std::env::current_exe().ok(),
          "timing": "host elapsed sums; overlapping and nested durations are not additive wall time",
          "device_counters": "cumulative per process and device; never attribute snapshot deltas to concurrent proofs"}));
        Some(layer)
      },
      Err(error) => {
        eprintln!("[metrics] cannot create {path:?}: {error}");
        None
      },
    }
  }

  fn write(&self, value: &Value) {
    let mut bytes = serde_json::to_vec(value).expect("metric record");
    bytes.push(b'\n');
    if let Err(error) = self.output.lock().unwrap().write_all(&bytes) {
      eprintln!("[metrics] write failed: {error}");
    }
  }
}

impl<S: Subscriber + for<'a> LookupSpan<'a>> Layer<S> for Metrics {
  fn on_new_span(
    &self,
    attrs: &span::Attributes<'_>,
    id: &span::Id,
    ctx: Context<'_, S>,
  ) {
    let Some(span) = ctx.span(id) else {
      return;
    };
    let parent = span.parent().and_then(|p| {
      p.scope().find_map(|p| {
        p.extensions().get::<State>().map(|s| Arc::clone(&s.bucket))
      })
    });
    let mut fields = Fields::default();
    attrs.record(&mut fields);
    let name = attrs.metadata().name();
    let boundary = matches!(
      name,
      "aiur/metrics_unit"
        | "aiur/prove_planned"
        | "aiur/prove_records"
        | "aiur/witness"
        | "stark/batch_round_1"
        | "stark/batch_round_2"
    );
    let bucket = if boundary {
      let mut identity =
        parent.as_ref().map_or_else(Map::new, |p| p.identity.clone());
      identity.extend(fields.0.clone());
      if name == "stark/batch_round_1" {
        identity.insert("round".into(), 1.into());
      }
      if name == "stark/batch_round_2" {
        identity.insert("round".into(), 2.into());
      }
      Arc::new(Bucket {
        id: NEXT_ID.fetch_add(1, Ordering::Relaxed),
        parent: parent.as_ref().map(|p| p.id),
        identity,
        started: Instant::now(),
        totals: Mutex::new(Aggregate::default()),
      })
    } else {
      let Some(parent) = parent else {
        return;
      };
      parent
    };
    span.extensions_mut().insert(State {
      bucket,
      name,
      fields: fields.0,
      boundary,
      active: HashMap::new(),
      elapsed: 0,
    });
  }

  fn on_enter(&self, id: &span::Id, ctx: Context<'_, S>) {
    let Some(span) = ctx.span(id) else {
      return;
    };
    let mut ext = span.extensions_mut();
    let Some(state) = ext.get_mut::<State>() else {
      return;
    };
    let entry = state
      .active
      .entry(std::thread::current().id())
      .or_insert_with(|| (0, Instant::now()));
    entry.0 += 1;
  }

  fn on_exit(&self, id: &span::Id, ctx: Context<'_, S>) {
    let Some(span) = ctx.span(id) else {
      return;
    };
    let mut ext = span.extensions_mut();
    let Some(state) = ext.get_mut::<State>() else {
      return;
    };
    let tid = std::thread::current().id();
    if let Some((depth, started)) = state.active.get_mut(&tid) {
      *depth -= 1;
      if *depth == 0 {
        state.elapsed = state.elapsed.saturating_add(
          u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX),
        );
        state.active.remove(&tid);
      }
    }
  }

  fn on_event(&self, event: &Event<'_>, ctx: Context<'_, S>) {
    let Some(span) = ctx.event_span(event) else {
      return;
    };
    let bucket = span.scope().find_map(|p| {
      p.extensions().get::<State>().map(|s| Arc::clone(&s.bucket))
    });
    let Some(bucket) = bucket else {
      return;
    };
    let mut fields = Fields::default();
    event.record(&mut fields);
    let name = fields
      .0
      .remove("metric")
      .and_then(|v| v.as_str().map(str::to_owned))
      .unwrap_or_else(|| "counter".into());
    let mut counters = BTreeMap::new();
    let mut last = BTreeMap::new();
    let mut labels = Map::new();
    let snapshot = fields.0.get("scope").and_then(Value::as_str)
      == Some("process_device_cumulative")
      || name == "lookup_admission";
    for (key, value) in fields.0 {
      let label = matches!(
        key.as_str(),
        "device"
          | "circuit"
          | "function"
          | "job"
          | "height"
          | "width"
          | "added_bits"
          | "log_height"
          | "width_bucket"
          | "backend"
      );
      if !label && let Some(value) = value.as_u64() {
        if snapshot || key == "cached_bytes" {
          last.insert(key, value);
        } else {
          counters.insert(key, value);
        }
      } else {
        labels.insert(key, value);
      }
    }
    bucket.totals.lock().unwrap().add(&name, &labels, 0, counters, last);
  }

  fn on_close(&self, id: span::Id, ctx: Context<'_, S>) {
    let Some(span) = ctx.span(&id) else {
      return;
    };
    let Some(state) = span.extensions_mut().remove::<State>() else {
      return;
    };
    if state.boundary {
      let mut record = json!({"type": "summary", "schema": 1, "pid": std::process::id(),
        "id": state.bucket.id, "parent": state.bucket.parent,
        "boundary": state.name, "identity": state.bucket.identity,
        "wall_elapsed_ns": u64::try_from(state.bucket.started.elapsed().as_nanos()).unwrap_or(u64::MAX),
        "elapsed_sum_ns": state.elapsed, "incomplete": std::thread::panicking(),
        "timestamp_ns": u64::try_from(SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_nanos()).unwrap_or(u64::MAX),
        "metrics": state.bucket.totals.lock().unwrap().rows()});
      #[cfg(feature = "cuda-trace-codegen")]
      {
        record["seed_cache_device_snapshot"] =
          aiur::trace_codegen::cuda::seed_cache_snapshot()
            .into_iter()
            .map(|(device, bytes, refused)| {
              json!({"device": device,
            "retained_bytes": bytes, "refused_requests": refused})
            })
            .collect::<Vec<_>>()
            .into();
      }
      record["process_rss_bytes"] =
        std::fs::read_to_string("/proc/self/status")
          .ok()
          .and_then(|s| {
            s.lines().find_map(|line| {
              line
                .strip_prefix("VmRSS:")
                .and_then(|v| v.split_whitespace().next())
                .and_then(|v| v.parse::<u64>().ok())
            })
          })
          .map(|kib| kib.saturating_mul(1024))
          .into();
      self.write(&record);
    } else {
      state.bucket.totals.lock().unwrap().add(
        state.name,
        &state.fields,
        state.elapsed,
        BTreeMap::new(),
        BTreeMap::new(),
      );
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use tracing_subscriber::{filter::filter_fn, prelude::*};

  fn capture(run: impl FnOnce()) -> Vec<Value> {
    let path = std::env::temp_dir().join(format!(
      "ix-metrics-{}-{}.jsonl",
      std::process::id(),
      NEXT_ID.fetch_add(1, Ordering::Relaxed)
    ));
    let file =
      OpenOptions::new().create_new(true).write(true).open(&path).unwrap();
    let subscriber = tracing_subscriber::registry().with(
      Metrics { output: Mutex::new(file) }.with_filter(filter_fn(selected)),
    );
    tracing::subscriber::with_default(subscriber, run);
    let result = std::fs::read_to_string(&path)
      .unwrap()
      .lines()
      .map(|line| serde_json::from_str(line).unwrap())
      .collect();
    std::fs::remove_file(path).unwrap();
    result
  }

  #[test]
  fn counters_are_bounded_by_piece_and_fine_events_are_disabled() {
    let records = capture(|| {
      let _proof =
        tracing::info_span!("aiur/prove_planned", pieces = 2).entered();
      assert!(
        tracing::info_span!("aiur/codegen_device_rows", rows = 65536)
          .is_disabled()
      );
      for shard in 0..2 {
        let _piece =
          tracing::info_span!("stark/batch_round_2", shard).entered();
        for _ in 0..3 {
          let _op =
            tracing::info_span!("cuda/lde", height = 16, width = 2).entered();
          tracing::info!(target: TARGET, metric = "seed_cache", device = 0, action = "upload", bytes = 64u64);
        }
      }
    });
    assert_eq!(records.len(), 3);
    for (shard, record) in records[..2].iter().enumerate() {
      assert_eq!(record["identity"]["shard"], shard);
      assert_eq!(record["identity"]["round"], 2);
      assert_eq!(record["parent"], records[2]["id"]);
      let metrics = record["metrics"].as_array().unwrap();
      let cache = metrics.iter().find(|m| m["name"] == "seed_cache").unwrap();
      assert_eq!(cache["count"], 3);
      assert_eq!(cache["counters"]["bytes"], 192);
      let lde = metrics.iter().find(|m| m["name"] == "cuda/lde").unwrap();
      assert_eq!(lde["count"], 3);
    }
  }

  #[test]
  fn concurrent_witnesses_keep_their_own_piece_identity() {
    let records = capture(|| {
      let _proof =
        tracing::info_span!("aiur/prove_planned", pieces = 2).entered();
      let dispatch = tracing::dispatcher::get_default(Clone::clone);
      let spans = (0..2)
        .map(|shard| tracing::info_span!("aiur/witness", shard, round = 1))
        .collect::<Vec<_>>();
      std::thread::scope(|scope| {
        for (shard, span) in spans.into_iter().enumerate() {
          let dispatch = dispatch.clone();
          scope.spawn(move || {
            tracing::dispatcher::with_default(&dispatch, || {
              let _entered = span.entered();
              for function in 0..4 {
                let _op =
                  tracing::info_span!("aiur/codegen_pack", function, rows = 8)
                    .entered();
                tracing::info!(target: TARGET, metric = "seed_pack", function,
                rows = 8u64, seed_bytes = (shard + 1) * 64);
              }
            })
          });
        }
      });
    });
    assert_eq!(records.len(), 3);
    for record in &records[..2] {
      let shard = record["identity"]["shard"].as_u64().unwrap();
      let counts = record["metrics"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|m| m["name"] == "seed_pack")
        .map(|m| m["counters"]["seed_bytes"].as_u64().unwrap())
        .collect::<Vec<_>>();
      assert_eq!(counts, vec![(shard + 1) * 64; 4]);
    }
  }

  #[test]
  fn unwinding_emits_an_incomplete_summary() {
    let records = capture(|| {
      let result = std::panic::catch_unwind(|| {
        let _piece =
          tracing::info_span!("stark/batch_round_1", shard = 5).entered();
        tracing::info!(target: TARGET, metric = "trace", rows = 8u64);
        panic!("fixture failure");
      });
      assert!(result.is_err());
    });
    assert_eq!(records.len(), 1);
    assert_eq!(records[0]["incomplete"], true);
    assert_eq!(records[0]["metrics"][0]["counters"]["rows"], 8);
  }

  #[test]
  fn cumulative_snapshots_and_gauges_are_not_summed() {
    let records = capture(|| {
      let _piece =
        tracing::info_span!("stark/batch_round_2", shard = 0).entered();
      for transforms in [5u64, 8] {
        tracing::info!(target: TARGET, metric = "ntt_snapshot", device = 0,
          scope = "process_device_cumulative", log_height = 20, transforms);
        tracing::info!(target: TARGET, metric = "host_coset", action = "hit",
          log_height = 20, cached_bytes = 1024u64);
      }
    });
    let rows = records[0]["metrics"].as_array().unwrap();
    let ntt = rows.iter().find(|r| r["name"] == "ntt_snapshot").unwrap();
    assert_eq!(ntt["last"]["transforms"], 8);
    assert_eq!(ntt["counters"], json!({}));
    let coset = rows.iter().find(|r| r["name"] == "host_coset").unwrap();
    assert_eq!(coset["count"], 2);
    assert_eq!(coset["last"]["cached_bytes"], 1024);
    assert!(records[0]["wall_elapsed_ns"].as_u64().unwrap() > 0);
  }
}
