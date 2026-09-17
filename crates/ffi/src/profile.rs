//! Opt-in lightweight summaries and timestamped profiling events.

use std::{
  fs::{File, OpenOptions},
  io::Write,
  sync::{Arc, Mutex, Once, OnceLock},
  time::{SystemTime, UNIX_EPOCH},
};

use serde_json::{Map, Value, json};
use tracing::{Subscriber, field::Visit, span};
use tracing_subscriber::{
  Layer, filter::filter_fn, layer::Context, prelude::*,
};

mod metrics;

type Sink = Arc<Mutex<File>>;
static SINK: OnceLock<Option<Sink>> = OnceLock::new();
static INIT: Once = Once::new();

thread_local! {
  static TID: String = std::fs::read_link("/proc/thread-self")
    .ok()
    .and_then(|path| path.file_name().map(|name| name.to_string_lossy().into_owned()))
    .unwrap_or_else(|| format!("{:?}", std::thread::current().id()));
}

struct Fields(Map<String, Value>);

impl Visit for Fields {
  fn record_debug(
    &mut self,
    field: &tracing::field::Field,
    value: &dyn std::fmt::Debug,
  ) {
    self.0.insert(field.name().into(), json!(format!("{value:?}")));
  }
}

struct Timeline(Sink);

impl Timeline {
  fn emit(&self, mut event: Value) {
    event["ts_ns"] = json!(
      SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos() as u64
    );
    event["tid"] = TID.with(|tid| json!(tid));
    event["pid"] = json!(std::process::id());
    let mut line = serde_json::to_vec(&event).expect("span event is JSON");
    line.push(b'\n');
    // Write through: the global subscriber outlives Rust's ordinary drop scope.
    if let Err(error) = self.0.lock().unwrap().write_all(&line) {
      eprintln!("[profile] span write failed: {error}");
    }
  }
}

impl<S: Subscriber> Layer<S> for Timeline {
  fn on_new_span(
    &self,
    attrs: &span::Attributes<'_>,
    id: &span::Id,
    ctx: Context<'_, S>,
  ) {
    let mut fields = Fields(Map::new());
    attrs.record(&mut fields);
    let parent = attrs.parent().cloned().or_else(|| {
      attrs.is_contextual().then(|| ctx.current_span().id().cloned()).flatten()
    });
    self.emit(json!({"event": "new", "id": id.into_u64(),
      "parent": parent.map(|id| id.into_u64()), "name": attrs.metadata().name(),
      "target": attrs.metadata().target(), "fields": fields.0}));
  }

  fn on_record(
    &self,
    id: &span::Id,
    values: &span::Record<'_>,
    _: Context<'_, S>,
  ) {
    let mut fields = Fields(Map::new());
    values.record(&mut fields);
    self.emit(
      json!({"event": "record", "id": id.into_u64(), "fields": fields.0}),
    );
  }

  fn on_enter(&self, id: &span::Id, _: Context<'_, S>) {
    self.emit(json!({"event": "enter", "id": id.into_u64()}));
  }

  fn on_exit(&self, id: &span::Id, _: Context<'_, S>) {
    self.emit(json!({"event": "exit", "id": id.into_u64()}));
  }

  fn on_close(&self, id: span::Id, _: Context<'_, S>) {
    self.emit(json!({"event": "close", "id": id.into_u64()}));
  }
}

pub(crate) fn layer<S>() -> Option<impl Layer<S>>
where
  S: Subscriber + for<'span> tracing_subscriber::registry::LookupSpan<'span>,
{
  let sink = SINK.get_or_init(|| {
    let path = std::env::var_os("AIUR_PROFILE")?;
    match OpenOptions::new().write(true).create_new(true).open(&path) {
      Ok(file) => Some(Arc::new(Mutex::new(file))),
      Err(error) => {
        eprintln!("[profile] cannot create {path:?}: {error}");
        None
      },
    }
  });
  sink.as_ref().map(|sink| {
    Timeline(sink.clone()).with_filter(filter_fn(|meta| {
      meta.is_span()
        && ["aiur/", "stark/", "cuda/"]
          .iter()
          .any(|p| meta.name().starts_with(p))
    }))
  })
}

pub(crate) fn init() {
  if std::env::var_os("AIUR_PROFILE").is_none()
    && std::env::var_os("AIUR_METRICS").is_none()
    && std::env::var_os("RUST_LOG").is_none()
  {
    return;
  }
  INIT.call_once(|| {
    let mut layers = Vec::new();
    if let Some(timeline) = layer::<tracing_subscriber::Registry>() {
      layers.push(timeline.boxed());
    }
    if let Some(metrics) = metrics::Metrics::from_env() {
      layers.push(metrics.with_filter(filter_fn(metrics::selected)).boxed());
    }
    if let Ok(filter) = std::env::var("RUST_LOG") {
      layers.push(
        tracing_subscriber::fmt::layer()
          .with_ansi(false)
          .with_writer(std::io::stderr)
          .with_filter(tracing_subscriber::EnvFilter::new(filter))
        .boxed(),
      );
    }
    if layers.is_empty() {
      return;
    }
    if let Err(error) = tracing_subscriber::registry().with(layers).try_init() {
      eprintln!("[profile] cannot install subscriber: {error}");
    }
  });
}
