//! The stage worker `ix compress` spawns: `ix-compression-worker <stage>
//! <args...>` runs one FRI, first KZG or recursive KZG stage. Stages run in
//! their own executable so the Lean executable links no KZG proving code or
//! its CUDA runtime, and so each heavy phase exits before the next starts.
use tracing_subscriber::{
  Layer, filter::FilterFn, layer::SubscriberExt, util::SubscriberInitExt,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let args: Vec<String> = std::env::args().skip(1).collect();
  let Some((stage, rest)) = args.split_first() else {
    return Err("usage: ix-compression-worker <fri|kzg|wrap> <args...>".into());
  };
  let texray = std::env::var("IX_TEXRAY").as_deref() == Ok("1");
  let timing = texray.then(|| {
    tracing_texray::TeXRayLayer::new().streaming().track_ram().with_filter(
      FilterFn::new(|metadata| {
        metadata.is_span()
          && (metadata.name().starts_with("compression/")
            || matches!(
              metadata.name(),
              "stark/stage1_commit"
                | "stark/lookup_construction"
                | "stark/stage2_commit"
                | "stark/quotient"
                | "stark/fri_open"
            ))
      }),
    )
  });
  tracing_subscriber::registry()
    .with(
      tracing_subscriber::fmt::layer()
        .with_writer(std::io::stderr)
        .with_ansi(false)
        .with_filter(tracing_subscriber::filter::LevelFilter::INFO),
    )
    .with(timing)
    .try_init()?;
  let span = match stage.as_str() {
    "fri" => tracing::info_span!("compression/fri"),
    "kzg" => tracing::info_span!("compression/kzg"),
    "wrap" => tracing::info_span!("compression/wrap"),
    _ => return Err("unknown compression stage".into()),
  };
  let span = if texray { tracing_texray::examine(span) } else { span };
  span.in_scope(|| ix_proof_compression::pipeline::command(stage, rest))
}
