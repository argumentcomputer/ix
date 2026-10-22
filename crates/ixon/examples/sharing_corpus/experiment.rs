//! Explicit offline branch of sharing_corpus. No output is published as a
//! canonical artifact. A flushed BEGIN without END is incomplete; the external
//! wrapper must record timeout/signal status, never count it as a success.

use super::*;
use ixon::sharing_exact::experimental::{self, Event};

/// Never replace evidence. Identical pre-existing artifacts may be reused.
fn preserve(path: &std::path::Path, bytes: &[u8]) -> Result<(), String> {
  match std::fs::OpenOptions::new().write(true).create_new(true).open(path) {
    Ok(mut file) => file.write_all(bytes).map_err(|e| e.to_string()),
    Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
      if std::fs::read(path).map_err(|e| e.to_string())? == bytes {
        Ok(())
      } else {
        Err(format!("refusing differing existing artifact {}", path.display()))
      }
    },
    Err(e) => Err(e.to_string()),
  }
}

fn ids(ts: &[u32]) -> String {
  ts.iter().map(u32::to_string).collect::<Vec<_>>().join(",")
}

fn emit(out: &mut impl Write, addr: &str, e: &Event) -> std::io::Result<()> {
  match e {
    Event::Component { width, index, mode, members, area, closure } => {
      writeln!(
        out,
        "component\t{addr}\t{width}\t{index}\t{mode}\t{}\t{area}\t{closure}",
        ids(members)
      )
    },
    Event::Row { width, index, mode, count, delta, selected } => writeln!(
      out,
      "row\t{addr}\t{width}\t{index}\t{mode}\t{count}\t{delta}\t{}",
      ids(selected)
    ),
    Event::Width { width, certain, uncertain, components, slack } => writeln!(
      out,
      "width\t{addr}\t{width}\t{certain}\t{uncertain}\t{components}\t{slack}"
    ),
    Event::Input {
      input_visits,
      interned_nodes,
      dag_nodes,
      edges,
      roots,
      table_entries,
      refs,
      univs,
      level_args,
      scalar_bits,
      max_scalar_bits,
    } => writeln!(
      out,
      "input\t{addr}\t{input_visits}\t{interned_nodes}\t{dag_nodes}\t{edges}\t{roots}\t{table_entries}\t{refs}\t{univs}\t{level_args}\t{scalar_bits}\t{max_scalar_bits}"
    ),
    Event::Progress => Ok(()),
  }
}

pub(super) fn run(
  args: &Args,
  limits: &ExactSharingLimits,
  mmap: &[u8],
  consts: &[ixon::env::LazyConstSlice],
) -> Result<(), String> {
  let path = args.experiment_tsv.as_ref().ok_or("missing experimental TSV")?;
  let mut out = std::io::BufWriter::new(
    std::fs::OpenOptions::new()
      .write(true)
      .create_new(true)
      .open(path)
      .map_err(|e| e.to_string())?,
  );
  writeln!(out, "experiment\tv1\tK={:?}\ttie=set_prec\tevaluator=rust-area-phi\tnumeric=u128/i128-checked\texact_baseline={}\tlimits={limits:?}",
    args.experiment_k, if args.experiment_input_canonical { "saved-input" } else { "unknown" }).map_err(|e| e.to_string())?;
  writeln!(
    out,
    "invocation\t{:?}\ttiming=includes-trace-IO",
    std::env::args().collect::<Vec<_>>()
  )
  .map_err(|e| e.to_string())?;
  let export = args.experiment_export.as_ref().map(std::path::Path::new);
  if let Some(dir) = export {
    std::fs::create_dir_all(dir).map_err(|e| e.to_string())?;
  }
  let mut failed = 0;
  for entry in consts {
    let addr = entry.addr.hex();
    let bytes = &mmap[entry.offset..entry.offset + entry.len];
    let start = Instant::now();
    writeln!(
      out,
      "begin\t{addr}\twire_bytes={}\tinput_hash={}",
      bytes.len(),
      blake3::hash(bytes)
    )
    .map_err(|e| e.to_string())?;
    out.flush().map_err(|e| e.to_string())?;
    eprintln!("[EXPERIMENT] BEGIN {addr} K={:?}", args.experiment_k);
    let result = (|| -> Result<(), String> {
      if let Some(dir) = export {
        preserve(&dir.join(format!("{addr}.input.ixn")), bytes)?;
      }
      let mut input = bytes;
      let c = Constant::get(&mut input).map_err(|e| format!("decode: {e}"))?;
      if !input.is_empty() {
        return Err("decode: trailing constant bytes".into());
      }
      let mut observe = |e: &Event| -> Result<(), SharingError> {
        if args
          .experiment_timeout_ms
          .is_some_and(|ms| start.elapsed().as_millis() >= ms as u128)
        {
          return Err(SharingError::Internal(
            "EXPERIMENT timeout (cooperative phase 1)".into(),
          ));
        }
        emit(&mut out, &addr, e)
          .and_then(|()| {
            if matches!(e, Event::Component { .. }) {
              out.flush()
            } else {
              Ok(())
            }
          })
          .map_err(|e| {
            SharingError::Internal(format!("EXPERIMENT trace IO: {e}"))
          })
      };
      if let Some(k) = args.experiment_k {
        let (candidate, result) =
          experimental::normalize(&c, limits, k, &mut observe)
            .map_err(|e| e.to_string())?;
        let mut encoded = Vec::new();
        candidate.put(&mut encoded);
        if let Some(dir) = export {
          preserve(
            &dir.join(format!("{addr}.K{k}.experimental.ixn")),
            &encoded,
          )?;
        }
        writeln!(out, "output\t{addr}\tbytes={}\tinput_equal={}\thash={}\tselected_width={}\tmeters={:?}",
          encoded.len(), encoded == bytes, blake3::hash(&encoded), result.stats.w,
          result.stats.candidate_meters).map_err(|e| e.to_string())?;
      } else {
        experimental::classify(&c, limits, &mut observe)
          .map_err(|e| e.to_string())?;
      }
      Ok(())
    })();
    let status = match result {
      Ok(()) => "ok-experimental".to_string(),
      Err(e) => {
        failed += 1;
        format!("failed:{e}")
      },
    };
    writeln!(
      out,
      "end\t{addr}\t{status}\tms={:.3}",
      start.elapsed().as_secs_f64() * 1e3
    )
    .map_err(|e| e.to_string())?;
    out.flush().map_err(|e| e.to_string())?;
    eprintln!("[EXPERIMENT] END {addr} {status}");
  }
  if failed == 0 {
    Ok(())
  } else {
    Err(format!(
      "{failed} experimental constants failed; no canonical output published"
    ))
  }
}
