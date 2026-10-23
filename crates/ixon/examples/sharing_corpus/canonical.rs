//! Fixed-rule corpus receipts through the ordinary production API.
//! No variable gate, classification observer or noncanonical entry point.

use super::*;

fn preserve(path: &std::path::Path, bytes: &[u8]) -> Result<(), String> {
  match std::fs::OpenOptions::new().write(true).create_new(true).open(path) {
    Ok(mut file) => file.write_all(bytes).map_err(|e| e.to_string()),
    Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
      if std::fs::read(path).map_err(|e| e.to_string())? == bytes {
        Ok(())
      } else {
        Err(format!("refusing differing artifact {}", path.display()))
      }
    },
    Err(e) => Err(e.to_string()),
  }
}

pub(super) fn run(
  args: &Args,
  limits: &ExactSharingLimits,
  mmap: &[u8],
  consts: &[ixon::env::LazyConstSlice],
) -> Result<(), String> {
  let path = args.canonical_tsv.as_ref().ok_or("missing canonical TSV")?;
  let mut out = std::io::BufWriter::new(
    std::fs::OpenOptions::new()
      .write(true)
      .create_new(true)
      .open(path)
      .map_err(|e| e.to_string())?,
  );
  writeln!(out, "canonical\tv1\trule=sharing-k16-greedy-v1\tK=16\thash=blake3\tAPI=normalize_constant_sharing_tiered_par\tlimits={limits:?}")
    .map_err(|e| e.to_string())?;
  writeln!(
    out,
    "invocation\t{:?}\tconstant_order=serial\ttiming=includes-receipt-IO",
    std::env::args().collect::<Vec<_>>()
  )
  .map_err(|e| e.to_string())?;
  let export = args.canonical_export.as_ref().map(std::path::Path::new);
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
      "begin\t{addr}\tinput_bytes={}\tinput_hash={}",
      bytes.len(),
      blake3::hash(bytes)
    )
    .map_err(|e| e.to_string())?;
    out.flush().map_err(|e| e.to_string())?;
    eprintln!("[CANONICAL] BEGIN {addr}");
    let result = (|| -> Result<(), String> {
      if let Some(dir) = export {
        preserve(&dir.join(format!("{addr}.input.ixn")), bytes)?;
      }
      let mut input = bytes;
      let c = Constant::get(&mut input).map_err(|e| format!("decode: {e}"))?;
      if !input.is_empty() {
        return Err("decode: trailing constant bytes".into());
      }
      let (candidate, result) = normalize_constant_sharing_tiered_par(
        LAYOUT,
        &c,
        limits,
        args.parallel,
      )
      .map_err(|e| e.to_string())?;
      let mut encoded = Vec::new();
      candidate.put(&mut encoded);
      if let Some(dir) = export {
        preserve(&dir.join(format!("{addr}.canonical.ixn")), &encoded)?;
      }
      writeln!(out, "output\t{addr}\tbytes={}\tinput_equal={}\thash={}\tselected_width={}\tselected_width_max_component={}\tmeters={:?}",
        encoded.len(), encoded == bytes, blake3::hash(&encoded), result.stats.w,
        result.phase1.components.iter().map(Vec::len).max().unwrap_or(0), result.stats.candidate_meters)
        .map_err(|e| e.to_string())?;
      Ok(())
    })();
    let status = match result {
      Ok(()) => "ok-canonical".to_string(),
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
    eprintln!("[CANONICAL] END {addr} {status}");
  }
  if failed == 0 {
    Ok(())
  } else {
    Err(format!("{failed} canonical constants failed"))
  }
}
