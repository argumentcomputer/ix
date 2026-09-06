//! Diagnostic name lookup without decoding expression metadata or checking.
//! cargo run --release -p ix-ffi --example resolve_anon_names -- FILE.ixe PREFIX...

use std::process::ExitCode;

fn run() -> Result<(), String> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  if args.len() < 2
    || args[1..].iter().any(|p| {
      p.len() < 8 || p.len() > 64 || !p.bytes().all(|c| c.is_ascii_hexdigit())
    })
  {
    return Err(
      "usage: resolve_anon_names FILE.ixe HEX_PREFIX... (8–64 hex digits)"
        .into(),
    );
  }
  let bytes = std::fs::read(&args[0]).map_err(|e| e.to_string())?;
  let index = ixon::env::Env::parse_lazy_index(&bytes)?;
  for entry in &index.named {
    let hex = entry.addr.hex();
    if args[1..].iter().any(|p| hex.starts_with(&p.to_ascii_lowercase())) {
      println!("{} {} {:?}", hex, entry.name, entry.hints);
    }
  }
  Ok(())
}

fn main() -> ExitCode {
  match run() {
    Ok(()) => ExitCode::SUCCESS,
    Err(e) => {
      eprintln!("{e}");
      ExitCode::FAILURE
    },
  }
}
