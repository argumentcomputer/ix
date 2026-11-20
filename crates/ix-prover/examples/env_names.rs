//! Print `address<TAB>name` for every named constant of a serialized `.ixe`
//! environment; with a shard manifest, also the index of the leaf that owns
//! the constant (`-` for a constant no leaf owns).
//!
//! ```text
//! env_names ENV.ixe [MANIFEST.ixes]
//! ```
use aggregate_controller::prepare;
use ix_prover::request::Environment;
use ixon::shard::ShardManifest;
use std::{error::Error, io::Write};

fn main() -> Result<(), Box<dyn Error>> {
  let args: Vec<String> = std::env::args().collect();
  let path = args.get(1).ok_or("usage: env_names ENV.ixe [MANIFEST.ixes]")?;
  // Names are metadata: only the full decode keeps them.
  let environment = Environment::from_bytes(&std::fs::read(path)?)?;
  let env = environment.env();
  let owners = match args.get(2) {
    Some(manifest) => {
      let manifest = ShardManifest::from_bytes(&std::fs::read(manifest)?)?;
      let context = aggregate_controller::claim_context(env, false)?;
      Some(prepare::prepare_run(&context, env, &manifest)?.owner_by_address)
    },
    None => None,
  };
  let stdout = std::io::stdout();
  let mut out = std::io::BufWriter::new(stdout.lock());
  for entry in env.named.iter() {
    let addr = &entry.value().addr;
    match &owners {
      Some(owners) => match owners.get(addr) {
        Some(leaf) => writeln!(out, "{}\t{}\t{leaf}", addr.hex(), entry.key().pretty())?,
        None => writeln!(out, "{}\t{}\t-", addr.hex(), entry.key().pretty())?,
      },
      None => writeln!(out, "{}\t{}", addr.hex(), entry.key().pretty())?,
    }
  }
  Ok(())
}
