//! Offline numeric diagnostic; no production algorithm or limit changes.
//! Usage: sharing_numeric EXPORT_DIR DEPTH (0..=512).
//! Closed term: fun (A : Type) (f : A -> A -> A) (z : A) => T_depth,
//! T_0=z, T_(i+1)=f T_i T_i. Every sharing row uses the same A/f/z scope.
//! Typing follows this construction; this executable does not run a kernel.

use std::io::Write;
use std::path::Path;
use std::sync::Arc;
use std::time::Instant;

use ix_common::env::DefinitionSafety;
use ixon::Env;
use ixon::constant::{Constant, ConstantInfo, DefKind, Definition};
use ixon::expr::Expr;
use ixon::sharing_exact::{ExactSharingLimits, SharingDag, experimental};
use ixon::univ::Univ;
use sha2::{Digest, Sha256};

fn tower(depth: u64) -> Constant {
  let binary = Expr::all(Expr::var(0), Expr::all(Expr::var(1), Expr::var(2)));
  let typ = Expr::all(
    Expr::sort(0),
    Expr::all(binary.clone(), Expr::all(Expr::var(1), Expr::var(2))),
  );
  let mut sharing = vec![Expr::var(0)];
  for i in 0..depth {
    let previous = Arc::new(Expr::Share(i));
    sharing
      .push(Expr::app(Expr::app(Expr::var(1), previous.clone()), previous));
  }
  let value = Expr::lam(
    Expr::sort(0),
    Expr::lam(binary, Expr::lam(Expr::var(1), Arc::new(Expr::Share(depth)))),
  );
  Constant::with_tables(
    ConstantInfo::Defn(Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ,
      value,
    }),
    sharing,
    vec![],
    vec![Univ::succ(Univ::zero())],
  )
}

// Independent scoped-subgrammar check; it never expands a Share.
fn scoped(e: &Expr, binders: u64, prior: u64) -> bool {
  match e {
    Expr::Var(i) => *i < binders,
    Expr::Sort(i) => *i == 0,
    Expr::Share(i) => binders == 3 && *i < prior,
    Expr::App(f, a) => scoped(f, binders, prior) && scoped(a, binders, prior),
    Expr::Lam(_, ty, body) | Expr::All(_, _, ty, body) => {
      scoped(ty, binders, prior) && scoped(body, binders + 1, prior)
    },
    _ => false,
  }
}

fn validate(c: &Constant) -> Result<SharingDag, String> {
  let ConstantInfo::Defn(d) = &c.info else {
    return Err("not a definition".into());
  };
  let count = u64::try_from(c.sharing.len())
    .map_err(|e| format!("sharing length exceeds u64: {e}"))?;
  if d.kind != DefKind::Definition
    || d.safety != DefinitionSafety::Safe
    || d.lvls != 0
    || !c.refs.is_empty()
    || c.univs != vec![Univ::succ(Univ::zero())]
    || !scoped(&d.typ, 0, 0)
    || !scoped(&d.value, 0, count)
    || c
      .sharing
      .iter()
      .enumerate()
      .any(|(i, e)| !u64::try_from(i).is_ok_and(|prior| scoped(e, 3, prior)))
  {
    return Err("fixture scope/fixed-field validation failed".into());
  }
  let mut bytes = Vec::new();
  c.put(&mut bytes);
  let mut rest = bytes.as_slice();
  let decoded = Constant::get(&mut rest)?;
  if !rest.is_empty() || decoded != *c {
    return Err("constant roundtrip mismatch".into());
  }
  SharingDag::from_constant(c, &ExactSharingLimits::default())
    .map_err(|e| e.to_string())
}

fn preserve(path: &Path, bytes: &[u8]) -> Result<(), String> {
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

fn run(dir: &Path, depth: u64) -> Result<(), String> {
  let c = tower(depth);
  let dag = validate(&c)?;
  let (addr, bytes) = c.commit();
  std::fs::create_dir_all(dir).map_err(|e| e.to_string())?;
  preserve(&dir.join(format!("depth-{depth:04}.input.ixn")), &bytes)?;
  let env = Env::new();
  env.store_const(addr.clone(), c.clone());
  let mut envelope = Vec::new();
  env.put(&mut envelope)?;
  let mut rest = envelope.as_slice();
  let loaded = Env::get(&mut rest)?;
  if !rest.is_empty() || loaded.consts.len() != 1 {
    return Err("env roundtrip mismatch".into());
  }
  preserve(&dir.join(format!("depth-{depth:04}.input.ixe")), &envelope)?;
  println!(
    "INPUT\tdepth={depth}\tbody_unshared_bits={}\tbytes={}\tdag_nodes={}\taddress={}\tsha256={:x}\tixe_sha256={:x}",
    if depth == 0 { 1 } else { depth + 2 },
    bytes.len(),
    dag.len(),
    addr.hex(),
    Sha256::digest(&bytes),
    Sha256::digest(&envelope)
  );
  println!(
    "VALID\tcodec-roundtrip\tbackward-shares\tclosed-binders\trefs-empty\tunivs=[SuccZero]\ttyping=construction-only\tlimits=default\tK=12\texact-baseline=unknown"
  );
  std::io::stdout().flush().map_err(|e| e.to_string())?;
  let limits = ExactSharingLimits::default();
  let start = Instant::now();
  let mut widths = 0;
  let classified = experimental::classify(&c, &limits, &mut |event| {
    if matches!(event, experimental::Event::Width { .. }) {
      widths += 1;
    }
    Ok(())
  });
  println!(
    "CLASSIFY\tdepth={depth}\twidths={widths}\tms={}\tresult={classified:?}",
    start.elapsed().as_millis()
  );
  std::io::stdout().flush().map_err(|e| e.to_string())?;
  let start = Instant::now();
  match experimental::normalize(&c, &limits, 12, &mut |_| Ok(())) {
    Err(e) => println!(
      "NORMALIZE\tdepth={depth}\tms={}\terror={e:?}\tdisplay={e}",
      start.elapsed().as_millis()
    ),
    Ok((out, result)) => {
      let other =
        SharingDag::from_constant(&out, &limits).map_err(|e| e.to_string())?;
      let ConstantInfo::Defn(d) = &out.info else {
        return Err("output kind changed".into());
      };
      if other.nodes() != dag.nodes()
        || other.roots() != dag.roots()
        || out.refs != c.refs
        || out.univs != c.univs
        || d.kind != DefKind::Definition
        || d.safety != DefinitionSafety::Safe
        || d.lvls != 0
      {
        return Err("output DAG/fixed-field mismatch".into());
      }
      let mut encoded = Vec::new();
      out.put(&mut encoded);
      preserve(
        &dir.join(format!("depth-{depth:04}.K12.experimental.ixn")),
        &encoded,
      )?;
      println!(
        "NORMALIZE\tdepth={depth}\tms={}\tok\tbytes={}\tsha256={:x}\twidth={}\tmeters={:?}",
        start.elapsed().as_millis(),
        encoded.len(),
        Sha256::digest(&encoded),
        result.stats.w,
        result.stats.candidate_meters
      );
    },
  }
  Ok(()) // Numeric refusal is recorded data; validation/IO failures remain errors.
}

fn main() -> Result<(), String> {
  let args: Vec<String> = std::env::args().collect();
  if args.len() != 3 {
    return Err("usage: sharing_numeric EXPORT_DIR DEPTH".into());
  }
  let depth: u64 =
    args[2].parse().map_err(|e| format!("invalid depth: {e}"))?;
  if depth > 512 {
    return Err("diagnostic depth exceeds 512".into());
  }
  run(Path::new(&args[1]), depth)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn scoped_backward_towers_and_rejections() {
    for depth in [0, 1, 62, 63, 64, 125, 126, 127, 128, 130, 256] {
      assert!(validate(&tower(depth)).is_ok(), "depth {depth}");
    }
    let mut bad = tower(2);
    bad.sharing[0] = Arc::new(Expr::Share(0));
    assert!(validate(&bad).is_err());
    assert!(
      SharingDag::from_constant(&bad, &ExactSharingLimits::default()).is_err()
    );
    let mut bad = tower(2);
    bad.sharing[0] = Expr::var(3);
    assert!(validate(&bad).is_err());
    let mut bad = tower(2);
    bad.univs.clear();
    assert!(validate(&bad).is_err());
  }

  #[test]
  fn small_unshared_body_length_oracle() {
    let mut body = Expr::var(0);
    for depth in 0..=10 {
      let mut bytes = Vec::new();
      ixon::serialize::put_expr(&body, &mut bytes);
      assert_eq!(bytes.len(), 3 * (1usize << depth) - 2);
      body = Expr::app(Expr::app(Expr::var(1), body.clone()), body);
    }
  }
}
