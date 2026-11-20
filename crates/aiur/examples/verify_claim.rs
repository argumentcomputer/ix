//! Verify a proof of `entry(args) = output` against the key recompiled from a
//! package's program. The arguments and the output are supplied by the
//! verifier, as signed integers (one per line or whitespace-separated); the
//! package's execution data (arguments, hints) is not read.
//!
//! `verify_claim PACKAGE.ixa PROOF ARGS.txt OUTPUT.txt`
//!
//! `verify_claim --batch PACKAGE.ixa MANIFEST [THREADS]` compiles the key once
//! and verifies every claim of `MANIFEST`, one `PROOF ARGS.txt OUTPUT.txt`
//! triple of paths per line, on `THREADS` threads (default: all cores). It
//! prints `key ready` once the key is built, before any proof is read, then
//! `ok LINE` or `fail LINE: REASON` for each manifest line, in
//! manifest order, and exits 0 only if every line verified. A proof whose
//! check panics is reported as `fail` for that line; the other lines are
//! still checked.
//!
//! Words are signed decimal integers in canonical form (`0`, or an optional
//! `-` and no leading zeros) with absolute value below the field's
//! characteristic, so each field element has exactly one accepted spelling
//! of each sign.
use aiur::field::FieldBackend;
use aiur::{
  artifact::ExecutionPackage,
  trace::{
    TracePlan,
    stark::{Backend, Parameters, Proof},
  },
};
use std::{
  error::Error,
  fs,
  panic::{AssertUnwindSafe, catch_unwind},
  sync::atomic::{AtomicUsize, Ordering},
  time::Instant,
};

const P: i128 = 18446744069414584321;

fn word(w: &str) -> Result<u64, Box<dyn Error>> {
  let digits = w.strip_prefix('-').unwrap_or(w);
  let canonical = !digits.is_empty()
    && digits.bytes().all(|b| b.is_ascii_digit())
    && (digits == "0" || !digits.starts_with('0'))
    && !(w.starts_with('-') && digits == "0");
  if !canonical {
    return Err(format!("not a canonical signed integer: {w:?}").into());
  }
  let v: i128 = w.parse()?;
  if v <= -P || v >= P {
    return Err(format!("integer {w} is outside (-p, p)").into());
  }
  Ok(v.rem_euclid(P) as u64)
}

fn words(path: &str) -> Result<Vec<u64>, Box<dyn Error>> {
  fs::read_to_string(path)?.split_whitespace().map(word).collect()
}

fn single(
  package: &str,
  proof: &str,
  args_path: &str,
  output_path: &str,
) -> Result<(), Box<dyn Error>> {
  let start = Instant::now();
  let (package, digest) = ExecutionPackage::load(package.as_ref())?;
  let (program, trace) = package.package.traced()?;
  let mut program = program.check_field::<multi_stark::types::Val>()?;
  program.track_depth(&trace)?;
  let plan = TracePlan::new(&program, trace)?;
  let entry =
    &program.program().entries.first().ok_or("no selected entrypoint")?.name;
  let backend = Backend::new(&plan, Parameters::default())?;
  let setup = start.elapsed().as_secs_f64();
  let call = program.field().decode(&words(args_path)?)?;
  let output = program.field().decode(&words(output_path)?)?;
  let bytes = fs::read(proof)?;
  let start = Instant::now();
  let proof = Proof::from_bytes(&bytes)?;
  backend.verify(entry, &call, &output, &proof)?;
  println!(
    "verified {entry}: package {digest}, proof blake3 {} ({} bytes), {} argument words, {} output words; key setup {setup:.2} s, verify {:.2} s",
    blake3::hash(&bytes).to_hex(),
    bytes.len(),
    call.len(),
    output.len(),
    start.elapsed().as_secs_f64()
  );
  Ok(())
}

fn batch(
  package: &str,
  manifest: &str,
  threads: Option<&String>,
) -> Result<bool, Box<dyn Error>> {
  let start = Instant::now();
  let jobs: Vec<Vec<String>> = fs::read_to_string(manifest)?
    .lines()
    .filter(|l| !l.trim().is_empty())
    .map(|l| l.split_whitespace().map(str::to_owned).collect())
    .collect();
  let (package, digest) = ExecutionPackage::load(package.as_ref())?;
  let (program, trace) = package.package.traced()?;
  let mut program = program.check_field::<multi_stark::types::Val>()?;
  program.track_depth(&trace)?;
  let plan = TracePlan::new(&program, trace)?;
  let entry =
    &program.program().entries.first().ok_or("no selected entrypoint")?.name;
  let backend = Backend::new(&plan, Parameters::default())?;
  let setup = start.elapsed().as_secs_f64();
  println!("key ready: {entry}, package {digest}, {} claims", jobs.len());
  let width = match threads {
    Some(t) => t.parse::<usize>()?.max(1),
    None => std::thread::available_parallelism().map_or(1, |n| n.get()),
  };
  let check = |job: &[String]| -> Result<(), String> {
    let [proof, args_path, output_path] = job else {
      return Err("a manifest line is not PROOF ARGS OUTPUT".into());
    };
    let call = program
      .field()
      .decode(&words(args_path).map_err(|e| e.to_string())?)
      .map_err(|e| e.to_string())?;
    let output = program
      .field()
      .decode(&words(output_path).map_err(|e| e.to_string())?)
      .map_err(|e| e.to_string())?;
    let bytes = fs::read(proof).map_err(|e| format!("{proof}: {e}"))?;
    let proof = Proof::from_bytes(&bytes).map_err(|e| e.to_string())?;
    backend.verify(entry, &call, &output, &proof)
  };
  let next = AtomicUsize::new(0);
  let verify_start = Instant::now();
  let mut results: Vec<(usize, Result<(), String>)> = std::thread::scope(|s| {
    let workers: Vec<_> = (0..width.min(jobs.len().max(1)))
      .map(|_| {
        s.spawn(|| {
          let mut out = Vec::new();
          loop {
            let i = next.fetch_add(1, Ordering::Relaxed);
            let Some(job) = jobs.get(i) else { break };
            let r = catch_unwind(AssertUnwindSafe(|| check(job)))
              .unwrap_or_else(|_| Err("the check panicked".into()));
            out.push((i, r));
          }
          out
        })
      })
      .collect();
    workers.into_iter().flat_map(|w| w.join().unwrap_or_default()).collect()
  });
  results.sort_by_key(|(i, _)| *i);
  let mut all = results.len() == jobs.len();
  for (i, r) in &results {
    match r {
      Ok(()) => println!("ok {}", i + 1),
      Err(e) => {
        all = false;
        println!("fail {}: {}", i + 1, e.replace('\n', " "))
      },
    }
  }
  println!(
    "batch {entry}: package {digest}, {} of {} claims verified; key setup {setup:.2} s, verify {:.2} s on {width} threads",
    results.iter().filter(|(_, r)| r.is_ok()).count(),
    jobs.len(),
    verify_start.elapsed().as_secs_f64()
  );
  Ok(all)
}

fn main() -> Result<(), Box<dyn Error>> {
  let args: Vec<_> = std::env::args().collect();
  match args.as_slice() {
    [_, flag, package, manifest, rest @ ..]
      if flag == "--batch" && rest.len() <= 1 =>
    {
      if !batch(package, manifest, rest.first())? {
        std::process::exit(1);
      }
      Ok(())
    },
    [_, package, proof, args_path, output_path] => {
      single(package, proof, args_path, output_path)
    },
    _ => Err(
      "usage: verify_claim PACKAGE.ixa PROOF ARGS.txt OUTPUT.txt | verify_claim --batch PACKAGE.ixa MANIFEST [THREADS]"
        .into(),
    ),
  }
}
