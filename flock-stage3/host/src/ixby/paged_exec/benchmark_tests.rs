//! Opt-in throughput measurement over original program/input bytes. Each
//! measured proof is a conditional execution segment, not a complete run.
use super::*;
use crate::ixby::ixbf::DecodeLimits;
use std::{
  io::Write,
  path::Path,
  sync::atomic::{AtomicUsize, Ordering},
  time::Instant,
};

fn option(
  name: &str,
  default: usize,
  range: std::ops::RangeInclusive<usize>,
) -> usize {
  let value = std::env::var(name)
    .map_or(default, |s| s.parse().expect("unsigned benchmark option"));
  assert!(range.contains(&value), "{name} outside benchmark bounds");
  value
}

fn write_new(path: &Path, bytes: &[u8]) {
  let mut file = std::fs::OpenOptions::new()
    .write(true)
    .create_new(true)
    .open(path)
    .unwrap();
  file.write_all(bytes).unwrap();
  file.sync_all().unwrap();
}

#[test]
#[ignore = "original artifacts; bounded actual-proof throughput measurement with shared setup"]
fn original_execution_proof_throughput() {
  let program =
    std::fs::read(std::env::var_os("IXBY_PAGED_PROGRAM").unwrap()).unwrap();
  let input =
    std::fs::read(std::env::var_os("IXBY_PAGED_INPUT").unwrap()).unwrap();
  let count = option("IXBY_PROOF_BATCHES", 32, 1..=256);
  let skip = option("IXBY_PROOF_SKIP", 0, 0..=100_000);
  let workers = option("IXBY_PROOF_WORKERS", 1, 1..=16).min(count);
  let threads = option("IXBY_PROOF_THREADS", 4, 1..=64);
  assert!(workers * threads <= 64, "benchmark CPU thread bound");
  let class = match std::env::var("IXBY_PAGED_NATIVE_CLASS").as_deref() {
    Ok("shared") | Err(_) => BatchClass::Shared,
    Ok("shared-compact") => BatchClass::SharedCompact,
    Ok("shared-compact-boolean") => BatchClass::SharedCompactBoolean,
    Ok("shared-boolean") => BatchClass::SharedBoolean,
    Ok("shared-1024") => BatchClass::Shared1024,
    Ok("shared-compact-packed") => BatchClass::SharedCompactPacked,
    Ok("shared-packed-1024") => BatchClass::SharedPacked1024,
    _ => panic!("IXBY_PAGED_NATIVE_CLASS must be shared or shared-compact"),
  };
  let out = std::env::var_os("IXBY_PROOF_OUT").map(std::path::PathBuf::from);
  if let Some(out) = &out {
    std::fs::create_dir(out).unwrap();
    write_new(
      &out.join("config.txt"),
      format!(
        "claim=conditional execution segments\nclass={class:?}\nprogram_blake3={}\ninput_blake3={}\nskip={skip}\nbatches={count}\nworkers={workers}\nthreads_per_worker={threads}\n",
        blake3::hash(&program), blake3::hash(&input)
      ).as_bytes(),
    );
  }
  let loading = Instant::now();
  let mut image =
    NativeImage::load(&program, &input, DecodeLimits::default()).unwrap();
  let mut machine = image.machine().unwrap();
  machine.compare_native_advice = false;
  let load_seconds = loading.elapsed().as_secs_f64();
  let skipping = Instant::now();
  for _ in 0..skip {
    machine.batch(class, &mut image.memory).unwrap().expect("skip before halt");
  }
  let skip_seconds = skipping.elapsed().as_secs_f64();
  let generating = Instant::now();
  let advice: Vec<_> = (0..count)
    .map(|_| {
      machine
        .batch(class, &mut image.memory)
        .unwrap()
        .expect("sample before halt")
    })
    .collect();
  let native_seconds = generating.elapsed().as_secs_f64();
  for (batch, advice) in advice.iter().enumerate() {
    let mut at = 55;
    let mut counts = [0; 24];
    for (chip, quota) in Chip::ALL.into_iter().zip(class.quotas()) {
      for _ in 0..quota {
        counts[chip as usize] += usize::from(advice.private[at] == F128::ONE);
        at += 2 + STATE_WORDS + chip.advice_words();
      }
    }
    eprintln!("proof_quota,{},{counts:?}", skip + batch);
  }
  let statements: Vec<_> = advice
    .iter()
    .map(|a| ExecutionStatement::from_words(&a.expected).unwrap())
    .collect();
  for pair in statements.windows(2) {
    assert_eq!(pair[0].parameters(), pair[1].parameters());
    assert_eq!(pair[0].final_state(), pair[1].initial());
  }
  let first = statements.first().unwrap().initial();
  let last = statements.last().unwrap().final_state();
  let microsteps = last[0].lo - first[0].lo;
  let logical_steps = last[1 + FUEL].hi - first[1 + FUEL].hi;
  let compiling = Instant::now();
  let setup = CompiledPagedExecution::compile(class).unwrap();
  let setup_seconds = compiling.elapsed().as_secs_f64();
  let next = AtomicUsize::new(0);
  eprintln!(
    "proof benchmark: class={class:?} skip={skip} batches={count} workers={workers} threads={threads} load_seconds={load_seconds:.9} skip_seconds={skip_seconds:.9} native_seconds={native_seconds:.9} setup_seconds={setup_seconds:.9}"
  );
  eprintln!(
    "proof_sample,batch,worker,microsteps,logical_steps,witness_seconds,prove_seconds,verify_seconds,bytes"
  );
  let proving = Instant::now();
  std::thread::scope(|scope| {
    for worker in 0..workers {
      let (setup, next, advice, statements, out) =
        (&setup, &next, &advice, &statements, &out);
      scope.spawn(move || {
        let pool = rayon::ThreadPoolBuilder::new().num_threads(threads).build().unwrap();
        pool.install(|| loop {
          let i = next.fetch_add(1, Ordering::Relaxed);
          let Some(advice) = advice.get(i) else { break };
          let expected = &statements[i];
          let started = Instant::now();
          let witness = setup.witness(advice).unwrap();
          let witness_seconds = started.elapsed().as_secs_f64();
          let started = Instant::now();
          let proof = setup.prove_rows(
            &witness,
            setup.drivers.iter().map(|d| d.prover(&witness)).collect(),
          ).unwrap();
          let prove_seconds = started.elapsed().as_secs_f64();
          drop(witness);
          let started = Instant::now();
          setup.verify(expected, &proof).unwrap();
          let verify_seconds = started.elapsed().as_secs_f64();
          if let Some(out) = out {
            let stem = format!("{:010}", skip + i);
            let words: Vec<_> = expected.words().iter().flat_map(|w|
              w.lo.to_le_bytes().into_iter().chain(w.hi.to_le_bytes())
            ).collect();
            write_new(&out.join(format!("{stem}.statement")), &words);
            write_new(&out.join(format!("{stem}.flock")), &proof);
          }
          eprintln!("proof_sample,{},{worker},{},{},{witness_seconds:.9},{prove_seconds:.9},{verify_seconds:.9},{}",
            skip + i,
            expected.final_state()[0].lo - expected.initial()[0].lo,
            expected.final_state()[1 + FUEL].hi - expected.initial()[1 + FUEL].hi,
            proof.len());
        });
      });
    }
  });
  let elapsed = proving.elapsed().as_secs_f64();
  eprintln!(
    "proof benchmark complete: batches={count} microsteps={microsteps} logical_steps={logical_steps} worker_wall_seconds={elapsed:.9} batches_per_second={:.9} logical_steps_per_second={:.9}; every segment proof verified; source admission, complete execution and aggregation are outside this benchmark",
    count as f64 / elapsed,
    logical_steps as f64 / elapsed
  );
}
