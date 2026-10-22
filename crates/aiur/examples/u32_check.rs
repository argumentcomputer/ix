//! Exercise the actual Lean-exported opaque word library, including malicious
//! advice and mutated circuit rows. Run after `lake exe u32_tests PACKAGE.json`.
use aiur::{
  Program,
  bytecode::Type,
  execute::Execution,
  hints::HintChannels,
  maps::MapOverrides,
  trace::{
    TraceArtifact, TracePlan,
    stark::{Backend, Parameters},
  },
};
use serde::Deserialize;
use std::error::Error;

#[derive(Deserialize)]
struct Package {
  program: Program,
  trace: TraceArtifact,
}

fn bytes(word: u32) -> Vec<u64> {
  word.to_le_bytes().into_iter().map(u64::from).collect()
}

fn main() -> Result<(), Box<dyn Error>> {
  let path = std::env::args().nth(1).ok_or("usage: u32_check PACKAGE.json")?;
  let package: Package = serde_json::from_slice(&std::fs::read(path)?)?;
  let program = package.program.check()?;
  let mut channels = HintChannels::new();
  aiur::library::u32::register(&mut channels, program.field())?;
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(&program, &mut maps)?;
  let hints =
    program.prepare_hint_channels(&[], &channels)?.with_map_overrides(&maps)?;
  let table_hints = program.prepare_hint_channels(&[], &channels)?;
  let plan = TracePlan::new(&program, package.trace)?;
  let backend = Backend::new(&plan, Parameters::default())?;
  let mut checks = 0;
  let mut check = |name: &str,
                   args: Vec<u64>,
                   expected: Vec<u64>|
   -> Result<_, Box<dyn Error>> {
    let entry = format!("Words::{name}");
    let record = hints.execute(&entry, args.clone())?;
    assert_eq!(record.output, expected, "{entry}({args:?})");
    let fallback = table_hints.execute(&entry, args.clone())?;
    assert_eq!(record.output, fallback.output);
    assert_eq!(record.queries, fallback.queries);
    let trace = plan.generate(&record, &entry, &args, true)?;
    plan.check(&record, &trace, &entry, &args)?;
    assert_eq!(trace, plan.generate_reference(&record, &entry, &args, true)?);
    checks += 1;
    Ok(())
  };
  let mut values =
    vec![0, 1, 255, 256, 65535, 65536, 1 << 31, u32::MAX - 1, u32::MAX];
  let mut seed = 0x93c4_18bd_u32;
  for _ in 0..32 {
    seed = seed.wrapping_mul(1664525).wrapping_add(1013904223);
    values.push(seed);
  }
  for &a in &values {
    check("pack", bytes(a), vec![u64::from(a)])?;
    check("expand", vec![u64::from(a)], bytes(a))?;
    check("rotr8", bytes(a), vec![u64::from(a.rotate_right(8))])?;
    check("rotr16", bytes(a), vec![u64::from(a.rotate_right(16))])?;
    for b in [0, 1, u32::MAX, a.rotate_left(13)] {
      let args: Vec<_> = bytes(a).into_iter().chain(bytes(b)).collect();
      for (operation, result) in [
        ("add", a.wrapping_add(b)),
        ("sub", a.wrapping_sub(b)),
        ("lt", u32::from(a < b)),
        ("xor", a ^ b),
        ("and", a & b),
        ("or", a | b),
        ("xor_rotr7", (a ^ b).rotate_right(7)),
        ("xor_rotr12", (a ^ b).rotate_right(12)),
      ] {
        check(operation, args.clone(), vec![u64::from(result)])?;
      }
      check("compact_lt", vec![a.into(), b.into()], vec![u64::from(a < b)])?;
      check("raw_lt", vec![a.into(), b.into()], vec![u64::from(a < b)])?;
      let args = args.into_iter().chain(bytes(b)).collect();
      check("add3", args, vec![u64::from(a.wrapping_add(b).wrapping_add(b))])?;
    }
  }
  check("overflow", vec![], vec![0])?;
  check("overflow3", vec![], vec![u64::from(u32::MAX - 2)])?;
  check("conversion", vec![], vec![u64::from(u32::MAX)])?;

  // constrain_eq! intentionally permits candidate execution. Both population
  // paths must retain the equality, and a proof of a wrong result must not verify.
  let reject = |record: &Execution,
                entry: &str,
                args: &[u64],
                prove: bool|
   -> Result<(), Box<dyn Error>> {
    let trace = plan.generate(record, entry, args, true)?;
    assert!(
      plan.check(record, &trace, entry, args).is_err(),
      "{entry}({args:?}), output {:?}",
      record.output
    );
    assert_eq!(trace, plan.generate_reference(record, entry, args, true)?);
    if prove {
      let witness = backend.generate(record, entry, args)?;
      let reference = backend.witness(record, &trace)?;
      for (a, b) in witness.traces.iter().zip(&reference.traces) {
        assert_eq!(a.width, b.width);
        assert_eq!(a.values, b.values);
      }
      let proof = backend.prove(entry, args, &record.output, witness)?;
      assert!(backend.verify(entry, args, &record.output, &proof).is_err());
    }
    Ok(())
  };
  for (entry, args) in [
    ("byte", vec![256]),
    ("pack", vec![256, 0, 0, 0]),
    ("expand", vec![1 << 32]),
    ("compact_lt", vec![0, 1 << 32]),
    ("compact_lt", vec![program.field().modulus() - 1, 0]),
    ("raw_lt", vec![0, 1 << 32]),
    ("raw_lt", vec![program.field().modulus() - 1, 0]),
  ] {
    let range_error = entry == "byte" || entry == "pack";
    let entry = format!("Words::{entry}");
    let candidate = hints.execute(&entry, args.clone());
    if range_error {
      assert!(candidate.is_err());
    } else {
      reject(&candidate?, &entry, &args, false)?;
    }
  }
  let byte_type = Type::Tuple { items: vec![Type::Field; 4] };
  for (entry, channel, arity, wrong) in [
    ("overflow", "u32.add", 2, [1, 0, 0, 0]),
    ("overflow", "u32.add", 2, [256, 0, 0, 0]),
    ("overflow", "u32.add", 2, [255, 255, 255, 255]),
    ("overflow3", "u32.add3", 3, [254, 255, 255, 255]),
    ("overflow3", "u32.add3", 3, [252, 255, 255, 255]),
  ] {
    let mut bad = HintChannels::new();
    bad.insert(
      channel,
      Type::Tuple { items: vec![byte_type.clone(); arity] },
      byte_type.clone(),
      move |input, output| {
        let expected = if arity == 2 {
          [bytes(u32::MAX), bytes(1)].concat()
        } else {
          bytes(u32::MAX).repeat(3)
        };
        assert_eq!(input, expected, "addition hints take byte operands");
        output.copy_from_slice(&wrong);
        Ok(())
      },
    )?;
    let entry = format!("Words::{entry}");
    let prepared = program.prepare_hint_channels(&[], &bad)?;
    if wrong[0] == 256 {
      assert!(prepared.execute(&entry, vec![]).is_err());
    } else {
      let record = prepared.execute(&entry, vec![])?;
      reject(&record, &entry, &[], true)?;
    }
  }
  let mut bad = HintChannels::new();
  bad.insert(
    "u32.sub",
    Type::Tuple { items: vec![Type::Field; 2] },
    byte_type.clone(),
    |_, output| {
      output.fill(0);
      Ok(())
    },
  )?;
  let args = [bytes(0), bytes(1)].concat();
  let record = program
    .prepare_hint_channels(&[], &bad)?
    .execute("Words::lt", args.clone())?;
  reject(&record, "Words::lt", &args, true)?;
  for wrong in [
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [256, 0, 0, 0, 255, 255, 255, 255, 1, 0, 0, 0],
    [0, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0],
    [0, 0, 0, 0, 254, 255, 255, 255, 1, 0, 0, 0],
  ] {
    let mut bad = HintChannels::new();
    bad.insert(
      "u32.lt",
      Type::Tuple { items: vec![Type::Field; 2] },
      Type::Tuple { items: vec![byte_type.clone(); 3] },
      move |_, out| {
        out.copy_from_slice(&wrong);
        Ok(())
      },
    )?;
    let prepared = program.prepare_hint_channels(&[], &bad)?;
    if wrong[0] == 256 {
      assert!(prepared.execute("Words::raw_lt", vec![0, 1]).is_err());
    } else {
      let record = prepared.execute("Words::raw_lt", vec![0, 1])?;
      if wrong[8] == 0 {
        // The borrow/result is correct. Value propagation reconstructs
        // the right operand's bytes from b=1, so the row checker accepts
        // the repair. Static-table counts still describe the original
        // advice: only the full STARK lookup balance rejects this witness.
        assert_eq!(record.output, [1]);
        let trace = plan.generate(&record, "Words::raw_lt", &[0, 1], true)?;
        plan.check(&record, &trace, "Words::raw_lt", &[0, 1])?;
        assert_eq!(
          trace,
          plan.generate_reference(&record, "Words::raw_lt", &[0, 1], true)?
        );
        let witness = backend.generate(&record, "Words::raw_lt", &[0, 1])?;
        let proof = backend.prove("Words::raw_lt", &[0, 1], &[1], witness)?;
        let error =
          backend.verify("Words::raw_lt", &[0, 1], &[1], &proof).unwrap_err();
        println!(
          "Recomposed advice passed row checks; verifier rejected: {error}"
        );
      } else {
        reject(&record, "Words::raw_lt", &[0, 1], true)?;
      }
    }
  }

  // Mutate populated rows independently of the interpreter and host providers.
  let entry = "Words::overflow3";
  let record = hints.execute(entry, vec![])?;
  let trace = plan.generate(&record, entry, &[], true)?;
  let matrix = trace
    .matrices
    .iter()
    .position(|m| m.unpadded_height > 0)
    .ok_or("no active row")?;
  let mut mutations = 0;
  for column in 0..trace.matrices[matrix].width {
    let mut bad = trace.clone();
    let value = &mut bad.matrices[matrix].values[column];
    *value = program.field().add(*value, 1);
    assert!(
      plan.check(&record, &bad, entry, &[]).is_err(),
      "unconstrained column {column}"
    );
    mutations += 1;
  }
  let witness = backend.generate(&record, entry, &[])?;
  let reference = backend.witness(&record, &trace)?;
  for (a, b) in witness.traces.iter().zip(&reference.traces) {
    assert_eq!(a.width, b.width);
    assert_eq!(a.values, b.values);
  }
  let proof = backend.prove(entry, &[], &record.output, witness)?;
  backend.verify(entry, &[], &record.output, &proof)?;
  assert!(
    aiur::library::u32::register(
      &mut HintChannels::new(),
      aiur::field::PrimeField::new(65537).unwrap()
    )
    .is_err()
  );
  println!(
    "Passed {checks} execution/reference-trace cases, invalid inputs/advice, 8 rejected proofs from dishonest advice, {mutations} row mutations, and a verified proof."
  );
  Ok(())
}
