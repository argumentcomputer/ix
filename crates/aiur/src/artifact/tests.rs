use super::*;

const P: u64 = 0xffff_ffff_0000_0001;

fn add(a: Polynomial, b: Polynomial) -> Polynomial {
  Polynomial::Add(Box::new([a, b]))
}
fn sub(a: Polynomial, b: Polynomial) -> Polynomial {
  Polynomial::Sub(Box::new([a, b]))
}
fn mul(a: Polynomial, b: Polynomial) -> Polynomial {
  Polynomial::Mul(Box::new([a, b]))
}
fn var(i: usize) -> Polynomial {
  Polynomial::Var(i)
}
fn constant(v: u64) -> Polynomial {
  Polynomial::Const(v)
}

fn sample_program() -> Program {
  let pair = Type::Tuple { items: vec![Type::Field, Type::Field] };
  let ptr = Type::Ptr { target: Box::new(pair.clone()) };
  let named = Type::Enum { name: "Option".into() };
  use Instruction as I;
  let code = vec![
    I::Literal { dest: 0, value: P - 1 },
    I::Copy { dest: vec![1, 2], source: vec![0, 0] },
    I::Neg { dest: 3, source: 1 },
    I::Binary { dest: 4, operator: Binary::Add, left: 0, right: 1 },
    I::Binary { dest: 4, operator: Binary::Sub, left: 0, right: 1 },
    I::Binary { dest: 4, operator: Binary::Mul, left: 0, right: 1 },
    I::Binary { dest: 4, operator: Binary::Div, left: 0, right: 1 },
    I::Guard { tests: vec![(0, 7), (1, P - 2)], message: "guard ü".into() },
    I::Branch { tests: vec![(2, 3)], otherwise: 12 },
    I::Branch { tests: vec![], otherwise: 0 },
    I::Jump { target: 13 },
    I::Call { function: 0, args: vec![0], dest: vec![5] },
    I::Store { r#type: pair.clone(), value: vec![0, 1], dest: 6 },
    I::Load { r#type: ptr.clone(), pointer: 6, dest: vec![7] },
    I::Hint {
      channel: "u32".into(),
      r#type: named.clone(),
      key_type: pair.clone(),
      key: vec![0, 1],
      dest: vec![8, 9],
    },
    I::AssertEq {
      left: vec![0],
      right: vec![1],
      message: Some("unequal".into()),
      runtime_check: true,
    },
    I::AssertEq {
      left: vec![],
      right: vec![],
      message: None,
      runtime_check: false,
    },
    I::Ret { value: vec![5] },
    I::Fail { message: String::new() },
  ];
  Program {
    version: 2,
    modulus: P,
    functions: vec![
      Function {
        name: "main".into(),
        params: vec![Type::Field, ptr.clone()],
        result: pair.clone(),
        registers: 10,
        code,
      },
      Function {
        name: "empty".into(),
        params: vec![],
        result: Type::Tuple { items: vec![] },
        registers: 0,
        code: vec![],
      },
    ],
    enums: vec![Enum {
      name: "Option".into(),
      constructors: vec![
        Constructor { name: "none".into(), fields: vec![] },
        Constructor { name: "some".into(), fields: vec![named, ptr] },
      ],
    }],
    tables: vec![Table {
      name: "t".into(),
      r#type: pair.clone(),
      rows: vec![vec![0, P - 1], vec![], vec![3]],
    }],
    maps: vec![Map {
      name: "m".into(),
      params: vec![Type::Field],
      result: pair,
      input: 0,
      output: 1,
    }],
    entries: vec![
      Entry {
        name: "main".into(),
        function: 0,
        inputs: vec![
          IoType::Field,
          IoType::Tuple { items: vec![IoType::Field] },
          IoType::Array { element: Box::new(IoType::Field), length: 4 },
          IoType::Struct {
            name: "S".into(),
            fields: vec![("x".into(), IoType::Field)],
          },
          IoType::Enum {
            name: "E".into(),
            constructors: vec![
              ("a".into(), vec![]),
              ("b".into(), vec![IoType::Field, IoType::Field]),
            ],
          },
        ],
        output: Some(IoType::Field),
      },
      Entry { name: "other".into(), function: 1, inputs: vec![], output: None },
    ],
  }
}

fn nested() -> Polynomial {
  sub(mul(add(var(0), constant(P - 1)), var(2)), add(constant(0), var(1)))
}

fn sample_trace() -> TraceArtifact {
  let pair = Type::Tuple { items: vec![Type::Field, Type::Field] };
  let steps = vec![
    Action::Assign { dest: vec![0, 1], values: vec![var(0), nested()] },
    Action::Inverse { dest: 2, value: nested() },
    Action::Choose {
      dest: vec![3],
      tests: vec![vec![var(0), var(1)], vec![], vec![constant(1)]],
    },
    Action::Failure { dest: vec![4], differences: vec![sub(var(0), var(1))] },
    Action::Call { name: "f".into(), args: vec![var(0)], dest: vec![5] },
    Action::Store { r#type: pair.clone(), values: vec![var(0)], dest: 6 },
    Action::Load { r#type: Type::Field, address: var(6), dest: vec![7] },
    Action::Hint {
      channel: "c".into(),
      instruction: 14,
      r#type: pair.clone(),
      key_type: Type::Enum { name: "E".into() },
      key: vec![var(0), nested()],
      dest: vec![8],
    },
  ]
  .into_iter()
  .enumerate()
  .map(|(i, action)| PopulationStep { guard: var(i), action })
  .collect();
  TraceArtifact {
    version: 2,
    modulus: P,
    functions: vec![FunctionPlan {
      name: "main".into(),
      chip: "main".into(),
      witnesses: 9,
      inputs: vec![0],
      output: vec![5],
      steps,
      writes: vec![ColumnWrite { column: 0, source: 1, guard: nested() }],
    }],
    chips: vec![Chip {
      name: "main".into(),
      width: 4,
      activation: 3,
      inputs: vec![0, 1],
      output: vec![var(1)],
      constraints: vec![nested(), constant(0)],
      sends: vec![Send {
        channel: "f".into(),
        args: vec![var(0)],
        result: vec![1],
        enable: var(3),
      }],
      memory: vec![MemoryLookup {
        r#type: pair,
        address: var(2),
        values: vec![var(0), var(1)],
        enable: constant(1),
      }],
    }],
    groups: vec![FunctionGroup {
      name: "g".into(),
      width: 5,
      activation: add(var(0), var(1)),
      constraints: vec![nested()],
      receive: vec![var(0), var(1)],
      sends: vec![GroupLookup { enable: var(4), args: vec![nested()] }],
      members: vec![GroupMember {
        name: "main".into(),
        columns: vec![0, 1, 2],
        selector: 3,
        writes: vec![GroupWrite { column: 4, value: nested() }],
      }],
    }],
  }
}

fn sample() -> Package {
  Package {
    program: sample_program(),
    trace: sample_trace(),
    metadata: Metadata {
      name: "sample".into(),
      compiler: "aiur test".into(),
      source: [7; 32],
      key: "k".into(),
    },
  }
}

/// Recomputes the trailing digest so that a test reaches the section parser.
fn sign(mut bytes: Vec<u8>) -> Vec<u8> {
  let body = bytes.len() - DIGEST_LEN;
  let digest = blake3::hash(&bytes[..body]);
  bytes[body..].copy_from_slice(digest.as_bytes());
  bytes
}

fn assemble(modulus: u64, sections: &[(u32, Vec<u8>)]) -> Vec<u8> {
  let mut w = Writer::new();
  w.raw(&MAGIC);
  w.u32(VERSION);
  w.u32(0);
  w.u64(modulus);
  for (tag, payload) in sections {
    w.u32(*tag);
    w.bytes(payload);
  }
  w.raw(&[0; DIGEST_LEN]);
  sign(w.into_bytes())
}

fn payloads(package: &Package) -> Vec<(u32, Vec<u8>)> {
  vec![
    (SECTION_METADATA, metadata_bytes(&package.metadata)),
    (SECTION_BYTECODE, program_bytes(&package.program).unwrap()),
    (SECTION_TRACE, trace_payload(&package.trace).unwrap()),
    (SECTION_GROUPS, groups_payload(&package.trace).unwrap()),
  ]
}

#[test]
fn round_trip() {
  let package = sample();
  let bytes = encode(&package).unwrap();
  assert_eq!(decode(&bytes).unwrap(), package);
  assert_eq!(encode(&decode(&bytes).unwrap()).unwrap(), bytes);
  assert_eq!(assemble(P, &payloads(&package)), bytes);
  let lengths = sections(&bytes).unwrap();
  assert_eq!(lengths.len(), 4);
  assert_eq!(
    lengths[1],
    (SECTION_BYTECODE, program_bytes(&package.program).unwrap().len() as u64)
  );
}

#[test]
fn json_round_trip() {
  let package = sample();
  let json = to_json(&package.program, &package.trace).unwrap();
  let (program, trace) = from_json(&json).unwrap();
  assert_eq!(program, package.program);
  assert_eq!(trace, package.trace);
  let binary = decode(&encode(&package).unwrap()).unwrap();
  assert_eq!((binary.program, binary.trace), (program, trace));
}

#[test]
fn exported_fixture_round_trips() {
  let bytes = std::fs::read(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/grouping.json"
  ))
  .unwrap();
  let (program, trace) = from_json(&bytes).unwrap();
  assert!(!trace.groups.is_empty());
  let package = Package { program, trace, metadata: Metadata::default() };
  let decoded = decode(&encode(&package).unwrap()).unwrap();
  assert_eq!(decoded, package);
  let json = to_json(&package.program, &package.trace).unwrap();
  let (program, trace) = from_json(&json).unwrap();
  assert_eq!((program, trace), (decoded.program, decoded.trace));
}

#[test]
fn content_digest_ignores_metadata() {
  let mut package = sample();
  let digest = content_digest(&package.program, &package.trace).unwrap();
  package.metadata.name = "renamed".into();
  assert_eq!(content_digest(&package.program, &package.trace).unwrap(), digest);
  package.trace.groups.clear();
  assert_ne!(content_digest(&package.program, &package.trace).unwrap(), digest);
  let mut hasher = blake3::Hasher::new();
  let p = program_bytes(&sample_program()).unwrap();
  let t = trace_bytes(&sample_trace()).unwrap();
  hasher.update(b"aiur-image-content/1\0");
  hasher.update(&(p.len() as u64).to_le_bytes());
  hasher.update(&p);
  hasher.update(&(t.len() as u64).to_le_bytes());
  hasher.update(&t);
  assert_eq!(*hasher.finalize().as_bytes(), digest);
}

#[test]
fn rejects_malformed_headers() {
  let bytes = encode(&sample()).unwrap();
  let mut bad = bytes.clone();
  bad[0] = b'X';
  assert!(decode(&sign(bad)).unwrap_err().contains("magic"));
  let mut bad = bytes.clone();
  bad[8..12].copy_from_slice(&2u32.to_le_bytes());
  assert!(decode(&sign(bad)).unwrap_err().contains("version"));
  let mut bad = bytes.clone();
  bad[12] = 1;
  assert!(decode(&sign(bad)).unwrap_err().contains("flags"));
  let mut bad = bytes.clone();
  bad[16..24].copy_from_slice(&(P - 2).to_le_bytes());
  assert!(decode(&sign(bad)).unwrap_err().contains("modulus"));
  assert!(decode(&[]).is_err());
}

#[test]
fn rejects_every_truncation() {
  let bytes = encode(&sample()).unwrap();
  for len in 0..bytes.len() {
    assert!(decode(&bytes[..len]).is_err(), "prefix {len}");
    assert!(decode(&sign_if_possible(&bytes[..len])).is_err(), "prefix {len}");
  }
}

fn sign_if_possible(bytes: &[u8]) -> Vec<u8> {
  if bytes.len() >= HEADER_LEN + DIGEST_LEN {
    sign(bytes.to_vec())
  } else {
    bytes.to_vec()
  }
}

#[test]
fn rejects_flipped_and_trailing_bytes() {
  let bytes = encode(&sample()).unwrap();
  for i in 0..bytes.len() {
    let mut bad = bytes.clone();
    bad[i] ^= 0x10;
    assert!(decode(&bad).is_err(), "byte {i}");
  }
  let mut bad = bytes.clone();
  bad.push(0);
  assert!(decode(&bad).is_err());
  let mut bad = bytes.clone();
  bad.insert(bytes.len() - DIGEST_LEN, 0);
  assert!(decode(&sign(bad)).unwrap_err().contains("trailing"));
}

#[test]
fn rejects_section_framing_errors() {
  let package = sample();
  let mut sections = payloads(&package);
  sections.swap(2, 3);
  assert!(decode(&assemble(P, &sections)).unwrap_err().contains("tag"));
  let mut sections = payloads(&package);
  sections.pop();
  assert!(decode(&assemble(P, &sections)).is_err());
  let mut sections = payloads(&package);
  sections.push((5, vec![]));
  assert!(decode(&assemble(P, &sections)).is_err());
  let mut sections = payloads(&package);
  sections[0].1.push(0);
  assert!(decode(&assemble(P, &sections)).unwrap_err().contains("trailing"));
}

#[test]
fn rejects_noncanonical_field_elements() {
  let mut package = sample();
  if let Instruction::Literal { value, .. } =
    &mut package.program.functions[0].code[0]
  {
    *value = P;
  }
  assert!(encode(&package).is_err());
  let mut sections = payloads(&sample());
  let mut w = Writer::new();
  write_program(&mut w, &package.program).unwrap();
  sections[1].1 = w.into_bytes();
  let error = decode(&assemble(P, &sections)).unwrap_err();
  assert!(error.contains("noncanonical"), "{error}");

  let mut trace = sample_trace();
  trace.chips[0].constraints.push(add(var(0), constant(u64::MAX)));
  assert!(trace_bytes(&trace).is_err());
  let mut sections = payloads(&sample());
  let mut w = Writer::new();
  write_trace(&mut w, &trace).unwrap();
  sections[2].1 = w.into_bytes();
  let error = decode(&assemble(P, &sections)).unwrap_err();
  assert!(error.contains("noncanonical"), "{error}");
}

#[test]
fn rejects_mismatched_moduli() {
  let mut package = sample();
  package.trace.modulus = 7;
  assert!(encode(&package).is_err());
  let mut sections = payloads(&sample());
  let mut w = Writer::with_modulus(P);
  let mut trace = sample_trace();
  trace.modulus = P - 2;
  write_trace(&mut w, &trace).unwrap();
  sections[2].1 = w.into_bytes();
  assert!(decode(&assemble(P, &sections)).unwrap_err().contains("modulus"));
}

fn nodes(raw: &[(u8, &[u64])]) -> Vec<u8> {
  let mut w = Writer::new();
  w.count(raw.len());
  for (tag, operands) in raw {
    w.u8(*tag);
    for &x in *operands {
      w.u64(x);
    }
  }
  w.into_bytes()
}

fn parse_polynomial(bytes: &[u8]) -> Result<Polynomial, String> {
  let mut r = Reader::with_modulus(bytes, P);
  let p = read_polynomial(&mut r)?;
  r.finish()?;
  Ok(p)
}

#[test]
fn polynomial_node_references() {
  let ok = nodes(&[(1, &[0]), (0, &[5]), (4, &[0, 1])]);
  assert_eq!(parse_polynomial(&ok).unwrap(), mul(var(0), constant(5)));
  let mut w = Writer::new();
  write_polynomial(&mut w, &mul(var(0), constant(5))).unwrap();
  assert_eq!(w.into_bytes(), ok);

  let forward = nodes(&[(1, &[0]), (2, &[0, 2]), (1, &[1])]);
  assert!(parse_polynomial(&forward).unwrap_err().contains("later"));
  let own = nodes(&[(1, &[0]), (2, &[0, 1])]);
  assert!(parse_polynomial(&own).unwrap_err().contains("later"));
  let shared = nodes(&[(1, &[0]), (2, &[0, 0])]);
  assert!(parse_polynomial(&shared).unwrap_err().contains("shared"));
  let reused = nodes(&[(1, &[0]), (1, &[1]), (2, &[0, 1]), (3, &[0, 2])]);
  assert!(parse_polynomial(&reused).unwrap_err().contains("shared"));
  let unreferenced = nodes(&[(1, &[0]), (1, &[1])]);
  assert!(
    parse_polynomial(&unreferenced).unwrap_err().contains("unreferenced")
  );
  assert!(parse_polynomial(&nodes(&[])).unwrap_err().contains("empty"));
  assert!(parse_polynomial(&nodes(&[(5, &[])])).is_err());
  assert!(parse_polynomial(&nodes(&[(0, &[P])])).is_err());
}

#[test]
fn bounded_counts_and_nesting() {
  let mut w = Writer::new();
  w.u64(u64::MAX);
  assert!(Reader::new(w.as_bytes()).count().is_err());
  let mut w = Writer::new();
  w.u64(9);
  w.raw(&[0; 8]);
  assert!(Reader::new(w.as_bytes()).count().is_err());
  let mut ty = Type::Field;
  for _ in 0..MAX_NESTING {
    ty = Type::Ptr { target: Box::new(ty) };
  }
  let mut w = Writer::new();
  write_type(&mut w, &ty);
  assert!(read_type(&mut Reader::new(w.as_bytes())).is_err());
  let Type::Ptr { target } = ty else { unreachable!() };
  let mut w = Writer::new();
  write_type(&mut w, &target);
  assert_eq!(read_type(&mut Reader::new(w.as_bytes())).unwrap(), *target);
  let mut io = IoType::Field;
  for _ in 0..=MAX_NESTING {
    io = IoType::Tuple { items: vec![io] };
  }
  let mut w = Writer::new();
  write_io_type(&mut w, &io);
  assert!(read_io_type(&mut Reader::new(w.as_bytes())).is_err());
  let mut r = Reader::new(&[2]);
  assert!(r.bool().is_err());
  let mut r = Reader::new(&[1, 0, 0, 0, 0, 0, 0, 0, 0xff]);
  assert!(r.str().unwrap_err().contains("UTF-8"));
}

/// Runs `body` on a thread whose stack fits recursive traversals of very
/// deep polynomials (derived equality and drop recurse).
fn with_large_stack(body: impl FnOnce() + std::marker::Send + 'static) {
  std::thread::Builder::new()
    .stack_size(256 << 20)
    .spawn(body)
    .unwrap()
    .join()
    .unwrap();
}

#[test]
fn deep_polynomial_round_trip() {
  with_large_stack(|| {
    let mut deep = var(0);
    for i in 0..100_000u64 {
      deep = match i % 3 {
        0 => add(deep, constant(i)),
        1 => sub(var(1), deep),
        _ => mul(deep, var(2)),
      };
    }
    let mut package = sample();
    package.trace.groups[0].constraints.push(deep);
    let bytes = encode(&package).unwrap();
    let decoded = decode(&bytes).unwrap();
    assert_eq!(decoded, package);
    for p in [package, decoded] {
      let mut trace = p.trace;
      trace.groups[0].constraints.drain(..).for_each(dismantle);
    }
  });
}

#[test]
fn deep_malformed_polynomial_is_rejected_without_recursion() {
  // A 100 000-deep chain followed by an unreferenced node: the decoder must
  // discard the chain without the recursive drop.
  let depth = 100_000u64;
  let mut raw: Vec<(u8, Vec<u64>)> = vec![(1, vec![0])];
  for i in 0..depth {
    raw.push((1, vec![1]));
    raw.push((2, vec![2 * i, 2 * i + 1]));
  }
  raw.push((1, vec![0]));
  let raw: Vec<(u8, &[u64])> =
    raw.iter().map(|(t, o)| (*t, o.as_slice())).collect();
  assert!(parse_polynomial(&nodes(&raw)).unwrap_err().contains("unreferenced"));
}

#[test]
fn read_and_write_files() {
  let dir = std::env::temp_dir()
    .join(format!("aiur-artifact-test-{}", std::process::id()));
  std::fs::create_dir_all(&dir).unwrap();
  let path = dir.join("sample.aiur");
  let package = sample();
  write_atomic(&path, &package).unwrap();
  write_atomic(&path, &package).unwrap();
  assert_eq!(read(&path).unwrap(), package);
  let leftovers = std::fs::read_dir(&dir).unwrap().count();
  assert_eq!(leftovers, 1);
  let json = dir.join("sample.json");
  let mut text = b"  \n".to_vec();
  text.extend(to_json(&package.program, &package.trace).unwrap());
  std::fs::write(&json, text).unwrap();
  let error = read(&json).unwrap_err();
  assert!(error.contains("JSON artifact"), "{error}");
  assert!(error.contains("aiur-artifact convert"), "{error}");
  std::fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn random_corruption_never_panics() {
  let bytes = encode(&sample()).unwrap();
  let mut state = 0x9e37_79b9_7f4a_7c15u64;
  let mut next = move || {
    state ^= state << 13;
    state ^= state >> 7;
    state ^= state << 17;
    state
  };
  let body = bytes.len() - DIGEST_LEN;
  let mut accepted = 0;
  for _ in 0..20_000 {
    let mut bad = bytes.clone();
    for _ in 0..1 + next() % 4 {
      let at = HEADER_LEN + (next() as usize) % (body - HEADER_LEN);
      bad[at] = match next() % 3 {
        0 => bad[at] ^ (1 << (next() % 8)),
        1 => 0xff,
        _ => next() as u8,
      };
    }
    if decode(&sign(bad)).is_ok() {
      accepted += 1;
    }
  }
  assert!(accepted < 20_000);
}
