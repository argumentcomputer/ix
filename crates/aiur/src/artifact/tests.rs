use super::*;
use serde_json::json;

/// A program and plan using every variant of the grammar. JSON is only the
/// literal notation of the Rust structures here.
fn sample() -> Package {
  let f = json!({"kind":"field"});
  let pair = json!({"kind":"tuple","items":[f, {"kind":"ptr","target":f}]});
  let named = json!({"kind":"enum","name":"Choice"});
  let program: Program = serde_json::from_value(json!({
    "version": 2, "modulus": 18446744069414584321u64,
    "functions": [{"name": "main", "params": [f, pair], "result": named,
      "registers": 300, "code": [
        {"op":"literal","dest":200,"value":18446744069414584320u64},
        {"op":"copy","dest":[1,2],"source":[3,4]},
        {"op":"neg","dest":5,"source":6},
        {"op":"binary","dest":7,"operator":"add","left":1,"right":2},
        {"op":"binary","dest":7,"operator":"sub","left":1,"right":2},
        {"op":"binary","dest":7,"operator":"mul","left":1,"right":2},
        {"op":"binary","dest":7,"operator":"div","left":1,"right":2},
        {"op":"guard","tests":[[1, 0], [2, 99999]],"message":"guarded ✓"},
        {"op":"branch","tests":[[1, 3]],"otherwise":20000},
        {"op":"jump","target":5000000},
        {"op":"call","function":0,"args":[1],"dest":[2,3]},
        {"op":"store","type":pair,"value":[1,2],"dest":9},
        {"op":"load","type":pair,"pointer":9,"dest":[1,2]},
        {"op":"hint","channel":"ch","type":f,"key_type":named,"key":[1],"dest":[2]},
        {"op":"assert_eq","left":[1],"right":[2],"message":null,"runtime_check":false},
        {"op":"assert_eq","left":[],"right":[],"message":"same","runtime_check":true},
        {"op":"ret","value":[1,2,3]},
        {"op":"fail","message":""}]}],
    "enums": [{"name":"Choice","constructors":[
      {"name":"None","fields":[]},{"name":"Some","fields":[f, named]}]}],
    "tables": [{"name":"xs","type":pair,"rows":[[0, 1], [4311826560u64, 2]]}],
    "maps": [{"name":"m","params":[f],"result":pair,"input":1,"output":2}],
    "entries": [
      {"name":"main","function":0,"inputs":[
        {"kind":"field"},
        {"kind":"tuple","items":[{"kind":"field"}]},
        {"kind":"array","element":{"kind":"field"},"length":16512},
        {"kind":"struct","name":"S","fields":[["x",{"kind":"field"}]]},
        {"kind":"enum","name":"E","constructors":[["A",[]],["B",[{"kind":"field"}]]]}],
       "output":{"kind":"field"}},
      {"name":"unit","function":0,"inputs":[],"output":null}]
  }))
  .unwrap();
  let x = json!({"var": 0});
  let c = json!({"const": 18446744069414584320u64});
  let sum = json!({"add": [x, {"sub": [c, {"mul": [x, x]}]}]});
  let trace: TraceArtifact = serde_json::from_value(json!({
    "version": 3, "modulus": 18446744069414584321u64, "limbs": [16, 8],
    "functions": [{"name":"main","chip":"main","witnesses":4,"inputs":[0],
      "output":[1],"steps":[
        {"guard":c,"action":{"op":"assign","dest":[1],"values":[sum]}},
        {"guard":x,"action":{"op":"inverse","dest":1,"value":x}},
        {"guard":x,"action":{"op":"choose","dest":[1],"tests":[[x],[]]}},
        {"guard":x,"action":{"op":"failure","dest":[1],"differences":[x]}},
        {"guard":x,"action":{"op":"call","name":"main","args":[x],"dest":[2]}},
        {"guard":x,"action":{"op":"store","type":pair,"values":[x],"dest":3}},
        {"guard":x,"action":{"op":"load","type":f,"address":x,"dest":[1]}},
        {"guard":x,"action":{"op":"hint","channel":"","instruction":13,
          "type":f,"key_type":f,"key":[x],"dest":[2]}}],
      "writes":[{"column":0,"source":3,"guard":sum}]}],
    "chips": [{"name":"main","width":3,"activation":2,"inputs":[0],
      "output":[x],"constraints":[sum],
      "sends":[{"channel":"call","args":[x],"result":[1],"enable":c}],
      "memory":[{"type":pair,"address":x,"values":[x, c],"enable":x}],
      "depth":{"column":1,"rank":7,"slots":[{"kind":"gap","column":0}]}},
     {"name":"leaf","width":1,"activation":0,"inputs":[],"output":[],
      "constraints":[],"sends":[{"channel":"call","args":[],"result":[],"enable":c}],
      "memory":[],"depth":{"column":null,"rank":2,
        "slots":[{"kind":"external","column":0}]}}],
    "groups": [{"name":"g","width":5,"activation":x,"constraints":[sum],
      "receive":[x],"sends":[{"enable":x,"args":[c]}],
      "members":[{"name":"main","columns":[0,1],"selector":4,
        "writes":[{"column":2,"value":sum}]}]}]
  }))
  .unwrap();
  Package { program, trace: Some(trace) }
}

fn sample_hints() -> Vec<HintEntry> {
  serde_json::from_value(json!([
    {"channel":"","type":{"kind":"field"},"key_type":{"kind":"field"},
     "key":[1, 2],"output":[3]},
    {"channel":"ixvm.io.read","type":{"kind":"tuple","items":[]},
     "key_type":{"kind":"enum","name":"Choice"},"key":[],"output":[]}
  ]))
  .unwrap()
}

#[test]
fn packages_round_trip_canonically() {
  let package = sample();
  let bytes = package.encode();
  assert_eq!(&bytes[..8], PACKAGE_MAGIC);
  let decoded = Package::decode(&bytes).unwrap();
  assert_eq!(decoded, package);
  assert_eq!(decoded.encode(), bytes);
  let bare = Package { trace: None, ..package.clone() };
  assert_eq!(Package::decode(&bare.encode()).unwrap(), bare);

  let execution = ExecutionPackage {
    package_digest: Digest::of(&bytes),
    package,
    args: vec![0, u64::MAX],
    invalid_args: vec![7],
    hints: sample_hints(),
  };
  let encoded = execution.encode();
  let decoded = ExecutionPackage::decode(&encoded).unwrap();
  assert_eq!(decoded, execution);
  assert_eq!(decoded.encode(), encoded);
  let hints = encode_hints(&execution.hints);
  assert_eq!(decode_hints(&hints).unwrap(), execution.hints);
  let groups = &execution.package.trace.as_ref().unwrap().groups;
  let encoded = encode_groups(groups);
  assert_eq!(&decode_groups(&encoded).unwrap(), groups);
  assert!(decode_groups(&encoded[..encoded.len() - 1]).is_err());
}

#[test]
fn decoding_is_strict() {
  let bytes = sample().encode();
  // Every proper prefix is rejected, as are trailing bytes.
  for end in 0..bytes.len() {
    assert!(Package::decode(&bytes[..end]).is_err(), "prefix {end}");
  }
  let mut trailing = bytes.clone();
  trailing.push(0);
  assert!(Package::decode(&trailing).unwrap_err().contains("trailing"));
  // Magic, kind and version.
  let mut other = bytes.clone();
  other[0] = b'J';
  assert!(Package::decode(&other).unwrap_err().contains("not an Aiur"));
  assert!(
    ExecutionPackage::decode(&bytes)
      .unwrap_err()
      .contains("found a compiled package")
  );
  let mut version = bytes.clone();
  version[8] = 3;
  assert!(Package::decode(&version).unwrap_err().contains("version 3"));
  // An option tag beyond `some` where the trace begins.
  let bare = Package { trace: None, ..sample() }.encode();
  let mut option = bare.clone();
  *option.last_mut().unwrap() = 2;
  assert!(Package::decode(&option).unwrap_err().contains("option tag 2"));
}

type Check = fn(&mut Reader<'_>) -> Result<(), String>;

#[test]
fn unknown_tags_and_out_of_range_values_are_rejected() {
  let read = |bytes: &[u8], f: Check| {
    let mut r = Reader::new(bytes);
    f(&mut r)
  };
  let checks: [(&[u8], Check, &str); 6] = [
    (&[4], |r| ty(r).map(drop), "type tag 4"),
    (&[5], |r| io_type(r).map(drop), "IO type tag 5"),
    (&[14], |r| instruction(r).map(drop), "instruction tag 14"),
    (&[3, 0, 4, 0, 0], |r| instruction(r).map(drop), "operator tag 4"),
    (&[2, 1, 0, 5], |r| tree(r).map(drop), "polynomial tag 5"),
    (&[8], |r| action(r, &mut Polys::Trees).map(drop), "action tag 8"),
  ];
  for (bytes, f, message) in checks {
    let error = read(bytes, f).unwrap_err();
    assert!(error.contains(message), "{error}");
  }
  // A program version beyond u32.
  let mut w = Writer::new();
  w.nat(u64::from(u32::MAX) + 1);
  let bytes = w.into_bytes();
  assert!(
    program(&mut Reader::new(&bytes), Version::V2).unwrap_err().contains("u32")
  );
  // An assertion's runtime check is a strict bool.
  let error = instruction(&mut Reader::new(&[11, 0, 0, 0, 2])).unwrap_err();
  assert!(error.contains("bool tag 2"), "{error}");
}

/// The version 1 tree encoding of a polynomial, which writers no longer
/// emit.
fn put_tree(w: &mut Writer, p: &Polynomial) {
  let mut pending = vec![p];
  while let Some(p) = pending.pop() {
    match p {
      Polynomial::Const(value) => {
        w.u8(0);
        w.nat(*value);
      },
      Polynomial::Var(var) => {
        w.u8(1);
        w.usize(*var);
      },
      Polynomial::Add(xs) | Polynomial::Sub(xs) | Polynomial::Mul(xs) => {
        w.u8(match p {
          Polynomial::Add(_) => 2,
          Polynomial::Sub(_) => 3,
          _ => 4,
        });
        pending.push(&xs[1]);
        pending.push(&xs[0]);
      },
    }
  }
}

fn var(index: usize) -> Polynomial {
  Polynomial::Var(index)
}

fn add(a: Polynomial, b: Polynomial) -> Polynomial {
  Polynomial::Add(Box::new([a, b]))
}

fn mul(a: Polynomial, b: Polynomial) -> Polynomial {
  Polynomial::Mul(Box::new([a, b]))
}

/// A pool read from complete `bytes`, with constants below 7.
fn read_nodes(bytes: &[u8]) -> Result<Nodes, String> {
  let mut r = Reader::new(bytes);
  let nodes = Nodes::read(&mut r, Some(7))?;
  r.finish()?;
  Ok(nodes)
}

/// The polynomial of root `root` in `nodes`.
fn root(nodes: &mut Nodes, root: u64) -> Result<Polynomial, String> {
  let mut w = Writer::new();
  w.nat(root);
  let bytes = w.into_bytes();
  nodes.poly(&mut Reader::new(&bytes))
}

#[test]
fn deep_polynomials_need_no_recursion() {
  let mut p = var(0);
  for i in 0..200_000u64 {
    p = add(p, Polynomial::Const(i));
  }
  // Version 1 trees.
  let mut w = Writer::new();
  put_tree(&mut w, &p);
  let bytes = w.into_bytes();
  let mut r = Reader::new(&bytes);
  let from_tree = tree(&mut r).unwrap();
  r.finish().unwrap();
  let mut again = Writer::new();
  put_tree(&mut again, &from_tree);
  assert_eq!(again.into_bytes(), bytes);
  // Version 2 node pools.
  let mut interner = Interner::default();
  let index = interner.intern(&p);
  let mut w = Writer::new();
  interner.put(&mut w);
  let mut nodes = Nodes::read(&mut Reader::new(&w.into_bytes()), None).unwrap();
  let from_pool = root(&mut nodes, u64::try_from(index).unwrap()).unwrap();
  let mut again = Writer::new();
  put_tree(&mut again, &from_pool);
  assert_eq!(again.into_bytes(), bytes);
  // Release the chains without recursing through `Drop`.
  for mut p in [p, from_tree, from_pool] {
    while let Polynomial::Add(xs) = p {
      let [left, _] = *xs;
      p = left;
    }
  }
}

/// A group whose polynomials are `activation` and `constraints`.
fn bare_group(
  name: &str,
  activation: Polynomial,
  constraints: Vec<Polynomial>,
) -> FunctionGroup {
  FunctionGroup {
    name: name.into(),
    width: 2,
    activation,
    constraints,
    receive: vec![],
    sends: vec![],
    members: vec![],
  }
}

/// Each distinct node is stored once, in the order a post-order walk of
/// the polynomials, in file order, first completes it. Lean's writer
/// (`Aiur.Trace`) produces these bytes for the same groups.
#[test]
fn shared_subexpressions_are_stored_once() {
  let sum = add(var(0), var(1));
  let square = mul(sum.clone(), sum);
  let groups = vec![
    bare_group("a", var(0), vec![square.clone()]),
    bare_group("b", var(0), vec![var(1), square]),
  ];
  let bytes = encode_groups(&groups);
  let mut expected = GROUPS_MAGIC.to_vec();
  expected.extend([2]);
  // x0, x1, x0 + x1 and (x0 + x1)^2, operands as distances back.
  expected.extend([4, 1, 0, 1, 1, 2, 2, 1, 4, 1, 1]);
  expected.extend([2]);
  expected.extend([1, b'a', 2, 0, 1, 3, 0, 0, 0]);
  expected.extend([1, b'b', 2, 0, 2, 1, 3, 0, 0, 0]);
  assert_eq!(bytes, expected);
  assert_eq!(decode_groups(&bytes).unwrap(), groups);

  // A polynomial reused by a second chip adds no node to the pool.
  let pool_size = |package: &Package| {
    let bare = Package { trace: None, ..package.clone() }.encode();
    let bytes = package.encode();
    let mut r = Reader::new(&bytes[bare.len()..]);
    r.nat().unwrap();
    r.nat().unwrap();
    r.usizes().unwrap();
    r.nat().unwrap()
  };
  let package = sample();
  let mut shared = package.clone();
  let trace = shared.trace.as_mut().unwrap();
  let constraint = trace.chips[0].constraints[0].clone();
  trace.chips[1].constraints.push(constraint);
  // Repeated table rows are stored once and expanded on reading.
  let mut table = shared.program.tables[0].clone();
  table.name = "ys".into();
  table.rows.push(table.rows[0].clone());
  shared.program.tables.push(table);
  assert_eq!(pool_size(&shared), pool_size(&package));
  let bytes = shared.encode();
  let decoded = Package::decode(&bytes).unwrap();
  assert_eq!(decoded, shared);
  assert_eq!(decoded.encode(), bytes);
}

#[test]
fn pool_references_point_back_into_the_pool() {
  // x0, x1, x0 + x1.
  let mut nodes = read_nodes(&[3, 1, 0, 1, 1, 2, 2, 1]).unwrap();
  assert_eq!(root(&mut nodes, 2).unwrap(), add(var(0), var(1)));
  let error = root(&mut nodes, 3).unwrap_err();
  assert!(error.contains("root 3 is not one of the 3"), "{error}");
  for (bytes, message) in [
    // A zero distance (a node referring to itself).
    (&[2, 1, 0, 2, 0, 1][..], "refers 0 nodes back"),
    // Distances past the first node.
    (&[2, 1, 0, 2, 1, 2][..], "refers 2 nodes back"),
    (&[1, 2, 1, 1][..], "refers 1 nodes back"),
    (&[1, 5][..], "polynomial node tag 5"),
    (&[1, 0, 7][..], "not below the modulus 7"),
    (&[2, 1, 0][..], "end of input"),
    (&[3, 1, 0][..], "count 3"),
  ] {
    let error = read_nodes(bytes).map(drop).unwrap_err();
    assert!(error.contains(message), "{error}");
  }
  // The same checks apply within a file.
  let mut forward = GROUPS_MAGIC.to_vec();
  forward.extend([2, 2, 2, 1, 1, 1, 0, 0]);
  let error = decode_groups(&forward).unwrap_err();
  assert!(error.contains("refers 1 nodes back"), "{error}");
  let mut missing = GROUPS_MAGIC.to_vec();
  missing.extend([2, 1, 1, 0, 1, 1, b'g', 2, 1, 0, 0, 0, 0]);
  let error = decode_groups(&missing).unwrap_err();
  assert!(error.contains("root 1 is not one of the 1"), "{error}");
  // Table rows: values below the modulus, indices into the pool.
  let error = Rows::read(&mut Reader::new(&[1, 1, 7]), 7).unwrap_err();
  assert!(error.contains("table value 7"), "{error}");
  let mut rows = Rows::read(&mut Reader::new(&[1, 1, 6]), 7).unwrap();
  assert_eq!(
    rows.table(&mut Reader::new(&[2, 0, 0])).unwrap(),
    vec![vec![6], vec![6]]
  );
  let error = rows.table(&mut Reader::new(&[1, 1])).unwrap_err();
  assert!(error.contains("table row 1 is not one of the 1"), "{error}");
}

#[test]
fn polynomial_expansion_is_bounded() {
  // x0, then 40 doublings: node i expands to 2^(i + 1) - 1 nodes.
  let mut bytes = vec![41, 1, 0];
  for _ in 0..40 {
    bytes.extend([2, 1, 1]);
  }
  let error = root(&mut read_nodes(&bytes).unwrap(), 40).unwrap_err();
  assert!(error.contains("expand to more than"), "{error}");
  // Node 27 alone fits the bound, which counts every polynomial read from
  // the pool.
  let mut nodes = read_nodes(&bytes).unwrap();
  assert!(root(&mut nodes, 10).is_ok());
  let error = root(&mut nodes, 27).unwrap_err();
  assert!(error.contains("expand to more than"), "{error}");
}

#[test]
fn content_addressed_names_are_checked() {
  let bytes = sample().encode();
  let digest = Digest::of(&bytes);
  assert_eq!(Digest::from_hex(&digest.to_string()).unwrap(), digest);
  assert!(Digest::from_hex(&digest.to_string().to_uppercase()).is_err());
  let dir = std::env::temp_dir().join(format!("aiur-artifact-{digest}"));
  std::fs::create_dir_all(&dir).unwrap();
  let named = dir.join(format!("ixvm-{digest}.{EXTENSION}"));
  std::fs::write(&named, &bytes).unwrap();
  let (package, loaded) = Package::load(&named).unwrap();
  assert_eq!((package, loaded), (sample(), digest));
  let plain = dir.join("plain.ixa");
  std::fs::write(&plain, &bytes).unwrap();
  assert_eq!(Package::load(&plain).unwrap().1, digest);
  let mut tampered = bytes.clone();
  *tampered.last_mut().unwrap() ^= 1;
  std::fs::write(&named, &tampered).unwrap();
  let error = Package::load(&named).unwrap_err();
  assert!(error.contains("named by digest"), "{error}");
  std::fs::remove_dir_all(&dir).unwrap();
}

/// Version 1 copies of Lean's fixtures still decode, and re-encoding them
/// writes exactly the version 2 bytes Lean's writer produced for the same
/// programs.
#[test]
fn version_1_fixtures_still_decode() {
  let grouping = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/grouping.v1.ixa"
  ));
  let depth = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/depth.v1.ixa"
  ));
  let lean = [
    &include_bytes!(concat!(
      env!("CARGO_MANIFEST_DIR"),
      "/tests/fixtures/grouping.ixa"
    ))[..],
    &include_bytes!(concat!(
      env!("CARGO_MANIFEST_DIR"),
      "/tests/fixtures/depth.ixa"
    ))[..],
  ];
  for (bytes, lean) in [&grouping[..], &depth[..]].into_iter().zip(lean) {
    assert_eq!(bytes[8], 1);
    let package = Package::decode(bytes).unwrap();
    let encoded = package.encode();
    assert_eq!(encoded[8], 2);
    assert_eq!(encoded, lean);
    let decoded = Package::decode(&encoded).unwrap();
    assert_eq!(decoded, package);
    assert_eq!(decoded.encode(), encoded);
  }
  let package = Package::decode(grouping).unwrap();
  assert!(package.trace.as_ref().is_some_and(|t| t.groups.len() == 1));
  // A version 1 grouping, with its activation x0 + 5 as a tree.
  let mut v1 = GROUPS_MAGIC.to_vec();
  v1.extend([1, 1, 1, b'g', 2, 2, 1, 0, 0, 5, 0, 0, 0, 0]);
  let groups = vec![bare_group("g", add(var(0), Polynomial::Const(5)), vec![])];
  assert_eq!(decode_groups(&v1).unwrap(), groups);
  assert_eq!(decode_groups(&encode_groups(&groups)).unwrap(), groups);
}

fn sample_invocation() -> Invocation {
  Invocation {
    entry: "IxVM::verify_claim".into(),
    args: vec![0, 1, 127, 128, u64::MAX],
    streams: Streams(vec![
      Stream { channel: 0, key: vec![1, 2], values: vec![0, 255, 16512] },
      Stream { channel: 7, key: vec![], values: vec![] },
    ]),
  }
}

#[test]
fn invocations_round_trip_strictly() {
  let invocation = sample_invocation();
  let bytes = invocation.encode();
  assert_eq!(&bytes[..8], INVOCATION_MAGIC);
  let decoded = Invocation::decode(&bytes).unwrap();
  assert_eq!(decoded, invocation);
  assert_eq!(decoded.encode(), bytes);
  for end in 0..bytes.len() {
    assert!(Invocation::decode(&bytes[..end]).is_err(), "prefix {end}");
  }
  let mut trailing = bytes.clone();
  trailing.push(0);
  assert!(Invocation::decode(&trailing).unwrap_err().contains("trailing"));
  let error = Invocation::decode(&sample().encode()).unwrap_err();
  assert!(error.contains("found a compiled package"), "{error}");
  let error = Package::decode(&bytes).unwrap_err();
  assert!(error.contains("found an invocation"), "{error}");
  // A stream count beyond the remaining input.
  let mut w = Writer::new();
  w.raw(INVOCATION_MAGIC);
  w.nat(FORMAT_VERSION);
  w.str("e");
  w.nats(&[]);
  w.nat(1000);
  let error = Invocation::decode(&w.into_bytes()).unwrap_err();
  assert!(error.contains("count 1000"), "{error}");
}

#[test]
fn case_files_round_trip_strictly() {
  let cases = vec![
    Case {
      label: "accepted ✓".into(),
      accept: true,
      rejects_with: None,
      exercises: Some("IxVM::check".into()),
      invocation: sample_invocation(),
    },
    Case {
      label: "rejected".into(),
      accept: false,
      rejects_with: Some("hash of the supplied bytes".into()),
      exercises: None,
      invocation: Invocation {
        streams: Streams::default(),
        ..sample_invocation()
      },
    },
  ];
  let bytes = encode_cases(&cases);
  assert_eq!(&bytes[..8], CASES_MAGIC);
  assert_eq!(decode_cases(&bytes).unwrap(), cases);
  assert_eq!(decode_cases(&encode_cases(&[])).unwrap(), vec![]);
  // Every truncation is refused, including one at a case boundary.
  for end in 0..bytes.len() {
    assert!(decode_cases(&bytes[..end]).is_err(), "prefix {end}");
  }
  let mut trailing = bytes.clone();
  trailing.push(0);
  assert!(decode_cases(&trailing).unwrap_err().contains("trailing"));
  let mut continuation = bytes.clone();
  *continuation.last_mut().unwrap() = 2;
  let error = decode_cases(&continuation).unwrap_err();
  assert!(error.contains("case continuation tag 2"), "{error}");
  // A verdict is a strict bool.
  let label_end = 9 + 1 + 1 + "accepted ✓".len();
  let mut verdict = bytes.clone();
  verdict[label_end] = 2;
  let error = decode_cases(&verdict).unwrap_err();
  assert!(error.contains("bool tag 2"), "{error}");
}
