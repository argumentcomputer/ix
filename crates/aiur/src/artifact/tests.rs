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
  version[8] = 2;
  assert!(Package::decode(&version).unwrap_err().contains("version 2"));
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
    (&[2, 1, 0, 5], |r| poly(r).map(drop), "polynomial tag 5"),
    (&[8], |r| action(r).map(drop), "action tag 8"),
  ];
  for (bytes, f, message) in checks {
    let error = read(bytes, f).unwrap_err();
    assert!(error.contains(message), "{error}");
  }
  // A program version beyond u32.
  let mut w = Writer::new();
  w.nat(u64::from(u32::MAX) + 1);
  let bytes = w.into_bytes();
  assert!(program(&mut Reader::new(&bytes)).unwrap_err().contains("u32"));
  // An assertion's runtime check is a strict bool.
  let error = instruction(&mut Reader::new(&[11, 0, 0, 0, 2])).unwrap_err();
  assert!(error.contains("bool tag 2"), "{error}");
}

#[test]
fn deep_polynomials_need_no_recursion() {
  let mut p = Polynomial::Var(0);
  for i in 0..200_000u64 {
    p = Polynomial::Add(Box::new([p, Polynomial::Const(i)]));
  }
  let mut w = Writer::new();
  put_poly(&mut w, &p);
  let bytes = w.into_bytes();
  let mut r = Reader::new(&bytes);
  let decoded = poly(&mut r).unwrap();
  r.finish().unwrap();
  let mut again = Writer::new();
  put_poly(&mut again, &decoded);
  assert_eq!(again.into_bytes(), bytes);
  // Release both chains without recursing through `Drop`.
  for mut p in [p, decoded] {
    while let Polynomial::Add(xs) = p {
      let [left, _] = *xs;
      p = left;
    }
  }
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

/// Lean writes the canonical encoding: re-encoding what Rust decodes from
/// Lean's grouping fixture reproduces its bytes.
#[test]
fn lean_fixture_is_canonical() {
  let bytes = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/grouping.ixa"
  ));
  let package = Package::decode(bytes).unwrap();
  assert!(package.trace.as_ref().is_some_and(|t| t.groups.len() == 1));
  assert_eq!(package.encode(), bytes);
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
