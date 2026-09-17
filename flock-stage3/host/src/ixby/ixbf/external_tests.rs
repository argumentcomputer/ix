//! Explicit opt-in checks against separately generated reference artifacts.
//! No compiler checkout, binary image or native proof is a crate dependency.
use super::*;
use num_bigint::BigUint;
use std::{
  ffi::OsStr,
  fs::File,
  io::Read,
  path::{Path, PathBuf},
};

fn path(variable: &str) -> PathBuf {
  std::env::var_os(variable).map(PathBuf::from).unwrap_or_else(|| {
    panic!("{variable} must explicitly name the retained external fixture")
  })
}

fn read(path: &Path) -> Vec<u8> {
  let limit = DecodeLimits::default().bytes;
  let mut bytes = Vec::new();
  File::open(path)
    .unwrap()
    .take(limit as u64 + 1)
    .read_to_end(&mut bytes)
    .unwrap();
  assert!(bytes.len() <= limit, "external fixture file byte limit");
  bytes
}

#[test]
#[ignore = "requires the independently exported complete-functional compiler corpus"]
fn compiler_corpus_covers_complete_functional_wire() {
  let directory = path("IXBY_IXBF_CORPUS");
  let mut files: Vec<_> = std::fs::read_dir(&directory)
    .unwrap()
    .map(|entry| entry.unwrap())
    .filter(|entry| {
      entry.file_type().unwrap().is_file()
        && entry.path().extension() == Some(OsStr::new("ixby"))
    })
    .map(|entry| entry.path())
    .collect();
  files.sort();
  let mut scalars = [0usize; 7];
  let mut instructions = [0usize; 8];
  let mut operations = [0usize; 8];
  let mut primitives = [0usize; 58];
  for path in &files {
    let bytes = read(path);
    let artifact = decode_program(&bytes, DecodeLimits::default()).unwrap();
    assert_eq!(artifact.encode(), bytes);
    assert_eq!(artifact.max_steps(), &((BigUint::from(1u8) << 70usize) + 17u8));
    let inventory = artifact.inventory();
    for (total, value) in scalars.iter_mut().zip(inventory.scalars) {
      *total += value.literals;
    }
    for (total, value) in instructions.iter_mut().zip(inventory.instructions) {
      *total += value;
    }
    for (total, value) in operations.iter_mut().zip(inventory.operations) {
      *total += value;
    }
    for value in inventory.primitives {
      primitives[usize::from(value.primitive.opcode())] += value.sites;
    }
  }
  assert!(scalars.iter().all(|count| *count != 0), "incomplete scalar corpus");
  assert!(
    instructions.iter().all(|count| *count != 0),
    "incomplete instruction corpus"
  );
  assert!(
    operations.iter().all(|count| *count != 0),
    "incomplete operation corpus"
  );
  assert!(
    primitives.iter().all(|count| *count != 0),
    "incomplete primitive corpus"
  );
  let bytes = read(&directory.join("identity.ixby"));
  let artifact = decode_program(&bytes, DecodeLimits::default()).unwrap();
  let input_bytes = read(&directory.join("identity.ixbi"));
  let output_bytes = read(&directory.join("identity.ixbo"));
  let input =
    decode_input(&artifact, &input_bytes, DecodeLimits::default()).unwrap();
  let output =
    decode_output(&artifact, &output_bytes, DecodeLimits::default()).unwrap();
  assert_eq!(input.values().nodes(), output.values().nodes());
  assert!(input.values().depth() >= 3, "structured value nesting");
  let mut kinds = [false; 5];
  for node in input.values().nodes() {
    kinds[match node.kind {
      ValueKind::Scalar(_) => 0,
      ValueKind::Constructor(_) => 1,
      ValueKind::PartialApplication(_) => 2,
      ValueKind::Erased => 3,
      ValueKind::Array => 4,
    }] = true;
  }
  assert!(kinds.into_iter().all(|seen| seen), "incomplete wire-value corpus");
  eprintln!(
    "independent IXBF corpus: {} programs; all 58 primitives, 7 scalar kinds, 5 value kinds, 8 operations and 8 instructions; structured I/O",
    files.len()
  );
}

#[test]
#[ignore = "requires the exact retained Stage 2 binary and successful Init input/output"]
fn retained_stage2_init_artifacts_match_exact_pins() {
  let bytes = read(&path("IXBY_IXBF_STAGE2_IMAGE"));
  assert_eq!(
    blake3::hash(&bytes).to_hex().as_str(),
    crate::ixby::test_support::INIT_PROGRAM_V2_BLAKE3
  );
  let artifact = decode_program(&bytes, DecodeLimits::default()).unwrap();
  let census = artifact.inventory();
  assert_eq!(
    (
      bytes.len(),
      artifact.entry(),
      census.functions,
      census.blocks,
      census.constructors
    ),
    (1_002_355, 680, 681, 6_763, 146)
  );
  assert_eq!(artifact.max_steps(), &BigUint::from(16_000_000_000u64));
  assert_eq!(census.maximum_function_arity, BigUint::from(55u8));
  assert_eq!(census.maximum_frame_locals, BigUint::from(73u8));
  assert_eq!(census.maximum_constructor_fields, BigUint::from(9u8));
  assert_eq!(
    (census.maximum_function_blocks, census.maximum_operand_vector),
    (185, 55)
  );
  assert_eq!(census.instructions, [3627, 530, 1183, 0, 1, 1016, 0, 406]);
  assert_eq!(census.operations, [0, 239, 747, 33, 67, 2533, 0, 8]);
  assert_eq!(census.primitives.len(), 41);
  assert!(
    census.primitives.iter().all(|primitive| primitive.native_opcode.is_some())
  );
  assert_eq!(
    census.scalars.iter().map(|s| s.literals).collect::<Vec<_>>(),
    [608, 0, 4, 618, 2, 0, 6]
  );
  assert_eq!(census.scalars[0].maximum_bits, 65);
  assert_eq!(census.scalars[6].maximum_bytes, 744_159);
  let input_bytes = read(&path("IXBY_IXBF_INIT_INPUT"));
  let output_bytes = read(&path("IXBY_IXBF_INIT_OUTPUT"));
  assert_eq!(
    blake3::hash(&input_bytes).to_hex().as_str(),
    crate::ixby::test_support::INIT_INPUT_V2_BLAKE3
  );
  assert_eq!(
    blake3::hash(&output_bytes).to_hex().as_str(),
    crate::ixby::test_support::INIT_OUTPUT_V2_BLAKE3
  );
  let input =
    decode_input(&artifact, &input_bytes, DecodeLimits::default()).unwrap();
  let output =
    decode_output(&artifact, &output_bytes, DecodeLimits::default()).unwrap();
  assert_eq!(
    (input.source().len(), input.values().nodes().len(), output.source().len()),
    (9_611_120, 2, 49)
  );
  let claim_hex =
    "e5b3e3b111341071d9458212c5dad62dbb628b50d9ec2fb72987bb4f451c37f91000";
  let claim: Vec<_> = (0..claim_hex.len())
    .step_by(2)
    .map(|offset| {
      u8::from_str_radix(&claim_hex[offset..offset + 2], 16).unwrap()
    })
    .collect();
  assert_eq!(
    input.values().nodes()[0].kind,
    ValueKind::Scalar(Scalar::Bytes(&claim))
  );
  assert_eq!(
    output.values().nodes()[0].kind,
    ValueKind::Scalar(Scalar::Bytes(&claim))
  );
  let ValueKind::Scalar(Scalar::Bytes(proof)) = input.values().nodes()[1].kind
  else {
    panic!("native proof bytes")
  };
  assert_eq!(proof.len(), 9_611_064);
  eprintln!(
    "real Init IXBF/IXFI/IXFO canonical intake and static census: passed; no execution proof generated"
  );
}
