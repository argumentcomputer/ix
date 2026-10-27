//! Artifact binding transport. These tests do not claim semantic admission.

use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use ix_common::address::Address;
use ixon::diff::diff_envs;
use ixon::env::{Env, RoleBinding};
use ixon::role_table::RoleTable;
use ixon::tag::TagN;
use rustc_hash::FxHashSet;

const INPUTS: [&[u8]; 6] = [
  include_bytes!("../../kernel/tests/fixtures/input_contracts/many-match.ixe"),
  include_bytes!(
    "../../kernel/tests/fixtures/input_contracts/linear-match.ixe"
  ),
  include_bytes!(
    "../../kernel/tests/fixtures/input_contracts/uses-mismatch.ixe"
  ),
  include_bytes!(
    "../../kernel/tests/fixtures/input_contracts/ownership-mismatch.ixe"
  ),
  include_bytes!(
    "../../kernel/tests/fixtures/input_contracts/locality-mismatch.ixe"
  ),
  include_bytes!(
    "../../kernel/tests/fixtures/input_contracts/result-only-unique.ixe"
  ),
];

fn binding(bytes: &[u8]) -> RoleBinding {
  RoleBinding { address: Address::hash(bytes), bytes: Arc::from(bytes) }
}

fn canonical_binding(version: u8) -> RoleBinding {
  binding(
    &RoleTable { version, bound: vec![], evidence: vec![] }.to_bytes().unwrap(),
  )
}

fn encode(env: &Env) -> Vec<u8> {
  let mut bytes = Vec::new();
  env.put(&mut bytes).unwrap();
  bytes
}

struct TempFile(PathBuf);
impl TempFile {
  fn new(bytes: &[u8]) -> Self {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let path = std::env::temp_dir().join(format!(
      "ix-binding-{}-{}.ixe",
      std::process::id(),
      NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let mut file = std::fs::OpenOptions::new()
      .write(true)
      .create_new(true)
      .open(&path)
      .unwrap();
    std::io::Write::write_all(&mut file, bytes).unwrap();
    Self(path)
  }
}
impl Drop for TempFile {
  fn drop(&mut self) {
    let _ = std::fs::remove_file(&self.0);
  }
}

fn all_readers_reject(bytes: &[u8]) {
  let mut input = bytes;
  assert!(Env::get(&mut input).is_err());
  input = bytes;
  assert!(Env::get_demoted_named(&mut input).is_err());
  input = bytes;
  assert!(Env::get_anon(&mut input).is_err());
  assert!(Env::parse_lazy_index(bytes).is_err());
  let file = TempFile::new(bytes);
  assert!(Env::get_anon_mmap(&file.0).is_err());
}

#[test]
fn unbound_fixtures_remain_exact_and_bound_layout_is_independent() {
  for original in INPUTS {
    let mut input = original;
    let mut env = Env::get(&mut input).unwrap();
    assert_eq!(original.len(), 122);
    assert_eq!(env.role_binding, None);
    assert_eq!(encode(&env), original);
    assert_eq!(env.envelope_version(), 4);
    let section = canonical_binding(2);
    assert_eq!(section.bytes.as_ref(), &[0xe8, 0x03, 2, 0, 0]);
    env.role_binding = Some(section.clone());

    // Independent v5 assembly: the legacy empty main/assumptions header is
    // 35 bytes; the binding follows it, then the existing six sections
    // remain exact, with nothing after section 6.
    let mut expected = original[..35].to_vec();
    expected[0] = 0xe5;
    expected.extend_from_slice(section.address.as_bytes());
    expected.push(5);
    expected.extend_from_slice(section.bytes.as_ref());
    expected.extend_from_slice(&original[35..]);
    let bytes = encode(&env);
    assert_eq!(bytes, expected);
    let (header, blobs, consts, hints, names, named, comms) =
      env.serialized_size_breakdown().unwrap();
    assert_eq!(
      header + blobs + consts + hints + names + named + comms,
      bytes.len()
    );
    let file = TempFile::new(&[]);
    assert_eq!(
      usize::try_from(env.put_file(&file.0).unwrap()).unwrap(),
      bytes.len()
    );
    assert_eq!(std::fs::read(&file.0).unwrap(), bytes);

    let full = Env::get(&mut bytes.as_slice()).unwrap();
    let demoted = Env::get_demoted_named(&mut bytes.as_slice()).unwrap();
    let anon = Env::get_anon(&mut bytes.as_slice()).unwrap();
    let mmap = Env::get_anon_mmap(&file.0).unwrap();
    let index = Env::parse_lazy_index(&bytes).unwrap();
    let lazy = Env::from_lazy_index(&index, &bytes).unwrap();
    for loaded in [&full, &demoted, &anon, &mmap, &lazy] {
      assert_eq!(loaded.role_binding, env.role_binding);
      assert_eq!(loaded.consts.len(), env.consts.len());
    }
    assert_eq!(encode(&full), bytes);
    assert_eq!(index.role_binding, env.role_binding);
  }
}

/// The role-bound envelope ends after section 6: the full and lazy readers
/// reject any trailing bytes. A tag-5 envelope without a binding header and
/// the tags after 5 are rejected on every reader path.
#[test]
fn v5_ends_after_comms_and_other_tags_are_unsupported() {
  let mut input = INPUTS[0];
  let mut env = Env::get(&mut input).unwrap();
  env.role_binding = Some(canonical_binding(2));
  let bytes = encode(&env);
  assert_eq!(bytes[0], 0xe5);
  for tail in [&[0u8][..], &[0, 0][..]] {
    let mut trailing = bytes.clone();
    trailing.extend_from_slice(tail);
    for error in [
      Env::get(&mut trailing.as_slice()).unwrap_err(),
      Env::get_demoted_named(&mut trailing.as_slice()).unwrap_err(),
      Env::parse_lazy_index(&trailing).unwrap_err(),
    ] {
      assert!(error.contains("trailing bytes"), "{error}");
    }
  }
  let mut unbound = INPUTS[0].to_vec();
  unbound[0] = 0xe5;
  all_readers_reject(&unbound);
  for tag in [0xe6, 0xe7] {
    let mut other = bytes.clone();
    other[0] = tag;
    all_readers_reject(&other);
    let error = Env::get(&mut other.as_slice()).unwrap_err();
    assert!(error.contains("unsupported .ixe envelope version"), "{error}");
  }
}

#[test]
fn framing_hash_and_presence_are_checked_on_every_header_path() {
  let mut env = Env::new();
  env.role_binding = Some(canonical_binding(2));
  let bytes = encode(&env);
  all_readers_reject(&bytes[..35]);
  all_readers_reject(&bytes[..68]);
  let mut corrupt = bytes.clone();
  corrupt[35] ^= 1;
  all_readers_reject(&corrupt);
  let mut oversized = bytes[..67].to_vec();
  TagN::put(0, 0, u64::MAX, &mut oversized);
  oversized.extend_from_slice(&bytes[68..]);
  all_readers_reject(&oversized);

  env.role_binding.as_mut().unwrap().address = Address::hash(b"wrong");
  let mut output = vec![42];
  assert!(env.put(&mut output).is_err());
  assert_eq!(output, [42]);
  let file = TempFile::new(b"retained");
  assert!(env.put_file(&file.0).is_err());
  assert_eq!(std::fs::read(&file.0).unwrap(), b"retained");

  // Opaque payloads are not silently normalized or downgraded. Admission
  // subsequently applies the existing canonical role-table/semantic checks.
  for payload in [&[][..], &[0xe8, 0x03, 2, 0, 0, 0][..]] {
    env.role_binding = Some(binding(payload));
    let encoded = encode(&env);
    assert_eq!(encoded[0], 0xe5);
    let loaded = Env::get(&mut encoded.as_slice()).unwrap();
    assert_eq!(loaded.role_binding, env.role_binding);
    assert!(RoleTable::from_bytes(payload).is_err());
  }
}

#[test]
fn pruning_and_anonymous_diff_retain_exact_binding_identity() {
  let mut input = INPUTS[0];
  let mut env = Env::get(&mut input).unwrap();
  env.role_binding = Some(canonical_binding(2));
  let root = env.consts.iter().next().unwrap().key().clone();
  let bytes = encode(&env);
  let (index, names) = Env::parse_lazy_index_with_names(&bytes).unwrap();
  let lazy = Env::from_lazy_index(&index, &bytes).unwrap();
  let assumed = FxHashSet::default();
  for pruned in [
    env.prune_to_closure(&root, &assumed).unwrap(),
    env.prune_to_closure_anon(&root, &assumed).unwrap(),
    lazy
      .prune_to_closure_streaming(&index, &bytes, &names, &root, &assumed)
      .unwrap(),
  ] {
    assert_eq!(pruned.role_binding, env.role_binding);
    assert_eq!(pruned.consts.len(), 1);
    assert_eq!(
      Env::get(&mut encode(&pruned).as_slice()).unwrap().role_binding,
      env.role_binding
    );
  }
  let mut other = env.clone();
  other.role_binding = Some(canonical_binding(3));
  for meta in [false, true] {
    let d = diff_envs(&env, &other, meta).unwrap();
    assert!(!d.is_empty());
    assert!(d.role_binding_changed.is_some());
    assert!(d.consts_only_a.is_empty() && d.consts_only_b.is_empty());
  }
  other.role_binding.as_mut().unwrap().address =
    env.role_binding.as_ref().unwrap().address.clone();
  assert!(
    diff_envs(&env, &other, false).unwrap().role_binding_changed.is_some()
  );
  other.role_binding = None;
  assert!(
    diff_envs(&env, &other, false).unwrap().role_binding_changed.is_some()
  );
}
