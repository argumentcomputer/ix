//! Full-boundary controls for direct beta-redexes constructing canonical Eq types.
//! Expected verdicts are independent of the fixture loader and current checker.
#[test]
fn committed_direct_beta_equality_controls() {
  let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("../../Tests/Fixtures/ixon-v4/transport/beta");
  for (name, rejection) in [
    ("hiddenBad", Some("SharedToUnique")),
    ("hiddenGood", None),
    ("deadBad", None),
    ("changedInput", Some("TypeMismatch")),
    ("changedResult", Some("TypeMismatch")),
    ("matchingResult", None),
    ("dependentGood", None),
    ("aliasGood", None),
    ("proofLetBad", Some("SharedToUnique")),
    ("directProofBad", Some("SharedToUnique")),
    ("directProofGood", None),
    ("computationalBad", Some("SharedToUnique")),
    ("computationalGood", None),
  ] {
    let bytes = std::fs::read(directory.join(format!("{name}.ixe"))).unwrap();
    let mut input = bytes.as_slice();
    let env = ixon::env::Env::get(&mut input).unwrap();
    assert!(input.is_empty());
    let profile = ixon::resource::addressed::Profile::from_bytes(
      &std::fs::read(directory.join(format!("{name}.profile"))).unwrap(),
    )
    .unwrap();
    assert_eq!(
      profile.address().unwrap().hex(),
      "3a3b136bebf70228abeb5e8b6c40ce127d9f204807333b2eaaae5c4a4070497c",
      "{name}"
    );
    let result = super::super::validate(&env, &profile);
    match (rejection, result) {
      (None, Ok(_)) => {},
      (Some(expected), Err(message)) => assert!(
        message.starts_with("resource admission Some(")
          && message.ends_with(&format!(": {expected}")),
        "{name}: expected {expected}, got {message}",
      ),
      (expected, result) => {
        panic!("{name}: expected {expected:?}, got {result:?}")
      },
    }
  }
}
