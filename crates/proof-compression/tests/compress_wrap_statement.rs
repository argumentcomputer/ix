#![cfg(feature = "plonk")]

use aiur::{artifact::Package, trace::stark::Parameters};
use ix_proof_compression::pipeline;
use multi_stark::{
  expr::Expr,
  lookup::Lookup,
  system::{CircuitInputs, System},
  types::{GoldilocksBlake3Config, Val},
};
use p3_field::PrimeCharacteristicRing;
use stark_verifier::compress_wrap::{Statement, Wrapper};

// The bundled recursive key supplies a valid final-schema shape. These tests
// compare statement specialization only; they do not derive a wrapper's
// recursive compression key or claim equivalence between proof systems.
const SCHEMA_FIXTURE: &[u8] =
  include_bytes!("../verifying-keys/0.3/recursive-vk.bin");

fn root_key(scale: u64) -> Vec<u8> {
  let parameters = Parameters::DEFAULT;
  let cp = parameters.commitment();
  let fp = parameters.fri();
  let one = Expr::constant(Val::ONE);
  let relation = Expr::main(0) * Expr::main(0) - Expr::main(1);
  let mut message = vec![one.clone(), Expr::constant(Val::ZERO)];
  message.extend([Expr::main(0), Expr::main(1)]);
  message.extend(std::iter::repeat_n(Expr::constant(Val::ZERO), 14));
  let (system, _) = System::new(
    GoldilocksBlake3Config::new(cp, fp),
    vec![CircuitInputs {
      main_width: 2,
      constraints: vec![relation * Expr::constant(Val::from_u64(scale))],
      lookups: vec![Lookup::pull(one, message)],
      ..Default::default()
    }],
  );
  stark_key::to_bytes(&system, cp, fp)
}

fn statements() -> [Statement; 3] {
  let first = root_key(1);
  let second = root_key(2);
  assert_ne!(first, second);
  let mut claims = vec![vec![Val::ZERO; 18]];
  claims[0][0] = Val::ONE;
  claims[0][2] = Val::from_u64(3);
  claims[0][3] = Val::from_u64(9);
  let first_key = *blake3::hash(&first).as_bytes();
  let a = Statement::new(first_key, &claims);
  let b = Statement::new(*blake3::hash(&second).as_bytes(), &claims);
  claims[0][17] = Val::ONE;
  let c = Statement::new(first_key, &claims);
  [a, b, c]
}

fn compare_schemas(
  statements: &[Statement; 3],
  claims: [Vec<Val>; 3],
) -> Result<(), Box<dyn std::error::Error>> {
  let encoded = claims.map(|row| stark_verifier::claims_bytes(&[row]));
  let words: Vec<_> = statements
    .iter()
    .zip(&encoded)
    .map(|(statement, claim)| {
      pipeline::check_claim(&statement.preimage(), claim)
    })
    .collect::<Result<_, _>>()?;
  let prefix: [u64; 10] = words[0][..10].try_into()?;
  assert_eq!(&prefix[2..], &[0; 8]);
  for index in 1..statements.len() {
    assert_ne!(statements[0].preimage(), statements[index].preimage());
    assert_eq!(words[0][..10], words[index][..10]);
    assert_ne!(words[0][10..], words[index][10..]);
    assert!(
      pipeline::check_claim(&statements[index].preimage(), &encoded[0])
        .is_err()
    );
  }
  let expected = pipeline::final_schema(SCHEMA_FIXTURE, &prefix)?;
  for word in &words[1..] {
    assert_eq!(
      expected,
      pipeline::final_schema(SCHEMA_FIXTURE, &word[..10].try_into()?)?
    );
  }
  let mut other_prefix = prefix;
  other_prefix[2] = 1;
  assert_ne!(expected, pipeline::final_schema(SCHEMA_FIXTURE, &other_prefix)?);
  Ok(())
}

#[test]
fn root_keys_and_claims_change_the_digest_without_respecializing_final_schema()
-> Result<(), Box<dyn std::error::Error>> {
  let statements = statements();
  let claims = statements.each_ref().map(|statement| {
    [Val::ONE, Val::from_u64(7)]
      .into_iter()
      .chain(statement.arguments().map(Val::from_u64))
      .collect()
  });
  compare_schemas(&statements, claims)
}

#[test]
#[ignore = "requires IX_COMPRESS_WRAP_ARTIFACT naming the trusted exported CompressWrap package; builds its backend metadata, without executing or proving"]
fn exported_wrapper_claims_keep_the_final_schema_independent_of_root_identity()
-> Result<(), Box<dyn std::error::Error>> {
  let path = std::env::var_os("IX_COMPRESS_WRAP_ARTIFACT")
    .ok_or("set IX_COMPRESS_WRAP_ARTIFACT to the trusted package")?;
  let (package, _) = Package::load(std::path::Path::new(&path))?;
  let wrapper = Wrapper::new(package, Parameters::DEFAULT, None)?;
  let statements = statements();
  let claims = [
    wrapper.claim_for(&statements[0])?,
    wrapper.claim_for(&statements[1])?,
    wrapper.claim_for(&statements[2])?,
  ];
  compare_schemas(&statements, claims)
}
