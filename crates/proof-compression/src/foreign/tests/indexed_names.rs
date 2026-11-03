use super::*;

#[test]
fn indexed_names_preserve_owned_names_and_lazy_census() {
  struct UnusedName;
  // The conversion must never run; counting builders keep names lazy.
  #[allow(clippy::fallible_impl_from)]
  impl From<UnusedName> for String {
    fn from(_: UnusedName) -> Self {
      panic!("counting must not materialize an input name")
    }
  }
  let mut census = CircuitBuilder::<Scalar>::counting();
  census.input(UnusedName);
  census.input_indexed("goldilocks", usize::MAX);
  assert_eq!(census.stats().inputs, 2);
  for name in ["", "input α[17]"] {
    let mut builder = CircuitBuilder::<Scalar>::new();
    builder.input(name);
    assert_eq!(
      builder.finish().witness().generate().err(),
      Some(WitnessError::MissingInput { name: name.into() })
    );
  }
  let mut builder = CircuitBuilder::<Scalar>::new();
  builder.input_indexed("goldilocks", usize::MAX);
  assert_eq!(
    builder.finish().witness().generate().err(),
    Some(WitnessError::MissingInput {
      name: format!("goldilocks[{}]", usize::MAX)
    })
  );
}
