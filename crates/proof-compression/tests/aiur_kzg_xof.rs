use aiur::{
  artifact::WidePackage, bytecode::Type, field::FieldBackend,
  hints::HintChannels, maps::MapOverrides,
};
use ix_proof_compression::{aiur_backend::Bn254, kzg::Scalar};
use std::sync::Arc;

#[test]
fn compiled_blake3_xof_matches_native_block_and_chunk_boundaries() {
  let package = WidePackage::decode(include_bytes!(
    "../../aiur/tests/fixtures/kzg-xof.ixa"
  ))
  .unwrap();
  let program = package.program.check_with(Bn254).unwrap();
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(&program, &mut maps).unwrap();
  for length in
    [0usize, 1, 63, 64, 65, 1023, 1024, 1025, 2048, 3072, 4097, 5121, 6145]
  {
    let input: Arc<[u8]> = (0..length)
      .map(|i| u8::try_from((i * 73 + 19) % 256).unwrap())
      .collect::<Vec<_>>()
      .into();
    let mut reader = blake3::Hasher::new().update(&input).finalize_xof();
    let mut expected = [0u8; 96];
    reader.fill(&mut expected);
    let expected: Vec<Scalar> = expected
      .as_chunks::<4>()
      .0
      .iter()
      .map(|bytes| Bn254.from_u64(u64::from(u32::from_le_bytes(*bytes))))
      .collect();
    let mut channels = HintChannels::new();
    aiur::library::u32::register(&mut channels, Bn254).unwrap();
    aiur::library::u64::register(&mut channels, Bn254).unwrap();
    channels
      .insert_fixed::<1, 1>(
        "kzg.test.byte",
        Type::Field,
        Type::Field,
        move |[offset]| {
          let offset = usize::try_from(Bn254.try_to_u64(offset)?)
            .map_err(|error| error.to_string())?;
          Ok([Bn254.from_u64(u64::from(
            *input.get(offset).ok_or("XOF test byte out of bounds")?,
          ))])
        },
      )
      .unwrap();
    let executor = program
      .prepare_hint_channels(&[], &channels)
      .unwrap()
      .with_map_overrides(&maps)
      .unwrap();
    let record = executor
      .execute(
        "KzgXofTest::run",
        vec![Bn254.from_u64(u64::try_from(length).unwrap())],
      )
      .unwrap();
    assert_eq!(record.output, expected, "XOF input length {length}");
  }
}
