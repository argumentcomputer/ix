use super::*;
use crate::{
  field::NativeField,
  library::io::{Stream, Streams},
};
use multi_stark::{
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  types::Val,
};

type F = NativeField<Val>;
const FIELD: F = NativeField::new();
const P: u64 = Val::ORDER_U64;

fn stream(channel: u64, key: &[u64], values: &[u64]) -> Stream {
  Stream { channel, key: key.to_vec(), values: values.to_vec() }
}

fn bytes<'a>(channel: u64, key: &'a [u64], payload: &'a [u8]) -> Entry<'a> {
  Entry { channel, key, payload: Payload::Bytes(payload) }
}

fn words<'a>(channel: u64, key: &'a [u64], payload: &'a [u64]) -> Entry<'a> {
  Entry { channel, key, payload: Payload::Words(payload) }
}

fn read<const N: usize>(
  advice: &impl StreamAdvice<F>,
  channel: u64,
  offset: u64,
) -> Result<[u64; N], String> {
  let mut channels = HintChannels::new();
  advice.register_read::<N>("read", N == 1, &mut channels)?;
  let function = channels.function("read").unwrap();
  let mut output = [Val::from_u64(0); N];
  function(&[Val::from_u64(channel), Val::from_u64(offset)], &mut output)?;
  Ok(output.map(|v| v.as_canonical_u64()))
}

fn all_metadata(advice: &impl StreamAdvice<F>) -> Vec<HintEntry> {
  let key = Type::Field;
  let mut entries =
    advice.metadata("info", &key, None, |_, _| true, false).unwrap();
  entries.extend(
    advice.metadata("claim", &key, Some(0), |c, _| c == 0, false).unwrap(),
  );
  entries
    .extend(advice.metadata("tag", &key, None, |c, _| c == 3, true).unwrap());
  entries
}

fn sample() -> Streams {
  Streams(vec![
    stream(2, &[7], &[1, 2, 3]),
    stream(0, &[1, 2], &[255, 0]),
    stream(2, &[8], &[]),
    stream(3, &[9], &[4]),
    stream(3, &[10], &[600]),
    stream(2, &[11], &[9, 8]),
    stream(4, &[9], &[P - 1, 0]),
    stream(3, &[12], &[5]),
  ])
}

#[test]
fn offsets_and_reads_match_reference() {
  let streams = sample();
  let reference = streams.prepare(FIELD).unwrap();
  let advice = Advice::from_streams(FIELD, &streams).unwrap();
  let offsets: Vec<_> =
    advice.streams().iter().map(|s| (s.channel, s.offset, s.len)).collect();
  assert_eq!(
    offsets,
    [
      (2, 0, 3),
      (0, 0, 2),
      (2, 3, 0),
      (3, 0, 1),
      (3, 1, 1),
      (2, 3, 2),
      (4, 0, 2),
      (3, 2, 1),
    ]
  );
  assert!(advice.is_byte_channel(0) && advice.is_byte_channel(2));
  assert!(!advice.is_byte_channel(3) && !advice.is_byte_channel(4));
  assert!(advice.is_byte_channel(1), "unused channels are empty bytes");
  for channel in 0..6 {
    for offset in 0..7 {
      assert_eq!(
        read::<1>(&advice, channel, offset),
        read::<1>(&reference, channel, offset)
      );
      assert_eq!(
        read::<2>(&advice, channel, offset),
        read::<2>(&reference, channel, offset)
      );
    }
  }
  assert_eq!(read::<1>(&advice, 3, 1), Ok([600]));
  assert_eq!(read::<2>(&advice, 4, 0), Ok([P - 1, 0]));
  assert_eq!(read::<2>(&advice, 2, 3), Ok([9, 8]));
  assert!(read::<2>(&advice, 2, 4).is_err());
  assert!(read::<1>(&advice, 300, 0).is_err());
  assert_eq!(all_metadata(&advice), all_metadata(&reference));
}

#[test]
fn byte_boundary_selects_storage() {
  let low = Streams(vec![stream(1, &[0], &[0, 255])]);
  let high = Streams(vec![stream(1, &[0], &[0, 256])]);
  let low = Advice::from_streams(FIELD, &low).unwrap();
  let high = Advice::from_streams(FIELD, &high).unwrap();
  assert!(low.is_byte_channel(1));
  assert!(!high.is_byte_channel(1));
  assert_eq!(read::<2>(&low, 1, 0), Ok([0, 255]));
  assert_eq!(read::<2>(&high, 1, 0), Ok([0, 256]));
  assert_eq!(low.retained_bytes().payload + 14, high.retained_bytes().payload);
}

#[test]
fn widening_preserves_earlier_bytes() {
  let advice = Advice::from_entries(
    FIELD,
    [bytes(5, &[0], &[1, 2]), words(5, &[1], &[1 << 40]), bytes(5, &[2], &[3])],
  )
  .unwrap();
  assert!(!advice.is_byte_channel(5));
  assert_eq!(read::<4>(&advice, 5, 0), Ok([1, 2, 1 << 40, 3]));
  assert_eq!(advice.streams()[2].offset, 3);
}

#[test]
fn typed_entries_match_adapter() {
  let streams = sample();
  let narrowed: Vec<Option<Vec<u8>>> = streams
    .0
    .iter()
    .map(|s| s.values.iter().map(|&v| u8::try_from(v).ok()).collect())
    .collect();
  let entries =
    streams.0.iter().zip(&narrowed).map(|(s, narrow)| match narrow {
      Some(payload) => bytes(s.channel, &s.key, payload),
      None => words(s.channel, &s.key, &s.values),
    });
  let typed = Advice::from_entries(FIELD, entries).unwrap();
  let adapted = Advice::from_streams(FIELD, &streams).unwrap();
  assert_eq!(typed.streams(), adapted.streams());
  assert_eq!(all_metadata(&typed), all_metadata(&adapted));
  assert_eq!(typed.retained_bytes(), adapted.retained_bytes());
}

#[test]
fn validation_matches_reference() {
  let cases = [
    (vec![stream(256, &[0], &[1])], "below 256"),
    (vec![stream(u64::MAX, &[0], &[1])], "below 256"),
    (vec![stream(0, &[P], &[1])], "noncanonical"),
    (vec![stream(0, &[0], &[P])], "noncanonical"),
    (vec![stream(0, &[0], &[u64::MAX])], "noncanonical"),
    (vec![stream(0, &[1], &[1]), stream(0, &[1], &[2])], "duplicate"),
  ];
  for (streams, message) in cases {
    let streams = Streams(streams);
    let reference = streams.prepare(FIELD).err().unwrap();
    let compact = Advice::from_streams(FIELD, &streams).err().unwrap();
    assert_eq!(reference, compact);
    assert!(compact.contains(message), "{compact}");
  }
  let distinct = Streams(vec![
    stream(0, &[1], &[1]),
    stream(1, &[1], &[2]),
    stream(0, &[1, 0], &[3]),
    stream(0, &[], &[]),
  ]);
  assert!(Advice::from_streams(FIELD, &distinct).is_ok());
  assert!(
    Advice::from_entries(FIELD, [bytes(0, &[1], &[1]), words(0, &[1], &[2])])
      .is_err()
  );
}

#[test]
fn value_hints_require_one_field() {
  let streams = Streams(vec![stream(3, &[0], &[1, 2])]);
  let advice = Advice::from_streams(FIELD, &streams).unwrap();
  let reference = streams.prepare(FIELD).unwrap();
  let compact =
    advice.metadata("tag", &Type::Field, None, |_, _| true, true).unwrap_err();
  let expected = reference
    .metadata("tag", &Type::Field, None, |_, _| true, true)
    .unwrap_err();
  assert_eq!(compact, expected);
}

#[test]
fn empty_advice() {
  let advice = Advice::from_streams(FIELD, &Streams::default()).unwrap();
  assert!(advice.streams().is_empty());
  assert_eq!(advice.retained_bytes(), AdviceBytes::default());
  assert!(read::<1>(&advice, 0, 0).is_err());
  let empty = Advice::from_entries(FIELD, [bytes(2, &[0], &[])]).unwrap();
  assert_eq!(empty.streams()[0].len, 0);
  assert!(read::<1>(&empty, 2, 0).is_err());
}
