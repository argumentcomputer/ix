import Aiur.Modules.Frontend

/-! The native BLAKE3 KZG challenger: hash state || observations, reduce the
first 64 XOF bytes little-endian into Fr, retain the next 32 as the new state,
and clear observations. Observations are stored reversed for linear append. -/
namespace MultiStark.Source

def kzgTranscript : Aiur.Modules.Program Nat := aiur⟦
module KzgTranscript {
  type Transcript = &([UInt32::U32; 8], Bytes::Stream);

  fn reverse_onto(input: Bytes::Stream, tail: Bytes::Stream) -> Bytes::Stream {
    match *input {
      Lists::Node::Nil => tail,
      Lists::Node::Cons(byte, rest) => reverse_onto(rest, &(Lists::Node::Cons(byte, tail))),
    }
  }

  fn start(seed: Bytes::Stream) -> Transcript {
    &([UInt32::ZERO;8], reverse_onto(seed, &(Lists::Node::Nil)))
  }

  fn observe_bytes(transcript: Transcript, bytes: Bytes::Stream) -> Transcript {
    let (state, reverse) = *transcript;
    &(state, reverse_onto(bytes, reverse))
  }

  fn observe_field(transcript: Transcript, value: Field) -> Transcript {
    observe_bytes(transcript, KzgIO::prepend32(KzgIO::scalar_bytes(value), &(Lists::Node::Nil)))
  }

  fn observe_u64(transcript: Transcript, value: Field) -> Transcript {
    observe_bytes(transcript, KzgIO::prepend8(UInt64::from_field(value), &(Lists::Node::Nil)))
  }

  fn observe_fields(transcript: Transcript, values: Lists::List<Field>) -> Transcript {
    match *values {
      Lists::Node::Nil => transcript,
      Lists::Node::Cons(value, rest) => observe_fields(observe_field(transcript, value), rest),
    }
  }

  fn observe_u64s(transcript: Transcript, values: Lists::List<Field>) -> Transcript {
    match *values {
      Lists::Node::Nil => transcript,
      Lists::Node::Cons(value, rest) => observe_u64s(observe_u64(transcript, value), rest),
    }
  }

  fn observe_claim_rows(transcript: Transcript, claims: Lists::List<Lists::List<Field>>) -> Transcript {
    match *claims {
      Lists::Node::Nil => transcript,
      Lists::Node::Cons(claim, rest) => {
        let transcript = observe_field(transcript, Lists::length(claim));
        observe_claim_rows(observe_fields(transcript, claim), rest)
      },
    }
  }

  fn observe_claims(transcript: Transcript, claims: Lists::List<Lists::List<Field>>) -> Transcript {
    observe_claim_rows(observe_field(transcript, Lists::length(claims)), claims)
  }

  fn observe_commitment(transcript: Transcript, commitment: Lists::List<Lists::List<BN254G1::Point>>) -> Transcript {
    observe_bytes(transcript, KzgIO::fields_to_bytes(BN254G1::commitment_bytes(commitment)))
  }

  fn reduce64(wide: [UInt32::U32;16]) -> Field {
    let value = 0;
    let value = 4294967296 * value + Blake3::pack_word(wide[15]);
    let value = 4294967296 * value + Blake3::pack_word(wide[14]);
    let value = 4294967296 * value + Blake3::pack_word(wide[13]);
    let value = 4294967296 * value + Blake3::pack_word(wide[12]);
    let value = 4294967296 * value + Blake3::pack_word(wide[11]);
    let value = 4294967296 * value + Blake3::pack_word(wide[10]);
    let value = 4294967296 * value + Blake3::pack_word(wide[9]);
    let value = 4294967296 * value + Blake3::pack_word(wide[8]);
    let value = 4294967296 * value + Blake3::pack_word(wide[7]);
    let value = 4294967296 * value + Blake3::pack_word(wide[6]);
    let value = 4294967296 * value + Blake3::pack_word(wide[5]);
    let value = 4294967296 * value + Blake3::pack_word(wide[4]);
    let value = 4294967296 * value + Blake3::pack_word(wide[3]);
    let value = 4294967296 * value + Blake3::pack_word(wide[2]);
    let value = 4294967296 * value + Blake3::pack_word(wide[1]);
    let value = 4294967296 * value + Blake3::pack_word(wide[0]);
    value
  }

  fn derive(bytes: Bytes::Stream) -> Field {
    let (wide,_state)=KzgBlake3::xof96(bytes); reduce64(wide)
  }

  fn sample(transcript: Transcript) -> (Field, Transcript) {
    let (state, reverse) = *transcript;
    let bytes = KzgIO::prepend32(Blake3::digest_bytes(state), reverse_onto(reverse, &(Lists::Node::Nil)));
    let (wide, next) = KzgBlake3::xof96(bytes);
    let value = reduce64(wide);
    (value, &(next, &(Lists::Node::Nil)))
  }
}
⟧

end MultiStark.Source
