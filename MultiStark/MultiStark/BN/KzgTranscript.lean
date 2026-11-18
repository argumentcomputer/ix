import Aiur.Modules.Frontend

/-! The native BLAKE3 KZG challenger: hash state || observations, reduce the
first 64 XOF bytes little-endian into Fr, retain the next 32 as the new state,
and clear observations. The state and observations are kept as one byte
string in little-endian words, stored reversed for linear append. -/
namespace MultiStark.Source

def kzgTranscript : Aiur.Modules.Program Nat := aiur⟦
module KzgTranscript {
  type U8 = UInt8::U8;
  type U32 = UInt32::U32;
  -- Hashed bytes so far: whole words in reverse order, their count, and
  -- 0..3 trailing bytes (unused tail bytes are zero).
  type Transcript = &(KzgIO::Words, Field, Field, [U8; 3]);

  inline fn reset(state: [U32; 8]) -> Transcript {
    let words = &(Lists::Node::Cons(state[0], &(Lists::Node::Nil)));
    let words = &(Lists::Node::Cons(state[1], words));
    let words = &(Lists::Node::Cons(state[2], words));
    let words = &(Lists::Node::Cons(state[3], words));
    let words = &(Lists::Node::Cons(state[4], words));
    let words = &(Lists::Node::Cons(state[5], words));
    let words = &(Lists::Node::Cons(state[6], words));
    let words = &(Lists::Node::Cons(state[7], words));
    &(words, 8, 0, [UInt8::BYTE_0; 3])
  }

  fn push_byte(transcript: Transcript, byte: U8) -> Transcript {
    let (words, count, length, tail) = *transcript;
    match length {
      0 => &(words, count, 1, [byte, UInt8::BYTE_0, UInt8::BYTE_0]),
      1 => &(words, count, 2, [tail[0], byte, UInt8::BYTE_0]),
      2 => &(words, count, 3, [tail[0], tail[1], byte]),
      3 => &(&(Lists::Node::Cons(UInt32::from_bytes([tail[0], tail[1], tail[2], byte]), words)), count + 1, 0, [UInt8::BYTE_0; 3]),
    }
  }

  fn push_word(transcript: Transcript, word: U32) -> Transcript {
    let (words, count, length, tail) = *transcript;
    let w = UInt32::to_bytes(word);
    match length {
      0 => &(&(Lists::Node::Cons(word, words)), count + 1, 0, tail),
      1 => &(&(Lists::Node::Cons(UInt32::from_bytes([tail[0], w[0], w[1], w[2]]), words)), count + 1, 1, [w[3], UInt8::BYTE_0, UInt8::BYTE_0]),
      2 => &(&(Lists::Node::Cons(UInt32::from_bytes([tail[0], tail[1], w[0], w[1]]), words)), count + 1, 2, [w[2], w[3], UInt8::BYTE_0]),
      3 => &(&(Lists::Node::Cons(UInt32::from_bytes([tail[0], tail[1], tail[2], w[0]]), words)), count + 1, 3, [w[1], w[2], w[3]]),
    }
  }

  inline fn cons8(a: [U32; 8], words: KzgIO::Words) -> KzgIO::Words {
    let words = &(Lists::Node::Cons(a[0], words));
    let words = &(Lists::Node::Cons(a[1], words));
    let words = &(Lists::Node::Cons(a[2], words));
    let words = &(Lists::Node::Cons(a[3], words));
    let words = &(Lists::Node::Cons(a[4], words));
    let words = &(Lists::Node::Cons(a[5], words));
    let words = &(Lists::Node::Cons(a[6], words));
    &(Lists::Node::Cons(a[7], words))
  }

  fn observe32(transcript: Transcript, b: [U8; 32]) -> Transcript {
    let (words, count, length, tail) = *transcript;
    match length {
      0 => &(cons8([UInt32::from_bytes([b[0], b[1], b[2], b[3]]), UInt32::from_bytes([b[4], b[5], b[6], b[7]]), UInt32::from_bytes([b[8], b[9], b[10], b[11]]), UInt32::from_bytes([b[12], b[13], b[14], b[15]]),
          UInt32::from_bytes([b[16], b[17], b[18], b[19]]), UInt32::from_bytes([b[20], b[21], b[22], b[23]]), UInt32::from_bytes([b[24], b[25], b[26], b[27]]), UInt32::from_bytes([b[28], b[29], b[30], b[31]])], words),
        count + 8, 0, tail),
      1 => &(cons8([UInt32::from_bytes([tail[0], b[0], b[1], b[2]]), UInt32::from_bytes([b[3], b[4], b[5], b[6]]), UInt32::from_bytes([b[7], b[8], b[9], b[10]]), UInt32::from_bytes([b[11], b[12], b[13], b[14]]),
          UInt32::from_bytes([b[15], b[16], b[17], b[18]]), UInt32::from_bytes([b[19], b[20], b[21], b[22]]), UInt32::from_bytes([b[23], b[24], b[25], b[26]]), UInt32::from_bytes([b[27], b[28], b[29], b[30]])], words),
        count + 8, 1, [b[31], UInt8::BYTE_0, UInt8::BYTE_0]),
      2 => &(cons8([UInt32::from_bytes([tail[0], tail[1], b[0], b[1]]), UInt32::from_bytes([b[2], b[3], b[4], b[5]]), UInt32::from_bytes([b[6], b[7], b[8], b[9]]), UInt32::from_bytes([b[10], b[11], b[12], b[13]]),
          UInt32::from_bytes([b[14], b[15], b[16], b[17]]), UInt32::from_bytes([b[18], b[19], b[20], b[21]]), UInt32::from_bytes([b[22], b[23], b[24], b[25]]), UInt32::from_bytes([b[26], b[27], b[28], b[29]])], words),
        count + 8, 2, [b[30], b[31], UInt8::BYTE_0]),
      3 => &(cons8([UInt32::from_bytes([tail[0], tail[1], tail[2], b[0]]), UInt32::from_bytes([b[1], b[2], b[3], b[4]]), UInt32::from_bytes([b[5], b[6], b[7], b[8]]), UInt32::from_bytes([b[9], b[10], b[11], b[12]]),
          UInt32::from_bytes([b[13], b[14], b[15], b[16]]), UInt32::from_bytes([b[17], b[18], b[19], b[20]]), UInt32::from_bytes([b[21], b[22], b[23], b[24]]), UInt32::from_bytes([b[25], b[26], b[27], b[28]])], words),
        count + 8, 3, [b[29], b[30], b[31]]),
    }
  }

  fn observe_words(transcript: Transcript, words: KzgIO::Words) -> Transcript {
    match *words {
      Lists::Node::Nil => transcript,
      Lists::Node::Cons(w, rest) => observe_words(push_word(transcript, w), rest),
    }
  }

  fn observe_input(transcript: Transcript, input: KzgIO::Input) -> Transcript {
    let (words, offset) = input;
    match offset {
      0 => observe_words(transcript, words),
      _ => {
        let Lists::Node::Cons(w, rest) = *words; let w = UInt32::to_bytes(w);
        match offset {
          1 => observe_words(push_byte(push_byte(push_byte(transcript, w[1]), w[2]), w[3]), rest),
          2 => observe_words(push_byte(push_byte(transcript, w[2]), w[3]), rest),
          3 => observe_words(push_byte(transcript, w[3]), rest),
        }
      },
    }
  }

  fn observe_bytes(transcript: Transcript, bytes: Bytes::Stream) -> Transcript {
    match *bytes {
      Lists::Node::Nil => transcript,
      Lists::Node::Cons(byte, rest) => observe_bytes(push_byte(transcript, byte), rest),
    }
  }

  inline fn start(seed: KzgIO::Input) -> Transcript {
    observe_input(reset([UInt32::ZERO; 8]), seed)
  }

  fn observe_field(transcript: Transcript, value: Field) -> Transcript {
    observe32(transcript, KzgIO::scalar_bytes(value))
  }

  fn observe_u64(transcript: Transcript, value: Field) -> Transcript {
    let b = UInt64::from_field(value);
    push_word(push_word(transcript, UInt32::from_bytes([b[0], b[1], b[2], b[3]])), UInt32::from_bytes([b[4], b[5], b[6], b[7]]))
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

  inline fn observe_claims(transcript: Transcript, claims: Lists::List<Lists::List<Field>>) -> Transcript {
    observe_claim_rows(observe_field(transcript, Lists::length(claims)), claims)
  }

  inline fn observe_commitment(transcript: Transcript, commitment: Lists::List<Lists::List<BN254G1::Point>>) -> Transcript {
    observe_bytes(transcript, KzgIO::fields_to_bytes(BN254G1::commitment_bytes(commitment)))
  }

  inline fn reduce64(wide: [UInt32::U32;16]) -> Field {
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

  inline fn derive(bytes: Bytes::Stream) -> Field {
    let (wide,_state)=KzgBlake3::xof96(bytes); reduce64(wide)
  }

  fn reverse_words(input: KzgIO::Words, tail: KzgIO::Words) -> KzgIO::Words {
    match *input {
      Lists::Node::Nil => tail,
      Lists::Node::Cons(w, rest) => reverse_words(rest, &(Lists::Node::Cons(w, tail))),
    }
  }

  fn sample(transcript: Transcript) -> (Field, Transcript) {
    let (words, count, length, tail) = *transcript;
    let (wide, next) = KzgBlake3::xof96_words(reverse_words(words, &(Lists::Node::Nil)), 4 * count + length, length, tail);
    (reduce64(wide), reset(next))
  }
}
⟧

end MultiStark.Source
