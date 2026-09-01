module
public import Ix.Aiur.Meta

/-!
# Transcript interface: the Blake3 byte challenger

The Fiat-Shamir transcript both multi-stark configs use
(`SerializingChallenger64<Val, HashChallenger<u8, Blake3, 32>>` in Rust;
`Transcript` in pcs-traits), threaded as a pair `(input, output)` of byte
lists. This is the one transcript implementation (blake3 is fixed by
design); it lives apart from the verifier core so the core refers only to
the transcript's NAMES — `ch_sample8`/`ch_sample_field`/`ch_sample_ext`/
`ch_sample_bits` (draws, with rejection sampling of field elements),
`ch_observe_val`/`snoc_b8` (appends), the prepend-built segments
(`b8_onto`, `limbs_onto`, `log_degrees_onto`, `accs_onto`), `rev_onto`,
and `seed_tag_onto` (the domain-separation tag). Commitment serialization
belongs to the PCS (`commitment_onto` in its module): the transcript only
knows bytes. Field elements cross through the field interface
(`val_from_bytes` on draws, `val_to_bytes` on observes).
-/

public section

namespace MultiStark

def transcriptBlake3 := ⟦
  -- ==========================================================================
  -- Fiat-Shamir challenger: `SerializingChallenger64<Val, HashChallenger<u8,
  -- Blake3, 32>>`. The inner byte challenger keeps an `input` buffer; a
  -- `sample` with empty `output` flushes (`input := output := blake3(input)`)
  -- and pops bytes from the END of the hash output. The outer layer serializes
  -- field elements as 8 little-endian bytes and samples field elements as
  -- 8-byte little-endian u64s.
  --
  -- The challenger is threaded as a pair `(input, output)` of byte lists, where
  -- `output` is held in pop order (front = next byte = hash byte 31, 30, …).
  -- ==========================================================================

  -- Cons 8 bytes (LSB-first) of `b` onto `tail` (one byte list segment).
  fn b8_onto(b: [U8; 8], tail: ByteStream) -> ByteStream {
    store(ListNode.Cons(b[0], store(ListNode.Cons(b[1], store(ListNode.Cons(b[2],
    store(ListNode.Cons(b[3], store(ListNode.Cons(b[4], store(ListNode.Cons(b[5],
    store(ListNode.Cons(b[6], store(ListNode.Cons(b[7], tail))))))))))))))))
  }



  -- Observe `log_degrees`: each is a `Val::from_u8`, i.e. 8 LE bytes `[ld,0,…]`.
  fn log_degrees_onto(lds: List‹U8›, tail: ByteStream) -> ByteStream {
    match load(lds) {
      ListNode.Nil => tail,
      ListNode.Cons(ld, rest) =>
        b8_onto([ld, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], log_degrees_onto(rest, tail)),
    }
  }

  -- Reverse `l` onto `acc` (used to put a hash output into pop order).
  fn rev_onto(l: ByteStream, acc: ByteStream) -> ByteStream {
    match load(l) {
      ListNode.Nil => acc,
      ListNode.Cons(b, rest) => rev_onto(rest, store(ListNode.Cons(b, acc))),
    }
  }

  -- Sample 8 bytes = `sample_array()` (for one base-field element, LE).
  -- The output buffer always holds a multiple of 8 bytes at a draw boundary
  -- (a flush refills 32, every draw takes 8, an observe clears to Nil), so
  -- the empty check happens at most once per draw: flush, then pop 8. The
  -- two arms' pops share columns (branch aux/lookups combine by max), which
  -- is what makes this strictly narrower than a per-byte sampler circuit.
  fn ch_sample8(input: ByteStream, output: ByteStream) -> ([U8; 8], ByteStream, ByteStream) {
    match load(output) {
      ListNode.Nil =>
        -- `HashChallenger<u8, Blake3, 32>` flush: hash the `input` buffer with
        -- blake3; `b3_flatten_onto` (Pcs.lean) gives the 32 output bytes, popped
        -- from the END (rev), with the `input := output := hash` update.
        let h = @blake3(input);
        let fwd = @b3_flatten_onto(h, store(ListNode.Nil));
        let rev = rev_onto(fwd, store(ListNode.Nil));
        let &ListNode.Cons(b0, r1) = rev;
        let &ListNode.Cons(b1, r2) = r1;
        let &ListNode.Cons(b2, r3) = r2;
        let &ListNode.Cons(b3, r4) = r3;
        let &ListNode.Cons(b4, r5) = r4;
        let &ListNode.Cons(b5, r6) = r5;
        let &ListNode.Cons(b6, r7) = r6;
        let &ListNode.Cons(b7, r8) = r7;
        ([b0, b1, b2, b3, b4, b5, b6, b7], fwd, r8),
      ListNode.Cons(b0, r1) =>
        let &ListNode.Cons(b1, r2) = r1;
        let &ListNode.Cons(b2, r3) = r2;
        let &ListNode.Cons(b3, r4) = r3;
        let &ListNode.Cons(b4, r5) = r4;
        let &ListNode.Cons(b5, r6) = r5;
        let &ListNode.Cons(b6, r7) = r6;
        let &ListNode.Cons(b7, r8) = r7;
        ([b0, b1, b2, b3, b4, b5, b6, b7], input, r8),
    }
  }

  -- Sample one base-field element with REJECTION SAMPLING, mirroring
  -- `SerializingChallenger64::sample`'s inner loop: draw 8 bytes as a LE u64
  -- (the `log2_ceil(p) = 64` mask is a no-op for Goldilocks); if the raw value
  -- is ≥ p (probability ≈ 2⁻³²), DISCARD it and draw the next 8 bytes — a
  -- rejected draw consumes challenger bytes, shifting every later sample,
  -- exactly as in the reference. `bytes_lt_modulus` decides `raw < p`; the accepted
  -- limb is canonical (< p) by construction.
  fn ch_sample_field(input: ByteStream, output: ByteStream) -> ([U8; 8], ByteStream, ByteStream) {
    let (raw, i1, o1) = ch_sample8(input, output);
    match @bytes_lt_modulus(raw) {
      1 => (raw, i1, o1),
      _ => ch_sample_field(i1, o1),
    }
  }

  -- Sample a degree-2 extension element: two base samples (`from_basis_*`),
  -- each rejection-sampled, returning their 8-byte LE limbs (canonical, but
  -- also re-observable as raw bytes) and the threaded challenger.
  fn ch_sample_ext(input: ByteStream, output: ByteStream) -> ([U8; 8], [U8; 8], ByteStream, ByteStream) {
    let (c0, i0, o0) = ch_sample_field(input, output);
    let (c1, i1, o1) = ch_sample_field(i0, o0);
    (c0, c1, i1, o1)
  }

  -- Prepend the 8 elements of `d` onto `tail` (generic list helper).
  fn cons8(d: [G; 8], tail: List‹G›) -> List‹G› {
    store(ListNode.Cons(d[0], store(ListNode.Cons(d[1], store(ListNode.Cons(d[2],
    store(ListNode.Cons(d[3], store(ListNode.Cons(d[4], store(ListNode.Cons(d[5],
    store(ListNode.Cons(d[6], store(ListNode.Cons(d[7], tail))))))))))))))))
  }

  -- `sample_bits(n)` (FRI query index). `SerializingChallenger64::sample_bits`
  -- reads one 8-byte sample as a little-endian u64 and masks the low `n` bits.
  -- We return the low `n` bits as a list (LSB first = the leaf→root Merkle/FRI
  -- path). Only the low 4 bytes are decomposed: 32 bits bound every
  -- log-height (Goldilocks two-adicity is 32), and `take_bits` aborts on the
  -- Nil match if `n` ever exceeded 32 — exactly as it did at 64 with the old
  -- full decomposition. The full 8 bytes are still drawn (Fiat-Shamir
  -- alignment with the reference challenger).
  fn take_bits(bits: List‹G›, n: G) -> List‹G› {
    match n {
      0 => store(ListNode.Nil),
      _ =>
        let &ListNode.Cons(b, rest) = bits;
        store(ListNode.Cons(b, take_bits(rest, n - 1))),
    }
  }
  fn ch_sample_bits(input: ByteStream, output: ByteStream, n: G)
      -> (List‹G›, ByteStream, ByteStream) {
    let (bytes, i1, o1) = ch_sample8(input, output);
    let bits =
      cons8(u8_bit_decomposition(bytes[0]),
      cons8(u8_bit_decomposition(bytes[1]),
      cons8(u8_bit_decomposition(bytes[2]),
      cons8(u8_bit_decomposition(bytes[3]), store(ListNode.Nil)))));
    (take_bits(bits, n), i1, o1)
  }

  -- Append (observe) 8 little-endian bytes of `b` at the END of the challenger
  -- input buffer. The transcript is held front-to-back (front = first observed =
  -- first hashed, matching `blake3`'s absorption order), so an observation
  -- appends — `b8_onto` PREPENDS, hence the `list_concat`.
  fn snoc_b8(input: ByteStream, b: [U8; 8]) -> ByteStream {
    list_concat(input, b8_onto(b, store(ListNode.Nil)))
  }
  -- The intermediate accumulators as a prepend-built stream, in order — each
  -- an `observe_algebra_element`: two canonical 8-LE-byte limbs. (`read_ext`
  -- reduced the limbs mod p, matching `as_canonical_u64` serialization.)
  -- Prepend-composed so observing all of them is one `list_concat`, not a
  -- per-element re-walk of the input buffer.
  fn accs_onto(accs: List‹Ext›, tail: ByteStream) -> ByteStream {
    match load(accs) {
      ListNode.Nil => tail,
      ListNode.Cons(e, rest) => b8_onto(@val_to_bytes(e[0]), b8_onto(@val_to_bytes(e[1]), accs_onto(rest, tail))),
    }
  }

  -- ==========================================================================
  -- PCS challenger continuation (Phase 4): the post-ζ transcript that
  -- `two_adic_pcs::verify` + `verify_fri` replay. Unlike `fiat_shamir` — where
  -- every sample is followed by an observe (so each sample re-flushes from an
  -- empty `output`) — the PCS phase has *consecutive* samples with no observe
  -- between (the PCS batch challenge α, then immediately the FRI batch challenge
  -- α). So both challenger buffers must be threaded: `output` carries the
  -- leftover hash bytes from one sample into the next instead of re-flushing.
  -- ==========================================================================

  -- Observe one `Val` (8 LE bytes): append to `input`, CLEAR `output` (any
  -- leftover sampled bytes are discarded), per `HashChallenger::observe`.
  fn ch_observe_val(input: ByteStream, v: U64) -> (ByteStream, ByteStream) {
    (snoc_b8(input, v), store(ListNode.Nil))
  }

  -- Sample a degree-2 extension element, threading BOTH challenger buffers so a
  -- following consecutive sample continues from the same hash `output` stream
  -- (no re-flush). Limbs are rejection-sampled (`ch_sample_field`), so they are
  -- canonical; the `gl_reduce` is a no-op kept for type/intent clarity.
  fn pcs_sample_ext(input: ByteStream, output: ByteStream)
      -> (Ext, ByteStream, ByteStream) {
    let (c0, c1, i1, o1) = ch_sample_ext(input, output);
    ([@val_from_bytes(c0), @val_from_bytes(c1)], i1, o1)
  }

  -- `b"multi-stark/v0"` — the domain-separation tag the challenger seed
  -- starts with (`GoldilocksBlake3Config::new`).
  fn seed_tag_onto(tail: ByteStream) -> ByteStream {
    store(ListNode.Cons(109u8, store(ListNode.Cons(117u8, store(ListNode.Cons(108u8,
    store(ListNode.Cons(116u8, store(ListNode.Cons(105u8, store(ListNode.Cons(45u8,
    store(ListNode.Cons(115u8, store(ListNode.Cons(116u8, store(ListNode.Cons(97u8,
    store(ListNode.Cons(114u8, store(ListNode.Cons(107u8, store(ListNode.Cons(47u8,
    store(ListNode.Cons(118u8, store(ListNode.Cons(48u8,
    tail))))))))))))))))))))))))))))
  }
  -- Raw u64 wire words (protocol parameters + system shape), each as its 8 LE
  -- bytes, in order.
  fn limbs_onto(ls: List‹U64›, tail: ByteStream) -> ByteStream {
    match load(ls) {
      ListNode.Nil => tail,
      ListNode.Cons(l, rest) => b8_onto(l, limbs_onto(rest, tail)),
    }
  }
⟧

end MultiStark

end
