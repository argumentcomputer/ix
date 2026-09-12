module
public import Ix.Ixby.Aiur.Fragment
public import Ix.Aiur.Meta
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
public import Ix.IxVM.Blake3
public import Ix.MultiStark.Goldilocks

/-! First program-independent IxBy constrained interpreter slice. The circuit
reads and authenticates raw canonical artifacts itself. It does not trust a
host-decoded program, instruction trace, output, or primitive result. This
is an experimental straight-line scalar subset; see `Fragment.lean`.

The reused Aiur compiler, lookup/memory arguments, BLAKE3 gadget, and field
gadgets have NOT been formally proved to refine the IxBy Lean evaluator.
Execution/proving tests establish conformance evidence, not that theorem. -/

public section

namespace Ix.Ixby.AiurBackend

def scalarInterpreter := ⟦
  enum IBValue {
    Bool(G),
    Word([U8; 4]),
    Field(G),
    Ext([G; 2]),
    Erased
  }

  type IBLocals = List‹IBValue›

  -- Advice is untrusted. Range-check EVERY loaded byte before storing it;
  -- neither U8 annotations nor io_read by themselves establish this range.
  fn ib_read_advice(channel: G, idx: G, len: G) -> ByteStream {
    match len {
      0 => store(ListNode.Nil),
      _ =>
        let [raw] = io_read(channel, idx, 1);
        let (byte, _) = u8_range_check(raw, 0);
        let tail = ib_read_advice(channel, idx + 1, len - 1);
        store(ListNode.Cons(byte, tail)),
    }
  }

  fn ib_load(channel: G, limit: G) -> ByteStream {
    let (idx, len) = io_get_info(channel, [0]);
    assert_eq!(u32_less_than(len, limit + 1), 1, "IxBy artifact byte limit");
    ib_read_advice(channel, idx, len)
  }

  fn ib_byte(bytes: ByteStream) -> (U8, ByteStream) {
    let ListNode.Cons(byte, rest) = load(bytes);
    (byte, rest)
  }

  fn ib_expect(bytes: ByteStream, expected: G) -> ByteStream {
    let (byte, rest) = ib_byte(bytes);
    assert_eq!(to_field(byte), expected, "IxBy byte/tag mismatch");
    rest
  }

  fn ib_word(bytes: ByteStream) -> ([U8; 4], ByteStream) {
    let (a, rest) = ib_byte(bytes);
    let (b, rest) = ib_byte(rest);
    let (c, rest) = ib_byte(rest);
    let (d, rest) = ib_byte(rest);
    ([a, b, c, d], rest)
  }

  fn ib_u32(bytes: ByteStream) -> (G, ByteStream) {
    let (word, rest) = @ib_word(bytes);
    (@b3_pack_w(word), rest)
  }

  fn ib_header(bytes: ByteStream, last: G) -> ByteStream {
    let bytes = @ib_expect(bytes, 73);
    let bytes = @ib_expect(bytes, 88);
    let bytes = @ib_expect(bytes, 66);
    let bytes = @ib_expect(bytes, last);
    let (version, rest) = @ib_u32(bytes);
    assert_eq!(version, 0, "IxBy wire revision");
    rest
  }

  fn ib_field(bytes: ByteStream) -> (G, ByteStream) {
    let (lo, rest) = @ib_word(bytes);
    let (hi, rest) = @ib_word(rest);
    let raw = [lo[0], lo[1], lo[2], lo[3], hi[0], hi[1], hi[2], hi[3]];
    assert_eq!(@gl_lt_p(raw), 1, "IxBy noncanonical field");
    (@gl_val(raw), rest)
  }

  fn ib_scalar(bytes: ByteStream) -> (IBValue, ByteStream) {
    let (tag, rest) = ib_byte(bytes);
    match tag {
      0 =>
        let (boolean, rest) = ib_byte(rest);
        let b = to_field(boolean);
        assert_eq!(b * b, b, "IxBy noncanonical Bool");
        (IBValue.Bool(b), rest),
      1 =>
        let (word, rest) = @ib_word(rest);
        (IBValue.Word(word), rest),
      2 =>
        let (field, rest) = ib_field(rest);
        (IBValue.Field(field), rest),
      3 =>
        let (c0, rest) = ib_field(rest);
        let (c1, rest) = ib_field(rest);
        (IBValue.Ext([c0, c1]), rest),
      _ =>
        assert_eq!(0, 1, "IxBy unsupported scalar");
        (IBValue.Erased, rest),
    }
  }

  fn ib_value(bytes: ByteStream) -> (IBValue, ByteStream) {
    let (tag, rest) = ib_byte(bytes);
    match tag {
      0 => ib_scalar(rest),
      3 => (IBValue.Erased, rest),
      _ =>
        assert_eq!(0, 1, "IxBy unsupported structured value");
        (IBValue.Erased, rest),
    }
  }

  -- Internal lists are reverse ordered so appending an immutable local is
  -- one store. Absolute wire indices are transported explicitly below.
  fn ib_inputs(bytes: ByteStream, remaining: G, locals: IBLocals) -> IBLocals {
    match remaining {
      0 =>
        assert_eq!(load(bytes), ListNode.Nil, "IxBy trailing input bytes");
        locals,
      _ =>
        let (value, rest) = ib_value(bytes);
        ib_inputs(rest, remaining - 1, store(ListNode.Cons(value, locals))),
    }
  }

  fn ib_local(locals: IBLocals, reverse_index: G) -> IBValue {
    let ListNode.Cons(value, tail) = load(locals);
    match reverse_index {
      0 => value,
      _ => ib_local(tail, reverse_index - 1),
    }
  }

  fn ib_operand(bytes: ByteStream, locals: IBLocals, count: G) -> (IBValue, ByteStream) {
    let (tag, rest) = ib_byte(bytes);
    match tag {
      0 =>
        let (index, rest) = @ib_u32(rest);
        assert_eq!(u32_less_than(index, count), 1, "IxBy invalid local");
        (ib_local(locals, count - (index + 1)), rest),
      1 => ib_scalar(rest),
      2 => (IBValue.Erased, rest),
      _ =>
        assert_eq!(0, 1, "IxBy unknown operand");
        (IBValue.Erased, rest),
    }
  }

  fn ib_unary(opcode: G, a: IBValue) -> IBValue {
    match opcode {
      13 => let IBValue.Word(a) = a; IBValue.Field(@b3_pack_w(a)),
      17 => let IBValue.Field(a) = a; IBValue.Field(@gl_inverse(a)),
      24 => let IBValue.Ext(a) = a; IBValue.Ext(@eg_inverse(a)),
      27 => let IBValue.Ext(a) = a; IBValue.Field(a[0]),
      28 => let IBValue.Ext(a) = a; IBValue.Field(a[1]),
      _ => assert_eq!(0, 1, "IxBy unsupported unary primitive"); IBValue.Erased,
    }
  }

  fn ib_binary(opcode: G, a: IBValue, b: IBValue) -> IBValue {
    match opcode {
      0 =>
        let IBValue.Word(a) = a; let IBValue.Word(b) = b;
        IBValue.Word(u32_add(a, b)),
      3 =>
        let IBValue.Word(a) = a; let IBValue.Word(b) = b;
        IBValue.Word(@u32_and(a, b)),
      4 =>
        let IBValue.Word(a) = a; let IBValue.Word(b) = b;
        IBValue.Word([u8_or(a[0], b[0]), u8_or(a[1], b[1]),
          u8_or(a[2], b[2]), u8_or(a[3], b[3])]),
      5 =>
        let IBValue.Word(a) = a; let IBValue.Word(b) = b;
        IBValue.Word(@u32_xor(a, b)),
      9 =>
        let IBValue.Word(a) = a; let IBValue.Word(b) = b;
        IBValue.Bool(eq_zero(@b3_pack_w(a) - @b3_pack_w(b))),
      10 =>
        let IBValue.Word(a) = a; let IBValue.Word(b) = b;
        IBValue.Bool(u32_less_than(@b3_pack_w(a), @b3_pack_w(b))),
      14 => let IBValue.Field(a) = a; let IBValue.Field(b) = b; IBValue.Field(a + b),
      15 => let IBValue.Field(a) = a; let IBValue.Field(b) = b; IBValue.Field(a - b),
      16 => let IBValue.Field(a) = a; let IBValue.Field(b) = b; IBValue.Field(a * b),
      18 => let IBValue.Field(a) = a; let IBValue.Field(b) = b; IBValue.Bool(eq_zero(a - b)),
      21 => let IBValue.Ext(a) = a; let IBValue.Ext(b) = b; IBValue.Ext(@eg_add(a, b)),
      22 => let IBValue.Ext(a) = a; let IBValue.Ext(b) = b; IBValue.Ext(@eg_sub(a, b)),
      23 => let IBValue.Ext(a) = a; let IBValue.Ext(b) = b; IBValue.Ext(@eg_mul(a, b)),
      25 => let IBValue.Ext(a) = a; let IBValue.Ext(b) = b; IBValue.Bool(@eg_eq(a, b)),
      26 => let IBValue.Field(a) = a; let IBValue.Field(b) = b; IBValue.Ext([a, b]),
      _ => assert_eq!(0, 1, "IxBy unsupported binary primitive"); IBValue.Erased,
    }
  }

  fn ib_op(bytes: ByteStream, locals: IBLocals, count: G) -> (IBValue, ByteStream) {
    let (tag, rest) = ib_byte(bytes);
    match tag {
      0 => ib_operand(rest, locals, count),
      1 =>
        let (opcode, rest) = ib_byte(rest);
        let (arity, rest) = @ib_u32(rest);
        assert_eq!(u32_less_than(arity, @ib_max_operands() + 1), 1, "IxBy primitive operand capacity");
        let (a, rest) = ib_operand(rest, locals, count);
        match arity {
          1 => (ib_unary(to_field(opcode), a), rest),
          2 =>
            let (b, rest) = ib_operand(rest, locals, count);
            (ib_binary(to_field(opcode), a, b), rest),
          _ => assert_eq!(0, 1, "IxBy unsupported primitive arity"); (IBValue.Erased, rest),
        },
      _ => assert_eq!(0, 1, "IxBy unsupported operation"); (IBValue.Erased, rest),
    }
  }

  -- Parsing and execution are fused for this straight-line subset. ALL
  -- blocks are consumed; only the final block may return. The proven run
  -- takes exactly block_count + 1 reference transitions (including terminal).
  fn ib_blocks(bytes: ByteStream, remaining: G, index: G,
      locals: IBLocals, count: G) -> IBValue {
    assert_eq!(eq_zero(remaining), 0, "IxBy missing terminal return");
    let (declared, rest) = @ib_u32(bytes);
    assert_eq!(declared, count, "IxBy incoming local frame");
    assert_eq!(u32_less_than(count, @ib_max_locals() + 1), 1, "IxBy local capacity");
    let (tag, rest) = ib_byte(rest);
    match tag {
      0 =>
        assert_eq!(eq_zero(remaining - 1), 0, "IxBy final block must return");
        let (value, rest) = ib_op(rest, locals, count);
        let (next, rest) = @ib_u32(rest);
        assert_eq!(next, index + 1, "IxBy nonsequential successor");
        ib_blocks(rest, remaining - 1, index + 1,
          store(ListNode.Cons(value, locals)), count + 1),
      1 =>
        assert_eq!(remaining, 1, "IxBy premature return or unused code");
        let (value, rest) = ib_operand(rest, locals, count);
        assert_eq!(load(rest), ListNode.Nil, "IxBy trailing program bytes");
        value,
      _ => assert_eq!(0, 1, "IxBy unsupported control"); IBValue.Erased,
    }
  }

  fn ib_run(program: ByteStream, input: ByteStream) -> IBValue {
    let code = @ib_header(program, 89);
    let (entry, code) = @ib_u32(code);
    let (constructors, code) = @ib_u32(code);
    let (functions, code) = @ib_u32(code);
    assert_eq!([entry, constructors, functions], [0, 0, 1], "IxBy scalar program shape");
    let (arity, code) = @ib_u32(code);
    let (entry_block, code) = @ib_u32(code);
    let (blocks, code) = @ib_u32(code);
    assert_eq!(entry_block, 0, "IxBy nonzero block entry");
    assert_eq!(eq_zero(blocks), 0, "IxBy empty function");
    assert_eq!(u32_less_than(blocks, @ib_max_blocks() + 1), 1, "IxBy block capacity");
    assert_eq!(u32_less_than(blocks + 1, @ib_max_steps() + 1), 1, "IxBy step capacity");
    assert_eq!(u32_less_than(arity, @ib_max_operands() + 1), 1, "IxBy operand capacity");
    assert_eq!(u32_less_than(arity, @ib_max_nodes() + 1), 1, "IxBy input node capacity");
    let input = @ib_header(input, 73);
    let (inputs, input) = @ib_u32(input);
    assert_eq!(inputs, arity, "IxBy input arity");
    let locals = ib_inputs(input, arity, store(ListNode.Nil));
    ib_blocks(code, blocks, 0, locals, arity)
  }

  fn ib_cons(byte: U8, tail: ByteStream) -> ByteStream {
    store(ListNode.Cons(byte, tail))
  }

  fn ib_put4(a: [U8; 4], tail: ByteStream) -> ByteStream {
    @ib_cons(a[0], @ib_cons(a[1], @ib_cons(a[2], @ib_cons(a[3], tail))))
  }

  fn ib_put8(a: [U8; 8], tail: ByteStream) -> ByteStream {
    @ib_put4([a[0], a[1], a[2], a[3]], @ib_put4([a[4], a[5], a[6], a[7]], tail))
  }

  fn ib_put_digest(a: [[U8; 4]; 8], tail: ByteStream) -> ByteStream {
    @ib_put4(a[0], @ib_put4(a[1], @ib_put4(a[2], @ib_put4(a[3],
      @ib_put4(a[4], @ib_put4(a[5], @ib_put4(a[6], @ib_put4(a[7], tail))))))))
  }

  fn ib_output(value: IBValue) -> (ByteStream, G) {
    let nil = store(ListNode.Nil);
    let (body, size) = match value {
      -- b is Boolean by input admission or the defining primitive constraints.
      IBValue.Bool(b) => (@ib_cons(0u8, @ib_cons(0u8, @ib_cons(u8_from_field_unsafe(b), nil))), 3),
      IBValue.Word(w) => (@ib_cons(0u8, @ib_cons(1u8, @ib_put4(w, nil))), 6),
      IBValue.Field(f) => (@ib_cons(0u8, @ib_cons(2u8, @ib_put8(gl_to_bytes(f), nil))), 10),
      IBValue.Ext(f) => (@ib_cons(0u8, @ib_cons(3u8,
        @ib_put8(gl_to_bytes(f[0]), @ib_put8(gl_to_bytes(f[1]), nil)))), 18),
      IBValue.Erased => (@ib_cons(3u8, nil), 1),
    };
    (@ib_put4([73u8, 88u8, 66u8, 79u8], @ib_put4([0u8; 4], body)), size + 8)
  }

  -- Exact Commitment.hash framing: ASCII("IxBy/commit/v0"), NUL, domain.
  fn ib_domain(domain: U8, bytes: ByteStream) -> ByteStream {
    @ib_put4([73u8, 120u8, 66u8, 121u8],
      @ib_put4([47u8, 99u8, 111u8, 109u8],
        @ib_put4([109u8, 105u8, 116u8, 47u8],
          @ib_cons(118u8, @ib_cons(48u8, @ib_cons(0u8, @ib_cons(domain, bytes)))))))
  }

  pub fn ixby_scalar_exec(p: [G; 8], b: [G; 8], i: [G; 8], o: [G; 8]) {
    let profile_hash = @ib_profile_hash();
    assert_eq!(@b3_pack(profile_hash), p, "IxBy profile commitment");
    -- This slice always returns one flat value and enters exactly one function.
    assert_eq!(u32_less_than(0, @ib_max_nodes()), 1, "IxBy output node capacity");
    assert_eq!(u32_less_than(0, @ib_max_depth()), 1, "IxBy value depth capacity");
    assert_eq!(u32_less_than(0, @ib_max_functions()), 1, "IxBy function capacity");
    let program = ib_load(0, @ib_max_program_bytes());
    let program_hash = @blake3(@ib_domain(1u8, @ib_put_digest(profile_hash, program)));
    assert_eq!(@b3_pack(program_hash), b, "IxBy program commitment");
    let input = ib_load(1, @ib_max_value_bytes());
    let input_hash = @blake3(@ib_domain(2u8, @ib_put_digest(program_hash, input)));
    assert_eq!(@b3_pack(input_hash), i, "IxBy input commitment");
    let (output, size) = ib_output(ib_run(program, input));
    assert_eq!(u32_less_than(size, @ib_max_value_bytes() + 1), 1, "IxBy output byte capacity");
    let output_hash = @blake3(@ib_domain(3u8, @ib_put_digest(program_hash, output)));
    assert_eq!(@b3_pack(output_hash), o, "IxBy output commitment");
  }
⟧

/-- Derive the circuit constants from the same profile used by the reference
codec. These are fixed in the verifying key, never supplied as prover advice. -/
def profileConstants (profile : Profile) : Except Codec.Error Aiur.Source.Toplevel := do
  -- The parser and opcode table above implement exactly these revisions.
  -- A future codec change must not silently build a stale interpreter key.
  unless Codec.wireVersion == 0 && Codec.semanticVersion == 0 do throw .version
  let bytes ← Codec.encodeProfile profile
  let digest := (Commitment.hash .profile bytes).bytes
  let hashBody := Aiur.Source.Term.array ((Array.range 8).map fun i =>
    .array ((Array.range 4).map fun j =>
      .u8Lit digest[i * 4 + j]!.toNat))
  let constants : Array (Lean.Name × Nat) := #[
    (`ib_max_locals, profile.limits.locals), (`ib_max_blocks, profile.limits.blocks),
    (`ib_max_operands, profile.limits.operands), (`ib_max_nodes, profile.limits.inputNodes),
    (`ib_max_depth, profile.valueDepth), (`ib_max_functions, profile.limits.functions),
    (`ib_max_continuations, profile.limits.continuations),
    (`ib_max_constructors, profile.limits.constructors),
    (`ib_max_rank, profile.valueDepth + profile.maxSteps),
    (`ib_max_steps, profile.maxSteps), (`ib_max_program_bytes, profile.programBytes),
    (`ib_max_value_bytes, profile.valueBytes)]
  let functions := constants.map fun (name, value) =>
    Aiur.Source.Function.monoNonEntry ⟨name⟩ [] .field (.field (.ofNat value))
  return ⟨#[], #[], functions.push (Aiur.Source.Function.monoNonEntry
    ⟨`ib_profile_hash⟩ [] (.array (.array .u8 4) 8) hashBody)⟩

def scalarConstants : Except Codec.Error Aiur.Source.Toplevel := profileConstants profile

def scalarToplevel : Except String Aiur.Source.Toplevel := do
  let constants ← scalarConstants.mapError (fun e => s!"profile encoding: {repr e}")
  let source ← (do
    let source ← IxVM.core.merge IxVM.byteStream
    let source ← source.merge IxVM.blake3
    let source ← source.merge MultiStark.goldilocks
    let source ← source.merge constants
    source.merge scalarInterpreter).mapError toString
  return source.prune [`ixby_scalar_exec]

end Ix.Ixby.AiurBackend
