module
public import Ix.Ixby.Aiur.Control

/-! Experimental immutable object interpreter. Constructor declarations, code,
and input trees are decoded from the authenticated bytes, never table advice.
Constructor identity uses all ten injective u32 limbs of its canonical name.
Fields/locals are reverse ordered, immutable typed-memory lists. Every object
is made with rank `1 + max child rank`; finite bounded ranks exclude cycles.
I/O node/depth limits are separate from the derived intermediate rank bound.

This source is not a proof of the Aiur compiler/memory/gadget arguments. See
`ObjectsRefinement.lean` for the explicit conditional representation contract. -/

public section

namespace Ix.Ixby.AiurBackend

def objectsInterpreter := ⟦
  enum ISValue { Atom(IBValue), Ctor(G, ISValues, G, G) }
  type ISValues = List‹ISValue›
  enum ISCtorDecl { Mk([G; 10], G) }
  type ISCtors = List‹ISCtorDecl›
  enum ISOp { Plain(ICOp), Construct(G, ICOperands, G), Project(ICOperand, G) }
  enum ISAlternative { Mk(G, G) }
  type ISAlternatives = List‹ISAlternative›
  enum ISInstr {
    Let(ISOp, G), Ret(ICOperand), Tail(G, ICOperands, G),
    Branch(ICOperand, G, G), Case(ICOperand, ISAlternatives, G)
  }
  enum ISBlock { Mk(G, ISInstr) }
  type ISBlocks = List‹ISBlock›
  enum ISFunction { Mk(G, G, G, ISBlocks) }
  type ISFunctions = List‹ISFunction›
  enum ISFrame { Mk(G, G, ISValues, G) }
  type ISStack = List‹ISFrame›
  enum ISControl { Eval(ISFrame), Ret(ISValue) }
  enum ISAction { Value(ISValue), Call(G, ISValues, G) }

  fn is_read_id(bytes: ByteStream) -> ([G; 10], ByteStream) {
    let (a, rest) = @ib_u32(bytes);
    let (b, rest) = @ib_u32(rest);
    let (c, rest) = @ib_u32(rest);
    let (d, rest) = @ib_u32(rest);
    let (e, rest) = @ib_u32(rest);
    let (f, rest) = @ib_u32(rest);
    let (g, rest) = @ib_u32(rest);
    let (h, rest) = @ib_u32(rest);
    let (i, rest) = @ib_u32(rest);
    let (j, rest) = @ib_u32(rest);
    ([a, b, c, d, e, f, g, h, i, j], rest)
  }

  fn is_id_eq(a: [G; 10], b: [G; 10]) -> G {
    eq_zero(a[0] - b[0]) * eq_zero(a[1] - b[1]) * eq_zero(a[2] - b[2]) *
    eq_zero(a[3] - b[3]) * eq_zero(a[4] - b[4]) * eq_zero(a[5] - b[5]) *
    eq_zero(a[6] - b[6]) * eq_zero(a[7] - b[7]) * eq_zero(a[8] - b[8]) *
    eq_zero(a[9] - b[9])
  }

  fn is_unique_id(id: [G; 10], ctors: ISCtors, remaining: G) {
    match remaining {
      0 => assert_eq!(load(ctors), ListNode.Nil, "IxBy extra constructors"); (),
      _ =>
        let ListNode.Cons(ISCtorDecl.Mk(other, _), tail) = load(ctors);
        assert_eq!(is_id_eq(id, other), 0, "IxBy duplicate constructor ID");
        is_unique_id(id, tail, remaining - 1),
    }
  }

  fn is_read_ctors(bytes: ByteStream, remaining: G) -> (ISCtors, ByteStream) {
    match remaining {
      0 => (store(ListNode.Nil), bytes),
      _ =>
        let (id, rest) = is_read_id(bytes);
        let (fields, rest) = @ib_u32(rest);
        assert_eq!(u32_less_than(fields, @ib_max_operands() + 1), 1, "IxBy constructor fields");
        let (ctors, rest) = is_read_ctors(rest, remaining - 1);
        is_unique_id(id, ctors, remaining - 1);
        (store(ListNode.Cons(ISCtorDecl.Mk(id, fields), ctors)), rest),
    }
  }

  fn is_ctor(ctors: ISCtors, count: G, index: G) -> ISCtorDecl {
    assert_eq!(u32_less_than(index, count), 1, "IxBy constructor index");
    list_lookup(ctors, index)
  }

  fn is_find_ctor(ctors: ISCtors, remaining: G, id: [G; 10], index: G) -> (G, G) {
    assert_eq!(eq_zero(remaining), 0, "IxBy unknown value constructor");
    let ListNode.Cons(ISCtorDecl.Mk(other, fields), tail) = load(ctors);
    match is_id_eq(id, other) {
      1 => (index, fields),
      _ => is_find_ctor(tail, remaining - 1, id, index + 1),
    }
  }

  fn is_rank(value: ISValue) -> G {
    match value {
      ISValue.Atom(_) => 1,
      ISValue.Ctor(_, _, _, rank) =>
        assert_eq!(eq_zero(rank), 0, "IxBy zero object rank");
        assert_eq!(u32_less_than(rank, @ib_max_rank() + 1), 1, "IxBy object rank bound");
        rank,
    }
  }

  fn is_fields_rank(fields: ISValues, remaining: G) -> G {
    match remaining {
      0 => assert_eq!(load(fields), ListNode.Nil, "IxBy extra constructor fields"); 0,
      _ =>
        let ListNode.Cons(value, tail) = load(fields);
        let rank = is_rank(value);
        let rest = is_fields_rank(tail, remaining - 1);
        match u32_less_than(rank, rest) { 1 => rest, _ => rank, },
    }
  }

  fn is_make(ctors: ISCtors, constructors: G, index: G, fields: ISValues, count: G) -> ISValue {
    let ISCtorDecl.Mk(_, declared) = is_ctor(ctors, constructors, index);
    assert_eq!(count, declared, "IxBy constructor arity");
    let rank = is_fields_rank(fields, count) + 1;
    assert_eq!(u32_less_than(rank, @ib_max_rank() + 1), 1, "IxBy constructed rank bound");
    ISValue.Ctor(index, fields, count, rank)
  }

  -- One shared node counter crosses all siblings and roots. Depth decreases
  -- only on child edges; scalar and nullary-constructor roots still cost one.
  fn is_read_value(bytes: ByteStream, ctors: ISCtors, constructors: G,
      nodes: G, depth: G) -> (ISValue, ByteStream, G) {
    assert_eq!(eq_zero(nodes), 0, "IxBy input node budget");
    assert_eq!(eq_zero(depth), 0, "IxBy input depth budget");
    let (tag, rest) = ib_byte(bytes);
    match tag {
      0 =>
        let (value, rest) = ib_scalar(rest);
        (ISValue.Atom(value), rest, nodes - 1),
      3 => (ISValue.Atom(IBValue.Erased), rest, nodes - 1),
      1 =>
        let (id, rest) = is_read_id(rest);
        let (index, declared) = is_find_ctor(ctors, constructors, id, 0);
        let (count, rest) = @ib_u32(rest);
        assert_eq!(count, declared, "IxBy input constructor arity");
        let (fields, rest, nodes) = is_read_values(rest, count, ctors, constructors,
          nodes - 1, depth - 1, store(ListNode.Nil));
        (is_make(ctors, constructors, index, fields, count), rest, nodes),
      _ => assert_eq!(0, 1, "IxBy unsupported object value");
        (ISValue.Atom(IBValue.Erased), rest, nodes - 1),
    }
  }

  fn is_read_values(bytes: ByteStream, remaining: G, ctors: ISCtors, constructors: G,
      nodes: G, depth: G, reversed: ISValues) -> (ISValues, ByteStream, G) {
    match remaining {
      0 => (reversed, bytes, nodes),
      _ =>
        let (value, rest, nodes) = is_read_value(bytes, ctors, constructors, nodes, depth);
        is_read_values(rest, remaining - 1, ctors, constructors, nodes, depth,
          store(ListNode.Cons(value, reversed))),
    }
  }

  fn is_read_op(bytes: ByteStream, self: G, locals: G) -> (ISOp, ByteStream) {
    let (tag, rest) = ib_byte(bytes);
    match tag {
      0 =>
        let (arg, rest) = ic_read_operand(rest, locals);
        (ISOp.Plain(ICOp.Copy(arg)), rest),
      1 =>
        let (opcode, rest) = ib_byte(rest);
        let arity = ic_primitive_arity(to_field(opcode));
        let (args, count, rest) = ic_read_operands(rest, locals);
        assert_eq!(count, arity, "IxBy primitive arity");
        (ISOp.Plain(ICOp.Primitive(to_field(opcode), args, count)), rest),
      2 =>
        let (ctor, rest) = @ib_u32(rest);
        let (args, count, rest) = ic_read_operands(rest, locals);
        (ISOp.Construct(ctor, args, count), rest),
      3 =>
        let (arg, rest) = ic_read_operand(rest, locals);
        let (index, rest) = @ib_u32(rest);
        (ISOp.Project(arg, index), rest),
      5 =>
        let (callee, rest) = @ib_u32(rest);
        let (args, count, rest) = ic_read_operands(rest, locals);
        (ISOp.Plain(ICOp.Call(callee, args, count)), rest),
      6 =>
        let (args, count, rest) = ic_read_operands(rest, locals);
        (ISOp.Plain(ICOp.Call(self, args, count)), rest),
      _ => assert_eq!(0, 1, "IxBy unsupported object operation");
        (ISOp.Plain(ICOp.Copy(ICOperand.Literal(IBValue.Erased))), rest),
    }
  }

  fn is_unique_alt(index: G, alts: ISAlternatives, remaining: G) {
    match remaining {
      0 => assert_eq!(load(alts), ListNode.Nil, "IxBy extra alternatives"); (),
      _ =>
        let ListNode.Cons(ISAlternative.Mk(other, _), tail) = load(alts);
        assert_eq!(eq_zero(index - other), 0, "IxBy duplicate case alternative");
        is_unique_alt(index, tail, remaining - 1),
    }
  }

  fn is_read_alts(bytes: ByteStream, remaining: G) -> (ISAlternatives, ByteStream) {
    match remaining {
      0 => (store(ListNode.Nil), bytes),
      _ =>
        let (ctor, rest) = @ib_u32(bytes);
        let (target, rest) = @ib_u32(rest);
        let (alts, rest) = is_read_alts(rest, remaining - 1);
        is_unique_alt(ctor, alts, remaining - 1);
        (store(ListNode.Cons(ISAlternative.Mk(ctor, target), alts)), rest),
    }
  }

  fn is_read_instr(bytes: ByteStream, self: G, locals: G) -> (ISInstr, ByteStream) {
    let (tag, rest) = ib_byte(bytes);
    match tag {
      0 =>
        let (op, rest) = is_read_op(rest, self, locals);
        let (next, rest) = @ib_u32(rest);
        (ISInstr.Let(op, next), rest),
      1 =>
        let (arg, rest) = ic_read_operand(rest, locals);
        (ISInstr.Ret(arg), rest),
      2 =>
        let (callee, rest) = @ib_u32(rest);
        let (args, count, rest) = ic_read_operands(rest, locals);
        (ISInstr.Tail(callee, args, count), rest),
      3 =>
        let (args, count, rest) = ic_read_operands(rest, locals);
        (ISInstr.Tail(self, args, count), rest),
      5 =>
        let (arg, rest) = ic_read_operand(rest, locals);
        let (count, rest) = @ib_u32(rest);
        assert_eq!(u32_less_than(count, @ib_max_constructors() + 1), 1, "IxBy alternative capacity");
        let (alts, rest) = is_read_alts(rest, count);
        (ISInstr.Case(arg, alts, count), rest),
      6 =>
        let (arg, rest) = ic_read_operand(rest, locals);
        let (yes, rest) = @ib_u32(rest);
        let (no, rest) = @ib_u32(rest);
        (ISInstr.Branch(arg, yes, no), rest),
      _ => assert_eq!(0, 1, "IxBy unsupported object instruction");
        (ISInstr.Ret(ICOperand.Literal(IBValue.Erased)), rest),
    }
  }

  fn is_read_blocks(bytes: ByteStream, remaining: G, self: G) -> (ISBlocks, ByteStream) {
    match remaining {
      0 => (store(ListNode.Nil), bytes),
      _ =>
        let (locals, rest) = @ib_u32(bytes);
        assert_eq!(u32_less_than(locals, @ib_max_locals() + 1), 1, "IxBy declared local capacity");
        let (instr, rest) = is_read_instr(rest, self, locals);
        let (blocks, rest) = is_read_blocks(rest, remaining - 1, self);
        (store(ListNode.Cons(ISBlock.Mk(locals, instr), blocks)), rest),
    }
  }

  fn is_read_functions(bytes: ByteStream, remaining: G, self: G) -> (ISFunctions, ByteStream) {
    match remaining {
      0 => (store(ListNode.Nil), bytes),
      _ =>
        let (arity, rest) = @ib_u32(bytes);
        assert_eq!(u32_less_than(arity, @ib_max_operands() + 1), 1, "IxBy function arity capacity");
        assert_eq!(u32_less_than(arity, @ib_max_locals() + 1), 1, "IxBy function local capacity");
        let (entry, rest) = @ib_u32(rest);
        let (count, rest) = @ib_u32(rest);
        assert_eq!(u32_less_than(count, @ib_max_blocks() + 1), 1, "IxBy block capacity");
        assert_eq!(eq_zero(count), 0, "IxBy empty function");
        let (blocks, rest) = is_read_blocks(rest, count, self);
        let (functions, rest) = is_read_functions(rest, remaining - 1, self + 1);
        (store(ListNode.Cons(ISFunction.Mk(arity, entry, count, blocks), functions)), rest),
    }
  }

  fn is_function(program: ISFunctions, count: G, index: G) -> ISFunction {
    assert_eq!(u32_less_than(index, count), 1, "IxBy function index");
    list_lookup(program, index)
  }

  fn is_block(blocks: ISBlocks, count: G, index: G) -> ISBlock {
    assert_eq!(u32_less_than(index, count), 1, "IxBy block index");
    list_lookup(blocks, index)
  }

  fn is_target(blocks: ISBlocks, count: G, index: G, locals: G) {
    let ISBlock.Mk(declared, _) = is_block(blocks, count, index);
    assert_eq!(declared, locals, "IxBy target frame contract");
  }

  fn is_check_call(program: ISFunctions, functions: G, callee: G, args: G) {
    let ISFunction.Mk(arity, _, _, _) = is_function(program, functions, callee);
    assert_eq!(arity, args, "IxBy direct call arity");
  }

  fn is_check_op(program: ISFunctions, functions: G, ctors: ISCtors, constructors: G, op: ISOp) {
    match op {
      ISOp.Plain(plain) => match plain {
        ICOp.Copy(_) => (), ICOp.Primitive(_, _, _) => (),
        ICOp.Call(callee, _, args) => is_check_call(program, functions, callee, args),
      },
      ISOp.Construct(index, _, args) =>
        let ISCtorDecl.Mk(_, fields) = is_ctor(ctors, constructors, index);
        assert_eq!(args, fields, "IxBy code constructor arity"); (),
      ISOp.Project(_, _) => (),
    }
  }

  fn is_check_alts(ctors: ISCtors, constructors: G, blocks: ISBlocks, count: G,
      locals: G, alts: ISAlternatives, remaining: G) {
    match remaining {
      0 => assert_eq!(load(alts), ListNode.Nil, "IxBy extra alternatives"); (),
      _ =>
        let ListNode.Cons(ISAlternative.Mk(ctor, target), tail) = load(alts);
        let ISCtorDecl.Mk(_, fields) = is_ctor(ctors, constructors, ctor);
        is_target(blocks, count, target, locals + fields);
        is_check_alts(ctors, constructors, blocks, count, locals, tail, remaining - 1),
    }
  }

  -- Every block and every alternative is checked, including unreachable code.
  fn is_check_blocks(program: ISFunctions, functions: G, ctors: ISCtors, constructors: G,
      blocks: ISBlocks, count: G, rest: ISBlocks, remaining: G) {
    match remaining {
      0 => assert_eq!(load(rest), ListNode.Nil, "IxBy extra decoded blocks"); (),
      _ =>
        let ListNode.Cons(ISBlock.Mk(locals, instr), tail) = load(rest);
        match instr {
          ISInstr.Let(op, target) =>
            is_check_op(program, functions, ctors, constructors, op);
            is_target(blocks, count, target, locals + 1),
          ISInstr.Ret(_) => (),
          ISInstr.Tail(callee, _, args) => is_check_call(program, functions, callee, args),
          ISInstr.Branch(_, yes, no) =>
            is_target(blocks, count, yes, locals);
            is_target(blocks, count, no, locals),
          ISInstr.Case(_, alts, alternatives) =>
            is_check_alts(ctors, constructors, blocks, count, locals, alts, alternatives),
        };
        is_check_blocks(program, functions, ctors, constructors, blocks, count, tail, remaining - 1),
    }
  }

  fn is_check_functions(program: ISFunctions, functions: G, ctors: ISCtors, constructors: G,
      rest: ISFunctions, remaining: G) {
    match remaining {
      0 => assert_eq!(load(rest), ListNode.Nil, "IxBy extra decoded functions"); (),
      _ =>
        let ListNode.Cons(ISFunction.Mk(arity, entry, count, blocks), tail) = load(rest);
        is_target(blocks, count, entry, arity);
        is_check_blocks(program, functions, ctors, constructors, blocks, count, blocks, count);
        is_check_functions(program, functions, ctors, constructors, tail, remaining - 1),
    }
  }

  fn is_operand(operand: ICOperand, locals: ISValues, count: G) -> ISValue {
    match operand {
      ICOperand.Local(index) =>
        assert_eq!(u32_less_than(index, count), 1, "IxBy runtime local index");
        list_lookup(locals, count - (index + 1)),
      ICOperand.Literal(value) => ISValue.Atom(value),
    }
  }

  fn is_args(args: ICOperands, remaining: G, locals: ISValues, count: G,
      reversed: ISValues) -> ISValues {
    match remaining {
      0 => assert_eq!(load(args), ListNode.Nil, "IxBy extra operands"); reversed,
      _ =>
        let ListNode.Cons(arg, rest) = load(args);
        let value = is_operand(arg, locals, count);
        is_args(rest, remaining - 1, locals, count, store(ListNode.Cons(value, reversed))),
    }
  }

  fn is_project(value: ISValue, index: G) -> ISValue {
    match value {
      ISValue.Atom(atom) =>
        assert_eq!(atom, IBValue.Erased, "IxBy projection of non-object");
        ISValue.Atom(IBValue.Erased),
      ISValue.Ctor(_, fields, count, _) =>
        assert_eq!(u32_less_than(index, count), 1, "IxBy field index");
        list_lookup(fields, count - (index + 1)),
    }
  }

  fn is_op(op: ISOp, locals: ISValues, count: G, ctors: ISCtors, constructors: G) -> ISAction {
    match op {
      ISOp.Plain(plain) => match plain {
        ICOp.Copy(arg) => ISAction.Value(is_operand(arg, locals, count)),
        ICOp.Primitive(opcode, args, arity) =>
          let ListNode.Cons(a, rest) = load(args);
          let ISValue.Atom(a) = is_operand(a, locals, count);
          match arity {
            1 =>
              assert_eq!(load(rest), ListNode.Nil, "IxBy extra unary operand");
              ISAction.Value(ISValue.Atom(ib_unary(opcode, a))),
            2 =>
              let ListNode.Cons(b, rest) = load(rest);
              let ISValue.Atom(b) = is_operand(b, locals, count);
              assert_eq!(load(rest), ListNode.Nil, "IxBy extra binary operand");
              ISAction.Value(ISValue.Atom(ib_binary(opcode, a, b))),
            _ => assert_eq!(0, 1, "IxBy primitive arity"); ISAction.Value(ISValue.Atom(IBValue.Erased)),
          },
        ICOp.Call(callee, args, arity) =>
          ISAction.Call(callee, is_args(args, arity, locals, count, store(ListNode.Nil)), arity),
      },
      ISOp.Construct(index, args, arity) =>
        let fields = is_args(args, arity, locals, count, store(ListNode.Nil));
        ISAction.Value(is_make(ctors, constructors, index, fields, arity)),
      ISOp.Project(arg, index) => ISAction.Value(is_project(is_operand(arg, locals, count), index)),
    }
  }

  fn is_append_fields(fields: ISValues, remaining: G, locals: ISValues) -> ISValues {
    match remaining {
      0 => assert_eq!(load(fields), ListNode.Nil, "IxBy extra case fields"); locals,
      _ =>
        let ListNode.Cons(value, tail) = load(fields);
        store(ListNode.Cons(value, is_append_fields(tail, remaining - 1, locals))),
    }
  }

  fn is_case(alts: ISAlternatives, remaining: G, index: G) -> G {
    assert_eq!(eq_zero(remaining), 0, "IxBy missing case alternative");
    let ListNode.Cons(ISAlternative.Mk(ctor, target), tail) = load(alts);
    match eq_zero(index - ctor) {
      1 => target,
      _ => is_case(tail, remaining - 1, index),
    }
  }

  fn is_frame(program: ISFunctions, functions: G, self: G, block: G,
      locals: ISValues, count: G) -> ISFrame {
    assert_eq!(u32_less_than(count, @ib_max_locals() + 1), 1, "IxBy runtime local capacity");
    let ISFunction.Mk(_, _, blocks, code) = is_function(program, functions, self);
    is_target(code, blocks, block, count);
    ISFrame.Mk(self, block, locals, count)
  }

  fn is_enter(program: ISFunctions, functions: G, callee: G, args: ISValues, count: G) -> ISFrame {
    let ISFunction.Mk(arity, entry, _, _) = is_function(program, functions, callee);
    assert_eq!(arity, count, "IxBy runtime call arity");
    is_frame(program, functions, callee, entry, args, count)
  }

  fn is_machine(program: ISFunctions, functions: G, ctors: ISCtors, constructors: G,
      control: ISControl, stack: ISStack, depth: G, fuel: G) -> ISValue {
    assert_eq!(eq_zero(fuel), 0, "IxBy exhausted transition budget");
    match control {
      ISControl.Eval(ISFrame.Mk(self, block, locals, count)) =>
        let ISFunction.Mk(_, _, blocks, code) = is_function(program, functions, self);
        let ISBlock.Mk(declared, instr) = is_block(code, blocks, block);
        assert_eq!(declared, count, "IxBy runtime frame contract");
        match instr {
          ISInstr.Let(op, next) => match is_op(op, locals, count, ctors, constructors) {
            ISAction.Value(value) =>
              let frame = is_frame(program, functions, self, next,
                store(ListNode.Cons(value, locals)), count + 1);
              is_machine(program, functions, ctors, constructors, ISControl.Eval(frame), stack, depth, fuel - 1),
            ISAction.Call(callee, args, arity) =>
              assert_eq!(u32_less_than(depth, @ib_max_continuations()), 1, "IxBy continuation capacity");
              let saved = ISFrame.Mk(self, next, locals, count);
              let frame = is_enter(program, functions, callee, args, arity);
              is_machine(program, functions, ctors, constructors, ISControl.Eval(frame),
                store(ListNode.Cons(saved, stack)), depth + 1, fuel - 1),
          },
          ISInstr.Ret(arg) =>
            let value = is_operand(arg, locals, count);
            is_machine(program, functions, ctors, constructors, ISControl.Ret(value), stack, depth, fuel - 1),
          ISInstr.Tail(callee, args, arity) =>
            let values = is_args(args, arity, locals, count, store(ListNode.Nil));
            let frame = is_enter(program, functions, callee, values, arity);
            is_machine(program, functions, ctors, constructors, ISControl.Eval(frame), stack, depth, fuel - 1),
          ISInstr.Branch(arg, yes, no) =>
            let ISValue.Atom(IBValue.Bool(b)) = is_operand(arg, locals, count);
            let target = match b {
              0 => no, 1 => yes,
              _ => assert_eq!(0, 1, "IxBy non-Boolean branch"); no,
            };
            let frame = is_frame(program, functions, self, target, locals, count);
            is_machine(program, functions, ctors, constructors, ISControl.Eval(frame), stack, depth, fuel - 1),
          ISInstr.Case(arg, alts, alternatives) =>
            let ISValue.Ctor(index, fields, arity, _) = is_operand(arg, locals, count);
            let target = is_case(alts, alternatives, index);
            let frame = is_frame(program, functions, self, target,
              is_append_fields(fields, arity, locals), count + arity);
            is_machine(program, functions, ctors, constructors, ISControl.Eval(frame), stack, depth, fuel - 1),
        },
      ISControl.Ret(value) => match load(stack) {
        ListNode.Nil => assert_eq!(depth, 0, "IxBy terminal stack depth"); value,
        ListNode.Cons(ISFrame.Mk(self, target, locals, count), rest) =>
          assert_eq!(eq_zero(depth), 0, "IxBy invalid return depth");
          let frame = is_frame(program, functions, self, target,
            store(ListNode.Cons(value, locals)), count + 1);
          is_machine(program, functions, ctors, constructors, ISControl.Eval(frame), rest, depth - 1, fuel - 1),
      },
    }
  }

  fn is_put_u32(value: G, tail: ByteStream) -> ByteStream {
    let bytes = gl_to_bytes(value);
    assert_eq!([bytes[4], bytes[5], bytes[6], bytes[7]], [0u8; 4], "IxBy output u32");
    @ib_put4([bytes[0], bytes[1], bytes[2], bytes[3]], tail)
  }

  fn is_put_id(id: [G; 10], tail: ByteStream) -> ByteStream {
    is_put_u32(id[0], is_put_u32(id[1], is_put_u32(id[2], is_put_u32(id[3],
      is_put_u32(id[4], is_put_u32(id[5], is_put_u32(id[6], is_put_u32(id[7],
        is_put_u32(id[8], is_put_u32(id[9], tail))))))))))
  }

  fn is_atom_output(value: IBValue, tail: ByteStream) -> (ByteStream, G) {
    match value {
      IBValue.Bool(b) => (@ib_cons(0u8, @ib_cons(0u8, @ib_cons(u8_from_field_unsafe(b), tail))), 3),
      IBValue.Word(w) => (@ib_cons(0u8, @ib_cons(1u8, @ib_put4(w, tail))), 6),
      IBValue.Field(f) => (@ib_cons(0u8, @ib_cons(2u8, @ib_put8(gl_to_bytes(f), tail))), 10),
      IBValue.Ext(f) => (@ib_cons(0u8, @ib_cons(3u8,
        @ib_put8(gl_to_bytes(f[0]), @ib_put8(gl_to_bytes(f[1]), tail)))), 18),
      IBValue.Erased => (@ib_cons(3u8, tail), 1),
    }
  }

  fn is_output(value: ISValue, ctors: ISCtors, constructors: G,
      nodes: G, depth: G, tail: ByteStream) -> (ByteStream, G, G) {
    assert_eq!(eq_zero(nodes), 0, "IxBy output node budget");
    assert_eq!(eq_zero(depth), 0, "IxBy output depth budget");
    match value {
      ISValue.Atom(atom) =>
        let (bytes, size) = is_atom_output(atom, tail);
        (bytes, size, nodes - 1),
      ISValue.Ctor(index, fields, count, _) =>
        assert_eq!(u32_less_than(is_rank(value), depth + 1), 1, "IxBy output rank/depth");
        let ISCtorDecl.Mk(id, declared) = is_ctor(ctors, constructors, index);
        assert_eq!(count, declared, "IxBy output constructor arity");
        let (bytes, size, nodes) = is_output_fields(fields, count, ctors, constructors,
          nodes - 1, depth - 1, tail);
        (@ib_cons(1u8, is_put_id(id, is_put_u32(count, bytes))), size + 45, nodes),
    }
  }

  -- Reverse fields are serialized by prepending: bytes remain in declaration
  -- order. Shared objects are unfolded, charging each occurrence to ONE budget.
  fn is_output_fields(fields: ISValues, remaining: G, ctors: ISCtors, constructors: G,
      nodes: G, depth: G, tail: ByteStream) -> (ByteStream, G, G) {
    match remaining {
      0 => assert_eq!(load(fields), ListNode.Nil, "IxBy extra output fields"); (tail, 0, nodes),
      _ =>
        let ListNode.Cons(value, rest) = load(fields);
        let (bytes, size, nodes) = is_output(value, ctors, constructors, nodes, depth, tail);
        let (bytes, restSize, nodes) = is_output_fields(rest, remaining - 1,
          ctors, constructors, nodes, depth, bytes);
        (bytes, size + restSize, nodes),
    }
  }

  fn is_run(program: ByteStream, input: ByteStream) -> (ISValue, ISCtors, G) {
    let code = @ib_header(program, 89);
    let (entry, code) = @ib_u32(code);
    let (constructors, code) = @ib_u32(code);
    assert_eq!(u32_less_than(constructors, @ib_max_constructors() + 1), 1, "IxBy constructor capacity");
    let (ctors, code) = is_read_ctors(code, constructors);
    let (functions, code) = @ib_u32(code);
    assert_eq!(u32_less_than(functions, @ib_max_functions() + 1), 1, "IxBy function capacity");
    assert_eq!(eq_zero(functions), 0, "IxBy empty program");
    -- Reused tail names exercise scope-safe normalization: the later input
    -- binding must not retarget this program-tail assertion. Source/native
    -- trailing-byte regressions cover the original compiler bug here.
    let (program, rest) = is_read_functions(code, functions, 0);
    assert_eq!(load(rest), ListNode.Nil, "IxBy trailing program bytes");
    is_check_functions(program, functions, ctors, constructors, program, functions);
    let ISFunction.Mk(arity, _, _, _) = is_function(program, functions, entry);
    let input = @ib_header(input, 73);
    let (inputs, input) = @ib_u32(input);
    assert_eq!(inputs, arity, "IxBy input arity");
    let (locals, rest, _) = is_read_values(input, inputs, ctors, constructors,
      @ib_max_nodes(), @ib_max_depth(), store(ListNode.Nil));
    assert_eq!(load(rest), ListNode.Nil, "IxBy trailing input bytes");
    let frame = is_enter(program, functions, entry, locals, inputs);
    (is_machine(program, functions, ctors, constructors, ISControl.Eval(frame),
      store(ListNode.Nil), 0, @ib_max_steps()), ctors, constructors)
  }

  pub fn ixby_objects_exec(p: [G; 8], b: [G; 8], i: [G; 8], o: [G; 8]) {
    let profile_hash = @ib_profile_hash();
    assert_eq!(@b3_pack(profile_hash), p, "IxBy profile commitment");
    let program = ib_load(0, @ib_max_program_bytes());
    let program_hash = @blake3(@ib_domain(1u8, @ib_put_digest(profile_hash, program)));
    assert_eq!(@b3_pack(program_hash), b, "IxBy program commitment");
    let input = ib_load(1, @ib_max_value_bytes());
    let input_hash = @blake3(@ib_domain(2u8, @ib_put_digest(program_hash, input)));
    assert_eq!(@b3_pack(input_hash), i, "IxBy input commitment");
    let (value, ctors, constructors) = is_run(program, input);
    let (body, size, _) = is_output(value, ctors, constructors,
      @ib_max_nodes(), @ib_max_depth(), store(ListNode.Nil));
    let output = @ib_put4([73u8, 88u8, 66u8, 79u8], @ib_put4([0u8; 4], body));
    assert_eq!(u32_less_than(size + 8, @ib_max_value_bytes() + 1), 1, "IxBy output byte capacity");
    let output_hash = @blake3(@ib_domain(3u8, @ib_put_digest(program_hash, output)));
    assert_eq!(@b3_pack(output_hash), o, "IxBy output commitment");
  }
⟧

def objectsToplevel : Except String Aiur.Source.Toplevel := do
  let constants ← (profileConstants objectsProfile).mapError (fun e => s!"profile encoding: {repr e}")
  let source ← (do
    let source ← IxVM.core.merge IxVM.byteStream
    let source ← source.merge IxVM.blake3
    let source ← source.merge MultiStark.goldilocks
    let source ← source.merge constants
    let source ← source.merge scalarInterpreter
    let source ← source.merge controlInterpreter
    source.merge objectsInterpreter).mapError toString
  return source.prune [`ixby_objects_exec]

end Ix.Ixby.AiurBackend
