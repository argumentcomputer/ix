module
public import Ix.Ixby.Aiur.Scalar

/-! Program-independent scalar CEK control. Canonical bytes are decoded into
immutable tables, every block is admitted, and a separate machine fetches from
those tables. No decoded table, frame, continuation, or execution trace is
accepted as advice. Constructors/PAPs and general application remain excluded.

`Refinement.lean` specifies the logical reversed-frame/stack representation.
It does not prove the Aiur compiler, memory argument, or this circuit sound. -/

public section

namespace Ix.Ixby.AiurBackend

def controlInterpreter := ⟦
  enum ICOperand { Local(G), Literal(IBValue) }
  type ICOperands = List‹ICOperand›
  enum ICOp {
    Copy(ICOperand),
    Primitive(G, ICOperands, G),
    Call(G, ICOperands, G)
  }
  enum ICInstr {
    Let(ICOp, G),
    Ret(ICOperand),
    Tail(G, ICOperands, G),
    Branch(ICOperand, G, G)
  }
  enum ICBlock { Mk(G, ICInstr) }
  type ICBlocks = List‹ICBlock›
  enum ICFunction { Mk(G, G, G, ICBlocks) }
  type ICFunctions = List‹ICFunction›

  -- Locals and continuations are top/newest first. Function/block/operand
  -- tables retain wire order. Function and block IDs are logical indices;
  -- all physical pointers stay private to Aiur's typed memory argument.
  enum ICFrame { Mk(G, G, IBLocals, G) }
  type ICStack = List‹ICFrame›
  enum ICControl { Eval(ICFrame), Ret(IBValue) }
  enum ICAction { Value(IBValue), Call(G, IBLocals, G) }

  fn ic_primitive_arity(opcode: G) -> G {
    match opcode {
      0 => 2, 3 => 2, 4 => 2, 5 => 2, 9 => 2, 10 => 2,
      13 => 1, 14 => 2, 15 => 2, 16 => 2, 17 => 1, 18 => 2,
      21 => 2, 22 => 2, 23 => 2, 24 => 1, 25 => 2, 26 => 2,
      27 => 1, 28 => 1,
      _ => assert_eq!(0, 1, "IxBy unsupported primitive"); 0,
    }
  }

  fn ic_read_operand(bytes: ByteStream, locals: G) -> (ICOperand, ByteStream) {
    let (tag, rest) = ib_byte(bytes);
    match tag {
      0 =>
        let (index, rest) = @ib_u32(rest);
        assert_eq!(u32_less_than(index, locals), 1, "IxBy code local index");
        (ICOperand.Local(index), rest),
      1 =>
        let (value, rest) = ib_scalar(rest);
        (ICOperand.Literal(value), rest),
      2 => (ICOperand.Literal(IBValue.Erased), rest),
      _ => assert_eq!(0, 1, "IxBy unknown operand");
        (ICOperand.Literal(IBValue.Erased), rest),
    }
  }

  fn ic_read_args(bytes: ByteStream, remaining: G, locals: G) -> (ICOperands, ByteStream) {
    match remaining {
      0 => (store(ListNode.Nil), bytes),
      _ =>
        let (arg, rest) = ic_read_operand(bytes, locals);
        let (args, rest) = ic_read_args(rest, remaining - 1, locals);
        (store(ListNode.Cons(arg, args)), rest),
    }
  }

  fn ic_read_operands(bytes: ByteStream, locals: G) -> (ICOperands, G, ByteStream) {
    let (count, rest) = @ib_u32(bytes);
    assert_eq!(u32_less_than(count, @ib_max_operands() + 1), 1, "IxBy code operand capacity");
    let (args, rest) = ic_read_args(rest, count, locals);
    (args, count, rest)
  }

  fn ic_read_op(bytes: ByteStream, self: G, locals: G) -> (ICOp, ByteStream) {
    let (tag, rest) = ib_byte(bytes);
    match tag {
      0 =>
        let (arg, rest) = ic_read_operand(rest, locals);
        (ICOp.Copy(arg), rest),
      1 =>
        let (opcode, rest) = ib_byte(rest);
        let arity = ic_primitive_arity(to_field(opcode));
        let (args, count, rest) = ic_read_operands(rest, locals);
        assert_eq!(count, arity, "IxBy primitive arity");
        (ICOp.Primitive(to_field(opcode), args, count), rest),
      5 =>
        let (callee, rest) = @ib_u32(rest);
        let (args, count, rest) = ic_read_operands(rest, locals);
        (ICOp.Call(callee, args, count), rest),
      6 =>
        let (args, count, rest) = ic_read_operands(rest, locals);
        (ICOp.Call(self, args, count), rest),
      _ => assert_eq!(0, 1, "IxBy unsupported operation");
        (ICOp.Copy(ICOperand.Literal(IBValue.Erased)), rest),
    }
  }

  fn ic_read_instr(bytes: ByteStream, self: G, locals: G) -> (ICInstr, ByteStream) {
    let (tag, rest) = ib_byte(bytes);
    match tag {
      0 =>
        let (op, rest) = ic_read_op(rest, self, locals);
        let (next, rest) = @ib_u32(rest);
        (ICInstr.Let(op, next), rest),
      1 =>
        let (arg, rest) = ic_read_operand(rest, locals);
        (ICInstr.Ret(arg), rest),
      2 =>
        let (callee, rest) = @ib_u32(rest);
        let (args, count, rest) = ic_read_operands(rest, locals);
        (ICInstr.Tail(callee, args, count), rest),
      3 =>
        let (args, count, rest) = ic_read_operands(rest, locals);
        (ICInstr.Tail(self, args, count), rest),
      6 =>
        let (condition, rest) = ic_read_operand(rest, locals);
        let (yes, rest) = @ib_u32(rest);
        let (no, rest) = @ib_u32(rest);
        (ICInstr.Branch(condition, yes, no), rest),
      _ => assert_eq!(0, 1, "IxBy unsupported instruction");
        (ICInstr.Ret(ICOperand.Literal(IBValue.Erased)), rest),
    }
  }

  fn ic_read_blocks(bytes: ByteStream, remaining: G, self: G) -> (ICBlocks, ByteStream) {
    match remaining {
      0 => (store(ListNode.Nil), bytes),
      _ =>
        let (locals, rest) = @ib_u32(bytes);
        assert_eq!(u32_less_than(locals, @ib_max_locals() + 1), 1, "IxBy declared local capacity");
        let (instr, rest) = ic_read_instr(rest, self, locals);
        let (blocks, rest) = ic_read_blocks(rest, remaining - 1, self);
        (store(ListNode.Cons(ICBlock.Mk(locals, instr), blocks)), rest),
    }
  }

  fn ic_read_functions(bytes: ByteStream, remaining: G, self: G) -> (ICFunctions, ByteStream) {
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
        let (blocks, rest) = ic_read_blocks(rest, count, self);
        let (functions, rest) = ic_read_functions(rest, remaining - 1, self + 1);
        (store(ListNode.Cons(ICFunction.Mk(arity, entry, count, blocks), functions)), rest),
    }
  }

  fn ic_function(program: ICFunctions, count: G, index: G) -> ICFunction {
    assert_eq!(u32_less_than(index, count), 1, "IxBy function index");
    list_lookup(program, index)
  }

  fn ic_block(blocks: ICBlocks, count: G, index: G) -> ICBlock {
    assert_eq!(u32_less_than(index, count), 1, "IxBy block index");
    list_lookup(blocks, index)
  }

  fn ic_target(blocks: ICBlocks, count: G, index: G, locals: G) {
    let ICBlock.Mk(declared, _) = ic_block(blocks, count, index);
    assert_eq!(declared, locals, "IxBy target frame contract");
  }

  fn ic_check_call(program: ICFunctions, functions: G, callee: G, args: G) {
    let ICFunction.Mk(arity, _, _, _) = ic_function(program, functions, callee);
    assert_eq!(arity, args, "IxBy direct call arity");
  }

  fn ic_check_op(program: ICFunctions, functions: G, op: ICOp) {
    match op {
      ICOp.Copy(_) => (),
      ICOp.Primitive(_, _, _) => (),
      ICOp.Call(callee, _, args) => ic_check_call(program, functions, callee, args),
    }
  }

  -- Admission scans ALL decoded blocks, not just those visited by execution.
  -- Syntax, scalar canonicality, local reads, and primitive arities were
  -- checked while decoding; forward targets/calls can now use the full image.
  fn ic_check_blocks(program: ICFunctions, functions: G, blocks: ICBlocks,
      count: G, rest: ICBlocks, remaining: G) {
    match remaining {
      0 => assert_eq!(load(rest), ListNode.Nil, "IxBy extra decoded blocks"); (),
      _ =>
        let ListNode.Cons(ICBlock.Mk(locals, instr), tail) = load(rest);
        match instr {
          ICInstr.Let(op, target) =>
            ic_check_op(program, functions, op);
            ic_target(blocks, count, target, locals + 1),
          ICInstr.Ret(_) => (),
          ICInstr.Tail(callee, _, args) => ic_check_call(program, functions, callee, args),
          ICInstr.Branch(_, yes, no) =>
            ic_target(blocks, count, yes, locals);
            ic_target(blocks, count, no, locals),
        };
        ic_check_blocks(program, functions, blocks, count, tail, remaining - 1),
    }
  }

  fn ic_check_functions(program: ICFunctions, functions: G, rest: ICFunctions, remaining: G) {
    match remaining {
      0 => assert_eq!(load(rest), ListNode.Nil, "IxBy extra decoded functions"); (),
      _ =>
        let ListNode.Cons(ICFunction.Mk(arity, entry, count, blocks), tail) = load(rest);
        ic_target(blocks, count, entry, arity);
        ic_check_blocks(program, functions, blocks, count, blocks, count);
        ic_check_functions(program, functions, tail, remaining - 1),
    }
  }

  fn ic_operand(operand: ICOperand, locals: IBLocals, count: G) -> IBValue {
    match operand {
      ICOperand.Local(index) =>
        assert_eq!(u32_less_than(index, count), 1, "IxBy runtime local index");
        ib_local(locals, count - (index + 1)),
      ICOperand.Literal(value) => value,
    }
  }

  fn ic_args(args: ICOperands, remaining: G, locals: IBLocals, count: G,
      reversed: IBLocals) -> IBLocals {
    match remaining {
      0 => assert_eq!(load(args), ListNode.Nil, "IxBy extra operands"); reversed,
      _ =>
        let ListNode.Cons(arg, rest) = load(args);
        let value = ic_operand(arg, locals, count);
        ic_args(rest, remaining - 1, locals, count, store(ListNode.Cons(value, reversed))),
    }
  }

  fn ic_op(op: ICOp, locals: IBLocals, count: G) -> ICAction {
    match op {
      ICOp.Copy(arg) => ICAction.Value(ic_operand(arg, locals, count)),
      ICOp.Primitive(opcode, args, arity) =>
        let ListNode.Cons(a, rest) = load(args);
        let a = ic_operand(a, locals, count);
        match arity {
          1 =>
            assert_eq!(load(rest), ListNode.Nil, "IxBy extra unary operand");
            ICAction.Value(ib_unary(opcode, a)),
          2 =>
            let ListNode.Cons(b, rest) = load(rest);
            let b = ic_operand(b, locals, count);
            assert_eq!(load(rest), ListNode.Nil, "IxBy extra binary operand");
            ICAction.Value(ib_binary(opcode, a, b)),
          _ => assert_eq!(0, 1, "IxBy primitive arity"); ICAction.Value(IBValue.Erased),
        },
      ICOp.Call(callee, args, arity) =>
        ICAction.Call(callee, ic_args(args, arity, locals, count, store(ListNode.Nil)), arity),
    }
  }

  fn ic_frame(program: ICFunctions, functions: G, self: G, block: G,
      locals: IBLocals, count: G) -> ICFrame {
    assert_eq!(u32_less_than(count, @ib_max_locals() + 1), 1, "IxBy runtime local capacity");
    let ICFunction.Mk(_, _, blocks, code) = ic_function(program, functions, self);
    ic_target(code, blocks, block, count);
    ICFrame.Mk(self, block, locals, count)
  }

  fn ic_enter(program: ICFunctions, functions: G, callee: G, args: IBLocals, count: G) -> ICFrame {
    let ICFunction.Mk(arity, entry, _, _) = ic_function(program, functions, callee);
    assert_eq!(arity, count, "IxBy runtime call arity");
    ic_frame(program, functions, callee, entry, args, count)
  }

  -- One recursive call per reference transition. In particular an instruction
  -- return produces Ret; popping a saved frame (or halting) takes ANOTHER step.
  -- Fuel and depth start at fixed bounded integers; no guest/advice reset exists.
  fn ic_machine(program: ICFunctions, functions: G, control: ICControl,
      stack: ICStack, depth: G, fuel: G) -> IBValue {
    assert_eq!(eq_zero(fuel), 0, "IxBy exhausted transition budget");
    match control {
      ICControl.Eval(ICFrame.Mk(self, block, locals, count)) =>
        let ICFunction.Mk(_, _, blocks, code) = ic_function(program, functions, self);
        let ICBlock.Mk(declared, instr) = ic_block(code, blocks, block);
        assert_eq!(declared, count, "IxBy runtime frame contract");
        match instr {
          ICInstr.Let(op, next) =>
            match ic_op(op, locals, count) {
              ICAction.Value(value) =>
                let frame = ic_frame(program, functions, self, next,
                  store(ListNode.Cons(value, locals)), count + 1);
                ic_machine(program, functions, ICControl.Eval(frame), stack, depth, fuel - 1),
              ICAction.Call(callee, args, arity) =>
                assert_eq!(u32_less_than(depth, @ib_max_continuations()), 1,
                  "IxBy continuation capacity");
                let saved = ICFrame.Mk(self, next, locals, count);
                let frame = ic_enter(program, functions, callee, args, arity);
                ic_machine(program, functions, ICControl.Eval(frame),
                  store(ListNode.Cons(saved, stack)), depth + 1, fuel - 1),
            },
          ICInstr.Ret(arg) =>
            let value = ic_operand(arg, locals, count);
            ic_machine(program, functions, ICControl.Ret(value), stack, depth, fuel - 1),
          ICInstr.Tail(callee, args, arity) =>
            let values = ic_args(args, arity, locals, count, store(ListNode.Nil));
            let frame = ic_enter(program, functions, callee, values, arity);
            ic_machine(program, functions, ICControl.Eval(frame), stack, depth, fuel - 1),
          ICInstr.Branch(condition, yes, no) =>
            let IBValue.Bool(b) = ic_operand(condition, locals, count);
            let target = match b {
              0 => no, 1 => yes,
              _ => assert_eq!(0, 1, "IxBy non-Boolean branch"); no,
            };
            let frame = ic_frame(program, functions, self, target, locals, count);
            ic_machine(program, functions, ICControl.Eval(frame), stack, depth, fuel - 1),
        },
      ICControl.Ret(value) =>
        match load(stack) {
          ListNode.Nil => assert_eq!(depth, 0, "IxBy terminal stack depth"); value,
          ListNode.Cons(ICFrame.Mk(self, target, locals, count), rest) =>
            assert_eq!(eq_zero(depth), 0, "IxBy invalid return depth");
            let frame = ic_frame(program, functions, self, target,
              store(ListNode.Cons(value, locals)), count + 1);
            ic_machine(program, functions, ICControl.Eval(frame), rest, depth - 1, fuel - 1),
        },
    }
  }

  fn ic_run(program: ByteStream, input: ByteStream) -> IBValue {
    let code = @ib_header(program, 89);
    let (entry, code) = @ib_u32(code);
    let (constructors, code) = @ib_u32(code);
    assert_eq!(constructors, 0, "IxBy constructors excluded");
    let (functions, code) = @ib_u32(code);
    assert_eq!(u32_less_than(functions, @ib_max_functions() + 1), 1, "IxBy function capacity");
    assert_eq!(eq_zero(functions), 0, "IxBy empty program");
    let (program, rest) = ic_read_functions(code, functions, 0);
    assert_eq!(load(rest), ListNode.Nil, "IxBy trailing program bytes");
    ic_check_functions(program, functions, program, functions);
    let ICFunction.Mk(arity, _, _, _) = ic_function(program, functions, entry);
    let input = @ib_header(input, 73);
    let (inputs, input) = @ib_u32(input);
    assert_eq!(inputs, arity, "IxBy input arity");
    assert_eq!(u32_less_than(inputs, @ib_max_nodes() + 1), 1, "IxBy input node capacity");
    let locals = ib_inputs(input, inputs, store(ListNode.Nil));
    let frame = ic_enter(program, functions, entry, locals, inputs);
    ic_machine(program, functions, ICControl.Eval(frame), store(ListNode.Nil), 0, @ib_max_steps())
  }

  pub fn ixby_control_exec(p: [G; 8], b: [G; 8], i: [G; 8], o: [G; 8]) {
    let profile_hash = @ib_profile_hash();
    assert_eq!(@b3_pack(profile_hash), p, "IxBy profile commitment");
    assert_eq!(u32_less_than(0, @ib_max_nodes()), 1, "IxBy output node capacity");
    assert_eq!(u32_less_than(0, @ib_max_depth()), 1, "IxBy value depth capacity");
    let program = ib_load(0, @ib_max_program_bytes());
    let program_hash = @blake3(@ib_domain(1u8, @ib_put_digest(profile_hash, program)));
    assert_eq!(@b3_pack(program_hash), b, "IxBy program commitment");
    let input = ib_load(1, @ib_max_value_bytes());
    let input_hash = @blake3(@ib_domain(2u8, @ib_put_digest(program_hash, input)));
    assert_eq!(@b3_pack(input_hash), i, "IxBy input commitment");
    let (output, size) = ib_output(ic_run(program, input));
    assert_eq!(u32_less_than(size, @ib_max_value_bytes() + 1), 1, "IxBy output byte capacity");
    let output_hash = @blake3(@ib_domain(3u8, @ib_put_digest(program_hash, output)));
    assert_eq!(@b3_pack(output_hash), o, "IxBy output commitment");
  }
⟧

def controlToplevel : Except String Aiur.Source.Toplevel := do
  let constants ← (profileConstants controlProfile).mapError (fun e => s!"profile encoding: {repr e}")
  let source ← (do
    let source ← IxVM.core.merge IxVM.byteStream
    let source ← source.merge IxVM.blake3
    let source ← source.merge MultiStark.goldilocks
    let source ← source.merge constants
    let source ← source.merge scalarInterpreter
    source.merge controlInterpreter).mapError toString
  return source.prune [`ixby_control_exec]

end Ix.Ixby.AiurBackend
