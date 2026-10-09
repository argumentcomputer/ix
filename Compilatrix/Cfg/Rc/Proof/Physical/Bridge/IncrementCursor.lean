import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.IncrementWrapper
import Compilatrix.Rt.Proof.Chunk

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix

theorem consume_increment (P : Cfg.Rc.Program) (layout : Cfg.Rc.Native.Layout)
    (dummy x : Nat) :
    Cfg.Rc.Native.consume P layout (Cfg.Rc.marker P.base.size dummy (.inc x 1)) =
      .ok (Cfg.Rc.marker P.base.size dummy (.inc x 1)) := by
  simp [Cfg.Rc.Native.consume, Cfg.Rc.reserved_marker, Cfg.Rc.decode_marker, pure, Except.pure]

theorem consume_increment_two_refused (P : Cfg.Rc.Program) (layout : Cfg.Rc.Native.Layout)
    (dummy x : Nat) :
    Cfg.Rc.Native.consume P layout (Cfg.Rc.marker P.base.size dummy (.inc x 2)) =
      .error "native RC accepts only well-formed inc1/dec markers" := by
  simp [Cfg.Rc.Native.consume, Cfg.Rc.reserved_marker, Cfg.Rc.decode_marker,
    throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- Actual literal1 encoding, rather than a raw untagged count operand. -/
theorem lower_increment (f : Fir.FunId) (tables : Rt.Lower.Tables)
    (limit dummy x : Nat) (state : Rt.Lower.St) :
    (Rt.Lower.instr f tables (Cfg.Rc.marker limit dummy (.inc x 1))).run state =
      .ok (true, {state with acc := Lir.Stmt.call [dummy] limit [.v x, .imm 3] :: state.acc}) := rfl

theorem increment_cursor {f off : Nat} {function : Lir.Func}
    {starts : Src.NatMap Nat} {blocks : List Rt.Lower.PBlock}
    (layout : Rt.Proof.Holds f function off starts blocks)
    {state : Rt.Lower.St} (limit dummy x : Nat)
    (extension : Rt.Proof.Ext blocks
      {state with
        acc := [Lir.Stmt.call [dummy] limit [.v x, .imm 3]].reverse ++ state.acc
        fresh := state.fresh})
    (opened : Rt.Proof.Open state) :
    ∃ block suffix, function.blocks[off+state.cur]? = some block ∧
      block.params = state.params ∧
      block.body.toList = state.acc.reverse ++ [.call [dummy] limit [.v x, .imm 3]] ++ suffix :=
  Rt.Proof.holds_open layout _ state.fresh extension opened





end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
