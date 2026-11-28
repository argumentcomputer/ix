import IxCC.Cfg.Rc.Proof.Physical.Bridge.FramedWrapper
import IxCC.Rt.Proof.Chunk

/-! Raw pre-split instruction identity. Final program lookup/split composition
belongs to H3Interface. No instruction simulation is assumed by these facts. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC

theorem consume_decrement (P : Cfg.Rc.Program) (layout : Cfg.Rc.Native.Layout)
    (dummy x : Nat) :
    Cfg.Rc.Native.consume P layout (Cfg.Rc.marker P.base.size dummy (.dec x)) =
      .ok (Cfg.Rc.marker P.base.size dummy (.dec x)) := by
  simp [Cfg.Rc.Native.consume, Cfg.Rc.reserved_marker, Cfg.Rc.decode_marker, pure, Except.pure]

/-- Actual ordinary Rt lowering emits exactly the marker wrapper call, with
the raw variable operand and the checked reserved dummy result destination. -/
theorem lower_decrement (f : Fir.FunId) (tables : Rt.Lower.Tables)
    (limit dummy x : Nat) (state : Rt.Lower.St) :
    (Rt.Lower.instr f tables (Cfg.Rc.marker limit dummy (.dec x))).run state =
      .ok (true, {state with acc := Lir.Stmt.call [dummy] (limit+1) [.v x] :: state.acc}) := rfl

/-- The actual completed lowering layout supplies a concrete block prefix.
The next statement is the decrement call, at the original acc.length. -/
theorem decrement_cursor {f off : Nat} {function : Lir.Func}
    {starts : Src.NatMap Nat} {blocks : List Rt.Lower.PBlock}
    (layout : Rt.Proof.Holds f function off starts blocks)
    {state : Rt.Lower.St} (limit dummy x : Nat)
    (extension : Rt.Proof.Ext blocks
      {state with
        acc := [Lir.Stmt.call [dummy] (limit+1) [.v x]].reverse ++ state.acc
        fresh := state.fresh})
    (opened : Rt.Proof.Open state) :
    ∃ block suffix, function.blocks[off+state.cur]? = some block ∧
      block.params = state.params ∧
      block.body.toList = state.acc.reverse ++ [.call [dummy] (limit+1) [.v x]] ++ suffix :=
  Rt.Proof.holds_open layout _ state.fresh extension opened




end IxCC.Cfg.Rc.Proof.Physical.Bridge
