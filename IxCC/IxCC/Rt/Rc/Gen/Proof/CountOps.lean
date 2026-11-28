import IxCC.Rt.Rc.Gen.Procs
import IxCC.Rt.Proof.Mem

/-! Actual machine-memory transition at the mutating increment/shared-dec
blocks. These connect the code to a four-byte write; complete entry-to-exit
execution and the heap count representation theorem remain separate gates. -/
namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem inc_add_step (mem : X86.Memory) (context count : Word) (env : Env)
    (hc : env[1]? = some count) :
    step { funcs := #[inc], main := 0 }
      { mem, ctx := context, stack := [{ fn := 0, label := 3, pos := 0, env }] } =
    .next { mem, ctx := context, stack := [{
      fn := 0, label := 3, pos := 1
      env := env.insert 2 (X86.Width.w32.truncate (count + 1)) }] } false := by
  simp [step, inc, v, i, Stmt.exec, Rhs.eval, Arg.eval, BinOp.eval, hc]

theorem inc_store_step (mem : X86.Memory) (context address count : Word) (env : Env)
    (ha : env[0]? = some address) (hc : env[2]? = some count)
    (hw : ∀ j < 4, mem.writable ((address + 4) + UInt64.ofNat j) = true) :
    step { funcs := #[inc], main := 0 }
      { mem, ctx := context, stack := [{ fn := 0, label := 3, pos := 1, env }] } =
    .next {
      mem := mem.write .w32 (address + 4) count, ctx := context
      stack := [{ fn := 0, label := 3, pos := 2, env }] } false := by
  have hs := write?_ok (w := .w32) (v := count) hw
  simp [step, inc, v, cellAddr, Stmt.exec, Addr.eval, Arg.eval, dispWord, ha, hc, hs]

theorem dec_sub_step (mem : X86.Memory) (context count : Word) (env : Env)
    (hc : env[3]? = some count) :
    step { funcs := #[dec], main := 0 }
      { mem, ctx := context, stack := [{ fn := 0, label := 4, pos := 0, env }] } =
    .next { mem, ctx := context, stack := [{
      fn := 0, label := 4, pos := 1
      env := env.insert 4 (X86.Width.w32.truncate (count - 1)) }] } false := by
  simp [step, dec, v, i, Stmt.exec, Rhs.eval, Arg.eval, BinOp.eval, hc]

theorem dec_store_step (mem : X86.Memory) (context address count : Word) (env : Env)
    (ha : env[1]? = some address) (hc : env[4]? = some count)
    (hw : ∀ j < 4, mem.writable ((address + 4) + UInt64.ofNat j) = true) :
    step { funcs := #[dec], main := 0 }
      { mem, ctx := context, stack := [{ fn := 0, label := 4, pos := 1, env }] } =
    .next {
      mem := mem.write .w32 (address + 4) count, ctx := context
      stack := [{ fn := 0, label := 4, pos := 2, env }] } false := by
  have hs := write?_ok (w := .w32) (v := count) hw
  simp [step, dec, v, cellAddr, Stmt.exec, Addr.eval, Arg.eval, dispWord, ha, hc, hs]





end IxCC.Rt.Rc.Gen
