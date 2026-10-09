import Compilatrix.Cfg.Rc.Proof.Physical.Publish

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Compilatrix.Lir

theorem allocation_call {p : Lir.Program} {g allocator fields : Nat}
    {env : Lir.Env} {entry : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Word}
    (function : p.funcs[g]? = some (allocationWrapper allocator fields))
    (enter : Lir.enter p allocator [] = some entry) :
    Lir.step p {mem, ctx, stack := {fn := g, label := 0, pos := 0, env} :: rest} =
      .next {mem, ctx, stack := entry ::
        {fn := g, label := 0, pos := 1, env, dsts := [fields]} :: rest} true := by
  apply Lir.step_call function rfl (by simp [allocationWrapper]) rfl (vs := [])
  · rfl
  · exact enter

theorem allocation_return {p : Lir.Program} {g allocator fields destination : Nat}
    {env : Lir.Env} {address : Word} {caller : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Word}
    (function : p.funcs[g]? = some (allocationWrapper allocator fields))
    (value : env[fields]? = some address) (dest : caller.dsts = [destination]) :
    Lir.step p {mem, ctx, stack :=
      {fn := g, label := 0, pos := 1 + fields, env} :: caller :: rest} =
      .next {mem, ctx, stack := {caller with env := caller.env.insert destination address, dsts := []} :: rest} false := by
  apply Lir.step_ret_caller (vals := [address]) function rfl
    (by simp [allocationWrapper, Nat.add_comm]) rfl
    (by simp [Lir.evalArgs, Lir.Arg.eval, value])
  simp [dest, Lir.bindParams]



end Compilatrix.Cfg.Rc.Native
