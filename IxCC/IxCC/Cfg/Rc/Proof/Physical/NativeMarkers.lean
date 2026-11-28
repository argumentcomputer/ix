import IxCC.Cfg.Rc.Native
import IxCC.Cfg.Rc.Proof.Physical.NativeCalls

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Lir

private def markerBlock (callee : Nat) : Lir.Block :=
  {body := #[.call [] callee [.v 0]], term := .ret [.imm 1]}

theorem marker_call {p : Lir.Program} {fd : Lir.Func} {g callee : Nat}
    {env : Lir.Env} {word : Word} {entry : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Word}
    (function : p.funcs[g]? = some fd)
    (block : fd.blocks[0]? = some (markerBlock callee))
    (value : env[0]? = some word)
    (enter : Lir.enter p callee [word] = some entry) :
    Lir.step p {mem, ctx, stack := {fn := g, label := 0, pos := 0, env} :: rest} =
      .next {mem, ctx, stack := entry :: {fn := g, label := 0, pos := 1, env, dsts := []} :: rest} true := by
  apply Lir.step_call function block (by simp [markerBlock]) rfl
    (vs := [word])
  · simp [Lir.evalArgs, Lir.Arg.eval, value]
  · exact enter

theorem increment_wrapper_call {p : Lir.Program} {g callee : Nat}
    {env : Lir.Env} {word : Word} {entry : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Word}
    (function : p.funcs[g]? = some (incrementWrapper callee))
    (value : env[0]? = some word)
    (enter : Lir.enter p callee [word] = some entry) :
    Lir.step p {mem, ctx, stack := {fn := g, label := 0, pos := 0, env} :: rest} =
      .next {mem, ctx, stack := entry :: {fn := g, label := 0, pos := 1, env, dsts := []} :: rest} true :=
  marker_call function rfl value enter

theorem decrement_wrapper_call {p : Lir.Program} {g callee : Nat}
    {env : Lir.Env} {word : Word} {entry : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Word}
    (function : p.funcs[g]? = some (decrementWrapper callee))
    (value : env[0]? = some word)
    (enter : Lir.enter p callee [word] = some entry) :
    Lir.step p {mem, ctx, stack := {fn := g, label := 0, pos := 0, env} :: rest} =
      .next {mem, ctx, stack := entry :: {fn := g, label := 0, pos := 1, env, dsts := []} :: rest} true :=
  marker_call function rfl value enter

/-- The dummy marker return writes only the suspended caller's reserved
destination. The full modified procedure memory is retained. -/
theorem marker_return {p : Lir.Program} {fd : Lir.Func} {g callee dummy : Nat}
    {env : Lir.Env} {caller : Lir.Frame} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Word}
    (function : p.funcs[g]? = some fd)
    (block : fd.blocks[0]? = some (markerBlock callee))
    (dest : caller.dsts = [dummy]) :
    Lir.step p {mem, ctx, stack := {fn := g, label := 0, pos := 1, env} :: caller :: rest} =
      .next {mem, ctx, stack := {caller with env := caller.env.insert dummy 1, dsts := []} :: rest} false := by
  apply Lir.step_ret_caller (vals := [1]) function block rfl rfl (by simp [Lir.evalArgs, Lir.Arg.eval])
  simp [dest, Lir.bindParams]




end IxCC.Cfg.Rc.Native
