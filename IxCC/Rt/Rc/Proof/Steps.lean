import IxCC.Rt.Rc.Procs
import IxCC.Lir.Semantics

namespace IxCC.Rt.Rc.Procs
open Lir

/-- Literal first-block operational obligation: an immediate never reads
memory. This is one case of the pending full increment theorem. -/
theorem inc_immediate_step (mem : X86.Memory) (ctx value : Word) (env : Env)
    (hlookup : env[0]? = some value)
    (himmediate : Cond.holds .tnz .w64 value 1 = true) :
    step { funcs := #[inc], main := 0 }
      { mem, ctx, stack := [{ fn := 0, label := 0, pos := 0, env }] } =
    .next { mem, ctx, stack := [{ fn := 0, label := 5, pos := 0, env }] } false := by
  simp [step, inc, v, i, to, Arg.eval, evalArgs, takeEdge, bindParams, hlookup, himmediate]

/-- The shared success exit returns no tokens and exactly the current memory. -/
theorem inc_return_step (mem : X86.Memory) (ctx : Word) (env : Env) :
    step { funcs := #[inc], main := 0 }
      { mem, ctx, stack := [{ fn := 0, label := 5, pos := 0, env }] } =
    .done [] mem := by
  simp [step, inc, evalArgs]

/-- Overflow exit is the existing heap resource outcome, not stuck or trap. -/
theorem inc_overflow_step (mem : X86.Memory) (ctx : Word) (env : Env) :
    step { funcs := #[inc], main := 0 }
      { mem, ctx, stack := [{ fn := 0, label := 4, pos := 0, env }] } =
    .fail .heap := by
  simp [step, inc]

end IxCC.Rt.Rc.Procs
