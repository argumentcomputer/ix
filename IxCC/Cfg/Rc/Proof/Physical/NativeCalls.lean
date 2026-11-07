import IxCC.Lir.Proof.Steps

/-! Memory-changing ordinary procedure calls. Unlike the older scalar Nat
procedure helper, the final memory may differ from the caller's initial memory.
The premises are actual Lir steps and traces, with no compiler simulation
oracle. H2's ambient procedure theorem supplies the internal trace. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Lir

theorem call_return {p : Lir.Program} {before after : X86.Memory} {ctx : Word}
    {caller callee terminal : Lir.Frame} {rest : List Lir.Frame} {dsts : List VReg}
    {values : List Word} {resultEnv : Lir.Env} {cost : Nat} {fd : Lir.Func}
    {block : Lir.Block} {args : List Lir.Arg}
    (callStep : Lir.step p {mem := before, ctx, stack := caller :: rest} =
      .next {mem := before, ctx, stack := callee ::
        {caller with pos := caller.pos + 1, dsts} :: rest} true)
    (body : Sem.Star (Lir.semStep p)
      {mem := before, ctx, stack := callee :: {caller with pos := caller.pos + 1, dsts} :: rest}
      cost
      {mem := after, ctx, stack := terminal :: {caller with pos := caller.pos + 1, dsts} :: rest})
    (function : p.funcs[terminal.fn]? = some fd)
    (blockLookup : fd.blocks[terminal.label]? = some block)
    (position : terminal.pos = block.body.size)
    (returns : block.term = .ret args)
    (read : Lir.evalArgs terminal.env args = some values)
    (bind : Lir.bindParams caller.env dsts values = some resultEnv) :
    Sem.Star (Lir.semStep p) {mem := before, ctx, stack := caller :: rest} (1 + cost)
      {mem := after, ctx, stack :=
        {caller with pos := caller.pos + 1, env := resultEnv, dsts := []} :: rest} := by
  have finish := Lir.step_ret_caller (p := p) (mem := after) (ctx := ctx)
    (caller := {caller with pos := caller.pos + 1, dsts}) (rest' := rest)
    function blockLookup position returns read bind
  have combined := (Sem.Star.single (Lir.semStep_next.mpr callStep)).trans
    (body.trans (Sem.Star.single (Lir.semStep_next.mpr finish)))
  simpa using combined

/-- A zero-result procedure restores every caller register even when it
mutates memory. Its call costs one clock charge plus its actual internal cost. -/
theorem call_return_zero {p : Lir.Program} {before after : X86.Memory} {ctx : Word}
    {caller callee terminal : Lir.Frame} {rest : List Lir.Frame} {cost : Nat}
    {fd : Lir.Func} {block : Lir.Block} {args : List Lir.Arg}
    (callStep : Lir.step p {mem := before, ctx, stack := caller :: rest} =
      .next {mem := before, ctx, stack := callee ::
        {caller with pos := caller.pos + 1, dsts := []} :: rest} true)
    (body : Sem.Star (Lir.semStep p)
      {mem := before, ctx, stack := callee :: {caller with pos := caller.pos + 1, dsts := []} :: rest}
      cost
      {mem := after, ctx, stack := terminal :: {caller with pos := caller.pos + 1, dsts := []} :: rest})
    (function : p.funcs[terminal.fn]? = some fd)
    (blockLookup : fd.blocks[terminal.label]? = some block)
    (position : terminal.pos = block.body.size)
    (returns : block.term = .ret args)
    (read : Lir.evalArgs terminal.env args = some []) :
    Sem.Star (Lir.semStep p) {mem := before, ctx, stack := caller :: rest} (1 + cost)
      {mem := after, ctx, stack := {caller with pos := caller.pos + 1, dsts := []} :: rest} :=
  call_return callStep body function blockLookup position returns read rfl



end IxCC.Cfg.Rc.Native
