import IxCC.Cfg.Rc.Proof.Physical.Bridge.IncrementCursor

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs IxCC.Cfg.Rc.Native

/-- Execute the actual two-argument inc1 call. The second operand is the real
lowered tagged literal3. Count room is absent from the premises; failure is
the actual terminal heap-resource outcome through both call boundaries. -/
theorem increment_instruction
    {H : Heap} {external : Nat → Nat} {held carry roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {x : Fir.Var}
    (before : Tokens H external (carry ++ held) live ρf ρo roots) (member : x ∈ live)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (idle : ReleaseInvariant H addresses mem (holdRoots external (roots ++ carry ++ held)) none []
      context base bump limit slots lists)
    {P : Lir.Program} {wrapper procedure dummy bound : Nat}
    (wrapperLookup : P.funcs[wrapper]? = some (incrementWrapper procedure))
    (procedureLookup : P.funcs[procedure]? = some Rt.Rc.Procs.inc)
    (caller : Lir.Frame) (callers : List Lir.Frame)
    {function : Lir.Func} {block : Lir.Block}
    (functionLookup : P.funcs[caller.fn]? = some function)
    (blockLookup : function.blocks[caller.label]? = some block)
    (position : caller.pos < block.body.size)
    (statement : block.body[caller.pos] = .call [dummy] wrapper [.v x, .imm 3])
    (registers : EnvWordsBelow addresses bound ρo caller.env)
    (real : x < bound) (reserved : bound ≤ dummy) :
    ∃ value H', ρo.get? x = some value ∧
      Own.Plain.evalAction ρo H (.inc x 1) = .ok H' ∧
      Tokens H' external ((value :: carry) ++ held) live ρf ρo roots ∧
      ((∃ mem', ReleaseInvariant H' addresses mem'
          (holdRoots external (roots ++ (value :: carry) ++ held)) none []
          context base bump limit slots lists ∧
          Sem.Star (Lir.semStep P)
            {mem, ctx := context, stack := caller :: callers} 2
            {mem := mem', ctx := context,
              stack := {caller with
                pos := caller.pos+1
                env := caller.env.insert dummy 1
                dsts := []} :: callers} ∧
          EnvWordsBelow addresses bound ρo (caller.env.insert dummy 1)) ∨
        Sem.Reaches (Lir.semStep P)
          {mem, ctx := context, stack := caller :: callers} 2 (.resource .heap)) := by
  obtain ⟨value, logical, lookup, _, _⟩ := before.den x member
  obtain ⟨word, _, register⟩ := registers x value real lookup
  let wrapperEnv : Lir.Env := (({} : Lir.Env).insert 0 word).insert 1 3
  let entry : Lir.Frame := {fn := wrapper, label := 0, pos := 0, env := wrapperEnv}
  let suspended : Lir.Frame := {caller with pos := caller.pos+1, dsts := [dummy]}
  have enter : Lir.enter P wrapper [word, 3] = some entry := by
    simp [Lir.enter, wrapperLookup, incrementWrapper, Lir.bindParams, entry, wrapperEnv]
  have args : Lir.evalArgs caller.env [.v x, .imm 3] = some [word, 3] := by
    simp [Lir.evalArgs, Lir.Arg.eval, register]
  have callStep := Lir.step_call (p := P) (mem := mem) (ctx := context)
    (fr := caller) (rest := callers) functionLookup blockLookup position statement args enter
  have argument : wrapperEnv[0]? = suspended.env[x]? := by
    change ((({} : Lir.Env).insert 0 word).insert 1 3)[0]? = caller.env[x]?
    rw [Lir.env_insert_ne _ _ (by decide : (1 : Nat) ≠ 0), Lir.env_insert_self]
    exact register.symm
  obtain ⟨value', H', lookup', action, tokens, outcome⟩ :=
    increment_wrapper_tokens before member idle wrapperLookup procedureLookup suspended callers
      registers real reserved argument rfl
  refine ⟨value', H', lookup', action, tokens, ?_⟩
  rcases outcome with ⟨mem', restored, trace, represented⟩ | failure
  · refine .inl ⟨mem', restored, ?_, represented⟩
    have joined := (Sem.Star.single (Lir.semStep_next.mpr callStep)).trans trace
    simpa only [entry, suspended, Bool.toNat_true] using joined
  · have joined := Sem.Reaches.star (Sem.Star.single (Lir.semStep_next.mpr callStep)) failure
    exact .inr (by simpa only [entry, suspended, Bool.toNat_true] using joined)


end IxCC.Cfg.Rc.Proof.Physical.Bridge
