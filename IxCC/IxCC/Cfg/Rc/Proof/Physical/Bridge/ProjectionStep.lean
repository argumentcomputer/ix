import IxCC.Cfg.Rc.Proof.Physical.Bridge.Projection

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs IxCC.Cfg.Rc.Native

/-- A concrete caller instruction, with field identity supplied by actual
source layout facts. The unchanged heap owns no new token at this cutpoint. -/
theorem projection_step
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held live ρf ρo roots)
    {y location refs : Nat} {body : Own.Body}
    (lookup : ρo.get? y = some (.loc location))
    (cell : H.cell? location = some (.live refs .dyn body))
    {addresses : AddressMap} {mem : X86.Memory} {address : Lir.Word}
    (physical : LiveCell addresses mem address refs body)
    {P : Lir.Program} {caller : Lir.Frame} {callers : List Lir.Frame}
    {function : Lir.Func} {block : Lir.Block} {bound : Nat}
    (registers : EnvWordsBelow addresses bound ρo caller.env)
    (parentRegister : caller.env[y]? = some address)
    (x i : Nat) (value : RVal) (fresh : x ∉ live)
    (field : body.fields[i]? = some value) (tables : Own.Tables) (context : Lir.Word)
    (functionLookup : P.funcs[caller.fn]? = some function)
    (blockLookup : function.blocks[caller.label]? = some block)
    (position : caller.pos < block.body.size)
    (statement : block.body[caller.pos] = .assign x
      (.load .w64 .zero (Rt.Lower.mem y ((8+8*i : Nat) : Int)))) :
    ∃ word, valueWord addresses value = some word ∧
      Own.evalRhs .rc tables ρo H (.proj y body.ctor.key i) = .ok (value, H) ∧
      Lir.step P {mem, ctx := context, stack := caller :: callers} =
        .next {mem, ctx := context, stack := {caller with
          pos := caller.pos+1
          env := caller.env.insert x word} :: callers} false ∧
      Tokens H external held live ρf (ρo.insert x value) roots ∧
      EnvWordsBelow addresses bound (ρo.insert x value) (caller.env.insert x word) ∧
      CanDup H value := by
  obtain ⟨word, represented, source, load, tokens, words, permission⟩ :=
    projection_field before lookup cell physical registers parentRegister x i value fresh field tables context
  refine ⟨word, represented, source, ?_, tokens, words, permission⟩
  apply Lir.step_stmt functionLookup blockLookup position statement (by rfl)
  simp only [Lir.Stmt.exec, load, Option.bind_eq_bind, Option.bind_some]


end IxCC.Cfg.Rc.Proof.Physical.Bridge
