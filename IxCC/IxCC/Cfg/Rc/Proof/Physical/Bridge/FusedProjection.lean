import IxCC.Cfg.Rc.Proof.Physical.Bridge.Projection
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedWords

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Rt.Rc
open IxCC IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs IxCC.Cfg.Rc.Native

/-- A projection only needs its actually read parent register. Unrelated
omitted comparison results do not block this concrete native instruction. -/
theorem fused_projection_step
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held live ρf ρo roots)
    {y location refs : Nat} {body : Own.Body}
    (lookup : ρo.get? y = some (.loc location))
    (cell : H.cell? location = some (.live refs .dyn body)) (scanned : body.ctor.nscalar = 0)
    {addresses : AddressMap} {mem : X86.Memory} (heapLive : Gen.HeapLive H addresses mem)
    {P : Lir.Program} {caller : Lir.Frame} {callers : List Lir.Frame}
    {function : Lir.Func} {block : Lir.Block} {bound : Nat} {D : Nat → Prop}
    (registers : FusedWords addresses D bound ρo caller.env) (liveParent : ¬ D y)
    (x i : Nat) (value : RVal) (fresh : x ∉ live) (real : x < bound)
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
      FusedWords addresses D bound (ρo.insert x value) (caller.env.insert x word) ∧
      CanDup H value := by
  obtain ⟨_, address, placed, physical⟩ := heapLive.cell location refs .dyn body cell
  obtain ⟨parentWord, parentRep, parentRegister⟩ := registers.word lookup liveParent
  have equal : parentWord = address := Option.some.inj (parentRep.symm.trans placed)
  subst parentWord
  have scannedField : i < body.ctor.nobj := by
    have := physical.arity
    have := (List.getElem?_eq_some_iff.mp field).1
    omega
  obtain ⟨word, represented, bytes⟩ := physical.scanned field scannedField
  have load : Lir.Rhs.eval caller.env mem context
      (.load .w64 .zero (Rt.Lower.mem y ((8+8*i : Nat) : Int))) = some word := by
    have addressEval : Lir.Addr.eval caller.env context (Rt.Lower.mem y ((8+8*i : Nat) : Int)) =
        some (address + UInt64.ofNat (8+8*i)) := by
      simp only [Lir.Addr.eval, Rt.Lower.mem, Option.bind_eq_bind,
        Option.bind_some, Lir.option_pure, parentRegister]
      rw [Lir.dispWord_ofNat]
      simp
    simp only [Lir.Rhs.eval, addressEval, Option.bind_eq_bind, Option.bind_some,
      Lir.loadWord, bytes.read64]
  refine ⟨word, represented, ?_, ?_, before.borrow x value fresh,
    registers.bind real represented, canDup_field before.balance cell (List.mem_of_getElem? field)⟩
  · simp [Own.evalRhs, lookup, RVal.asCtor, cell, field, Sem.Result.ofOption, Sem.Result.map]
  · apply Lir.step_stmt functionLookup blockLookup position statement (by rfl)
    simp only [Lir.Stmt.exec, load, Option.bind_eq_bind, Option.bind_some]


end IxCC.Cfg.Rc.Proof.Physical.Bridge
