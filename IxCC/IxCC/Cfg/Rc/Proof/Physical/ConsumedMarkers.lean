import IxCC.Cfg.Rc.Proof.Native.ConsumedCursor
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedOperands
import IxCC.Cfg.Rc.Proof.Physical.Bridge.IncrementCursor

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open Spec IxCC.Cfg.Rc.Proof.Physical.Bridge

/-- Operand liveness follows from the actual current consumed instruction
inside the function identified by the cursor, including its true fusion set. -/
theorem consumed_call_live
    {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs lp source target)
    {instruction : Cfg.Instr} {tail : List Cfg.Instr}
    (head : source.rest = instruction :: tail)
    {x callee : Nat} {args : List Fir.Arg}
    (consuming : consume P (layoutOf P) instruction = .ok (.bind x (.fir (.call callee args))))
    {function : Cfg.Fun}
    (sourceLookup : (consumed P pairs).fun? source.fn = some function) :
    ∀ arg ∈ args, Rt.Proof.LiveArg (Rt.Proof.Fused (tablesOf P pairs) function) arg := by
  obtain ⟨actual, rest, decision, _, position⟩ := cursor.next head
  rw [consuming] at decision
  cases decision
  obtain ⟨fd, block, _, _, _, _, _, _, lookup, blockLookup,
    _, _, _, _, _, _, _, _, _, ⟨pre, body⟩, _, _, _⟩ := position
  rw [sourceLookup] at lookup
  cases lookup
  apply fused_call_live (x := x) (callee := callee) blockLookup
  rw [← body]
  simp

/-- A runtime entry already present in the raw program survives the public
release-function append. -/
theorem raw_public_runtime {layout : Layout} {funcs : List Lir.Func} {main index : Nat}
    {function : Lir.Func}
    (lookup : (rawProgram layout funcs main).funcs[index]? = some function) :
    (Public.Spec.rawPublicProgram layout funcs main).funcs[index]? = some function := by
  have bound := (Array.getElem?_eq_some_iff.mp lookup).1
  simp only [Public.Spec.rawPublicProgram, Array.getElem?_push]
  rw [if_neg (Nat.ne_of_lt bound)]
  exact lookup

/-- Both inc entries are derived from the actual raw-source program layout;
no procedure-lookup premise is needed at a source marker. -/
theorem source_stage_increment_runtime (P : Program) (functions : Nat → Lir.Func) (main : Nat) :
    (Public.Spec.sourceStage P functions main).funcs[P.base.size]? =
      some (incrementWrapper (layoutOf P).incProc) ∧
    (Public.Spec.sourceStage P functions main).funcs[(layoutOf P).incProc]? =
      some Rt.Rc.Procs.inc := by
  have length : ((List.range P.base.size).map functions).length = (layoutOf P).sourceCount := by
    simp [layoutOf]
  exact ⟨raw_public_runtime (raw_inc_wrapper length main),
    raw_public_runtime (raw_inc_proc length main)⟩

/-- Convert a proved terminal resource execution to the finite failure form
used by cursor composition. The resource kind is retained in the witness. -/
theorem reaches_resource_fails {lp : Lir.Program} {state : Lir.State} {clock : Nat}
    {resource : Sem.Resource}
    (failed : Sem.Reaches (Lir.semStep lp) state clock (.resource resource)) :
    Sem.Fails (Lir.semStep lp) state := by
  obtain ⟨cost, terminal, trace, _, final⟩ :=
    (Sem.Reaches.iff_final (by simp : (Sem.Result.resource resource :
      Sem.Result (List Lir.Word × X86.Memory)) ≠ .timeout)).mp failed
  refine ⟨cost, terminal, resource, trace, ?_⟩
  generalize outcome : Lir.semStep lp terminal = result at final
  cases final
  rfl





end IxCC.Cfg.Rc.Native
