import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.FusedOperands
import Compilatrix.Rt.Proof.Rel

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Rt Compilatrix.Rt.Rc.Procs
open Compilatrix.Rt.Proof (Fused FusedDone LiveArg)

theorem fused_arg_insert_irrel
    {D : Nat → Prop} {source : Own.Env} {x : Nat} {value : Own.RVal} {arg : Fir.Arg}
    (live : LiveArg D arg) (omitted : D x) :
    Own.evalArg (source.insert x value) arg = Own.evalArg source arg := by
  cases arg with
  | var y =>
    have different : y ≠ x := by intro equal; subst y; exact live x rfl omitted
    exact Src.NatMap.get?_insert_ne _ _ different
  | lit _ | erased => rfl

theorem fused_args_insert_irrel
    {D : Nat → Prop} {source : Own.Env} {x : Nat} {value : Own.RVal} {args : List Fir.Arg}
    (live : ∀ arg ∈ args, LiveArg D arg) (omitted : D x) :
    Own.evalArgs (source.insert x value) args = Own.evalArgs source args := by
  induction args with
  | nil => rfl
  | cons a args ih =>
    simp only [Own.evalArgs]
    rw [fused_arg_insert_irrel (live a (by simp)) omitted,
      ih (fun arg member => live arg (by simp [member]))]

/-- A real fusion receipt and the actual last source instruction identify
the omitted destination, without any assumption about its target register. -/
theorem fused_result_receipt
    {tables : Lower.Tables} {function : Cfg.Fun} {index : Nat} {block : Cfg.Block}
    (blockLookup : function.blocks[index]? = some block)
    {init : List Cfg.Instr} {cond : Lir.Cond} {a b : Fir.Arg}
    (receipt : Lower.fusable tables (Lower.useCounts function) block = some (init, cond, a, b))
    {x : Nat} {op : Lam.Prim}
    (body : block.body = init ++ [.bind x (.fir (.prim op [a, b]))]) :
    Fused tables function x ∧ x < Rt.Proof.supOf function := by
  obtain ⟨y, otherOp, alts, default, otherBody, _, term, _, _⟩ := Rt.Proof.fusable_some receipt
  have equal := List.append_cancel_left (body.symm.trans otherBody)
  simp only [List.cons.injEq, Cfg.Instr.bind.injEq, Own.Rhs.fir.injEq,
    Fir.Rhs.prim.injEq, and_true] at equal
  obtain ⟨rfl, rfl⟩ := equal
  refine ⟨⟨index, block, init, cond, a, b, alts, default, blockLookup, receipt, term⟩, ?_⟩
  apply Rt.Proof.defs_lt_sup blockLookup
  simp only [Cfg.Check.blockDefs, Cfg.Check.instrDefs, List.mem_append, List.mem_map]
  right
  exact ⟨.bind x (.fir (.prim op [a, b])), by rw [body]; simp, rfl⟩

/-- The actual source comparison completes with no physical register write.
It supplies the existing production FusedDone invariant for the subsequent
branch and retains the dynamic-address relation. Policy is irrelevant to
the pure comparison, so this theorem uses the actual RC source effect. -/
theorem fused_comparison_complete
    {addresses : AddressMap} {tables : Lower.Tables} {function : Cfg.Fun}
    {index : Nat} {block : Cfg.Block} (blockLookup : function.blocks[index]? = some block)
    {frame : Cfg.Frame} {target : Lir.Env} {bound : Nat}
    (related : FusedWords addresses (Fused tables function) bound frame.env target)
    {init : List Cfg.Instr} {cond : Lir.Cond} {a b : Fir.Arg}
    (receipt : Lower.fusable tables (Lower.useCounts function) block = some (init, cond, a, b))
    {x : Nat} {op : Lam.Prim}
    (body : block.body = init ++ [.bind x (.fir (.prim op [a, b]))])
    (real : x < bound)
    {heap heap' : Own.Heap} {value : Own.RVal}
    (effect : Own.evalRhs .rc (Rt.Proof.ownTables tables) frame.env heap
      (.fir (.prim op [a, b])) = .ok (value, heap')) :
    heap' = heap ∧
      FusedWords addresses (Fused tables function) bound
        (frame.env.insert x value) target ∧
      FusedDone tables function block {frame with rest := [], env := frame.env.insert x value} := by
  obtain ⟨omitted, _⟩ := fused_result_receipt blockLookup receipt body
  have instruction : Cfg.Instr.bind x (.fir (.prim op [a, b])) ∈ block.body := by rw [body]; simp
  have live := fused_prim_live (tables := tables) blockLookup instruction
  have sameEffect : Own.evalRhs .immortal (Rt.Proof.ownTables tables) frame.env heap
      (.fir (.prim op [a, b])) = .ok (value, heap') := effect
  obtain ⟨sameHeap, values, evaluated, result⟩ := Rt.Proof.evalRhs_prim sameEffect
  have pair : ∃ va vb, values = [va, vb] := by
    cases ha : Own.evalArg frame.env a <;> cases hb : Own.evalArg frame.env b <;>
      simp [Own.evalArgs, ha, hb] at evaluated
    exact ⟨_, _, evaluated.symm⟩
  obtain ⟨va, vb, rfl⟩ := pair
  refine ⟨sameHeap, related.bind_omitted real omitted value, ?_⟩
  intro init' cond' a' b' receipt' _
  rw [receipt] at receipt'
  simp only [Option.some.injEq, Prod.mk.injEq] at receipt'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := receipt'
  refine ⟨x, op, va, vb, value, body, ?_, result, Src.NatMap.get?_insert_self ..⟩
  rw [fused_args_insert_irrel live omitted]
  exact evaluated





end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
