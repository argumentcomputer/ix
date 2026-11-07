import IxCC.Cfg.Rc.Proof.Physical.Bridge.CtorInvariant
import IxCC.Cfg.Rc.Proof.Native.Fieldless
import IxCC.Rt.Proof.Ops

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc IxCC.Cfg.Rc.Native
open IxCC.Rt.Proof

theorem admitted_ctor_positive {P : Program} {layout : Layout} {x : Nat}
    {ctor : Fir.CtorInfo} {args : List Fir.Arg} {kind : Own.Kind} {result : Cfg.Instr}
    (positive : 0 < ctor.arity)
    (accepted : consume P layout (.bind x (.alloc ctor args kind)) = .ok result) :
    CtorOk (Rt.Lower.tables P.base) ctor ∧ ctor.fieldless = false := by
  obtain ⟨_, _, _, _, _, table, tag, zero, succ, _⟩ := consume_allocation positive accepted
  refine ⟨⟨table, ?_, tag⟩, ?_⟩
  · simp [Rt.Lower.isNatKey, Rt.Lower.tables, zero, succ]
  · simp [Fir.CtorInfo.fieldless, Nat.ne_of_gt positive]

theorem admitted_ctor_fieldless {P : Program} {layout : Layout} {x : Nat}
    {ctor : Fir.CtorInfo} {args : List Fir.Arg} {kind : Own.Kind} {result : Cfg.Instr}
    (zero : ctor.arity = 0)
    (accepted : consume P layout (.bind x (.alloc ctor args kind)) = .ok result) :
    ValueCtorOk (Rt.Lower.tables P.base) (.ctor0 ctor) := by
  obtain ⟨_, _, _, table, tag, natZero, natSucc, _⟩ := consume_fieldless zero accepted
  refine ⟨⟨table, ?_, tag⟩, ?_⟩
  · simp [Rt.Lower.isNatKey, Rt.Lower.tables, natZero, natSucc]
  · simp [Fir.CtorInfo.fieldless, zero]

theorem admitted_alloc_preserves {P : Program} {layout : Layout} {x : Nat}
    {ctor : Fir.CtorInfo} {args : List Fir.Arg} {kind : Own.Kind} {result : Cfg.Instr}
    (positive : 0 < ctor.arity)
    (accepted : consume P layout (.bind x (.alloc ctor args kind)) = .ok result)
    {heap : Own.Heap} (before : HeapCtorOk (Rt.Lower.tables P.base) heap)
    (values : List Own.RVal)
    (fields : ∀ value ∈ values, ValueCtorOk (Rt.Lower.tables P.base) value) :
    HeapCtorOk (Rt.Lower.tables P.base) (heap.alloc .rc ⟨ctor, values⟩).2 := by
  have compatible := admitted_ctor_positive positive accepted
  exact before.alloc ⟨compatible.1, compatible.2, fields⟩

theorem valueCtorOk_of_valRel {tables : Rt.Lower.Tables} {words : List Lir.Word}
    {value : Own.RVal} {word : Lir.Word} (related : ValRel tables words value word) :
    ValueCtorOk tables value := by
  cases value <;> simp only [ValueCtorOk]
  exact related.2

/-- Primitive booleans use the already checked lowering table. The result's
table compatibility comes from actual source evaluation, not a fresh premise. -/
theorem bool_ctor_compatible {P : Cfg.Program} {t e : Lir.Word}
    (lowering : (Rt.Lower.tables P).bools = some (t, e)) {b : Bool} {value : Own.RVal}
    (effect : (match (if b then P.known.boolTrue else P.known.boolFalse) with
      | some c => Sem.Result.ofOption (Own.ctor0Of (ownTables (Rt.Lower.tables P)) c)
      | none => .stuck) = .ok value) : ValueCtorOk (Rt.Lower.tables P) value :=
  valueCtorOk_of_valRel (bool_rel (P := []) (tables_boolsOk P) lowering effect)





end IxCC.Cfg.Rc.Proof.Physical.Bridge
