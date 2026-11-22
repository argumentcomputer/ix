import IxCC.Cfg.Rc.Proof.Native.Allocation
import IxCC.Cfg.Rc.Proof.Physical.PublicationRegisters
import IxCC.Rt.Rc.Gen.Proof.AllocatorReady
import IxCC.Own.Plain.Semantics

/-! The zero-field branch is an immediate value in both source and physical
semantics. It performs no allocation, changes no memory and consumes no heap
reference count. Admission and the actual emitted assignment are explicit. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Rt.Rc
open IxCC.Rt.Rc.Procs

theorem consume_fieldless {P : Program} {l : Layout} {x : Nat}
    {c : Fir.CtorInfo} {args : List Fir.Arg} {kind : Own.Kind} {result : Instr}
    (zero : c.arity = 0)
    (accepted : consume P l (.bind x (.alloc c args kind)) = .ok result) :
    args = [] ∧ kind = .shared ∧ c.nscalar = 0 ∧
      Fir.CtorInfo.ofKey P.base.ctors c.key = some c ∧ c.tag ≤ Rt.maxTag ∧
      P.base.known.natZero ≠ some c.key ∧ P.base.known.natSucc ≠ some c.key ∧
      result = .bind x (.alloc c args kind) := by
  simp only [consume, reserved, Bool.false_eq_true, ↓reduceIte] at accepted
  by_cases hs : (kind == .shared && c.nscalar == 0 && c.fieldKinds.length == c.nobj &&
      c.fieldKinds.all (· == .shared) && args.length == c.arity &&
      Fir.CtorInfo.ofKey P.base.ctors c.key == some c) = true
  · simp only [hs, Bool.true_eq_false, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
    by_cases ht : c.tag > Rt.maxTag
    · simp [ht, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
    · simp only [ht, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
      by_cases hn : (P.base.known.natZero == some c.key || P.base.known.natSucc == some c.key) = true
      · simp [hn, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
      · simp only [hn, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
        have hz : c.fieldless = true := by simp [Fir.CtorInfo.fieldless, zero]
        simp only [hz, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hs
        obtain ⟨⟨⟨⟨⟨hk, hscalar⟩, _⟩, _⟩, hargs⟩, htable⟩ := hs
        have hknown : P.base.known.natZero ≠ some c.key ∧
            P.base.known.natSucc ≠ some c.key := by simpa using hn
        exact ⟨List.length_eq_zero_iff.mp (hargs.trans zero), hk, hscalar,
          htable, Nat.le_of_not_gt ht, hknown.1, hknown.2, accepted.symm⟩
  · simp [hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted

theorem fieldless_word (addresses : AddressMap) {c : Fir.CtorInfo}
    (zero : c.arity = 0) (tag : c.tag ≤ Rt.maxTag) :
    valueWord addresses (.ctor0 c) = some (Rt.ctor0Word c.tag) := by
  simp [valueWord, zero, tag]

theorem fieldless_source (tables : Own.Tables) (source : Own.Env) (heap : Own.Heap)
    {c : Fir.CtorInfo} (zero : c.arity = 0) :
    Own.Plain.evalRhs tables source heap (.ctor c []) = .ok (.ctor0 c, heap) := by
  simp [Own.Plain.evalRhs, Own.evalRhs, Own.evalArgs, Fir.CtorInfo.fieldless, zero]

theorem lower_fieldless (f x : Nat) (tables : Rt.Lower.Tables) (state : Rt.Lower.St)
    {c : Fir.CtorInfo} (zero : c.arity = 0) (scalar : c.nscalar = 0)
    (table : Fir.CtorInfo.ofKey tables.ctors c.key = some c)
    (tag : c.tag ≤ Rt.maxTag) (notNat : Rt.Lower.isNatKey tables c.key = false) :
    (Rt.Lower.instr f tables (.bind x (.alloc c [] .shared))).run state =
      .ok (true, {state with acc := .assign x (.arg (.imm (Rt.ctor0Word c.tag))) :: state.acc}) := by
  simp [Rt.Lower.instr, Rt.Lower.withOperands, Rt.Lower.operands, Rt.Lower.alloc,
    notNat, scalar, zero, table, Nat.not_lt_of_ge tag, Fir.CtorInfo.fieldless,
    Rt.Lower.assign, Rt.Lower.emit, StateT.run, StateT.bind, StateT.pure,
    MonadLift.monadLift, liftM, monadLift, StateT.lift, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, MonadState.modifyGet,
    bind, pure, Except.bind, Except.pure]

theorem fieldless_step {P : Lir.Program} {caller : Lir.Frame} {callers : List Lir.Frame}
    {function : Lir.Func} {block : Lir.Block} {mem : X86.Memory} {context : Lir.Word}
    {x : Nat} {c : Fir.CtorInfo}
    (hf : P.funcs[caller.fn]? = some function)
    (hb : function.blocks[caller.label]? = some block)
    (hp : caller.pos < block.body.size)
    (hs : block.body[caller.pos] = .assign x (.arg (.imm (Rt.ctor0Word c.tag)))) :
    Lir.step P {mem, ctx := context, stack := caller :: callers} =
      .next {mem, ctx := context, stack :=
        {caller with pos := caller.pos + 1, env := caller.env.insert x (Rt.ctor0Word c.tag)} :: callers} false := by
  apply Lir.step_stmt hf hb hp hs rfl
  rfl

theorem fieldless_registers {addresses : AddressMap} {bound x : Nat}
    {source : Own.Env} {target : Lir.Env} (related : EnvWordsBelow addresses bound source target)
    {c : Fir.CtorInfo} (zero : c.arity = 0) (tag : c.tag ≤ Rt.maxTag) :
    EnvWordsBelow addresses bound (source.insert x (.ctor0 c))
      (target.insert x (Rt.ctor0Word c.tag)) := related.bind (fieldless_word addresses zero tag)

theorem fieldless_ready {H : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem external context base bump limit slots lists)
    (c : Fir.CtorInfo) :
    Gen.AllocatorReady maxClass H addresses mem (fun loc => external loc + Own.Rc.refsIn loc [.ctor0 c])
      context base bump limit slots lists := by
  simpa [Own.Rc.refsIn] using ready








end IxCC.Cfg.Rc.Native.Spec
