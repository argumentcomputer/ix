import IxCC.Cfg.Rc.Proof.Physical.AllocationPrefix
import IxCC.Cfg.Rc.Proof.Physical.CheckedPrefix
import IxCC.Cfg.Rc.Proof.Physical.BindLayout
import IxCC.Cfg.Rc.Proof.Physical.PrefixHeap
import IxCC.Cfg.Rc.Proof.Native.Activation
import IxCC.Cfg.Rc.Proof.Physical.Bridge.CtorAdmission
import IxCC.Cfg.Rc.Proof.Physical.Bridge.CtorTables

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open Spec IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

/-- Execute the checked positive constructor binding through its canonical
copy prefix and real allocation wrapper. The result is the complete next
source/native activation and heap state, or actual resource failure. -/
theorem allocation_activation
    {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true)
    {pairs : List (Nat × Cfg.Fun)} (functions : Nat → Lir.Func) (main : Nat)
    {H : Heap} {addresses : AddressMap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {imm : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    {joins : Own.Plain.Joins} {Jf : List Fir.JEntry} {Jo : List Own.Plain.JEntry}
    {x : Fir.Var} {ctor : Fir.CtorInfo} {args : List Fir.Arg} {cont : Fir.Code}
    {sourceFunction : Fir.Fun} {function : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (before : Activation F P pairs (Public.Spec.sourceStage P functions main) H addresses
      (holdRoots external held) live ρf ρo roots joins Jf Jo (.bind x (.ctor ctor args) cont)
      sourceFunction.vars function source target imm)
    (sourceLookup : F.fun? source.fn = some sourceFunction) (positive : 0 < ctor.arity)
    {mem : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses mem external (roots ++ held)
      context base bump limit regionBytes slots lists)
    (callers : List Lir.Frame) :
    (∃ fields logical copied address next mem' slots' lists' after final,
      Own.evalArgs ρo args = some fields ∧ Fir.evalArgs ρf args = some logical ∧
      Own.Plain.evalActions ρo H (Own.Plain.copies (Own.Plain.heapArgs imm args)) = .ok copied ∧
      let allocated := copied.alloc .rc {ctor, fields}
      Own.Plain.evalRhs {ctors := F.ctors, known := F.known} ρo copied (.ctor ctor args) = .ok allocated ∧
      Activation F P pairs (Public.Spec.sourceStage P functions main) allocated.2
        (placeFresh addresses copied.size address) (holdRoots external held) (live ++ [x])
        (ρf.insert x (.ctor ctor logical)) (ρo.insert x allocated.1) (roots ++ [allocated.1])
        joins Jf Jo cont sourceFunction.vars function after final imm ∧
      HeapState P pairs allocated.2 (placeFresh addresses copied.size address) mem' external
        ((roots ++ [allocated.1]) ++ held) context base next limit regionBytes slots' lists' ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem, ctx := context, stack := target :: callers} (2 * (Own.Plain.copies (Own.Plain.heapArgs imm args)).length + 2)
        {mem := mem', ctx := context, stack := final :: callers} ∧
      copied.size = H.size ∧ after.fn = source.fn ∧
      (∀ value logical, Own.Proof.Den H value logical → Own.Proof.Den allocated.2 value logical)) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem, ctx := context, stack := target :: callers} := by
  have scopeFacts := before.scope
  simp only [Own.Plain.scopeOk, Bool.and_eq_true, and_assoc] at scopeFacts
  obtain ⟨freshBool, rhsScope, contScope⟩ := scopeFacts
  have fresh : x ∉ live := by simpa using freshBool
  have rhsFacts : args.length = ctor.arity ∧ args.all (Own.Plain.argIn live) = true ∧
      ctor.nscalar = 0 ∧ ctor.fieldKinds.length = ctor.nobj ∧
      ctor.fieldKinds.all (fun kind => decide (kind = .shared)) = true := by
    simpa only [Own.Plain.rhsIn, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using rhsScope
  have scope := rhsFacts.2.1
  have nextImmEq : Own.Plain.nextImm imm x (.ctor ctor args) = imm := by
    simp [Own.Plain.nextImm, Own.Plain.isImmRhs, Nat.ne_of_gt positive]
  have initialLayout : At F P source ρo Jo (Own.Plain.actionPrefix (Own.Plain.copies (Own.Plain.heapArgs imm args))
      (.bind x (.ctor ctor args) (Own.Plain.lowerCode (live ++ [x]) joins cont imm))) := by
    have layout := before.layout
    dsimp only [Own.Plain.lowerCode] at layout
    rw [nextImmEq] at layout
    exact layout
  obtain ⟨first, bindingTail, prefixHead, bindingLayout, absent⟩ :=
    checked_prefix_cursor checked initialLayout sourceLookup before.frame.words
  obtain ⟨tail, bindingHead, _⟩ := bind_layout bindingLayout .erased
  have bindingHead' : bindingTail = .bind x (.alloc ctor args .shared) :: tail := bindingHead
  have head : source.rest = encodePrefix P.base.size first (Own.Plain.copies (Own.Plain.heapArgs imm args)) ++
      .bind x (.alloc ctor args .shared) :: tail := by rw [bindingHead'] at prefixHead; exact prefixHead
  have real := checked_binding_real checked bindingLayout sourceLookup
    (by simp [Own.immRhs, reserved])
  rcases allocation_prefix functions main before.frame.cursor {ctors := F.ctors, known := F.known}
      ctor args x head before.frame.lookup before.canonical before.lexical.1 fresh scope positive
      heap.ready before.frame.words real before.frame.bounded absent before.running callers with success | failure
  · obtain ⟨fields, logical, copied, address, next, mem', slots', lists', final,
      arguments, sourceArgs, copies, effect, canonical, ready, trace, cursor, words,
      bounded, sub, size, running, admission, liveArgs, fused⟩ := success
    let allocated := copied.alloc .rc {ctor, fields}
    let after : Cfg.Frame := { source with
      rest := tail
      env := source.env.insert x allocated.1 }
    obtain ⟨actualTail, actualHead, actualLayout⟩ := bind_layout bindingLayout allocated.1
    have tailEqual : actualTail = tail := (List.cons.inj (actualHead.symm.trans bindingHead)).2
    subst actualTail
    have returned : ValueCtorOk (tablesOf P pairs) allocated.1 := by trivial
    have frame : FrameState P pairs (Public.Spec.sourceStage P functions main)
        (placeFresh addresses copied.size address) allocated.2.size sourceFunction.vars function after final :=
      ⟨before.frame.lookup, cursor, words, bounded, before.frame.compatible.bind x returned⟩
    have activation : Activation F P pairs (Public.Spec.sourceStage P functions main) allocated.2
        (placeFresh addresses copied.size address) (holdRoots external held) (live ++ [x])
        (ρf.insert x (.ctor ctor logical)) (ρo.insert x allocated.1) (roots ++ [allocated.1])
        joins Jf Jo cont sourceFunction.vars function after final imm :=
      ⟨canonical, actualLayout, frame, contScope, running, fused⟩
    have arity : fields.length = ctor.arity := (Own.evalArgs_length ρo arguments).trans rhsFacts.1
    have frameArgs := Cfg.Proof.evalArgs_sub before.lexical.1 arguments
    have fieldBounds := before.frame.bounded.args args frameArgs
    have bodyOk : BodyOk copied.size {ctor, fields} := by
      refine ⟨arity, positive, ?_⟩
      intro location member
      rw [size]
      exact fieldBounds (.loc location) member
    obtain ⟨actualInstruction, accepted⟩ := admission
    have admitted := admitted_ctor_positive positive accepted
    have bodyCompatible : BodyCtorOk (tablesOf P pairs) {ctor, fields} :=
      ⟨ctorOk_tablesOf pairs admitted.1, admitted.2, before.frame.compatible.args liveArgs frameArgs⟩
    have heapAfter : HeapState P pairs allocated.2 (placeFresh addresses copied.size address) mem' external
        ((roots ++ [allocated.1]) ++ held) context base next limit regionBytes slots' lists' :=
      ⟨ready, heapOk_alloc (actions_heapOk heap.ordered copies) bodyOk,
        (heap.compatible.evalActions copies).alloc bodyCompatible, heap.extent⟩
    obtain ⟨_, _, _, _, preserves⟩ := allocation_state_after before.canonical
      {ctors := F.ctors, known := F.known} ctor args x fresh scope arguments arity positive copies
    exact .inl ⟨fields, logical, copied, address, next, mem', slots', lists', after, final,
      arguments, sourceArgs, copies, effect, activation, heapAfter, trace, size, rfl, preserves⟩
  · exact .inr failure


end IxCC.Cfg.Rc.Native
