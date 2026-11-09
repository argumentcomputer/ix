import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarActivation
import IxCC.Cfg.Rc.Proof.Physical.CheckedPrefix
import IxCC.Cfg.Rc.Proof.Physical.CopyPrefix
import IxCC.Cfg.Rc.Proof.Physical.PrefixHeap

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC IxCC.Cfg.Rc IxCC.Cfg.Rc.Native
open IxCC.Cfg.Rc.Native.Spec IxCC.Rt.Rc.Procs

/-- Canonical argument binding executes its actual copy prefix before the
scalar assignment. The copied occurrence becomes the new lexical root;
existing aliases and captured join environments retain their ownership. -/
theorem argument_activation {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (checked : checkScopedProgram F bodies P = true)
    {pairs : List (Nat × Cfg.Fun)} (consuming : consumeAll P = .ok pairs)
    (functions : Nat → Lir.Func) (main : Nat)
    {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat}
    {live imm : List Fir.Var} {sourceEnv : Fir.Env} {ownedEnv : Own.Env} {roots : List Own.RVal}
    {joins : Own.Plain.Joins} {sourceJoins : List Fir.JEntry} {ownedJoins : List Own.Plain.JEntry}
    {x : Nat} {arg : Fir.Arg} {body : Fir.Code}
    {sourceFd : Fir.Fun} {fd : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (sourceLookup : F.fun? source.fn = some sourceFd)
    (before : Activation F P pairs (Public.Spec.sourceStage P functions main) H addresses external
      live sourceEnv ownedEnv roots joins sourceJoins ownedJoins (.bind x (.arg arg) body)
      sourceFd.vars fd source target imm)
    {mem : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses mem external roots context base bump limit regionBytes slots lists)
    {logical : Fir.Val} (evaluation : Fir.evalRhs F sourceEnv (.arg arg) = .ok logical)
    (callers : List Lir.Frame) :
    (∃ value H' mem' tail charge after,
      Own.Plain.evalActions ownedEnv H (Own.Plain.copies (Own.Plain.heapArgs imm [arg])) = .ok H' ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem, ctx := context, stack := target :: callers} charge
        {mem := mem', ctx := context, stack := after :: callers} ∧
      Activation F P pairs (Public.Spec.sourceStage P functions main) H' addresses external
        (live ++ [x]) (sourceEnv.insert x logical) (ownedEnv.insert x value) (roots ++ [value])
        joins sourceJoins ownedJoins body sourceFd.vars fd
        {source with rest := tail, env := source.env.insert x value} after
        (Own.Plain.nextImm imm x (.arg arg)) ∧
      HeapState P pairs H' addresses mem' external (roots ++ [value])
        context base bump limit regionBytes slots lists ∧
      H'.size = H.size ∧ (∀ root, H.value? root = H'.value? root)) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem, ctx := context, stack := target :: callers} := by
  have scope : x ∉ live ∧ Own.Plain.argIn live arg = true ∧
      Own.Plain.scopeOk (Own.Plain.signatures F) (live ++ [x])
        (Own.Plain.stackArities sourceJoins) body = true := by
    simpa [Own.Plain.scopeOk, Own.Plain.rhsIn, Bool.and_eq_true, and_assoc] using before.scope
  obtain ⟨fresh, argScope, bodyScope⟩ := scope
  have argsScope : [arg].all (Own.Plain.argIn live) = true := by simpa using argScope
  obtain ⟨value, logical', lexicalArg, sourceArg, den⟩ := Own.Plain.arg_den before.canonical.env argScope
  have logicalEqual : logical' = logical := by
    simpa only [Fir.evalRhs, sourceArg, Sem.Result.ofOption, Sem.Result.ok.injEq] using evaluation
  subst logical'
  have sub := before.lexical.1
  have original : Tokens H external [] live sourceEnv ownedEnv roots := Tokens.ofState before.canonical
  have tokens := Tokens.extend original sub
  have prefixAt : At F P source ownedEnv ownedJoins
      (Own.Plain.actionPrefix (Own.Plain.copies (Own.Plain.heapArgs imm [arg]))
        (.bind x (.arg arg) (Own.Plain.lowerCode (live ++ [x]) joins body
          (Own.Plain.nextImm imm x (.arg arg))))) := before.layout
  obtain ⟨first, bindingTail, prefixHead, atBind, absent⟩ :=
    checked_prefix_cursor checked prefixAt sourceLookup before.frame.words
  have ready : AllocatorReady H addresses mem (Own.Rc.holdRoots external (roots ++ []))
      context base bump limit slots lists := by simpa using heap.ready
  rcases copy_heapArgs_prefix functions main [arg] before.frame.cursor prefixHead before.frame.lookup tokens
      (ImmEnv.sub before.canonical.immOk sub) argsScope ready before.frame.words absent
      before.running callers with copied | failed
  · obtain ⟨fields, H', mem', middle, frameArgs, frameCopies, afterTokens, afterReady, prefixTrace,
      prefixCursor, words, middleRunning, values⟩ := copied
    have fullArg : Own.evalArg source.env arg = some value := Cfg.Proof.evalArg_sub sub lexicalArg
    have fieldEqual : fields = [value] := by
      simpa [Own.evalArgs, fullArg] using frameArgs.symm
    subst fields
    have copiedSize : H'.size = H.size := actions_size frameCopies
    have lexicalCopies : Own.Plain.evalActions ownedEnv H
        (Own.Plain.copies (Own.Plain.heapArgs imm [arg])) = .ok H' := by
      rw [copies_eval_sub sub (Tokens.present original) (Own.Plain.heapArgs imm [arg])
        (Own.Plain.heapArgs_scope imm argsScope) H]
      exact frameCopies
    have middleFrame : FrameState P pairs (Public.Spec.sourceStage P functions main)
        addresses H'.size sourceFd.vars fd {source with rest := bindingTail} middle :=
      ⟨before.frame.lookup, prefixCursor, words,
        by rw [copiedSize]; exact before.frame.bounded, before.frame.compatible⟩
    obtain ⟨tail, head, continuation⟩ := atBind.bind_continuation
    obtain ⟨supply, real⟩ := checked_binding_bounds (source := {source with rest := bindingTail})
      checked consuming sourceLookup before.frame.lookup atBind trivial
    obtain ⟨pow, gcd⟩ := source_stage_scalar_runtime P pairs functions main
    have effect : Own.evalRhs .rc P.base.tables source.env H' (.fir (.arg arg)) = .ok (value, H') := by
      simp [Own.evalRhs, fullArg]
    rcases (frame_step pow gcd middleFrame supply head trivial real effect middleRunning
        mem' context callers).2 with scalar | failed
    · obtain ⟨charge, after, running, trace, frame, fused⟩ := scalar
      have balance : Own.Rc.Balance H' external (roots ++ [value]) :=
        Own.Rc.balance_hold.mpr (by simpa using afterTokens.balance)
      have den' : Own.Proof.Den H' value logical := by
        change H'.value? value = some logical
        rw [← values value]
        exact den
      have himm_rhs : Own.Plain.isImmRhs imm (.arg arg) = true → Own.Plain.ImmVal value :=
        fun hr => Own.Plain.immVal_of_isImmArg before.canonical.immOk hr lexicalArg
      have state := before.canonical.bind_rhs x (.arg arg) fresh himm_rhs den' balance (fun root _ => values root)
      refine .inl ⟨value, H', mem', tail, 2 * (Own.Plain.copies (Own.Plain.heapArgs imm [arg])).length + charge, after,
        lexicalCopies, prefixTrace.trans trace,
        ⟨state, continuation value, frame, bodyScope, running, fused⟩,
        ⟨by simpa using afterReady, actions_heapOk heap.ordered frameCopies,
          heap.compatible.evalActions frameCopies, heap.extent⟩, copiedSize, values⟩
    · obtain ⟨cost, final, resource, trace, failure⟩ := failed
      exact .inr ⟨_, final, resource, prefixTrace.trans trace, failure⟩
  · exact .inr failed


end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
