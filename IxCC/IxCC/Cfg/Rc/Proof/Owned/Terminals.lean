import IxCC.Cfg.Rc.Proof.Owned.Activation
import IxCC.Cfg.Rc.Proof.Native.ReturnActivation
import IxCC.Cfg.Rc.Proof.Native.TrapActivation
import IxCC.Cfg.Rc.Proof.Native.TerminalOutcomes
import IxCC.Cfg.Rc.Proof.Native.HeapHistory
import IxCC.Cfg.Rc.Proof.Native.Outcome
import IxCC.Cfg.Rc.Proof.Physical.Admission
import IxCC.Fir.Proof.Unfold

/-! # `ret` and `trap` over the typing context (heap stage 2)

No action prefix: whatever the certificate placed before the terminal has run as single actions.
At `ret a` the checker took the argument's token and found none left (`closed`), so the returned
value is the only root (`closed_nil`); a `trap` ends the run with any tokens held. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Rt.Rc
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs IxCC.Own.Rc
open IxCC.Own.Plain (Ctx JCtx checkCode)

theorem ActivationOwned.return_value
    {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true)
    {pairs : List (Nat × Cfg.Fun)} (consuming : consumeAll P = .ok pairs)
    (functions : Nat → Lir.Func) (main : Nat)
    {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat} {roots : List Own.RVal}
    {live : List Fir.Var} {Γ : Ctx} {Δ : JCtx} {sourceEnv : Fir.Env} {ownedEnv : Own.Env}
    {lex : Own.Plain.Joins} {sourceJoins : List Fir.JEntry} {ownedJoins : List Own.Plain.JEntry}
    {arg : Fir.Arg} {sourceFunction : Fir.Fun} {function : Cfg.Fun}
    {source : Cfg.Frame} {target : Lir.Frame}
    (before : ActivationOwned F P pairs (Public.Spec.sourceStage P functions main) H addresses
      external live Γ Δ sourceEnv ownedEnv roots lex sourceJoins ownedJoins (.ret arg)
      sourceFunction.vars function source target)
    (sourceLookup : F.fun? source.fn = some sourceFunction)
    {memory : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses memory external roots
      context base bump limit regionBytes slots lists)
    (callers : List Lir.Frame) :
    (∃ value logical word,
      Own.evalArg ownedEnv arg = some value ∧ Fir.Arg.eval sourceEnv arg = some logical ∧
      Own.Proof.Den H value logical ∧ Balance H external [value] ∧
      HeapState P pairs H addresses memory external [value]
        context base bump limit regionBytes slots lists ∧
      Rt.Proof.RetAt (Public.Spec.sourceStage P functions main) target word ∧
      valueWord addresses value = some word ∧ Own.Plain.Bounded H.size value ∧
      ValueCtorOk (tablesOf P pairs) value) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem := memory, ctx := context, stack := target :: callers} := by
  obtain ⟨Γ', ht, hcl⟩ := Own.Plain.checkCode_ret before.typed
  obtain ⟨value, logical, owned₁, ownValue, sourceValue, den, inv₁, refs, _⟩ :=
    Own.Plain.takeArg_sem before.owned.takeInv ht
  obtain ⟨toks₁, htok₁, hr₁⟩ := inv₁.roots
  have hnil := Own.Plain.closed_nil htok₁ hcl
  subst hnil
  have ho := Own.Plain.EnvRoots.nil_inv hr₁
  subst ho
  have balance : Balance H external [value] := refs.balance before.owned.counts
  have lexical := before.lexical.1
  have frameValue := Cfg.Proof.evalArg_sub lexical ownValue
  obtain ⟨fd, scopeNames, params, acc, next, supply, lower, lookup, range, layout, cursor,
    sub, below, names, saved⟩ := before.layout
  have finished : source.rest = [] := by simpa only [skeleton, Cfg.Proof.spine] using cursor
  let block : Cfg.Block := {params, body := acc.reverse, term := .ret arg}
  have blockLookup : fd.blocks[source.blk]? = some block := by
    simpa only [skeleton, Cfg.Proof.Impl, Cfg.Fun.block?] using layout
  have programSize : P.base.size = F.size :=
    generate_size (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have nativeRange : source.fn < P.base.size := by simpa only [programSize] using range
  obtain ⟨original, actual, originalLookup, receipt, consumedLookup⟩ :=
    consumed_entry consuming nativeRange
  have originalEqual : original = fd := Option.some.inj (originalLookup.symm.trans lookup)
  subst original
  have actualEqual : actual = function :=
    Option.some.inj (consumedLookup.symm.trans before.frame.lookup)
  subst actual
  obtain ⟨consumedBody, consumedBodyEq, consumedBlock⟩ :=
    (consumeFunction_parts receipt).2.2.2.2.2 blockLookup
  have argLive : Rt.Proof.LiveArg (Rt.Proof.Fused (tablesOf P pairs) function) arg :=
    fused_term_live consumedBlock (args := [arg]) (fun x member => by
      simp only [Rt.Proof.otherUses, List.mem_append]
      exact .inr (by simpa [Cfg.Check.termVars] using Rt.Proof.argVars_of_mem member)) arg (by simp)
  have compatible := before.frame.compatible.arg argLive frameValue
  have heap' : HeapState P pairs H addresses memory external [value]
      context base bump limit regionBytes slots lists :=
    ⟨by rw [← holdRoots_sameRefs refs]; exact heap.ready, heap.ordered, heap.compatible,
      heap.extent⟩
  rcases before.frame.cursor.ret consuming nativeRange lookup before.frame.lookup blockLookup
      finished rfl before.frame.words frameValue before.running memory context callers with
      returned | failure
  · obtain ⟨word, represented, ret⟩ := returned
    exact .inl ⟨value, logical, word, ownValue, sourceValue, den, balance, heap', ret, represented,
      Own.Plain.den_bounded den, compatible⟩
  · exact .inr failure

section
variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {main clock : Nat} {sourceJoins : List Fir.JEntry}

/-- **`ret a`.** -/
theorem physical_return_owned (admission : CodeAdmission F bodies P config pairs functions)
    (arg : Fir.Arg) :
    PhysicalCodeOwned F P config pairs main clock sourceJoins (.ret arg) := by
  intro H addresses external live Γ Δ sourceEnv ownedEnv roots lex ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  rcases before.return_value admission.scopedProgram admission.consuming
      (Public.Spec.rawSource config P pairs) main sourceLookup heap callers with success | failure
  · obtain ⟨value, logical, word, _, sourceValue, den, balance, afterState, ret, represented,
      bounded, compatible⟩ := success
    show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _ (Fir.eval F clock sourceEnv sourceJoins (.ret arg))
    simp only [Fir.eval_ret, sourceValue, Sem.Result.ofOption]
    let returned : Returned P pairs
        (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) H addresses
        external context base limit regionBytes logical := {
      heap := H
      addresses := addresses
      memory := memory
      bump := bump
      slots := slots
      lists := lists
      frame := target
      value := value
      word := word
      den := den
      balance := balance
      state := afterState
      terminator := ret
      represented := represented
      bounded := bounded
      compatible := compatible
      preserved := fun _ _ _ h => h
      history := ⟨Nat.le_refl _, fun _ _ => rfl⟩ }
    exact .inl ⟨returned, 0, .refl _⟩
  · exact ResultAt.of_fails failure

/-- **`trap`**: the tokens held are not released (a trap ends the run). -/
theorem physical_trap_owned (admission : CodeAdmission F bodies P config pairs functions) :
    PhysicalCodeOwned F P config pairs main clock sourceJoins .trap := by
  intro H addresses external live Γ Δ sourceEnv ownedEnv roots lex ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _ (Fir.eval F clock sourceEnv sourceJoins .trap)
  rw [Fir.eval_trap]
  obtain ⟨fd, scopeNames, params, acc, next, supply, lower, lookup, range, layout, cursor,
    sub, below, names, saved⟩ := before.layout
  have finished : source.rest = [] := by simpa only [skeleton, Cfg.Proof.spine] using cursor
  let block : Cfg.Block := {params, body := acc.reverse, term := .trap}
  have blockLookup : fd.blocks[source.blk]? = some block := by
    simpa only [skeleton, Cfg.Proof.Impl, Cfg.Fun.block?] using layout
  have programSize : P.base.size = F.size :=
    generate_size (checkProgram_parts (checkScopedProgram_parts admission.scopedProgram).1).2
  have nativeRange : source.fn < P.base.size := by simpa only [programSize] using range
  exact .inl ⟨0, _, .refl _, before.frame.cursor.trap admission.consuming nativeRange lookup
    blockLookup finished rfl before.running memory context callers⟩

end

end IxCC.Cfg.Rc.Native.Spec
