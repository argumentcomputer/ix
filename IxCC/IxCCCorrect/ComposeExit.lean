import IxCCCorrect.GroundShape

/-!
# Both clauses of `Tier1` for the checked core (`IxCCCorrect.ComposeExit`)

`IxCCCorrect.ComposeExe` proves the first clause of `Tier1` (standard output is empty or a prefix
of the rendering of an agreeing answer). This module proves the second: **a trace that ends with
`exit 0` has written the whole rendering** of such an answer.

```lean
exit_of_outcome : PlainExeOutcome srcEval (fun _ => False) arity result D args σ →
  exitStatus σ = some 0 →
  ∃ ns v full, … ∧ srcEval ns (some (resultObs result v)) ∧ σ = started D ++ full ∧
    WriteSeq 1 0 (renderPlain result v) true full

tier1Check_sound_core : Recheck.ingress envBytes equations roots claim.kernelLimits = .ok inp →
  Recheck.run cfg P c = .ok a → Exe.build a layout = .ok ⟨inp', ce⟩ →
  tier1Check claim inp c a sc = true →
  ∃ acc, Admits claim envBytes acc ∧ Tier1Core claim acc ce.bytes
```

`Tier1Core claim acc image` is the body of `Tier1` word for word, over `LoadedFile image` and
`Trace image` (the checked core's process) instead of `FileTrace exe`. What separates
`tier1Check_sound_core` from `Tier1 claim envBytes exe` is only the shipped-file link (the traces of
the shipped file whose core is `ce.bytes` are those of `ce.bytes`, link B of the inventory).

**Why an exit 0 is the result's.** In every write loop (`WriteSeq`) the only `exit` is the last
call (`writeSeq_prefix_exit`), with the loop's status when every write was accepted and
`writeFailed` (74) otherwise. Every report's status is nonzero (`Message.status`), the
confinement makes no `exit`, so the only trace of `PlainExeOutcome` with no escape that ends in
`exit 0` is the confinement followed by the whole result loop, every write accepted, which wrote
its whole message (`writeSeq_written_full`).
-/

set_option autoImplicit false

namespace IxCC.Correct

open IxCC.X86
open IxCC.X86.Exe
open IxCC.X86.Exe.Process
open IxCC.X86.Exe.Plain
open IxCC.Sem (Obs Lang Result)

universe u

/-! ## Where a trace's `exit` is -/

theorem getLast?_append_of_ne_nil {α : Type} : ∀ (a : List α) {b : List α}, b ≠ [] →
    (a ++ b).getLast? = b.getLast?
  | [], _, _ => rfl
  | x :: a, b, hb => by
    have ih := getLast?_append_of_ne_nil a hb
    cases h : a ++ b with
    | nil => simp_all
    | cons y z =>
      rw [List.cons_append, h, List.getLast?_cons_cons, ← h]
      exact ih

theorem exitStatus_cons_cons (a b : Sys) (l : List Sys) :
    exitStatus (a :: b :: l) = exitStatus (b :: l) := by
  simp only [exitStatus, List.getLast?_cons_cons]

theorem exitStatus_append {a b : List Sys} (hb : b ≠ []) : exitStatus (a ++ b) = exitStatus b := by
  unfold exitStatus
  rw [getLast?_append_of_ne_nil a hb]

/-- **In a write loop, a prefix that ends in an `exit` is the whole loop**, and the status is the
loop's own when every write was accepted, `writeFailed` otherwise. -/
theorem writeSeq_prefix_exit {fd : Word} {status : Nat} :
    ∀ {m : List UInt8} {ok : Bool} {ρ : List Sys}, WriteSeq fd status m ok ρ →
      ∀ {τ : List Sys} {s : Word}, τ <+: ρ → exitStatus τ = some s →
      τ = ρ ∧ s = UInt64.ofNat (if ok then status else writeFailed)
  | _, _, _, .done, τ, s, ⟨t, ht⟩, hs => by
    cases τ with
    | nil => simp [exitStatus] at hs
    | cons a τ' =>
      cases τ' with
      | nil =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        simp only [exitStatus, List.getLast?_singleton, Option.some.injEq] at hs
        subst hs
        exact ⟨rfl, by simp⟩
      | cons b τ'' => simp at ht
  | _, _, _, .step _ _ _ hrest, τ, s, ⟨t, ht⟩, hs => by
    cases τ with
    | nil => simp [exitStatus] at hs
    | cons a τ' =>
      simp only [List.cons_append, List.cons.injEq] at ht
      obtain ⟨rfl, ht'⟩ := ht
      cases τ' with
      | nil => simp [exitStatus] at hs
      | cons b τ'' =>
        rw [exitStatus_cons_cons] at hs
        obtain ⟨h1, h2⟩ := writeSeq_prefix_exit hrest ⟨t, ht'⟩ hs
        exact ⟨by rw [h1], h2⟩
  | _, _, _, .refused _ _, τ, s, ⟨t, ht⟩, hs => by
    cases τ with
    | nil => simp [exitStatus] at hs
    | cons a τ' =>
      cases τ' with
      | nil =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht
        obtain ⟨rfl, -⟩ := ht
        simp [exitStatus] at hs
      | cons b τ'' =>
        cases τ'' with
        | nil =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht
          obtain ⟨rfl, rfl, rfl⟩ := ht
          simp only [exitStatus, List.getLast?_cons_cons, List.getLast?_singleton,
            Option.some.injEq] at hs
          subst hs
          exact ⟨rfl, by simp⟩
        | cons c τ''' => simp at ht

/-- **A write loop that accepted every write wrote its whole message** (shorter than `2 ^ 63`
bytes). -/
theorem writeSeq_written_full {fd : Word} {status : Nat} :
    ∀ {m : List UInt8} {ρ : List Sys}, WriteSeq fd status m true ρ → m.length < 2 ^ 63 →
      written fd ρ = m
  | _, _, .done, _ => by simp [written]
  | m, _, @WriteSeq.step _ _ _ r _ ρ _ _ hle hrest, hlen => by
    have hr : r.toNat < 2 ^ 63 := Nat.lt_of_le_of_lt hle hlen
    have ih := writeSeq_written_full hrest (by rw [List.length_drop]; omega)
    have e : written fd (Sys.write fd m r :: ρ) = m.take r.toNat ++ written fd ρ := by
      simp only [written, accepted, hr, ite_true]
    rw [e, ih, List.take_append_drop]

theorem message_status_ne_zero (msg : Message) : UInt64.ofNat msg.status ≠ 0 := by
  cases msg <;> decide

theorem writeFailed_ne_zero : UInt64.ofNat writeFailed ≠ 0 := by decide

/-- **A report never ends in `exit 0`**, nor does any prefix of it. -/
theorem reportsMsg_prefix_exit {arity : Nat} {msg : Message} {ρ : List Sys}
    (h : ReportsMsg arity msg ρ) {τ : List Sys} (hp : τ <+: ρ) : exitStatus τ ≠ some 0 := by
  intro hs
  obtain ⟨ok, full, hw, hρ⟩ := h
  obtain ⟨-, h2⟩ := writeSeq_prefix_exit hw (hp.trans hρ) hs
  cases ok with
  | true => exact message_status_ne_zero msg (by simpa using h2.symm)
  | false => exact writeFailed_ne_zero (by simpa using h2.symm)

/-- A call that is not an `exit`, followed by calls no prefix of which ends in `exit 0`. -/
theorem cons_prefix_exit {e : Sys} (he : exitStatus [e] = none) {ρ : List Sys}
    (hρ : ∀ τ, τ <+: ρ → exitStatus τ ≠ some 0) {σ : List Sys} (hp : σ <+: e :: ρ) :
    exitStatus σ ≠ some 0 := by
  obtain ⟨t, ht⟩ := hp
  cases σ with
  | nil => simp [exitStatus]
  | cons a σ' =>
    simp only [List.cons_append, List.cons.injEq] at ht
    obtain ⟨rfl, ht'⟩ := ht
    cases σ' with
    | nil => rw [he]; simp
    | cons b σ'' =>
      rw [exitStatus_cons_cons]
      exact hρ _ ⟨t, ht'⟩

theorem nil_prefix_exit : ∀ τ : List Sys, τ <+: [] → exitStatus τ ≠ some 0 := by
  intro τ hτ
  rw [List.prefix_nil.mp hτ]
  simp [exitStatus]

/-! ## The second clause, from an outcome -/

/-- **A trace with no escape that ends in `exit 0` is the confinement followed by the whole
result loop**, every write accepted, for a `v` the source evaluates to. -/
theorem exit_of_outcome {srcEval : List Nat → Option Obs → Prop} {arity : Nat}
    {result : ResultKind} {D : Nat} {args : List (List Nat)} {σ : List Sys}
    (h : IxCC.Exe.Plain.PlainExeOutcome srcEval (fun _ => False) arity result D args σ)
    (hexit : exitStatus σ = some 0) :
    ∃ ns v full, args.length = arity ∧ parseArgsList args = .ok ns ∧
      PlainCallMatches result (.ok (some (IxCC.Exe.Plain.resultObs result v))) (.value v) ∧
      srcEval ns (some (IxCC.Exe.Plain.resultObs result v)) ∧
      σ = started D ++ full ∧ WriteSeq 1 0 (renderPlain result v) true full := by
  have hS : ∀ τ, τ <+: started D → exitStatus τ ≠ some 0 := fun τ hτ =>
    cons_prefix_exit (by simp [exitStatus])
      (fun τ' hτ' => cons_prefix_exit (by simp [exitStatus]) nil_prefix_exit hτ') hτ
  rcases h with href | hpre | ⟨ρ, heq, hbody⟩
  · rcases href with ⟨r, ρ, -, hrep, hp⟩ | ⟨r, ρ, -, hrep, hp⟩
    · exact absurd hexit (cons_prefix_exit (by simp [exitStatus])
        (fun τ hτ => reportsMsg_prefix_exit hrep hτ) hp)
    · exact absurd hexit (cons_prefix_exit (by simp [exitStatus])
        (fun τ hτ => cons_prefix_exit (by simp [exitStatus])
          (fun τ' hτ' => reportsMsg_prefix_exit hrep hτ') hτ) hp)
  · exact absurd hexit (hS σ hpre)
  · by_cases hρn : ρ = []
    · subst hρn
      rw [List.append_nil] at heq
      exact absurd hexit (hS σ (by rw [heq]; exact List.prefix_refl _))
    have hρ : exitStatus ρ = some 0 := by rw [← exitStatus_append (a := started D) hρn, ← heq]; exact hexit
    have hrep : ∀ {m : Message}, ReportsMsg arity m ρ → False := fun hr =>
      reportsMsg_prefix_exit hr (List.prefix_refl ρ) hρ
    rcases hbody with ⟨-, hr⟩ | ⟨hlen, hparse⟩
    · exact (hrep hr).elim
    · cases hp : parseArgsList args with
      | overflow => rw [hp] at hparse; exact (hrep hparse).elim
      | bad => rw [hp] at hparse; exact (hrep hparse).elim
      | ok ns =>
        rw [hp] at hparse
        rcases hparse with ⟨v, hm, hs, hpr⟩ | ⟨o, -, -, hr⟩ | ⟨m, -, hr⟩ | hnil | hfalse
        · obtain ⟨ok, full, hw, hpf⟩ := hpr
          obtain ⟨h1, h2⟩ := writeSeq_prefix_exit hw hpf hρ
          cases ok with
          | false => exact absurd (by simpa using h2.symm) writeFailed_ne_zero
          | true => exact ⟨ns, v, full, hlen, rfl, hm, hs, by rw [heq, h1], hw⟩
        · exact (hrep hr).elim
        · exact (hrep hr).elim
        · exact absurd hnil hρn
        · exact hfalse.elim

/-- **The second clause of `Tier1` at one invocation and one trace.** -/
def Tier1ExitAt.{w} (claim : Claim) (acc : Src.KernelFront.Accepted) (args : List (List Nat))
    (σ : List Sys) : Prop :=
  exitStatus σ = some 0 →
    ∃ xs answer, claim.abi.parse args = some xs ∧ stdout σ = claim.abi.render answer ∧
      Agrees.{w} claim acc xs answer

/-- **From an outcome to the second clause of `Tier1`** (image-independent), under the
hypotheses of `tier1Stdout_of_outcome`. -/
theorem tier1Exit_of_outcome {claim : Claim} {acc : Src.KernelFront.Accepted} {src : Src.Program}
    {checked : Src.Relevance.Checked} {view : Nat → Option Obs → Option (Option Obs)}
    (hok : GroundOk acc src (Lam.Erase.Input.ofProgram src checked) (view 0) claim.target
      claim.abi)
    (hnat : ViewNat (view 0)) {arity : Nat} (harity : claim.abi.arity = arity)
    (hcanon : ∀ ns : List Nat, ns.length = arity → ReturnsCanon src ns)
    {result : ResultKind} {D : Nat} {args : List (List Nat)} {σ : List Sys}
    (h : IxCC.Exe.Plain.PlainExeOutcome (IxCC.Exe.Plain.srcPlainEval src checked view)
      (fun _ => False) arity result D args σ) :
    Tier1ExitAt.{u} claim acc args σ := by
  intro hexit
  obtain ⟨ns, v, full, hlen, hparse, hmatch, hsrc, rfl, hw⟩ := exit_of_outcome h hexit
  have hns : ns.length = arity := (parseArgsList_ok_length hparse).trans hlen
  obtain ⟨answer, hobs, hag⟩ :=
    agrees_of_srcPlainEval.{u} hok hnat (hns.trans harity.symm) (hcanon ns hns) hsrc
  refine ⟨ns, answer, abi_parse_of_parseArgsList (hlen.trans harity.symm) hparse, ?_, hag⟩
  have hout : stdout (started D ++ full) = stdout full := (written_append 1 (started D) full).trans rfl
  rw [hout]
  cases result with
  | nat =>
    cases hr : claim.abi.result with
    | nat =>
      simp only [IxCC.Exe.Plain.resultObs, abiObs, hr, Obs.nat.injEq] at hobs
      subst hobs
      have hv : v < 2 ^ 63 := (show _ ∧ v < 2 ^ 63 from hmatch).2
      have hl := (natDecimal_length_le v hv).2
      have e : claim.abi.render v = renderPlain .nat v := by
        simp [Abi.render, Abi.resultKind, hr]
      rw [e]
      exact writeSeq_written_full hw (by simp [renderPlain]; omega)
    | enum cs =>
      simp [IxCC.Exe.Plain.resultObs, abiObs, hr] at hobs
  | enum n =>
    cases hr : claim.abi.result with
    | nat =>
      simp [IxCC.Exe.Plain.resultObs, abiObs, hr] at hobs
    | enum cs =>
      have hlt := answer_lt_of_agrees hok hag hr
      simp only [IxCC.Exe.Plain.resultObs, abiObs, hr, Obs.ctor.injEq, and_true] at hobs
      subst hobs
      have hl := (natDecimal_length_le v hlt).2
      have e : claim.abi.render v = renderPlain (.enum n) v := by
        simp [Abi.render, Abi.resultKind, hr, renderPlain]
      rw [e]
      exact writeSeq_written_full hw (by simp [renderPlain]; omega)

/-! ## Both clauses for the checked core -/

/-- **The body of `Tier1` over an image**: both clauses, at every invocation, every loader state
of the image and every finite trace of it. `Tier1 claim envBytes exe` is `∃ acc, Admits claim
envBytes acc ∧` this with `FileTrace exe` for `Trace exe`. -/
def Tier1Core.{w} (claim : Claim) (acc : Src.KernelFront.Accepted) (image : ByteArray) : Prop :=
  ∀ args, ArgsOk args → ∀ s₀, LoadedFile image args s₀ → ∀ σ, Trace image s₀ σ →
    Tier1StdoutAt.{w} claim acc args σ ∧ Tier1ExitAt.{w} claim acc args σ

/-- **Both clauses of `Tier1` for the checked core, with no hypothesis about the source**
(immortal and zero-RC objects). -/
theorem plain_exe_tier1Core_shaped {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {a : Recheck.Artifact} (h : Recheck.run cfg P c = .ok a)
    {layout : X86.Exe.Layout} {inp' : X86.Exe.Input} {ce : X86.Exe.Certified inp'}
    (hb : IxCC.Exe.build a layout = .ok ⟨inp', ce⟩) {inp : Recheck.Input} {sc : Shape2.Cert}
    {claim : Claim} (hg : groundShapeCheck inp c a sc claim.target = .ok claim.abi) :
    Tier1Core.{u} claim inp.kernel.acc ce.bytes := by
  have hs := groundShapeCheck_sound hg
  have harity := recheck_arity h hb hs.ground
  have hp : ∀ ns : List Nat, ns.length = inp'.arity → NeverWrong a.front.source (0, ns) :=
    fun ns hns => hs.neverWrong ns (hns.trans harity.symm)
  have hcanon : ∀ ns : List Nat, ns.length = inp'.arity → ReturnsCanon a.src ns :=
    fun ns hns => hs.canon ns (hns.trans harity.symm)
  intro args hargs s₀ hload σ hσ
  have hout := plain_exe_sound_of_neverWrong h hb hp hargs
    (LoadedFile.toLoaded (IxCC.X86.Exe.Plain.Certified.checked ce) hload) hσ
  exact ⟨tier1Stdout_of_outcome (view := a.front.view) hs.ground (viewNat_viewOf _ _ 0) harity
      hcanon hout,
    tier1Exit_of_outcome (view := a.front.view) hs.ground (viewNat_viewOf _ _ 0) harity hcanon
      hout⟩

/-- **The tier-1 check gives `Admits` and both clauses of `Tier1` for the checked core.** -/
theorem tier1Check_sound_core {claim : Claim} {envBytes : ByteArray} {equations : Lean.Json}
    {roots : List String} {inp : Recheck.Input}
    (hin : Recheck.ingress envBytes equations roots claim.kernelLimits = .ok inp)
    {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert} {a : Recheck.Artifact}
    (h : Recheck.run cfg P c = .ok a)
    {layout : X86.Exe.Layout} {inp' : X86.Exe.Input} {ce : X86.Exe.Certified inp'}
    (hb : IxCC.Exe.build a layout = .ok ⟨inp', ce⟩) {sc : Shape2.Cert}
    (hcheck : tier1Check claim inp c a sc = true) :
    ∃ acc, Admits claim envBytes acc ∧ Tier1Core.{u} claim acc ce.bytes := by
  unfold tier1Check at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨henv, hrole⟩, hg⟩ := hcheck
  cases hgs : groundShapeCheck inp c a sc claim.target with
  | error e => rw [hgs] at hg; cases hg
  | ok abi =>
    rw [hgs] at hg
    have habi : abi = claim.abi := of_decide_eq_true hg
    subst habi
    exact ⟨inp.kernel.acc, admits_of_ingress hin henv hrole, plain_exe_tier1Core_shaped h hb hgs⟩

end IxCC.Correct
