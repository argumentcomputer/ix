import IxCC.Own.Plain.Proof.Owned.PrimStep

/-! # What the checker's acceptance of each construct says

One lemma per construct of `checkCode`: the facts its `do` block established. A binding is
inverted twice: `checkCode_bindStep` gives the step the checker ran (`bindStep`: a primitive
under its signature), `checkCode_bind` the same fact through `bindCtx`, which it equals
(`bindStep_eq_bindCtx`). `primStep_ok` is what an accepted primitive step established. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open IxCC.Fir (Var Arg)

theorem except_bind_ok' {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem checkCode_inc {Δ : JCtx} {Γ : Ctx} {x : Var} {n : Nat} {k : Code}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known}
    (h : checkCode Δ Γ (.act (.inc x n) k) borrows uniqs retUniq ctors known = .ok ()) :
    ∃ Γ', Γ.inc x n = .ok Γ' ∧ checkCode Δ Γ' k borrows uniqs retUniq ctors known = .ok () := by
  simp only [checkCode] at h
  exact except_bind_ok' h

theorem checkCode_dec {Δ : JCtx} {Γ : Ctx} {x : Var} {k : Code}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known}
    (h : checkCode Δ Γ (.act (.dec x) k) borrows uniqs retUniq ctors known = .ok ()) :
    ∃ Γ', Γ.dec x = .ok Γ' ∧ checkCode Δ Γ' k borrows uniqs retUniq ctors known = .ok () := by
  simp only [checkCode] at h
  exact except_bind_ok' h

/-- The step the checker ran at a binding. -/
theorem checkCode_bindStep {Δ : JCtx} {Γ : Ctx} {x : Var} {r : Fir.Rhs} {k : Code}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known}
    (h : checkCode Δ Γ (.bind x r k) borrows uniqs retUniq ctors known = .ok ()) :
    ∃ Γ', bindStep Γ x r borrows uniqs ctors = .ok Γ' ∧
      checkCode Δ Γ' k borrows uniqs retUniq ctors known = .ok () := by
  simp only [checkCode] at h
  cases hk : Γ.known x
  · simp only [hk, Bool.false_eq_true, ↓reduceIte] at h
    cases hb : bindStep Γ x r borrows uniqs ctors with
    | error e => rw [hb] at h; cases h
    | ok Γ' => rw [hb] at h; exact ⟨Γ', rfl, h⟩
  · simp only [hk, ↓reduceIte] at h
    cases h

/-- The same through `bindCtx`, the rule `bindStep` equals on every right-hand side of today. -/
theorem checkCode_bind {Δ : JCtx} {Γ : Ctx} {x : Var} {r : Fir.Rhs} {k : Code}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known}
    (h : checkCode Δ Γ (.bind x r k) borrows uniqs retUniq ctors known = .ok ()) :
    ∃ Γ', bindCtx Γ x r borrows uniqs ctors = .ok Γ' ∧
      checkCode Δ Γ' k borrows uniqs retUniq ctors known = .ok () := by
  obtain ⟨Γ', hb, hk⟩ := checkCode_bindStep h
  exact ⟨Γ', by rw [← bindStep_eq_bindCtx _ _ _ _ _ _ (bindStep_isArrPrim hb)]; exact hb, hk⟩

/-- **What an accepted primitive step established**: every argument available; the consumed
ones taken (`Γ₁`); the others still held in `Γ₁`; and the context is `Γ₁` with the marked
arguments immediates, a release if the signature has one, and the result bound. -/
theorem primStep_ok {Γ Γ' : Ctx} {sig : PrimSig} {x : Var} {args : List Arg}
    (h : primStep Γ sig x args = .ok Γ') :
    ∃ Γ₁, Γ.needArgs args = .ok () ∧ takeConsumed Γ sig.args args = .ok Γ₁ ∧
      checkRead Γ₁ sig.args args = .ok () ∧
      Γ' = bindResult
        (if sig.release then (markImm Γ₁ sig.args args).release else markImm Γ₁ sig.args args)
        x sig.result := by
  rw [primStep_eq] at h
  obtain ⟨⟨⟩, h1, h⟩ := except_bind_ok' h
  obtain ⟨Γ₁, h2, h⟩ := except_bind_ok' h
  obtain ⟨⟨⟩, h3, h⟩ := except_bind_ok' h
  exact ⟨Γ₁, h1, h2, h3, (Except.ok.inj h).symm⟩

theorem checkCode_reset {Δ : JCtx} {Γ : Ctx} {s : Nat} {x : Var} {ctor : Fir.CtorInfo}
    {fields : List (Option Var)} {uniq : Bool} {k : Code}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known}
    (h : checkCode Δ Γ (.reset s x ctor fields uniq k) borrows uniqs retUniq ctors known = .ok ()) :
    ∃ Γ', Γ.reset ctors s x ctor fields uniq known = .ok Γ' ∧
      checkCode Δ Γ' k borrows uniqs retUniq ctors known = .ok () := by
  simp only [checkCode] at h
  exact except_bind_ok' h

theorem checkCode_reuse {Δ : JCtx} {Γ : Ctx} {x : Var} {s : Nat} {ctor : Fir.CtorInfo}
    {args : List Arg} {uniq : Bool} {k : Code}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known}
    (h : checkCode Δ Γ (.reuse x s ctor args uniq k) borrows uniqs retUniq ctors known = .ok ()) :
    ∃ Γ', Γ.reuse ctors x s ctor args uniq known = .ok Γ' ∧
      checkCode Δ Γ' k borrows uniqs retUniq ctors known = .ok () := by
  simp only [checkCode] at h
  exact except_bind_ok' h

theorem checkCode_dropSlot {Δ : JCtx} {Γ : Ctx} {s : Nat} {k : Code}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known}
    (h : checkCode Δ Γ (.dropSlot s k) borrows uniqs retUniq ctors known = .ok ()) :
    ∃ Γ', Γ.dropSlot s = .ok Γ' ∧ checkCode Δ Γ' k borrows uniqs retUniq ctors known = .ok () := by
  simp only [checkCode] at h
  exact except_bind_ok' h

theorem checkCode_jp {Δ : JCtx} {Γ : Ctx} {j : Fir.JoinId} {ps captured : List Var} {rec : Bool}
    {body k : Code} {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known}
    (h : checkCode Δ Γ (.jp j ps captured rec body k) borrows uniqs retUniq ctors known = .ok ()) :
    nodupVars captured = true ∧ Γ.needCaptured j captured = .ok () ∧
      checkCode (if rec then Δ.insert j captured else Δ) (Γ.enter captured ps) body
        borrows uniqs retUniq ctors known = .ok () ∧
      checkCode (Δ.insert j captured) Γ k borrows uniqs retUniq ctors known = .ok () := by
  simp only [checkCode] at h
  cases hn : nodupVars captured
  · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
    cases h
  · simp only [hn, ↓reduceIte] at h
    obtain ⟨⟨⟩, h1, h⟩ := except_bind_ok' h
    obtain ⟨⟨⟩, h2, h⟩ := except_bind_ok' h
    exact ⟨rfl, h1, h2, h⟩

theorem checkCode_jmp {Δ : JCtx} {Γ : Ctx} {j : Fir.JoinId} {args : List Arg}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known}
    (h : checkCode Δ Γ (.jmp j args) borrows uniqs retUniq ctors known = .ok ()) :
    ∃ captured Γ₁ Γ₂, Δ.get? j = some captured ∧ Γ.takeArgs args = .ok Γ₁ ∧
      Γ₁.takeVars captured = .ok Γ₂ ∧ Γ₂.closed s!"jump to j{j}" = .ok () := by
  simp only [checkCode] at h
  cases hd : Δ.get? j with
  | none => rw [hd] at h; cases h
  | some captured =>
    rw [hd] at h
    obtain ⟨Γ₁, h1, h⟩ := except_bind_ok' h
    obtain ⟨Γ₂, h2, h⟩ := except_bind_ok' h
    exact ⟨captured, Γ₁, Γ₂, rfl, h1, h2, h⟩

theorem checkCode_case {Δ : JCtx} {Γ : Ctx} {x : Var} {alts : List Alt} {d : Option Code}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known}
    (h : checkCode Δ Γ (.case x alts d) borrows uniqs retUniq ctors known = .ok ()) :
    Γ.need x "scrutinised" = .ok () ∧
      checkAlts Δ Γ x alts borrows uniqs retUniq ctors known = .ok () ∧
      checkOpt Δ Γ d borrows uniqs retUniq ctors known = .ok () := by
  simp only [checkCode] at h
  obtain ⟨⟨⟩, h1, h⟩ := except_bind_ok' h
  obtain ⟨⟨⟩, h2, h3⟩ := except_bind_ok' h
  exact ⟨h1, h2, h3⟩

theorem checkCode_ret {Δ : JCtx} {Γ : Ctx} {a : Arg}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known}
    (h : checkCode Δ Γ (.ret a) borrows uniqs retUniq ctors known = .ok ()) :
    (retUniq = true → ∀ y, a = .var y → Γ.isUniq y = true) ∧
      ∃ Γ', Γ.takeArg a = .ok Γ' ∧ Γ'.closed "return" = .ok () := by
  simp only [checkCode] at h
  cases retUniq with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact ⟨(fun hc => by cases hc), except_bind_ok' h⟩
  | true =>
    simp only [↓reduceIte] at h
    cases a with
    | lit _ | erased =>
      exact ⟨(fun _ _ he => by cases he), except_bind_ok' h⟩
    | var y =>
      cases hu : Γ.isUniq y with
      | false =>
        simp [hu, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      | true =>
        simp only [hu, ↓reduceIte] at h
        refine ⟨(fun _ y' he => by cases he; exact hu), except_bind_ok' h⟩

theorem checkCode_tcall {Δ : JCtx} {Γ : Ctx} {f : Fir.FunId} {args : List Arg}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known}
    (h : checkCode Δ Γ (.tcall f args) borrows uniqs retUniq ctors known = .ok ()) :
    (retUniq = true → (uniqs.getD f ([], false)).2 = true) ∧
      ∃ Γ', Γ.takeOwnedUniqueArgs (borrows.getD f []) (uniqs.getD f ([], false)).1 args = .ok Γ' ∧
        Γ'.checkTailBorrowed (borrows.getD f []) args = .ok () ∧
        Γ'.closed s!"tail call of f{f}" = .ok () := by
  simp only [checkCode] at h
  by_cases hret : (retUniq && !(uniqs.getD f ([], false)).2) = true
  · simp [hret, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · have hretF : (retUniq && !(uniqs.getD f ([], false)).2) = false := by
      cases hb : (retUniq && !(uniqs.getD f ([], false)).2)
      · rfl
      · exact absurd hb hret
    simp only [hretF, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨Γ', h1, h⟩ := except_bind_ok' h
    obtain ⟨⟨⟩, h2, h3⟩ := except_bind_ok' h
    refine ⟨fun hr => ?_, Γ', h1, h2, h3⟩
    subst hr
    simpa using hretF

theorem checkAlts_cons {Δ : JCtx} {Γ : Ctx} {x : Var} {key : Key.CtorKey} {body : Code}
    {rest : List Alt} {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known}
    (h : checkAlts Δ Γ x (.mk key body :: rest) borrows uniqs retUniq ctors known = .ok ()) :
    checkCode Δ (Γ.setCtor x key) body borrows uniqs retUniq ctors known = .ok () ∧
      checkAlts Δ Γ x rest borrows uniqs retUniq ctors known = .ok () := by
  simp only [checkAlts] at h
  obtain ⟨⟨⟩, h1, h2⟩ := except_bind_ok' h
  exact ⟨h1, h2⟩

end IxCC.Own.Plain
