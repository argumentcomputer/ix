import IxCC.Own.Plain.Proof.Owned.Context

/-! # What the checker's acceptance of each construct says

One lemma per construct of `checkCode`: the facts its `do` block established. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open IxCC.Fir (Var Arg)

theorem except_bind_ok' {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem checkCode_inc {Δ : JCtx} {Γ : Ctx} {x : Var} {n : Nat} {k : Code}
    (h : checkCode Δ Γ (.act (.inc x n) k) = .ok ()) :
    ∃ Γ', Γ.inc x n = .ok Γ' ∧ checkCode Δ Γ' k = .ok () := by
  simp only [checkCode] at h
  exact except_bind_ok' h

theorem checkCode_dec {Δ : JCtx} {Γ : Ctx} {x : Var} {k : Code}
    (h : checkCode Δ Γ (.act (.dec x) k) = .ok ()) :
    ∃ Γ', Γ.dec x = .ok Γ' ∧ checkCode Δ Γ' k = .ok () := by
  simp only [checkCode] at h
  exact except_bind_ok' h

theorem checkCode_bind {Δ : JCtx} {Γ : Ctx} {x : Var} {r : Fir.Rhs} {k : Code}
    (h : checkCode Δ Γ (.bind x r k) = .ok ()) :
    ∃ Γ', bindCtx Γ x r = .ok Γ' ∧ checkCode Δ Γ' k = .ok () := by
  simp only [checkCode] at h
  cases hk : Γ.known x
  · simp only [hk, Bool.false_eq_true, ↓reduceIte] at h
    cases hb : bindCtx Γ x r with
    | error e => rw [hb] at h; cases h
    | ok Γ' => rw [hb] at h; exact ⟨Γ', rfl, h⟩
  · simp only [hk, ↓reduceIte] at h
    cases h

theorem checkCode_jp {Δ : JCtx} {Γ : Ctx} {j : Fir.JoinId} {ps captured : List Var} {rec : Bool}
    {body k : Code} (h : checkCode Δ Γ (.jp j ps captured rec body k) = .ok ()) :
    nodupVars captured = true ∧ Γ.needCaptured j captured = .ok () ∧
      checkCode (if rec then Δ.insert j captured else Δ) (Γ.enter captured ps) body = .ok () ∧
      checkCode (Δ.insert j captured) Γ k = .ok () := by
  simp only [checkCode] at h
  cases hn : nodupVars captured
  · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
    cases h
  · simp only [hn, ↓reduceIte, pure_bind] at h
    obtain ⟨⟨⟩, h1, h⟩ := except_bind_ok' h
    obtain ⟨⟨⟩, h2, h⟩ := except_bind_ok' h
    exact ⟨rfl, h1, h2, h⟩

theorem checkCode_jmp {Δ : JCtx} {Γ : Ctx} {j : Fir.JoinId} {args : List Arg}
    (h : checkCode Δ Γ (.jmp j args) = .ok ()) :
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
    (h : checkCode Δ Γ (.case x alts d) = .ok ()) :
    Γ.need x "scrutinised" = .ok () ∧ checkAlts Δ Γ alts = .ok () ∧ checkOpt Δ Γ d = .ok () := by
  simp only [checkCode] at h
  obtain ⟨⟨⟩, h1, h⟩ := except_bind_ok' h
  obtain ⟨⟨⟩, h2, h3⟩ := except_bind_ok' h
  exact ⟨h1, h2, h3⟩

theorem checkCode_ret {Δ : JCtx} {Γ : Ctx} {a : Arg} (h : checkCode Δ Γ (.ret a) = .ok ()) :
    ∃ Γ', Γ.takeArg a = .ok Γ' ∧ Γ'.closed "return" = .ok () := by
  simp only [checkCode] at h
  exact except_bind_ok' h

theorem checkCode_tcall {Δ : JCtx} {Γ : Ctx} {f : Fir.FunId} {args : List Arg}
    (h : checkCode Δ Γ (.tcall f args) = .ok ()) :
    ∃ Γ', Γ.takeArgs args = .ok Γ' ∧ Γ'.closed s!"tail call of f{f}" = .ok () := by
  simp only [checkCode] at h
  exact except_bind_ok' h

theorem checkAlts_cons {Δ : JCtx} {Γ : Ctx} {key : Key.CtorKey} {body : Code} {rest : List Alt}
    (h : checkAlts Δ Γ (.mk key body :: rest) = .ok ()) :
    checkCode Δ Γ body = .ok () ∧ checkAlts Δ Γ rest = .ok () := by
  simp only [checkAlts] at h
  obtain ⟨⟨⟩, h1, h2⟩ := except_bind_ok' h
  exact ⟨h1, h2⟩

end IxCC.Own.Plain
