import IxCC.Anf.Proof.Convert.Prog

/-! # ANF conversion: continuations

Conversion is in continuation-passing style: a term is converted with a
continuation (`Kont`) that is `ret`, a jump to a join point, or a
meta-continuation producing the rest of the target code once the value's
operand is known. Its simulation relates the target code to the *source*
computation followed by a source continuation `SK` (P1, M2.3):

* `KontR n dj k SK ρ' J'`: `ret` returns a related value; `jump l` jumps to
  a one-parameter join closure whose body simulates `SK`; a
  meta-continuation `f` simulates `SK` on every related operand, in every
  target environment that extends the current one (`KFunR`; levels keep
  their values, so code built later stays valid).
* `emit_sim` and `pass_sim`: binding a right-hand side, or passing an
  operand, to a related continuation.
* Pure Lam terms (`pureTerm`) evaluate to one value at every clock.
* Expected and binder kinds (`KindOk`, `Compat`), and the head of a spine
  (`GroupHead`). -/

set_option autoImplicit false

namespace IxCC.Anf.Convert.Proof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Lam (Kind Mode)
open IxCC.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName)
open IxCC.Ixon

namespace Setting

variable (S : Setting)

/-- Plain related values. -/
abbrev V : Lam.Val → Val → Prop := VR S.A S.G

/-- An operand whose value in the target environment is related. -/
def OpdR (x : Lam.Val) (o : Opd) (ρ : List Val) : Prop := ∃ w, o.val ρ = some w ∧ S.V x w

/-- A meta-continuation simulates `SK` on every matching operand, in every
extension of the target environments. -/
def KFunR {α β : Type} (n : Nat) (ρ' : List Val) (J' : List JClo) (Match : α → β → List Val → Prop)
    (f : Nat → Nat → β → M Exp) (SK : α → Nat → Result Lam.Val) : Prop :=
  ∀ ⦃d' dj' : Nat⦄ ⦃b : β⦄ ⦃e : Exp⦄ ⦃ρ'' : List Val⦄ ⦃J'' : List JClo⦄, f d' dj' b = .ok e →
    ρ''.length = d' → ρ' <:+ ρ'' → J''.length = dj' → J' <:+ J'' →
    ∀ x, Match x b ρ'' → SimUpTo S.V n (SK x) (fun k => eval S.Q k ρ'' J'' e)

/-- A continuation against a source continuation, at join depth `dj`. -/
def KontR (n dj : Nat) : Kont → (Lam.Val → Nat → Result Lam.Val) → List Val → List JClo → Prop
  | .ret, SK, _, _ => ∀ x w, S.V x w → SimUpTo S.V n (SK x) (fun _ => .ok w)
  | .jump l, SK, _, J' => l < dj ∧ ∃ ρj Jj bj, J'[dj - 1 - l]? = some (.mk ρj Jj 1 bj false) ∧
      ∀ x w, S.V x w → SimUpTo S.V n (SK x) (fun k => eval S.Q k (w :: ρj) Jj bj)
  | .bind _ f, SK, ρ', J' => S.KFunR n ρ' J' S.OpdR f SK

variable {S}

theorem KFunR.suffix {α β : Type} {n : Nat} {ρ' ρ₂ : List Val} {J' J₂ : List JClo}
    {Match : α → β → List Val → Prop} {f : Nat → Nat → β → M Exp} {SK : α → Nat → Result Lam.Val}
    (h : S.KFunR n ρ' J' Match f SK) (hρ : ρ' <:+ ρ₂) (hJ : J' <:+ J₂) :
    S.KFunR n ρ₂ J₂ Match f SK :=
  fun _ _ _ _ _ _ hf hd hρ' hdj hJ' x hx => h hf hd (hρ.trans hρ') hdj (hJ.trans hJ') x hx

theorem getElem?_suffix {α : Type} {xs ys : List α} (h : xs <:+ ys) {i : Nat} (hi : i < xs.length) :
    ys[ys.length - xs.length + i]? = xs[i]? := by
  obtain ⟨u, rfl⟩ := h
  rw [List.getElem?_append_right (by simp)]
  simp

theorem KontR.suffix {n dj dj₂ : Nat} {k : Kont} {SK : Lam.Val → Nat → Result Lam.Val}
    {ρ' ρ₂ : List Val} {J' J₂ : List JClo} (h : S.KontR n dj k SK ρ' J') (hρ : ρ' <:+ ρ₂)
    (hJ : J' <:+ J₂) (hl : J'.length = dj) (hl₂ : J₂.length = dj₂) : S.KontR n dj₂ k SK ρ₂ J₂ := by
  cases k with
  | ret => exact h
  | jump l =>
    obtain ⟨hl', ρj, Jj, bj, hj, hsim⟩ := h
    have hle : dj ≤ dj₂ := by rw [← hl, ← hl₂]; exact hJ.length_le
    refine ⟨by omega, ρj, Jj, bj, ?_, hsim⟩
    have := getElem?_suffix hJ (i := dj - 1 - l) (by omega)
    rw [hl, hl₂, show dj₂ - dj + (dj - 1 - l) = dj₂ - 1 - l by omega] at this
    rw [this, hj]
  | bind c f => exact KFunR.suffix h hρ hJ

/-! ## Emitting a binding, passing an operand -/

theorem jump_eval {Q : Program} {k : Nat} {ρ' : List Val} {J' : List JClo} {idx : Nat} {a : Atom}
    {ρj : List Val} {Jj : List JClo} {bj : Exp} {w : Val} (hj : J'[idx]? = some (.mk ρj Jj 1 bj false))
    (ha : a.eval ρ' = some w) :
    eval Q k ρ' J' (.jump idx [a]) = later k fun k => eval Q k (w :: ρj) Jj bj := by
  rw [eval_jump_of Q k ρ' J' hj (vs := [w]) (by simp [evalAtoms, ha]) rfl]
  rfl

theorem emit_sim {n : Nat} {cx : Cx} {b : Bind} {k : Kont} {e : Exp} (h : emit cx b k = .ok e)
    {ρ' : List Val} {J' : List JClo} (hd : ρ'.length = cx.d) (hdj : J'.length = cx.dj)
    {SK : Lam.Val → Nat → Result Lam.Val} (hk : S.KontR n cx.dj k SK ρ' J') {c : Nat → Result Lam.Val}
    (hb : SimUpTo S.V n c (fun k => evalBind S.Q k ρ' b)) :
    SimUpTo S.V n (fun k => (c k).bind (SK · k)) (fun k => eval S.Q k ρ' J' e) := by
  cases k with
  | ret =>
    cases h
    refine (SimUpTo.bind (evalBind_mono S.Q ρ' b) (fun w => ClockMono.const _) hb
      fun x w hxw => hk x w hxw).congr (fun _ => rfl) (fun k => ?_)
    rw [eval_bind]
    exact Result.bind_congr _ fun w => by rw [eval_ret']; rfl
  | jump l =>
    cases h
    obtain ⟨hl, ρj, Jj, bj, hj, hsim⟩ := hk
    refine (SimUpTo.bind (evalBind_mono S.Q ρ' b)
      (fun w => ClockMono.later (eval_mono S.Q (w :: ρj) Jj bj)) hb
      fun x w hxw => SimUpTo.laterR (eval_mono S.Q _ _ _) (hsim x w hxw)).congr
      (fun _ => rfl) (fun k => ?_)
    rw [eval_bind]
    exact Result.bind_congr _ fun w => jump_eval (by simpa using hj) (by simp [Atom.eval])
  | bind c f =>
    obtain ⟨e', he', h⟩ := Lam.ModesOk.bind_ok h
    cases h
    refine (SimUpTo.bind (evalBind_mono S.Q ρ' b) (fun w => eval_mono S.Q (w :: ρ') J' e') hb
      fun x w hxw => hk he' (by simp [hd]) (List.suffix_cons w ρ') hdj (List.suffix_refl J') x
        ⟨w, by rw [← hd]; exact Opd.val_lvl_top ρ' w, hxw⟩).congr (fun _ => rfl) (fun k => ?_)
    exact eval_bind S.Q k ρ' J' c b e'

theorem pass_sim {n : Nat} {cx : Cx} {o : Opd} {k : Kont} {e : Exp} (h : pass cx o k = .ok e)
    {ρ' : List Val} {J' : List JClo} (hd : ρ'.length = cx.d) (hdj : J'.length = cx.dj)
    {SK : Lam.Val → Nat → Result Lam.Val} (hk : S.KontR n cx.dj k SK ρ' J') {x : Lam.Val} {w : Val}
    (ho : o.val ρ' = some w) (hx : S.V x w) :
    SimUpTo S.V n (SK x) (fun k => eval S.Q k ρ' J' e) := by
  cases k with
  | ret =>
    cases h
    refine (hk x w hx).congr (fun _ => rfl) (fun k => ?_)
    rw [eval_ret', ← hd, Opd.val_atom ho]; rfl
  | jump l =>
    cases h
    obtain ⟨hl, ρj, Jj, bj, hj, hsim⟩ := hk
    refine (SimUpTo.laterR (eval_mono S.Q _ _ _) (hsim x w hx)).congr (fun _ => rfl) (fun k => ?_)
    rw [← hd]
    exact jump_eval hj (Opd.val_atom ho)
  | bind c f => exact hk h hd (List.suffix_refl ρ') hdj (List.suffix_refl J') x ⟨w, ho, hx⟩

end Setting

end IxCC.Anf.Convert.Proof
