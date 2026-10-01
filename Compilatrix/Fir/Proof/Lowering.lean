import Compilatrix.Fir.Lower
import Compilatrix.Src.Proof.NatMap

/-! # What `Fir.lower` produced

Inversion of the Anf → Fir lowering (`Fir.Lower`), one lemma per Anf
construct: from `Lower.exp A g ρ J st e = .ok (c, st')`, the Fir code `c`
and the lowerings of `e`'s parts, with the name supply threaded through.
The simulation (`Fir.Proof.Sim`) inverts the lowering at each construct it
evaluates. Also: the name supply only grows (`exp_supply`), the program
`Fir.lower` builds (`lower_fun`, `lower_fields`), and the tick bound's
equations (`TickBound`). -/

set_option autoImplicit false

namespace Compilatrix.Fir.Proof

open Compilatrix.Fir.Lower

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β} :
    x.bind f = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x <;> simp [Except.bind]

/-! ## The name supply -/

@[simp] theorem St.bindFresh_fst (st : St) (c : Ixon.V3.LetContract) : (st.bindFresh c).1 = st.vars := by
  simp [St.bindFresh, St.fresh]

@[simp] theorem St.bindFresh_vars (st : St) (c : Ixon.V3.LetContract) :
    (st.bindFresh c).2.vars = st.vars + 1 := by
  simp only [St.bindFresh, St.fresh]; split <;> rfl

@[simp] theorem St.bindFresh_joins (st : St) (c : Ixon.V3.LetContract) :
    (st.bindFresh c).2.joins = st.joins := by
  simp only [St.bindFresh, St.fresh]; split <;> rfl

@[simp] theorem St.fresh_fst (st : St) : st.fresh.1 = st.vars := rfl
@[simp] theorem St.fresh_vars (st : St) : st.fresh.2.vars = st.vars + 1 := rfl
@[simp] theorem St.fresh_joins (st : St) : st.fresh.2.joins = st.joins := rfl
@[simp] theorem St.freshN_fst (st : St) (n : Nat) : (st.freshN n).1 = List.range' st.vars n := rfl
@[simp] theorem St.freshN_vars (st : St) (n : Nat) : (st.freshN n).2.vars = st.vars + n := rfl
@[simp] theorem St.freshN_joins (st : St) (n : Nat) : (st.freshN n).2.joins = st.joins := rfl

/-! ## Atoms -/

theorem atom_var {g : Anf.GlobalId} {ρ : List Var} {i : Nat} {arg : Arg}
    (h : atom g ρ (.var i) = .ok arg) : ∃ x, ρ[i]? = some x ∧ arg = .var x := by
  simp only [atom] at h
  split at h
  · next x hx => cases h; exact ⟨x, hx, rfl⟩
  · cases h

theorem atom_lit {g : Anf.GlobalId} {ρ : List Var} {l : Lam.Lit} {arg : Arg}
    (h : atom g ρ (.lit l) = .ok arg) : arg = .lit l := by
  simp only [atom] at h; cases h; rfl

theorem atom_box {g : Anf.GlobalId} {ρ : List Var} {arg : Arg}
    (h : atom g ρ .box = .ok arg) : arg = .erased := by
  simp only [atom] at h; cases h; rfl

theorem atoms_cons {g : Anf.GlobalId} {ρ : List Var} {a : Anf.Atom} {as : List Anf.Atom} {args : List Arg}
    (h : atoms g ρ (a :: as) = .ok args) :
    ∃ arg args', atom g ρ a = .ok arg ∧ atoms g ρ as = .ok args' ∧ args = arg :: args' := by
  simp only [atoms, bind, Except.bind, pure, Except.pure] at h
  cases ha : atom g ρ a with
  | error => simp [ha] at h
  | ok arg =>
    simp only [ha] at h
    cases has : atoms g ρ as with
    | error => simp [has] at h
    | ok args' => simp only [has, Except.ok.injEq] at h; exact ⟨arg, args', rfl, rfl, h.symm⟩

theorem atoms_nil {g : Anf.GlobalId} {ρ : List Var} {args : List Arg}
    (h : atoms g ρ [] = .ok args) : args = [] := by
  simp only [atoms, Except.ok.injEq] at h; exact h.symm

theorem atoms_length {g : Anf.GlobalId} {ρ : List Var} :
    ∀ {as : List Anf.Atom} {args : List Arg}, atoms g ρ as = .ok args → args.length = as.length
  | [], _, h => by rw [atoms_nil h]; rfl
  | _ :: _, _, h => by
    obtain ⟨_, _, _, h', rfl⟩ := atoms_cons h
    simp [atoms_length h']

/-- An atom as a variable: itself, or a fresh temporary bound by the
prefix. -/
theorem atomVar_inv {g : Anf.GlobalId} {ρ : List Var} {st : St} {a : Anf.Atom} {y : Var}
    {pre : Code → Code} {st' : St} (h : atomVar g ρ st a = .ok (y, pre, st')) :
    (∃ i, a = .var i ∧ ρ[i]? = some y ∧ pre = id ∧ st' = st) ∨
      (∃ arg, (∀ i, a ≠ .var i) ∧ atom g ρ a = .ok arg ∧ y = st.vars ∧
        pre = (fun k => .bind st.vars (.arg arg) k) ∧ st' = st.fresh.2) := by
  cases a with
  | var i =>
    left
    simp only [atomVar, pure, Except.pure] at h
    split at h
    · next x hx => simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨i, rfl, hx, rfl, rfl⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  | lit l =>
    right
    simp only [atomVar, atom, pure, Except.pure, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨.lit l, fun i h => Anf.Atom.noConfusion h, rfl, rfl, rfl, rfl⟩
  | box =>
    right
    simp only [atomVar, atom, pure, Except.pure, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨.erased, fun i h => Anf.Atom.noConfusion h, rfl, rfl, rfl, rfl⟩

/-! ## Expressions, one construct at a time -/

section

variable {A : Anf.Program} {g : Anf.GlobalId} {ρ : List Var} {J : List JoinId} {st : St}
  {code : Code} {st' : St}

theorem exp_call {c : Ixon.V3.LetContract} {h0 : Anf.GlobalId} {as : List Anf.Atom} {e : Anf.Exp}
    (h : exp A g ρ J st (.bind c (.call h0 as) e) = .ok (code, st')) :
    ∃ args, atoms g ρ as = .ok args ∧ h0 < A.size ∧
      ((returnsTop e = true ∧ code = .tcall h0 args ∧ st' = st) ∨
        (returnsTop e = false ∧ ∃ k, exp A g (st.vars :: ρ) J (st.bindFresh c).2 e = .ok (k, st') ∧
          code = .bind st.vars (.call h0 args) k)) := by
  simp only [exp, bind, Except.bind, pure, Except.pure] at h
  cases ha : atoms g ρ as with
  | error => simp [ha] at h
  | ok args =>
    simp only [ha] at h
    refine ⟨args, rfl, ?_⟩
    by_cases hs : h0 < A.size
    · simp only [hs, ↓reduceIte] at h
      refine ⟨hs, ?_⟩
      by_cases hr : returnsTop e = true
      · simp only [hr, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
        exact .inl ⟨hr, h.1.symm, h.2.symm⟩
      · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
        right
        refine ⟨by simpa using hr, ?_⟩
        split at h
        · simp at h
        · rename_i p hk
          simp only [Except.ok.injEq] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h.symm
          exact ⟨p.1, by simpa using hk, by simp⟩
    · simp [hs, throw, throwThe, MonadExceptOf.throw] at h

theorem exp_glob {c : Ixon.V3.LetContract} {h0 : Anf.GlobalId} {e : Anf.Exp}
    (h : exp A g ρ J st (.bind c (.glob h0) e) = .ok (code, st')) :
    h0 < A.size ∧ ∃ hd, A.global? h0 = some hd ∧ hd.ps = [] ∧
      ((returnsTop e = true ∧ code = .tcall h0 [] ∧ st' = st) ∨
        (returnsTop e = false ∧ ∃ k, exp A g (st.vars :: ρ) J (st.bindFresh c).2 e = .ok (k, st') ∧
          code = .bind st.vars (.call h0 []) k)) := by
  simp only [exp, bind, Except.bind, pure, Except.pure] at h
  by_cases hs : h0 < A.size
  · simp only [hs, ↓reduceIte] at h
    refine ⟨hs, ?_⟩
    cases hg : A.global? h0 with
    | none => simp [hg, throw, throwThe, MonadExceptOf.throw] at h
    | some hd =>
      simp only [hg] at h
      by_cases hp : hd.ps.isEmpty = true
      · simp only [hp, ↓reduceIte] at h
        refine ⟨hd, rfl, List.isEmpty_iff.1 hp, ?_⟩
        by_cases hr : returnsTop e = true
        · simp only [hr, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
          exact .inl ⟨hr, h.1.symm, h.2.symm⟩
        · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
          right
          refine ⟨by simpa using hr, ?_⟩
          split at h
          · simp at h
          · rename_i p hk
            simp only [Except.ok.injEq] at h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h.symm
            exact ⟨p.1, by simpa using hk, by simp⟩
      · simp [hp, throw, throwThe, MonadExceptOf.throw] at h
  · simp [hs, throw, throwThe, MonadExceptOf.throw] at h

theorem exp_atom {c : Ixon.V3.LetContract} {a : Anf.Atom} {e : Anf.Exp}
    (h : exp A g ρ J st (.bind c (.atom a) e) = .ok (code, st')) :
    ∃ arg k, atom g ρ a = .ok arg ∧ exp A g (st.vars :: ρ) J (st.bindFresh c).2 e = .ok (k, st') ∧
      code = .bind st.vars (.arg arg) k := by
  simp only [exp, bind, Except.bind, pure, Except.pure] at h
  cases ha : atom g ρ a with
  | error => simp [ha] at h
  | ok arg =>
    simp only [ha] at h
    split at h
    · simp at h
    · rename_i p hk
      simp only [Except.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h.symm
      exact ⟨arg, p.1, rfl, by simpa using hk, by simp⟩

theorem exp_con {c : Ixon.V3.LetContract} {key : Key.CtorKey} {as : List Anf.Atom} {e : Anf.Exp}
    (h : exp A g ρ J st (.bind c (.con key as) e) = .ok (code, st')) :
    ∃ args info k, atoms g ρ as = .ok args ∧ CtorInfo.ofKey A.ctors key = some info ∧
      as.length = info.arity ∧ exp A g (st.vars :: ρ) J (st.bindFresh c).2 e = .ok (k, st') ∧
      code = .bind st.vars (.ctor info args) k := by
  simp only [exp, bind, Except.bind, pure, Except.pure] at h
  cases ha : atoms g ρ as with
  | error => simp [ha] at h
  | ok args =>
    simp only [ha] at h
    cases hi : CtorInfo.ofKey A.ctors key with
    | none => simp [hi, throw, throwThe, MonadExceptOf.throw] at h
    | some info =>
      simp only [hi] at h
      by_cases hl : as.length = info.arity
      · simp only [hl, ↓reduceIte] at h
        split at h
        · simp at h
        · rename_i p hk
          simp only [Except.ok.injEq] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h.symm
          exact ⟨args, info, p.1, rfl, rfl, hl, by simpa using hk, by simp⟩
      · simp [hl, throw, throwThe, MonadExceptOf.throw] at h

theorem exp_proj {c : Ixon.V3.LetContract} {key : Key.CtorKey} {i : Nat} {a : Anf.Atom} {e : Anf.Exp}
    (h : exp A g ρ J st (.bind c (.proj key i a) e) = .ok (code, st')) :
    ∃ y pre st₁ k, atomVar g ρ st a = .ok (y, pre, st₁) ∧
      exp A g (st₁.vars :: ρ) J (st₁.bindFresh c).2 e = .ok (k, st') ∧
      code = pre (.bind st₁.vars (.proj y key i) k) := by
  simp only [exp, bind, Except.bind, pure, Except.pure] at h
  cases ha : atomVar g ρ st a with
  | error => simp [ha] at h
  | ok p =>
    obtain ⟨y, pre, st₁⟩ := p
    simp only [ha] at h
    split at h
    · simp at h
    · rename_i q hk
      simp only [Except.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h.symm
      exact ⟨y, pre, st₁, q.1, rfl, by simpa using hk, by simp⟩

theorem exp_prim {c : Ixon.V3.LetContract} {p : Lam.Prim} {as : List Anf.Atom} {e : Anf.Exp}
    (h : exp A g ρ J st (.bind c (.prim p as) e) = .ok (code, st')) :
    ∃ args k, atoms g ρ as = .ok args ∧ (boolPrim p = true → boolPinsOk A = true) ∧
      exp A g (st.vars :: ρ) J (st.bindFresh c).2 e = .ok (k, st') ∧
      code = .bind st.vars (.prim p args) k := by
  simp only [exp, bind, Except.bind, pure, Except.pure] at h
  cases ha : atoms g ρ as with
  | error => simp [ha] at h
  | ok args =>
    simp only [ha] at h
    by_cases hb : (boolPrim p && !boolPinsOk A) = true
    · simp [hb, throw, throwThe, MonadExceptOf.throw] at h
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · simp at h
      · rename_i q hk
        simp only [Except.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h.symm
        refine ⟨args, q.1, rfl, fun hp => ?_, by simpa using hk, by simp⟩
        simpa [hp] using hb

theorem exp_app {c : Ixon.V3.LetContract} {f : Anf.Atom} {as : List Anf.Atom} {e : Anf.Exp}
    (h : exp A g ρ J st (.bind c (.app f as) e) = .ok (code, st')) : False := by
  simp [exp, throw, throwThe, MonadExceptOf.throw] at h

theorem exp_fn {c : Ixon.V3.LetContract} {ps : List Ixon.V3.BinderContract} {b e : Anf.Exp}
    (h : exp A g ρ J st (.bind c (.fn ps b) e) = .ok (code, st')) : False := by
  simp [exp, throw, throwThe, MonadExceptOf.throw] at h

theorem exp_join {n : Nat} {r : Bool} {b e : Anf.Exp}
    (h : exp A g ρ J st (.join n r b e) = .ok (code, st')) :
    ∃ st₀ body st₁ k, st₀.vars = st.vars + n ∧ st₀.joins = st.joins + 1 ∧
      exp A g ((List.range' st.vars n).reverse ++ ρ) (if r then st.joins :: J else J) st₀ b =
        .ok (body, st₁) ∧
      exp A g ρ (st.joins :: J) st₁ e = .ok (k, st') ∧
      code = .jp st.joins (List.range' st.vars n) r body k := by
  simp only [exp, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i p hb
    split at h
    · simp at h
    · rename_i q hk
      simp only [Except.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h.symm
      exact ⟨_, p.1, p.2, q.1, rfl, rfl, by simpa using hb, hk, by simp⟩

theorem exp_jump {j : Nat} {as : List Anf.Atom}
    (h : exp A g ρ J st (.jump j as) = .ok (code, st')) :
    ∃ args j', atoms g ρ as = .ok args ∧ J[j]? = some j' ∧ code = .jmp j' args ∧ st' = st := by
  simp only [exp, bind, Except.bind, pure, Except.pure] at h
  cases ha : atoms g ρ as with
  | error => simp [ha] at h
  | ok args =>
    simp only [ha] at h
    cases hj : J[j]? with
    | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
    | some j' =>
      simp only [hj, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨args, j', rfl, rfl, h.1.symm, h.2.symm⟩

theorem exp_case {x : Anf.Atom} {alts : List Anf.Alt} {d : Option Anf.Exp}
    (h : exp A g ρ J st (.case x alts d) = .ok (code, st')) :
    ∃ y pre st₁ alts' st₂ d', atomVar g ρ st x = .ok (y, pre, st₁) ∧
      exps A g ρ J y st₁ alts = .ok (alts', st₂) ∧ opt A g ρ J st₂ d = .ok (d', st') ∧
      code = pre (.case y alts' d') := by
  simp only [exp, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i p ha
    obtain ⟨y, pre, st₁⟩ := p
    split at h
    · simp at h
    · rename_i q has
      split at h
      · simp at h
      · rename_i r hd
        simp only [Except.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h.symm
        exact ⟨y, pre, st₁, q.1, q.2, r.1, ha, has, hd, rfl⟩

theorem exp_ret {a : Anf.Atom} (h : exp A g ρ J st (.ret a) = .ok (code, st')) :
    ∃ arg, atom g ρ a = .ok arg ∧ code = .ret arg ∧ st' = st := by
  simp only [exp, bind, Except.bind, pure, Except.pure] at h
  cases ha : atom g ρ a with
  | error => simp [ha] at h
  | ok arg =>
    simp only [ha, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨arg, rfl, h.1.symm, h.2.symm⟩

theorem exp_tick {e : Anf.Exp} (h : exp A g ρ J st (.tick e) = .ok (code, st')) :
    exp A g ρ J st e = .ok (code, st') := by
  simpa [exp] using h

theorem exp_trap (h : exp A g ρ J st .trap = .ok (code, st')) : code = .trap ∧ st' = st := by
  simp only [exp, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem exps_nil {y : Var} {alts' : List Alt} (h : exps A g ρ J y st [] = .ok (alts', st')) :
    alts' = [] ∧ st' = st := by
  simp only [exps, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem exps_cons {y : Var} {key : Key.CtorKey} {n : Nat} {body : Anf.Exp} {as : List Anf.Alt}
    {alts' : List Alt} (h : exps A g ρ J y st (.mk key n body :: as) = .ok (alts', st')) :
    (CtorInfo.ofKey A.ctors key).map (·.arity) = some n ∧ ∃ b st₁ rest,
      exp A g ((List.range' st.vars n).reverse ++ ρ) J (st.freshN n).2 body = .ok (b, st₁) ∧
      exps A g ρ J y st₁ as = .ok (rest, st') ∧
      alts' = .mk key (projections y key body (List.range' st.vars n) 0 b) :: rest := by
  simp only [exps, bind, Except.bind, pure, Except.pure] at h
  by_cases hn : (CtorInfo.ofKey A.ctors key).map (·.arity) = some n
  · simp only [hn, ↓reduceIte] at h
    refine ⟨hn, ?_⟩
    split at h
    · simp at h
    · rename_i p hb
      split at h
      · simp at h
      · rename_i q hr
        simp only [Except.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h.symm
        exact ⟨p.1, p.2, q.1, by simpa using hb, hr, by simp⟩
  · simp [hn, throw, throwThe, MonadExceptOf.throw] at h

theorem opt_none {d' : Option Code} (h : opt A g ρ J st none = .ok (d', st')) : d' = none ∧ st' = st := by
  simp only [opt, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem opt_some {e : Anf.Exp} {d' : Option Code} (h : opt A g ρ J st (some e) = .ok (d', st')) :
    ∃ c, exp A g ρ J st e = .ok (c, st') ∧ d' = some c := by
  simp only [opt, bind, Except.bind, pure, Except.pure] at h
  cases hc : exp A g ρ J st e with
  | error => simp [hc] at h
  | ok p =>
    simp only [hc, Except.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h.symm
    exact ⟨p.1, rfl, rfl⟩

end

/-! ## The supply only grows -/

/-- The supply after a lowering is at least the one before. -/
def Grows (st st' : St) : Prop := st.vars ≤ st'.vars ∧ st.joins ≤ st'.joins

theorem Grows.trans {a b c : St} (h₁ : Grows a b) (h₂ : Grows b c) : Grows a c :=
  ⟨Nat.le_trans h₁.1 h₂.1, Nat.le_trans h₁.2 h₂.2⟩

theorem Grows.refl (a : St) : Grows a a := ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem atomVar_grows {g : Anf.GlobalId} {ρ : List Var} {st : St} {a : Anf.Atom} {y : Var}
    {pre : Code → Code} {st' : St} (h : atomVar g ρ st a = .ok (y, pre, st')) : Grows st st' := by
  rcases atomVar_inv h with ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩
  · exact .refl _
  · exact ⟨by simp, by simp⟩

mutual

theorem exp_grows {A : Anf.Program} {g : Anf.GlobalId} :
    ∀ {ρ : List Var} {J : List JoinId} {st : St} {e : Anf.Exp} {code : Code} {st' : St},
      exp A g ρ J st e = .ok (code, st') → Grows st st'
  | _, _, st, .bind c b e, _, _, h => by
    cases b with
    | call h0 as =>
      obtain ⟨_, _, _, ⟨_, _, rfl⟩ | ⟨_, _, hk, _⟩⟩ := exp_call h
      · exact .refl _
      · exact Grows.trans ⟨by simp, by simp⟩ (exp_grows hk)
    | glob h0 =>
      obtain ⟨_, _, _, _, ⟨_, _, rfl⟩ | ⟨_, _, hk, _⟩⟩ := exp_glob h
      · exact .refl _
      · exact Grows.trans ⟨by simp, by simp⟩ (exp_grows hk)
    | atom a =>
      obtain ⟨_, _, _, hk, _⟩ := exp_atom h
      exact Grows.trans ⟨by simp, by simp⟩ (exp_grows hk)
    | con key as =>
      obtain ⟨_, _, _, _, _, _, hk, _⟩ := exp_con h
      exact Grows.trans ⟨by simp, by simp⟩ (exp_grows hk)
    | proj key i a =>
      obtain ⟨_, _, st₁, _, ha, hk, _⟩ := exp_proj h
      exact (atomVar_grows ha).trans (Grows.trans ⟨by simp, by simp⟩ (exp_grows hk))
    | prim p as =>
      obtain ⟨_, _, _, _, hk, _⟩ := exp_prim h
      exact Grows.trans ⟨by simp, by simp⟩ (exp_grows hk)
    | app f as => exact (exp_app h).elim
    | fn ps b => exact (exp_fn h).elim
  | _, _, st, .join n r b e, _, _, h => by
    obtain ⟨st₀, _, _, _, h₀v, h₀j, hb, hk, _⟩ := exp_join h
    exact Grows.trans ⟨by omega, by omega⟩ ((exp_grows hb).trans (exp_grows hk))
  | _, _, _, .jump j as, _, _, h => by
    obtain ⟨_, _, _, _, _, rfl⟩ := exp_jump h
    exact .refl _
  | _, _, _, .case x alts d, _, _, h => by
    obtain ⟨_, _, _, _, _, _, ha, has, hd, _⟩ := exp_case h
    exact (atomVar_grows ha).trans ((exps_grows has).trans (opt_grows hd))
  | _, _, _, .ret a, _, _, h => by
    obtain ⟨_, _, _, rfl⟩ := exp_ret h
    exact .refl _
  | _, _, _, .tick e, _, _, h => exp_grows (exp_tick h)
  | _, _, _, .trap, _, _, h => by
    obtain ⟨_, rfl⟩ := exp_trap h
    exact .refl _

theorem exps_grows {A : Anf.Program} {g : Anf.GlobalId} :
    ∀ {ρ : List Var} {J : List JoinId} {y : Var} {st : St} {alts : List Anf.Alt} {alts' : List Alt}
      {st' : St}, exps A g ρ J y st alts = .ok (alts', st') → Grows st st'
  | _, _, _, _, [], _, _, h => by
    obtain ⟨_, rfl⟩ := exps_nil h
    exact .refl _
  | _, _, _, st, .mk key n body :: as, _, _, h => by
    obtain ⟨_, _, _, _, hb, hr, _⟩ := exps_cons h
    exact Grows.trans ⟨by simp, by simp⟩ ((exp_grows hb).trans (exps_grows hr))

theorem opt_grows {A : Anf.Program} {g : Anf.GlobalId} :
    ∀ {ρ : List Var} {J : List JoinId} {st : St} {d : Option Anf.Exp} {d' : Option Code} {st' : St},
      opt A g ρ J st d = .ok (d', st') → Grows st st'
  | _, _, _, none, _, _, h => by
    obtain ⟨_, rfl⟩ := opt_none h
    exact .refl _
  | _, _, _, some e, _, _, h => by
    obtain ⟨_, hc, _⟩ := opt_some h
    exact exp_grows hc

end

/-! ## Functions and the program -/

theorem function_ok {A : Anf.Program} {g : Anf.GlobalId} {gd : Anf.GDef} {fd : Fun}
    (h : function A g gd = .ok fd) :
    ∃ st, exp A g (List.range gd.ps.length).reverse [] { vars := gd.ps.length } gd.body = .ok (fd.body, st) ∧
      fd.params = (List.range gd.ps.length).map (·, .tobj) := by
  simp only [function, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i p hp
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨p.2, by simpa using hp, rfl⟩

theorem functions_ok {A : Anf.Program} :
    ∀ {gs : List Anf.GlobalId} {fs : List (FunId × Fun)}, functions A gs = .ok fs →
      fs.map (·.1) = gs ∧ ∀ g fd, (g, fd) ∈ fs → ∃ gd, A.global? g = some gd ∧ function A g gd = .ok fd
  | [], fs, h => by
    simp only [functions, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun _ _ h => by cases h⟩
  | g :: gs, fs, h => by
    simp only [functions, bind, Except.bind, pure, Except.pure] at h
    split at h
    · next gd hgd =>
      split at h
      · simp at h
      · rename_i fd hfd
        split at h
        · simp at h
        · rename_i fs' hfs
          simp only [Except.ok.injEq] at h
          subst h
          obtain ⟨hm, hall⟩ := functions_ok hfs
          refine ⟨by simp [hm], fun g' fd' hmem => ?_⟩
          rcases List.mem_cons.1 hmem with e | hmem
          · cases e; exact ⟨gd, hgd, hfd⟩
          · exact hall g' fd' hmem
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- What `Fir.lower` checks, and the program it builds. -/
theorem lower_ok {A : Anf.Program} {F : Program} (h : lower A = .ok F) :
    (residual A).isEmpty = true ∧ pinsOk A = true ∧ (∀ r ∈ A.roots, r < A.size) ∧
      ∃ fs, functions A (List.range A.size) = .ok fs ∧
        F = { funs := Src.NatMap.ofList fs, size := A.size, exports := A.roots, ctors := A.ctors
              known := A.known } := by
  simp only [lower, bind, Except.bind, pure, Except.pure] at h
  by_cases hr : (residual A).isEmpty = true
  · simp only [hr, ↓reduceIte] at h
    by_cases hp : pinsOk A = true
    · simp only [hp, ↓reduceIte] at h
      refine ⟨hr, hp, ?_⟩
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · next hfind =>
        have hroots : ∀ r ∈ A.roots, r < A.size := by
          intro r hmem
          have := List.find?_eq_none.1 (by
            cases hf : List.find? (fun x => decide (A.size ≤ x)) A.roots with
            | none => rfl
            | some r' => exact absurd hf (hfind r')) r hmem
          simp at this
          omega
        refine ⟨hroots, ?_⟩
        split at h
        · simp at h
        · rename_i fs hfs
          simp only [Except.ok.injEq] at h
          exact ⟨fs, hfs, h.symm⟩
    · simp [hp, throw, throwThe, MonadExceptOf.throw] at h
  · simp [hr, throw, throwThe, MonadExceptOf.throw] at h

theorem lower_fields {A : Anf.Program} {F : Program} (h : lower A = .ok F) :
    F.size = A.size ∧ F.exports = A.roots ∧ F.ctors = A.ctors ∧ F.known = A.known := by
  obtain ⟨_, _, _, _, _, rfl⟩ := lower_ok h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every global below the size is the function its lowering gives. -/
theorem lower_fun {A : Anf.Program} {F : Program} (h : lower A = .ok F) {g : Anf.GlobalId}
    {gd : Anf.GDef} (hg : A.global? g = some gd) (hs : g < A.size) :
    ∃ fd, F.fun? g = some fd ∧ function A g gd = .ok fd := by
  obtain ⟨_, _, _, fs, hfs, rfl⟩ := lower_ok h
  obtain ⟨hm, hall⟩ := functions_ok hfs
  have hmem : g ∈ fs.map (·.1) := by rw [hm]; exact List.mem_range.2 hs
  obtain ⟨⟨g', fd⟩, hfd, rfl⟩ := List.mem_map.1 hmem
  obtain ⟨gd', hgd', hf⟩ := hall g' fd hfd
  rw [hg] at hgd'
  cases hgd'
  refine ⟨fd, ?_, hf⟩
  simp only [Program.fun?]
  exact Src.NatMap.get?_ofList (by rw [hm]; exact List.nodup_range) hfd

/-! ## The tick bound -/

theorem le_foldl_max {α : Type} (f : α → Nat) :
    ∀ (l : List α) (m : Nat), m ≤ l.foldl (fun n x => max n (f x)) m
  | [], _ => Nat.le_refl _
  | _ :: l, _ => Nat.le_trans (Nat.le_max_left _ _) (le_foldl_max f l _)

theorem le_foldl_max_of_mem {α : Type} (f : α → Nat) :
    ∀ (l : List α) (m : Nat) (p : α), p ∈ l → f p ≤ l.foldl (fun n x => max n (f x)) m
  | [], _, _, h => by cases h
  | q :: l, m, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_max f l _)
    · exact le_foldl_max_of_mem f l _ p hp

/-- Every global's tick depth is below the program's tick bound. -/
theorem tickDepth_lt {A : Anf.Program} {g : Anf.GlobalId} {gd : Anf.GDef} (hg : A.global? g = some gd)
    (hs : g < A.size) : tickDepth gd < tickBound A := by
  have hmem : (g, gd) ∈ A.globalList := by
    simp only [Anf.Program.globalList, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff]
    exact ⟨g, hs, gd, hg, rfl⟩
  have e : tickBound A = 1 + A.globalList.foldl (fun n x => max n (tickDepth x.2)) 0 := rfl
  have := le_foldl_max_of_mem (fun x : Anf.GlobalId × Anf.GDef => tickDepth x.2) A.globalList 0 _ hmem
  simp only at this
  omega

theorem tickDepth_ge (gd : Anf.GDef) :
    (TickBound.exp [] gd.body).1 ≤ tickDepth gd ∧ (TickBound.exp [] gd.body).2 ≤ tickDepth gd := by
  unfold tickDepth
  exact ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩

end Compilatrix.Fir.Proof
