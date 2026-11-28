import IxCC.Own.Plain.Sink
import IxCC.Fir.Proof.Lang
import IxCC.Src.Proof.NatMap
import IxCC.Sem.Forall2

/-! # Soundness of dead-arm constructor allocation sinking (`Own.Plain.Sink`)

Proves that `Own.Plain.Sink.run : Fir.Program → Fir.Program` preserves exact
`Fir.eval` semantics at the same clock (`Sim Eq id`), refines `Fir.Program`
(`Sem.Refines`), and preserves program metadata (`size`, `exports`, `ctors`,
`known`).

Key structure:
1. `eval_env_congr` / `eval_insert_not_free`: `Fir.eval` depends only on
   variables free in the evaluated `Code` (and in captured `JEntry` bodies).
2. `eval_sinkBind_eq`: for a constructor RHS that evaluates to `.ok v`,
   sinking `.bind x (.ctor ci args)` into a `case` arm where `x` is uniquely
   free produces the exact same `Fir.eval` result as binding `x ↦ v` upfront.
3. `eval_sinkCode_refines` / `evalCall_sink_refines`: per-clock
   `Sem.Result.Refines Eq` between `P` and `Sink.run P` (source `.stuck` on a
   dead-arm constructor refines any target outcome).
4. `run_sim` and `run_refines`: lift to `Sem.Sim Eq id` and `Sem.Refines`. -/

set_option autoImplicit false

namespace IxCC.Own.Plain.Sink

open IxCC.Fir
open IxCC.Sem (Result ClockMono Lang Sim Forall2)

/-! ## Metadata preservation -/

theorem run_size (F : Program) : (run F).size = F.size := rfl
theorem run_exports (F : Program) : (run F).exports = F.exports := rfl
theorem run_ctors (F : Program) : (run F).ctors = F.ctors := rfl
theorem run_known (F : Program) : (run F).known = F.known := rfl
theorem run_ctorInfo? (F : Program) (c : Key.CtorKey) : (run F).ctorInfo? c = F.ctorInfo? c := rfl

private theorem natMap_get?_map {α β : Type} (f : α → β) :
    ∀ (m : Src.NatMap α) (k : Nat), (m.map f).get? k = (m.get? k).map f
  | .leaf, _ => rfl
  | .node v z o, k => by
    simp only [Src.NatMap.map, Src.NatMap.get?]
    split
    · rfl
    · split
      · exact natMap_get?_map f z (k / 2)
      · exact natMap_get?_map f o (k / 2)

theorem run_fun? (F : Program) (f : FunId) : (run F).fun? f = (F.fun? f).map sinkFun :=
  natMap_get?_map sinkFun F.funs f

theorem boolVal_run (F : Program) (b : Bool) : boolVal (run F) b = boolVal F b := rfl

theorem primResult_run (F : Program) (op : Lam.Prim) (vs : List Val) :
    primResult (run F) op vs = primResult F op vs := rfl

theorem evalRhs_run (F : Program) (ρ : Env) (r : Rhs) :
    evalRhs (run F) ρ r = evalRhs F ρ r := by
  cases r <;> rfl

/-! ## Environment congruence on free variables -/

/-- Two environments agree on every variable satisfying `P`. -/
def EnvAgreeOn (P : Var → Prop) (ρ₁ ρ₂ : Env) : Prop :=
  ∀ y, P y → ρ₁.get? y = ρ₂.get? y

theorem EnvAgreeOn.mono {P Q : Var → Prop} {ρ₁ ρ₂ : Env}
    (h : EnvAgreeOn P ρ₁ ρ₂) (hPQ : ∀ y, Q y → P y) : EnvAgreeOn Q ρ₁ ρ₂ :=
  fun y hy => h y (hPQ y hy)

theorem EnvAgreeOn.refl (P : Var → Prop) (ρ : Env) : EnvAgreeOn P ρ ρ :=
  fun _ _ => rfl

theorem EnvAgreeOn.insert {P : Var → Prop} {ρ₁ ρ₂ : Env} {x : Var} {v : Val}
    (h : EnvAgreeOn (fun y => y ≠ x ∧ P y) ρ₁ ρ₂) :
    EnvAgreeOn P (ρ₁.insert x v) (ρ₂.insert x v) := by
  intro y hy
  by_cases hxy : y = x
  · subst hxy
    rw [Src.NatMap.get?_insert_self, Src.NatMap.get?_insert_self]
  · rw [Src.NatMap.get?_insert_ne _ _ hxy, Src.NatMap.get?_insert_ne _ _ hxy]
    exact h y ⟨hxy, hy⟩

theorem bindAll_agree {P : Var → Prop} {ps : List Var} :
    ∀ {ρ₁ ρ₂ : Env} {vs : List Val},
      vs.length = ps.length →
      EnvAgreeOn (fun y => ps.contains y = false ∧ P y) ρ₁ ρ₂ →
      EnvAgreeOn P (bindAll ρ₁ ps vs) (bindAll ρ₂ ps vs) := by
  induction ps with
  | nil =>
    intro ρ₁ ρ₂ vs hlen h
    cases vs with
    | nil =>
      intro y hy
      exact h y ⟨rfl, hy⟩
    | cons _ _ => simp at hlen
  | cons p ps ih =>
    intro ρ₁ ρ₂ vs hlen h
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [bindAll]
      refine ih hlen (EnvAgreeOn.insert ?_)
      intro y ⟨hne, hnotmem, hy⟩
      refine h y ⟨?_, hy⟩
      simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      exact ⟨hne, hnotmem⟩

theorem arg_eval_congr {a : Arg} {ρ₁ ρ₂ : Env}
    (h : EnvAgreeOn (fun y => argHas y a = true) ρ₁ ρ₂) :
    a.eval ρ₁ = a.eval ρ₂ := by
  cases a with
  | var z => exact h z (by simp [argHas])
  | lit _ => rfl
  | erased => rfl

theorem evalArgs_congr {as : List Arg} {ρ₁ ρ₂ : Env}
    (h : EnvAgreeOn (fun y => argsHas y as = true) ρ₁ ρ₂) :
    evalArgs ρ₁ as = evalArgs ρ₂ as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [evalArgs]
    have ha : a.eval ρ₁ = a.eval ρ₂ :=
      arg_eval_congr (h.mono fun y hy => by simp [argsHas, hy])
    have has : evalArgs ρ₁ as = evalArgs ρ₂ as :=
      ih (h.mono fun y hy => by simp [argsHas, hy])
    rw [ha, has]

theorem evalRhs_congr {Q : Program} {r : Rhs} {ρ₁ ρ₂ : Env}
    (h : EnvAgreeOn (fun y => rhsHas y r = true) ρ₁ ρ₂) :
    evalRhs Q ρ₁ r = evalRhs Q ρ₂ r := by
  cases r with
  | arg a =>
    simp only [evalRhs]
    rw [arg_eval_congr (h.mono fun y hy => by simpa [rhsHas] using hy)]
  | ctor ci as =>
    simp only [evalRhs]
    rw [evalArgs_congr (h.mono fun y hy => by simpa [rhsHas] using hy)]
  | proj z ci i =>
    simp only [evalRhs]
    rw [h z (by simp [rhsHas])]
  | prim op as =>
    simp only [evalRhs]
    rw [evalArgs_congr (h.mono fun y hy => by simpa [rhsHas] using hy)]
  | call _ _ => rfl

/-- Two join-point entries agree when they have the same metadata/body and
their captured environments agree on variables free in the body outside `params`. -/
def JEntryAgree (e₁ e₂ : JEntry) : Prop :=
  e₁.id = e₂.id ∧
  e₁.charged = e₂.charged ∧
  e₁.params = e₂.params ∧
  e₁.body = e₂.body ∧
  e₁.isRec = e₂.isRec ∧
  EnvAgreeOn (fun y => e₁.params.contains y = false ∧ freeInCode y e₁.body = true) e₁.env e₂.env

theorem JEntryAgree.refl (e : JEntry) : JEntryAgree e e :=
  ⟨rfl, rfl, rfl, rfl, rfl, EnvAgreeOn.refl _ _⟩

theorem JEntryAgree.weight_eq {e₁ e₂ : JEntry} (h : JEntryAgree e₁ e₂) :
    e₁.weight = e₂.weight := by
  obtain ⟨_, hc, _, hb, _, _⟩ := h
  simp [JEntry.weight, hc, hb]

theorem jweight_agree {J₁ J₂ : List JEntry} (h : Forall2 JEntryAgree J₁ J₂) :
    jweight J₁ = jweight J₂ := by
  induction h with
  | nil => rfl
  | cons he _ ih => simp [jweight, he.weight_eq, ih]

theorem JEntryAgree.after {e₁ e₂ : JEntry} {rest₁ rest₂ : List JEntry}
    (he : JEntryAgree e₁ e₂) (hr : Forall2 JEntryAgree rest₁ rest₂) :
    Forall2 JEntryAgree (e₁.after rest₁) (e₂.after rest₂) := by
  obtain ⟨hid, _, hp, hb, hrec, henv⟩ := he
  unfold JEntry.after
  rw [← hrec]
  split
  · exact Forall2.cons ⟨hid, rfl, hp, hb, rfl, henv⟩ hr
  · exact hr

theorem lookupJ_agree (j : JoinId) :
    ∀ {J₁ J₂ : List JEntry}, Forall2 JEntryAgree J₁ J₂ →
      (lookupJ j J₁ = none ∧ lookupJ j J₂ = none) ∨
      ∃ e₁ rest₁ e₂ rest₂,
        lookupJ j J₁ = some (e₁, rest₁) ∧
        lookupJ j J₂ = some (e₂, rest₂) ∧
        JEntryAgree e₁ e₂ ∧
        Forall2 JEntryAgree rest₁ rest₂
  | [], [], .nil => .inl ⟨rfl, rfl⟩
  | e₁ :: J₁, e₂ :: J₂, .cons he hrest => by
    simp only [lookupJ, ← he.1]
    split
    · exact .inr ⟨e₁, J₁, e₂, J₂, rfl, rfl, he, hrest⟩
    · exact lookupJ_agree j hrest

mutual

theorem eval_env_congr (Q : Program) (k : Nat) {ρ₁ ρ₂ : Env} {J₁ J₂ : List JEntry} (c : Code) :
    EnvAgreeOn (fun y => freeInCode y c = true) ρ₁ ρ₂ →
    Forall2 JEntryAgree J₁ J₂ →
    eval Q k ρ₁ J₁ c = eval Q k ρ₂ J₂ c := by
  cases c with
  | bind x r c' =>
    intro hρ hJ
    cases r with
    | call f as =>
      rw [eval_bindCall, eval_bindCall]
      have has : evalArgs ρ₁ as = evalArgs ρ₂ as :=
        evalArgs_congr (hρ.mono fun y hy => by simp [freeInCode, rhsHas, hy])
      rw [has]
      cases evalArgs ρ₂ as with
      | none => rfl
      | some vs =>
        simp only [Result.ofOption, Result.bind_ok]
        cases evalCall Q k f vs with
        | ok v =>
          simp only [Result.bind_ok]
          refine eval_env_congr Q k c' (EnvAgreeOn.insert ?_) hJ
          intro y ⟨hne, hy⟩
          exact hρ y (by simp [freeInCode, hy, Ne.symm hne])
        | timeout | resource _ | trap | stuck => rfl
    | arg a =>
      rw [eval_bind_arg, eval_bind_arg]
      have hr : evalRhs Q ρ₁ (.arg a) = evalRhs Q ρ₂ (.arg a) :=
        evalRhs_congr (hρ.mono fun y hy => by simp [freeInCode, hy])
      rw [hr]
      cases evalRhs Q ρ₂ (.arg a) with
      | ok v =>
        simp only [Result.bind_ok]
        refine eval_env_congr Q k c' (EnvAgreeOn.insert ?_) hJ
        intro y ⟨hne, hy⟩
        exact hρ y (by simp [freeInCode, hy, Ne.symm hne])
      | timeout | resource _ | trap | stuck => rfl
    | ctor ci as =>
      rw [eval_bind_ctor, eval_bind_ctor]
      have hr : evalRhs Q ρ₁ (.ctor ci as) = evalRhs Q ρ₂ (.ctor ci as) :=
        evalRhs_congr (hρ.mono fun y hy => by simp [freeInCode, hy])
      rw [hr]
      cases evalRhs Q ρ₂ (.ctor ci as) with
      | ok v =>
        simp only [Result.bind_ok]
        refine eval_env_congr Q k c' (EnvAgreeOn.insert ?_) hJ
        intro y ⟨hne, hy⟩
        exact hρ y (by simp [freeInCode, hy, Ne.symm hne])
      | timeout | resource _ | trap | stuck => rfl
    | proj z ci i =>
      rw [eval_bind_proj, eval_bind_proj]
      have hr : evalRhs Q ρ₁ (.proj z ci i) = evalRhs Q ρ₂ (.proj z ci i) :=
        evalRhs_congr (hρ.mono fun y hy => by simp [freeInCode, hy])
      rw [hr]
      cases evalRhs Q ρ₂ (.proj z ci i) with
      | ok v =>
        simp only [Result.bind_ok]
        refine eval_env_congr Q k c' (EnvAgreeOn.insert ?_) hJ
        intro y ⟨hne, hy⟩
        exact hρ y (by simp [freeInCode, hy, Ne.symm hne])
      | timeout | resource _ | trap | stuck => rfl
    | prim op as =>
      rw [eval_bind_prim, eval_bind_prim]
      have hr : evalRhs Q ρ₁ (.prim op as) = evalRhs Q ρ₂ (.prim op as) :=
        evalRhs_congr (hρ.mono fun y hy => by simp [freeInCode, hy])
      rw [hr]
      cases evalRhs Q ρ₂ (.prim op as) with
      | ok v =>
        simp only [Result.bind_ok]
        refine eval_env_congr Q k c' (EnvAgreeOn.insert ?_) hJ
        intro y ⟨hne, hy⟩
        exact hρ y (by simp [freeInCode, hy, Ne.symm hne])
      | timeout | resource _ | trap | stuck => rfl
  | jp j ps rec b c' =>
    intro hρ hJ
    rw [eval_jp, eval_jp]
    have he : JEntryAgree
        { id := j, charged := false, env := ρ₁, params := ps, body := b, isRec := rec }
        { id := j, charged := false, env := ρ₂, params := ps, body := b, isRec := rec } :=
      ⟨rfl, rfl, rfl, rfl, rfl, hρ.mono fun y ⟨hnm, hb⟩ => by
        simp only [freeInCode, hnm, hb, Bool.not_false, Bool.and_self, Bool.true_or]⟩
    exact eval_env_congr Q k c'
      (hρ.mono fun y hy => by simp [freeInCode, hy])
      (Forall2.cons he hJ)
  | jmp j as =>
    intro hρ hJ
    rw [eval_jmp, eval_jmp]
    have has : evalArgs ρ₁ as = evalArgs ρ₂ as :=
      evalArgs_congr (hρ.mono fun y hy => by simpa [freeInCode] using hy)
    rcases lookupJ_agree j hJ with ⟨h1, h2⟩ | ⟨e₁, rest₁, e₂, rest₂, h1, h2, he, hrest⟩
    · rw [h1, h2]; rfl
    · rw [h1, h2, has]
      cases evalArgs ρ₂ as with
      | none => rfl
      | some vs =>
        simp only [Result.ofOption, Result.bind_ok, jumpTo]
        have hafter := he.after hrest
        obtain ⟨_, hchg, hps, hbody, _, henv⟩ := he
        rw [← hps, ← hchg]
        by_cases hlen : vs.length = e₁.params.length
        · simp only [hlen, ↓reduceIte]
          have hbind : EnvAgreeOn (fun y => freeInCode y e₁.body = true)
              (bindAll e₁.env e₁.params vs) (bindAll e₂.env e₁.params vs) :=
            bindAll_agree hlen henv
          cases hc : e₁.charged with
          | true =>
            simp only [↓reduceIte]
            cases k with
            | zero => rfl
            | succ k =>
              simp only [Sem.later_succ, ← hbody]
              exact eval_env_congr Q k e₁.body hbind hafter
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, ← hbody]
            exact eval_env_congr Q k e₁.body hbind hafter
        · simp [hlen]
  | case x alts d =>
    intro hρ hJ
    rw [eval_case, eval_case]
    have hx : ρ₁.get? x = ρ₂.get? x := hρ x (by simp [freeInCode])
    rw [hx]
    cases ρ₂.get? x with
    | none => rfl
    | some v =>
      simp only [Result.ofOption, Result.bind_ok]
      cases v.asCtor Q.known with
      | none => rfl
      | some p =>
        exact evalAlts_env_congr Q k p.1 alts d
          (hρ.mono fun y hy => by
            rcases Bool.or_eq_true_iff.mp hy with ha | hd
            · simp [freeInCode, ha]
            · simp [freeInCode, hd]) hJ
  | ret a =>
    intro hρ _
    rw [eval_ret, eval_ret]
    rw [arg_eval_congr (hρ.mono fun y hy => by simpa [freeInCode] using hy)]
  | tcall f as =>
    intro hρ _
    rw [eval_tcall, eval_tcall]
    rw [evalArgs_congr (hρ.mono fun y hy => by simpa [freeInCode] using hy)]
  | trap =>
    intro _ _
    rw [eval_trap, eval_trap]
termination_by (k, c.size + jweight J₁)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right
       have hw := lookupJ_weight j h1
       rw [JEntry.jweight_after]
       simp only [JEntry.weight, hc, Bool.false_eq_true, ↓reduceIte] at hw
       simp only [Code.size] at *
       omega)
    | (apply Prod.Lex.right
       simp only [Code.size, jweight, JEntry.weight, Bool.false_eq_true, ↓reduceIte]
       omega)
    | (apply Prod.Lex.right
       simp only [Code.size]
       omega)

theorem evalAlts_env_congr (Q : Program) (k : Nat) {ρ₁ ρ₂ : Env} {J₁ J₂ : List JEntry}
    (key : Key.CtorKey) (alts : List Alt) (d : Option Code) :
    EnvAgreeOn (fun y => (freeInAlts y alts || freeInOpt y d) = true) ρ₁ ρ₂ →
    Forall2 JEntryAgree J₁ J₂ →
    evalAlts Q k ρ₁ J₁ key alts d = evalAlts Q k ρ₂ J₂ key alts d := by
  cases alts with
  | nil =>
    cases d with
    | none => intro _ _; rw [evalAlts_nil, evalAlts_nil]
    | some c =>
      intro hρ hJ
      rw [evalAlts_nil, evalAlts_nil]
      exact eval_env_congr Q k c (hρ.mono fun y hy => by simp [freeInAlts, freeInOpt, hy]) hJ
  | cons a rest =>
    cases a with
    | mk key' body =>
      intro hρ hJ
      rw [evalAlts_cons, evalAlts_cons]
      split
      · exact eval_env_congr Q k body
          (hρ.mono fun y hy => by simp [freeInAlts, hy]) hJ
      · exact evalAlts_env_congr Q k key rest d
          (hρ.mono fun y hy => by
            simp only [freeInAlts, Bool.or_eq_true] at hy ⊢
            rcases hy with hy | hy
            · exact .inl (.inr hy)
            · exact .inr hy) hJ
termination_by (k, Code.altsSize alts + Code.optSize d + jweight J₁ + 1)
decreasing_by
  all_goals simp_wf
  all_goals apply Prod.Lex.right
  all_goals simp only [Code.altsSize, Code.optSize]
  all_goals first
    | omega
    | (have := Code.size_pos body; omega)

end

theorem forall2_JEntryAgree_refl : ∀ J : List JEntry, Forall2 JEntryAgree J J
  | [] => .nil
  | e :: J => .cons (JEntryAgree.refl e) (forall2_JEntryAgree_refl J)

theorem eval_insert_not_free {Q : Program} {k : Nat} {ρ : Env} {J : List JEntry}
    {x : Var} {v : Val} {c : Code} (hfree : freeInCode x c = false) :
    eval Q k (ρ.insert x v) J c = eval Q k ρ J c := by
  refine eval_env_congr Q k c ?_ (forall2_JEntryAgree_refl J)
  intro y hy
  have hne : y ≠ x := by
    intro h
    subst h
    rw [hfree] at hy
    cases hy
  exact Src.NatMap.get?_insert_ne ρ v hne

/-! ## Sinking a single constructor binding -/

mutual

theorem eval_sinkBind_eq (Q : Program) (k : Nat) (ρ : Env) (J : List JEntry)
    (x : Var) (ci : CtorInfo) (args : List Arg) {v : Val}
    (hv : evalRhs Q ρ (.ctor ci args) = .ok v) (s : Code) :
    eval Q k ρ J (sinkBind x ci args s) = eval Q k (ρ.insert x v) J s := by
  cases s with
  | case u alts d =>
    unfold sinkBind
    split
    · next hcond =>
      simp only [Bool.and_eq_true, bne_iff_ne] at hcond
      have hne : u ≠ x := hcond.1.1
      rw [eval_case, eval_case, Src.NatMap.get?_insert_ne ρ v hne]
      cases ρ.get? u with
      | none => rfl
      | some vu =>
        simp only [Result.ofOption, Result.bind_ok]
        cases vu.asCtor Q.known with
        | none => rfl
        | some p =>
          exact evalAlts_sinkBind_eq Q k ρ J x ci args hv p.1 alts d
    · rw [eval_bind_ctor, hv]; rfl
  | bind _ _ _ | jp _ _ _ _ _ | jmp _ _ | ret _ | tcall _ _ | trap =>
    unfold sinkBind
    rw [eval_bind_ctor, hv]; rfl
termination_by s.size
decreasing_by
  all_goals simp_wf
  all_goals try simp only [Code.size]
  all_goals omega

theorem evalAlts_sinkBind_eq (Q : Program) (k : Nat) (ρ : Env) (J : List JEntry)
    (x : Var) (ci : CtorInfo) (args : List Arg) {v : Val}
    (hv : evalRhs Q ρ (.ctor ci args) = .ok v)
    (key : Key.CtorKey) (alts : List Alt) (d : Option Code) :
    evalAlts Q k ρ J key (sinkBindAlts x ci args alts) (sinkBindOpt x ci args d) =
      evalAlts Q k (ρ.insert x v) J key alts d := by
  cases alts with
  | nil =>
    simp only [sinkBindAlts]
    rw [evalAlts_nil, evalAlts_nil]
    cases d with
    | none => rfl
    | some b =>
      simp only [sinkBindOpt]
      cases hf : freeInCode x b with
      | true =>
        simp only [↓reduceIte]
        exact eval_sinkBind_eq Q k ρ J x ci args hv b
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact (eval_insert_not_free hf).symm
  | cons a rest =>
    cases a with
    | mk key' body =>
      simp only [sinkBindAlts]
      rw [evalAlts_cons, evalAlts_cons]
      split
      · cases hf : freeInCode x body with
        | true =>
          simp only [↓reduceIte]
          exact eval_sinkBind_eq Q k ρ J x ci args hv body
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact (eval_insert_not_free hf).symm
      · exact evalAlts_sinkBind_eq Q k ρ J x ci args hv key rest d
termination_by Code.altsSize alts + Code.optSize d + 1
decreasing_by
  all_goals simp_wf
  all_goals try simp only [Code.altsSize, Code.optSize]
  all_goals first
    | omega
    | (have := Code.size_pos body; omega)

end

/-! ## Full `sinkCode` / `run` refinement -/

/-- Corresponding join-point entries before and after `sinkCode`. -/
def JEntrySink (e₁ e₂ : JEntry) : Prop :=
  e₁.id = e₂.id ∧
  e₁.charged = e₂.charged ∧
  e₁.env = e₂.env ∧
  e₁.params = e₂.params ∧
  e₂.body = sinkCode e₁.body ∧
  e₁.isRec = e₂.isRec

theorem JEntrySink.after {e₁ e₂ : JEntry} {rest₁ rest₂ : List JEntry}
    (he : JEntrySink e₁ e₂) (hr : Forall2 JEntrySink rest₁ rest₂) :
    Forall2 JEntrySink (e₁.after rest₁) (e₂.after rest₂) := by
  obtain ⟨hid, _, henv, hp, hb, hrec⟩ := he
  unfold JEntry.after
  rw [← hrec]
  split
  · exact Forall2.cons ⟨hid, rfl, henv, hp, hb, rfl⟩ hr
  · exact hr

theorem lookupJ_sink (j : JoinId) :
    ∀ {J₁ J₂ : List JEntry}, Forall2 JEntrySink J₁ J₂ →
      (lookupJ j J₁ = none ∧ lookupJ j J₂ = none) ∨
      ∃ e₁ rest₁ e₂ rest₂,
        lookupJ j J₁ = some (e₁, rest₁) ∧
        lookupJ j J₂ = some (e₂, rest₂) ∧
        JEntrySink e₁ e₂ ∧
        Forall2 JEntrySink rest₁ rest₂
  | [], [], .nil => .inl ⟨rfl, rfl⟩
  | e₁ :: J₁, e₂ :: J₂, .cons he hrest => by
    simp only [lookupJ, ← he.1]
    split
    · exact .inr ⟨e₁, J₁, e₂, J₂, rfl, rfl, he, hrest⟩
    · exact lookupJ_sink j hrest

private theorem evalRhs_ctor_cases (P : Program) (ρ : Env) (ci : CtorInfo) (as : List Arg) :
    (∃ v, evalRhs P ρ (.ctor ci as) = .ok v) ∨ evalRhs P ρ (.ctor ci as) = .stuck := by
  simp only [evalRhs]
  cases evalArgs ρ as with
  | none => exact .inr rfl
  | some vs =>
    by_cases h : vs.length = ci.arity
    · exact .inl ⟨.ctor ci vs, by simp [h]⟩
    · exact .inr (by simp [h])

mutual

theorem eval_sinkCode_refines (P : Program) (k : Nat) (ρ : Env) {J₁ J₂ : List JEntry} (c : Code)
    (hJ : Forall2 JEntrySink J₁ J₂) :
    Result.Refines Eq (eval P k ρ J₁ c) (eval (run P) k ρ J₂ (sinkCode c)) := by
  cases c with
  | bind x r c' =>
    cases r with
    | call f as =>
      simp only [sinkCode]
      rw [eval_bindCall, eval_bindCall]
      cases evalArgs ρ as with
      | none => exact .stuck
      | some vs =>
        simp only [Result.ofOption, Result.bind_ok]
        have hcall := evalCall_sink_refines P k f vs
        generalize evalCall P k f vs = r1 at hcall
        generalize evalCall (run P) k f vs = r2 at hcall
        cases hcall with
        | ok heq =>
          subst heq
          simp only [Result.bind_ok]
          exact eval_sinkCode_refines P k (ρ.insert x _) c' hJ
        | timeout => exact .timeout
        | trap => exact .trap
        | stuck => exact .stuck
        | resource failure => exact .resource failure
    | ctor ci as =>
      simp only [sinkCode]
      rw [eval_bind_ctor]
      rcases evalRhs_ctor_cases P ρ ci as with ⟨v, hr⟩ | hr
      · rw [hr]
        simp only [Result.bind_ok]
        have hr' : evalRhs (run P) ρ (.ctor ci as) = .ok v := by
          rw [evalRhs_run]; exact hr
        rw [eval_sinkBind_eq (run P) k ρ J₂ x ci as hr' (sinkCode c')]
        exact eval_sinkCode_refines P k (ρ.insert x v) c' hJ
      · rw [hr]; exact .stuck
    | arg a =>
      simp only [sinkCode]
      rw [eval_bind_arg, eval_bind_arg, evalRhs_run]
      cases evalRhs P ρ (.arg a) with
      | ok v =>
        simp only [Result.bind_ok]
        exact eval_sinkCode_refines P k (ρ.insert x v) c' hJ
      | timeout => exact .timeout
      | resource failure => exact .resource failure
      | trap => exact .trap
      | stuck => exact .stuck
    | proj z ci i =>
      simp only [sinkCode]
      rw [eval_bind_proj, eval_bind_proj, evalRhs_run]
      cases evalRhs P ρ (.proj z ci i) with
      | ok v =>
        simp only [Result.bind_ok]
        exact eval_sinkCode_refines P k (ρ.insert x v) c' hJ
      | timeout => exact .timeout
      | resource failure => exact .resource failure
      | trap => exact .trap
      | stuck => exact .stuck
    | prim op as =>
      simp only [sinkCode]
      rw [eval_bind_prim, eval_bind_prim, evalRhs_run]
      cases evalRhs P ρ (.prim op as) with
      | ok v =>
        simp only [Result.bind_ok]
        exact eval_sinkCode_refines P k (ρ.insert x v) c' hJ
      | timeout => exact .timeout
      | resource failure => exact .resource failure
      | trap => exact .trap
      | stuck => exact .stuck
  | jp j ps rec b c' =>
    simp only [sinkCode]
    rw [eval_jp, eval_jp]
    have he : JEntrySink
        { id := j, charged := false, env := ρ, params := ps, body := b, isRec := rec }
        { id := j, charged := false, env := ρ, params := ps, body := sinkCode b, isRec := rec } :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact eval_sinkCode_refines P k ρ c' (Forall2.cons he hJ)
  | jmp j as =>
    simp only [sinkCode]
    rw [eval_jmp, eval_jmp]
    rcases lookupJ_sink j hJ with ⟨h1, h2⟩ | ⟨e₁, rest₁, e₂, rest₂, h1, h2, he, hrest⟩
    · rw [h1, h2]; exact .stuck
    · rw [h1, h2]
      cases evalArgs ρ as with
      | none => exact .stuck
      | some vs =>
        simp only [Result.ofOption, Result.bind_ok, jumpTo]
        have hafter := he.after hrest
        obtain ⟨_, hchg, henv, hps, hbody, _⟩ := he
        rw [← hps, ← hchg, ← henv, hbody]
        by_cases hlen : vs.length = e₁.params.length
        · simp only [hlen, ↓reduceIte]
          cases hc : e₁.charged with
          | true =>
            simp only [↓reduceIte]
            cases k with
            | zero => exact .timeout
            | succ k =>
              simp only [Sem.later_succ]
              exact eval_sinkCode_refines P k (bindAll e₁.env e₁.params vs) e₁.body hafter
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact eval_sinkCode_refines P k (bindAll e₁.env e₁.params vs) e₁.body hafter
        · simp only [hlen, ↓reduceIte]; exact .stuck
  | case x alts d =>
    simp only [sinkCode]
    rw [eval_case, eval_case, run_known]
    cases ρ.get? x with
    | none => exact .stuck
    | some v =>
      simp only [Result.ofOption, Result.bind_ok]
      cases v.asCtor P.known with
      | none => exact .stuck
      | some p => exact evalAlts_sinkCode_refines P k ρ p.1 alts d hJ
  | ret a =>
    simp only [sinkCode]
    rw [eval_ret, eval_ret]
    exact Result.Refines.refl (fun _ => rfl)
  | tcall f as =>
    simp only [sinkCode]
    rw [eval_tcall, eval_tcall]
    cases evalArgs ρ as with
    | none => exact .stuck
    | some vs => exact evalCall_sink_refines P k f vs
  | trap =>
    simp only [sinkCode]
    rw [eval_trap, eval_trap]
    exact .trap
termination_by (k, c.size + jweight J₁)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right
       have hw := lookupJ_weight j h1
       rw [JEntry.jweight_after]
       simp only [JEntry.weight, hc, Bool.false_eq_true, ↓reduceIte] at hw
       simp only [Code.size] at *
       omega)
    | (apply Prod.Lex.right
       simp only [Code.size, jweight, JEntry.weight, Bool.false_eq_true, ↓reduceIte]
       omega)
    | (apply Prod.Lex.right
       try simp only [Code.size]
       omega)

theorem evalAlts_sinkCode_refines (P : Program) (k : Nat) (ρ : Env) {J₁ J₂ : List JEntry}
    (key : Key.CtorKey) (alts : List Alt) (d : Option Code)
    (hJ : Forall2 JEntrySink J₁ J₂) :
    Result.Refines Eq (evalAlts P k ρ J₁ key alts d)
      (evalAlts (run P) k ρ J₂ key (sinkAlts alts) (sinkOpt d)) := by
  cases alts with
  | nil =>
    simp only [sinkAlts]
    rw [evalAlts_nil, evalAlts_nil]
    cases d with
    | none => exact .stuck
    | some c =>
      simp only [sinkOpt]
      exact eval_sinkCode_refines P k ρ c hJ
  | cons a rest =>
    cases a with
    | mk key' body =>
      simp only [sinkAlts]
      rw [evalAlts_cons, evalAlts_cons]
      split
      · exact eval_sinkCode_refines P k ρ body hJ
      · exact evalAlts_sinkCode_refines P k ρ key rest d hJ
termination_by (k, Code.altsSize alts + Code.optSize d + jweight J₁ + 1)
decreasing_by
  all_goals simp_wf
  all_goals apply Prod.Lex.right
  all_goals try simp only [Code.altsSize, Code.optSize]
  all_goals first
    | omega
    | (have := Code.size_pos body; omega)

theorem evalCall_sink_refines (P : Program) (k : Nat) (f : FunId) (vs : List Val) :
    Result.Refines Eq (evalCall P k f vs) (evalCall (run P) k f vs) := by
  rw [evalCall_eq, evalCall_eq, run_fun?]
  cases P.fun? f with
  | none => exact .stuck
  | some fd =>
    simp only [Option.map_some, Result.ofOption, Result.bind_ok, callFun, sinkFun]
    by_cases hlen : vs.length = fd.params.length
    · simp only [hlen, ↓reduceIte]
      cases k with
      | zero => exact .timeout
      | succ k =>
        simp only [Sem.later_succ]
        exact eval_sinkCode_refines P k (bindAll .leaf (fd.params.map (·.1)) vs) fd.body .nil
    · simp only [hlen, ↓reduceIte]; exact .stuck
termination_by (k, 0)
decreasing_by
  all_goals simp_wf
  all_goals apply Prod.Lex.left; omega

end

/-! ## Clocked simulation and language refinement -/

theorem run_call_sim (P : Program) (f : FunId) (vs : List Val) :
    Sim Eq id (fun k => Fir.run P k f vs) (fun k => Fir.run (run P) k f vs) where
  forward k _ := ⟨k, evalCall_sink_refines P k f vs⟩
  timeout k h := by
    have hr := evalCall_sink_refines P k f vs
    change evalCall P k f vs = .timeout at h
    rw [h] at hr
    exact Result.Refines.timeout_iff.mp hr

theorem run_sim (P : Program) (i : Nat × List Nat) :
    Sim Eq id (firRun P i) (firRun (run P) i) := by
  obtain ⟨r, ns⟩ := i
  show Sim Eq id (firRun P (r, ns)) (firRun (run P) (r, ns))
  unfold firRun
  rw [run_exports]
  cases P.exports[r]? with
  | none => exact { forward := fun _ _ => ⟨0, .stuck⟩, timeout := fun _ h => nomatch h }
  | some f =>
    simp only [run_fun?]
    cases P.fun? f with
    | none => exact { forward := fun _ _ => ⟨0, .stuck⟩, timeout := fun _ h => nomatch h }
    | some fd =>
      simp only [Option.map_some, sinkFun]
      by_cases he : ns.length = fd.params.length
      · simp only [Sem.entryRun, he, ↓reduceIte]
        exact run_call_sim P f (litArgs ns)
      · by_cases hlt : ns.length < fd.params.length
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          by_cases hn : ns = []
          · simp only [hn, ↓reduceIte]
            exact Sim.okConst rfl
          · simp only [hn, ↓reduceIte]
            exact Sim.laterConst rfl (fun k h => h)
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          exact Sim.bindStuck (run_call_sim P f (litArgs (ns.take fd.params.length)))
            fun _ _ _ => rfl

theorem run_retained (P : Program) (i : Nat × List Nat) :
    Sem.Behaviour.Refines Eq (Lang.behaviour P i) (Lang.behaviour (run P) i) :=
  (run_sim P i).refines (Lang.mono P i) (Lang.mono (run P) i)

theorem run_refines (P : Program) : Sem.Refines P (run P) :=
  Sem.Refines.of_sim (R := Lang.ObsEq) (fun _ _ h => h) fun i =>
    ⟨id, (run_sim P i).mono fun _ _ h => by rw [h]; rfl⟩

end IxCC.Own.Plain.Sink
