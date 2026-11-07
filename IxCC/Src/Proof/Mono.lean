import IxCC.Src.Proof.Unfold
import IxCC.Sem.Agrees

/-! # SrcEval: clock monotonicity

`Src.eval_mono` (design note 01 §6.1, M2.2): an outcome of SrcEval other
than `timeout` is the outcome at every larger clock, for `eval`, `apply`,
`applyAll`, `fire`, `force`, `forceAll`, `evalConst`, `headValue` and `run`;
so each is a `Sem.ClockMono` computation (as v2's `MonoAt`,
`jcb/ixby-archive:IxCC/Ixon/Eval.lean:898`).

Strong induction on the clock. Within one clock, the functions call each
other without a charge only in the order `eval → {apply, force, evalConst}
→ {fire, headValue} → {force, forceAll}`, and `eval` on subterms, so one
clock level is proved bottom-up: slots, then heads, then application, then
terms by structural recursion. Every other call is one clock down. -/

namespace IxCC.Src

open IxCC.Sem (Result ClockMono later)
open IxCC.Sem.Result (Agrees)

variable (p : Program)

/-- Every function of SrcEval agrees from clock `k` upward. -/
structure MonoAt (k : Nat) : Prop where
  eval : ∀ k', k ≤ k' → ∀ ls ρ t, Agrees (eval p k' ls ρ t) (eval p k ls ρ t)
  apply : ∀ k', k ≤ k' → ∀ f s, Agrees (apply p k' f s) (apply p k f s)
  applyAll : ∀ k', k ≤ k' → ∀ f ss, Agrees (applyAll p k' f ss) (applyAll p k f ss)
  fire : ∀ k', k ≤ k' → ∀ h ls args, Agrees (fire p k' h ls args) (fire p k h ls args)
  force : ∀ k', k ≤ k' → ∀ s, Agrees (force p k' s) (force p k s)
  forceAll : ∀ k', k ≤ k' → ∀ ss, Agrees (forceAll p k' ss) (forceAll p k ss)
  evalConst : ∀ k', k ≤ k' → ∀ ls c, Agrees (evalConst p k' ls c) (evalConst p k ls c)

section

variable {p} {k : Nat} (ih : ∀ j < k, MonoAt p j)
include ih

/-- A charge: agreement one clock down gives agreement here. -/
theorem later_agrees_of {α : Type} {k' : Nat} (hk : k ≤ k') {f f' : Nat → Result α}
    (h : ∀ j < k, ∀ j', j ≤ j' → Agrees (f' j') (f j)) : Agrees (later k' f') (later k f) := by
  cases k with
  | zero => exact .of_timeout
  | succ j =>
    obtain ⟨j', rfl⟩ : ∃ j', k' = j' + 1 := ⟨k' - 1, by omega⟩
    exact h j (by omega) j' (by omega)

theorem force_agrees_of {k' : Nat} (hk : k ≤ k') (s : Slot) :
    Agrees (force p k' s) (force p k s) := by
  cases s with
  | val v => rw [force_val, force_val]; exact .refl _
  | name t ρ' ls' =>
    rw [force_name, force_name]
    exact later_agrees_of ih hk fun j hj j' hj' => (ih j hj).eval j' hj' ls' ρ' t

theorem forceAll_agrees_of {k' : Nat} (hk : k ≤ k') :
    ∀ ss, Agrees (forceAll p k' ss) (forceAll p k ss)
  | [] => by rw [forceAll_nil, forceAll_nil]; exact .refl _
  | s :: ss => by
    rw [forceAll_cons, forceAll_cons]
    exact .bind (force_agrees_of ih hk s) fun _ _ =>
      .bind (forceAll_agrees_of hk ss) fun _ _ => .refl _

end

theorem recChosen_agrees {k k' : Nat} (hf : ∀ s, Agrees (force p k' s) (force p k s))
    (ls : Levels) (kind : RecKind) (ind np : CId) (majorIdx : Nat) (indices args : List Slot) :
    Agrees (recChosen p k' ls kind ind np majorIdx indices args)
      (recChosen p k ls kind ind np majorIdx indices args) := by
  cases kind with
  | empty => exact .refl _
  | ordinary => exact .bind (hf _) fun _ _ => .refl _
  | subsingleton _ _ => exact .refl _

section

variable {p} {k : Nat} (ih : ∀ j < k, MonoAt p j)
include ih

theorem fire_agrees_of {k' : Nat} (hk : k ≤ k') (h : Head) (ls : Levels) (args : List Slot) :
    Agrees (fire p k' h ls args) (fire p k h ls args) := by
  cases h with
  | ctor c =>
    rw [fire_ctor, fire_ctor]
    cases p.decl? c with
    | none => exact .refl _
    | some d =>
      cases d with
      | ctor _ _ _ _ np _ _ =>
        exact .bind (forceAll_agrees_of ih hk _) fun _ _ => .refl _
      | _ => exact .refl _
  | quotMk c =>
    rw [fire_quotMk, fire_quotMk]
    match args with
    | [_, _, a] => exact .bind (force_agrees_of ih hk a) fun _ _ => .refl _
    | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => exact .refl _
  | quotLift c =>
    rw [fire_quotLift, fire_quotLift]
    refine later_agrees_of ih hk fun j hj j' hj' => ?_
    match args with
    | [_, _, _, f, _, q] =>
      refine .bind ((ih j hj).force j' hj' q) fun qv _ => ?_
      match qv with
      | .con c' _ _ [a] =>
        dsimp only
        split
        · exact .bind ((ih j hj).force j' hj' f) fun fv _ => (ih j hj).apply j' hj' fv _
        · exact .refl _
      | .con _ _ _ [] | .con _ _ _ (_ :: _ :: _) | .lit _ | .str _ | .clo .. | .pap .. | .irr .. =>
        exact .refl _
    | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _]
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => exact .refl _
  | recr r =>
    rw [fire_recr, fire_recr]
    refine later_agrees_of ih hk fun j hj j' hj' => ?_
    cases p.decl? r with
    | none => exact .refl _
    | some d =>
      cases d with
      | recr _ _ _ np nmot nmin ni ind rules _ =>
        cases (p.table.recKindOf r).map (·.atLevels ls) with
        | none => exact .refl _
        | some kind =>
          refine .bind (recChosen_agrees p ((ih j hj).force j' hj') ls kind ind np _ _ args)
            fun jf _ => ?_
          dsimp only
          cases rules[jf.1]? with
          | none => exact .refl _
          | some rule =>
            dsimp only
            cases peelLams (args.take (np + nmot + nmin) ++ jf.2).length rule.rhs with
            | none => exact .refl _
            | some body => exact (ih j hj).eval j' hj' ls _ body
      | _ => cases (p.table.recKindOf r).map (·.atLevels ls) <;> exact .refl _
  | cases c =>
    rw [fire_cases, fire_cases]
    refine later_agrees_of ih hk fun j hj j' hj' => ?_
    cases p.table.resolveOf c with
    | none => exact .refl _
    | some res =>
      cases res with
      | case r =>
        dsimp only
        cases p.decl? r with
        | none => exact .refl _
        | some d =>
          cases d with
          | recr _ _ _ np _ _ ni ind _ _ =>
            cases (p.table.recKindOf r).map (·.atLevels ls) with
            | none => exact .refl _
            | some kind =>
              exact .bind (recChosen_agrees p ((ih j hj).force j' hj') ls kind ind np _ _ args)
                fun jf _ => .bind ((ih j hj).force j' hj' _) fun minor _ =>
                  (ih j hj).applyAll j' hj' minor jf.2
          | _ => cases (p.table.recKindOf r).map (·.atLevels ls) <;> exact .refl _
      | _ => exact .refl _
  | prim op =>
    rw [fire_prim, fire_prim]
    exact .bind (forceAll_agrees_of ih hk args) fun _ _ => .refl _

theorem apply_agrees_of {k' : Nat} (hk : k ≤ k') (f : Value) (s : Slot) :
    Agrees (apply p k' f s) (apply p k f s) := by
  cases f with
  | clo b d body ρ' ls' =>
    rw [apply_clo, apply_clo]
    split
    · exact later_agrees_of ih hk fun j hj j' hj' => (ih j hj).eval j' hj' ls' _ body
    · exact .refl _
  | pap h ls' args =>
    rw [apply_pap, apply_pap]
    split
    · exact fire_agrees_of ih hk h ls' _
    · exact .refl _
  | _ =>
    rw [apply_other p k' _ s (by intros; nofun) (by intros; nofun),
      apply_other p k _ s (by intros; nofun) (by intros; nofun)]
    exact .refl _

theorem applyAll_agrees_of {k' : Nat} (hk : k ≤ k') :
    ∀ (f : Value) (ss : List Slot), Agrees (applyAll p k' f ss) (applyAll p k f ss)
  | f, [] => by rw [applyAll_nil, applyAll_nil]; exact .refl _
  | f, s :: ss => by
    rw [applyAll_cons, applyAll_cons]
    exact .bind (apply_agrees_of ih hk f s) fun v _ => applyAll_agrees_of hk v ss

theorem headValue_agrees_of {k' : Nat} (hk : k ≤ k') (ls : Levels) (h : Head) :
    Agrees (headValue p k' ls h) (headValue p k ls h) := by
  rw [headValue_eq, headValue_eq]
  split
  · exact fire_agrees_of ih hk h ls []
  · exact .refl _

theorem evalConst_agrees_of {k' : Nat} (hk : k ≤ k') (ls : Levels) (c : CId) :
    Agrees (evalConst p k' ls c) (evalConst p k ls c) := by
  have hl : ∀ (t : Term), Agrees (later k' fun j => eval p j ls [] t)
      (later k fun j => eval p j ls [] t) := fun t =>
    later_agrees_of ih hk fun j hj j' hj' => (ih j hj).eval j' hj' ls [] t
  rw [evalConst_eq, evalConst_eq]
  cases p.table.resolveOf c with
  | some res =>
    cases res with
    | prim op => exact headValue_agrees_of ih hk ls _
    | csimp g vs _ => exact hl _
    | eqn _ body => exact hl _
    | case _ => exact headValue_agrees_of ih hk ls _
  | none =>
    dsimp only
    cases p.decl? c with
    | none => exact .refl _
    | some d =>
      cases d with
      | ctor => exact headValue_agrees_of ih hk ls _
      | recr => exact headValue_agrees_of ih hk ls _
      | quot kind _ _ =>
        cases kind with
        | ctor => exact headValue_agrees_of ih hk ls _
        | lift => exact headValue_agrees_of ih hk ls _
        | _ => exact .refl _
      | defn kind safety _ _ v =>
        cases kind <;> cases safety <;> try exact .refl _
        · exact hl _
        · dsimp only
          split
          · exact hl _
          · exact .refl _
      | _ => exact .refl _

theorem eval_agrees_of {k' : Nat} (hk : k ≤ k') (ls : Levels) :
    ∀ (ρ : Env) (t : Term), Agrees (eval p k' ls ρ t) (eval p k ls ρ t)
  | ρ, .var i => by
    rw [eval_var, eval_var]
    cases ρ[i]? with
    | some s => exact force_agrees_of ih hk s
    | none => exact .refl _
  | ρ, .sort _ => by rw [eval_sort, eval_sort]; exact .refl _
  | ρ, .pi .. => by rw [eval_pi, eval_pi]; exact .refl _
  | ρ, .natLit _ => by rw [eval_natLit, eval_natLit]; exact .refl _
  | ρ, .strLit _ => by rw [eval_strLit, eval_strLit]; exact .refl _
  | ρ, .lam .. => by rw [eval_lam, eval_lam]; exact .refl _
  | ρ, .letE c r ty v body => by
    rw [eval_letE, eval_letE]
    split
    · exact eval_agrees_of hk ls _ body
    · exact .bind (eval_agrees_of hk ls ρ v) fun x _ => eval_agrees_of hk ls _ body
  | ρ, .proj s i e => by
    rw [eval_proj, eval_proj]
    exact .bind (eval_agrees_of hk ls ρ e) fun _ _ => .refl _
  | ρ, .app f a m r => by
    rw [eval_app, eval_app]
    refine .bind (eval_agrees_of hk ls ρ f) fun fv _ => ?_
    split
    · exact apply_agrees_of ih hk fv _
    · cases m with
      | strict => exact .bind (eval_agrees_of hk ls ρ a) fun x _ => apply_agrees_of ih hk fv _
      | byName => exact apply_agrees_of ih hk fv _
  | ρ, .const c us => by
    rw [eval_const, eval_const]
    exact evalConst_agrees_of ih hk _ c

end

/-- Every clock level agrees upward. -/
theorem monoAt : ∀ k, MonoAt p k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    exact
      { eval := fun _ hk ls ρ t => eval_agrees_of ih hk ls ρ t
        apply := fun _ hk f s => apply_agrees_of ih hk f s
        applyAll := fun _ hk f ss => applyAll_agrees_of ih hk f ss
        fire := fun _ hk h ls args => fire_agrees_of ih hk h ls args
        force := fun _ hk s => force_agrees_of ih hk s
        forceAll := fun _ hk ss => forceAll_agrees_of ih hk ss
        evalConst := fun _ hk ls c => evalConst_agrees_of ih hk ls c }

/-- **Clock monotonicity** of SrcEval (`eval_mono`, design note 01 §6.1). -/
theorem eval_mono (ls : Levels) (ρ : Env) (t : Term) : ClockMono fun k => eval p k ls ρ t :=
  Result.Agrees.clockMono fun k k' hk => (monoAt p k).eval k' hk ls ρ t

theorem apply_mono (f : Value) (s : Slot) : ClockMono fun k => apply p k f s :=
  Result.Agrees.clockMono fun k k' hk => (monoAt p k).apply k' hk f s

theorem applyAll_mono (f : Value) (ss : List Slot) : ClockMono fun k => applyAll p k f ss :=
  Result.Agrees.clockMono fun k k' hk => (monoAt p k).applyAll k' hk f ss

theorem fire_mono (h : Head) (ls : Levels) (args : List Slot) :
    ClockMono fun k => fire p k h ls args :=
  Result.Agrees.clockMono fun k k' hk => (monoAt p k).fire k' hk h ls args

theorem force_mono (s : Slot) : ClockMono fun k => force p k s :=
  Result.Agrees.clockMono fun k k' hk => (monoAt p k).force k' hk s

theorem forceAll_mono (ss : List Slot) : ClockMono fun k => forceAll p k ss :=
  Result.Agrees.clockMono fun k k' hk => (monoAt p k).forceAll k' hk ss

theorem evalConst_mono (ls : Levels) (c : CId) : ClockMono fun k => evalConst p k ls c :=
  Result.Agrees.clockMono fun k k' hk => (monoAt p k).evalConst k' hk ls c

theorem run_mono (root : CId) (xs : List Value) : ClockMono fun k => run p k root xs :=
  Result.Agrees.clockMono fun k k' hk => by
    rw [run_eq, run_eq]
    exact .bind ((monoAt p k).evalConst k' hk [] root) fun f _ =>
      (monoAt p k).applyAll k' hk f _

end IxCC.Src
