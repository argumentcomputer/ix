import IxCC.Anf.Proof.Convert.Kont

/-! # ANF conversion: spine heads and argument order

A Lam spine evaluates each argument just before applying it; conversion
evaluates a group of arguments first and applies them together. The two
orders agree whenever the arguments skipped over are *pure* (a non-thunk
variable, a literal, □, a λ, a constructor of pure terms, or a `name`
argument): they evaluate to one slot at every clock (`lamArgs_pure`), and
partial applications of a telescope at a positive clock only build the next
closure (`applyArgs_tele`). `lamArgs` is the grouped order on the Lam side.

The head of a spine is either a plain value applied to strict arguments, or
a telescope closure whose binders' kinds agree with the kinds the spine's
modes expect (`GroupHead`, `Compat`); a `name` variable whose signature has
a `name` holds a minor thunk, whose forced value is such a closure
(`minor_sim`). (P1.) -/

set_option autoImplicit false

namespace IxCC.Anf.Convert.Proof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Lam (Kind Mode argSlot applyArgs)
open IxCC.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName expected covered KindsSpec)
open IxCC.Ixon

/-! ## Arguments in grouped order (Lam) -/

variable (L : Lam.Program)

/-- Evaluate the arguments' slots left to right, then continue with all of
them. -/
def lamArgs (k : Nat) (ρ : Lam.Env) : List (Lam.Term × Mode) →
    (List Lam.Slot → Nat → Result Lam.Val) → Result Lam.Val
  | [], C => C [] k
  | a :: rest, C => (argSlot L k ρ a).bind fun s => lamArgs k ρ rest fun ss => C (s :: ss)

theorem lamArgs_nil (k : Nat) (ρ : Lam.Env) (C : List Lam.Slot → Nat → Result Lam.Val) :
    lamArgs L k ρ [] C = C [] k := rfl

theorem lamArgs_cons (k : Nat) (ρ : Lam.Env) (a : Lam.Term × Mode) (rest : List (Lam.Term × Mode))
    (C : List Lam.Slot → Nat → Result Lam.Val) :
    lamArgs L k ρ (a :: rest) C =
      (argSlot L k ρ a).bind fun s => lamArgs L k ρ rest fun ss => C (s :: ss) := rfl

theorem lamArgs_congr (k : Nat) (ρ : Lam.Env) : ∀ (args : List (Lam.Term × Mode))
    {C C' : List Lam.Slot → Nat → Result Lam.Val}, (∀ ss, C ss k = C' ss k) →
    lamArgs L k ρ args C = lamArgs L k ρ args C'
  | [], _, _, h => h []
  | _ :: rest, _, _, h => Result.bind_congr _ fun s => lamArgs_congr k ρ rest fun ss => h (s :: ss)

/-- Arguments whose slots are the same at every clock. -/
def SlotsConst (k : Nat) (ρ : Lam.Env) : List (Lam.Term × Mode) → List Lam.Slot → Prop
  | [], ss => ss = []
  | a :: rest, ss => ∃ s ss', ss = s :: ss' ∧ argSlot L k ρ a = .ok s ∧ SlotsConst k ρ rest ss'

/-- Pure arguments skipped over: grouped and interleaved orders agree. -/
theorem lamArgs_pure (k : Nat) (ρ : Lam.Env) (X : Lam.Val → Nat → Result Lam.Val) :
    ∀ (run : List (Lam.Term × Mode)) (ss : List Lam.Slot), SlotsConst L k ρ run ss →
      ∀ (f : Lam.Val) (pre : List Lam.Slot),
      lamArgs L k ρ run (fun ss' k => (Lam.applyAll L k f (pre ++ ss')).bind (X · k)) =
        (Lam.applyAll L k f pre).bind fun g => (applyArgs L k ρ g run).bind (X · k)
  | [], _, _, f, pre => by
    simp only [lamArgs_nil, List.append_nil, Lam.applyArgs_nil, Result.bind_ok]
  | a :: run, _, ⟨s, ss', rfl, hs, hrest⟩, f, pre => by
    rw [lamArgs_cons, hs, Result.bind_ok]
    have ih := lamArgs_pure k ρ X run ss' hrest f (pre ++ [s])
    simp only [List.append_assoc, List.singleton_append] at ih
    rw [ih, applyAll_append, Result.bind_assoc]
    refine Result.bind_congr _ fun g => ?_
    simp only [Lam.applyArgs_cons, hs, Result.bind_ok, Lam.applyAll_cons, Lam.applyAll_nil,
      Result.bind_assoc]

/-- At a positive clock, applying a telescope closure that still lacks at
least as many binders as there are arguments evaluates the arguments in
order and then applies them together. -/
theorem applyArgs_tele (k : Nat) (hk : 1 ≤ k) (ρ : Lam.Env) (body : Lam.Term) :
    ∀ (args : List (Lam.Term × Mode)) (ps : List (Mode × V3.BinderContract)) (ρs : Lam.Env),
      args.length ≤ ps.length + 1 →
      applyArgs L k ρ (.clos ρs (lamsWith ps body)) args =
        lamArgs L k ρ args fun ss k => Lam.applyAll L k (.clos ρs (lamsWith ps body)) ss
  | [], _, _, _ => by simp [Lam.applyArgs_nil, lamArgs_nil, Lam.applyAll_nil]
  | [a], ps, ρs, _ => by
    rw [Lam.applyArgs_cons, lamArgs_cons]
    refine Result.bind_congr _ fun s => ?_
    simp only [lamArgs_nil, Lam.applyAll_cons, Lam.applyAll_nil, Lam.applyArgs_nil]
  | a :: a' :: rest, p :: ps, ρs, hl => by
    rw [Lam.applyArgs_cons, lamArgs_cons]
    refine Result.bind_congr _ fun s => ?_
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [apply_lamsWith_cons, later_succ, Result.bind_ok,
      applyArgs_tele (j + 1) hk ρ body (a' :: rest) ps (s :: ρs) (by simp at hl ⊢; omega)]
    refine lamArgs_congr L (j + 1) ρ (a' :: rest) fun ss => ?_
    rw [Lam.applyAll_cons, apply_lamsWith_cons, later_succ, Result.bind_ok]
  | _ :: _ :: _, [], _, hl => by simp at hl

/-! ## Pure terms (Lam) -/

variable {L}
variable {A : Arities} {G : Src.NatMap Lam.ModesOk.GInfo}

mutual

theorem pure_eval {ks : List Kind} {vars : List VarInfo} {ρ : Lam.Env} {ρt : List Val}
    (henv : EnvR A G ks vars ρ ρt) : ∀ t : Lam.Term, pureTerm vars t = true →
      ∃ v, ∀ k, Lam.eval L k ρ t = .ok v
  | .var i, h => by
    simp only [pureTerm] at h
    cases hv : vars[i]? with
    | none => rw [hv] at h; cases h
    | some vi =>
      rw [hv] at h
      obtain ⟨q, s, w, _, hs, _, hsr, ht⟩ := henv.get hv
      have hq : q.isName = false := by rw [← ht]; simpa using h
      cases q with
      | name _ => cases hq
      | strict =>
        cases hsr with
        | val _ => exact ⟨_, fun k => by rw [Lam.eval_var_of L k ρ hs, Lam.force_val]⟩
  | .lit l, _ => ⟨_, fun k => Lam.eval_lit L k ρ l⟩
  | .box, _ => ⟨_, fun k => Lam.eval_box' L k ρ⟩
  | .lam m c b, _ => ⟨_, fun k => Lam.eval_lam L k ρ m c b⟩
  | .con c fs, h => by
    simp only [pureTerm] at h
    obtain ⟨vs, hvs⟩ := pure_evalList henv fs h
    exact ⟨_, fun k => by rw [Lam.eval_con, hvs]; rfl⟩
  | .glob _, h | .app .., h | .letE .., h | .case .., h | .proj .., h | .prim .., h | .tick _, h
  | .trap, h => by simp [pureTerm] at h

theorem pure_evalList {ks : List Kind} {vars : List VarInfo} {ρ : Lam.Env} {ρt : List Val}
    (henv : EnvR A G ks vars ρ ρt) : ∀ ts : List Lam.Term, pureList vars ts = true →
      ∃ vs, ∀ k, Lam.evalList L k ρ ts = .ok vs
  | [], _ => ⟨[], fun k => Lam.evalList_nil L k ρ⟩
  | t :: ts, h => by
    simp only [pureList, Bool.and_eq_true] at h
    obtain ⟨v, hv⟩ := pure_eval henv t h.1
    obtain ⟨vs, hvs⟩ := pure_evalList henv ts h.2
    exact ⟨v :: vs, fun k => by rw [Lam.evalList_cons, hv, Result.bind_ok, hvs]; rfl⟩

end

/-- Pure arguments have one slot at every clock. -/
theorem pure_slots {ks : List Kind} {vars : List VarInfo} {ρ : Lam.Env} {ρt : List Val}
    (henv : EnvR A G ks vars ρ ρt) : ∀ run : List (Lam.Term × Mode),
      (∀ a ∈ run, pureArg vars a = true) → ∃ ss, ∀ k, SlotsConst L k ρ run ss
  | [], _ => ⟨[], fun _ => rfl⟩
  | (a, m) :: run, h => by
    obtain ⟨ss, hss⟩ := pure_slots henv run fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ha := h (a, m) List.mem_cons_self
    cases m with
    | name => exact ⟨_ :: ss, fun k => ⟨_, ss, rfl, rfl, hss k⟩⟩
    | strict =>
      obtain ⟨v, hv⟩ := pure_eval (L := L) henv a (by simpa [pureArg] using ha)
      exact ⟨.val v :: ss, fun k => ⟨_, ss, rfl, by simp [argSlot, hv], hss k⟩⟩

theorem lamArgs_const {k : Nat} {ρ : Lam.Env} : ∀ {args : List (Lam.Term × Mode)} {ss : List Lam.Slot},
    SlotsConst L k ρ args ss → ∀ C, lamArgs L k ρ args C = C ss k
  | [], _, h, C => by cases h; rfl
  | _ :: _, _, ⟨s, ss', rfl, hs, hrest⟩, C => by
    rw [lamArgs_cons, hs, Result.bind_ok, lamArgs_const hrest]

/-! ## Expected and binder kinds -/

/-- The kind a spine position expects from its head's binder modes and
signatures. -/
def expKind (tele : List Mode) (sigs : List (List Mode)) (p : Nat) : Kind :=
  if tele.getD p .strict = .name then .name (sigs.getD p []) else .strict

/-- An expected kind fits a binder kind: the same, or two `name` kinds
whose signatures have no `name`. -/
def KindOk (e b : Kind) : Prop :=
  e = b ∨ ∃ se sb, e = .name se ∧ b = .name sb ∧ hasName se = false ∧ hasName sb = false

/-- Every position's expected kind fits the binder's. -/
def Compat (tele : List Mode) (sigs : List (List Mode)) (tk : List Kind) : Prop :=
  ∀ p, KindOk (expKind tele sigs p) (tk.getD p .strict)

theorem nameArgOk_plain {ks : List Kind} {sig sig' : List Mode} {t : Lam.Term}
    (h : NameArgOk G ks sig t) (hs : hasName sig = false) (hs' : hasName sig' = false) :
    NameArgOk G ks sig' t := by
  cases h with
  | plain _ ht => exact .plain hs' ht
  | fwd hn _ => rw [hs] at hn; cases hn
  | tele hn _ _ _ _ _ => rw [hs] at hn; cases hn

theorem SlotR.kindOk {e b : Kind} {s : Lam.Slot} {w : Val} (h : SlotR A G e s w) (hk : KindOk e b) :
    SlotR A G b s w := by
  rcases hk with rfl | ⟨se, sb, rfl, rfl, hse, hsb⟩
  · exact h
  · cases h with
    | name ht =>
      cases ht with
      | mk henv hconv hna hw => exact .name (.mk henv hconv (nameArgOk_plain hna hse hsb) hw)

end IxCC.Anf.Convert.Proof
